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
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac mem_side := cbn; first [ (let E := fresh "E" in intros E; discriminate E) | solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ exact I | reflexivity ] ] | solve [ repeat first [ left; reflexivity | right ] ] | tauto ].
Local Ltac mem_hyp Hr := cbn in Hr; first [ solve [ repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); first [ discriminate Hr | destruct Hr ] ] | intuition discriminate ].
(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv ShapeAlg Shapi1s Nodes MmapSim AgentLib Frame SymExec SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 SymAux LibK2dm RefMocc D_Kn21w D_Knp98 Spec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_M1ef.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Mz0p.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Tails.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Abp7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Tails.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Wamxh DU_Stts DU_Erh2 DU_Fo4k.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Fo4k.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Fo4k.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_T8mv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Tr7g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Shm0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require DU_Twyu DU_Tr7g LibIface V_AKit LibTail DU_Ssji.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Knp98 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_M1ef OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Mz0p.DU_MainA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tails.DU_Ogma OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Abp7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tails.DU_Dgah OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Stts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Erh2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Fo4k OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Fo4k.DU_Psxb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Fo4k.DU_Pbje OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_T8mv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tr7g.DU_TrLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Shm0.DU_T9tr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Twyu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Tr7g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibTail OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.DU_Ssji.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem Cells Step Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU DriverKit.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Record out_state (nb : nat) (M : word -> option byte) : Prop := OUTST {
  o_nb    : (nb <= 500)%nat;
  o_flags : rdn RSEGS M (Z_to_bv 64 0x31a38) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  o_rpos  : rdn RSEGS M (Z_to_bv 64 0x31a40) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  o_rend  : rdn RSEGS M (Z_to_bv 64 0x31a48) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  o_wend  : rdn RSEGS M (Z_to_bv 64 0x31a58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62ff8));
  o_wpos  : rdn RSEGS M (Z_to_bv 64 0x31a60) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x62bf8 + 2 * Z.of_nat nb)));
  o_wbase : rdn RSEGS M (Z_to_bv 64 0x31a70) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62bf8));
  o_write : rdn RSEGS M (Z_to_bv 64 0x31a80) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x260f8));
  o_buf   : rdn RSEGS M (Z_to_bv 64 0x31a90) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62bf8));
  o_bsz   : rdn RSEGS M (Z_to_bv 64 0x31a98) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  o_fd    : rdn RSEGS M (Z_to_bv 64 0x31ab0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  o_lock  : rdn RSEGS M (Z_to_bv 64 0x31ac4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  o_lbf   : rdn RSEGS M (Z_to_bv 64 0x31ac8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  o_bytes : rdn RSEGS M (Z_to_bv 64 0x62bf8) (2 * nb) = Some (zero_lines nb) }.

Definition out_pristine (M : word -> option byte) : Prop :=
  forall i, (0x31a38 <= i < 0x31b20)%Z -> M (Z_to_bv 64 i) = None.

Record md_ok (fs0 : Fs) (md : Model) : Prop := MDOK_ {
  mk_fs  : m_fs md = fs0;
  mk_fd1 : fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
  mk_fd2 : fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2));
  mk_h   : m_halted md = None;
  mk_lz  : m_vm_lazy md = [] }.

Lemma zero_lines_length : forall n, length (zero_lines n) = (2 * n)%nat.
Proof. induction n; cbn; [reflexivity|]. rewrite IHn. lia. Qed.

Lemma zero_lines_S : forall n, zero_lines (S n) = zero_lines n ++ [Z_to_bv 8 48; Z_to_bv 8 10].
Proof. induction n as [|n IH]; [reflexivity|]. cbn [zero_lines app]. rewrite <- IH. reflexivity. Qed.

Section Loop.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutPU} {DK : DriverKit LayoutPU InitPU}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Hypothesis Hvsp : valid_sp sp0.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Variable fs0 : Fs.
  (* [comment removed for export] *)
  Local Notation R16 := (at_random_bytes (ed_random rdraw)) (only parsing).
  Definition CANW : word := blob_val false (guard_bytes (at_random_bytes (ed_random rdraw))) 0 8.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables limg_lo limg_hi : Z.
  Hypothesis Hlimg : (0x10000 <= limg_lo)%Z /\ (limg_hi <= 0x31a38)%Z.
  Variable limg : (word -> option byte) -> Prop.
  Hypothesis limg_intro : forall m, Mem.mem_inv RSEGS m ->
    (forall i, (limg_lo <= i < limg_hi)%Z -> m (Z_to_bv 64 i) = None) -> limg m.
  Definition LLU : LibLayout := mkLibLayout LayoutPU 0x1807c 0x41bd0 limg limg_lo limg_hi limg_intro 0x62768.
  Hypothesis LIBOK : lib_call_ok LLU.

  (* [comment removed for export] *)
  Variables (b capk plen owned aligned : Z) (payload : list byte) (v6 : word).
  Hypothesis Hlen : Z.of_nat (length payload) = plen.
  Hypothesis Hplen : (plen < 2 ^ 26)%Z.
  Hypothesis Hal : (plen = 0 /\ aligned = 0x41bb0 /\ owned = 0)%Z \/ (0 < plen /\ aligned = owned)%Z.
  Hypothesis Hpc : (plen < capk)%Z.

  Record lp_st (first : bool) (j nb : nat) (vals : list word) (R : bvmap 5 word) (M : word -> option byte)
         (md : Model) (A : AS) : Prop := LPST {
    p_base : base_ok sp0 a0s path envv tid vals;
    p_v6   : vals_ev vals 6 = v6;
    p_v20  : vals_ev vals 20 = Z_to_bv 64 b;
    p_v23  : vals_ev vals 23 = Z_to_bv 64 owned;
    p_know : know_ok RSEGS (ENV a0s path rdraw vals) M knL;
    p_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208);
    p_gp : getr R 3 = Z_to_bv 64 0x10800;
    p_tp : getr R 4 = Z_to_bv 64 0x424f8;
    p_s0 : getr R 8 = Z_to_bv 64 plen;
    p_s1 : getr R 9 = Z_to_bv 64 aligned;
    p_s2 : getr R 18 = Z_to_bv 64 owned;
    (* [comment removed for export] *)
    p_s4 : getr R 20 = Z_to_bv 64 0x41ba0;
    p_s5 : getr R 21 = Z_to_bv 64 (Z.of_nat j);
    p_s6 : getr R 22 = Z_to_bv 64 0;
    p_s7 : getr R 23 = Z_to_bv 64 18446744073709551614;
    p_ainv : ainv A M md;
    p_mi : Mem.mem_inv RSEGS M;
    p_md : md_ok fs0 md;
    p_liveb : a_live A b = Some capk;
    p_own : plen = 0%Z \/ (a_live A owned = Some plen /\
              forall i, (0 <= i < plen)%Z -> M (Z_to_bv 64 (owned + i)) = Some (nth (Z.to_nat i) payload (Z_to_bv 8 0)));
    p_out : if first then out_pristine M else out_state nb M;
    (* [comment removed for export] *)
    p_bud : (a_livebytes A + LIB_LIVE plen <= LIVE_MAX)%Z /\ (a_nlive A + LIB_NLIVE <= NLIVE_MAX)%Z }.

  Lemma u64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros. apply u_small. assumption. Qed.

  (* [comment removed for export] *)
  Lemma knL_img_none : forall vals M, know_ok RSEGS (ENV a0s path rdraw vals) M knL ->
    forall i, (0x10000 <= i < 0x31a38)%Z -> M (Z_to_bv 64 i) = None.
  Proof.
    intros vals M HK i Hi.
    pose proof (know_nth RSEGS _ _ knL ltac:(let i := kidx knL (is_kimg_cov 0x10000 1) in exact i) _ HK eq_refl) as K.
    cbn [kentry_ok] in K. (first [ dand3 K as _ _ K | destruct K as (_ & _ & K) ]). apply K. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma knL_can : forall vals M, know_ok RSEGS (ENV a0s path rdraw vals) M knL ->
    rdn RSEGS M (Z_to_bv 64 0x62768) 8 = Some (word_to_le_bytes 8 CANW).
  Proof. intros vals M HK. unfold CANW. krd_solve HK. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma knL_dw : nth_error knL knL_dwi = Some (KWr (SA (ELit 0) 0x31000) 0x33000). Proof. vm_compute. reflexivity. Qed.
  Lemma incb_sok : forall vals M, base_ok sp0 a0s path envv tid vals -> know_ok RSEGS (ENV a0s path rdraw vals) M knL ->
    store_ok RSEGS M (Z_to_bv 64 0x41ba4) 1%nat = true.
  Proof.
    intros vals M HB HK.
    pose proof (kwr_store_ok RSEGS (ENV a0s path rdraw vals) _ knL knL_dwi _ _ _ 0x41ba4 1 HK knL_dw ltac:(lia) ltac:(cbn; lia)) as Hst.
    unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hst.
    exact Hst.
  Qed.
  Lemma incb_agree : forall M bb (x : word), bv_unsigned x <> 0x41ba4%Z -> wbytes M (Z_to_bv 64 0x41ba4) [bb] x = M x.
  Proof. intros M bb x Hx. pose proof (u64_range x). apply MemSplit.wbytes_outside; cbn [length]; rewrite u64 by lia; lia. Qed.
  #[using="payload"] Lemma out_state_agree : forall nb M M',
    (forall x : word, (0x31a38 <= bv_unsigned x < 0x31b20)%Z -> M' x = M x) ->
    (forall x : word, (0x62bf8 <= bv_unsigned x < 0x62ff8)%Z -> M' x = M x) ->
    out_state nb M -> out_state nb M'.
  Proof.
    intros nb M M' Z1 Z2 [F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13].
    split; rewrite ?(rdn_zone M M' 0x31a38 0x31b20 _ _ Z1) by lia; try assumption.
    rewrite (rdn_zone M M' 0x62bf8 0x62ff8 _ _ Z2) by (rewrite ?zero_lines_length; lia). exact F13.
  Qed.
  (* [comment removed for export] *)
  #[using="Hal Htid HCEIL Hvsp"] Lemma call_prep : forall first j nb vals R M md A,
    lp_st first j nb vals R M md A ->
    exists R1,
      msteps RSEGS (mkst R (Z_to_bv 64 0x17f20) M (seg_rom RSEGS))
                   (mkst R1 (0x1807c : word) (wbytes M (Z_to_bv 64 0x41ba4) [Z_to_bv 8 1]) (seg_rom RSEGS))
      /\ lp_st first j nb vals R1 (wbytes M (Z_to_bv 64 0x41ba4) [Z_to_bv 8 1]) md A
      /\ getr R1 10 = Z_to_bv 64 aligned /\ getr R1 11 = Z_to_bv 64 plen /\ getr R1 1 = Z_to_bv 64 0x17f34.
  Proof.
    intros first j nb vals R M md A ST.
    pose proof ST as [HB V6 V20 V23 HK P2 P3 P4 P8 P9 P18 P20 P21 P22 P23 AI0 MI MD LIVEB OWN OUT BUD].
    (first [ pose proof (HB) as dR_2; dand5 dR_2 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    pose proof alloc_ceiling_val as CV.
    destruct (tr_call R M (seg_rom RSEGS) P20 (incb_sok vals M HB HK)) as (R1 & MS & A10 & A11 & A1 & KEEP).
    exists R1. split; [replace (Z_to_bv 64 0x17f20) with (0x17f20 : word) by (apply bv_eq; reflexivity); exact MS|].
    destruct (drv_client sp0 A M (wbytes M (Z_to_bv 64 0x41ba4) [Z_to_bv 8 1]) md SPlo ltac:(lia) AI0 MI
                ltac:(intros x _ N2 _; apply incb_agree; lia) (wbytes_grows _ _ _)) as [AI1 MI1].
    split; [| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [rewrite A10; exact P9 | rewrite A11; exact P8 | exact A1]].
    split; try (rewrite KEEP by (intros E; discriminate E)); try assumption.
    - apply (know_knL_byte vals _ M). exact HK.
    - destruct OWN as [P0|[LVo BY]]; [left; exact P0| right]. split; [exact LVo|]. intros i Hi.
      (first [ pose proof ((as_live_ok A M md owned plen AI0 LVo)) as dR_9; dand6 dR_9 as _ _ P1 HI IMG _ | destruct (as_live_ok A M md owned plen AI0 LVo) as (_ & _ & P1 & HI & IMG & _) ]).
      cbn [al_image_lo al_image_hi LayoutPU] in IMG. rewrite incb_agree by (rewrite u64 by lia; lia). apply BY. exact Hi.
    - destruct first.
      + intros i Hi. rewrite incb_agree by (rewrite u64 by lia; lia). apply OUT. exact Hi.
      + apply (out_state_agree nb M); [intros x Hx; apply incb_agree; lia | intros x Hx; apply incb_agree; lia | exact OUT].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hal Hplen Hlen LIBOK limg_intro limg Hlimg limg_hi limg_lo Htid HCEIL Hvsp"] Lemma lib_part : forall first j nb vals R M md A T,
    lp_st first j nb vals R M md A ->
    (forall R' M' md' A', lp_st first j nb vals R' M' md' A' -> getr R' 10 = Z_to_bv 64 0 ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x17f34) M' (seg_rom RSEGS)) md') T) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17f20) M (seg_rom RSEGS)) md) T.
  Proof.
    intros first j nb vals R0 M0 md A T ST0 K.
    (* [comment removed for export] *)
    destruct (call_prep first j nb vals R0 M0 md A ST0) as (R1 & MS & ST & A10 & A11 & A1).
    pose proof ST0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MD0 _ _ _ _]. pose proof MD0 as [_ _ _ Mh0 Mlz0].
    eapply rz_msteps; [exact Mh0 | exact Mlz0 | exact MS |]. clear MS ST0 MD0 Mh0 Mlz0.
    set (M := wbytes M0 (Z_to_bv 64 0x41ba4) [Z_to_bv 8 1]) in *.
    pose proof ST as [HB V6 V20 V23 HK P2 P3 P4 P8 P9 P18 P20 P21 P22 P23 AI0 MI MD LIVEB OWN OUT BUD].
    (first [ pose proof (HB) as dR_2; dand5 dR_2 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]). pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    replace (0x1807c : word) with (Z_to_bv 64 0x1807c) by (apply bv_eq; reflexivity).
    change (realizes RSEGS (mkCfg (mkst R1 (Z_to_bv 64 0x1807c) M (seg_rom RSEGS)) md) T)
      with (realizes (al_segs (ll_alloc LLU)) (mkCfg (mkst R1 (Z_to_bv 64 (ll_entry LLU)) M (seg_rom (al_segs (ll_alloc LLU)))) md) T).
    apply (LIBOK R1 M md A aligned payload T).
    - (* [comment removed for export] *)
      assert (SP1 : bv_unsigned (getr R1 2) = (bv_unsigned sp0 - 208)%Z) by (rewrite P2; apply u64; lia).
      constructor; rewrite ?SP1.
      + exact A10.
      + rewrite A11, <- Hlen. reflexivity.
      + exact P4.
      + rewrite A1. rewrite u64 by lia. reflexivity.
      + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      + rewrite HCEIL. unfold LIB_STACK. lia.
      + lia.
      + exact MI.
      + unfold LIB_STACK. apply (stk_of_win vals (blobs_ev (blobs0 a0s path rdraw)) M knL knL_iw); rewrite ?V0; try exact HK; try exact knL_win; lia.
      + change (al_errno (ll_alloc LLU)) with (bv_unsigned (Z_to_bv 64 0x424f8) - 164)%Z. rewrite u64 by lia.
        apply rw_errno_any.
      + apply rw_bss_any.
      + apply limg_intro; [exact MI|]. intros i Hi. apply (knL_img_none vals M HK). clear -Hi Hlimg. lia.
      + exists CANW. apply rw_guard. apply (knL_can vals M HK).
      + rewrite Hlen. exact Hplen.
      + intros Hne. destruct OWN as [P0|[LV BY]]; [exfalso; apply Hne; apply Nat2Z.inj; rewrite Hlen, P0; reflexivity|].
        destruct Hal as [[P0 _]|[_ ->]]; [lia|]. rewrite Hlen. split; [exact LV|].
        (first [ pose proof ((as_live_ok A M md owned plen AI0 LV)) as dR_4; dand5 dR_4 as N0 _ P1 HI _ | destruct (as_live_ok A M md owned plen AI0 LV) as (N0 & _ & P1 & HI & _) ]).
        apply bytes_at_block; rewrite ?Hlen; [lia| rewrite HCEIL in HI; lia| exact BY].
      + exact AI0.
      + rewrite Hlen. exact BUD.   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      intros R' M' md' A' POST.
      destruct POST as [CS A0' MDF AI' BUD' LV LVB MI' STK' ERR' BSS' IMG' GRD' CF].
      rewrite A1.
      change (realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x17f34) M' (seg_rom RSEGS)) md') T).
      assert (SPV : bv_unsigned (getr R1 2) = (bv_unsigned sp0 - 208)%Z) by (rewrite P2; apply u64; lia).
      rewrite SPV in CF. change (ll_alloc LLU) with LayoutPU in CF. unfold LIB_STACK in CF.
      change (fun a : Z => (ll_bss LLU <= a < ll_bss LLU + 16)%Z) with bss16 in CF.
      assert (LZ : forall x : word, lzone x -> M' x = M x) by (apply (lzone_ccall A A' M M' md md' _ AI0 AI' CF); unfold LIBW; lia).
      assert (CSR : forall r : reg, In r callee_saved -> r <> 1 -> getr R' r = getr R1 r).
      { intros r Hr H1. exact (CS r Hr). }
      apply (K R' M' md' A'); [| exact A0'].
      split.
      + exact HB. + exact V6. + exact V20. + exact V23.
      + rewrite <- V0 in CF. apply (know_knL_lib vals _ A A' M M' md md' HK ltac:(rewrite V0; lia) AI0 AI' CF ltac:(rewrite V0; lia) ltac:(rewrite V0; lia)).
      + rewrite CSR by mem_side. exact P2.
      + rewrite CSR by mem_side. exact P3.
      + rewrite CSR by mem_side. exact P4.
      + rewrite CSR by mem_side. exact P8.
      + rewrite CSR by mem_side. exact P9.
      + rewrite CSR by mem_side. exact P18.
      + rewrite CSR by mem_side. exact P20.
      + rewrite CSR by mem_side. exact P21.
      + rewrite CSR by mem_side. exact P22.
      + rewrite CSR by mem_side. exact P23.
      + exact AI'.
      + exact MI'.
      + (first [ dand12 MDF as FD _ FS _ _ _ _ _ _ _ LZ' HH | destruct MDF as (FD & _ & FS & _ & _ & _ & _ & _ & _ & _ & LZ' & HH) ]). split.   (* [comment removed for export] *)
        * unfold m_fs. rewrite FS. exact Mfs.
        * unfold m_fds. rewrite FD. exact Mfd1.
        * unfold m_fds. rewrite FD. exact Mfd2.
        * exact HH.
        * exact LZ'.
      + apply LV. exact LIVEB.
      + destruct OWN as [P0|[LVo BY]]; [left; exact P0| right]. split; [apply LV; exact LVo|].
        intros i Hi. rewrite (LVB owned plen i LVo Hi). apply BY. exact Hi.
      + destruct first.
        * intros i Hi. rewrite LZ by (unfold lzone; rewrite u64 by lia; lia). apply OUT. exact Hi.
        * destruct OUT as [F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13].
          assert (Z1 : forall x : word, (0x10000 <= bv_unsigned x < 0x41bd0)%Z -> M' x = M x) by (intros x Hx; apply LZ; unfold lzone; lia).
          assert (Z2 : forall x : word, (0x62ba4 <= bv_unsigned x < 0x64000)%Z -> M' x = M x) by (intros x Hx; apply LZ; unfold lzone; lia).
          split; rewrite ?(rdn_zone M M' 0x10000 0x41bd0 _ _ Z1) by lia; try assumption.
          rewrite (rdn_zone M M' 0x62ba4 0x64000 _ _ Z2) by lia. exact F13.
      + destruct BUD' as [B1 B2]. change (ll_alloc LLU) with LayoutPU in B1, B2. rewrite B1, B2. exact BUD.   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Hal Htid HCEIL Hvsp"] Lemma pf_prep : forall first j nb vals R M md A,
    lp_st first j nb vals R M md A -> getr R 10 = Z_to_bv 64 0 ->
    exists R2,
      msteps RSEGS (mkst R (Z_to_bv 64 0x17f34) M (seg_rom RSEGS))
                   (mkst R2 (0x17ff0 : word) (wbytes M (Z_to_bv 64 0x41ba4) [Z_to_bv 8 0]) (seg_rom RSEGS))
      /\ lp_st first j nb vals R2 (wbytes M (Z_to_bv 64 0x41ba4) [Z_to_bv 8 0]) md A
      /\ getr R2 19 = Z_to_bv 64 0 /\ getr R2 11 = Z_to_bv 64 0 /\ getr R2 1 = Z_to_bv 64 0x17f44
      /\ rdn RSEGS (wbytes M (Z_to_bv 64 0x41ba4) [Z_to_bv 8 0]) (Z_to_bv 64 0x41ba4) 1%nat = Some [Z_to_bv 8 0].
  Proof.
    intros first j nb vals R M md A ST A0.
    pose proof ST as [HB V6 V20 V23 HK P2 P3 P4 P8 P9 P18 P20 P21 P22 P23 AI0 MI MD LIVEB OWN OUT BUD].
    (first [ pose proof (HB) as dR_2; dand5 dR_2 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    pose proof alloc_ceiling_val as CV.
    destruct (tr_pf R M (seg_rom RSEGS) P20 (incb_sok vals M HB HK)) as (R2 & MS & A19 & A11 & A1 & KEEP).
    exists R2. split; [replace (Z_to_bv 64 0x17f34) with (0x17f34 : word) by (apply bv_eq; reflexivity); exact MS|].
    destruct (drv_client sp0 A M (wbytes M (Z_to_bv 64 0x41ba4) [Z_to_bv 8 0]) md SPlo ltac:(lia) AI0 MI
                ltac:(intros x _ N2 _; apply incb_agree; lia) (wbytes_grows _ _ _)) as [AI1 MI1].
    split; [| split; [rewrite A19; exact A0 | split; [rewrite A11; exact A0 | split; [exact A1 |
              apply (rdn_wbytes_hit RSEGS [Z_to_bv 8 0] M (Z_to_bv 64 0x41ba4)); cbn [length]; rewrite u64 by lia; lia]]]].
    split; try (rewrite KEEP by (intros E; discriminate E)); try assumption.
    - apply (know_knL_byte vals _ M). exact HK.
    - destruct OWN as [P0|[LVo BY]]; [left; exact P0| right]. split; [exact LVo|]. intros i Hi.
      (first [ pose proof ((as_live_ok A M md owned plen AI0 LVo)) as dR_9; dand6 dR_9 as _ _ P1 HI IMG _ | destruct (as_live_ok A M md owned plen AI0 LVo) as (_ & _ & P1 & HI & IMG & _) ]).
      cbn [al_image_lo al_image_hi LayoutPU] in IMG. rewrite incb_agree by (rewrite u64 by lia; lia). apply BY. exact Hi.
    - destruct first.
      + intros i Hi. rewrite incb_agree by (rewrite u64 by lia; lia). apply OUT. exact Hi.
      + apply (out_state_agree nb M); [intros x Hx; apply incb_agree; lia | intros x Hx; apply incb_agree; lia | exact OUT].
  Qed.

  (* [comment removed for export] *)
  #[using="payload HCEIL Hvsp"] Lemma pf_client : forall A M M' md,
    ainv A M md -> Mem.mem_inv RSEGS M ->
    (forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z ->
                      ~ (0x31a38 <= bv_unsigned x < 0x31b20)%Z -> ~ (0x62bf8 <= bv_unsigned x < 0x62ff8)%Z -> M' x = M x) ->
    mem_grows M M' ->
    ainv A M' md /\ Mem.mem_inv RSEGS M'.
  Proof.
    intros A M M' md AI0 MI OUT G.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    assert (Hh : m_halted md = None) by (destruct (as_lazy_nil A M md AI0) as [_ X]; exact X).
    split.
    - apply (as_frame A M M' md md AI0).
      + intros a Ho. pose proof (owned_azone A M md a AI0 Ho) as ZZ. unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in ZZ.
        destruct (Z_lt_le_dec a 0) as [N|N]; [lia|]. destruct (Z_lt_le_dec a (2 ^ 64)) as [N2|N2].
        * apply OUT; rewrite u64 by lia; lia.
        * replace (Z_to_bv 64 a) with (Z_to_bv 64 (a mod 2 ^ 64)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; cbn [bv_modulus Z.of_N]; rewrite Zmod_mod; reflexivity).
          lia.
      + intros a Hs. cbn [al_shared LayoutPU] in Hs. unfold pu_shared in Hs. apply OUT; rewrite u64 by lia; lia.
      + intros p n i HL Hi. (first [ pose proof ((as_live_ok A M md p n AI0 HL)) as dR_6; dand7 dR_6 as _ _ _ _ _ MPp _ | destruct (as_live_ok A M md p n AI0 HL) as (_ & _ & _ & _ & _ & MPp & _) ]). apply G. apply MPp. exact Hi.
      + intros a [Ha Hni] Hm. rewrite HCEIL in Ha. unfold in_image in Hni. cbn [al_image_lo al_image_hi LayoutPU] in Hni.
        rewrite OUT in Hm; [exact Hm| rewrite u64 by lia; lia| rewrite u64 by lia; lia| rewrite u64 by lia; lia].
      + reflexivity.
      + exact Hh.
    - intros x v Hx. destruct (Mem.ro_addr RSEGS x) eqn:RO; [|reflexivity]. exfalso.
      pose proof (proj1 (as_ro_addr_iff (AI:=AI) x) RO) as RA. cbn [al_image_lo al_rw_lo LayoutPU] in RA.
      rewrite OUT in Hx by lia. pose proof (MI x v Hx) as RO'. rewrite RO' in RO. discriminate.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hal Hlimg limg_hi limg_lo Htid HCEIL Hvsp"] Lemma pf_first : forall j nb vals R M md A T,
    lp_st true j nb vals R M md A -> getr R 10 = Z_to_bv 64 0 -> T [] ->
    (forall R' M', lp_st false j 0 vals R' M' md A -> getr R' 19 = Z_to_bv 64 0 ->
        rdn RSEGS M' (Z_to_bv 64 0x41ba4) 1%nat = Some [Z_to_bv 8 0] ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x17f44) M' (seg_rom RSEGS)) md) T) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17f34) M (seg_rom RSEGS)) md)
             (t_emit [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 48); WriteEv (Z_to_bv 64 1) (Z_to_bv 8 10)] T).
  Proof.
    intros j nb vals R0 M0 md A T ST0 A0 Tnil K.
    (* [comment removed for export] *)
    destruct (pf_prep true j nb vals R0 M0 md A ST0 A0) as (R2 & MS & ST & A19 & A11 & A1 & INCB).
    pose proof ST0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MD0 _ _ _ _]. pose proof MD0 as [_ _ _ Mh0 Mlz0].
    eapply rz_msteps; [exact Mh0 | exact Mlz0 | exact MS |]. clear MS ST0 MD0 Mh0 Mlz0.
    set (M := wbytes M0 (Z_to_bv 64 0x41ba4) [Z_to_bv 8 0]) in *.
    pose proof ST as [HB V6 V20 V23 HK P2 P3 P4 P8 P9 P18 P20 P21 P22 P23 AI0 MI MD LIVEB OWN OUT BUD].
    (first [ pose proof (HB) as dR_7; dand5 dR_7 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]). pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    replace (0x17ff0 : word) with (Z_to_bv 64 0x17ff0) by (apply bv_eq; reflexivity).
    assert (PH : fp1H M (Z_to_bv 64 (bv_unsigned sp0 - 208)) (bv_unsigned CANW)).
    { split.
      - rewrite u64 by lia. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      - rewrite u64 by lia. lia.
      - rewrite u64 by lia. lia.
      - unfold FP1_FR. apply (stk_ok_of_win vals (blobs_ev (blobs0 a0s path rdraw)) M knL knL_iw); rewrite ?V0, ?u64 by lia; try exact HK; try exact knL_win; lia.
      - intros i Hi. apply (knL_img_none vals M HK). clear -Hi Hlimg. lia.
      - unfold STDOUT_F. exact OUT.
      - rewrite Z_to_bv_bv_unsigned. apply (knL_can vals M HK).
      - apply u64_range. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply (first_printf R2 M md (Z_to_bv 64 (bv_unsigned sp0 - 208)) (bv_unsigned CANW) PH A1 P2 A11 Mfd1 Mh Mlz T Tnil).
    intros R' M' CS PP. destruct PP as [AG G F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12].
    unfold FP1_FR, STDOUT_F, STDOUT_BUF in AG. rewrite u64 in AG by lia.
    assert (CSR : forall r : reg, In r callee_saved -> r <> 1 -> r <> 19 -> getr R' r = getr R2 r).
    { intros r Hr H1 H19. exact (CS r Hr). }
    assert (OUTp : forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z ->
                     ~ (0x31a38 <= bv_unsigned x < 0x31b20)%Z -> ~ (0x62bf8 <= bv_unsigned x < 0x62ff8)%Z -> M' x = M x).
    { intros x N1 N2 N3. apply AG; lia. }
    destruct (pf_client A M M' md AI0 MI OUTp G) as [AI' MI'].
    apply (K R' M'); [| rewrite (CS 19%bv ltac:(mem_side)); exact A19
                     | rewrite (rdn_zone M M' 0x41ba4 0x41ba5 0x41ba4 1 ltac:(intros x Hx; apply OUTp; lia)) by lia; exact INCB].
    split.
    - exact HB. - exact V6. - exact V20. - exact V23.
    - apply (know_knL_pf vals _ M M' HK ltac:(rewrite V0; lia)); [| exact G].
      intros x OUTx. pose proof (u64_range x).
      assert (B1 := OUTx (EVar 0) (-208 - 1200)%Z 1200%Z ltac:(mem_side)).
      assert (B2 := OUTx (ELit 0) 0x31a38%Z 232%Z ltac:(mem_side)).
      assert (B3 := OUTx (ELit 0) 0x62bf8%Z 1024%Z ltac:(mem_side)).
      unfold estart in B1, B2, B3. cbn [a_base a_off edenot ev ENV] in B1, B2, B3. rewrite V0 in B1.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in B2, B3.
      apply AG; lia.
    - rewrite CSR by mem_side. exact P2.
    - rewrite CSR by mem_side. exact P3.
    - rewrite CSR by mem_side. exact P4.
    - rewrite CSR by mem_side. exact P8.
    - rewrite CSR by mem_side. exact P9.
    - rewrite CSR by mem_side. exact P18.
    - rewrite CSR by mem_side. exact P20.
    - rewrite CSR by mem_side. exact P21.
    - rewrite CSR by mem_side. exact P22.
    - rewrite CSR by mem_side. exact P23.
    - exact AI'.
    - exact MI'.
    - exact MD.
    - exact LIVEB.
    - destruct OWN as [P0|[LVo BY]]; [left; exact P0| right]. split; [exact LVo|].
      intros i Hi. (first [ pose proof ((as_live_ok A M md owned plen AI0 LVo)) as dR_9; dand6 dR_9 as _ _ P1 HI IMG _ | destruct (as_live_ok A M md owned plen AI0 LVo) as (_ & _ & P1 & HI & IMG & _) ]).
      rewrite HCEIL in HI. cbn [al_image_lo al_image_hi LayoutPU] in IMG.
      rewrite OUTp by (rewrite u64 by lia; lia). apply BY. exact Hi.
    - split; try assumption; [lia | reflexivity].
    - exact BUD.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hal Hlimg limg_hi limg_lo Htid HCEIL Hvsp"] Lemma pf_next : forall j nb vals R M md A T,
    lp_st false j nb vals R M md A -> getr R 10 = Z_to_bv 64 0 -> (nb <= 400)%nat ->
    (forall R' M', lp_st false j (S nb) vals R' M' md A -> getr R' 19 = Z_to_bv 64 0 ->
        rdn RSEGS M' (Z_to_bv 64 0x41ba4) 1%nat = Some [Z_to_bv 8 0] ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x17f44) M' (seg_rom RSEGS)) md) T) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17f34) M (seg_rom RSEGS)) md) T.
  Proof.
    intros j nb vals R0 M0 md A T ST0 A0 Hnb K.
    (* [comment removed for export] *)
    destruct (pf_prep false j nb vals R0 M0 md A ST0 A0) as (R2 & MS & ST & A19 & A11 & A1 & INCB).
    pose proof ST0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MD0 _ _ _ _]. pose proof MD0 as [_ _ _ Mh0 Mlz0].
    eapply rz_msteps; [exact Mh0 | exact Mlz0 | exact MS |]. clear MS ST0 MD0 Mh0 Mlz0.
    set (M := wbytes M0 (Z_to_bv 64 0x41ba4) [Z_to_bv 8 0]) in *.
    pose proof ST as [HB V6 V20 V23 HK P2 P3 P4 P8 P9 P18 P20 P21 P22 P23 AI0 MI MD LIVEB OWN OUT BUD].
    (first [ pose proof (HB) as dR_10; dand5 dR_10 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]). pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof OUT as [F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    set (w := (0x62bf8 + 2 * Z.of_nat nb)%Z) in *.
    assert (PH : pfH M (Z_to_bv 64 (bv_unsigned sp0 - 208)) w (bv_unsigned CANW)).
    { split; rewrite ?u64 by lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      - lia.
      - lia.
      - unfold PF_FR. apply (stk_ok_of_win vals (blobs_ev (blobs0 a0s path rdraw)) M knL knL_iw); rewrite ?V0, ?u64 by lia; try exact HK; try exact knL_win; lia.
      - intros i Hi. apply (knL_img_none vals M HK). clear -Hi Hlimg. lia.
      - exact F1.
      - exact F4.
      - exact F5.
      - subst w. lia.
      - exact F9.
      - exact F11.
      - exact F12.
      - rewrite Z_to_bv_bv_unsigned. apply (knL_can vals M HK).
      - apply u64_range. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct (printf0_buffered R2 M (seg_rom RSEGS) (Z_to_bv 64 (bv_unsigned sp0 - 208)) w (bv_unsigned CANW) PH A1 P2 A11)
      as (R' & M' & MS2 & CS & FM & NB & NW & NF).
    replace (0x17ff0 : word) with (Z_to_bv 64 0x17ff0) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Mh | exact Mlz | exact MS2 |].
    destruct FM as [AGo G].
    assert (AG : forall x : word,
              ~ (bv_unsigned sp0 - 208 - 1056 <= bv_unsigned x < bv_unsigned sp0 - 208)%Z ->
              ~ (0x31a38 <= bv_unsigned x < 0x31a3c)%Z -> ~ (0x31a60 <= bv_unsigned x < 0x31a68)%Z ->
              ~ (w <= bv_unsigned x < w + 2)%Z -> M' x = M x).
    { intros x N1 N2 N3 N4. apply AGo. unfold outside, in_rng. rewrite (u64 (bv_unsigned sp0 - 208)) by lia.
      rewrite !u64 by (subst w; lia). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    assert (CSR : forall r : reg, In r callee_saved -> r <> 1 -> r <> 19 -> getr R' r = getr R2 r).
    { intros r Hr H1 H19. exact (CS r Hr). }
    assert (OUTp : forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z ->
                     ~ (0x31a38 <= bv_unsigned x < 0x31b20)%Z -> ~ (0x62bf8 <= bv_unsigned x < 0x62ff8)%Z -> M' x = M x).
    { intros x N1 N2 N3. apply AG; subst w; lia. }
    destruct (pf_client A M M' md AI0 MI OUTp G) as [AI' MI'].
    apply (K R' M'); [| rewrite (CS 19%bv ltac:(mem_side)); exact A19
                     | rewrite (rdn_zone M M' 0x41ba4 0x41ba5 0x41ba4 1 ltac:(intros x Hx; apply OUTp; lia)) by lia; exact INCB].
    split.
    - exact HB. - exact V6. - exact V20. - exact V23.
    - apply (know_knL_pf vals _ M M' HK ltac:(rewrite V0; lia)); [| exact G].
      intros x OUTx. pose proof (u64_range x).
      assert (B1 := OUTx (EVar 0) (-208 - 1200)%Z 1200%Z ltac:(mem_side)).
      assert (B2 := OUTx (ELit 0) 0x31a38%Z 232%Z ltac:(mem_side)).
      assert (B3 := OUTx (ELit 0) 0x62bf8%Z 1024%Z ltac:(mem_side)).
      unfold estart in B1, B2, B3. cbn [a_base a_off edenot ev ENV] in B1, B2, B3. rewrite V0 in B1.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in B2, B3.
      apply AG; subst w; lia.
    - rewrite CSR by mem_side. exact P2.
    - rewrite CSR by mem_side. exact P3.
    - rewrite CSR by mem_side. exact P4.
    - rewrite CSR by mem_side. exact P8.
    - rewrite CSR by mem_side. exact P9.
    - rewrite CSR by mem_side. exact P18.
    - rewrite CSR by mem_side. exact P20.
    - rewrite CSR by mem_side. exact P21.
    - rewrite CSR by mem_side. exact P22.
    - rewrite CSR by mem_side. exact P23.
    - exact AI'.
    - exact MI'.
    - exact MD.
    - exact LIVEB.
    - destruct OWN as [P0|[LVo BY]]; [left; exact P0| right]. split; [exact LVo|].
      intros i Hi. (first [ pose proof ((as_live_ok A M md owned plen AI0 LVo)) as dR_13; dand6 dR_13 as _ _ P1 HI IMG _ | destruct (as_live_ok A M md owned plen AI0 LVo) as (_ & _ & P1 & HI & IMG & _) ]).
      rewrite HCEIL in HI. cbn [al_image_lo al_image_hi LayoutPU] in IMG.
      rewrite OUTp by (rewrite u64 by lia; lia). apply BY. exact Hi.
    - (* [comment removed for export] *)
      assert (Z1 : forall x : word, (0x31a3c <= bv_unsigned x < 0x31a60)%Z -> M' x = M x) by (intros x Hx; apply AG; subst w; lia).
      assert (Z2 : forall x : word, (0x31a68 <= bv_unsigned x < 0x31b28)%Z -> M' x = M x) by (intros x Hx; apply AG; subst w; lia).
      assert (Z3 : forall x : word, (0x62bf8 <= bv_unsigned x < w)%Z -> M' x = M x) by (intros x Hx; apply AG; subst w; lia).
      split.
      + lia.
      + exact NF.
      + rewrite (rdn_zone M M' 0x31a3c 0x31a60 _ _ Z1) by lia. exact F2.
      + rewrite (rdn_zone M M' 0x31a3c 0x31a60 _ _ Z1) by lia. exact F3.
      + rewrite (rdn_zone M M' 0x31a3c 0x31a60 _ _ Z1) by lia. exact F4.
      + rewrite NW. subst w. rewrite Nat2Z.inj_succ. do 3 f_equal. lia.
      + rewrite (rdn_zone M M' 0x31a68 0x31b28 _ _ Z2) by lia. exact F6.
      + rewrite (rdn_zone M M' 0x31a68 0x31b28 _ _ Z2) by lia. exact F7.
      + rewrite (rdn_zone M M' 0x31a68 0x31b28 _ _ Z2) by lia. exact F8.
      + rewrite (rdn_zone M M' 0x31a68 0x31b28 _ _ Z2) by lia. exact F9.
      + rewrite (rdn_zone M M' 0x31a68 0x31b28 _ _ Z2) by lia. exact F10.
      + rewrite (rdn_zone M M' 0x31a68 0x31b28 _ _ Z2) by lia. exact F11.
      + rewrite (rdn_zone M M' 0x31a68 0x31b28 _ _ Z2) by lia. exact F12.
      + replace (2 * S nb)%nat with (2 * nb + 2)%nat by lia. rewrite zero_lines_S.
        apply rdn_app_Z; [| | lia| subst w; lia].
        * destruct nb as [|n]; [reflexivity|].
          rewrite (rdn_zone M M' 0x62bf8 w _ _ Z3) by (subst w; lia). exact F13.
        * replace (0x62bf8 + Z.of_nat (2 * nb))%Z with w by (subst w; lia). exact NB.
    - exact BUD.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dec_step : forall f j nb vals R M md A T,
    lp_st f (S j) nb vals R M md A -> getr R 19 = Z_to_bv 64 0 -> (Z.of_nat j < 1000)%Z ->
    (forall R', lp_st f j nb vals R' M md A ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (if Nat.eqb j 0 then 0x17f58 else 0x17f20)) M (seg_rom RSEGS)) md) T) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17f44) M (seg_rom RSEGS)) md) T.
  Proof.
    intros f j nb vals R M md A T ST H19 Hj K.
    pose proof ST as [HB V6 V20 V23 HK P2 P3 P4 P8 P9 P18 P20 P21 P22 P23 AI0 MI MD LIVEB OWN OUT]. pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    destruct (tr_dec R M (seg_rom RSEGS) j P21 Hj H19 P23) as (R' & MS & S5 & KEEP).
    replace (Z_to_bv 64 0x17f44) with (0x17f44 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Mh | exact Mlz | exact MS |].
    replace ((if Nat.eqb j 0 then 0x17f58 else 0x17f20) : word) with (Z_to_bv 64 (if Nat.eqb j 0 then 0x17f58 else 0x17f20))
      by (destruct (Nat.eqb j 0); apply bv_eq; reflexivity).
    apply K. split; try assumption; try (rewrite KEEP by (intros E; discriminate E); assumption).
  Qed.

  #[using="Hal Hplen Hlen LIBOK limg_intro limg Hlimg limg_hi limg_lo Htid HCEIL Hvsp"] Theorem tr_loop : forall j nb vals R M md A T,
    lp_st false (S j) nb vals R M md A -> (nb + S j <= 400)%nat ->
    (forall R' M' md' A', lp_st false 0 (nb + S j) vals R' M' md' A' ->
        rdn RSEGS M' (Z_to_bv 64 0x41ba4) 1%nat = Some [Z_to_bv 8 0] ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x17f58) M' (seg_rom RSEGS)) md') T) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17f20) M (seg_rom RSEGS)) md) T.
  Proof.
    intros j. induction j as [|j IH]; intros nb vals R M md A T ST Hb KEND.
    - apply (lib_part false 1 nb vals R M md A T ST). intros R1 M1 md1 A1 ST1 A0.
      apply (pf_next 1 nb vals R1 M1 md1 A1 T ST1 A0 ltac:(lia)). intros R2 M2 ST2 S19 INCB2.
      apply (dec_step false 0 (S nb) vals R2 M2 md1 A1 T ST2 S19 ltac:(lia)). intros R3 ST3. cbn [Nat.eqb].
      apply (KEND R3 M2 md1 A1); [| exact INCB2]. replace (nb + 1)%nat with (S nb) by lia. exact ST3.
    - apply (lib_part false (S (S j)) nb vals R M md A T ST). intros R1 M1 md1 A1 ST1 A0.
      apply (pf_next (S (S j)) nb vals R1 M1 md1 A1 T ST1 A0 ltac:(lia)). intros R2 M2 ST2 S19 INCB2.
      apply (dec_step false (S j) (S nb) vals R2 M2 md1 A1 T ST2 S19 ltac:(lia)). intros R3 ST3. cbn [Nat.eqb].
      apply (IH (S nb) vals R3 M2 md1 A1 T ST3 ltac:(lia)).
      intros R' M' md' A' ST' INCB'. apply (KEND R' M' md' A'); [| exact INCB']. replace (nb + S (S j))%nat with (S nb + S j)%nat by lia. exact ST'.
  Qed.

  #[using="Hal Hplen Hlen LIBOK limg_intro limg Hlimg limg_hi limg_lo Htid HCEIL Hvsp"] Theorem tr_entry : forall j vals R M md A T,
    lp_st true (S j) 0 vals R M md A -> (j <= 300)%nat -> T [] ->
    (forall R' M' md' A', lp_st false 0 j vals R' M' md' A' ->
        rdn RSEGS M' (Z_to_bv 64 0x41ba4) 1%nat = Some [Z_to_bv 8 0] ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x17f58) M' (seg_rom RSEGS)) md') T) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17f20) M (seg_rom RSEGS)) md)
             (t_emit [WriteEv (Z_to_bv 64 1) (Z_to_bv 8 48); WriteEv (Z_to_bv 64 1) (Z_to_bv 8 10)] T).
  Proof.
    intros j vals R M md A T ST Hj Tnil KEND.
    apply (lib_part true (S j) 0 vals R M md A _ ST). intros R1 M1 md1 A1 ST1 A0.
    apply (pf_first (S j) 0 vals R1 M1 md1 A1 T ST1 A0 Tnil). intros R2 M2 ST2 S19 INCB2.
    apply (dec_step false j 0 vals R2 M2 md1 A1 T ST2 S19 ltac:(lia)). intros R3 ST3.
    destruct j as [|j]; cbn [Nat.eqb].
    - apply (KEND R3 M2 md1 A1); [exact ST3 | exact INCB2].
    - apply (tr_loop j 0 vals R3 M2 md1 A1 T ST3 ltac:(lia)). intros R' M' md' A' ST' INCB'. apply (KEND R' M' md' A'); [exact ST' | exact INCB'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="payload Hvsp"] Lemma sr_le_ok : forall vals R,
    length vals = 70%nat -> vals_ev vals 0 = sp0 -> junk_at vals R ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 208) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x424f8 ->
    getr R 18 = vals_ev vals 23 -> getr R 22 = Z_to_bv 64 0 ->
    regs_ok (ENV a0s path rdraw vals) sr_le R.
  Proof.
    intros vals R HL V0 HJ P2 P3 P4 P18 P22.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_le all_regs];
      try (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
             change (edenot (ENV a0s path rdraw vals) (EVar n)) with (vals_ev vals n);
             first [ let i := eval vm_compute in (n - 38)%nat in
                     etransitivity; [| symmetry; exact (HJ i ltac:(lia))]; f_equal; apply bv_eq; reflexivity
                   | exact P18 ] end).
    - apply getr_zero.
    - rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. change (vals_ev vals 0) with (vals_ev vals 0). rewrite V0, P2. f_equal; lia.
    - exact P3.
    - exact P4.
    - exact P22.
  Qed.

  Lemma knL_vars22 : kn_vars_lt 22 knL = true. Proof. vm_compute. reflexivity. Qed.
  Lemma knTL_vars22' : kn_vars_lt 22 knTL = true. Proof. vm_compute. reflexivity. Qed.
  Lemma knL_free_incl : kn_incl knL (kn_keep2 knL (RS_call (-208) FREE_STACK) VICT ++ [kwr_data]) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma know_knL_free : forall E M',
    know_ok RSEGS E M' (kn_keep2 knL (RS_call (-208) FREE_STACK) VICT) -> know_ok RSEGS E M' knL.
  Proof.
    intros E M' HK. apply (know_ok_incl RSEGS E M' knL _ knL_free_incl).
    apply know_ok_app; [exact HK | constructor; [apply kwr_data_ok | constructor]].
  Qed.
  Lemma knL_tail_incl : kn_incl knTL knL = true. Proof. vm_compute. reflexivity. Qed.
  (* [comment removed for export] *)

  #[using="payload"] Lemma out_state_zone : forall nb M M',
    (forall x : word, dzone x -> M' x = M x) -> out_state nb M -> out_state nb M'.
  Proof.
    intros nb M M' AG [F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13].
    assert (Z1 : forall x : word, (0x10000 <= bv_unsigned x < 0x42454)%Z -> M' x = M x) by (intros x Hx; apply AG; unfold dzone; lia).
    assert (Z2 : forall x : word, (0x62ba4 <= bv_unsigned x < 0x64000)%Z -> M' x = M x) by (intros x Hx; apply AG; unfold dzone; lia).
    split; rewrite ?(rdn_zone M M' 0x10000 0x42454 _ _ Z1) by lia; try assumption.
    rewrite (rdn_zone M M' 0x62ba4 0x64000 _ _ Z2) by lia. exact F13.
  Qed.

  (* [comment removed for export] *)
  #[using="Hpc Hal HCEIL Hvsp"] Theorem tr_exit : forall nb vals R M md A (cnt : bool),
    lp_st false 0 nb vals R M md A -> rdn RSEGS M (Z_to_bv 64 0x41ba4) 1%nat = Some [Z_to_bv 8 0] -> (nb <= 8)%nat ->
    branch_taken BC_LT v6 (Z_to_bv 64 0) = cnt ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17f58) M (seg_rom RSEGS)) md)
             (t_emit (W 1 (zero_lines nb)) (t_exit (exit_code 0) fs0)).
  Proof.
    intros nb vals R M md A cnt ST INCB Hnb Hcnt.
    pose proof ST as [HB V6 V20 V23 HK0 P2 P3 P4 P8 P9 P18 P20 P21 P22 P23 AI0 MI MD LIVEB OWN OUT].
    (first [ pose proof (HB) as dR_15; dand5 dR_15 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]). pose proof MD as [Mfs Mfd1 Mfd2 Mh Mlz].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    set (valsE := rebase vals 23 (Z_to_bv 64 owned) R).
    assert (HLv : (NB <= length vals)%nat) by (rewrite HL; unfold NB; lia).
    assert (HLE : length valsE = 70%nat) by (subst valsE; apply rebase_length; [exact HLv| unfold NB; lia]).
    assert (AGE : forall j, (j < NB)%nat -> vals_ev valsE j = vals_ev vals j).
    { intros j Hj. destruct (Nat.eq_dec j 23) as [->|Hne]; subst valsE; [rewrite rebase_at by (assumption || (unfold NB; lia)); symmetry; exact V23|].
      apply rebase_lt; [exact HLv| unfold NB; lia| exact Hj| exact Hne]. }
    assert (HBE : base_ok sp0 a0s path envv tid valsE) by (split; [exact HLE|]; rewrite !AGE by (unfold NB; lia); OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption).
    assert (HR : regs_ok (ENV a0s path rdraw valsE) sr_le R).
    { apply (sr_le_ok valsE R HLE); rewrite ?AGE by (unfold NB; lia); try assumption.
      - subst valsE. apply rebase_junk; [exact HLv| unfold NB; lia].
      - rewrite V23. exact P18. }
    assert (HK : know_ok RSEGS (ENV a0s path rdraw valsE) M knL).
    { apply (know_ok_agree RSEGS 22 (ENV a0s path rdraw vals)); [| exact knL_vars22 | exact HK0].
      split; [|reflexivity]. intros i Hi. cbn [ev ENV]. symmetry. apply AGE. unfold NB. lia. }
    clear HK0.
    (* [comment removed for export] *)
    run_block_gen FUEL_X STOPS_X (SCR [] [] []) 70%nat true.
    cbn [mem_denot] in EQM. subst M0.
    assert (CH : callH valsE (blobs_ev (blobs0 a0s path rdraw)) srE0 knL owned (-208) 0x17f60).
    { split; rewrite ?HLE, ?AGE by (unfold NB; lia); rewrite ?V0; try reflexivity; try lia.
      - change (sr_get srE0 10) with (EVar 23). cbn [edenot ev]. rewrite AGE by (unfold NB; lia). exact V23.
      - exists knL_iw. exact knL_win. }
    assert (HP : (owned = 0 /\ plen = 0)%Z \/ a_live A owned = Some plen).
    { destruct OWN as [P0|[LV _]]; [| right; exact LV]. destruct Hal as [[_ [_ O0]]|[Hp _]]; [left; lia| lia]. }
    apply (W_free_as valsE (blobs_ev (blobs0 a0s path rdraw)) srE0 knL R0 M md A owned plen (-208) 0x17f60 _ HR HK CH AI0
             ltac:(destruct HP as [[A1 A2]|A3]; [left; lia| right; exact A3]) MI).
    clear HR HK. intros R1 M1 md1 A1 HR HK1 AI1 MI1 MF1 GONE1 OTHER1 _ _ FR1.   (* [comment removed for export] *)
    pose proof (know_knL_free _ M1 HK1) as HK. clear HK1.
    rewrite HLE in HR. change (sr_post srE0 70) with srE1_0 in HR.
    rewrite AGE, V0 in FR1 by (unfold NB; lia).
    assert (DZ : forall x : word, dzone x -> M1 x = M x).
    { apply (dzone_acall sp0 Hvsp HCEIL (AllocSpec.owned A) (AllocSpec.owned A1) valsE (blobs_ev (blobs0 a0s path rdraw)) (-208) (blk owned plen) nowhere M M1);
        rewrite ?AGE by (unfold NB; lia); try exact V0; try exact FR1; try lia.
      - intros a Ho. exact (owned_azone A M md a AI0 Ho).
      - intros a Ho. exact (owned_azone A1 M1 md1 a AI1 Ho).
      - intros a [Hz Ha]. destruct HP as [[O0 _]|LV]; [lia|]. replace a with (owned + (a - owned))%Z by lia.
        eapply (live_azone A M md owned plen); [exact AI0| exact LV| lia].
      - intros a Hn. destruct Hn. }
    pose proof (out_state_zone nb M M1 DZ OUT) as OUT1.
    set (vals1 := valsE ++ junk_vals R1) in *.
    assert (HL1 : length vals1 = 102%nat) by (subst vals1; rewrite length_app, junk_vals_length, HLE; reflexivity).
    assert (AG1 : forall i, (i < 70)%nat -> vals_ev vals1 i = vals_ev valsE i) by (intros i Hi; subst vals1; apply vals_ev_app_l; rewrite HLE; exact Hi).
    assert (Hh1 : m_halted md1 = None) by (destruct (as_lazy_nil A1 M1 md1 AI1) as [_ X]; exact X).
    assert (Hl1 : m_vm_lazy md1 = []) by (destruct (as_lazy_nil A1 M1 md1 AI1) as [X _]; exact X).
    (* [comment removed for export] *)
    assert (Hbo : b <> owned).
    { intros ->. destruct HP as [[O0 _]|LV].
      - (first [ pose proof ((as_live_ok A M md owned capk AI0 LIVEB)) as dR_16; dand4 dR_16 as _ _ P1 _ | destruct (as_live_ok A M md owned capk AI0 LIVEB) as (_ & _ & P1 & _) ]). lia.
      - rewrite LIVEB in LV. injection LV. lia. }
    assert (LIVEB1 : a_live A1 b = Some capk) by (rewrite (OTHER1 b Hbo); exact LIVEB).
    assert (FC2 : file_clean M1 0x31948 (Z_to_bv 64 0) (Z_to_bv 64 0)) by (unfold file_clean; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; krd_solve HK).
    (* [comment removed for export] *)
    assert (ATX : atexit_st M1 true).
    { unfold atexit_st. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [krd_solve HK| krd_solve HK| krd_solve HK| krd_solve HK| krd_solve HK|].
      rewrite (rdn_zone M M1 0x10000 0x42454 0x41ba4 1 ltac:(intros x Hx; apply DZ; unfold dzone; lia)) by lia. exact INCB. }
    assert (SSP : ssp_cells M1 CANW) by (unfold CANW; split; krd_solve HK).
    assert (FD1 : fd_lookup (m_fds md1) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))).
    { destruct MF1 as (FD & _). unfold m_fds. rewrite FD. exact Mfd1. }
    replace fs0 with (m_fs md1).
    2:{ (first [ dand4 MF1 as _ _ FS _ | destruct MF1 as (_ & _ & FS & _) ]). unfold m_fs. rewrite FS. exact Mfs. }
    assert (TAIL : forall R2 sr, regs_ok (ENV a0s path rdraw vals1) sr R2 ->
              sr_get sr 2 = EAlu ALU_ADD (EVar 0) (ELit (-128)) -> sr_get sr 3 = ELit 0x10800 -> sr_get sr 4 = ELit 0x424f8 ->
              sr_get sr 8 = ELit 0 -> sr_get sr 9 = EVar 20 ->
              realizes RSEGS (mkCfg (mkst R2 (Z_to_bv 64 0x17d8c) M1 (seg_rom RSEGS)) md1)
                       (t_emit (W 1 (zero_lines nb)) (t_exit (exit_code 0) (m_fs md1)))).
    { intros R2 sr HR2 G2 G3 G4 G8 G9.
      set (valsX := rebase vals1 24 (Z_to_bv 64 0) R2).
      assert (HLX : (NB <= length vals1)%nat) by (rewrite HL1; unfold NB; lia).
      assert (AGX : forall j, (j < NB)%nat -> j <> 24%nat -> vals_ev valsX j = vals_ev valsE j).
      { intros j Hj Hne. subst valsX. rewrite rebase_lt by (assumption || (unfold NB; lia)). apply AG1. unfold NB in Hj. lia. }
      apply (tail_exit sp0 a0s path envv rdraw tid Hvsp HCEIL valsX R2 M1 md1 A1 b capk 0 (Z_to_bv 64 0) (Z_to_bv 64 0) (zero_lines nb) true).
      - split; [apply rebase_length; [exact HLX| unfold NB; lia]|]. rewrite !AGX, !AGE by (unfold NB; lia). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
      - apply rebase_junk; [exact HLX| unfold NB; lia].
      - rewrite (HR2 (2%bv : reg)), G2. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite AG1, AGE, V0 by (unfold NB; lia). f_equal; lia.
      - rewrite (HR2 (3%bv : reg)), G3. reflexivity.
      - rewrite (HR2 (4%bv : reg)), G4. reflexivity.
      - rewrite AGX, AGE by (unfold NB; lia). exact V20.
      - subst valsX. apply rebase_at; [exact HLX| unfold NB; lia].
      - lia.
      - rewrite (HR2 (8%bv : reg)), G8. reflexivity.
      - rewrite (HR2 (9%bv : reg)), G9. cbn [edenot ev ENV]. rewrite AG1, AGE by (unfold NB; lia). exact V20.
      - apply (know_ok_agree RSEGS 22 (ENV a0s path rdraw vals1)).
        + split; [|reflexivity]. intros i Hi. cbn [ev ENV]. subst valsX. rewrite rebase_lt by (assumption || (unfold NB; lia)). reflexivity.
        + exact knTL_vars22'.
        + apply (know_ok_incl RSEGS _ M1 knTL knL knL_tail_incl). exact HK.
      - exact AI1.
      - exact LIVEB1.
      - exact MI1.
      - exact FC2.
      - exact ATX.
      - destruct OUT1 as [F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13].
        destruct nb as [|n].
        + left. split; [reflexivity|]. exists (Z_to_bv 64 0x62bf8), (Z_to_bv 64 0). unfold file_clean.
          change (0x62bf8 + 2 * Z.of_nat 0)%Z with 0x62bf8%Z in F5.
          OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
        + right. exists 0x62bf8%Z, (0x62bf8 + 2 * Z.of_nat (S n))%Z, (Z_to_bv 64 0x62bf8), (Z_to_bv 64 1024), (Z_to_bv 64 0), CANW.
          split; [|split; [lia| exact FD1]].
          split; try assumption.
          * lia.
          * rewrite zero_lines_length. lia.
          * rewrite zero_lines_length. pose proof rw_bytes_max_ge17. lia.
          * rewrite zero_lines_length. exact F13. }
    destruct cnt.
    - run_block_gen FUEL_X STOPS_X (SCR [true] [] []) 102%nat true.
      { cbn [sc_denot edenot ev ENV]. rewrite AG1, AGE by (unfold NB; lia). rewrite V6. exact Hcnt. }
      cbn [mem_denot] in EQM. subst M0.
      eapply (TAIL R2); [exact HR| reflexivity ..].
    - run_block_gen FUEL_X STOPS_X (SCR [false] [] []) 102%nat true.
      { cbn [sc_denot edenot ev ENV]. rewrite AG1, AGE by (unfold NB; lia). rewrite V6. exact Hcnt. }
      cbn [mem_denot] in EQM. subst M0.
      eapply (TAIL R2); [exact HR| reflexivity ..].
  Qed.
End Loop.
