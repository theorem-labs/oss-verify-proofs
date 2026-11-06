(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA LibcKit Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PP_kit2A F_pp_ctxA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pp_BA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pp_DA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_ctxA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_BA__A3P.F_pp_BA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_BA__A3P.F_pp_CA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_BA__A3P.F_pp_LA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_BA__A3P.F_pp_FA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_DA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_BA__A3P.F_pp_EA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
(* [comment removed for export] *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in let X := leftmost E in
      lazymatch X with
      | bv_unsigned _ => match goal with H : rng RNG ?lo ?len |- _ => first [ mentions len X | mentions lo X ]; solve_acc_with H end
      end
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

Lemma h_caplen_fixup : forall h d, h_caplen (fixup_usb_mmapped_len h d) = h_caplen h.
Proof.
  intros h d. unfold fixup_usb_mmapped_len.
  destruct (_ <? 64); [reflexivity|]. destruct (_ <? _); [reflexivity|].
  destruct (_ && _); [|reflexivity]. destruct (_ <? _); [reflexivity|].
  destruct (_ <=? _); destruct (_ <? _); reflexivity.
Qed.

Lemma h_len_fixup_irrel : forall a b a' b' c l d,
  h_len (fixup_usb_mmapped_len (mkHdr a b c l) d) = h_len (fixup_usb_mmapped_len (mkHdr a' b' c l) d).
Proof.
  intros. unfold fixup_usb_mmapped_len. cbn [h_caplen h_len h_sec h_usec].
  destruct (_ <? 64); [reflexivity|]. destruct (_ <? _); [reflexivity|].
  destruct (_ && _); [|reflexivity]. destruct (_ <? _); [reflexivity|].
  unfold incoming_isochronous_transfer_completed_len. cbn [h_caplen].
  destruct (_ <=? _); cbn [h_len h_caplen h_sec h_usec]; destruct (_ <? _); reflexivity.
Qed.

(* [comment removed for export] *)
Ltac pp_model := unfold pcapint_post_process, swap_pseudo_headers, DLT_PFLOG, DLT_LINUX_SLL, DLT_LINUX_SLL2,
                        DLT_USB_LINUX, DLT_USB_LINUX_MMAPPED, DLT_NFLOG; cbn [Z.eqb Pos.eqb].
(* [comment removed for export] *)
Ltac pp_model_other := unfold pcapint_post_process, swap_pseudo_headers, DLT_PFLOG, DLT_LINUX_SLL, DLT_LINUX_SLL2,
                        DLT_USB_LINUX, DLT_USB_LINUX_MMAPPED, DLT_NFLOG;
  repeat match goal with |- context [?l =? ?k] => replace (l =? k) with false by (symmetry; apply Z.eqb_neq; lia) end;
  cbv iota.

Ltac close_inv := unfold ppinv; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].

(* [comment removed for export] *)
Ltac pp_init' := lazymatch goal with I : ppinv ?c ?m ?d ?h |- _ =>
  repeat match goal with H : rw_cells _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
                       | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
                       | H : wr_at _ _ _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H | H : unpoisoned _ _ _ |- _ => clear H
                       | H : length _ = _ |- _ => clear H end;
  open_inv I; unfold c in *;
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo c_RNG] in * end.

Ltac pp_ret' :=
  lazymatch goal with FR : rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _], ST : stk _ _ _ (bv_unsigned ?spv + -32) |- _ =>
    release_frame FR ST (bv_unsigned spv) end;
  apply evtF_done; unfold ppost;
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo FOOT];
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [cbv delta [mkR]; reflexivity|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
  repeat match goal with |- _ /\ _ => split end;
  lazymatch goal with
  | |- zarr _ _ _ => split; [|split]; hyp_by_addr
  | |- _ => first [hyp_by_addr | assumption]
  end.

(* [comment removed for export] *)
Local Ltac bdecide_T := try lstep; first [btrue | bfalse].
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

#[using="Type"] Theorem post_process_proof : post_process_stmt.
Proof.
  unfold post_process_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HA DA ws wu linktype swapped hdr d lo.
  intros ST LO LOA HDR ZA MI RT -> -> -> -> LT CAP LEN HL OH OD HAT DAT SEP AL1 AL2 RSTK RIMG RIMGSH.
  destruct hdr as [hs hu caplen len0]. cbn [h_caplen h_len] in *. unfold PP_FRAME, PP_ENTRY, PCAP_POST_PROCESS_ENTRY in *.
  destruct OH as (H0 & _ & UNPH & RHA & RHS & _ & BLKH). destruct OD as (D0 & _ & UNPD & RDA & RDS & _ & BLKD).
  band_ind BLKH bH. band_ind BLKD bD.
  set (c := mkPP sp gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HA DA ws wu caplen len0 (length d) lo RNG bH bD).
  assert (WF : ppwf c).
  { unfold ppwf, c; cbn [c_caplen c_N c_len0 c_lo c_sp c_HA c_DA c_bH c_bD c_RNG c_m0].
    rewrite AL1, Z.sub_0_r, Z.add_0_r in RHS.
    replace (shad (DA - DA mod 8)) with (shad DA) in RDS by (rewrite !shad_div; Z.div_mod_to_equations; lia).
    repeat match goal with |- _ /\ _ => split end; first [ assumption | lia ]. }
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (@ATOP_hi _) as ATOPhi.
  destruct ZA as (ZB & ZW & ZR).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (HA + 20, HA + 24); (DA, DA + caplen)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold pkthdr_cells in HDR. cbn [h_caplen h_len] in HDR.
  pose proof (zbytes_length d) as LZ.
  pose proof RT as RT'. destruct RT' as (_ & GOT & _ & _ & SHB & _).
  carve_frame 32%nat ST.
  do 5 lstep. do 3 lstep.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (I : ppinv c mm d len0) by close_inv end.
  (* [comment removed for export] *)
  assert (K : forall hdr' d' ms', h_caplen hdr' = caplen ->
            pcapint_post_process linktype swapped (mkHdr hs hu caplen len0) d = (hdr', d') ->
            ppost c (h_len hdr') d' ms' ->
            post_process_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HA DA ws wu linktype swapped
              (mkHdr hs hu caplen len0) d lo m ms').
  { intros hdr' d' ms' HC PP P.
    destruct P as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & m' & -> & -> & -> & -> & P).
    destruct P as (MU' & WM' & MI' & ST' & HDR' & ZA').
    unfold post_process_post. rewrite PP. cbn [fst snd h_caplen]. unfold PP_FRAME, pkthdr_cells. rewrite HC.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. }
  (* [comment removed for export] *)
  Ltac branch HDR' D' HL BR K :=
    lazymatch goal with I : ppinv ?c _ _ _ |- evtF _ ?RNG _ _ => apply (evtF_mono asegs RNG (ppost c HL D')) end;
    [ BR
    | let ms' := fresh "ms'" in let Pm := fresh "Pm" in
      intros ms' Pm; eapply (K HDR' D'); [ | | first [exact Pm | erewrite (h_len_fixup_irrel _ _ 0 0); exact Pm] ] ].
  destruct swapped; cbn [Z.b2z].
  - (* [comment removed for export] *)
    bdecide_T. run.
    destruct (Z.ltb_spec 219 linktype) as [GT|LE].
    + bdecide_T. run. destruct (Z.eqb_spec linktype 220) as [->|N220].
      * bdecide_T.
        set (D := swap_linux_usb_header (mkHdr 0 0 caplen len0) d true).
        branch (fixup_usb_mmapped_len (mkHdr hs hu caplen len0) D) D (h_len (fixup_usb_mmapped_len (mkHdr 0 0 caplen len0) D))
               ltac:(eapply (usbmm_spec c WF); first [exact I | reflexivity]) K.
        { apply h_caplen_fixup. } { pp_model. reflexivity. }
      * bdecide. run. destruct (Z.eqb_spec linktype 239) as [->|N239].
        -- bdecide_T.
           branch (mkHdr hs hu caplen len0) (swap_nflog_header (mkHdr 0 0 caplen len0) d) len0
                  ltac:(eapply (nflog_spec c WF); first [exact I | reflexivity]) K.
           { reflexivity. } { pp_model. reflexivity. }
        -- bdecide. run. destruct (Z.eqb_spec linktype 276) as [->|N276].
           ++ bdecide.
              branch (mkHdr hs hu caplen len0) (swap_linux_sll2_socketcan_header (mkHdr 0 0 caplen len0) d) len0
                     ltac:(eapply (sll2_spec c WF); first [exact I | reflexivity]) K.
              { reflexivity. } { pp_model. reflexivity. }
           ++ bdecide_T.
              branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 5 lstep; repeat lstep; pp_ret') K.
              { reflexivity. } { pp_model_other. reflexivity. }
    + bdecide. run. destruct (Z.eqb_spec linktype 113) as [->|N113].
      * bdecide_T.
        branch (mkHdr hs hu caplen len0) (swap_linux_sll_socketcan_header (mkHdr 0 0 caplen len0) d) len0
               ltac:(eapply (sll_spec c WF); first [exact I | reflexivity]) K.
        { reflexivity. } { pp_model. reflexivity. }
      * bdecide. run. destruct (Z.eqb_spec linktype 117) as [->|N117].
        -- bdecide_T.
           branch (mkHdr hs hu caplen len0) (swap_pflog_header (mkHdr 0 0 caplen len0) d) len0
                  ltac:(eapply (pflog_spec c WF); first [exact I | reflexivity]) K.
           { reflexivity. } { pp_model. reflexivity. }
        -- bdecide. run. destruct (Z.eqb_spec linktype 189) as [->|N189].
           ++ bdecide.
              branch (mkHdr hs hu caplen len0) (swap_linux_usb_header (mkHdr 0 0 caplen len0) d false) len0
                     ltac:(eapply (usb_spec c WF); first [exact I | reflexivity]) K.
              { reflexivity. } { pp_model. reflexivity. }
           ++ bdecide_T.
              branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 5 lstep; repeat lstep; pp_ret') K.
              { reflexivity. } { pp_model_other. reflexivity. }
  - (* [comment removed for export] *)
    bdecide. lstep. destruct (Z.eqb_spec linktype 220) as [->|N220].
    + branch (fixup_usb_mmapped_len (mkHdr hs hu caplen len0) d) d (h_len (fixup_usb_mmapped_len (mkHdr 0 0 caplen len0) d))
             ltac:(eapply (fixup_spec' c WF); first [exact I | reflexivity]) K.
      { apply h_caplen_fixup. } { pp_model. reflexivity. }
    + run. bdecide_T.
      branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 5 lstep; repeat lstep; pp_ret') K.
      { reflexivity. } { pp_model_other. reflexivity. }
Qed.

End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_pp_BA__B3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_pp_CA.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StrwF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PP_kit2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pp_ctxA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_pp_BA__B3P.F_pp_BA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_pp_CA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_pp_BA__B3P.F_pp_LA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_pp_BA__B3P.F_pp_FA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_pp_BA__B3P.F_pp_DA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_pp_BA__B3P.F_pp_EA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
(* [comment removed for export] *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in let X := leftmost E in
      lazymatch X with
      | bv_unsigned _ => match goal with H : rng RNG ?lo ?len |- _ => first [ mentions len X | mentions lo X ]; solve_acc_with H end
      end
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

Lemma h_caplen_fixup : forall h d, h_caplen (fixup_usb_mmapped_len h d) = h_caplen h.
Proof.
  intros h d. unfold fixup_usb_mmapped_len.
  destruct (_ <? 64); [reflexivity|]. destruct (_ <? _); [reflexivity|].
  destruct (_ && _); [|reflexivity]. destruct (_ <? _); [reflexivity|].
  destruct (_ <=? _); destruct (_ <? _); reflexivity.
Qed.

Lemma h_len_fixup_irrel : forall a b a' b' c l d,
  h_len (fixup_usb_mmapped_len (mkHdr a b c l) d) = h_len (fixup_usb_mmapped_len (mkHdr a' b' c l) d).
Proof.
  intros. unfold fixup_usb_mmapped_len. cbn [h_caplen h_len h_sec h_usec].
  destruct (_ <? 64); [reflexivity|]. destruct (_ <? _); [reflexivity|].
  destruct (_ && _); [|reflexivity]. destruct (_ <? _); [reflexivity|].
  unfold incoming_isochronous_transfer_completed_len. cbn [h_caplen].
  destruct (_ <=? _); cbn [h_len h_caplen h_sec h_usec]; destruct (_ <? _); reflexivity.
Qed.

(* [comment removed for export] *)
Ltac pp_model := unfold pcapint_post_process, swap_pseudo_headers, DLT_PFLOG, DLT_LINUX_SLL, DLT_LINUX_SLL2,
                        DLT_USB_LINUX, DLT_USB_LINUX_MMAPPED, DLT_NFLOG; cbn [Z.eqb Pos.eqb].
(* [comment removed for export] *)
Ltac pp_model_other := unfold pcapint_post_process, swap_pseudo_headers, DLT_PFLOG, DLT_LINUX_SLL, DLT_LINUX_SLL2,
                        DLT_USB_LINUX, DLT_USB_LINUX_MMAPPED, DLT_NFLOG;
  repeat match goal with |- context [?l =? ?k] => replace (l =? k) with false by (symmetry; apply Z.eqb_neq; lia) end;
  cbv iota.

Ltac close_inv := unfold ppinv; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].

(* [comment removed for export] *)
Ltac pp_init' := lazymatch goal with I : ppinv ?c ?m ?d ?h |- _ =>
  repeat match goal with H : rw_cells _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H
                       | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
                       | H : wr_at _ _ _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H | H : unpoisoned _ _ _ |- _ => clear H
                       | H : length _ = _ |- _ => clear H end;
  open_inv I; unfold c in *;
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo c_RNG c_junk] in * end.

Ltac pp_ret' :=
  lazymatch goal with FR : rw_cells _ _ _ [CB 8 _; C8 _; C8 _; C8 _; C8 _; C8 _], ST : stk _ _ _ (bv_unsigned ?spv + -48) |- _ =>
    release_frame FR ST (bv_unsigned spv) end;
  apply evtF_done; unfold ppost;
  cbn [c_sp c_gp c_tp c_ra c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m0 c_HA c_DA c_ws c_wu c_caplen c_len0 c_N c_lo c_junk FOOT];
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [cbv delta [mkR]; reflexivity|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
  repeat match goal with |- _ /\ _ => split end;
  lazymatch goal with
  | |- zarr _ _ _ => split; [|split]; hyp_by_addr
  | |- _ => first [hyp_by_addr | assumption]
  end.

(* [comment removed for export] *)
Local Ltac bdecide_T := try lstep; first [btrue | bfalse].
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

#[using="Type"] Theorem post_process_proof : post_process_stmt.
Proof.
  unfold post_process_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m RNG HA DA ws wu linktype swapped hdr d lo.
  intros ST LO LOA HDR ZA MI RT -> -> -> -> LT CAP LEN HL OH OD HAT DAT SEP AL1 AL2 RSTK RIMG RIMGSH.
  destruct hdr as [hs hu caplen len0]. cbn [h_caplen h_len] in *. unfold PP_FRAME, PP_ENTRY, PCAP_POST_PROCESS_ENTRY in *.
  destruct OH as (H0 & _ & UNPH & RHA & RHS & _ & BLKH). destruct OD as (D0 & _ & UNPD & RDA & RDS & _ & BLKD).
  band_ind BLKH bH. band_ind BLKD bD.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (@ATOP_hi _) as ATOPhi.
  destruct ZA as (ZB & ZW & ZR).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (HA + 20, HA + 24); (DA, DA + caplen)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold pkthdr_cells in HDR. cbn [h_caplen h_len] in HDR.
  pose proof (zbytes_length d) as LZ.
  pose proof RT as RT'. destruct RT' as (_ & GOT & _ & _ & SHB & _).
  carve_frame 48%nat ST.
  do 6 lstep. do 3 lstep.
  (* [comment removed for export] *)
  lazymatch goal with FR : rw_cells _ ?m1 _ [CB 8 ?jk; C8 _; C8 _; C8 _; C8 _; C8 _] |- _ =>
    set (c := mkPP sp gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m HA DA ws wu caplen len0 (length d) lo RNG bH bD jk) end.
  assert (WF : ppwf c).
  { unfold ppwf, c; cbn [c_caplen c_N c_len0 c_lo c_sp c_HA c_DA c_bH c_bD c_RNG c_m0].
    rewrite AL1, Z.sub_0_r, Z.add_0_r in RHS.
    replace (shad (DA - DA mod 8)) with (shad DA) in RDS by (rewrite !shad_div; Z.div_mod_to_equations; lia).
    repeat match goal with |- _ /\ _ => split end; first [ assumption | lia ]. }
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (I : ppinv c mm d len0) by close_inv end.
  (* [comment removed for export] *)
  assert (K : forall hdr' d' ms', h_caplen hdr' = caplen ->
            pcapint_post_process linktype swapped (mkHdr hs hu caplen len0) d = (hdr', d') ->
            ppost c (h_len hdr') d' ms' ->
            post_process_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HA DA ws wu linktype swapped
              (mkHdr hs hu caplen len0) d lo m ms').
  { intros hdr' d' ms' HC PP P.
    destruct P as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & m' & -> & -> & -> & -> & P).
    destruct P as (MU' & WM' & MI' & ST' & HDR' & ZA').
    unfold post_process_post. rewrite PP. cbn [fst snd h_caplen]. unfold PP_FRAME, pkthdr_cells. rewrite HC.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. }
  (* [comment removed for export] *)
  Ltac branch HDR' D' HL BR K :=
    lazymatch goal with I : ppinv ?c _ _ _ |- evtF _ ?RNG _ _ => apply (evtF_mono asegs RNG (ppost c HL D')) end;
    [ BR
    | let ms' := fresh "ms'" in let Pm := fresh "Pm" in
      intros ms' Pm; eapply (K HDR' D'); [ | | first [exact Pm | erewrite (h_len_fixup_irrel _ _ 0 0); exact Pm] ] ].
  destruct swapped; cbn [Z.b2z].
  - (* [comment removed for export] *)
    bdecide. run.
    destruct (Z.ltb_spec 219 linktype) as [GT|LE].
    + bdecide_T. run. destruct (Z.eqb_spec linktype 220) as [->|N220].
      * bdecide_T.
        set (D := swap_linux_usb_header (mkHdr 0 0 caplen len0) d true).
        branch (fixup_usb_mmapped_len (mkHdr hs hu caplen len0) D) D (h_len (fixup_usb_mmapped_len (mkHdr 0 0 caplen len0) D))
               ltac:(eapply (usbmm_spec c WF); first [exact I | reflexivity]) K.
        { apply h_caplen_fixup. } { pp_model. reflexivity. }
      * bdecide. run. destruct (Z.eqb_spec linktype 239) as [->|N239].
        -- bdecide_T.
           branch (mkHdr hs hu caplen len0) (swap_nflog_header (mkHdr 0 0 caplen len0) d) len0
                  ltac:(eapply (nflog_spec c WF); first [exact I | reflexivity]) K.
           { reflexivity. } { pp_model. reflexivity. }
        -- bdecide. run. destruct (Z.eqb_spec linktype 276) as [->|N276].
           ++ bdecide.
              branch (mkHdr hs hu caplen len0) (swap_linux_sll2_socketcan_header (mkHdr 0 0 caplen len0) d) len0
                     ltac:(eapply (sll2_spec c WF); first [exact I | reflexivity]) K.
              { reflexivity. } { pp_model. reflexivity. }
           ++ bdecide_T.
              branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 5 lstep; repeat lstep; pp_ret') K.
              { reflexivity. } { pp_model_other. reflexivity. }
    + bdecide. run. destruct (Z.eqb_spec linktype 113) as [->|N113].
      * bdecide_T.
        branch (mkHdr hs hu caplen len0) (swap_linux_sll_socketcan_header (mkHdr 0 0 caplen len0) d) len0
               ltac:(eapply (sll_spec c WF); first [exact I | reflexivity]) K.
        { reflexivity. } { pp_model. reflexivity. }
      * bdecide. run. destruct (Z.eqb_spec linktype 117) as [->|N117].
        -- bdecide_T.
           branch (mkHdr hs hu caplen len0) (swap_pflog_header (mkHdr 0 0 caplen len0) d) len0
                  ltac:(eapply (pflog_spec c WF); first [exact I | reflexivity]) K.
           { reflexivity. } { pp_model. reflexivity. }
        -- bdecide. run. destruct (Z.eqb_spec linktype 189) as [->|N189].
           ++ bdecide.
              branch (mkHdr hs hu caplen len0) (swap_linux_usb_header (mkHdr 0 0 caplen len0) d false) len0
                     ltac:(eapply (usb_spec c WF); first [exact I | reflexivity]) K.
              { reflexivity. } { pp_model. reflexivity. }
           ++ bdecide_T.
              branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 5 lstep; repeat lstep; pp_ret') K.
              { reflexivity. } { pp_model_other. reflexivity. }
  - (* [comment removed for export] *)
    bdecide_T. destruct (Z.eqb_spec linktype 220) as [->|N220].
    + branch (fixup_usb_mmapped_len (mkHdr hs hu caplen len0) d) d (h_len (fixup_usb_mmapped_len (mkHdr 0 0 caplen len0) d))
             ltac:(eapply (fixup_spec' c WF); first [exact I | reflexivity]) K.
      { apply h_caplen_fixup. } { pp_model. reflexivity. }
    + run. bdecide_T.
      branch (mkHdr hs hu caplen len0) d len0 ltac:(pp_init' ; do 5 lstep; repeat lstep; pp_ret') K.
      { reflexivity. } { pp_model_other. reflexivity. }
Qed.

End CANSEC1.
End TwB.
