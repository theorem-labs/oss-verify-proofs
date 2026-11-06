(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr SysStep ITree Nodes Decode ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_printf_iface F_printf_core_common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma zb_to_bytes : forall l, zb l = to_bytes l.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land32_lowbyte : forall x, 0 <= x -> Z.land x 32 = 0 -> Z.land (x mod 256) 32 = 0.
Proof.
  intros x Hx H. change 256 with (2^8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm x (Z.ones 8)), <- Z.land_assoc, H. apply Z.land_0_r.
Qed.

Section FileSink.
  Context {St : Type}.
  (* [comment removed for export] *)
  Variables (Fp B bs : Z) (rpos rend closefn readfn seekfn prev next : Z) (tail : list byte).
  (* [comment removed for export] *)
  Variable sw0 : bool.
  (* [comment removed for export] *)
  Variable ch0 : bool.
  (* [comment removed for export] *)
  Variable st0 : St.

  (* [comment removed for export] *)
  Definition fsink_inv (f : file_st) : Prop :=
    f_wactive f = true /\ f_rbuf f = [] /\ f_bufsize f = bs /\ f_nowr f = false
    /\ (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31))
    /\ (f_stdoutw f = true -> sw0 = true) /\ f_chan f = ch0.

  Definition SINK_file (m : mem) (fs : file_st * St) : Prop :=
    let f := fst fs in
    snd fs = st0 /\ fsink_inv f /\
    exists (flags mode : word) (bufbytes : list byte),
      rw_cells ssegs m Fp (fcells flags rpos rend closefn (B + bs) (B + zlength (f_wbuf f)) B readfn (wfn_of f) seekfn B bs prev next (f_fd f) mode (lbf_of f) tail)
      /\ flags_ok f flags
      /\ rw_cells ssegs m B [CB (Z.to_nat bs) bufbytes]
      /\ firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f)
      /\ zlength (f_wbuf f) <= bs.

  (* [comment removed for export] *)
  Definition TOPOK_file (sp : Z) : Prop := True.

  (* [comment removed for export] *)
  Definition PIECE_MAX : Z := 2^26 - 1024.
  Definition OUT_file (s : list Z) : M (file_st * St) unit :=
    fun fs => if zlength s <=? PIECE_MAX
              then ebind (fwritex (fst fs) s (snd fs)) (fun r => ITree.Ret (Ok (tt, (fst r, snd r))))
              else ITree.Ret Unr.

  (* [comment removed for export] *)
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis B0 : 0 < B.
  Hypothesis BS0 : 0 <= bs <= 1024.
  Hypothesis BShi : B + bs <= 2^47.   (* [comment removed for export] *)
  Hypothesis Fphi : Fp + 232 < 2^63.
  Hypothesis FB : B + bs <= Fp \/ Fp + 232 <= B.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis TL : firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8.

  Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
    Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
  Proof using BS0 BSEP1 BSEP2 FB FSEP1 FSEP2. pin_using (fun (BS0 BSEP1 BSEP2 FB FSEP1 FSEP2 : unit) => tt).
    intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
  Qed.

  Lemma file_sink_frame : sink_frame_stmt Fp 232 B bs SINK_file.
  Proof using BS0 BSEP1 BSEP2 FB FSEP1 FSEP2. pin_using (fun (BS0 BSEP1 BSEP2 FB FSEP1 FSEP2 : unit) => tt).
    unfold sink_frame_stmt. intros W m m' [f st] (EST & INV & flags & mode & bufbytes & FC & FL & BUF & BP & WBL) MU WM D1 D2. cbn [fst snd] in *.
    split; [exact EST|]. split; [exact INV|]. exists flags, mode, bufbytes.
    split. { eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. unfold fcells. rewrite file_cells_size.
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split; [exact FL|].
    split. { eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D2 | lia | cbn; lia | cbn; lia]. }
    split; [exact BP | exact WBL].
  Qed.

  Lemma file_sink_flags : sink_flags_stmt Fp SINK_file.
  Proof using Fp0 Fphi. pin_using (fun (Fp0 Fphi : unit) => tt).
    unfold sink_flags_stmt. intros m [f st] (EST & INV & flags & mode & bufbytes & FC & FL & _). cbn [fst snd] in *.
    exists (Z_to_bv 8 (bv_unsigned flags)).
    pose proof (bv_unsigned_in_range 64 flags) as FR. unfold bv_modulus in FR.
    split.
    - unfold fcells, file_cells in FC. apply (proj1 (rw_cells_app ssegs m Fp [C4 flags] _)) in FC. destruct FC as [FC _].
      destruct FC as [[WF BY] WR]. split; [split|].
      + cbn. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes] in BY |- *. rewrite app_nil_r in BY |- *.
        change (le4 flags) with ([Z_to_bv 8 (bv_unsigned flags)] ++ Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8)) in BY.
        apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [BY _]. exact BY.
      + cbn [cells_size csize Nat.add] in WR |- *. destruct WR as (A1 & A2 & A3). split; [lia|]. split; [lia|]. intros i Hi. apply A3. lia.
    - rewrite Z_to_bv_unsigned. change (2 ^ Z.of_N 8) with 256. apply land32_lowbyte; [lia|].
      destruct FL as (_ & _ & _ & FE & _). exact FE.
  Qed.

  Lemma file_topok : topok_stmt TOPOK_file.
  Proof using Type. pin_using tt. unfold topok_stmt, TOPOK_file. intros; exact I. Qed.

  (* [comment removed for export] *)
  Lemma fsink_inv_fx : forall f f', fsink_inv f -> fx_inv f f' -> fsink_inv f'.
  Proof using Type. pin_using tt.
    intros f f' (WA & RB & BS & NW & CH & SWB & CHN) (E1 & E2 & E3 & E4 & E5 & E6 & WA' & RB' & SW & LB).
    unfold fsink_inv. rewrite E1, E2, E3, E5, WA', RB', WA, RB. repeat split; auto.
  Qed.
  Lemma flags_ok_fx : forall f f' flags, fx_inv f f' -> flags_ok f flags -> flags_ok f' flags.
  Proof using Type. pin_using tt.
    intros f f' flags (E1 & E2 & E3 & E4 & E5 & E6 & _) FL. unfold flags_ok in *. rewrite E2, E4, E5, E6. exact FL.
  Qed.

  (* [comment removed for export] *)
  Lemma file_out : out_stmt Fp 232 Fp B bs SINK_file TOPOK_file OUT_file.
  Proof using B0 BS0 BSEP1 BSEP2 BShi FB FSEP1 FSEP2 Fp0. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi FB FSEP1 FSEP2 Fp0 : unit) => tt).
    unfold out_stmt. intros until canary. intros HS SRC BYT LB -> -> ST LO GLO SPHI S47 TQ SSP MI D1 D2 D3 D4 D5.
    destruct st as [f st']. destruct HS as (EST & INV & flags & mode & bufbytes & FC & FL & BUF & BP & WBL). cbn [fst snd] in *.
    pose proof INV as (WA & RB & BSZ & NW & CH & SWB & CHN).
    unfold OUT_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. cbn in A0R.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite zb_length in SB.
    set (S := bv_unsigned a0) in *.
    assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm). rewrite NW in FLw.
    unfold implM, OUT_file. cbn [fst snd].
    destruct (zlength bs0 <=? PIECE_MAX) eqn:SMALL.
    2:{ apply impl_ret_intro. apply evt_done. exact I. }
    apply Z.leb_le in SMALL. unfold PIECE_MAX in SMALL.
    eapply impl_ebind.
    { pose proof (fwritex_spec (St:=St) ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (zlength bs0)) (Z_to_bv 64 Fp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc m st' f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes bs0 S lo canary) as FX.
      unfold implM in FX. rewrite WA, BSZ in FX. apply FX; clear FX;
        rewrite ?zb_to_bytes in *; unfold FWRITEX_DEPTH, zlength in *;
        fastfirst (first [ noevar_assumption | exact FC | exact BUF | exact BP | exact SRC | exact BYT | exact EA0 | reflexivity | exact CH | exact ST | exact SSP | exact MI
              | exact FLsvb | exact FLw
              | intros X; rewrite X in WA; discriminate
              | lia
              | match goal with |- ?g => idtac "FILEOUT-PREM:" g end; fail ]). }
    cbv beta. intros [f' st''] ms' PO. cbn [fst snd] in PO |- *.
    unfold fwritex_post in PO.
    destruct PO as (-> & FXI & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP').
    apply impl_ret_intro. apply evt_done. cbn [epost fst snd]. unfold out_post, SR.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, fx_W; cbn [outside]. rewrite BSZ. intros; lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    { (* [comment removed for export] *)
      split; [cbn [snd]; congruence|]. split; [exact (fsink_inv_fx f f' INV FXI)|].
      pose proof FXI as (E1 & E2 & E3 & E4 & E5 & E6 & WA' & RB' & SW & LBI).
      cbn [fst snd]. exists flags, mode', bufbytes'. rewrite ?E1, ?BSZ. rewrite ?WA, ?BSZ in FC'. rewrite ?BSZ in BUF'. rewrite ?BSZ in WBL'.
      split; [exact FC'|]. split; [exact (flags_ok_fx f f' flags FXI FL)|]. split; [exact BUF'|]. split; [exact BP'| exact WBL']. }
    split; [exact SSP'|].
    (* [comment removed for export] *)
    eapply bytes_at_transport; [exact SRC | exact MU |].
    unfold fx_W. rewrite zb_length, BSZ. cbn [disjoint_from]. unfold zlength in *. lia.
  Qed.
End FileSink.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Bridge.
  Context {St : Type}.
  #[local] Notation impl := (ITree.impl ssegs (at_node ssegs) (npeek ssegs)).

  (* [comment removed for export] *)
  Lemma impl_bind_cong2 : forall {A B1 B2} (t : itree node A) (k1 : A -> itree node B1) (k2 : A -> itree node B2)
      (Q1 : B1 -> machine_state -> Prop) (Q2 : B2 -> machine_state -> Prop) ms,
    (forall r ms', impl (k1 r) Q1 ms' -> impl (k2 r) Q2 ms') ->
    impl (ITree.bind node t k1) Q1 ms -> impl (ITree.bind node t k2) Q2 ms.
  Proof using Type. pin_using tt.
    intros A B1 B2 t. induction t as [r|n k IH]; intros k1 k2 Q1 Q2 ms HK H; cbn [ITree.bind] in *.
    - apply HK. exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)].
      + left. split; [exact Hat|]. intros rsp. eapply IH; [exact HK| apply Hk].
      + right. exists g. split; [exact Hg|]. eapply IH; [exact HK| apply Hk].
  Qed.

  Lemma impl_bind_assoc_rev : forall {A B C} (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) Q ms,
    impl (ITree.bind node (ITree.bind node t g) f) Q ms -> impl (ITree.bind node t (fun x => ITree.bind node (g x) f)) Q ms.
  Proof using Type. pin_using tt.
    intros A B C t. induction t as [r|n k IH]; intros g f Q ms H; cbn [ITree.bind] in *.
    - exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(h & Hh & Hk)].
      + left. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
      + right. exists h. split; [exact Hh|]. apply IH. apply Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma OUT_file_step : forall {B B2} p (k : unit -> M (file_st * St) B) (f : file_st) (st : St)
      (Q : B -> file_st * St -> machine_state -> Prop) (k2 : file_st -> M St B2) (Q2 : B2 -> St -> machine_state -> Prop) ms,
    zlength p <= PIECE_MAX ->
    (forall f1 st1 ms1, implM ssegs (k tt) (f1, st1) Q ms1 -> implM ssegs (k2 f1) st1 Q2 ms1) ->
    implM ssegs (mbind (OUT_file p) k) (f, st) Q ms ->
    implM ssegs (mbind (fwritex f p) k2) st Q2 ms.
  Proof using Type. pin_using tt.
    intros B B2 p k f st Q k2 Q2 ms SMALL HK H. unfold implM, mbind, OUT_file, ebind in *. cbn [fst snd] in H.
    replace (zlength p <=? PIECE_MAX) with true in H by (symmetry; apply Z.leb_le; exact SMALL).
    apply impl_bind_assoc_rev in H.
    eapply impl_bind_cong2; [| exact H]. cbv beta. intros [|[f1 st1]] ms1 H1; cbn [ITree.bind fst snd] in H1 |- *.
    - cbn in H1 |- *. eapply evt_mono; [exact H1|]. intros ms' X. exact X.
    - apply HK. exact H1.
  Qed.

  (* [comment removed for export] *)
  Definition pieces_small (ps : list (list Z)) : Prop := Forall (fun p => zlength p <= PIECE_MAX) ps.
  Lemma out_pieces_bridge : forall ps (f : file_st) (st : St) (r : Z) (Q : Z -> file_st * St -> machine_state -> Prop) ms,
    pieces_small ps ->
    implM ssegs (outsk OUT_file ps (mret r)) (f, st) Q ms ->
    implM ssegs (out_pieces f ps) st (fun f' st' ms' => Q r (f', st') ms') ms.
  Proof using Type. pin_using tt.
    induction ps as [|p ps IH]; intros f st r Q ms SM H; cbn [outsk out_pieces] in *.
    - exact H.
    - apply Forall_cons_iff in SM. destruct SM as [SM1 SM2].
      eapply OUT_file_step; [exact SM1 | | exact H]. cbv beta. intros f1 st1 ms1 H1. apply IH; [exact SM2 | exact H1].
  Qed.
End Bridge.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_printf_core_common.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma zb_to_bytes : forall l, zb l = to_bytes l.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land32_lowbyte : forall x, 0 <= x -> Z.land x 32 = 0 -> Z.land (x mod 256) 32 = 0.
Proof.
  intros x Hx H. change 256 with (2^8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm x (Z.ones 8)), <- Z.land_assoc, H. apply Z.land_0_r.
Qed.

Section FileSink.
  Context {St : Type}.
  (* [comment removed for export] *)
  Variables (Fp B bs : Z) (rpos rend closefn readfn seekfn prev next : Z) (tail : list byte).
  (* [comment removed for export] *)
  Variable sw0 : bool.
  (* [comment removed for export] *)
  Variable ch0 : bool.
  (* [comment removed for export] *)
  Variable st0 : St.

  (* [comment removed for export] *)
  Definition fsink_inv (f : file_st) : Prop :=
    f_wactive f = true /\ f_rbuf f = [] /\ f_bufsize f = bs /\ f_nowr f = false
    /\ (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31))
    /\ (f_stdoutw f = true -> sw0 = true) /\ f_chan f = ch0.

  Definition SINK_file (m : mem) (fs : file_st * St) : Prop :=
    let f := fst fs in
    snd fs = st0 /\ fsink_inv f /\
    exists (flags mode : word) (bufbytes : list byte),
      rw_cells usegs m Fp (fcells flags rpos rend closefn (B + bs) (B + zlength (f_wbuf f)) B readfn (wfn_of f) seekfn B bs prev next (f_fd f) mode (lbf_of f) tail)
      /\ flags_ok f flags
      /\ rw_cells usegs m B [CB (Z.to_nat bs) bufbytes]
      /\ firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f)
      /\ zlength (f_wbuf f) <= bs.

  (* [comment removed for export] *)
  Definition TOPOK_file (sp : Z) : Prop := True.

  (* [comment removed for export] *)
  Definition PIECE_MAX : Z := 2^26 - 1024.
  Definition OUT_file (s : list Z) : M (file_st * St) unit :=
    fun fs => if zlength s <=? PIECE_MAX
              then ebind (fwritex (fst fs) s (snd fs)) (fun r => ITree.Ret (Ok (tt, (fst r, snd r))))
              else ITree.Ret Unr.

  (* [comment removed for export] *)
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis B0 : 0 < B.
  Hypothesis BS0 : 0 <= bs <= 1024.
  Hypothesis BShi : B + bs <= 2^47.   (* [comment removed for export] *)
  Hypothesis Fphi : Fp + 232 < 2^63.
  Hypothesis FB : B + bs <= Fp \/ Fp + 232 <= B.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis TL : firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8.

  Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
    Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
  Proof using BS0 BSEP1 BSEP2 FB FSEP1 FSEP2. pin_using (fun (BS0 BSEP1 BSEP2 FB FSEP1 FSEP2 : unit) => tt).
    intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
  Qed.

  Lemma file_sink_frame : sink_frame_stmt Fp 232 B bs SINK_file.
  Proof using BS0 BSEP1 BSEP2 FB FSEP1 FSEP2. pin_using (fun (BS0 BSEP1 BSEP2 FB FSEP1 FSEP2 : unit) => tt).
    unfold sink_frame_stmt. intros W m m' [f st] (EST & INV & flags & mode & bufbytes & FC & FL & BUF & BP & WBL) MU WM D1 D2. cbn [fst snd] in *.
    split; [exact EST|]. split; [exact INV|]. exists flags, mode, bufbytes.
    split. { eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. unfold fcells. rewrite file_cells_size.
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split; [exact FL|].
    split. { eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D2 | lia | cbn; lia | cbn; lia]. }
    split; [exact BP | exact WBL].
  Qed.

  Lemma file_sink_flags : sink_flags_stmt Fp SINK_file.
  Proof using Fp0 Fphi. pin_using (fun (Fp0 Fphi : unit) => tt).
    unfold sink_flags_stmt. intros m [f st] (EST & INV & flags & mode & bufbytes & FC & FL & _). cbn [fst snd] in *.
    exists (Z_to_bv 8 (bv_unsigned flags)).
    pose proof (bv_unsigned_in_range 64 flags) as FR. unfold bv_modulus in FR.
    split.
    - unfold fcells, file_cells in FC. apply (proj1 (rw_cells_app usegs m Fp [C4 flags] _)) in FC. destruct FC as [FC _].
      destruct FC as [[WF BY] WR]. split; [split|].
      + cbn. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes] in BY |- *. rewrite app_nil_r in BY |- *.
        change (le4 flags) with ([Z_to_bv 8 (bv_unsigned flags)] ++ Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8)) in BY.
        apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [BY _]. exact BY.
      + cbn [cells_size csize Nat.add] in WR |- *. destruct WR as (A1 & A2 & A3). split; [lia|]. split; [lia|]. intros i Hi. apply A3. lia.
    - rewrite Z_to_bv_unsigned. change (2 ^ Z.of_N 8) with 256. apply land32_lowbyte; [lia|].
      destruct FL as (_ & _ & _ & FE & _). exact FE.
  Qed.

  Lemma file_topok : topok_stmt TOPOK_file.
  Proof using Type. pin_using tt. unfold topok_stmt, TOPOK_file. intros; exact I. Qed.

  (* [comment removed for export] *)
  Lemma fsink_inv_fx : forall f f', fsink_inv f -> fx_inv f f' -> fsink_inv f'.
  Proof using Type. pin_using tt.
    intros f f' (WA & RB & BS & NW & CH & SWB & CHN) (E1 & E2 & E3 & E4 & E5 & E6 & WA' & RB' & SW & LB).
    unfold fsink_inv. rewrite E1, E2, E3, E5, WA', RB', WA, RB. repeat split; auto.
  Qed.
  Lemma flags_ok_fx : forall f f' flags, fx_inv f f' -> flags_ok f flags -> flags_ok f' flags.
  Proof using Type. pin_using tt.
    intros f f' flags (E1 & E2 & E3 & E4 & E5 & E6 & _) FL. unfold flags_ok in *. rewrite E2, E4, E5, E6. exact FL.
  Qed.

  (* [comment removed for export] *)
  Lemma file_out : out_stmt Fp 232 Fp B bs SINK_file TOPOK_file OUT_file.
  Proof using B0 BS0 BSEP1 BSEP2 BShi FB FSEP1 FSEP2 Fp0. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi FB FSEP1 FSEP2 Fp0 : unit) => tt).
    unfold out_stmt. intros until canary. intros HS SRC BYT LB -> -> ST LO GLO SPHI S47 TQ SSP MI D1 D2 D3 D4 D5.
    destruct st as [f st']. destruct HS as (EST & INV & flags & mode & bufbytes & FC & FL & BUF & BP & WBL). cbn [fst snd] in *.
    pose proof INV as (WA & RB & BSZ & NW & CH & SWB & CHN).
    unfold OUT_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. cbn in A0R.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite zb_length in SB.
    set (S := bv_unsigned a0) in *.
    assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm). rewrite NW in FLw.
    unfold implM, OUT_file. cbn [fst snd].
    destruct (zlength bs0 <=? PIECE_MAX) eqn:SMALL.
    2:{ apply impl_ret_intro. apply evt_done. exact I. }
    apply Z.leb_le in SMALL. unfold PIECE_MAX in SMALL.
    eapply impl_ebind.
    { pose proof (fwritex_spec (St:=St) ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (zlength bs0)) (Z_to_bv 64 Fp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc m st' f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes bs0 S lo canary) as FX.
      unfold implM in FX. rewrite WA, BSZ in FX. apply FX; clear FX;
        rewrite ?zb_to_bytes in *; unfold FWRITEX_DEPTH, zlength in *;
        fastfirst (first [ noevar_assumption | exact FC | exact BUF | exact BP | exact SRC | exact BYT | exact EA0 | reflexivity | exact CH | exact ST | exact SSP | exact MI
              | exact FLsvb | exact FLw
              | intros X; rewrite X in WA; discriminate
              | lia
              | match goal with |- ?g => idtac "FILEOUT-PREM:" g end; fail ]). }
    cbv beta. intros [f' st''] ms' PO. cbn [fst snd] in PO |- *.
    unfold fwritex_post in PO.
    destruct PO as (-> & FXI & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP').
    apply impl_ret_intro. apply evt_done. cbn [epost fst snd]. unfold out_post, SR.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, fx_W; cbn [outside]. rewrite BSZ. intros; lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    { (* [comment removed for export] *)
      split; [cbn [snd]; congruence|]. split; [exact (fsink_inv_fx f f' INV FXI)|].
      pose proof FXI as (E1 & E2 & E3 & E4 & E5 & E6 & WA' & RB' & SW & LBI).
      cbn [fst snd]. exists flags, mode', bufbytes'. rewrite ?E1, ?BSZ. rewrite ?WA, ?BSZ in FC'. rewrite ?BSZ in BUF'. rewrite ?BSZ in WBL'.
      split; [exact FC'|]. split; [exact (flags_ok_fx f f' flags FXI FL)|]. split; [exact BUF'|]. split; [exact BP'| exact WBL']. }
    split; [exact SSP'|].
    (* [comment removed for export] *)
    eapply bytes_at_transport; [exact SRC | exact MU |].
    unfold fx_W. rewrite zb_length, BSZ. cbn [disjoint_from]. unfold zlength in *. lia.
  Qed.
End FileSink.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Bridge.
  Context {St : Type}.
  #[local] Notation impl := (ITree.impl usegs (at_node usegs) (npeek usegs)).

  (* [comment removed for export] *)
  Lemma impl_bind_cong2 : forall {A B1 B2} (t : itree node A) (k1 : A -> itree node B1) (k2 : A -> itree node B2)
      (Q1 : B1 -> machine_state -> Prop) (Q2 : B2 -> machine_state -> Prop) ms,
    (forall r ms', impl (k1 r) Q1 ms' -> impl (k2 r) Q2 ms') ->
    impl (ITree.bind node t k1) Q1 ms -> impl (ITree.bind node t k2) Q2 ms.
  Proof using Type. pin_using tt.
    intros A B1 B2 t. induction t as [r|n k IH]; intros k1 k2 Q1 Q2 ms HK H; cbn [ITree.bind] in *.
    - apply HK. exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)].
      + left. split; [exact Hat|]. intros rsp. eapply IH; [exact HK| apply Hk].
      + right. exists g. split; [exact Hg|]. eapply IH; [exact HK| apply Hk].
  Qed.

  Lemma impl_bind_assoc_rev : forall {A B C} (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) Q ms,
    impl (ITree.bind node (ITree.bind node t g) f) Q ms -> impl (ITree.bind node t (fun x => ITree.bind node (g x) f)) Q ms.
  Proof using Type. pin_using tt.
    intros A B C t. induction t as [r|n k IH]; intros g f Q ms H; cbn [ITree.bind] in *.
    - exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(h & Hh & Hk)].
      + left. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
      + right. exists h. split; [exact Hh|]. apply IH. apply Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma OUT_file_step : forall {B B2} p (k : unit -> M (file_st * St) B) (f : file_st) (st : St)
      (Q : B -> file_st * St -> machine_state -> Prop) (k2 : file_st -> M St B2) (Q2 : B2 -> St -> machine_state -> Prop) ms,
    zlength p <= PIECE_MAX ->
    (forall f1 st1 ms1, implM usegs (k tt) (f1, st1) Q ms1 -> implM usegs (k2 f1) st1 Q2 ms1) ->
    implM usegs (mbind (OUT_file p) k) (f, st) Q ms ->
    implM usegs (mbind (fwritex f p) k2) st Q2 ms.
  Proof using Type. pin_using tt.
    intros B B2 p k f st Q k2 Q2 ms SMALL HK H. unfold implM, mbind, OUT_file, ebind in *. cbn [fst snd] in H.
    replace (zlength p <=? PIECE_MAX) with true in H by (symmetry; apply Z.leb_le; exact SMALL).
    apply impl_bind_assoc_rev in H.
    eapply impl_bind_cong2; [| exact H]. cbv beta. intros [|[f1 st1]] ms1 H1; cbn [ITree.bind fst snd] in H1 |- *.
    - cbn in H1 |- *. eapply evt_mono; [exact H1|]. intros ms' X. exact X.
    - apply HK. exact H1.
  Qed.

  (* [comment removed for export] *)
  Definition pieces_small (ps : list (list Z)) : Prop := Forall (fun p => zlength p <= PIECE_MAX) ps.
  Lemma out_pieces_bridge : forall ps (f : file_st) (st : St) (r : Z) (Q : Z -> file_st * St -> machine_state -> Prop) ms,
    pieces_small ps ->
    implM usegs (outsk OUT_file ps (mret r)) (f, st) Q ms ->
    implM usegs (out_pieces f ps) st (fun f' st' ms' => Q r (f', st') ms') ms.
  Proof using Type. pin_using tt.
    induction ps as [|p ps IH]; intros f st r Q ms SM H; cbn [outsk out_pieces] in *.
    - exact H.
    - apply Forall_cons_iff in SM. destruct SM as [SM1 SM2].
      eapply OUT_file_step; [exact SM1 | | exact H]. cbv beta. intros f1 st1 ms1 H1. apply IH; [exact SM2 | exact H1].
  Qed.
End Bridge.
End TwB.
