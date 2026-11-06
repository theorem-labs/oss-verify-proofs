(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From Stdlib Require Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfpcap_chkA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac lit_branch := let K := fresh "Klit" in if_cases K; try (vm_compute in K; discriminate K); clear K.

Section WithCeil.
Context {CEILV : CEIL}.
Section Chk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  (* [comment removed for export] *)
  Definition chk_ctx (sp tp : word) (R : rctx) (s : PState H hptr) (CL FB : list cblock) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem) : Prop :=
    GIo K R s CL FB m /\ (usp0 R - 8388608 <= lo)%Z /\ (lo + 81920 <= bv_unsigned sp)%Z /\ (bv_unsigned sp <= rc_spmain R)%Z
    /\ tp = rc_tp R /\ (bv_unsigned sp mod 16 = 0)%Z
    /\ In (f, FA, FILE_BLOCK) FB /\ sites = sites_at (bv_unsigned sp + D_CHECK_HEADER)
    /\ length magic = 4%nat /\ Forall (fun z => 0 <= z < 256)%Z magic
    /\ (bv_unsigned sp <= ERR)%Z /\ (ERR + 4 <= MG)%Z /\ (MG + 4 <= rc_spmain R)%Z
    /\ (bv_unsigned sp <= EB)%Z /\ (EB + 256 <= rc_spmain R)%Z /\ (EB + 256 <= ERR \/ MG + 4 <= EB)%Z /\ (EB mod 8 = 0)%Z.

  (* [comment removed for export] *)
  Definition chk_fail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PState H hptr) (CL FB : list cblock) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' : word) (m3 : mem) (ps3 : PState H hptr)
           (msg : list Z) (junk3 : list byte) (ew : word) (hc : list cell),
      chk_ctx sp tp R s CL FB lo MG FA EB ERR f magic m ->
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -112) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3 ->
      GIo K R ps3 CL FB m3 ->
      rw_cells ssegs m3 (bv_unsigned sp + -112) hc -> cells_size hc = 32%nat ->
      rw_cells ssegs m3 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m3 ERR [C4 ew] -> rw_cells ssegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) ->
      rw_cells ssegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] -> (Z.of_nat (length msg) < 256)%Z ->
      Forall (fun z => 0 < z < 256)%Z msg -> ps_outfile ps3 = ps_outfile s ->
      evt ssegs (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s) (CH_Err msg) ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15264) fc None m3 (seg_rom ssegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' m3 ps3 msg junk3 ew hc : ltac2:(SecDiet.SzSec.tyM 'chk_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_fail__body : ltac2:(SecDiet.SzSec.bodyP 'chk_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros CTX MIx ST3 AG3 G3 FA3 Hhc FRS3 ERR3 MG3 HEB3 LEN3 RNG3 OFX.
    destruct CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (rw_cells_forget _ _ _ _ FA3) as [fj FA3']. clear FA3. rewrite Hhc in FA3'.
    hide HEB3. hide MG3.
    pose proof (munch_refl [(ERR, ERR + 4)]%Z m3) as MU3. pose proof (wmono_refl ssegs m3) as WM3.
    do 16 pstep.
    release_frame FA3' ST3 (bv_unsigned sp + -80)%Z. release_frame FRS3 ST3 (bv_unsigned sp).
    unhide HEB3. unhide MG3.
    destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL. cbn [map] in MG3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGW : agrees_on (fun a => outside [(ERR, ERR + 4)]%Z a) m3 mm) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]);
      assert (HEB' : rw_cells ssegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3])
        by (eapply agrees_rw_cells; [exact AGW | exact HEB3 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
      assert (MG' : rw_cells ssegs mm MG [CB 4 (map b8 [k0; k1; k2; k3])])
        by (eapply rw_cells_recell; [eapply agrees_rw_cells; [exact AGW | exact MG3 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia] | cbn; repeat split; exact Logic.I | reflexivity]);
      assert (G' : GIo K R ps3 CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU3 | exact WM3 |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil])
    end.
    apply evt_done. unfold check_header_post.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, (Z_to_bv 64 1) end.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [solve [assumption | congruence] |].
    split; [assumption|]. split; [assumption|].
    split. { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGW|]. intros a [_ [_ Hn]]; cbn [outside]; lia. }
    split; [exact MG'|]. split; [assumption|].
    exists junk3. split; [reflexivity|]. split; [reflexivity|]. split; [exact G'|]. split; [exact HEB'|]. split; [exact LEN3| exact RNG3].
  Qed.
  End Sz1.
  Lemma chk_fail : ltac:(let t := eval cbv delta [chk_fail__stmt] in chk_fail__stmt in exact t).
  Proof using HFL SFL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' t3' t4' t5' t6' m3 ps3 msg junk3 ew hc. ltac2:(SecDiet.SzSec.closeP 'chk_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition z8 : list byte := repeat (Z_to_bv 8 0) 8.
  Definition fd_pad48 : list byte := repeat (Z_to_bv 8 0) 24 ++ le4 (Z_to_bv 64 (-1)) ++ repeat (Z_to_bv 8 0) 20.
  Definition blank_cells (P : Z) : list cell :=
    [ C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 0);
      CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); C4 (Z_to_bv 64 0);
      CB 48 fd_pad48;
      C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0) ].

  Definition blank_recell__stmt : Prop := forall m P,
    rw_cells ssegs m P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                         C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                         CB (Z.to_nat (PCAP_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_SF_TOTAL - 188)))]) ->
    rw_cells ssegs m P (blank_cells P).
  Section Sz2.
  Variables m P : ltac2:(SecDiet.SzSec.tyM 'blank_recell__stmt "vv" @m).
  Lemma blank_recell__body : ltac2:(SecDiet.SzSec.bodyP 'blank_recell__stmt "vv").
  Proof using Type. pin_using tt.
    intros Hc.
    destruct (rw_cells_cut _ _ _ 3 Hc) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [B C]. clear Hc X.
    cbn [firstn skipn cells_size csize Nat.add] in A, B, C.
    unfold PCAP_SF_TOTAL in C. change (Z.to_nat (664 - 188)) with 476%nat in C.
    assert (A' : rw_cells ssegs m P (firstn 7 (blank_cells P))).
    { eapply rw_cells_recell; [exact A | cbn; repeat split; exact Logic.I | vm_compute; reflexivity]. }
    assert (C' : rw_cells ssegs m (P + Z.of_nat 48 + Z.of_nat 8) (skipn 8 (blank_cells P))).
    { eapply rw_cells_recell; [exact C | cbn; repeat split; exact Logic.I | unfold fd_pad48; vm_compute; reflexivity]. }
    pose proof (rw_cells_uncut _ _ _ _ _ A' B ltac:(cbn; lia)) as AB.
    pose proof (rw_cells_uncut _ _ _ _ _ AB C' ltac:(cbn; lia)) as ABC. exact ABC.
  Qed.
  End Sz2.
  Lemma blank_recell : ltac:(let t := eval cbv delta [blank_recell__stmt] in blank_recell__stmt in exact t).
  Proof using Type. intros m P. ltac2:(SecDiet.SzSec.closeP 'blank_recell__body "vv"). Qed.

  (* [comment removed for export] *)
  Definition pcells (P : Z) (sw : bool) (maj min lt ext : Z) (nxt bsz buf snapc clean hsz lsw scl : cell) : list cell :=
    [ C8 (Z_to_bv 64 0); nxt; C4 (Z_to_bv 64 (-1)); bsz; buf; CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z sw)); CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      C4 (Z_to_bv 64 maj); C4 (Z_to_bv 64 min); snapc; C4 (Z_to_bv 64 lt); C4 (Z_to_bv 64 ext);
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); C4 (Z_to_bv 64 0);
      CB 48 fd_pad48; C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; clean; hsz; lsw; scl ].
  Definition blank_junk : pcap_junk :=
    mkPJ (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 12) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 16)
         (repeat (Z_to_bv 8 0) 12) (repeat (Z_to_bv 8 0) 28) fd_pad48 (repeat (Z_to_bv 8 0) 304) (repeat (Z_to_bv 8 0) 72) (Z_to_bv 64 0).

  Hypothesis HPL : heap_perm_law K.
  Hypothesis MALLOC : malloc_stmt_o HO K.
  Hypothesis FREE : free_stmt_o HO K.

  (* [comment removed for export] *)
  Definition blocks2_apart__stmt : Prop := forall R s bq B BS q P PS CL FB m,
    GIo K R s ((bq, B, BS) :: (q, P, PS) :: CL) FB m -> (1 <= BS)%Z -> (1 <= PS)%Z -> (B + BS <= P \/ P + PS <= B)%Z.
  Section Sz3.
  Variables R s bq B BS q P PS CL FB m : ltac2:(SecDiet.SzSec.tyM 'blocks2_apart__stmt "vvvvvvvvvvv" @R).
  Lemma blocks2_apart__body : ltac2:(SecDiet.SzSec.bodyP 'blocks2_apart__stmt "vvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G HBS HPS.
    destruct (Z.le_gt_cases (B + BS) P) as [|Hlt]; [left; lia|]. destruct (Z.le_gt_cases (P + PS) B) as [|Hlt']; [right; lia|]. exfalso.
    destruct (Z.le_gt_cases P B) as [Hpb|Hpb].
    - destruct (GIo_CLc_facts K R s [(bq, B, BS)] ((q, P, PS) :: CL) FB m B G
                 ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia)) as [_ Hn].
      apply Hn. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
    - destruct (GIo_CLc_facts K R s [(bq, B, BS)] ((q, P, PS) :: CL) FB m P G
                 ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia)) as [_ Hn].
      apply Hn. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
  Qed.
  End Sz3.
  Lemma blocks2_apart : ltac:(let t := eval cbv delta [blocks2_apart__stmt] in blocks2_apart__stmt in exact t).
  Proof using Type. intros R s bq B BS q P PS CL FB m. ltac2:(SecDiet.SzSec.closeP 'blocks2_apart__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition chk_fill__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PState H hptr) (CL FB : list cblock) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m3 : mem) (ps3 : PState H hptr) (q : hptr) (P : Z)
           (maj min n0 n1 n2 n3 l0 l1 l2 l3 mi : Z) (sw : bool) (mid junk8 e3 : list byte),
      chk_ctx sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) ->
      (0 <= maj < 2^16)%Z -> (0 <= min < 2^16)%Z ->
      (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
      (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= l2 < 256)%Z -> (0 <= l3 < 256)%Z -> l2 = 0%Z -> (l3 mod 4 = 0)%Z ->
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -112) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3 ->
      GIo K R ps3 ((q, P, PCAP_SF_TOTAL) :: CL) FB m3 ->
      rw_cells ssegs m3 P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                            C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                            CB (Z.to_nat (PCAP_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_SF_TOTAL - 188)))]) ->
      rw_cells ssegs m3 (bv_unsigned sp + -112) [CB 8 junk8; C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ->
      rw_cells ssegs m3 (bv_unsigned sp + -100)
        [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))] ->
      rw_cells ssegs m3 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m3 ERR [C4 z64] -> rw_cells ssegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m3 EB [CB 256 e3] ->
      ps_outfile ps3 = ps_outfile s ->
      implM ssegs (chk_fill_model MOps (prims HO fo_nop sites) q f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)) ps3
        (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
                 z64 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 FA) (Z_to_bv 64 min) (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x151d0) fc None m3 (seg_rom ssegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m3 ps3 q P maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw mid junk8 e3 : ltac2:(SecDiet.SzSec.tyM 'chk_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_fill__body : ltac2:(SecDiet.SzSec.bodyP 'chk_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FREE HFL HPL MALLOC SFL. pin_using (fun (FREE HFL HPL MALLOC SFL : unit) => tt).
    intros CTX MI3 Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3 MI2 ST3 AG3 G3 CELLS0 FRA FRD FRS ERRc MG4 HEB3 OFX.
    destruct CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    assert (MIB : (2^31 <= mi < 2^32)%Z) by (unfold TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in MI3; lia).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    cbn [cb_addr cb_size fst snd] in P1, P2, P3, P4, P5, P6. unfold PCAP_SF_TOTAL in P4, P5, P6.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    assert (NB : forall a, in_block CL a -> ~ (P <= a < P + 664)%Z).
    { intros a Ha Hin. destruct (GIo_CLc_facts K R ps3 [(q, P, PCAP_SF_TOTAL)] CL FB m3 a G3
                 ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; exact Hin)) as [_ Hn]. exact (Hn Ha). }
    apply blank_recell in CELLS0. rename CELLS0 into CELLS. unfold blank_cells, PCAP_PRIV_OFF in CELLS.
    (* [comment removed for export] *)
    unfold chk_fill_model. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. rewrite (land_ffff l0 l1 l2 l3) by lia.
    unfold PCAP_TSTAMP_PRECISION_MICRO. cbn [Z.eqb mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_free prims].
    set (lt := linktype_to_dlt (l0 + 256 * l1)). set (snap := pcapint_adjust_snapshot lt (le4val n0 n1 n2 n3)).
    pose proof (linktype_to_dlt_range (l0 + 256 * l1) ltac:(lia)) as LTR. fold lt in LTR.
    pose proof (adjust_snapshot_range lt (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as SNR. fold snap in SNR. unfold INT_MAX in SNR.
    set (EXT := s32 (Z.land (le4val l0 l1 l2 l3) 4294901760)).
    pose proof (s32_range (Z.land (le4val l0 l1 l2 l3) 4294901760)) as EXR. fold EXT in EXR.
    set (POSTQ := check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
    (* [comment removed for export] *)
    assert (K4OK : forall (ra6 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m6 : mem) (ps6 : PState H hptr)
                          (bq : hptr) (B BS HS SS : Z) (LS : lenswap_t) (SC : sf_scale_t) (bjunk e6 : list byte),
      (HS = 16 \/ HS = 24)%Z -> (1 <= SS <= 2147483647)%Z -> BS = (if 2048 <? SS then 2048 else SS)%Z ->
      mem_inv ssegs m6 -> stk ssegs m6 lo (bv_unsigned sp + -112) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6 ->
      GIo K R ps6 ((bq, B, BS) :: (q, P, PCAP_SF_TOTAL) :: CL) FB m6 ->
      rw_cells ssegs m6 B [CB (Z.to_nat BS) bjunk] ->
      rw_cells ssegs m6 P (pcells P sw maj min lt EXT (C8 (Z_to_bv 64 87024)) (C4 (Z_to_bv 64 BS)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 SS))
                             (C8 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 HS)) (C4 (Z_to_bv 64 (lenswap_code LS))) (C4 (Z_to_bv 64 (sfscale_code SC)))) ->
      rw_cells ssegs m6 (bv_unsigned sp + -112) [CB 8 junk8; C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ->
      rw_cells ssegs m6 (bv_unsigned sp + -100)
        [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))] ->
      rw_cells ssegs m6 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m6 ERR [C4 z64] -> rw_cells ssegs m6 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m6 EB [CB 256 e6] ->
      ps_outfile ps6 = ps_outfile s ->
      implM ssegs (mret (CH_Ok (mkPcap q f BS BS bq [] sw maj min SS lt EXT 0 0 [] hdr0 (PrivPcap (mkSf HS LS SC))))) ps6 POSTQ
        (MS (mkR ra6 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 B) a1' a2' a3' a4' a5' a6' a7'
                 z64 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x153c4) fc None m6 (seg_rom ssegs))).
    { intros ra6 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m6 ps6 bq B BS HS SS LS SC bjunk e6 HHS HSS HBS MI6 ST6 AG6 G6 BUF CELLS6 FRA6 FRD6 FRS6 ERR6 MG6 HEB6 OF6.
      clear CELLS FRA FRD FRS ERRc MG4 HEB3 MI2 ST3 AG3.
      assert (BSR : (1 <= BS <= 2048)%Z) by (rewrite HBS; destruct (Z.ltb_spec 2048 SS); lia).
      pose proof (GIo_block_ok K _ _ _ _ _ _ G6 ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & B5 & B6).
      cbn [cb_addr cb_size fst snd] in B1, B2, B3, B4, B5, B6.
      pose proof (GIo_got_pcap K _ _ _ _ _ G6) as GOT. unfold PK, GOT_PCAP_ADDR, GOT_INSTALL_BPF, GOT_BREAKLOOP in GOT; cbn [pk_oneshot pk_cleanup_sf] in GOT.
      assert (NB6 : forall a, in_block CL a -> ~ (P <= a < P + 664)%Z /\ ~ (B <= a < B + BS)%Z).
      { intros a Ha. split; intros Hin.
        - destruct (GIo_CLc_facts K R ps6 [(bq, B, BS); (q, P, PCAP_SF_TOTAL)] CL FB m6 a G6
                     ltac:(unfold in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; lia)) as [_ Hn]. exact (Hn Ha).
        - destruct (GIo_CLc_facts K R ps6 [(bq, B, BS); (q, P, PCAP_SF_TOTAL)] CL FB m6 a G6
                     ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia)) as [_ Hn]. exact (Hn Ha). }
      pose proof (blocks2_apart _ _ _ _ _ _ _ _ _ _ _ G6 ltac:(lia) ltac:(unfold PCAP_SF_TOTAL; lia)) as BP. unfold PCAP_SF_TOTAL in BP.
      pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl ssegs m6) as WM6.
      hide HEB6. hide MG6. hide ERR6. hide BUF.
      unfold pcells in CELLS6.
      apply (implM_ret ssegs).
      do 3 pstep. do 2 step. do 13 step.
      release_frame FRA6 ST6 (bv_unsigned sp + -100)%Z. release_frame FRD6 ST6 (bv_unsigned sp + -80)%Z. release_frame FRS6 ST6 (bv_unsigned sp).
      unhide HEB6. unhide MG6. unhide ERR6. unhide BUF.
      destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL. cbn [map] in MG6.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGW : agrees_on (fun a => outside [(P, P + 664)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
        assert (HEB' : rw_cells ssegs mm EB [CB 256 e6])
          by (eapply agrees_rw_cells; [exact AGW | exact HEB6 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; (keep_hyps CEILV sp R lo EB P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B a LO BU E1 SPW P4 Ha; lia)]);
        assert (MG' : rw_cells ssegs mm MG [CB 4 (map b8 [k0; k1; k2; k3])])
          by (eapply rw_cells_recell; [eapply agrees_rw_cells; [exact AGW | exact MG6 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; (keep_hyps CEILV sp R lo MG EB ERR P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B a LO BU R1 R2 SPW P4 Ha; lia)] | cbn; repeat split; exact Logic.I | reflexivity]);
        assert (ERR' : rw_cells ssegs mm ERR [C4 z64])
          by (eapply agrees_rw_cells; [exact AGW | exact ERR6 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; (keep_hyps CEILV sp R lo EB ERR P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B a LO BU R1 SPW P4 Ha; lia)]);
        assert (BUF' : rw_cells ssegs mm B [CB (Z.to_nat BS) bjunk])
          by (eapply agrees_rw_cells; [exact AGW | exact BUF | intros a Ha; cbn [outside cells_size csize Nat.add] in *; (keep_hyps CEILV sp R lo EB P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B BS a BP Ha; lia)]);
        assert (G' : GIo K R ps6 ((bq, B, BS) :: (q, P, PCAP_SF_TOTAL) :: CL) FB mm)
          by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |];
              apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; (keep_hyps CEILV sp EB P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B; lia)| apply Forall_nil])
      end.
      apply evt_done. subst POSTQ. unfold check_header_post.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 P), mm, z64 end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [solve [assumption | congruence] |].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGW|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
               split; [exact (proj1 (NB6 a Ha))| exact Logic.I]. }
      split; [exact MG'|]. split; [exact ERR'|].
      exists P, [(q, P, PCAP_SF_TOTAL); (bq, B, BS)].
      split; [reflexivity|].
      split. { eapply (GIo_perm K HPL); [exact G'|].
               eapply Permutation.Permutation_trans; [apply Permutation.Permutation_cons_append|]. cbn [app].
               replace (CL ++ [(q, P, PCAP_SF_TOTAL); (bq, B, BS)]) with ((CL ++ [(q, P, PCAP_SF_TOTAL)]) ++ [(bq, B, BS)])
                 by (first [now rewrite app_assoc | now rewrite <- app_assoc]).
               change ((q, P, PCAP_SF_TOTAL) :: CL ++ [(bq, B, BS)]) with (((q, P, PCAP_SF_TOTAL) :: CL) ++ [(bq, B, BS)]).
               apply Permutation.Permutation_app_tail. apply Permutation.Permutation_cons_append. }
      split; [| split; [reflexivity| exists e6; exact HEB']].
      exists z8, z8, z8. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists B, 0%Z, blank_junk, [], bjunk.
      destruct (rw_cells_cut _ _ _ 33 CELLS6) as [CP CQ]. cbn [firstn skipn cells_size csize Nat.add] in CP, CQ.
      split; [unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc]; reflexivity|].
      split. { unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, PK, blank_junk.
               cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_next_pcap pk_cleanup_sf
                    pc_priv pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                    pc_tstamp_precision pc_header h_sec h_usec h_caplen h_len hdr0].
               exact CP. }
      split. { unfold priv_cells, PCAP_PRIV_OFF. cbn [pc_priv sf_cells sf_hdrsize sf_lengths_swapped sf_scale_type].
               replace (P + 648)%Z with (P + Z.of_nat 648)%Z by lia. exact CQ. }
      split; [exact BUF'|]. split; [reflexivity|]. split; [reflexivity|].
      unfold pcap_wf. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                            pc_linktype pc_linktype_ext pc_header pc_priv h_caplen h_len hdr0 sf_hdrsize length Z.of_nat].
      unfold INT_MAX. repeat split; try (keep_hyps CEILV sp EB P n0 n1 n2 n3 l0 l1 l2 l3 k0 k1 k2 k3 B SS HSS BS BSR maj Bmaj min Bmin LTR EXR HS HHS; lia). }
    (* [comment removed for export] *)
    assert (K4FAIL : forall (ra6 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m6 : mem) (ps6 : PState H hptr) (e6 : list byte),
      mem_inv ssegs m6 -> stk ssegs m6 lo (bv_unsigned sp + -112) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6 ->
      GIo K R ps6 ((q, P, PCAP_SF_TOTAL) :: CL) FB m6 ->
      rw_cells ssegs m6 (bv_unsigned sp + -112) [CB 8 junk8; C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ->
      rw_cells ssegs m6 (bv_unsigned sp + -100)
        [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))] ->
      rw_cells ssegs m6 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m6 ERR [C4 z64] -> rw_cells ssegs m6 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m6 EB [CB 256 e6] ->
      ps_outfile ps6 = ps_outfile s ->
      implM ssegs (mbind (pfree HO q) (fun _ => mret (CH_Err Msg.out_of_memory))) ps6 POSTQ
        (MS (mkR ra6 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 z64 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15380) fc None m6 (seg_rom ssegs))).
    { intros ra6 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m6 ps6 e6 MI6 ST6 AG6 G6 FRA6 FRD6 FRS6 ERR6 MG6 HEB6 OF6.
      clear CELLS FRA FRD FRS ERRc MG4 HEB3 MI2 ST3 AG3.
      pose proof (rw_cells_bound _ _ _ _ HEB6) as BEB. cbn [cells_size csize Nat.add] in BEB.
      assert (L6 : length e6 = 256%nat) by (destruct HEB6 as [[WF _] _]; cbn in WF; (keep_hyps CEILV sp R MG EB ERR P maj min n0 n1 n2 n3 l0 l1 l2 l3 mi e6 WF; tauto)).
      assert (HEB14 : rw_cells ssegs m6 EB [CB 14 (firstn 14 e6); CB 242 (skipn 14 e6)]).
      { eapply rw_cells_recell; [exact HEB6 | cbn; rewrite length_firstn, length_skipn, L6; repeat split; reflexivity |].
        cbn [cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn. }
      destruct (rw_cells_cut _ _ _ 1 HEB14) as [HEBa HEBb]. clear HEB6 HEB14. cbn [firstn skipn cells_size csize Nat.add] in HEBa, HEBb.
      hide HEBb. hide MG6. hide ERR6.
      assert (LENM : length (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) = 14%nat) by (vm_compute; reflexivity).
      pose proof (munch_refl [(EB, EB + 14)]%Z m6) as MU6. pose proof (wmono_refl ssegs m6) as WM6.
      unfold implM. iprefix. do 5 step.
      call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB 0x10df2%Z 14%Z (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) (firstn 14 e6));
        [reflexivity | reflexivity | reflexivity
        | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m6 0x10df2 (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) MI6 ltac:(vm_compute; reflexivity) ltac:((keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 e6; lia)) ltac:(rewrite LENM; cbn; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 e6; lia))))
        | rewrite LENM; reflexivity | (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 e6; lia) | exact HEBa | unfold rc_lo in LO; (keep_hyps CEILV sp R lo EB magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 LO BU E1 SPW; lia) | (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 BEB; lia) | (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 e6; lia) | exact MI6 |].
      unhide HEBb. unhide MG6. unhide ERR6.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGW : agrees_on (fun a => outside [(EB, EB + 14)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
        assert (G7 : GIo K R ps6 ((q, P, PCAP_SF_TOTAL) :: CL) FB mm)
          by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; (keep_hyps CEILV sp R lo EB magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 LO BU E1 E2; lia)| apply Forall_nil]);
        assert (HEB7 : rw_cells ssegs mm EB [CB 14 (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]); CB 242 (skipn 14 e6)])
          by (eapply (rw_cells_uncut _ _ _ _ _ ltac:(eassumption));
              [eapply agrees_rw_cells; [exact AGW | exact HEBb | intros a Ha; cbn [outside cells_size csize Nat.add] in *; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 a Ha; lia)] | cbn; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 e6; lia)]);
        assert (MG7 : rw_cells ssegs mm MG (map (fun z => C1 (Z_to_bv 8 z)) magic))
          by (eapply agrees_rw_cells; [exact AGW | exact MG6 | intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; (keep_hyps CEILV sp MG EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 a R2 D1 Ha; lia)]);
        assert (ERR7 : rw_cells ssegs mm ERR [C4 z64])
          by (eapply agrees_rw_cells; [exact AGW | exact ERR6 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; (keep_hyps CEILV sp MG EB ERR magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 a R2 D1 Ha; lia)]);
        assert (AG7 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
          by (eapply agrees_on_trans; [exact AG6|]; eapply agrees_on_weaken; [exact AGW|]; intros a [_ [Hn _]]; cbn [outside]; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 e6 a Hn; lia))
      end.
      clear AGW HEBb MG6 ERR6 AG6 G6.
      do 2 step.
      (* [comment removed for export] *)
      name_sp sp (-112)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ []); [| reflexivity].
        split; [exact G7|]. split; [rewrite Hsp; eassumption|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [] ps7 ms7 PO. cbv beta in PO. destruct PO as (av7 & m7 & E & OF7 & MI7 & ST7 & AGf & Gf).
      unfold hpost_regs in E. destruct_exs E. subst ms7. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 86940)) with (Z_to_bv 64 86940) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in AGf, Gf.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm (seg_rom ssegs)] =>
      assert (KEEP : forall A cs, rw_cells ssegs _ A cs -> (bv_unsigned sp + -112 <= A)%Z -> rw_cells ssegs mm A cs)
        by (intros A cs HC HA; eapply agrees_rw_cells; [exact AGf | exact HC | intros a Ha; left; lia]) end.
      apply KEEP in HEB7; [|lia]. apply KEEP in MG7; [|lia]. apply KEEP in ERR7; [|lia].
      match goal with X1 : rw_cells ssegs _ (bv_unsigned sp + -112)%Z _, X2 : rw_cells ssegs _ (bv_unsigned sp + -100)%Z _, X3 : rw_cells ssegs _ (bv_unsigned sp + -80)%Z _ |- _ =>
        apply KEEP in X1; [|lia]; apply KEEP in X2; [|lia]; apply KEEP in X3; [|lia];
        pose proof (rw_cells_uncut _ _ _ _ _ X1 X2 ltac:(cbn; lia)) as HC32 end.
      apply (implM_ret ssegs). step.
      eapply chk_fail with (msg := Msg.out_of_memory);
        [ | exact MI7 | exact ST7 | | exact Gf | exact HC32 | reflexivity | assumption | exact ERR7 | exact MG7 | exact HEB7 | vm_compute; reflexivity
        | apply snprintf_ok; [vm_compute; reflexivity| constructor] | congruence ].
      { split; [exact G|]. repeat (split; [eassumption|]). eassumption. }
      eapply agrees_on_trans; [exact AG7|]. eapply agrees_on_weaken; [exact AGf|]. intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]. }
    (* [comment removed for export] *)
    assert (PKEEP : forall m5, munch [(P, P + 664)]%Z m3 m5 -> wmono ssegs m3 m5 ->
              GIo K R ps3 ((q, P, PCAP_SF_TOTAL) :: CL) FB m5
              /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m5
              /\ (forall A cs, rw_cells ssegs m3 A cs -> (P + 664 <= A)%Z -> rw_cells ssegs m5 A cs)
              /\ stk ssegs m5 lo (bv_unsigned sp + -112)).
    { intros m5 MU WM.
      split; [eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU | exact WM |];
              apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; lia| apply Forall_nil]|].
      split; [eapply agrees_on_trans; [exact AG3|]; eapply agrees_on_of_munch; [exact MU | exact WM |];
              intros a _ [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia| split; [exact (NB a Ha)| exact Logic.I]]|].
      split. { intros A cs HC HA. eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HC |].
               intros a Ha. cbn [outside]. lia. }
      eapply stk_transport_disjoint; [exact ST3 | exact MU | exact WM | cbn [disjoint_from]; unfold rc_lo in LO; lia]. }
    (* [comment removed for export] *)
    assert (K3A : forall (ra5 t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m5 : mem) (HS SS : Z) (LS : lenswap_t) (SC : sf_scale_t),
      (HS = 16 \/ HS = 24)%Z -> (2048 <= SS <= 2147483647)%Z ->
      mem_inv ssegs m5 -> munch [(P, P + 664)]%Z m3 m5 -> wmono ssegs m3 m5 ->
      rw_cells ssegs m5 P (pcells P sw maj min lt EXT (C8 (Z_to_bv 64 87024)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 SS))
                             (C8 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 HS)) (C4 (Z_to_bv 64 (lenswap_code LS))) (C4 (Z_to_bv 64 (sfscale_code SC)))) ->
      implM ssegs (chk_buf_model MOps (prims HO fo_nop sites) q f 0 sw maj min lt EXT HS SS LS SC) ps3 POSTQ
        (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' (Z_to_bv 64 2048) a2' a3' a4' a5' a6' a7'
                 z64 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1536c) fc None m5 (seg_rom ssegs))).
    { intros ra5 t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m5 HS SS LS SC HHS HSS MI5 MU5 WM5 CELLS5.
      destruct (PKEEP m5 MU5 WM5) as (G5 & AG5 & _ & ST5).
      clear CELLS MI2.
      unfold chk_buf_model. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. replace (if 2048 <? SS then 2048 else SS)%Z with 2048%Z by (destruct (Z.ltb_spec 2048 SS); lia).
      cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_free prims].
      unfold pcells in CELLS5.
      unfold implM. iprefix. step. pstep. step.
      destruct (PKEEP _ MU5 WM5) as (G5' & AG5' & KEEP5 & _). clear G5 AG5.
      pose proof (KEEP5 _ _ FRA ltac:(unfold rc_lo in LO; lia)) as FRA5. pose proof (KEEP5 _ _ FRD ltac:(unfold rc_lo in LO; lia)) as FRD5.
      pose proof (KEEP5 _ _ FRS ltac:(unfold rc_lo in LO; lia)) as FRS5. pose proof (KEEP5 _ _ ERRc ltac:(unfold rc_lo in LO; lia)) as ERR5.
      pose proof (KEEP5 _ _ MG4 ltac:(unfold rc_lo in LO; lia)) as MG5. pose proof (KEEP5 _ _ HEB3 ltac:(unfold rc_lo in LO; lia)) as HEB5.
      clear KEEP5.
      name_sp sp (-112)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply MALLOC; [| reflexivity | lia].
        split; [exact G5'|]. split; [rewrite Hsp; eassumption|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [bq|] ps6 ms6 PO; cbv beta iota in PO.
      - destruct PO as (av & m6 & E & OFm & MI6 & ST6 & AG6 & (B & bjunk & -> & G6 & BUF)).
        assert (OF6 : ps_outfile ps6 = ps_outfile s) by congruence.
        unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 86904)) with (Z_to_bv 64 86904) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G6 ltac:(left; reflexivity)) as (B1 & _ & _ & B4 & _). cbn [cb_addr cb_size fst snd] in B1, B4.
        lazymatch type of AG6 with agrees_on _ ?ma _ =>
        assert (KEEP6 : forall A cs, rw_cells ssegs ma A cs -> (bv_unsigned sp + -112 <= A \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells ssegs m6 A cs) end.
        { intros A cs HC HA. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HA as [HA|HA]; [left; lia| right].
          unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_SF_TOTAL. lia. }
        apply KEEP6 in CELLS5; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP6 in FRA5; [|lia]. apply KEEP6 in FRD5; [|lia]. apply KEEP6 in FRS5; [|lia].
        apply KEEP6 in ERR5; [|lia]. apply KEEP6 in MG5; [|lia]. apply KEEP6 in HEB5; [|lia].
        assert (AG06 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right].
          unfold in_block. apply Exists_cons_tl. exact Ha. }
        clear KEEP6 AG6 AG5' G5'.
        pose proof (blocks2_apart _ _ _ _ _ _ _ _ _ _ _ G6 ltac:(lia) ltac:(unfold PCAP_SF_TOTAL; lia)) as BP. unfold PCAP_SF_TOTAL in BP.
        pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl ssegs m6) as WM6.
        hide BUF. unfold implM. iprefix. step. step. if_cases Kb; [ idtac | try (zify_cond Kb; exfalso; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 B B1 Kb; lia)) ].
        unhide BUF.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P, P + 664)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
          apply (agrees_rw_cells _ _ _ _ _ AGW) in BUF; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; (keep_hyps CEILV sp R lo EB magic P n0 n1 n2 n3 l0 l1 l2 l3 B a BP Ha; lia)];
          assert (G6' : GIo K R ps6 ((bq, B, _) :: (q, P, PCAP_SF_TOTAL) :: CL) FB mm)
            by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |];
                apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3; lia)| apply Forall_nil]);
          assert (AG6' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
            by (eapply agrees_on_trans; [exact AG06|]; eapply agrees_on_weaken; [exact AGW|];
                intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; (keep_hyps CEILV sp R lo EB magic P n0 n1 n2 n3 l0 l1 l2 l3 a LO BU SPW P4 Ha; lia)| split; [exact (NB a Ha)| exact Logic.I]])
        end.
        apply evt_done. eapply K4OK; try eassumption.
        { lia. }
        { destruct (Z.ltb_spec 2048 SS); lia. }
      - destruct PO as (av & m6 & E & OFm & MI6 & ST6 & AG6 & -> & G6 & EN6).
        assert (OF6 : ps_outfile ps6 = ps_outfile s) by congruence.
        unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 86904)) with (Z_to_bv 64 86904) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        lazymatch type of AG6 with agrees_on _ ?ma _ =>
        assert (KEEP6 : forall A cs, rw_cells ssegs ma A cs -> (bv_unsigned sp + -112 <= A \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells ssegs m6 A cs) end.
        { intros A cs HC HA. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HA as [HA|HA]; [left; lia| right].
          unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_SF_TOTAL. lia. }
        apply KEEP6 in CELLS5; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP6 in FRA5; [|lia]. apply KEEP6 in FRD5; [|lia]. apply KEEP6 in FRS5; [|lia].
        apply KEEP6 in ERR5; [|lia]. apply KEEP6 in MG5; [|lia]. apply KEEP6 in HEB5; [|lia].
        assert (AG06 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right].
          unfold in_block. apply Exists_cons_tl. exact Ha. }
        clear KEEP6 AG6 AG5' G5'.
        pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl ssegs m6) as WM6.
        unfold implM. iprefix. pstep. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P, P + 664)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
          assert (G6' : GIo K R ps6 ((q, P, PCAP_SF_TOTAL) :: CL) FB mm)
            by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |];
                apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; lia| apply Forall_nil]);
          assert (AG6' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
            by (eapply agrees_on_trans; [exact AG06|]; eapply agrees_on_weaken; [exact AGW|];
                intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia| split; [exact (NB a Ha)| exact Logic.I]])
        end.
        apply evt_done. eapply K4FAIL; try eassumption. }
    (* [comment removed for export] *)
    assert (K3B : forall (ra5 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m5 : mem) (HS SS : Z) (LS : lenswap_t) (SC : sf_scale_t),
      (HS = 16 \/ HS = 24)%Z -> (1 <= SS < 2048)%Z ->
      mem_inv ssegs m5 -> munch [(P, P + 664)]%Z m3 m5 -> wmono ssegs m3 m5 ->
      rw_cells ssegs m5 P (pcells P sw maj min lt EXT (C8 (Z_to_bv 64 87024)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 SS))
                             (C8 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 HS)) (C4 (Z_to_bv 64 (lenswap_code LS))) (C4 (Z_to_bv 64 (sfscale_code SC)))) ->
      implM ssegs (chk_buf_model MOps (prims HO fo_nop sites) q f 0 sw maj min lt EXT HS SS LS SC) ps3 POSTQ
        (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 SS) a1' a2' a3' a4' a5' a6' a7'
                 z64 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x153b4) fc None m5 (seg_rom ssegs))).
    { intros ra5 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m5 HS SS LS SC HHS HSS MI5 MU5 WM5 CELLS5.
      destruct (PKEEP m5 MU5 WM5) as (G5 & AG5 & _ & ST5).
      clear CELLS MI2.
      unfold chk_buf_model. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. replace (if 2048 <? SS then 2048 else SS)%Z with SS by (destruct (Z.ltb_spec 2048 SS); lia).
      cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_free prims].
      unfold pcells in CELLS5.
      unfold implM. iprefix. step. step.
      destruct (PKEEP _ MU5 WM5) as (G5' & AG5' & KEEP5 & _). clear G5 AG5.
      pose proof (KEEP5 _ _ FRA ltac:(unfold rc_lo in LO; lia)) as FRA5. pose proof (KEEP5 _ _ FRD ltac:(unfold rc_lo in LO; lia)) as FRD5.
      pose proof (KEEP5 _ _ FRS ltac:(unfold rc_lo in LO; lia)) as FRS5. pose proof (KEEP5 _ _ ERRc ltac:(unfold rc_lo in LO; lia)) as ERR5.
      pose proof (KEEP5 _ _ MG4 ltac:(unfold rc_lo in LO; lia)) as MG5. pose proof (KEEP5 _ _ HEB3 ltac:(unfold rc_lo in LO; lia)) as HEB5.
      clear KEEP5.
      name_sp sp (-112)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply MALLOC; [| reflexivity | lia].
        split; [exact G5'|]. split; [rewrite Hsp; eassumption|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [bq|] ps6 ms6 PO; cbv beta iota in PO.
      - destruct PO as (av & m6 & E & OFm & MI6 & ST6 & AG6 & (B & bjunk & -> & G6 & BUF)).
        assert (OF6 : ps_outfile ps6 = ps_outfile s) by congruence.
        unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 86972)) with (Z_to_bv 64 86972) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G6 ltac:(left; reflexivity)) as (B1 & _ & _ & B4 & _). cbn [cb_addr cb_size fst snd] in B1, B4.
        lazymatch type of AG6 with agrees_on _ ?ma _ =>
        assert (KEEP6 : forall A cs, rw_cells ssegs ma A cs -> (bv_unsigned sp + -112 <= A \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells ssegs m6 A cs) end.
        { intros A cs HC HA. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HA as [HA|HA]; [left; lia| right].
          unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_SF_TOTAL. lia. }
        apply KEEP6 in CELLS5; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP6 in FRA5; [|lia]. apply KEEP6 in FRD5; [|lia]. apply KEEP6 in FRS5; [|lia].
        apply KEEP6 in ERR5; [|lia]. apply KEEP6 in MG5; [|lia]. apply KEEP6 in HEB5; [|lia].
        assert (AG06 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right].
          unfold in_block. apply Exists_cons_tl. exact Ha. }
        clear KEEP6 AG6 AG5' G5'.
        pose proof (blocks2_apart _ _ _ _ _ _ _ _ _ _ _ G6 ltac:(lia) ltac:(unfold PCAP_SF_TOTAL; lia)) as BP. unfold PCAP_SF_TOTAL in BP.
        pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl ssegs m6) as WM6.
        hide BUF. unfold implM. iprefix. step. step. if_cases Kb; [ try (zify_cond Kb; exfalso; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 B B1 Kb; lia)) | idtac ].
        unhide BUF.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P, P + 664)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
          apply (agrees_rw_cells _ _ _ _ _ AGW) in BUF; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; (keep_hyps CEILV sp R lo EB magic P n0 n1 n2 n3 l0 l1 l2 l3 SS B a BP Ha; lia)];
          assert (G6' : GIo K R ps6 ((bq, B, _) :: (q, P, PCAP_SF_TOTAL) :: CL) FB mm)
            by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |];
                apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3; lia)| apply Forall_nil]);
          assert (AG6' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
            by (eapply agrees_on_trans; [exact AG06|]; eapply agrees_on_weaken; [exact AGW|];
                intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; (keep_hyps CEILV sp R lo EB magic P n0 n1 n2 n3 l0 l1 l2 l3 a LO BU SPW P4 Ha; lia)| split; [exact (NB a Ha)| exact Logic.I]])
        end.
        apply evt_done. eapply K4OK; try eassumption.
        { lia. }
        { destruct (Z.ltb_spec 2048 SS); lia. }
      - destruct PO as (av & m6 & E & OFm & MI6 & ST6 & AG6 & -> & G6 & EN6).
        assert (OF6 : ps_outfile ps6 = ps_outfile s) by congruence.
        unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 86972)) with (Z_to_bv 64 86972) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        lazymatch type of AG6 with agrees_on _ ?ma _ =>
        assert (KEEP6 : forall A cs, rw_cells ssegs ma A cs -> (bv_unsigned sp + -112 <= A \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells ssegs m6 A cs) end.
        { intros A cs HC HA. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HA as [HA|HA]; [left; lia| right].
          unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_SF_TOTAL. lia. }
        apply KEEP6 in CELLS5; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP6 in FRA5; [|lia]. apply KEEP6 in FRD5; [|lia]. apply KEEP6 in FRS5; [|lia].
        apply KEEP6 in ERR5; [|lia]. apply KEEP6 in MG5; [|lia]. apply KEEP6 in HEB5; [|lia].
        assert (AG06 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right].
          unfold in_block. apply Exists_cons_tl. exact Ha. }
        clear KEEP6 AG6 AG5' G5'.
        pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl ssegs m6) as WM6.
        unfold implM. iprefix. pstep. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P, P + 664)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]);
          assert (G6' : GIo K R ps6 ((q, P, PCAP_SF_TOTAL) :: CL) FB mm)
            by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU6 | exact WM6 |];
                apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; lia| apply Forall_nil]);
          assert (AG6' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
            by (eapply agrees_on_trans; [exact AG06|]; eapply agrees_on_weaken; [exact AGW|];
                intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia| split; [exact (NB a Ha)| exact Logic.I]])
        end.
        apply evt_done. eapply K4FAIL; try eassumption. }
    (* [comment removed for export] *)
    assert (K2 : forall (ra5 t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m5 : mem) (LS : lenswap_t) (SC : sf_scale_t),
      mem_inv ssegs m5 -> munch [(P, P + 664)]%Z m3 m5 -> wmono ssegs m3 m5 ->
      rw_cells ssegs m5 P (pcells P sw maj min lt EXT (C8 (Z_to_bv 64 87024)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 snap))
                             (C8 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 (lenswap_code LS))) (C4 (Z_to_bv 64 (sfscale_code SC)))) ->
      implM ssegs (chk_sf_model MOps (prims HO fo_nop sites) q f 0 mi sw maj min lt EXT snap LS SC) ps3 POSTQ
        (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 snap) (Z_to_bv 64 (P + 648)) a2' a3' a4' a5' a6' a7'
                 z64 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 P) (Z_to_bv 64 min) (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (sxv l0 l1 l2 l3))
                 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1531c) fc None m5 (seg_rom ssegs))).
    { intros ra5 t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m5 LS SC MI5 MU5 WM5 CELLS5.
      clear CELLS MI2. unfold chk_sf_model. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. unfold pcells in CELLS5.
      hide FRA. hide FRD. hide FRS. hide ERRc. hide MG4. hide HEB3.
      destruct (Z.eq_dec mi KUZNETZOV_TCPDUMP_MAGIC) as [EK|NK].
      - (* [comment removed for export] *)
        subst mi. rewrite Z.eqb_refl.
        unfold implM. iprefix. do 3 step. lit_branch. step. rewrite (sx32_small lt) by lia. do 2 step. pstep.
        destruct (Z.eq_dec lt 1) as [EL1|EL1].
        + replace (lt =? DLT_EN10MB) with true by (unfold DLT_EN10MB; symmetry; apply Z.eqb_eq; lia). cbv iota.
          step. if_cases Kd; [ try (zify_cond Kd; exfalso; (keep_hyps CEILV EL1 Kd; lia)) | idtac ]. do 2 step.
          destruct (Z.le_gt_cases snap 2147483633) as [S1|S1].
          * replace (snap <=? INT_MAX - 14) with true by (unfold INT_MAX; symmetry; apply Z.leb_le; lia). cbv iota.
            step. if_cases Ks; [ try (zify_cond Ks; rewrite ?signed_lit_small in Ks by lia; exfalso; lia) | idtac ].
            step. rewrite (addiw_small snap 14) by lia.
            step. do 2 step.
            destruct (Z.lt_ge_cases (snap + 14) 2048) as [S2|S2].
            -- step. if_cases Kt; [ idtac | try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) ].
               apply evt_done. eapply K3B; [right; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
            -- step. if_cases Kt; [ try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) | idtac ]. step.
               apply evt_done. eapply K3A; [right; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
          * replace (snap <=? INT_MAX - 14) with false by (unfold INT_MAX; symmetry; apply Z.leb_gt; lia). cbv iota.
            step. if_cases Ks; [ idtac | try (zify_cond Ks; rewrite ?signed_lit_small in Ks by lia; exfalso; lia) ].
            step. pstep. do 2 step. step. if_false. step.
            apply evt_done. eapply K3A; [right; reflexivity | unfold INT_MAX; lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
        + replace (lt =? DLT_EN10MB) with false by (unfold DLT_EN10MB; symmetry; apply Z.eqb_neq; lia). cbv iota.
          step. if_cases Kd; [ idtac | try (zify_cond Kd; exfalso; (keep_hyps CEILV EL1 Kd; lia)) ]. do 2 step.
          destruct (Z.lt_ge_cases snap 2048) as [S2|S2].
          * step. if_cases Kt; [ idtac | try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) ].
            apply evt_done. eapply K3B; [right; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
          * step. if_cases Kt; [ try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) | idtac ].
            apply evt_done. eapply K3A; [right; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
      - replace (mi =? KUZNETZOV_TCPDUMP_MAGIC) with false by (symmetry; apply Z.eqb_neq; exact NK). cbv iota.
        unfold KUZNETZOV_TCPDUMP_MAGIC in NK.
        unfold implM. iprefix. do 2 step. step. if_cases Km; [ idtac | try (zify_cond Km; exfalso; (keep_hyps CEILV sp R lo EB magic P n0 n1 n2 n3 l0 l1 l2 l3 mi NK Km; lia)) ].
        step. pstep. do 2 step.
        destruct (Z.lt_ge_cases snap 2048) as [S2|S2].
        + step. if_cases Kt; [ try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) | idtac ].
          apply evt_done. eapply K3B; [left; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5].
        + step. if_cases Kt; [ idtac | try (zify_cond Kt; exfalso; (keep_hyps CEILV sp EB magic P n0 n1 n2 n3 l0 l1 l2 l3 S2 Kt; lia)) ].
          apply evt_done. eapply K3A; [left; reflexivity | lia | assumption | exact MU5 | exact WM5 | exact CELLS5]. }
    pose proof (munch_refl [(P, P + 664)]%Z m3) as MU3. pose proof (wmono_refl ssegs m3) as WM3.
    hide HEB3. hide MG4. hide ERRc.
    unfold implM. iprefix. do 6 step.
    rewrite (lt16_word l0 l1 l2 l3) by lia. step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply linktype_to_dlt_proof; [eassumption | reflexivity | lia]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 86508)) with (Z_to_bv 64 86508) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold lt.
    do 3 step. rewrite (ltext_word l0 l1 l2 l3) by lia. fold EXT.
    rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
    do 3 step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply adjust_snapshot_proof; [reflexivity | lia | reflexivity | unfold le4val; lia]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 86532)) with (Z_to_bv 64 86532) by (symmetry; apply ret_pc_even; [lia|reflexivity]). fold snap.
    do 7 pstep. step. if_false. step. if_false.
    (* [comment removed for export] *)
    do 2 step.
    destruct (Z.eq_dec mi NSEC_TCPDUMP_MAGIC) as [EN|NN].
    - subst mi. rewrite Z.eqb_refl. step. lit_branch. step. pstep. step.
      destruct (Z.eq_dec maj 543) as [M543|M543].
      + replace (maj =? 2) with false by (symmetry; apply Z.eqb_neq; lia). replace (maj =? 543) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
        step. if_cases Kc; [ try (zify_cond Kc; exfalso; (keep_hyps CEILV M543 Kc; lia)) | idtac ]. step. step. pstep. step.
        apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
      + replace (maj =? 543) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Kc; [ idtac | try (zify_cond Kc; exfalso; (keep_hyps CEILV M543 Kc; lia)) ]. step.
        destruct (Z.eq_dec maj 2) as [M2|M2].
        * replace (maj =? 2) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
          step. if_cases Kc2; [ try (zify_cond Kc2; exfalso; (keep_hyps CEILV M2 Kc2; lia)) | idtac ].
          destruct (Z.lt_ge_cases 2 min) as [Mn|Mn].
          -- step. if_cases Kc3; [ idtac | try (zify_cond Kc3; exfalso; (keep_hyps CEILV sp EB magic P min n0 n1 n2 n3 l0 l1 l2 l3 Mn Kc3; lia)) ]. step.
             destruct (Z.eq_dec min 3) as [M3|M3].
             ++ replace (min <? 3) with false by (symmetry; apply Z.ltb_ge; lia). replace (min =? 3) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
                step. if_cases Kc4; [ try (zify_cond Kc4; exfalso; (keep_hyps CEILV M3 Kc4; lia)) | idtac ]. step. pstep. step.
                apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
             ++ replace (min <? 3) with false by (symmetry; apply Z.ltb_ge; lia). replace (min =? 3) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
                step. if_cases Kc4; [ idtac | try (zify_cond Kc4; exfalso; (keep_hyps CEILV M3 Kc4; lia)) ]. pstep.
                apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
          -- replace (min <? 3) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
             step. if_cases Kc3; [ try (zify_cond Kc3; exfalso; (keep_hyps CEILV sp EB magic P min n0 n1 n2 n3 l0 l1 l2 l3 Mn Kc3; lia)) | idtac ]. step. pstep. step.
             apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
        * replace (maj =? 2) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
          step. if_cases Kc2; [ idtac | try (zify_cond Kc2; exfalso; (keep_hyps CEILV M2 Kc2; lia)) ]. pstep.
          apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
    - replace (mi =? NSEC_TCPDUMP_MAGIC) with false by (symmetry; apply Z.eqb_neq; exact NN). unfold NSEC_TCPDUMP_MAGIC in NN.
      step. if_cases Km; [ idtac | try (zify_cond Km; exfalso; (keep_hyps CEILV sp R lo EB magic P n0 n1 n2 n3 l0 l1 l2 l3 mi NN Km; lia)) ]. pstep. step.
      destruct (Z.eq_dec maj 543) as [M543|M543].
      + replace (maj =? 2) with false by (symmetry; apply Z.eqb_neq; lia). replace (maj =? 543) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
        step. if_cases Kc; [ try (zify_cond Kc; exfalso; (keep_hyps CEILV M543 Kc; lia)) | idtac ]. step. step. pstep. step.
        apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
      + replace (maj =? 543) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Kc; [ idtac | try (zify_cond Kc; exfalso; (keep_hyps CEILV M543 Kc; lia)) ]. step.
        destruct (Z.eq_dec maj 2) as [M2|M2].
        * replace (maj =? 2) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
          step. if_cases Kc2; [ try (zify_cond Kc2; exfalso; (keep_hyps CEILV M2 Kc2; lia)) | idtac ].
          destruct (Z.lt_ge_cases 2 min) as [Mn|Mn].
          -- step. if_cases Kc3; [ idtac | try (zify_cond Kc3; exfalso; (keep_hyps CEILV sp EB magic P min n0 n1 n2 n3 l0 l1 l2 l3 Mn Kc3; lia)) ]. step.
             destruct (Z.eq_dec min 3) as [M3|M3].
             ++ replace (min <? 3) with false by (symmetry; apply Z.ltb_ge; lia). replace (min =? 3) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
                step. if_cases Kc4; [ try (zify_cond Kc4; exfalso; (keep_hyps CEILV M3 Kc4; lia)) | idtac ]. step. pstep. step.
                apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
             ++ replace (min <? 3) with false by (symmetry; apply Z.ltb_ge; lia). replace (min =? 3) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
                step. if_cases Kc4; [ idtac | try (zify_cond Kc4; exfalso; (keep_hyps CEILV M3 Kc4; lia)) ]. pstep.
                apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
          -- replace (min <? 3) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
             step. if_cases Kc3; [ try (zify_cond Kc3; exfalso; (keep_hyps CEILV sp EB magic P min n0 n1 n2 n3 l0 l1 l2 l3 Mn Kc3; lia)) | idtac ]. step. pstep. step.
             apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
        * replace (maj =? 2) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
          step. if_cases Kc2; [ idtac | try (zify_cond Kc2; exfalso; (keep_hyps CEILV M2 Kc2; lia)) ]. pstep.
          apply evt_done. eapply K2; [assumption | exact MU3 | exact WM3 | exact CELLS].
  Qed.
  End Sz4.
  Lemma chk_fill : ltac:(let t := eval cbv delta [chk_fill__stmt] in chk_fill__stmt in exact t).
  Proof using FREE HFL HPL MALLOC SFL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m3 ps3 q P maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw mid junk8 e3. ltac2:(SecDiet.SzSec.closeP 'chk_fill__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Chk.

End WithCeil.
End F_sfpcap_chkA.

(* [comment removed for export] *)
Module F_sfpcapng_aiA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition AI_FMT_OOM_IF : Z := 0x10d02.     (* [comment removed for export] *)
Definition AI_FMT_TOOMANY : Z := 0x1034f.    (* [comment removed for export] *)
Definition AI_FMT_TOOSHORT : Z := 0x10cd0.   (* [comment removed for export] *)
Definition AI_FMT_ENDOFOPT : Z := 0x1084a.   (* [comment removed for export] *)
Definition AI_FMT_TSRESOL_LEN : Z := 0x102ff.
Definition AI_FMT_TSOFF_LEN : Z := 0x1079c.
Definition AI_STR_TSOFF_DUP : Z := 0x10b41.  (* [comment removed for export] *)
Definition AI_STR_TSRESOL_DUP : Z := 0x1046b. (* [comment removed for export] *)
Definition AI_FMT_DEC_HIGH : Z := 0x10688.
Definition AI_FMT_BIN_HIGH : Z := 0x108ee.

Definition out_of_image (A n : Z) : Prop := A + n <= 0x10000 \/ 0x55000 <= A.

Section AIA.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (st : PS) (C1 C2 FB : list cblk) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIo K R st (C1 ++ IBLK i I s ++ C2) FB m.
  Hypothesis ST : stk ssegs m lo (bv_unsigned sp).
  Hypothesis LO : usp0 R - 8388608 <= lo.
  Hypothesis BU : lo + (65536 + 112) <= bv_unsigned sp.
  Hypothesis SPM : bv_unsigned sp <= rc_spmain R.
  Hypothesis MI : mem_inv ssegs m.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : bv_unsigned sp mod 16 = 0.
  Hypothesis RSP : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPW : 0x7fff80000000 <= usp0 R.
  Hypothesis SP47 : usp0 R <= 2^47.
  Hypothesis HS : pc_priv p = PrivNg s i.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis B14 : 0 < B /\ B + pc_bufalloc p <= CEILZ.
  Hypothesis APB : P + 680 <= B \/ B + pc_bufalloc p <= P.
  (* [comment removed for export] *)
  Hypothesis P5 : out_of_image P 680.
  Hypothesis HPV : rw_cells ssegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].
  Hypothesis HNG : rw_cells ssegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad).
  Hypothesis HIF : ifaces_ok p I m.
  Hypothesis UTS : 0 < ng_user_tsresol s < 2^64.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis WMB : 0 <= ng_max_blocksize s < 2^32.
  Hypothesis HBUF : rw_cells ssegs m B [CB (Z.to_nat (pc_bufalloc p)) bs].
  Hypothesis PFX : firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p).
  Hypothesis LENB : Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32.
  Hypothesis GRD : Forall (fun z => 0 <= z < 256) (pc_bufdata p).
  Hypothesis HCUR : rw_cells ssegs m CUR (cursor_cells B c cpad).
  Hypothesis CUR1 : bv_unsigned sp <= CUR.
  Hypothesis CUR2 : CUR + 24 <= rc_spmain R.
  Hypothesis CUR8 : CUR mod 8 = 0.
  Hypothesis IDB0 : 0 <= idb_off.
  Hypothesis COFF : cur_off c = idb_off + 8.
  Hypothesis CREM : 0 <= cur_remaining c.
  Hypothesis CEND : cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)).
  Hypothesis CBT : 0 <= cur_block_type c < 2^32.
  Hypothesis HEB : rw_cells ssegs m EB [CB 256 ej].
  Hypothesis EBX : (bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ EB = P + 216.
  Hypothesis EB64 : 0 < EB /\ EB + 256 < 2^64.
  (* [comment removed for export] *)
  Hypothesis CLB : forall a, in_block (C1 ++ C2) a -> a < CEILZ.
  Hypothesis INPc : forall a, P <= a < P + 680 -> in_block (C1 ++ C2) a.
  Hypothesis INBc : forall a, B <= a < B + pc_bufalloc p -> in_block (C1 ++ C2) a.
  Hypothesis CRE : client_range R (C1 ++ C2) (bv_unsigned sp) EB 256.
  Hypothesis EBiv : client_iv R (C1 ++ C2) (EB, EB + 256).

  #[local] Notation POSTQ := (add_interface_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Notation AGP := (ai_AGP sp C1 C2 P B CUR EB p m).
  #[local] Notation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  #[local] Notation AIREST := (ai_REST K R C1 C2 FB P B CUR EB p s c ej (ps_outfile st)).
  #[local] Notation AIREST_F := (ai_REST_F K R C1 C2 FB P B CUR p s (ps_outfile st)).

  Open Scope bv_scope.

  (* [comment removed for export] *)
  Definition ai_exit__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (st3 : PS) (ok : bool) (c' : cursor) (p' : pcapT) (msg : list Z) (hd : list cell),
    mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -112) -> AGP m3 ->
    rw_cells ssegs m3 (bv_unsigned sp + -112) hd -> cells_size hd = 8%nat -> FRAME m3 ->
    AIREST m3 st3 (ok, c', p', msg) ->
    evt ssegs (POSTQ (ok, c', p', msg) st3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' y0 y1 (Z_to_bv 64 (Z.b2z ok)) a1' a2' a3' a4' a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x173b8) fc None m3 (seg_rom ssegs)).
  Section Sz1.
  Variables ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 st3 ok c' p' msg hd : ltac2:(SecDiet.SzSec.tyM 'ai_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ai_exit__body : ltac2:(SecDiet.SzSec.bodyP 'ai_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU. pin_using (fun (BU : unit) => tt).
    intros MI3 ST3 AG3 HD3 Hhd FR3 REST.
    clear HPV HNG HBUF HCUR HEB.
    destruct (rw_cells_forget _ _ _ _ HD3) as [hj HD3']. clear HD3. rewrite Hhd in HD3'.
    unfold ai_FRAME in FR3.
    pose proof (rw_cells_uncut _ _ _ _ _ HD3' FR3 ltac:(cbn; lia)) as FR. clear HD3' FR3. cbn [app] in FR.
    do 15 step.
    release_frame FR ST3 (bv_unsigned sp).
    apply evt_done. unfold add_interface_post.
    destruct REST as (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & RM).
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 (Z.b2z ok)), mm, s', i', I', pad', bs' end.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OFr|]. split; [assumption|]. split; [assumption|]. split; [exact AG3|].
    split; [exact E1|]. split; [exact G3|]. split; [exact NG3|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|]. split; [reflexivity|]. exact RM.
  Qed.
  End Sz1.
  Lemma ai_exit : ltac:(let t := eval cbv delta [ai_exit__stmt] in ai_exit__stmt in exact t).
  Proof using BU. intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 st3 ok c' p' msg hd. ltac2:(SecDiet.SzSec.closeP 'ai_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition airest_f_frame__stmt : Prop := forall (m3 m4 : mem) (st' : PS) (c' : cursor) (p' : pcapT) (lo1 hi1 k : Z),
    AIREST_F m3 st' c' p' -> munch [(lo1, hi1); (EB, EB + k)]%Z m3 m4 -> wmono ssegs m3 m4 ->
    (usp0 R - 8388608 <= lo1)%Z -> (hi1 <= bv_unsigned sp + -112)%Z -> (0 <= k <= 256)%Z ->
    AIREST_F m4 st' c' p'.
  Section Sz2.
  Variables m3 m4 st' c' p' lo1 hi1 k : ltac2:(SecDiet.SzSec.tyM 'airest_f_frame__stmt "vvvvvvvv" @m3).
  Lemma airest_f_frame__body : ltac2:(SecDiet.SzSec.bodyP 'airest_f_frame__stmt "vvvvvvvv").
  Proof using APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SPM SPW. pin_using (fun (APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SPM SPW : unit) => tt).
    intros (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & IC3 & (ccs' & CC3 & Hccs')) MU WM L1 H1 HK.
    clear HPV HNG HBUF HCUR HEB HIF.
    assert (AGS : agrees_on (fun a => outside [(lo1, hi1); (EB, EB + k)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    exists s', i', I', pad', bs'. split; [exact OFr|]. split; [exact E1|].
    split.
    { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU | exact WM |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [| apply Forall_nil].
      destruct EBiv as [X|X]; [left; cbn [fst snd] in *; lia| right]. unfold iv_in_block in *. apply Exists_app. right.
      apply Exists_exists in X as (b & Hb & Hr). apply Exists_exists. exists b. split; [exact Hb|]. cbn [fst snd] in *. lia. }
    split; [transport NG3 m4 AGS ltac:(prs); exact NG3|].
    split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [transport BUF3 m4 AGS ltac:(prs); exact BUF3|].
    split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|].
    split.
    { destruct i' as [q|]; [| exact IC3]. destruct IC3 as [(junk & IB3) SZ]. split; [| exact SZ]. exists junk.
      pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(apply in_or_app; left; left; reflexivity)) as (Q1 & _ & _ & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q4.
      assert (API : (P + 680 <= I' \/ I' + 40 * ng_ifaces_size s' <= P)%Z).
      { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
      transport IB3 m4 AGS ltac:(prs). exact IB3. }
    exists ccs'. split; [| exact Hccs']. transport CC3 m4 AGS ltac:(prs). exact CC3.
  Qed.
  End Sz2.
  Lemma airest_f_frame : ltac:(let t := eval cbv delta [airest_f_frame__stmt] in airest_f_frame__stmt in exact t).
  Proof using APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SPM SPW. intros m3 m4 st' c' p' lo1 hi1 k. ltac2:(SecDiet.SzSec.closeP 'airest_f_frame__body "vvvvvvvv"). Qed.

  Lemma airest_f_done : forall (m' : mem) (st' : PS) (c' : cursor) (p' : pcapT) (msg : list Z),
    AIREST_F m' st' c' p' ->
    (exists junk'', rw_cells ssegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'']) ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    AIREST m' st' (false, c', p', msg).
  Proof using Type. pin_using tt.
    intros m' st' c' p' msg (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & IC3 & CC3) HE HL HOK.
    exists s', i', I', pad', bs'. split; [exact OFr|]. split; [exact E1|]. split; [exact G3|]. split; [exact NG3|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|]. cbv iota. split; [exact IC3|]. split; [exact CC3|]. split; [exact HE|]. split; [exact HL| exact HOK].
  Qed.

  (* [comment removed for export] *)
  Definition ai_snp__stmt : Prop := forall (ra' t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v : word)
      (m3 : mem) (st3 : PS) (fs : string) (args : list farg) (FMTA : Z) (msg : list Z) (c' : cursor) (p' : pcapT) (hd : list cell),
    mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -112) -> AGP m3 ->
    rw_cells ssegs m3 (bv_unsigned sp + -112) hd -> cells_size hd = 8%nat -> FRAME m3 ->
    rw_cells ssegs m3 EB [CB 256 ej] ->
    fmt_at m3 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
    (forall (CL : list cblk) D dn, Forall2 (farg_word R CL (bv_unsigned sp + -112) D dn m3) args (firstn (length args) [a3v; a4v; a5'])) ->
    Fmt.snprintf 256 fs args = msg -> items_okb (fmt fs) = true -> Forall arg_ok args ->
    AIREST_F m3 st3 c' p' ->
    evt ssegs (POSTQ (false, c', p', msg) st3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 EB) y1 a0' (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3v a4v a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x173ac) fc None m3 (seg_rom ssegs)).
  Section Sz4.
  Variables ra' t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 st3 fs args FMTA msg c' p' hd : ltac2:(SecDiet.SzSec.tyM 'ai_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ai_snp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using ALN APB B14 BU CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SNPRINTF SPM SPW TP. pin_using (fun (ALN APB B14 BU CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros MI3 ST3 AG3 HD3 Hhd FR3 HEB3 FAT FOK ALEN FW EMSG FIT AOK REST.
    clear HPV HNG HBUF HCUR HEB HIF.
    pose proof REST as REST'. destruct REST' as (s' & i' & I' & pad' & bs' & _ & _ & G3 & _).
    unfold ai_FRAME in FR3.
    hide HD3. hide FR3. hide HEB3.
    do 2 step. unhide HEB3.
    name_sp sp (-112)%Z.
    eapply evt_cut.
    { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R st3 (IBLK i' I' s' ++ C1 ++ C2) FB lo EB 256%Z FMTA fs args ej);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | reflexivity | reflexivity | lia | exact FAT | exact FOK | exact ALEN | rewrite Hsp; apply FW | exact HEB3
        | destruct CRE as [Hb|Hs]; [left; intros a Ha; apply in_block_app; right; exact (Hb a Ha) | right; rewrite Hsp; lia] ]. }
    cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 95156)) with (Z_to_bv 64 95156) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -112 - STDIO_STACK, bv_unsigned sp + -112); (EB, EB + 256)]%Z a) m3 m4)
      by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    unfold STDIO_STACK in AGS, MU4.
    pose proof (airest_f_frame _ _ _ _ _ _ _ _ REST MU4 WM4 ltac:(lia) ltac:(lia) ltac:(lia)) as REST4.
    unhide HD3. unhide FR3.
    transport HD3 m4 AGS ltac:(prs). transport FR3 m4 AGS ltac:(prs).
    hide HD3. hide FR3. hide HEB4.
    step.
    unhide HD3. unhide FR3. unhide HEB4.
    eapply (ai_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 st3 false c' p' msg hd);
      [exact MI4 | exact ST4 | | exact HD3 | exact Hhd | exact FR3 |].
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] (_ & _ & Hn & _)]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
    apply (airest_f_done _ _ _ _ _ REST4).
    - exists junk4. pose proof (snprintf_length 256 fs args) as LS. change (Z.to_nat (256 - 1)) with 255%nat in LS. rewrite EMSG in LS, HEB4.
      change (Z.to_nat 256) with 256%nat in HEB4. replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB4 by lia. exact HEB4.
    - pose proof (snprintf_length 256 fs args) as LS. rewrite EMSG in LS. change (Z.to_nat (256 - 1)) with 255%nat in LS. lia.
    - rewrite <- EMSG. apply snprintf_ok; [exact FIT| exact AOK].
  Qed.
  End Sz4.
  Lemma ai_snp : ltac:(let t := eval cbv delta [ai_snp__stmt] in ai_snp__stmt in exact t).
  Proof using ALN APB B14 BU CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SNPRINTF SPM SPW TP. intros ra' t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 st3 fs args FMTA msg c' p' hd. ltac2:(SecDiet.SzSec.closeP 'ai_snp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_mcp__stmt : Prop := forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (st3 : PS) (SRC n : Z) (str : string) (msg : list Z) (c' : cursor) (p' : pcapT) (hd : list cell),
    mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -112) -> AGP m3 ->
    rw_cells ssegs m3 (bv_unsigned sp + -112) hd -> cells_size hd = 8%nat -> FRAME m3 ->
    rw_cells ssegs m3 EB [CB 256 ej] ->
    fmt_at m3 SRC str -> (Z.of_nat (String.length str) + 1 = n)%Z -> (n <= 256)%Z ->
    map b8 msg = map (fun ch => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii ch))) (String.list_ascii_of_string str) ->
    Forall (fun z => 0 < z < 256)%Z msg ->
    AIREST_F m3 st3 c' p' ->
    evt ssegs (POSTQ (false, c', p', msg) st3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 EB) y1 a0' (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x17388) fc None m3 (seg_rom ssegs)).
  Section Sz5.
  Variables ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 st3 SRC n str msg c' p' hd : ltac2:(SecDiet.SzSec.tyM 'ai_mcp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ai_mcp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_mcp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using APB B14 BU CBT CEND COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HinP IDB0 LENB LO P14 P5 RSP SFL SPM SPW UTS WMB. pin_using (fun (APB B14 BU CBT CEND COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HinP IDB0 LENB LO P14 P5 RSP SFL SPM SPW UTS WMB : unit) => tt).
    intros MI3 ST3 AG3 HD3 Hhd FR3 HEB3 [SRCB SRCR] LN NB EMSG MOK REST.
    clear HPV HNG HBUF HCUR HEB HIF.
    unfold ai_FRAME in FR3.
    assert (LM : length msg = String.length str).
    { apply (f_equal (@length _)) in EMSG. rewrite !length_map, length_list_ascii in EMSG. exact EMSG. }
    pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat n; (256 - Z.to_nat n)%nat] HEB3 ltac:(cbn; lia)) as HE'. clear HEB3. cbn [mk_CB_cells app] in HE'.
    destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
    lazymatch type of HE2 with rw_cells _ _ ?A _ => replace A with (EB + n)%Z in HE2 by lia end.
    destruct P14 as [P1 P4].
    hide HD3. hide FR3. hide HE2.
    do 2 step.
    eapply evt_cut.
    { eapply (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB SRC n);
        [reflexivity | reflexivity | reflexivity | exact SRCB | rewrite length_app, length_map, length_list_ascii; cbn [length]; lia | lia | exact HE1
        | pose proof P5 as P5'; unfold out_of_image in P5'; destruct EBX as [X| ->]; lia | lia | lia | exact MI3]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m4 & -> & MU4 & WM4 & MI4 & HE1' & _). clear HE1.
    replace (ret_pc (Z_to_bv 64 95120)) with (Z_to_bv 64 95120) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (AGS : agrees_on (fun a => outside [(EB, EB + n)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (MU4' : munch [(bv_unsigned sp + -112, bv_unsigned sp + -112); (EB, EB + n)]%Z m3 m4).
    { intros a Ho. apply MU4. cbn [outside fst snd] in *. tauto. }
    pose proof (airest_f_frame _ _ _ _ _ _ _ _ REST MU4' WM4 ltac:(lia) ltac:(lia) ltac:(lia)) as REST4.
    assert (ST4 : stk ssegs m4 lo (bv_unsigned sp + -112)).
    { eapply stk_transport_disjoint; [exact ST3 | exact MU4 | exact WM4 | cbn [disjoint_from]; destruct EBX as [X| ->]; unfold rc_lo in *; lia]. }
    unhide HD3. unhide FR3. unhide HE2.
    transport HD3 m4 AGS ltac:(prs). transport FR3 m4 AGS ltac:(prs). transport HE2 m4 AGS ltac:(prs).
    hide HD3. hide FR3. hide HE2. hide HE1'.
    do 2 step.
    unhide HD3. unhide FR3. unhide HE2. unhide HE1'.
    eapply (ai_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 st3 false c' p' msg hd);
      [exact MI4 | exact ST4 | | exact HD3 | exact Hhd | exact FR3 |].
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a (_ & _ & _ & Hn & _); cbn [outside]. split; [lia| exact Logic.I]. }
    apply (airest_f_done _ _ _ _ _ REST4).
    - lazymatch type of HE2 with rw_cells _ _ _ [CB _ ?j] => exists j end.
      join_cells HE1' HE2.
      eapply rw_cells_recell; [exact HE1' | pose proof (proj1 (proj1 HE1')) as WF; cbn in WF |- *; rewrite ?length_app, ?length_map, ?length_list_ascii in *; cbn [length] in *; repeat split; try lia; tauto |].
      cbn [cells_bytes cbytes app]. rewrite EMSG, <- app_assoc. reflexivity.
    - rewrite LM. lia.
    - exact MOK.
  Qed.
  End Sz5.
  Lemma ai_mcp : ltac:(let t := eval cbv delta [ai_mcp__stmt] in ai_mcp__stmt in exact t).
  Proof using APB B14 BU CBT CEND COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HinP IDB0 LENB LO P14 P5 RSP SFL SPM SPW UTS WMB. intros ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 st3 SRC n str msg c' p' hd. ltac2:(SecDiet.SzSec.closeP 'ai_mcp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AIA.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition AI_FMT_OOM_IF : Z := 0x10d02.     (* [comment removed for export] *)
Definition AI_FMT_TOOMANY : Z := 0x1034f.    (* [comment removed for export] *)
Definition AI_FMT_TOOSHORT : Z := 0x10cd0.   (* [comment removed for export] *)
Definition AI_FMT_ENDOFOPT : Z := 0x1084a.   (* [comment removed for export] *)
Definition AI_FMT_TSRESOL_LEN : Z := 0x102ff.
Definition AI_FMT_TSOFF_LEN : Z := 0x1079c.
Definition AI_STR_TSOFF_DUP : Z := 0x10b41.  (* [comment removed for export] *)
Definition AI_STR_TSRESOL_DUP : Z := 0x1046b. (* [comment removed for export] *)
Definition AI_FMT_DEC_HIGH : Z := 0x10688.
Definition AI_FMT_BIN_HIGH : Z := 0x108ee.

Definition out_of_image (A n : Z) : Prop := A + n <= 0x10000 \/ 0x56000 <= A.

Section AIA.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (st : PS) (C1 C2 FB : list cblk) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIo K R st (C1 ++ IBLK i I s ++ C2) FB m.
  Hypothesis ST : stk usegs m lo (bv_unsigned sp).
  Hypothesis LO : usp0 R - 8388608 <= lo.
  Hypothesis BU : lo + (65536 + 112) <= bv_unsigned sp.
  Hypothesis SPM : bv_unsigned sp <= rc_spmain R.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : bv_unsigned sp mod 16 = 0.
  Hypothesis RSP : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPW : 0x7fff80000000 <= usp0 R.
  Hypothesis SP47 : usp0 R <= 2^47.
  Hypothesis HS : pc_priv p = PrivNg s i.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis B14 : 0 < B /\ B + pc_bufalloc p <= CEILZ.
  Hypothesis APB : P + 680 <= B \/ B + pc_bufalloc p <= P.
  (* [comment removed for export] *)
  Hypothesis P5 : out_of_image P 680.
  Hypothesis HPV : rw_cells usegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].
  Hypothesis HNG : rw_cells usegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad).
  Hypothesis HIF : ifaces_ok p I m.
  Hypothesis UTS : 0 < ng_user_tsresol s < 2^64.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis WMB : 0 <= ng_max_blocksize s < 2^32.
  Hypothesis HBUF : rw_cells usegs m B [CB (Z.to_nat (pc_bufalloc p)) bs].
  Hypothesis PFX : firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p).
  Hypothesis LENB : Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32.
  Hypothesis GRD : Forall (fun z => 0 <= z < 256) (pc_bufdata p).
  Hypothesis HCUR : rw_cells usegs m CUR (cursor_cells B c cpad).
  Hypothesis CUR1 : bv_unsigned sp <= CUR.
  Hypothesis CUR2 : CUR + 24 <= rc_spmain R.
  Hypothesis CUR8 : CUR mod 8 = 0.
  Hypothesis IDB0 : 0 <= idb_off.
  Hypothesis COFF : cur_off c = idb_off + 8.
  Hypothesis CREM : 0 <= cur_remaining c.
  Hypothesis CEND : cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)).
  Hypothesis CBT : 0 <= cur_block_type c < 2^32.
  Hypothesis HEB : rw_cells usegs m EB [CB 256 ej].
  Hypothesis EBX : (bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ EB = P + 216.
  Hypothesis EB64 : 0 < EB /\ EB + 256 < 2^64.
  (* [comment removed for export] *)
  Hypothesis CLB : forall a, in_block (C1 ++ C2) a -> a < CEILZ.
  Hypothesis INPc : forall a, P <= a < P + 680 -> in_block (C1 ++ C2) a.
  Hypothesis INBc : forall a, B <= a < B + pc_bufalloc p -> in_block (C1 ++ C2) a.
  Hypothesis CRE : client_range R (C1 ++ C2) (bv_unsigned sp) EB 256.
  Hypothesis EBiv : client_iv R (C1 ++ C2) (EB, EB + 256).

  #[local] Notation POSTQ := (add_interface_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Notation AGP := (ai_AGP sp C1 C2 P B CUR EB p m).
  #[local] Notation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  #[local] Notation AIREST := (ai_REST K R C1 C2 FB P B CUR EB p s c ej (ps_outfile st)).
  #[local] Notation AIREST_F := (ai_REST_F K R C1 C2 FB P B CUR p s (ps_outfile st)).

  Open Scope bv_scope.

  (* [comment removed for export] *)
  Definition ai_exit__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (st3 : PS) (ok : bool) (c' : cursor) (p' : pcapT) (msg : list Z) (hd : list cell),
    mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -112) -> AGP m3 ->
    rw_cells usegs m3 (bv_unsigned sp + -112) hd -> cells_size hd = 8%nat -> FRAME m3 ->
    AIREST m3 st3 (ok, c', p', msg) ->
    evt usegs (POSTQ (ok, c', p', msg) st3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' y0 y1 (Z_to_bv 64 (Z.b2z ok)) a1' a2' a3' a4' a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x179c4) fc None m3 (seg_rom usegs)).
  Section Sz1.
  Variables ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 st3 ok c' p' msg hd : ltac2:(SecDiet.SzSec.tyM 'ai_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ai_exit__body : ltac2:(SecDiet.SzSec.bodyP 'ai_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU. pin_using (fun (BU : unit) => tt).
 intros MI3 ST3 AG3 HD3 Hhd FR3 REST.
    clear HPV HNG HBUF HCUR HEB.
    destruct (rw_cells_forget _ _ _ _ HD3) as [hj HD3']. clear HD3. rewrite Hhd in HD3'.
    unfold ai_FRAME in FR3.
    pose proof (rw_cells_uncut _ _ _ _ _ HD3' FR3 ltac:(cbn; lia)) as FR. clear HD3' FR3. cbn [app] in FR.
    do 15 step.
    release_frame FR ST3 (bv_unsigned sp).
    apply evt_done. unfold add_interface_post.
    destruct REST as (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & RM).
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 (Z.b2z ok)), mm, s', i', I', pad', bs' end.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OFr|]. split; [assumption|]. split; [assumption|]. split; [exact AG3|].
    split; [exact E1|]. split; [exact G3|]. split; [exact NG3|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|]. split; [reflexivity|]. exact RM.
  Qed.
  End Sz1.
  Lemma ai_exit : ltac:(let t := eval cbv delta [ai_exit__stmt] in ai_exit__stmt in exact t).
  Proof using BU. intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 st3 ok c' p' msg hd. ltac2:(SecDiet.SzSec.closeP 'ai_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition airest_f_frame__stmt : Prop := forall (m3 m4 : mem) (st' : PS) (c' : cursor) (p' : pcapT) (lo1 hi1 k : Z),
    AIREST_F m3 st' c' p' -> munch [(lo1, hi1); (EB, EB + k)]%Z m3 m4 -> wmono usegs m3 m4 ->
    (usp0 R - 8388608 <= lo1)%Z -> (hi1 <= bv_unsigned sp + -112)%Z -> (0 <= k <= 256)%Z ->
    AIREST_F m4 st' c' p'.
  Section Sz2.
  Variables m3 m4 st' c' p' lo1 hi1 k : ltac2:(SecDiet.SzSec.tyM 'airest_f_frame__stmt "vvvvvvvv" @m3).
  Lemma airest_f_frame__body : ltac2:(SecDiet.SzSec.bodyP 'airest_f_frame__stmt "vvvvvvvv").
  Proof using APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SPM SPW. pin_using (fun (APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SPM SPW : unit) => tt).
    intros (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & IC3 & (ccs' & CC3 & Hccs')) MU WM L1 H1 HK.
    clear HPV HNG HBUF HCUR HEB HIF.
    assert (AGS : agrees_on (fun a => outside [(lo1, hi1); (EB, EB + k)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    exists s', i', I', pad', bs'. split; [exact OFr|]. split; [exact E1|].
    split.
    { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU | exact WM |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [| apply Forall_nil].
      destruct EBiv as [X|X]; [left; cbn [fst snd] in *; lia| right]. unfold iv_in_block in *. apply Exists_app. right.
      apply Exists_exists in X as (b & Hb & Hr). apply Exists_exists. exists b. split; [exact Hb|]. cbn [fst snd] in *. lia. }
    split; [transport NG3 m4 AGS ltac:(prs); exact NG3|].
    split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [transport BUF3 m4 AGS ltac:(prs); exact BUF3|].
    split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|].
    split.
    { destruct i' as [q|]; [| exact IC3]. destruct IC3 as [(junk & IB3) SZ]. split; [| exact SZ]. exists junk.
      pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(apply in_or_app; left; left; reflexivity)) as (Q1 & _ & _ & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q4.
      assert (API : (P + 680 <= I' \/ I' + 40 * ng_ifaces_size s' <= P)%Z).
      { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
      transport IB3 m4 AGS ltac:(prs). exact IB3. }
    exists ccs'. split; [| exact Hccs']. transport CC3 m4 AGS ltac:(prs). exact CC3.
  Qed.
  End Sz2.
  Lemma airest_f_frame : ltac:(let t := eval cbv delta [airest_f_frame__stmt] in airest_f_frame__stmt in exact t).
  Proof using APB B14 BU CEND COFF CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SPM SPW. intros m3 m4 st' c' p' lo1 hi1 k. ltac2:(SecDiet.SzSec.closeP 'airest_f_frame__body "vvvvvvvv"). Qed.

  Lemma airest_f_done : forall (m' : mem) (st' : PS) (c' : cursor) (p' : pcapT) (msg : list Z),
    AIREST_F m' st' c' p' ->
    (exists junk'', rw_cells usegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'']) ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    AIREST m' st' (false, c', p', msg).
  Proof using Type. pin_using tt.
    intros m' st' c' p' msg (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & IC3 & CC3) HE HL HOK.
    exists s', i', I', pad', bs'. split; [exact OFr|]. split; [exact E1|]. split; [exact G3|]. split; [exact NG3|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|]. cbv iota. split; [exact IC3|]. split; [exact CC3|]. split; [exact HE|]. split; [exact HL| exact HOK].
  Qed.

  (* [comment removed for export] *)
  Definition ai_snp__stmt : Prop := forall (ra' t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v : word)
      (m3 : mem) (st3 : PS) (fs : string) (args : list farg) (FMTA : Z) (msg : list Z) (c' : cursor) (p' : pcapT) (hd : list cell),
    mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -112) -> AGP m3 ->
    rw_cells usegs m3 (bv_unsigned sp + -112) hd -> cells_size hd = 8%nat -> FRAME m3 ->
    rw_cells usegs m3 EB [CB 256 ej] ->
    fmt_at m3 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
    (forall (CL : list cblk) D dn, Forall2 (farg_word R CL (bv_unsigned sp + -112) D dn m3) args (firstn (length args) [a3v; a4v; a5'])) ->
    Fmt.snprintf 256 fs args = msg -> items_okb (fmt fs) = true -> Forall arg_ok args ->
    AIREST_F m3 st3 c' p' ->
    evt usegs (POSTQ (false, c', p', msg) st3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 EB) y1 a0' (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3v a4v a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x179b8) fc None m3 (seg_rom usegs)).
  Section Sz4.
  Variables ra' t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 st3 fs args FMTA msg c' p' hd : ltac2:(SecDiet.SzSec.tyM 'ai_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ai_snp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using ALN APB B14 BU CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SNPRINTF SPM SPW TP. pin_using (fun (ALN APB B14 BU CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SNPRINTF SPM SPW TP : unit) => tt).
 intros MI3 ST3 AG3 HD3 Hhd FR3 HEB3 FAT FOK ALEN FW EMSG FIT AOK REST.
    clear HPV HNG HBUF HCUR HEB HIF.
    pose proof REST as REST'. destruct REST' as (s' & i' & I' & pad' & bs' & _ & _ & G3 & _).
    unfold ai_FRAME in FR3.
    hide HD3. hide FR3. hide HEB3.
    do 2 step. unhide HEB3.
    name_sp sp (-112)%Z.
    eapply evt_cut.
    { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R st3 (IBLK i' I' s' ++ C1 ++ C2) FB lo EB 256%Z FMTA fs args ej);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | reflexivity | reflexivity | lia | exact FAT | exact FOK | exact ALEN | rewrite Hsp; apply FW | exact HEB3
        | destruct CRE as [Hb|Hs]; [left; intros a Ha; apply in_block_app; right; exact (Hb a Ha) | right; rewrite Hsp; lia] ]. }
    cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 96704)) with (Z_to_bv 64 96704) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -112 - STDIO_STACK, bv_unsigned sp + -112); (EB, EB + 256)]%Z a) m3 m4)
      by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    unfold STDIO_STACK in AGS, MU4.
    pose proof (airest_f_frame _ _ _ _ _ _ _ _ REST MU4 WM4 ltac:(lia) ltac:(lia) ltac:(lia)) as REST4.
    unhide HD3. unhide FR3.
    transport HD3 m4 AGS ltac:(prs). transport FR3 m4 AGS ltac:(prs).
    hide HD3. hide FR3. hide HEB4.
    step.
    unhide HD3. unhide FR3. unhide HEB4.
    eapply (ai_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 st3 false c' p' msg hd);
      [exact MI4 | exact ST4 | | exact HD3 | exact Hhd | exact FR3 |].
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] (_ & _ & Hn & _)]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
    apply (airest_f_done _ _ _ _ _ REST4).
    - exists junk4. pose proof (snprintf_length 256 fs args) as LS. change (Z.to_nat (256 - 1)) with 255%nat in LS. rewrite EMSG in LS, HEB4.
      change (Z.to_nat 256) with 256%nat in HEB4. replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB4 by lia. exact HEB4.
    - pose proof (snprintf_length 256 fs args) as LS. rewrite EMSG in LS. change (Z.to_nat (256 - 1)) with 255%nat in LS. lia.
    - rewrite <- EMSG. apply snprintf_ok; [exact FIT| exact AOK].
  Qed.
  End Sz4.
  Lemma ai_snp : ltac:(let t := eval cbv delta [ai_snp__stmt] in ai_snp__stmt in exact t).
  Proof using ALN APB B14 BU CEND CLB COFF CRE CREM CUR1 CUR2 CUR8 EBX EBiv HFL HinP IDB0 LENB LO P14 RSP SFL SNPRINTF SPM SPW TP. intros ra' t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 st3 fs args FMTA msg c' p' hd. ltac2:(SecDiet.SzSec.closeP 'ai_snp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_mcp__stmt : Prop := forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (st3 : PS) (SRC n : Z) (str : string) (msg : list Z) (c' : cursor) (p' : pcapT) (hd : list cell),
    mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -112) -> AGP m3 ->
    rw_cells usegs m3 (bv_unsigned sp + -112) hd -> cells_size hd = 8%nat -> FRAME m3 ->
    rw_cells usegs m3 EB [CB 256 ej] ->
    fmt_at m3 SRC str -> (Z.of_nat (String.length str) + 1 = n)%Z -> (n <= 256)%Z ->
    map b8 msg = map (fun ch => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii ch))) (String.list_ascii_of_string str) ->
    Forall (fun z => 0 < z < 256)%Z msg ->
    AIREST_F m3 st3 c' p' ->
    evt usegs (POSTQ (false, c', p', msg) st3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 EB) y1 a0' (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x17994) fc None m3 (seg_rom usegs)).
  Section Sz5.
  Variables ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 st3 SRC n str msg c' p' hd : ltac2:(SecDiet.SzSec.tyM 'ai_mcp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ai_mcp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_mcp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using APB B14 BU CBT CEND COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HinP IDB0 LENB LO P14 P5 RSP SFL SPM SPW UTS WMB. pin_using (fun (APB B14 BU CBT CEND COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HinP IDB0 LENB LO P14 P5 RSP SFL SPM SPW UTS WMB : unit) => tt).
 intros MI3 ST3 AG3 HD3 Hhd FR3 HEB3 [SRCB SRCR] LN NB EMSG MOK REST.
    clear HPV HNG HBUF HCUR HEB HIF.
    unfold ai_FRAME in FR3.
    assert (LM : length msg = String.length str).
    { apply (f_equal (@length _)) in EMSG. rewrite !length_map, length_list_ascii in EMSG. exact EMSG. }
    pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat n; (256 - Z.to_nat n)%nat] HEB3 ltac:(cbn; lia)) as HE'. clear HEB3. cbn [mk_CB_cells app] in HE'.
    destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
    lazymatch type of HE2 with rw_cells _ _ ?A _ => replace A with (EB + n)%Z in HE2 by lia end.
    destruct P14 as [P1 P4].
    hide HD3. hide FR3. hide HE2.
    do 2 step.
    eapply evt_cut.
    { eapply (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB SRC n);
        [reflexivity | reflexivity | reflexivity | exact SRCB | rewrite length_app, length_map, length_list_ascii; cbn [length]; lia | lia | exact HE1
        | pose proof P5 as P5'; unfold out_of_image in P5'; destruct EBX as [X| ->]; lia | lia | lia | exact MI3]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m4 & -> & MU4 & WM4 & MI4 & HE1' & _). clear HE1.
    replace (ret_pc (Z_to_bv 64 96668)) with (Z_to_bv 64 96668) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (AGS : agrees_on (fun a => outside [(EB, EB + n)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (MU4' : munch [(bv_unsigned sp + -112, bv_unsigned sp + -112); (EB, EB + n)]%Z m3 m4).
    { intros a Ho. apply MU4. cbn [outside fst snd] in *. tauto. }
    pose proof (airest_f_frame _ _ _ _ _ _ _ _ REST MU4' WM4 ltac:(lia) ltac:(lia) ltac:(lia)) as REST4.
    assert (ST4 : stk usegs m4 lo (bv_unsigned sp + -112)).
    { eapply stk_transport_disjoint; [exact ST3 | exact MU4 | exact WM4 | cbn [disjoint_from]; destruct EBX as [X| ->]; unfold rc_lo in *; lia]. }
    unhide HD3. unhide FR3. unhide HE2.
    transport HD3 m4 AGS ltac:(prs). transport FR3 m4 AGS ltac:(prs). transport HE2 m4 AGS ltac:(prs).
    hide HD3. hide FR3. hide HE2. hide HE1'.
    do 2 step.
    unhide HD3. unhide FR3. unhide HE2. unhide HE1'.
    eapply (ai_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 st3 false c' p' msg hd);
      [exact MI4 | exact ST4 | | exact HD3 | exact Hhd | exact FR3 |].
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a (_ & _ & _ & Hn & _); cbn [outside]. split; [lia| exact Logic.I]. }
    apply (airest_f_done _ _ _ _ _ REST4).
    - lazymatch type of HE2 with rw_cells _ _ _ [CB _ ?j] => exists j end.
      join_cells HE1' HE2.
      eapply rw_cells_recell; [exact HE1' | pose proof (proj1 (proj1 HE1')) as WF; cbn in WF |- *; rewrite ?length_app, ?length_map, ?length_list_ascii in *; cbn [length] in *; repeat split; try lia; tauto |].
      cbn [cells_bytes cbytes app]. rewrite EMSG, <- app_assoc. reflexivity.
    - rewrite LM. lia.
    - exact MOK.
  Qed.
  End Sz5.
  Lemma ai_mcp : ltac:(let t := eval cbv delta [ai_mcp__stmt] in ai_mcp__stmt in exact t).
  Proof using APB B14 BU CBT CEND COFF CRE CREM CUR1 CUR2 CUR8 EB64 EBX EBiv G HFL HinP IDB0 LENB LO P14 P5 RSP SFL SPM SPW UTS WMB. intros ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 st3 SRC n str msg c' p' hd. ltac2:(SecDiet.SzSec.closeP 'ai_mcp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AIA.

End WithCeil.
End TwB.
End F_sfpcapng_aiA.

(* [comment removed for export] *)
Module F_sfpcapng_aiB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_memmove OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiA.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma m_divu : forall a b : word, bv_unsigned b <> 0 -> mul_div M_DIVU a b = Z_to_bv 64 (bv_unsigned a / bv_unsigned b).
Proof using Type. pin_using tt.
  intros a b Hb. unfold mul_div. rewrite (proj2 (Z.eqb_neq _ _) Hb).
  apply bv_eq. rewrite bv_divu_unsigned, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 b).
  unfold bv_modulus in *. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Lemma mulhu40 : forall k, 0 <= k < 2^32 -> Z.shiftr (k * 4294967296 * 171798691840) 64 = k * 40.
Proof using Type. pin_using tt. intros k Hk. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. nia. Qed.

Lemma ifs_cells_app : forall (l1 l2 : list ng_if) (j1 j2 : list if_junk),
  length j1 = length l1 -> ifs_cells l1 j1 ++ ifs_cells l2 j2 = ifs_cells (l1 ++ l2) (j1 ++ j2).
Proof using Type. pin_using tt.
  induction l1 as [|i l1 IH]; intros l2 [|j j1] j2 HL; cbn [length] in HL; try discriminate HL; [reflexivity|].
  cbn [ifs_cells app]. rewrite <- app_assoc. f_equal. apply IH. lia.
Qed.

Section AIB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (st : PS) (C1 C2 FB : list cblk) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIo K R st (C1 ++ IBLK i I s ++ C2) FB m.
  Hypothesis ST : stk ssegs m lo (bv_unsigned sp).
  Hypothesis LO : usp0 R - 8388608 <= lo.
  Hypothesis BU : lo + (65536 + 112) <= bv_unsigned sp.
  Hypothesis SPM : bv_unsigned sp <= rc_spmain R.
  Hypothesis MI : mem_inv ssegs m.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : bv_unsigned sp mod 16 = 0.
  Hypothesis RSP : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPW : 0x7fff80000000 <= usp0 R.
  Hypothesis SP47 : usp0 R <= 2^47.
  Hypothesis HS : pc_priv p = PrivNg s i.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis B14 : 0 < B /\ B + pc_bufalloc p <= CEILZ.
  Hypothesis APB : P + 680 <= B \/ B + pc_bufalloc p <= P.
  (* [comment removed for export] *)
  Hypothesis P5 : out_of_image P 680.
  Hypothesis HPV : rw_cells ssegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].
  Hypothesis HNG : rw_cells ssegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad).
  Hypothesis HIF : ifaces_ok p I m.
  Hypothesis UTS : 0 < ng_user_tsresol s < 2^64.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis WMB : 0 <= ng_max_blocksize s < 2^32.
  Hypothesis HBUF : rw_cells ssegs m B [CB (Z.to_nat (pc_bufalloc p)) bs].
  Hypothesis PFX : firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p).
  Hypothesis LENB : Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32.
  Hypothesis GRD : Forall (fun z => 0 <= z < 256) (pc_bufdata p).
  Hypothesis HCUR : rw_cells ssegs m CUR (cursor_cells B c cpad).
  Hypothesis CUR1 : bv_unsigned sp <= CUR.
  Hypothesis CUR2 : CUR + 24 <= rc_spmain R.
  Hypothesis CUR8 : CUR mod 8 = 0.
  Hypothesis IDB0 : 0 <= idb_off.
  Hypothesis COFF : cur_off c = idb_off + 8.
  Hypothesis CREM : 0 <= cur_remaining c.
  Hypothesis CEND : cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)).
  Hypothesis CBT : 0 <= cur_block_type c < 2^32.
  Hypothesis HEB : rw_cells ssegs m EB [CB 256 ej].
  Hypothesis EBX : (bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ EB = P + 216.
  Hypothesis EB64 : 0 < EB /\ EB + 256 < 2^64.
  (* [comment removed for export] *)
  Hypothesis CLB : forall a, in_block (C1 ++ C2) a -> a < CEILZ.
  Hypothesis INPc : forall a, P <= a < P + 680 -> in_block (C1 ++ C2) a.
  Hypothesis INBc : forall a, B <= a < B + pc_bufalloc p -> in_block (C1 ++ C2) a.
  Hypothesis CRE : client_range R (C1 ++ C2) (bv_unsigned sp) EB 256.
  Hypothesis EBiv : client_iv R (C1 ++ C2) (EB, EB + 256).

  #[local] Notation POSTQ := (add_interface_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Notation AGP := (ai_AGP sp C1 C2 P B CUR EB p m).
  #[local] Notation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  #[local] Notation AIREST := (ai_REST K R C1 C2 FB P B CUR EB p s c ej (ps_outfile st)).
  #[local] Notation AIREST_F := (ai_REST_F K R C1 C2 FB P B CUR p s (ps_outfile st)).

  (* [comment removed for export] *)
  Definition ai_scale (opts : idbopts) : ng_scale_t * option Z :=
    let tsresol := io_tsresol opts in
    let user := ng_user_tsresol s in
    if tsresol =? user then (NG_PASS_THROUGH, None)
    else if user <? tsresol then (if io_is_binary opts then (SCALE_DOWN_BIN, None) else (SCALE_DOWN_DEC, Some (tsresol / user)))
    else (if io_is_binary opts then (SCALE_UP_BIN, None) else (SCALE_UP_DEC, Some (user / tsresol))).
  Definition ai_snap : Z := get_le32 (pc_bufdata p) (idb_off + 4).
  Definition ai_slot0 : ng_if := mkIf ai_snap 0 NG_PASS_THROUGH 0 0.
  Definition ai_slot (opts : idbopts) : ng_if :=
    let '(sct, scf) := ai_scale opts in
    mkIf ai_snap (io_tsresol opts) sct (match scf with Some f => f | None => 0 end) (io_tsoffset opts).
  (* [comment removed for export] *)
  Definition ai_result (sg : pcap_ng_sf) (i1 : option hptr) (res : list Z * ((list Z) + (idbopts * cursor))) : bool * cursor * pcapT * list Z :=
    let p2 := set_ng (mkNg (ng_user_tsresol sg) (ng_max_blocksize sg) (ng_ifcount sg) (ng_ifaces_size sg) (ai_slot0 :: ng_ifaces sg)) i1 (set_ng sg i1 p) in
    let '(buf, r) := res in
    let p3 := set_bufdata buf p2 in
    match r with
    | inl m => (false, c, p3, m)
    | inr (opts, c') =>
        (true, c', set_ng (mkNg (ng_user_tsresol sg) (ng_max_blocksize sg) (ng_ifcount sg) (ng_ifaces_size sg) (ai_slot opts :: ng_ifaces sg)) i1 p3, [])
    end.

  (* [comment removed for export] *)
  Definition ai_tail__stmt : Prop := forall (ra' t0' t1' t2' a2' a3' a6' a7' t3' t4' t5' y3 y4 y5 y6 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 bs3 cpad3 : list byte)
      (opts : idbopts) (c' : cursor) (buf' : list Z) (hd : list cell),
    ng_user_tsresol sg = ng_user_tsresol s -> ng_max_blocksize sg = ng_max_blocksize s -> ng_ifaces sg = ng_ifaces s ->
    ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1 -> ng_ifcount sg <= ng_ifaces_size sg -> 1 <= ng_ifaces_size sg < 2^26 ->
    length js = length (ng_ifaces s) ->
    SA = I' + 40 * (ng_ifcount sg - 1) ->
    (0 <= ai_snap < 2^32)%Z -> (0 < io_tsresol opts < 2^64)%Z ->
    mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -112) -> AGP m3 ->
    rw_cells ssegs m3 (bv_unsigned sp + -112) hd -> cells_size hd = 8%nat -> FRAME m3 ->
    rw_cells ssegs m3 (P + 648) (ng_cells sg I' pad1) ->
    rw_cells ssegs m3 I' (ifs_cells (rev (ng_ifaces s)) js) ->
    rw_cells ssegs m3 SA [C4 (Z_to_bv 64 ai_snap); CB 36 sj] ->
    rw_cells ssegs m3 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] ->
    GIo K R stG ((q1, I', 40 * ng_ifaces_size sg) :: C1 ++ C2) FB m3 ->
    rw_cells ssegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs3] -> firstn (length buf') bs3 = map b8 buf' -> length buf' = length (pc_bufdata p) ->
    Forall (fun z => 0 <= z < 256)%Z buf' ->
    rw_cells ssegs m3 CUR (cursor_cells B c' cpad3) ->
    (0 <= cur_remaining c')%Z -> (cur_off c <= cur_off c')%Z -> (cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c)%Z -> cur_block_type c' = cur_block_type c ->
    rw_cells ssegs m3 EB [CB 256 ej] -> ps_outfile stG = ps_outfile st ->
    evt ssegs (POSTQ (ai_result sg (Some q1) (buf', inr (opts, c'))) stG)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 P)
               (Z_to_bv 64 I') (Z_to_bv 64 ((ng_ifcount sg - 1) * 4294967296)) a2' a3' (Z_to_bv 64 (io_tsresol opts)) (Z_to_bv 64 (Z.b2z (io_is_binary opts))) a6' a7'
               (Z_to_bv 64 (P + 648)) y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' (Z_to_bv 64 (io_tsoffset opts)))
          F (Z_to_bv 64 0x17240) fc None m3 (seg_rom ssegs)).
  Section Sz4.
  Variables ra' t0' t1' t2' a2' a3' a6' a7' t3' t4' t5' y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 stG sg q1 I' SA js pad1 sj tail3 bs3 cpad3 opts c' buf' hd : ltac2:(SecDiet.SzSec.tyM 'ai_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ai_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ai_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HinB HinP IDB0 IFW LENB LO P14 RSP SFL SPW UTS. pin_using (fun (APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HinB HinP IDB0 IFW LENB LO P14 RSP SFL SPW UTS : unit) => tt).
    intros U1 U2 U5 IC1 IC2 SZ LJS HSA SNR TSR MI3 ST3 AG3 HD3 Hhd FR3 NG3 AR1 SL3 AR2 G3 BUF3 PFX3 LB3 GR3 CC3 CR1 CR2 CR3 CR4 HEB3 OFG.
    clear HPV HNG HBUF HCUR HEB HIF.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
    assert (API : (P + 680 <= I' \/ I' + 40 * ng_ifaces_size sg <= P)%Z).
    { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
    unfold ai_FRAME in FR3. unfold ng_cells in NG3.
    hide HD3. hide FR3. hide AR1. hide AR2. hide BUF3. hide CC3. hide HEB3. hide SL3.
    do 3 step.
    replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 ((ng_ifcount sg - 1) * 4294967296))) 32)) with (Z_to_bv 64 (ng_ifcount sg - 1))
      by (f_equal; rewrite unsigned_lit by nia; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; nia).
    step. rewrite (unsigned_lit (ng_ifcount sg - 1)) by lia.
    step. replace (I' + (ng_ifcount sg - 1) * 40)%Z with SA by lia.
    assert (APIB : (B + pc_bufalloc p <= I' \/ I' + 40 * ng_ifaces_size sg <= B)%Z).
    { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinB) as AP. cbn [cb_addr cb_size fst snd] in AP. lia. }
    assert (LSJ : length sj = 36%nat) by (destruct SL3 as [[WF _] _]; cbn in WF; lia).
    (* [comment removed for export] *)
    assert (FIN : forall (m5 : mem) (jn : if_junk),
      munch [(SA, SA + 40)]%Z m3 m5 -> wmono ssegs m3 m5 ->
      rw_cells ssegs m5 SA (if_cells (ai_slot opts) jn) ->
      AIREST m5 stG (ai_result sg (Some q1) (buf', inr (opts, c')))).
    { intros m5 jn MU WM SL5.
      assert (AGS : agrees_on (fun a => outside [(SA, SA + 40)]%Z a) m3 m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide AR1. unhide AR2. unhide BUF3. unhide CC3. unhide HEB3.
      pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
      transport NG3 m5 AGS ltac:(prs). transport AR2 m5 AGS ltac:(prs). transport BUF3 m5 AGS ltac:(prs).
      transport AR1 m5 AGS ltac:(intros a Ha; rewrite ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [outside]; split; [lia| exact Logic.I]).
      transport CC3 m5 AGS ltac:(prs). transport HEB3 m5 AGS ltac:(prs).
      assert (G5 : GIo K R stG ((q1, I', 40 * ng_ifaces_size sg) :: C1 ++ C2) FB m5).
      { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      unfold ai_result. exists (mkNg (ng_user_tsresol sg) (ng_max_blocksize sg) (ng_ifcount sg) (ng_ifaces_size sg) (ai_slot opts :: ng_ifaces sg)), (Some q1), I', pad1, bs3.
      split; [exact OFG|]. split; [reflexivity|]. split; [exact G5|]. split; [exact NG3|]. split; [cbn; exact U1|]. split; [cbn; exact U2|]. split; [cbn; lia|]. split; [cbn; lia|].
      split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LB3|]. split; [exact GR3|]. cbv iota.
      split.
      { unfold ifaces_ok. cbn [pc_priv set_ng set_priv set_bufdata ng_ifaces ng_ifaces_size ng_ifcount].
        exists (js ++ [jn]), tail3. split; [rewrite !length_app, LJS, U5; cbn [length]; lia|].
        split; [| rewrite U5; cbn [length]; split; [lia|]; split; [lia|]; split; [lia|];
                  constructor; [| exact IFW];
                  unfold if_wf, ai_slot, ai_scale; cbn [if_tsresol if_scale_type if_scale_factor];
                  destruct (io_tsresol opts =? ng_user_tsresol s) eqn:QX1; [cbn; split; [exact TSR| discriminate]|];
                  destruct (ng_user_tsresol s <? io_tsresol opts) eqn:QX2; destruct (io_is_binary opts); cbn [is_dec if_scale_factor];
                  (split; [exact TSR|]); intros Hd; try discriminate Hd;
                  [ apply Z.ltb_lt in QX2; split; [apply Z.div_str_pos; lia| apply Z.div_lt_upper_bound; lia]
                  | apply Z.ltb_ge in QX2; apply Z.eqb_neq in QX1; split; [apply Z.div_str_pos; lia| apply Z.div_lt_upper_bound; lia] ] ].
        cbn [rev]. rewrite <- (ifs_cells_app (rev (ng_ifaces sg)) [ai_slot opts] js [jn]) by (rewrite length_rev, LJS, U5; reflexivity).
        cbn [ifs_cells]. rewrite app_nil_r, U5.
        pose proof (rw_cells_uncut _ _ _ _ _ AR1 SL5 ltac:(rewrite ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as J1.
        pose proof (rw_cells_uncut _ _ _ _ _ J1 AR2 ltac:(rewrite cells_size_app, ifs_cells_size, if_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as J2.
        exact J2. }
      split; [exists cpad3; exact CC3|]. split; [exact CR1|]. split; [exact CR2|]. split; [exact CR3|]. split; [exact CR4|]. split; [exact HEB3| reflexivity]. }
    pose proof (munch_refl [(SA, SA + 40)]%Z m3) as MU5. pose proof (wmono_refl ssegs m3) as WM5.
    unhide SL3. step. step.
    step.
    (* [comment removed for export] *)
    assert (LEAF : forall (ra'' t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word) (m5 : mem) (jn : if_junk),
      mem_inv ssegs m5 -> stk ssegs m5 lo (bv_unsigned sp + -112) ->
      munch [(SA, SA + 40)]%Z m3 m5 -> wmono ssegs m3 m5 ->
      rw_cells ssegs m5 SA (if_cells (ai_slot opts) jn) ->
      evt ssegs (POSTQ (ai_result sg (Some q1) (buf', inr (opts, c'))) stG)
        (MS (mkR ra'' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0'' t1'' t2'' (Z_to_bv 64 EB) (Z_to_bv 64 P) (Z_to_bv 64 1) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                 (Z_to_bv 64 (P + 648)) y3 y4 y5 y6 y7 y8 y9 y10 y11 t3'' t4'' t5'' t6'') F (Z_to_bv 64 0x173b8) fc None m5 (seg_rom ssegs))).
    { intros until jn. intros MI5 ST5 MU WM SL5.
      assert (AGS : agrees_on (fun a => outside [(SA, SA + 40)]%Z a) m3 m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide HD3. unhide FR3.
      transport HD3 m5 AGS ltac:(prs). transport FR3 m5 AGS ltac:(prs).
      unfold ai_result.
      eapply ai_exit; try eassumption.
      - eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] _]; cbn [outside]; (split; [| exact Logic.I]); [lia|].
        pose proof (CLB a Ha). destruct (proj1 (in_block_In _ _) Ha) as (b' & Hin & Hr). pose proof (head_apart K _ _ _ _ _ _ _ G3 Hin) as AP. cbn [cb_addr cb_size fst snd] in AP. lia.
      - pose proof (FIN m5 jn MU WM SL5) as X. unfold ai_result in X. exact X. }
    assert (U0 : (0 < ng_user_tsresol sg < 2^64)%Z) by (rewrite U1; exact UTS).
    destruct (Z.eq_dec (io_tsresol opts) (ng_user_tsresol sg)) as [TE|TE].
    - (* [comment removed for export] *)
      rewrite (eqb_lits_eq _ _ TE). cbn [negb]. cbv iota.
      do 3 step.
      eapply LEAF; [assumption | assumption | exact MU5 | exact WM5 |].
      lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 12 ?b; _] =>
        eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a (firstn 4 b) (bv_extract 0 64 (le_bytes_to_word (skipn 4 b))))));
        [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
        unfold if_cells, ai_slot, ai_scale; rewrite (proj2 (Z.eqb_eq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)); cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
        pose proof (proj1 (proj1 SL3)) as WF; cbn in WF; rewrite (le8_ld (skipn 4 b)) by (rewrite length_skipn; lia);
        rewrite <- (firstn_skipn 4 b) at 3; rewrite <- ?app_assoc; reflexivity
      end.
    - rewrite (eqb_lits_false (io_tsresol opts) (ng_user_tsresol sg) ltac:(lia) ltac:(lia) TE). cbn [negb]. cbv iota.
      step.
      (* [comment removed for export] *)
      assert (WFb : forall (b : list byte) n, length b = n -> True) by (intros; exact Logic.I).
      destruct (Z.lt_ge_cases (ng_user_tsresol sg) (io_tsresol opts)) as [LT|GE].
      + (* [comment removed for export] *)
        replace (bv_ltu (Z_to_bv 64 (ng_user_tsresol sg)) (Z_to_bv 64 (io_tsresol opts))) with true
          by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
        destruct (io_is_binary opts) eqn:BIN; cbn [Z.b2z].
        * (* [comment removed for export] *)
          step. if_false. step. step. rewrite (unsigned_lit (ng_ifcount sg - 1)) by lia. step. step. step. replace (I' + (ng_ifcount sg - 1) * 40)%Z with SA by lia.
          step. step. step.
          eapply LEAF; [assumption | assumption | exact MU5 | exact WM5 |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 12 ?b; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a (firstn 4 b) (bv_extract 0 64 (le_bytes_to_word (skipn 4 b))))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, ai_slot, ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_lt (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            pose proof (proj1 (proj1 SL3)) as WF; cbn in WF; rewrite (le8_ld (skipn 4 b)) by (rewrite ?length_skipn, ?length_firstn in *; lia);
            rewrite <- (firstn_skipn 4 b) at 3; rewrite <- ?app_assoc; reflexivity
          end.
        * (* [comment removed for export] *)
          step. if_true. step.
          rewrite (m_divu (Z_to_bv 64 (io_tsresol opts)) (Z_to_bv 64 (ng_user_tsresol sg))) by (rewrite unsigned_lit by lia; lia). rewrite !(unsigned_lit (io_tsresol opts)), !(unsigned_lit (ng_user_tsresol sg)) by lia.
          step. step. rewrite (unsigned_lit (ng_ifcount sg - 1)) by lia. step. step. replace (I' + (ng_ifcount sg - 1) * 40)%Z with SA by lia.
          step. step. step. step.
          eapply LEAF; [assumption | assumption | exact MU5 | exact WM5 |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 4 ?b; _; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a b (Z_to_bv 64 0))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, ai_slot, ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_lt (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            rewrite <- U1; rewrite <- ?app_assoc; reflexivity
          end.
      + (* [comment removed for export] *)
        replace (bv_ltu (Z_to_bv 64 (ng_user_tsresol sg)) (Z_to_bv 64 (io_tsresol opts))) with false
          by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia). cbn [negb]. cbv iota.
        destruct (io_is_binary opts) eqn:BIN; cbn [Z.b2z].
        * (* [comment removed for export] *)
          step. if_false. step. step. rewrite (unsigned_lit (ng_ifcount sg - 1)) by lia. step. step. replace (I' + (ng_ifcount sg - 1) * 40)%Z with SA by lia.
          step. step. step.
          eapply LEAF; [assumption | assumption | exact MU5 | exact WM5 |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 12 ?b; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a (firstn 4 b) (bv_extract 0 64 (le_bytes_to_word (skipn 4 b))))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, ai_slot, ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_ge (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            pose proof (proj1 (proj1 SL3)) as WF; cbn in WF; rewrite (le8_ld (skipn 4 b)) by (rewrite ?length_skipn, ?length_firstn in *; lia);
            rewrite <- (firstn_skipn 4 b) at 3; rewrite <- ?app_assoc; reflexivity
          end.
        * (* [comment removed for export] *)
          step. if_true. step.
          rewrite (m_divu (Z_to_bv 64 (ng_user_tsresol sg)) (Z_to_bv 64 (io_tsresol opts))) by (rewrite unsigned_lit by lia; lia). rewrite !(unsigned_lit (io_tsresol opts)), !(unsigned_lit (ng_user_tsresol sg)) by lia.
          step. step. rewrite (unsigned_lit (ng_ifcount sg - 1)) by lia. step. replace (I' + (ng_ifcount sg - 1) * 40)%Z with SA by lia.
          step. step. step. step.
          eapply LEAF; [assumption | assumption | exact MU5 | exact WM5 |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 4 ?b; _; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a b (Z_to_bv 64 0))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, ai_slot, ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_ge (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            rewrite <- U1; rewrite <- ?app_assoc; reflexivity
          end.
  Qed.
  End Sz4.
  Lemma ai_tail : ltac:(let t := eval cbv delta [ai_tail__stmt] in ai_tail__stmt in exact t).
  Proof using APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HinB HinP IDB0 IFW LENB LO P14 RSP SFL SPW UTS. intros ra' t0' t1' t2' a2' a3' a6' a7' t3' t4' t5' y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 stG sg q1 I' SA js pad1 sj tail3 bs3 cpad3 opts c' buf' hd. ltac2:(SecDiet.SzSec.closeP 'ai_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AIB.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_memmove.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiA.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma m_divu : forall a b : word, bv_unsigned b <> 0 -> mul_div M_DIVU a b = Z_to_bv 64 (bv_unsigned a / bv_unsigned b).
Proof using Type. pin_using tt.
  intros a b Hb. unfold mul_div. rewrite (proj2 (Z.eqb_neq _ _) Hb).
  apply bv_eq. rewrite bv_divu_unsigned, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 b).
  unfold bv_modulus in *. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Lemma mulhu40 : forall k, 0 <= k < 2^32 -> Z.shiftr (k * 4294967296 * 171798691840) 64 = k * 40.
Proof using Type. pin_using tt. intros k Hk. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. nia. Qed.

Lemma ifs_cells_app : forall (l1 l2 : list ng_if) (j1 j2 : list if_junk),
  length j1 = length l1 -> ifs_cells l1 j1 ++ ifs_cells l2 j2 = ifs_cells (l1 ++ l2) (j1 ++ j2).
Proof using Type. pin_using tt.
  induction l1 as [|i l1 IH]; intros l2 [|j j1] j2 HL; cbn [length] in HL; try discriminate HL; [reflexivity|].
  cbn [ifs_cells app]. rewrite <- app_assoc. f_equal. apply IH. lia.
Qed.

Section AIB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (st : PS) (C1 C2 FB : list cblk) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIo K R st (C1 ++ IBLK i I s ++ C2) FB m.
  Hypothesis ST : stk usegs m lo (bv_unsigned sp).
  Hypothesis LO : usp0 R - 8388608 <= lo.
  Hypothesis BU : lo + (65536 + 112) <= bv_unsigned sp.
  Hypothesis SPM : bv_unsigned sp <= rc_spmain R.
  Hypothesis MI : mem_inv usegs m.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : bv_unsigned sp mod 16 = 0.
  Hypothesis RSP : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPW : 0x7fff80000000 <= usp0 R.
  Hypothesis SP47 : usp0 R <= 2^47.
  Hypothesis HS : pc_priv p = PrivNg s i.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis B14 : 0 < B /\ B + pc_bufalloc p <= CEILZ.
  Hypothesis APB : P + 680 <= B \/ B + pc_bufalloc p <= P.
  (* [comment removed for export] *)
  Hypothesis P5 : out_of_image P 680.
  Hypothesis HPV : rw_cells usegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].
  Hypothesis HNG : rw_cells usegs m (P + PCAP_PRIV_OFF) (ng_cells s I pad).
  Hypothesis HIF : ifaces_ok p I m.
  Hypothesis UTS : 0 < ng_user_tsresol s < 2^64.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis WMB : 0 <= ng_max_blocksize s < 2^32.
  Hypothesis HBUF : rw_cells usegs m B [CB (Z.to_nat (pc_bufalloc p)) bs].
  Hypothesis PFX : firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p).
  Hypothesis LENB : Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32.
  Hypothesis GRD : Forall (fun z => 0 <= z < 256) (pc_bufdata p).
  Hypothesis HCUR : rw_cells usegs m CUR (cursor_cells B c cpad).
  Hypothesis CUR1 : bv_unsigned sp <= CUR.
  Hypothesis CUR2 : CUR + 24 <= rc_spmain R.
  Hypothesis CUR8 : CUR mod 8 = 0.
  Hypothesis IDB0 : 0 <= idb_off.
  Hypothesis COFF : cur_off c = idb_off + 8.
  Hypothesis CREM : 0 <= cur_remaining c.
  Hypothesis CEND : cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)).
  Hypothesis CBT : 0 <= cur_block_type c < 2^32.
  Hypothesis HEB : rw_cells usegs m EB [CB 256 ej].
  Hypothesis EBX : (bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ EB = P + 216.
  Hypothesis EB64 : 0 < EB /\ EB + 256 < 2^64.
  (* [comment removed for export] *)
  Hypothesis CLB : forall a, in_block (C1 ++ C2) a -> a < CEILZ.
  Hypothesis INPc : forall a, P <= a < P + 680 -> in_block (C1 ++ C2) a.
  Hypothesis INBc : forall a, B <= a < B + pc_bufalloc p -> in_block (C1 ++ C2) a.
  Hypothesis CRE : client_range R (C1 ++ C2) (bv_unsigned sp) EB 256.
  Hypothesis EBiv : client_iv R (C1 ++ C2) (EB, EB + 256).

  #[local] Notation POSTQ := (add_interface_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Notation AGP := (ai_AGP sp C1 C2 P B CUR EB p m).
  #[local] Notation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  #[local] Notation AIREST := (ai_REST K R C1 C2 FB P B CUR EB p s c ej (ps_outfile st)).
  #[local] Notation AIREST_F := (ai_REST_F K R C1 C2 FB P B CUR p s (ps_outfile st)).

  (* [comment removed for export] *)
  Definition ai_scale (opts : idbopts) : ng_scale_t * option Z :=
    let tsresol := io_tsresol opts in
    let user := ng_user_tsresol s in
    if tsresol =? user then (NG_PASS_THROUGH, None)
    else if user <? tsresol then (if io_is_binary opts then (SCALE_DOWN_BIN, None) else (SCALE_DOWN_DEC, Some (tsresol / user)))
    else (if io_is_binary opts then (SCALE_UP_BIN, None) else (SCALE_UP_DEC, Some (user / tsresol))).
  Definition ai_snap : Z := get_le32 (pc_bufdata p) (idb_off + 4).
  Definition ai_slot0 : ng_if := mkIf ai_snap 0 NG_PASS_THROUGH 0 0.
  Definition ai_slot (opts : idbopts) : ng_if :=
    let '(sct, scf) := ai_scale opts in
    mkIf ai_snap (io_tsresol opts) sct (match scf with Some f => f | None => 0 end) (io_tsoffset opts).
  (* [comment removed for export] *)
  Definition ai_result (sg : pcap_ng_sf) (i1 : option hptr) (res : list Z * ((list Z) + (idbopts * cursor))) : bool * cursor * pcapT * list Z :=
    let p2 := set_ng (mkNg (ng_user_tsresol sg) (ng_max_blocksize sg) (ng_ifcount sg) (ng_ifaces_size sg) (ai_slot0 :: ng_ifaces sg)) i1 (set_ng sg i1 p) in
    let '(buf, r) := res in
    let p3 := set_bufdata buf p2 in
    match r with
    | inl m => (false, c, p3, m)
    | inr (opts, c') =>
        (true, c', set_ng (mkNg (ng_user_tsresol sg) (ng_max_blocksize sg) (ng_ifcount sg) (ng_ifaces_size sg) (ai_slot opts :: ng_ifaces sg)) i1 p3, [])
    end.

  (* [comment removed for export] *)
  Definition ai_tail__stmt : Prop := forall (ra' t0' t2' a0' a2' a3' a5' a6' a7' t3' t4' t5' t6' y0 y2 y3 y5 y6 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 bs3 cpad3 : list byte)
      (opts : idbopts) (c' : cursor) (buf' : list Z) (hd : list cell),
    ng_user_tsresol sg = ng_user_tsresol s -> ng_max_blocksize sg = ng_max_blocksize s -> ng_ifaces sg = ng_ifaces s ->
    ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1 -> ng_ifcount sg <= ng_ifaces_size sg -> 1 <= ng_ifaces_size sg < 2^26 ->
    length js = length (ng_ifaces s) ->
    SA = I' + 40 * (ng_ifcount sg - 1) ->
    (0 <= ai_snap < 2^32)%Z -> (0 < io_tsresol opts < 2^64)%Z ->
    mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -112) -> AGP m3 ->
    rw_cells usegs m3 (bv_unsigned sp + -112) hd -> cells_size hd = 8%nat -> FRAME m3 ->
    rw_cells usegs m3 (P + 648) (ng_cells sg I' pad1) ->
    rw_cells usegs m3 I' (ifs_cells (rev (ng_ifaces s)) js) ->
    rw_cells usegs m3 SA [C4 (Z_to_bv 64 ai_snap); CB 36 sj] ->
    rw_cells usegs m3 (SA + 40) [CB (Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))) tail3] ->
    GIo K R stG ((q1, I', 40 * ng_ifaces_size sg) :: C1 ++ C2) FB m3 ->
    rw_cells usegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs3] -> firstn (length buf') bs3 = map b8 buf' -> length buf' = length (pc_bufdata p) ->
    Forall (fun z => 0 <= z < 256)%Z buf' ->
    rw_cells usegs m3 CUR (cursor_cells B c' cpad3) ->
    (0 <= cur_remaining c')%Z -> (cur_off c <= cur_off c')%Z -> (cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c)%Z -> cur_block_type c' = cur_block_type c ->
    rw_cells usegs m3 EB [CB 256 ej] -> ps_outfile stG = ps_outfile st ->
    evt usegs (POSTQ (ai_result sg (Some q1) (buf', inr (opts, c'))) stG)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' (Z_to_bv 64 (Z.b2z (io_is_binary opts))) t2' y0 (Z_to_bv 64 (P + 648))
               a0' (Z_to_bv 64 (io_tsresol opts)) a2' a3' (Z_to_bv 64 SA) a5' a6' a7'
               y2 y3 (Z_to_bv 64 (io_tsoffset opts)) y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x17874) fc None m3 (seg_rom usegs)).
  Section Sz4.
  Variables ra' t0' t2' a0' a2' a3' a5' a6' a7' t3' t4' t5' t6' y0 y2 y3 y5 y6 y7 y8 y9 y10 y11 m3 stG sg q1 I' SA js pad1 sj tail3 bs3 cpad3 opts c' buf' hd : ltac2:(SecDiet.SzSec.tyM 'ai_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ai_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ai_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HinB HinP IDB0 IFW LENB LO P14 RSP SFL SPW UTS. pin_using (fun (APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HinB HinP IDB0 IFW LENB LO P14 RSP SFL SPW UTS : unit) => tt).
 intros U1 U2 U5 IC1 IC2 SZ LJS HSA SNR TSR MI3 ST3 AG3 HD3 Hhd FR3 NG3 AR1 SL3 AR2 G3 BUF3 PFX3 LB3 GR3 CC3 CR1 CR2 CR3 CR4 HEB3 OFG.
    clear HPV HNG HBUF HCUR HEB HIF.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
    assert (API : (P + 680 <= I' \/ I' + 40 * ng_ifaces_size sg <= P)%Z).
    { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
    unfold ai_FRAME in FR3. unfold ng_cells in NG3.
    assert (APIB : (B + pc_bufalloc p <= I' \/ I' + 40 * ng_ifaces_size sg <= B)%Z).
    { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinB) as AP. cbn [cb_addr cb_size fst snd] in AP. lia. }
    assert (LSJ : length sj = 36%nat) by (destruct SL3 as [[WF _] _]; cbn in WF; lia).
    assert (SAR : (0 < SA /\ SA + 40 < 2^64)%Z) by (clear - HSA Q1 Q4 IC1 IC2 SZ; lia).
    assert (U0 : (0 < ng_user_tsresol sg < 2^64)%Z) by (rewrite U1; exact UTS).
    hide HD3. hide FR3. hide AR1. hide AR2. hide BUF3. hide CC3. hide HEB3. hide SL3.
    (* [comment removed for export] *)
    step. if_false_by (eqz_false SA ltac:(clear - SAR; lia)).
    step.
    (* [comment removed for export] *)
    assert (FIN : forall (m5 : mem) (jn : if_junk),
      munch [(SA, SA + 40)]%Z m3 m5 -> wmono usegs m3 m5 ->
      rw_cells usegs m5 SA (if_cells (ai_slot opts) jn) ->
      AIREST m5 stG (ai_result sg (Some q1) (buf', inr (opts, c')))).
    { intros m5 jn MU WM SL5.
      assert (AGS : agrees_on (fun a => outside [(SA, SA + 40)]%Z a) m3 m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide AR1. unhide AR2. unhide BUF3. unhide CC3. unhide HEB3.
      pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
      transport NG3 m5 AGS ltac:(prs). transport AR2 m5 AGS ltac:(prs). transport BUF3 m5 AGS ltac:(prs).
      transport AR1 m5 AGS ltac:(intros a Ha; rewrite ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [outside]; split; [lia| exact Logic.I]).
      transport CC3 m5 AGS ltac:(prs). transport HEB3 m5 AGS ltac:(prs).
      assert (G5 : GIo K R stG ((q1, I', 40 * ng_ifaces_size sg) :: C1 ++ C2) FB m5).
      { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      unfold ai_result. exists (mkNg (ng_user_tsresol sg) (ng_max_blocksize sg) (ng_ifcount sg) (ng_ifaces_size sg) (ai_slot opts :: ng_ifaces sg)), (Some q1), I', pad1, bs3.
      split; [exact OFG|]. split; [reflexivity|]. split; [exact G5|]. split; [exact NG3|]. split; [cbn; exact U1|]. split; [cbn; exact U2|]. split; [cbn; lia|]. split; [cbn; lia|].
      split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LB3|]. split; [exact GR3|]. cbv iota.
      split.
      { unfold ifaces_ok. cbn [pc_priv set_ng set_priv set_bufdata ng_ifaces ng_ifaces_size ng_ifcount].
        exists (js ++ [jn]), tail3. split; [rewrite !length_app, LJS, U5; cbn [length]; lia|].
        split; [| rewrite U5; cbn [length]; split; [lia|]; split; [lia|]; split; [lia|];
                  constructor; [| exact IFW];
                  unfold if_wf, ai_slot, ai_scale; cbn [if_tsresol if_scale_type if_scale_factor];
                  destruct (io_tsresol opts =? ng_user_tsresol s) eqn:QX1; [cbn; split; [exact TSR| discriminate]|];
                  destruct (ng_user_tsresol s <? io_tsresol opts) eqn:QX2; destruct (io_is_binary opts); cbn [is_dec if_scale_factor];
                  (split; [exact TSR|]); intros Hd; try discriminate Hd;
                  [ apply Z.ltb_lt in QX2; split; [apply Z.div_str_pos; lia| apply Z.div_lt_upper_bound; lia]
                  | apply Z.ltb_ge in QX2; apply Z.eqb_neq in QX1; split; [apply Z.div_str_pos; lia| apply Z.div_lt_upper_bound; lia] ] ].
        cbn [rev]. rewrite <- (ifs_cells_app (rev (ng_ifaces sg)) [ai_slot opts] js [jn]) by (rewrite length_rev, LJS, U5; reflexivity).
        cbn [ifs_cells]. rewrite app_nil_r, U5.
        pose proof (rw_cells_uncut _ _ _ _ _ AR1 SL5 ltac:(rewrite ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as J1.
        pose proof (rw_cells_uncut _ _ _ _ _ J1 AR2 ltac:(rewrite cells_size_app, ifs_cells_size, if_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as J2.
        exact J2. }
      split; [exists cpad3; exact CC3|]. split; [exact CR1|]. split; [exact CR2|]. split; [exact CR3|]. split; [exact CR4|]. split; [exact HEB3| reflexivity]. }
    pose proof (munch_refl [(SA, SA + 40)]%Z m3) as MU5. pose proof (wmono_refl usegs m3) as WM5.
    (* [comment removed for export] *)
    unhide SL3. step. step.
    step.
    (* [comment removed for export] *)
    assert (LEAF : forall (ra'' t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' y4'' : word) (m5 : mem) (jn : if_junk),
      mem_inv usegs m5 -> stk usegs m5 lo (bv_unsigned sp + -112) ->
      munch [(SA, SA + 40)]%Z m3 m5 -> wmono usegs m3 m5 ->
      rw_cells usegs m5 SA (if_cells (ai_slot opts) jn) ->
      evt usegs (POSTQ (ai_result sg (Some q1) (buf', inr (opts, c'))) stG)
        (MS (mkR ra'' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0'' t1'' t2'' y0 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                 y2 y3 y4'' y5 y6 y7 y8 y9 y10 y11 t3'' t4'' t5'' t6'') F (Z_to_bv 64 0x179c4) fc None m5 (seg_rom usegs))).
    { intros until jn. intros MI5 ST5 MU WM SL5.
      assert (AGS : agrees_on (fun a => outside [(SA, SA + 40)]%Z a) m3 m5) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide HD3. unhide FR3.
      transport HD3 m5 AGS ltac:(prs). transport FR3 m5 AGS ltac:(prs).
      unfold ai_result.
      eapply ai_exit; try eassumption.
      - eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] _]; cbn [outside]; (split; [| exact Logic.I]); [lia|].
        pose proof (CLB a Ha). destruct (proj1 (in_block_In _ _) Ha) as (b' & Hin & Hr). pose proof (head_apart K _ _ _ _ _ _ _ G3 Hin) as AP. cbn [cb_addr cb_size fst snd] in AP. lia.
      - pose proof (FIN m5 jn MU WM SL5) as X. unfold ai_result in X. exact X. }
    destruct (Z.eq_dec (io_tsresol opts) (ng_user_tsresol sg)) as [TE|TE].
    - (* [comment removed for export] *)
      rewrite (eqb_lits_eq _ _ TE). cbn [negb]. cbv iota.
      do 3 step.
      eapply LEAF; [assumption | assumption | exact MU5 | exact WM5 |].
      lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 12 ?b; _] =>
        eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a (firstn 4 b) (bv_extract 0 64 (le_bytes_to_word (skipn 4 b))))));
        [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
        unfold if_cells, ai_slot, ai_scale; rewrite (proj2 (Z.eqb_eq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)); cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
        pose proof (proj1 (proj1 SL3)) as WF; cbn in WF; rewrite (le8_ld (skipn 4 b)) by (rewrite length_skipn; lia);
        rewrite <- (firstn_skipn 4 b) at 3; rewrite <- ?app_assoc; reflexivity
      end.
    - rewrite (eqb_lits_false (io_tsresol opts) (ng_user_tsresol sg) ltac:(lia) ltac:(lia) TE). cbn [negb]. cbv iota.
      step.
      destruct (Z.lt_ge_cases (ng_user_tsresol sg) (io_tsresol opts)) as [LT|GE].
      + (* [comment removed for export] *)
        replace (bv_ltu (Z_to_bv 64 (ng_user_tsresol sg)) (Z_to_bv 64 (io_tsresol opts))) with true
          by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
        destruct (io_is_binary opts) eqn:BIN; cbn [Z.b2z].
        * (* [comment removed for export] *)
          step. if_false. do 5 step.
          eapply LEAF; [assumption | assumption | exact MU5 | exact WM5 |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 12 ?b; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a (firstn 4 b) (bv_extract 0 64 (le_bytes_to_word (skipn 4 b))))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, ai_slot, ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_lt (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            pose proof (proj1 (proj1 SL3)) as WF; cbn in WF; rewrite (le8_ld (skipn 4 b)) by (rewrite ?length_skipn, ?length_firstn in *; lia);
            rewrite <- (firstn_skipn 4 b) at 3; rewrite <- ?app_assoc; reflexivity
          end.
        * (* [comment removed for export] *)
          step. if_true. step. if_false_by (eqz_false (ng_user_tsresol sg) ltac:(clear - U0; lia)).
          step.
          rewrite (m_divu (Z_to_bv 64 (io_tsresol opts)) (Z_to_bv 64 (ng_user_tsresol sg))) by (rewrite unsigned_lit by lia; lia). rewrite !(unsigned_lit (io_tsresol opts)), !(unsigned_lit (ng_user_tsresol sg)) by lia.
          step. step. step. step. step.
          eapply LEAF; [assumption | assumption | exact MU5 | exact WM5 |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 4 ?b; _; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a b (Z_to_bv 64 0))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, ai_slot, ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_lt (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            rewrite <- U1; rewrite <- ?app_assoc; reflexivity
          end.
      + (* [comment removed for export] *)
        replace (bv_ltu (Z_to_bv 64 (ng_user_tsresol sg)) (Z_to_bv 64 (io_tsresol opts))) with false
          by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia). cbn [negb]. cbv iota.
        destruct (io_is_binary opts) eqn:BIN; cbn [Z.b2z].
        * (* [comment removed for export] *)
          step. if_false. do 4 step.
          eapply LEAF; [assumption | assumption | exact MU5 | exact WM5 |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 12 ?b; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a (firstn 4 b) (bv_extract 0 64 (le_bytes_to_word (skipn 4 b))))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, ai_slot, ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_ge (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            pose proof (proj1 (proj1 SL3)) as WF; cbn in WF; rewrite (le8_ld (skipn 4 b)) by (rewrite ?length_skipn, ?length_firstn in *; lia);
            rewrite <- (firstn_skipn 4 b) at 3; rewrite <- ?app_assoc; reflexivity
          end.
        * (* [comment removed for export] *)
          step. if_true. step. if_false_by (eqz_false (io_tsresol opts) ltac:(clear - TSR; lia)).
          step.
          rewrite (m_divu (Z_to_bv 64 (ng_user_tsresol sg)) (Z_to_bv 64 (io_tsresol opts))) by (rewrite unsigned_lit by lia; lia). rewrite !(unsigned_lit (io_tsresol opts)), !(unsigned_lit (ng_user_tsresol sg)) by lia.
          step. step. step. step.
          eapply LEAF; [assumption | assumption | exact MU5 | exact WM5 |].
          lazymatch type of SL3 with rw_cells _ _ _ [_; CB 4 ?a; _; _; CB 4 ?b; _; _] =>
            eapply (rw_cells_recell _ _ _ (if_cells (ai_slot opts) (mkIJ a b (Z_to_bv 64 0))));
            [exact SL3 | pose proof (proj1 (proj1 SL3)) as WF; cbn in WF |- *; repeat split; try exact Logic.I; rewrite ?length_firstn, ?length_skipn in *; lia |];
            unfold if_cells, ai_slot, ai_scale; rewrite (proj2 (Z.eqb_neq (io_tsresol opts) (ng_user_tsresol s)) ltac:(lia)), (proj2 (Z.ltb_ge (ng_user_tsresol s) (io_tsresol opts)) ltac:(lia)), BIN;
            cbn [cells_bytes cbytes app ij_p1 ij_p2 ij_sf if_snaplen if_tsresol if_scale_type if_scale_factor if_tsoffset ngscale_code is_dec];
            rewrite <- U1; rewrite <- ?app_assoc; reflexivity
          end.
  Qed.
  End Sz4.
  Lemma ai_tail : ltac:(let t := eval cbv delta [ai_tail__stmt] in ai_tail__stmt in exact t).
  Proof using APB BU CEND CLB COFF CREM CUR1 CUR8 EBX HFL HinB HinP IDB0 IFW LENB LO P14 RSP SFL SPW UTS. intros ra' t0' t2' a0' a2' a3' a5' a6' a7' t3' t4' t5' t6' y0 y2 y3 y5 y6 y7 y8 y9 y10 y11 m3 stG sg q1 I' SA js pad1 sj tail3 bs3 cpad3 opts c' buf' hd. ltac2:(SecDiet.SzSec.closeP 'ai_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AIB.

End WithCeil.
End TwB.
End F_sfpcapng_aiB.

(* [comment removed for export] *)
Module F_sfpcapng_chkF.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
Import ListNotations.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcap_chkA.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section NgModel.
  Context {M : Type -> Type} (MO : MonadOps M) {fh ptr : Type} (P : Prims M fh ptr).
  Local Notation "x <- m ;; k" := (mo_bind MO m (fun x => k)) (at level 100, m at next level, right associativity).
  Local Notation "m ;;; k" := (mo_bind MO m (fun _ => k)) (at level 100, right associativity).
  Local Notation "' pat <- m ;; k" := (mo_bind MO m (fun x => let 'pat := x in k)) (at level 100, pat pattern, m at next level, right associativity).
  Local Notation "'ret' x" := (mo_ret MO x) (at level 10).
  Local Notation "'fret' f x" := (e_fret P f x) (at level 10, f at level 0).
  #[local] Notation pcapM := (PcapTypes.pcap ptr fh).
  #[local] Notation chkres := (@check_result fh ptr).

  (* [comment removed for export] *)
  Definition ngc_fail (m : list Z) (p : pcapM) : M chkres :=
    free_opt MO P (ng_ifaces_ptr_of p) ;;; e_free P (pc_buffer p) ;;; e_free P (pc_self p) ;;; fret FF_NG_CHECK_HEADER (CH_Err m).

  (* [comment removed for export] *)
  Definition ngc_done (precision idb_off : Z) (p1 : pcapM) : M chkres :=
    let lt := linktype_to_dlt (get_le16 (pc_bufdata p1) idb_off) in
    let snapshot := pcapint_adjust_snapshot lt (get_le32 (pc_bufdata p1) (idb_off + 4)) in
    let ng := ng_of p1 in
    let mb := MAX_BLOCKSIZE_FOR_SNAPLEN (max_snaplen_for_dlt lt) in
    let ng := if ng_max_blocksize ng <? mb
              then mkNg (ng_user_tsresol ng) mb (ng_ifcount ng) (ng_ifaces_size ng) (ng_ifaces ng)
              else ng in
    fret FF_NG_CHECK_HEADER (CH_Ok (mkPcap (pc_self p1) (pc_rfile p1) (pc_bufsize p1) (pc_bufalloc p1) (pc_buffer p1)
                  (pc_bufdata p1) (pc_swapped p1) (pc_version_major p1) (pc_version_minor p1)
                  snapshot lt 0 precision 0 [] hdr0 (PrivNg ng (ng_ifaces_ptr_of p1)))).

  Definition ngc_loop_tail (precision : Z) (r : ((list Z) + Z) * pcapM) : M chkres :=
    match r with
    | (inl m, p1) => ngc_fail m p1
    | (inr idb_off, p1) => ngc_done precision idb_off p1
    end.
  (* [comment removed for export] *)
  Definition ngc_find (fuel : nat) (precision : Z) (p0 : pcapM) : M chkres :=
    r <- ng_find_idb MO P fuel p0 ;; ngc_loop_tail precision r.

  (* [comment removed for export] *)
  Definition ngc_after_rb (fuel : nat) (precision : Z) (swapped : bool) (p0 : pcapM) (st : rb_status) (data : list Z) : M chkres :=
    let p0 := set_bufdata (pc_bufdata p0 ++ data) p0 in
    match st with
    | RBS_Err m => ngc_fail m p0
    | RBS_Eof => ngc_fail [] p0
    | RBS_Ok =>
      let p0 := if swapped then set_bufdata (swap_field 2 14 (swap_field 2 12 (pc_bufdata p0))) p0 else p0 in
      let major := get_le16 (pc_bufdata p0) 12 in
      let minor := get_le16 (pc_bufdata p0) 14 in
      if negb ((major =? 1) && ((minor =? 0) || (minor =? 2)))
      then ngc_fail (Msg.unsupported_pcapng_version major minor) p0
      else
      let p0 := mkPcap (pc_self p0) (pc_rfile p0) (pc_bufsize p0) (pc_bufalloc p0) (pc_buffer p0)
                  (pc_bufdata p0) (pc_swapped p0) major minor (pc_snapshot p0) (pc_linktype p0)
                  (pc_linktype_ext p0) precision 0 [] hdr0 (pc_priv p0) in
      ngc_find fuel precision p0
    end.

  (* [comment removed for export] *)
  Definition ngc_p0 (self : ptr) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) (buf : ptr) (user_tsresol : Z) : pcapM :=
    let bufsize := if 2048 <? TL then TL else 2048 in
    mkPcap self fp bufsize bufsize buf (le_bytes 4 magic_int ++ le_bytes 4 TL ++ le_bytes 4 BYTE_ORDER_MAGIC)
           swapped 0 0 0 0 0 precision 0 [] hdr0 (PrivNg (mkNg user_tsresol INITIAL_MAX_BLOCKSIZE 0 0 []) None).

  (* [comment removed for export] *)
  Definition ngc_buf (fuel : nat) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) (self : ptr) (user_tsresol : Z) : M chkres :=
    let bufsize := if 2048 <? TL then TL else 2048 in
    b <- e_malloc P bufsize ;;
    match b with
    | None => e_free P self ;;; fret FF_NG_CHECK_HEADER (CH_Err Msg.out_of_memory)
    | Some buf =>
      '(st, data) <- read_bytes MO P fp (DHeap buf 12) (TL - 12) true ;;
      ngc_after_rb fuel precision swapped (ngc_p0 self fp precision magic_int swapped TL buf user_tsresol) st data
    end.

  (* [comment removed for export] *)
  Definition ngc_open (fuel : nat) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) : M chkres :=
    r <- pcapint_open_offline_common MO P PCAP_NG_SF_TOTAL ;;
    match r with
    | inl m => fret FF_NG_CHECK_HEADER (CH_Err m)
    | inr self =>
      let user_tsresol := if precision =? PCAP_TSTAMP_PRECISION_MICRO then Some 1000000
                          else if precision =? PCAP_TSTAMP_PRECISION_NANO then Some 1000000000
                          else None in
      match user_tsresol with
      | None => e_free P self ;;; fret FF_NG_CHECK_HEADER (CH_Err (Msg.unknown_tstamp_resolution precision))
      | Some user_tsresol => ngc_buf fuel fp precision magic_int swapped TL self user_tsresol
      end
    end.

  (* [comment removed for export] *)
  Definition ngc_head (fuel : nat) (magic : list Z) (fp : fh) (precision : Z) : M chkres :=
    let magic_int := le_of_bytes magic in
    if negb (magic_int =? BT_SHB) then fret FF_NG_CHECK_HEADER CH_NotMe else
    tlb <- e_fread P fp (DStack SiteNgTotalLength 0) 4 ;;
    if zlength tlb <? 4 then
      (e <- e_ferror P fp ;;
       if e then (m <- errmsg_for_errno MO P "error reading dump file" [] ;; fret FF_NG_CHECK_HEADER (CH_Err m)) else fret FF_NG_CHECK_HEADER CH_NotMe)
    else
    bomb <- e_fread P fp (DStack SiteNgByteOrderMagic 0) 4 ;;
    if zlength bomb <? 4 then
      (e <- e_ferror P fp ;;
       if e then (m <- errmsg_for_errno MO P "error reading dump file" [] ;; fret FF_NG_CHECK_HEADER (CH_Err m)) else fret FF_NG_CHECK_HEADER CH_NotMe)
    else
    let total_length := get_le32 tlb 0 in
    let byte_order_magic := get_le32 bomb 0 in
    let '(ok, swapped, total_length) :=
      if byte_order_magic =? BYTE_ORDER_MAGIC then (true, false, total_length)
      else if bswap32 byte_order_magic =? BYTE_ORDER_MAGIC then (true, true, bswap32 total_length)
      else (false, false, total_length) in
    if negb ok then fret FF_NG_CHECK_HEADER CH_NotMe else
    if (total_length <? 28) || (BT_SHB_INSANE_MAX <? total_length)
    then fret FF_NG_CHECK_HEADER (CH_Err (Msg.shb_invalid_length total_length))
    else ngc_open fuel fp precision magic_int swapped total_length.

  Lemma ngc_head_eq : forall fuel magic fp precision,
    pcap_ng_check_header MO P fuel magic fp precision = e_fenter P FF_NG_CHECK_HEADER (ngc_head fuel magic fp precision).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ngc_K (fuel : nat) (rb : block_result) : M (((list Z) + Z) * pcapM) :=
    match rb with
    | RB_Eof p => ret (inl Msg.no_idb, p)
    | RB_Err m p => ret (inl m, p)
    | RB_Ok c p =>
      let bt := cur_block_type c in
      if bt =? BT_IDB then
        match get_from_block_data c 8 with
        | inl m => ret (inl m, p)
        | inr (off, c) =>
          let p := if pc_swapped p
                   then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off (pc_bufdata p))) p
                   else p in
          '(ok, c, p, m) <- add_interface MO P p off c ;;
          if ok then ret (inr off, p) else ret (inl m, p)
        end
      else if (bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB) then
        ret (inl Msg.packet_before_idb, p)
      else ng_find_idb MO P fuel p
    end.
  Lemma ng_find_idb_S : forall fuel p,
    ng_find_idb MO P (S fuel) p = (rb <- read_block MO P (DStack SiteBhdrCheckHeader 0) p ;; ngc_K fuel rb).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ngc_round (fuel : nat) (precision : Z) (rb : block_result) : M chkres :=
    match rb with
    | RB_Eof p => ngc_fail Msg.no_idb p
    | RB_Err m p => ngc_fail m p
    | RB_Ok c p =>
      let bt := cur_block_type c in
      if bt =? BT_IDB then
        match get_from_block_data c 8 with
        | inl m => ngc_fail m p
        | inr (off, c) =>
          let p := if pc_swapped p
                   then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off (pc_bufdata p))) p
                   else p in
          '(ok, c, p, m) <- add_interface MO P p off c ;;
          if ok then ngc_done precision off p else ngc_fail m p
        end
      else if (bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB) then ngc_fail Msg.packet_before_idb p
      else ngc_find fuel precision p
    end.
End NgModel.

Section ChkNgF.
  Context {H hptr : Type} (K : modkit H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HPL : heap_perm_law K.

  (* [comment removed for export] *)
  Definition ngcells (P : Z) (np bsz buf sw maj min snap lt ext prec cln : cell) : list cell :=
    [ C8 (Z_to_bv 64 0); np; C4 (Z_to_bv 64 (-1)); bsz; buf; CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (P + 648)); sw; CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      maj; min; snap; lt; ext;
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); prec;
      CB 48 fd_pad48; C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; cln ].
  Remark ngcells_size : forall P np bsz buf sw maj min snap lt ext prec cln,
    csize np = 8%nat -> csize bsz = 4%nat -> csize buf = 8%nat -> csize sw = 4%nat -> csize maj = 4%nat -> csize min = 4%nat ->
    csize snap = 4%nat -> csize lt = 4%nat -> csize ext = 4%nat -> csize prec = 4%nat -> csize cln = 8%nat ->
    cells_size (ngcells P np bsz buf sw maj min snap lt ext prec cln) = 648%nat.
  Proof using Type. pin_using tt. intros. cbn. lia. Qed.

  (* [comment removed for export] *)
  Definition ngcells0 (P : Z) : list cell :=
    ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0))
              (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)).
  Definition ng0 : pcap_ng_sf := mkNg 0 0 0 0 [].
  Definition pad0 : list byte := repeat (Z_to_bv 8 0) 4.

  (* [comment removed for export] *)
  Lemma blank_recell_ng : forall m P,
    rw_cells ssegs m P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                         C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                         CB (Z.to_nat (PCAP_NG_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_NG_SF_TOTAL - 188)))]) ->
    rw_cells ssegs m P (ngcells0 P ++ ng_cells ng0 0 pad0).
  Proof using Type. pin_using tt.
    intros m P Hc.
    destruct (rw_cells_cut _ _ _ 3 Hc) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [B C]. clear Hc X.
    cbn [firstn skipn cells_size csize Nat.add] in A, B, C.
    unfold PCAP_NG_SF_TOTAL in C. change (Z.to_nat (680 - 188)) with 492%nat in C. unfold PCAP_PRIV_OFF in B.
    assert (A' : rw_cells ssegs m P (firstn 7 (ngcells0 P))).
    { eapply rw_cells_recell; [exact A | cbn; repeat split; exact Logic.I | vm_compute; reflexivity]. }
    assert (C' : rw_cells ssegs m (P + Z.of_nat 48 + Z.of_nat 8) (skipn 8 (ngcells0 P ++ ng_cells ng0 0 pad0))).
    { eapply rw_cells_recell; [exact C | cbn; repeat split; exact Logic.I | unfold fd_pad48, z8, pad0; vm_compute; reflexivity]. }
    pose proof (rw_cells_uncut _ _ _ _ _ A' B ltac:(cbn; lia)) as AB.
    pose proof (rw_cells_uncut _ _ _ _ _ AB C' ltac:(cbn; lia)) as ABC. exact ABC.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ngc_AGQ (sp : word) (CL : list cblk) (EB ERR : Z) (m m3 : mem) : Prop :=
    agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4)) m m3.
  (* [comment removed for export] *)
  Definition ngc_FRS (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (m3 : mem) : Prop :=
    rw_cells ssegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition ngc_p (f qs : hptr) (sw : bool) (BS0 MINOR : Z) (qb : hptr) (bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) : pcapT :=
    mkPcap qs f BS0 bufalloc qb bufdata sw 1 MINOR 0 0 0 0 0 [] hdr0 (PrivNg sg i).
  (* [comment removed for export] *)
  Definition ngc_hcells (P : Z) (sw : bool) (BS0 MINOR : Z) (B : Z) : list cell :=
    ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 1)) (C4 (Z_to_bv 64 MINOR))
              (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Lemma ngl_iv_P : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk) lo hi,
    P <= lo -> hi <= P + 680 -> iv_in_block (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) (lo, hi).
  Proof using Type. pin_using tt.
    intros. unfold iv_in_block. apply (proj2 (Exists_app _ _ _)). right. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
  Qed.
  Lemma ngl_iv_B : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk) lo hi,
    B <= lo -> hi <= B + ba -> iv_in_block (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) (lo, hi).
  Proof using Type. pin_using tt.
    intros. unfold iv_in_block. apply (proj2 (Exists_app _ _ _)). right. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
  Qed.
  Lemma ngl_in_CL : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk) a,
    in_block CL a -> in_block (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) a.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros. apply (proj2 (in_block_app _ _ _)). right. unfold in_block in *. do 2 apply Exists_cons_tl. assumption.
  Qed.
  Lemma ngl_perm : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk),
    Permutation (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) (CL ++ (qs, P, 680) :: (qb, B, ba) :: IBLK i I sg).
  Proof using Type. pin_using tt.
    intros. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app].
    apply Permutation_cons_app. apply Permutation_cons_app. apply Permutation_refl.
  Qed.
  (* [comment removed for export] *)
  Lemma ngl_perm_rb : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk),
    Permutation ((qb, B, ba) :: (IBLK i I sg ++ [(qs, P, 680)]) ++ CL) (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL).
  Proof using Type. pin_using tt.
    intros. rewrite <- app_assoc. cbn [app].
    replace (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) with ((IBLK i I sg ++ [(qs, P, 680)]) ++ (qb, B, ba) :: CL) by (rewrite <- app_assoc; reflexivity).
    apply Permutation_cons_app. rewrite <- app_assoc. apply Permutation_refl.
  Qed.
  Lemma ngl_assoc_rb : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk),
    IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL = (IBLK i I sg ++ [(qs, P, 680)]) ++ (qb, B, ba) :: CL.
  Proof using Type. pin_using tt. intros. rewrite <- app_assoc. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ngl_facts : forall R st (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL FB : list cblk) m,
    GIo K R st (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) FB m -> 1 <= ba ->
    (0 < B /\ B mod 16 = 0 /\ B + ba <= CEILZ)
    /\ (P + 680 <= B \/ B + ba <= P)
    /\ (forall sg' q, PrivNg sg i = PrivNg sg' (Some q) ->
          0 < I /\ I + 40 * ng_ifaces_size sg' <= CEILZ
          /\ (I + 40 * ng_ifaces_size sg' <= P \/ P + 680 <= I) /\ (I + 40 * ng_ifaces_size sg' <= B \/ B + ba <= I))
    /\ (forall a, in_block CL a -> ~ (P <= a < P + 680) /\ ~ (B <= a < B + ba)).
  Proof using HPL. pin_using (fun (HPL : unit) => tt).
    intros R st i I sg qs P qb B ba CL FB m G Hba.
    assert (HinB : In (qb, B, ba) (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL)) by (apply in_or_app; right; right; left; reflexivity).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; left; exact HinB)) as (B1 & B2 & B3 & B4 & _). cbn [cb_addr cb_size fst snd] in B1, B2, B3, B4.
    pose proof (mid_apart K _ _ (IBLK i I sg) ((qb, B, ba) :: CL) FB (qs, P, 680) (qb, B, ba) m G ltac:(apply in_or_app; right; left; reflexivity)) as APB.
    cbn [cb_addr cb_size fst snd] in APB.
    split; [lia|]. split; [lia|]. split.
    - intros sg' q E. injection E as Ei Es. subst i sg'. cbn [IBLK] in G.
      pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(left; reflexivity)) as (I1 & I2 & I3 & I4 & _). cbn [cb_addr cb_size fst snd] in I1, I4.
      pose proof (head_apart K _ _ _ _ _ (qs, P, 680) _ G ltac:(left; reflexivity)) as X1.
      pose proof (head_apart K _ _ _ _ _ (qb, B, ba) _ G ltac:(right; left; reflexivity)) as X2.
      cbn [cb_addr cb_size fst snd] in X1, X2. lia.
    - intros a Ha. pose proof (GIo_perm K HPL _ _ _ _ _ _ G (ngl_perm i I sg qs P qb B ba CL)) as G'.
      destruct (GIo_CLc_facts K R st CL _ FB m a G' Ha) as [_ Hn]. split; intros Hin; apply Hn; unfold in_block.
      + apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
      + apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
  Qed.
End ChkNgF.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkA.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Sorting.Permutation.
Import ListNotations.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkA.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section NgModel.
  Context {M : Type -> Type} (MO : MonadOps M) {fh ptr : Type} (P : Prims M fh ptr).
  Local Notation "x <- m ;; k" := (mo_bind MO m (fun x => k)) (at level 100, m at next level, right associativity).
  Local Notation "m ;;; k" := (mo_bind MO m (fun _ => k)) (at level 100, right associativity).
  Local Notation "' pat <- m ;; k" := (mo_bind MO m (fun x => let 'pat := x in k)) (at level 100, pat pattern, m at next level, right associativity).
  Local Notation "'ret' x" := (mo_ret MO x) (at level 10).
  Local Notation "'fret' f x" := (e_fret P f x) (at level 10, f at level 0).
  #[local] Notation pcapM := (PcapTypes.pcap ptr fh).
  #[local] Notation chkres := (@check_result fh ptr).

  (* [comment removed for export] *)
  Definition ngc_fail (m : list Z) (p : pcapM) : M chkres :=
    free_opt MO P (ng_ifaces_ptr_of p) ;;; e_free P (pc_buffer p) ;;; e_free P (pc_self p) ;;; fret FF_NG_CHECK_HEADER (CH_Err m).

  (* [comment removed for export] *)
  Definition ngc_done (precision idb_off : Z) (p1 : pcapM) : M chkres :=
    let lt := linktype_to_dlt (get_le16 (pc_bufdata p1) idb_off) in
    let snapshot := pcapint_adjust_snapshot lt (get_le32 (pc_bufdata p1) (idb_off + 4)) in
    let ng := ng_of p1 in
    let mb := MAX_BLOCKSIZE_FOR_SNAPLEN (max_snaplen_for_dlt lt) in
    let ng := if ng_max_blocksize ng <? mb
              then mkNg (ng_user_tsresol ng) mb (ng_ifcount ng) (ng_ifaces_size ng) (ng_ifaces ng)
              else ng in
    fret FF_NG_CHECK_HEADER (CH_Ok (mkPcap (pc_self p1) (pc_rfile p1) (pc_bufsize p1) (pc_bufalloc p1) (pc_buffer p1)
                  (pc_bufdata p1) (pc_swapped p1) (pc_version_major p1) (pc_version_minor p1)
                  snapshot lt 0 precision 0 [] hdr0 (PrivNg ng (ng_ifaces_ptr_of p1)))).

  Definition ngc_loop_tail (precision : Z) (r : ((list Z) + Z) * pcapM) : M chkres :=
    match r with
    | (inl m, p1) => ngc_fail m p1
    | (inr idb_off, p1) => ngc_done precision idb_off p1
    end.
  (* [comment removed for export] *)
  Definition ngc_find (fuel : nat) (precision : Z) (p0 : pcapM) : M chkres :=
    r <- ng_find_idb MO P fuel p0 ;; ngc_loop_tail precision r.

  (* [comment removed for export] *)
  Definition ngc_after_rb (fuel : nat) (precision : Z) (swapped : bool) (p0 : pcapM) (st : rb_status) (data : list Z) : M chkres :=
    let p0 := set_bufdata (pc_bufdata p0 ++ data) p0 in
    match st with
    | RBS_Err m => ngc_fail m p0
    | RBS_Eof => ngc_fail [] p0
    | RBS_Ok =>
      let p0 := if swapped then set_bufdata (swap_field 2 14 (swap_field 2 12 (pc_bufdata p0))) p0 else p0 in
      let major := get_le16 (pc_bufdata p0) 12 in
      let minor := get_le16 (pc_bufdata p0) 14 in
      if negb ((major =? 1) && ((minor =? 0) || (minor =? 2)))
      then ngc_fail (Msg.unsupported_pcapng_version major minor) p0
      else
      let p0 := mkPcap (pc_self p0) (pc_rfile p0) (pc_bufsize p0) (pc_bufalloc p0) (pc_buffer p0)
                  (pc_bufdata p0) (pc_swapped p0) major minor (pc_snapshot p0) (pc_linktype p0)
                  (pc_linktype_ext p0) precision 0 [] hdr0 (pc_priv p0) in
      ngc_find fuel precision p0
    end.

  (* [comment removed for export] *)
  Definition ngc_p0 (self : ptr) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) (buf : ptr) (user_tsresol : Z) : pcapM :=
    let bufsize := if 2048 <? TL then TL else 2048 in
    mkPcap self fp bufsize bufsize buf (le_bytes 4 magic_int ++ le_bytes 4 TL ++ le_bytes 4 BYTE_ORDER_MAGIC)
           swapped 0 0 0 0 0 precision 0 [] hdr0 (PrivNg (mkNg user_tsresol INITIAL_MAX_BLOCKSIZE 0 0 []) None).

  (* [comment removed for export] *)
  Definition ngc_buf (fuel : nat) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) (self : ptr) (user_tsresol : Z) : M chkres :=
    let bufsize := if 2048 <? TL then TL else 2048 in
    b <- e_malloc P bufsize ;;
    match b with
    | None => e_free P self ;;; fret FF_NG_CHECK_HEADER (CH_Err Msg.out_of_memory)
    | Some buf =>
      '(st, data) <- read_bytes MO P fp (DHeap buf 12) (TL - 12) true ;;
      ngc_after_rb fuel precision swapped (ngc_p0 self fp precision magic_int swapped TL buf user_tsresol) st data
    end.

  (* [comment removed for export] *)
  Definition ngc_open (fuel : nat) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) : M chkres :=
    r <- pcapint_open_offline_common MO P PCAP_NG_SF_TOTAL ;;
    match r with
    | inl m => fret FF_NG_CHECK_HEADER (CH_Err m)
    | inr self =>
      let user_tsresol := if precision =? PCAP_TSTAMP_PRECISION_MICRO then Some 1000000
                          else if precision =? PCAP_TSTAMP_PRECISION_NANO then Some 1000000000
                          else None in
      match user_tsresol with
      | None => e_free P self ;;; fret FF_NG_CHECK_HEADER (CH_Err (Msg.unknown_tstamp_resolution precision))
      | Some user_tsresol => ngc_buf fuel fp precision magic_int swapped TL self user_tsresol
      end
    end.

  (* [comment removed for export] *)
  Definition ngc_head (fuel : nat) (magic : list Z) (fp : fh) (precision : Z) : M chkres :=
    let magic_int := le_of_bytes magic in
    if negb (magic_int =? BT_SHB) then fret FF_NG_CHECK_HEADER CH_NotMe else
    tlb <- e_fread P fp (DStack SiteNgTotalLength 0) 4 ;;
    if zlength tlb <? 4 then
      (e <- e_ferror P fp ;;
       if e then (m <- errmsg_for_errno MO P "error reading dump file" [] ;; fret FF_NG_CHECK_HEADER (CH_Err m)) else fret FF_NG_CHECK_HEADER CH_NotMe)
    else
    bomb <- e_fread P fp (DStack SiteNgByteOrderMagic 0) 4 ;;
    if zlength bomb <? 4 then
      (e <- e_ferror P fp ;;
       if e then (m <- errmsg_for_errno MO P "error reading dump file" [] ;; fret FF_NG_CHECK_HEADER (CH_Err m)) else fret FF_NG_CHECK_HEADER CH_NotMe)
    else
    let total_length := get_le32 tlb 0 in
    let byte_order_magic := get_le32 bomb 0 in
    let '(ok, swapped, total_length) :=
      if byte_order_magic =? BYTE_ORDER_MAGIC then (true, false, total_length)
      else if bswap32 byte_order_magic =? BYTE_ORDER_MAGIC then (true, true, bswap32 total_length)
      else (false, false, total_length) in
    if negb ok then fret FF_NG_CHECK_HEADER CH_NotMe else
    if (total_length <? 28) || (BT_SHB_INSANE_MAX <? total_length)
    then fret FF_NG_CHECK_HEADER (CH_Err (Msg.shb_invalid_length total_length))
    else ngc_open fuel fp precision magic_int swapped total_length.

  Lemma ngc_head_eq : forall fuel magic fp precision,
    pcap_ng_check_header MO P fuel magic fp precision = e_fenter P FF_NG_CHECK_HEADER (ngc_head fuel magic fp precision).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ngc_K (fuel : nat) (rb : block_result) : M (((list Z) + Z) * pcapM) :=
    match rb with
    | RB_Eof p => ret (inl Msg.no_idb, p)
    | RB_Err m p => ret (inl m, p)
    | RB_Ok c p =>
      let bt := cur_block_type c in
      if bt =? BT_IDB then
        match get_from_block_data c 8 with
        | inl m => ret (inl m, p)
        | inr (off, c) =>
          let p := if pc_swapped p
                   then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off (pc_bufdata p))) p
                   else p in
          '(ok, c, p, m) <- add_interface MO P p off c ;;
          if ok then ret (inr off, p) else ret (inl m, p)
        end
      else if (bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB) then
        ret (inl Msg.packet_before_idb, p)
      else ng_find_idb MO P fuel p
    end.
  Lemma ng_find_idb_S : forall fuel p,
    ng_find_idb MO P (S fuel) p = (rb <- read_block MO P (DStack SiteBhdrCheckHeader 0) p ;; ngc_K fuel rb).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ngc_round (fuel : nat) (precision : Z) (rb : block_result) : M chkres :=
    match rb with
    | RB_Eof p => ngc_fail Msg.no_idb p
    | RB_Err m p => ngc_fail m p
    | RB_Ok c p =>
      let bt := cur_block_type c in
      if bt =? BT_IDB then
        match get_from_block_data c 8 with
        | inl m => ngc_fail m p
        | inr (off, c) =>
          let p := if pc_swapped p
                   then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off (pc_bufdata p))) p
                   else p in
          '(ok, c, p, m) <- add_interface MO P p off c ;;
          if ok then ngc_done precision off p else ngc_fail m p
        end
      else if (bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB) then ngc_fail Msg.packet_before_idb p
      else ngc_find fuel precision p
    end.
End NgModel.

Section ChkNgF.
  Context {H hptr : Type} (K : modkit H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HPL : heap_perm_law K.

  (* [comment removed for export] *)
  Definition ngcells (P : Z) (np bsz buf sw maj min snap lt ext prec cln : cell) : list cell :=
    [ C8 (Z_to_bv 64 0); np; C4 (Z_to_bv 64 (-1)); bsz; buf; CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (P + 648)); sw; CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      maj; min; snap; lt; ext;
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); prec;
      CB 48 fd_pad48; C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; cln ].
  Remark ngcells_size : forall P np bsz buf sw maj min snap lt ext prec cln,
    csize np = 8%nat -> csize bsz = 4%nat -> csize buf = 8%nat -> csize sw = 4%nat -> csize maj = 4%nat -> csize min = 4%nat ->
    csize snap = 4%nat -> csize lt = 4%nat -> csize ext = 4%nat -> csize prec = 4%nat -> csize cln = 8%nat ->
    cells_size (ngcells P np bsz buf sw maj min snap lt ext prec cln) = 648%nat.
  Proof using Type. pin_using tt. intros. cbn. lia. Qed.

  (* [comment removed for export] *)
  Definition ngcells0 (P : Z) : list cell :=
    ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0))
              (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)).
  Definition ng0 : pcap_ng_sf := mkNg 0 0 0 0 [].
  Definition pad0 : list byte := repeat (Z_to_bv 8 0) 4.

  (* [comment removed for export] *)
  Lemma blank_recell_ng : forall m P,
    rw_cells usegs m P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                         C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                         CB (Z.to_nat (PCAP_NG_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_NG_SF_TOTAL - 188)))]) ->
    rw_cells usegs m P (ngcells0 P ++ ng_cells ng0 0 pad0).
  Proof using Type. pin_using tt.
    intros m P Hc.
    destruct (rw_cells_cut _ _ _ 3 Hc) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [B C]. clear Hc X.
    cbn [firstn skipn cells_size csize Nat.add] in A, B, C.
    unfold PCAP_NG_SF_TOTAL in C. change (Z.to_nat (680 - 188)) with 492%nat in C. unfold PCAP_PRIV_OFF in B.
    assert (A' : rw_cells usegs m P (firstn 7 (ngcells0 P))).
    { eapply rw_cells_recell; [exact A | cbn; repeat split; exact Logic.I | vm_compute; reflexivity]. }
    assert (C' : rw_cells usegs m (P + Z.of_nat 48 + Z.of_nat 8) (skipn 8 (ngcells0 P ++ ng_cells ng0 0 pad0))).
    { eapply rw_cells_recell; [exact C | cbn; repeat split; exact Logic.I | unfold fd_pad48, z8, pad0; vm_compute; reflexivity]. }
    pose proof (rw_cells_uncut _ _ _ _ _ A' B ltac:(cbn; lia)) as AB.
    pose proof (rw_cells_uncut _ _ _ _ _ AB C' ltac:(cbn; lia)) as ABC. exact ABC.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ngc_AGQ (sp : word) (CL : list cblk) (EB ERR : Z) (m m3 : mem) : Prop :=
    agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4)) m m3.
  (* [comment removed for export] *)
  Definition ngc_FRS (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (m3 : mem) : Prop :=
    rw_cells usegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition ngc_p (f qs : hptr) (sw : bool) (BS0 MINOR : Z) (qb : hptr) (bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) : pcapT :=
    mkPcap qs f BS0 bufalloc qb bufdata sw 1 MINOR 0 0 0 0 0 [] hdr0 (PrivNg sg i).
  (* [comment removed for export] *)
  Definition ngc_hcells (P : Z) (sw : bool) (BS0 MINOR : Z) (B : Z) : list cell :=
    ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 1)) (C4 (Z_to_bv 64 MINOR))
              (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Lemma ngl_iv_P : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk) lo hi,
    P <= lo -> hi <= P + 680 -> iv_in_block (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) (lo, hi).
  Proof using Type. pin_using tt.
    intros. unfold iv_in_block. apply (proj2 (Exists_app _ _ _)). right. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
  Qed.
  Lemma ngl_iv_B : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk) lo hi,
    B <= lo -> hi <= B + ba -> iv_in_block (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) (lo, hi).
  Proof using Type. pin_using tt.
    intros. unfold iv_in_block. apply (proj2 (Exists_app _ _ _)). right. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
  Qed.
  Lemma ngl_in_CL : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk) a,
    in_block CL a -> in_block (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) a.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros. apply (proj2 (in_block_app _ _ _)). right. unfold in_block in *. do 2 apply Exists_cons_tl. assumption.
  Qed.
  Lemma ngl_perm : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk),
    Permutation (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) (CL ++ (qs, P, 680) :: (qb, B, ba) :: IBLK i I sg).
  Proof using Type. pin_using tt.
    intros. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app].
    apply Permutation_cons_app. apply Permutation_cons_app. apply Permutation_refl.
  Qed.
  (* [comment removed for export] *)
  Lemma ngl_perm_rb : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk),
    Permutation ((qb, B, ba) :: (IBLK i I sg ++ [(qs, P, 680)]) ++ CL) (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL).
  Proof using Type. pin_using tt.
    intros. rewrite <- app_assoc. cbn [app].
    replace (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) with ((IBLK i I sg ++ [(qs, P, 680)]) ++ (qb, B, ba) :: CL) by (rewrite <- app_assoc; reflexivity).
    apply Permutation_cons_app. rewrite <- app_assoc. apply Permutation_refl.
  Qed.
  Lemma ngl_assoc_rb : forall (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL : list cblk),
    IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL = (IBLK i I sg ++ [(qs, P, 680)]) ++ (qb, B, ba) :: CL.
  Proof using Type. pin_using tt. intros. rewrite <- app_assoc. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ngl_facts : forall R st (i : option hptr) I sg (qs : hptr) P (qb : hptr) B ba (CL FB : list cblk) m,
    GIo K R st (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL) FB m -> 1 <= ba ->
    (0 < B /\ B mod 16 = 0 /\ B + ba <= CEILZ)
    /\ (P + 680 <= B \/ B + ba <= P)
    /\ (forall sg' q, PrivNg sg i = PrivNg sg' (Some q) ->
          0 < I /\ I + 40 * ng_ifaces_size sg' <= CEILZ
          /\ (I + 40 * ng_ifaces_size sg' <= P \/ P + 680 <= I) /\ (I + 40 * ng_ifaces_size sg' <= B \/ B + ba <= I))
    /\ (forall a, in_block CL a -> ~ (P <= a < P + 680) /\ ~ (B <= a < B + ba)).
  Proof using HPL. pin_using (fun (HPL : unit) => tt).
    intros R st i I sg qs P qb B ba CL FB m G Hba.
    assert (HinB : In (qb, B, ba) (IBLK i I sg ++ (qs, P, 680) :: (qb, B, ba) :: CL)) by (apply in_or_app; right; right; left; reflexivity).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; left; exact HinB)) as (B1 & B2 & B3 & B4 & _). cbn [cb_addr cb_size fst snd] in B1, B2, B3, B4.
    pose proof (mid_apart K _ _ (IBLK i I sg) ((qb, B, ba) :: CL) FB (qs, P, 680) (qb, B, ba) m G ltac:(apply in_or_app; right; left; reflexivity)) as APB.
    cbn [cb_addr cb_size fst snd] in APB.
    split; [lia|]. split; [lia|]. split.
    - intros sg' q E. injection E as Ei Es. subst i sg'. cbn [IBLK] in G.
      pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(left; reflexivity)) as (I1 & I2 & I3 & I4 & _). cbn [cb_addr cb_size fst snd] in I1, I4.
      pose proof (head_apart K _ _ _ _ _ (qs, P, 680) _ G ltac:(left; reflexivity)) as X1.
      pose proof (head_apart K _ _ _ _ _ (qb, B, ba) _ G ltac:(right; left; reflexivity)) as X2.
      cbn [cb_addr cb_size fst snd] in X1, X2. lia.
    - intros a Ha. pose proof (GIo_perm K HPL _ _ _ _ _ _ G (ngl_perm i I sg qs P qb B ba CL)) as G'.
      destruct (GIo_CLc_facts K R st CL _ FB m a G' Ha) as [_ Hn]. split; intros Hin; apply Hn; unfold in_block.
      + apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
      + apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
  Qed.
End ChkNgF.

End WithCeil.
End TwB.
End F_sfpcapng_chkF.
