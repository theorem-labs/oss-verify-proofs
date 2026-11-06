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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_nextA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfpcap_chkB.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcap_chkA.
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
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section Chk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis OPEN_COMMON : open_offline_common_stmt HO K sites.
  Hypothesis MALLOC : malloc_stmt_o HO K.
  Hypothesis FREE : free_stmt_o HO K.

  (* [comment removed for export] *)
  Definition chk_hdr__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PState H hptr) (CL FB : list cblock) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x5 x6 x8 : word) (m2 : mem) (ps2 : PState H hptr)
           (maj min n0 n1 n2 n3 l0 l1 l2 l3 mi : Z) (sw : bool) (mid junk8 e2 : list byte),
      chk_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) ->
      (0 <= maj < 2^16)%Z -> (0 <= min < 2^16)%Z ->
      (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
      (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= l2 < 256)%Z -> (0 <= l3 < 256)%Z ->
      mem_inv ssegs m2 -> stk ssegs m2 lo (bv_unsigned sp + -112) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m2 ->
      GIo K R ps2 CL FB m2 ->
      rw_cells ssegs m2 (bv_unsigned sp + -112) [CB 8 junk8; C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ->
      rw_cells ssegs m2 (bv_unsigned sp + -100)
        [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))] ->
      rw_cells ssegs m2 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m2 ERR [C4 z64] -> rw_cells ssegs m2 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m2 EB [CB 256 e2] ->
      ps_outfile ps2 = ps_outfile s ->
      implM ssegs (chk_rest2 MOps (prims HO fo_nop sites) f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)) ps2
        (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0 a1 a2 a3 a4 a5 a6 a7
                 z64 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 FA) x5 x6 (Z_to_bv 64 (mi + (2^64 - 2^32))) x8
                 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15124) fc None m2 (seg_rom ssegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x5 x6 x8 m2 ps2 maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw mid junk8 e2 : ltac2:(SecDiet.SzSec.tyM 'chk_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_hdr__body : ltac2:(SecDiet.SzSec.bodyP 'chk_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF. pin_using (fun (FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF : unit) => tt).
    intros CTX MI3 Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 MI2 ST2 AG2 G2 FRA FRD FRS ERRc MG4 HEB2 OFX.
    pose proof CTX as CTX'. destruct CTX' as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    assert (MIB : (2^31 <= mi < 2^32)%Z) by (unfold TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in MI3; lia).
    pose proof (rw_cells_bound _ _ _ _ HEB2) as BEB. cbn [cells_size csize Nat.add] in BEB.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    set (POSTQ := check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
    assert (FRSZ : cells_size ([CB 8 junk8; C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ++
                               [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))]) = 32%nat) by reflexivity.
    (* [comment removed for export] *)
    assert (KSNP : forall (ra5 t0' t1' t2' a3' a4' a5' a6' a7' s5' s6' s8' t3' t4' t5' t6' : word) (FMTA : Z) (fs : string) (args : list farg),
      (ra5 = Z_to_bv 64 0x15264 \/ ra5 = Z_to_bv 64 0x1516c) ->
      fmt_at m2 FMTA fs -> fmt_ok fs args = true -> (length args <= 2)%nat -> Forall2 (farg_word R CL (bv_unsigned sp + -112) EB 256 m2) args (firstn (length args) [a3'; a4']) ->
      (length (Fmt.snprintf 256 fs args) <= 255)%nat -> items_okb (fmt fs) = true -> Forall arg_ok args ->
      implM ssegs (mret (CH_Err (Fmt.snprintf 256 fs args))) ps2 POSTQ
        (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 z64 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 FA) s5' s6' (Z_to_bv 64 (mi + (2^64 - 2^32))) s8'
                 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m2 (seg_rom ssegs))).
    { intros ra5 t0' t1' t2' a3' a4' a5' a6' a7' s5' s6' s8' t3' t4' t5' t6' FMTA fs args Hra FMT5 FOK LA FW LEN IOK AOK.
      apply (implM_ret ssegs). name_sp sp (-112)%Z.
      eapply evt_cut.
      { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps2 CL FB lo EB 256%Z FMTA fs args e2);
          [| reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | exact (Nat.le_le_succ_r _ _ LA) | rewrite Hsp; replace (firstn (length args) [a3'; a4'; a5']) with (firstn (length args) [a3'; a4']) by (clear -LA; destruct args as [|? [|? [|? ?]]]; cbn in LA |- *; fastfirst (first [ noevar_assumption |reflexivity | lia])); exact FW | exact HEB2 | right; rewrite Hsp; lia].
        split; [exact G2|]. split; [rewrite Hsp; exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI2|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      cbv beta. intros ms' PO. destruct PO as (av & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -112 - STDIO_STACK, bv_unsigned sp + -112); (EB, EB + 256)]%Z a) m2 m6)
        by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      unfold STDIO_STACK in AGS.
      assert (KEEP : forall A cs, rw_cells ssegs m2 A cs -> (bv_unsigned sp + -112 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= EB \/ EB + 256 <= A)%Z -> rw_cells ssegs m6 A cs).
      { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AGS | exact HC | intros a Ha; cbn [outside]; lia]. }
      pose proof (rw_cells_uncut _ _ _ _ _ FRA FRD ltac:(cbn; lia)) as HC32.
      apply KEEP in HC32; [|lia|rewrite FRSZ; lia]. apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia].
      apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in MG4; [|lia|rewrite cells_size_map_C1, GL; lia].
      assert (G6 : GIo K R ps2 CL FB m6).
      { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU6 | exact WM6 |].
        apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, STDIO_STACK; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (AG6 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
      { eapply agrees_on_trans; [exact AG2|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|].
        pose proof (CLB a Ha). unfold rc_lo in LO. lia. }
      change (Z.to_nat 256) with 256%nat in HEB6.
      replace (256 - length (Fmt.snprintf 256 fs args) - 1)%nat with (255 - length (Fmt.snprintf 256 fs args))%nat in HEB6 by lia.
      destruct Hra as [-> | ->].
      - replace (ret_pc (Z_to_bv 64 86628)) with (Z_to_bv 64 86628) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        eapply (chk_fail K sites HFL SFL); [exact CTX | exact MI6 | exact ST6 | exact AG6 | exact G6 | exact HC32 | exact FRSZ | exact FRS | exact ERRc | exact MG4 | exact HEB6 | lia | apply snprintf_ok; [exact IOK| exact AOK] | congruence].
      - replace (ret_pc (Z_to_bv 64 86380)) with (Z_to_bv 64 86380) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        hide HEB6. step. unhide HEB6.
        eapply (chk_fail K sites HFL SFL); [exact CTX | exact MI6 | exact ST6 | exact AG6 | exact G6 | exact HC32 | exact FRSZ | exact FRS | exact ERRc | exact MG4 | exact HEB6 | lia | apply snprintf_ok; [exact IOK| exact AOK] | congruence]. }
    (* [comment removed for export] *)
    assert (KVER : forall (a0' : word),
      implM ssegs (mret (CH_Err (Msg.unsupported_pcap_version maj min))) ps2 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1 a2 a3 a4 a5 a6 a7
                 z64 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 FA) (Z_to_bv 64 min) (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) x8
                 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15248) fc None m2 (seg_rom ssegs))).
    { intros a0'. hide HEB2. hide MG4. hide ERRc.
      assert (MSG : fmt_at m2 0x10565 "unsupported pcap savefile version %u.%u"%string).
      { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m2 0x10565 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "unsupported pcap savefile version %u.%u"%string) ++ [Z_to_bv 8 0])
                                 MI2 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
      unfold implM. iprefix. do 7 step. unhide HEB2. unhide MG4. unhide ERRc.
      apply evt_done. unfold Msg.unsupported_pcap_version, PCAP_ERRBUF_SIZE.
      eapply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [AInt maj; AInt min]); [left; reflexivity | exact MSG | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
      { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
      pose proof (snprintf_length 256 "unsupported pcap savefile version %u.%u"%string [AInt maj; AInt min]) as LS. change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS. }
    (* [comment removed for export] *)
    assert (KOK : forall (a0' : word),
      implM ssegs (if negb (Z.land (le4val l0 l1 l2 l3) 67043328 =? 0)
                   then mret (CH_Err (Msg.reserved_not_zero (Z.land (le4val l0 l1 l2 l3) 67043328)))
                   else mbind (pcapint_open_offline_common MOps (prims HO fo_nop sites) PCAP_SF_TOTAL)
                          (fun r => match r with
                                    | inl m => mret (CH_Err m)
                                    | inr self => chk_fill_model MOps (prims HO fo_nop sites) self f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)
                                    end)) ps2 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1 a2 a3 a4 a5 a6 a7
                 z64 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 FA) (Z_to_bv 64 min) (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) x8
                 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15148) fc None m2 (seg_rom ssegs))).
    { intros a0'. rewrite (reserved_val l0 l1 l2 l3) by lia.
      hide HEB2. hide MG4. hide ERRc.
      unfold implM. iprefix. step. rewrite (sx32_lit l0 l1 l2 l3) by lia. do 2 step.
      rewrite (reserved_word l0 l1 l2 l3) by lia.
      destruct (Z.eq_dec ((l2 + 256 * (l3 mod 4)) * 65536) 0) as [RZ|RZ].
      - (* [comment removed for export] *)
        replace ((l2 + 256 * (l3 mod 4)) * 65536 =? 0) with true by (symmetry; apply Z.eqb_eq; exact RZ). cbn [negb].
        assert (Z2 : l2 = 0%Z) by lia. assert (Z3 : (l3 mod 4 = 0)%Z) by lia.
        step. if_cases Kr; [ idtac | try (zify_cond Kr; exfalso; lia) ].
        do 4 step. unhide HEB2. unhide MG4. unhide ERRc.
        name_sp sp (-112)%Z.
        apply evt_done. eapply (implM_bind ssegs).
        { eapply OPEN_COMMON; [| reflexivity | reflexivity | reflexivity | left; reflexivity | exact HEB2 | | exact E8 ].
          { split; [exact G2|]. split; [rewrite Hsp; exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1B_STACK; rewrite Hsp; lia|].
            split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
          right; rewrite Hsp; lia. }
        intros [msg|q] ps3 ms3 PO; cbv beta iota in PO.
        + (* [comment removed for export] *)
          destruct PO as (av & m3 & E & OF3 & MI3' & ST3 & AG3 & (junk3 & -> & G3 & HEB3 & LEN3 & RNG3)).
          unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
          replace (ret_pc (Z_to_bv 64 86476)) with (Z_to_bv 64 86476) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
          assert (KEEP : forall A cs, rw_cells ssegs m2 A cs -> (bv_unsigned sp + -112 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= EB \/ EB + 256 <= A)%Z -> rw_cells ssegs m3 A cs).
          { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG3 | exact HC | intros a Ha; split; [left; lia| lia]]. }
          pose proof (rw_cells_uncut _ _ _ _ _ FRA FRD ltac:(cbn; lia)) as HC32.
          apply KEEP in HC32; [|lia|rewrite FRSZ; lia]. apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia].
          apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in MG4; [|lia|rewrite cells_size_map_C1, GL; lia].
          assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3).
          { eapply agrees_on_trans; [exact AG2|]. eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] [Hn1 Hn2]]; (split; [|exact Hn1]); [left; lia| right; exact Ha]. }
          apply (implM_ret ssegs). hide HEB3. step. if_true. unhide HEB3.
          eapply (chk_fail K sites HFL SFL); [exact CTX | exact MI3' | exact ST3 | exact AG03 | exact G3 | exact HC32 | exact FRSZ | exact FRS | exact ERRc | exact MG4 | exact HEB3 | exact LEN3 | exact RNG3 | congruence].
        + (* [comment removed for export] *)
          destruct PO as (av & m3 & E & OF3 & MI3' & ST3 & AG3 & (P & -> & G3 & CELLS & HEB3)).
          unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
          replace (ret_pc (Z_to_bv 64 86476)) with (Z_to_bv 64 86476) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
          pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (P1 & _ & _ & P4 & _). cbn [cb_addr cb_size fst snd] in P1, P4. unfold PCAP_SF_TOTAL in P4.
          assert (KEEP : forall A cs, rw_cells ssegs m2 A cs -> (bv_unsigned sp + -112 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= EB \/ EB + 256 <= A)%Z -> rw_cells ssegs m3 A cs).
          { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG3 | exact HC | intros a Ha; split; [left; lia| lia]]. }
          apply KEEP in FRA; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in FRD; [|lia|cbn [cells_size csize Nat.add]; lia].
          apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia].
          apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in MG4; [|lia|rewrite cells_size_map_C1, GL; lia].
          assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3).
          { eapply agrees_on_trans; [exact AG2|]. eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] [Hn1 Hn2]]; (split; [|exact Hn1]); [left; lia| right; exact Ha]. }
          hide HEB3. hide CELLS. unfold implM. iprefix. step. if_cases Kp; [ try (zify_cond Kp; exfalso; lia) | idtac ]. unhide HEB3. unhide CELLS.
          apply evt_done. eapply (chk_fill HO K sites HFL SFL HPL MALLOC FREE);
            [exact CTX | exact MI3 | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact Z2 | exact Z3
            | exact MI3' | exact ST3 | exact AG03 | exact G3 | exact CELLS | exact FRA | exact FRD | exact FRS | exact ERRc | exact MG4 | exact HEB3 | congruence].
      - (* [comment removed for export] *)
        replace ((l2 + 256 * (l3 mod 4)) * 65536 =? 0) with false by (symmetry; apply Z.eqb_neq; exact RZ). cbn [negb].
        step. if_cases Kr; [ try (zify_cond Kr; exfalso; lia) | idtac ].
        assert (MSG : fmt_at m2 0x10a25 "savefile linktype reserved field not zero (0x%08x)"%string).
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m2 0x10a25 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "savefile linktype reserved field not zero (0x%08x)"%string) ++ [Z_to_bv 8 0])
                                   MI2 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        do 5 step. unhide HEB2. unhide MG4. unhide ERRc.
        apply evt_done. unfold Msg.reserved_not_zero, PCAP_ERRBUF_SIZE.
        eapply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [AInt ((l2 + 256 * (l3 mod 4)) * 65536)]); [right; reflexivity | exact MSG | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints1].
        { cbn [length firstn]. constructor; [reflexivity| constructor]. }
        pose proof (snprintf_length 256 "savefile linktype reserved field not zero (0x%08x)"%string [AInt ((l2 + 256 * (l3 mod 4)) * 65536)]) as LS.
        change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS. }
    (* [comment removed for export] *)
    hide HEB2. hide MG4. hide ERRc. unfold chk_rest2. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims].
    unfold implM. iprefix. step. rewrite (zx16_lit maj) by lia. step. rewrite (zx16_lit min) by lia. step.
    destruct (Z.eq_dec maj 2) as [M2|M2].
    - replace (maj =? 2) with true by (symmetry; apply Z.eqb_eq; lia). replace (maj =? 543) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb].
      step. if_cases K1; [ try (zify_cond K1; exfalso; lia) | idtac ]. step.
      destruct (Z.le_gt_cases min 4) as [M4|M4].
      + replace (min <=? 4) with true by (symmetry; apply Z.leb_le; lia). cbn [negb].
        step. if_cases K2'; try (zify_cond K2'; exfalso; lia).
        apply evt_done. apply KOK.
      + replace (min <=? 4) with false by (symmetry; apply Z.leb_gt; lia). cbn [negb].
        step. if_cases K2'; try (zify_cond K2'; exfalso; lia). step. step. if_cases K3; [ idtac | try (zify_cond K3; exfalso; lia) ].
        apply evt_done. apply KVER.
    - replace (maj =? 2) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb].
      step. if_cases K1; [ idtac | try (zify_cond K1; exfalso; lia) ]. step.
      destruct (Z.eq_dec maj 543) as [M5|M5].
      + replace (maj =? 543) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb].
        step. if_cases K3; [ try (zify_cond K3; exfalso; lia) | idtac ].
        destruct (Z.eq_dec min 0) as [M0|M0].
        * replace (min =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
          step. if_cases K4; [ try (zify_cond K4; exfalso; lia) | idtac ].
          apply evt_done. apply KOK.
        * replace (min =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
          step. if_cases K4; [ idtac | try (zify_cond K4; exfalso; lia) ].
          apply evt_done. apply KVER.
      + replace (maj =? 543) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb].
        step. if_cases K3; [ idtac | try (zify_cond K3; exfalso; lia) ].
        apply evt_done. apply KVER.
  Qed.
  End Sz1.
  Lemma chk_hdr : ltac:(let t := eval cbv delta [chk_hdr__stmt] in chk_hdr__stmt in exact t).
  Proof using FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x5 x6 x8 m2 ps2 maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw mid junk8 e2. ltac2:(SecDiet.SzSec.closeP 'chk_hdr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Chk.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcap_chkF.
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
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section Chk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis OPEN_COMMON : open_offline_common_stmt HO K sites.
  Hypothesis MALLOC : malloc_stmt_o HO K.
  Hypothesis FREE : free_stmt_o HO K.

  (* [comment removed for export] *)
  Definition chk_hdr__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PState H hptr) (CL FB : list cblock) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x3 x4 x7 : word) (m2 : mem) (ps2 : PState H hptr)
           (maj min n0 n1 n2 n3 l0 l1 l2 l3 mi : Z) (sw : bool) (mid e2 : list byte),
      chk_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) ->
      (0 <= maj < 2^16)%Z -> (0 <= min < 2^16)%Z ->
      (0 <= n0 < 256)%Z -> (0 <= n1 < 256)%Z -> (0 <= n2 < 256)%Z -> (0 <= n3 < 256)%Z ->
      (0 <= l0 < 256)%Z -> (0 <= l1 < 256)%Z -> (0 <= l2 < 256)%Z -> (0 <= l3 < 256)%Z ->
      mem_inv usegs m2 -> stk usegs m2 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m2 ->
      GIo K R ps2 CL FB m2 ->
      rw_cells usegs m2 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ->
      rw_cells usegs m2 (bv_unsigned sp + -92)
        [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))] ->
      rw_cells usegs m2 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m2 ERR [C4 z64] -> rw_cells usegs m2 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m2 EB [CB 256 e2] ->
      ps_outfile ps2 = ps_outfile s ->
      implM usegs (chk_rest2 MOps (prims HO fo_nop sites) f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)) ps2
        (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0 a1 a2 a3 a4 a5 a6 a7
                 z64 x3 x4 (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (Z.b2z sw)) x7
                 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15654) fc None m2 (seg_rom usegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x3 x4 x7 m2 ps2 maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw mid e2 : ltac2:(SecDiet.SzSec.tyM 'chk_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_hdr__body : ltac2:(SecDiet.SzSec.bodyP 'chk_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF. pin_using (fun (FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF : unit) => tt).
 intros CTX MI3 Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 MI2 ST2 AG2 G2 FRA FRD FRS ERRc MG4 HEB2 OFX.
    pose proof CTX as CTX'. destruct CTX' as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    assert (MIB : (2^31 <= mi < 2^32)%Z) by (unfold TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in MI3; lia).
    pose proof (rw_cells_bound _ _ _ _ HEB2) as BEB. cbn [cells_size csize Nat.add] in BEB.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    set (POSTQ := check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
    assert (FRSZ : cells_size ([C4 (Z_to_bv 64 (mi + (2^64 - 2^32)))] ++
                               [C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3))]) = 24%nat) by reflexivity.
    (* [comment removed for export] *)
    assert (KSNP : forall (ra5 t0' t1' t2' a3' a4' a5' a6' a7' s3' s4' s7' t3' t4' t5' t6' : word) (FMTA : Z) (fs : string) (args : list farg),
      (ra5 = Z_to_bv 64 0x157b4 \/ ra5 = Z_to_bv 64 0x1569c) ->
      fmt_at m2 FMTA fs -> fmt_ok fs args = true -> (length args <= 2)%nat -> Forall2 (farg_word R CL (bv_unsigned sp + -96) EB 256 m2) args (firstn (length args) [a3'; a4']) ->
      (length (Fmt.snprintf 256 fs args) <= 255)%nat -> items_okb (fmt fs) = true -> Forall arg_ok args ->
      implM usegs (mret (CH_Err (Fmt.snprintf 256 fs args))) ps2 POSTQ
        (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 z64 s3' s4' (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (Z.b2z sw)) s7'
                 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m2 (seg_rom usegs))).
    { intros ra5 t0' t1' t2' a3' a4' a5' a6' a7' s3' s4' s7' t3' t4' t5' t6' FMTA fs args Hra FMT5 FOK LA FW LEN IOK AOK.
      apply (implM_ret usegs). name_sp sp (-96)%Z.
      eapply evt_cut.
      { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps2 CL FB lo EB 256%Z FMTA fs args e2);
          [| reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | exact (Nat.le_le_succ_r _ _ LA) | rewrite Hsp; replace (firstn (length args) [a3'; a4'; a5']) with (firstn (length args) [a3'; a4']) by (clear -LA; destruct args as [|? [|? [|? ?]]]; cbn in LA |- *; fastfirst (first [ noevar_assumption |reflexivity | lia])); exact FW | exact HEB2 | right; rewrite Hsp; lia].
        split; [exact G2|]. split; [rewrite Hsp; exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI2|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      cbv beta. intros ms' PO. destruct PO as (av & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -96 - STDIO_STACK, bv_unsigned sp + -96); (EB, EB + 256)]%Z a) m2 m6)
        by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      unfold STDIO_STACK in AGS.
      assert (KEEP : forall A cs, rw_cells usegs m2 A cs -> (bv_unsigned sp + -96 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= EB \/ EB + 256 <= A)%Z -> rw_cells usegs m6 A cs).
      { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AGS | exact HC | intros a Ha; cbn [outside]; lia]. }
      pose proof (rw_cells_uncut _ _ _ _ _ FRA FRD ltac:(cbn; lia)) as HC32.
      apply KEEP in HC32; [|lia|rewrite FRSZ; lia]. apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia].
      apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in MG4; [|lia|rewrite cells_size_map_C1, GL; lia].
      assert (G6 : GIo K R ps2 CL FB m6).
      { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU6 | exact WM6 |].
        apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, STDIO_STACK; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (AG6 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
      { eapply agrees_on_trans; [exact AG2|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|].
        pose proof (CLB a Ha). unfold rc_lo in LO. lia. }
      change (Z.to_nat 256) with 256%nat in HEB6.
      replace (256 - length (Fmt.snprintf 256 fs args) - 1)%nat with (255 - length (Fmt.snprintf 256 fs args))%nat in HEB6 by lia.
      destruct Hra as [-> | ->].
      - replace (ret_pc (Z_to_bv 64 87988)) with (Z_to_bv 64 87988) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        eapply (chk_fail K sites HFL SFL); [exact CTX | exact MI6 | exact ST6 | exact AG6 | exact G6 | exact HC32 | exact FRSZ | exact FRS | exact ERRc | exact MG4 | exact HEB6 | lia | apply snprintf_ok; [exact IOK| exact AOK] | congruence].
      - replace (ret_pc (Z_to_bv 64 87708)) with (Z_to_bv 64 87708) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        hide HEB6. step. unhide HEB6.
        eapply (chk_fail K sites HFL SFL); [exact CTX | exact MI6 | exact ST6 | exact AG6 | exact G6 | exact HC32 | exact FRSZ | exact FRS | exact ERRc | exact MG4 | exact HEB6 | lia | apply snprintf_ok; [exact IOK| exact AOK] | congruence]. }
    (* [comment removed for export] *)
    assert (KVER : forall (a0' : word),
      implM usegs (mret (CH_Err (Msg.unsupported_pcap_version maj min))) ps2 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1 a2 a3 a4 a5 a6 a7
                 z64 (Z_to_bv 64 min) (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (Z.b2z sw)) x7
                 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15798) fc None m2 (seg_rom usegs))).
    { intros a0'. hide HEB2. hide MG4. hide ERRc.
      assert (MSG : fmt_at m2 0x10565 "unsupported pcap savefile version %u.%u"%string).
      { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m2 0x10565 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "unsupported pcap savefile version %u.%u"%string) ++ [Z_to_bv 8 0])
                                 MI2 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
      unfold implM. iprefix. do 7 step. unhide HEB2. unhide MG4. unhide ERRc.
      apply evt_done. unfold Msg.unsupported_pcap_version, PCAP_ERRBUF_SIZE.
      eapply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [AInt maj; AInt min]); [left; reflexivity | exact MSG | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
      { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
      pose proof (snprintf_length 256 "unsupported pcap savefile version %u.%u"%string [AInt maj; AInt min]) as LS. change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS. }
    (* [comment removed for export] *)
    assert (KOK : forall (a0' : word),
      implM usegs (if negb (Z.land (le4val l0 l1 l2 l3) 67043328 =? 0)
                   then mret (CH_Err (Msg.reserved_not_zero (Z.land (le4val l0 l1 l2 l3) 67043328)))
                   else mbind (pcapint_open_offline_common MOps (prims HO fo_nop sites) PCAP_SF_TOTAL)
                          (fun r => match r with
                                    | inl m => mret (CH_Err m)
                                    | inr self => chk_fill_model MOps (prims HO fo_nop sites) self f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)
                                    end)) ps2 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1 a2 a3 a4 a5 a6 a7
                 z64 (Z_to_bv 64 min) (Z_to_bv 64 maj) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (Z.b2z sw)) x7
                 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15678) fc None m2 (seg_rom usegs))).
    { intros a0'. rewrite (reserved_val l0 l1 l2 l3) by lia.
      hide HEB2. hide MG4. hide ERRc.
      unfold implM. iprefix. step. rewrite (sx32_lit l0 l1 l2 l3) by lia. do 2 step.
      rewrite (reserved_word l0 l1 l2 l3) by lia.
      destruct (Z.eq_dec ((l2 + 256 * (l3 mod 4)) * 65536) 0) as [RZ|RZ].
      - (* [comment removed for export] *)
        replace ((l2 + 256 * (l3 mod 4)) * 65536 =? 0) with true by (symmetry; apply Z.eqb_eq; exact RZ). cbn [negb].
        assert (Z2 : l2 = 0%Z) by lia. assert (Z3 : (l3 mod 4 = 0)%Z) by lia.
        step. if_cases Kr; [ idtac | try (zify_cond Kr; exfalso; lia) ].
        do 4 step. unhide HEB2. unhide MG4. unhide ERRc.
        name_sp sp (-96)%Z.
        apply evt_done. eapply (implM_bind usegs).
        { eapply OPEN_COMMON; [| reflexivity | reflexivity | reflexivity | left; reflexivity | exact HEB2 | | exact E8 ].
          { split; [exact G2|]. split; [rewrite Hsp; exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1B_STACK; rewrite Hsp; lia|].
            split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
          right; rewrite Hsp; lia. }
        intros [msg|q] ps3 ms3 PO; cbv beta iota in PO.
        + (* [comment removed for export] *)
          destruct PO as (av & m3 & E & OF3 & MI3' & ST3 & AG3 & (junk3 & -> & G3 & HEB3 & LEN3 & RNG3)).
          unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
          replace (ret_pc (Z_to_bv 64 87816)) with (Z_to_bv 64 87816) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
          assert (KEEP : forall A cs, rw_cells usegs m2 A cs -> (bv_unsigned sp + -96 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= EB \/ EB + 256 <= A)%Z -> rw_cells usegs m3 A cs).
          { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG3 | exact HC | intros a Ha; split; [left; lia| lia]]. }
          pose proof (rw_cells_uncut _ _ _ _ _ FRA FRD ltac:(cbn; lia)) as HC32.
          apply KEEP in HC32; [|lia|rewrite FRSZ; lia]. apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia].
          apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in MG4; [|lia|rewrite cells_size_map_C1, GL; lia].
          assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3).
          { eapply agrees_on_trans; [exact AG2|]. eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] [Hn1 Hn2]]; (split; [|exact Hn1]); [left; lia| right; exact Ha]. }
          apply (implM_ret usegs). hide HEB3. step. if_true. unhide HEB3.
          eapply (chk_fail0 K sites HFL SFL); [exact CTX | exact MI3' | exact ST3 | exact AG03 | exact G3 | exact HC32 | exact FRSZ | exact FRS | exact ERRc | exact MG4 | exact HEB3 | exact LEN3 | exact RNG3 | congruence].
        + (* [comment removed for export] *)
          destruct PO as (av & m3 & E & OF3 & MI3' & ST3 & AG3 & (P & -> & G3 & CELLS & HEB3)).
          unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
          replace (ret_pc (Z_to_bv 64 87816)) with (Z_to_bv 64 87816) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
          pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (P1 & _ & _ & P4 & _). cbn [cb_addr cb_size fst snd] in P1, P4. unfold PCAP_SF_TOTAL in P4.
          assert (KEEP : forall A cs, rw_cells usegs m2 A cs -> (bv_unsigned sp + -96 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= EB \/ EB + 256 <= A)%Z -> rw_cells usegs m3 A cs).
          { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG3 | exact HC | intros a Ha; split; [left; lia| lia]]. }
          apply KEEP in FRA; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in FRD; [|lia|cbn [cells_size csize Nat.add]; lia].
          apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia].
          apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in MG4; [|lia|rewrite cells_size_map_C1, GL; lia].
          assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3).
          { eapply agrees_on_trans; [exact AG2|]. eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] [Hn1 Hn2]]; (split; [|exact Hn1]); [left; lia| right; exact Ha]. }
          hide HEB3. hide CELLS. unfold implM. iprefix. step. if_cases Kp; [ try (zify_cond Kp; exfalso; lia) | idtac ]. unhide HEB3. unhide CELLS.
          apply evt_done. eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcap_chkF.chk_fill HO K sites HFL SFL HPL MALLOC FREE);
            [exact CTX | exact MI3 | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact Z2 | exact Z3
            | exact MI3' | exact ST3 | exact AG03 | exact G3 | exact CELLS | exact FRA | exact FRD | exact FRS | exact ERRc | exact MG4 | exact HEB3 | congruence].
      - (* [comment removed for export] *)
        replace ((l2 + 256 * (l3 mod 4)) * 65536 =? 0) with false by (symmetry; apply Z.eqb_neq; exact RZ). cbn [negb].
        step. if_cases Kr; [ try (zify_cond Kr; exfalso; lia) | idtac ].
        assert (MSG : fmt_at m2 0x10a25 "savefile linktype reserved field not zero (0x%08x)"%string).
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m2 0x10a25 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "savefile linktype reserved field not zero (0x%08x)"%string) ++ [Z_to_bv 8 0])
                                   MI2 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        do 5 step. unhide HEB2. unhide MG4. unhide ERRc.
        apply evt_done. unfold Msg.reserved_not_zero, PCAP_ERRBUF_SIZE.
        eapply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [AInt ((l2 + 256 * (l3 mod 4)) * 65536)]); [right; reflexivity | exact MSG | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints1].
        { cbn [length firstn]. constructor; [reflexivity| constructor]. }
        pose proof (snprintf_length 256 "savefile linktype reserved field not zero (0x%08x)"%string [AInt ((l2 + 256 * (l3 mod 4)) * 65536)]) as LS.
        change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS. }
    (* [comment removed for export] *)
    hide HEB2. hide MG4. hide ERRc. unfold chk_rest2. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims].
    unfold implM. iprefix. step. rewrite (zx16_lit maj) by lia. step. rewrite (zx16_lit min) by lia. step.
    destruct (Z.eq_dec maj 2) as [M2|M2].
    - replace (maj =? 2) with true by (symmetry; apply Z.eqb_eq; lia). replace (maj =? 543) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb].
      step. if_cases K1; [ try (zify_cond K1; exfalso; lia) | idtac ]. step.
      destruct (Z.le_gt_cases min 4) as [M4|M4].
      + replace (min <=? 4) with true by (symmetry; apply Z.leb_le; lia). cbn [negb].
        step. if_cases K2'; try (zify_cond K2'; exfalso; lia).
        apply evt_done. apply KOK.
      + replace (min <=? 4) with false by (symmetry; apply Z.leb_gt; lia). cbn [negb].
        step. if_cases K2'; try (zify_cond K2'; exfalso; lia). step. step. if_cases K3; [ idtac | try (zify_cond K3; exfalso; lia) ].
        apply evt_done. apply KVER.
    - replace (maj =? 2) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb].
      step. if_cases K1; [ idtac | try (zify_cond K1; exfalso; lia) ]. step.
      destruct (Z.eq_dec maj 543) as [M5|M5].
      + replace (maj =? 543) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb].
        step. if_cases K3; [ try (zify_cond K3; exfalso; lia) | idtac ].
        destruct (Z.eq_dec min 0) as [M0|M0].
        * replace (min =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
          step. if_cases K4; [ try (zify_cond K4; exfalso; lia) | idtac ].
          apply evt_done. apply KOK.
        * replace (min =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
          step. if_cases K4; [ idtac | try (zify_cond K4; exfalso; lia) ].
          apply evt_done. apply KVER.
      + replace (maj =? 543) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb].
        step. if_cases K3; [ idtac | try (zify_cond K3; exfalso; lia) ].
        apply evt_done. apply KVER.
  Qed.
  End Sz1.
  Lemma chk_hdr : ltac:(let t := eval cbv delta [chk_hdr__stmt] in chk_hdr__stmt in exact t).
  Proof using FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x3 x4 x7 m2 ps2 maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw mid e2. ltac2:(SecDiet.SzSec.closeP 'chk_hdr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Chk.

End WithCeil.
End TwB.
End F_sfpcap_chkB.

(* [comment removed for export] *)
Module F_sfpcap_chk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcap_swap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcap_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_chkB.
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
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section Chk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis OPEN_COMMON : open_offline_common_stmt HO K sites.
  Hypothesis MALLOC : malloc_stmt_o HO K.
  Hypothesis FREE : free_stmt_o HO K.

  (* [comment removed for export] *)
  Definition chk_tail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x6 x8 : word)
           (m m1 : mem) (R : rctx) (s : PState H hptr) (CL FB : list cblock) (lo MG FA EB ERR : Z) (f : hptr)
           (magic : list Z) (ej junk : list byte) (W mi : Z) (sw : bool),
      GIo K R s CL FB m -> (usp0 R - 8388608 <= lo)%Z -> (lo + 81920 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= rc_spmain R)%Z ->
      tp = rc_tp R -> (bv_unsigned sp mod 16 = 0)%Z ->
      In (f, FA, FILE_BLOCK) FB -> sites = sites_at (bv_unsigned sp + D_CHECK_HEADER) ->
      length magic = 4%nat -> Forall (fun z => 0 <= z < 256)%Z magic ->
      (bv_unsigned sp <= ERR)%Z -> (ERR + 4 <= MG)%Z -> (MG + 4 <= rc_spmain R)%Z ->
      (bv_unsigned sp <= EB)%Z -> (EB + 256 <= rc_spmain R)%Z -> (EB + 256 <= ERR \/ MG + 4 <= EB)%Z -> (EB mod 8 = 0)%Z ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) -> (0 <= W < 2^64)%Z ->
      (if sw then W <> 18446744072127431636 /\ W <> 18446744072127434036 /\ W <> 18446744072127396941 else W = mi + (2^64 - 2^32))%Z ->
      mem_inv ssegs m1 -> stk ssegs m1 lo (bv_unsigned sp + -112) ->
      munch [(bv_unsigned sp + -112, bv_unsigned sp); (ERR, ERR + 4)]%Z m m1 -> wmono ssegs m m1 ->
      rw_cells ssegs m1 (bv_unsigned sp + -112) [CB 32 junk; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m1 ERR [C4 z64] -> rw_cells ssegs m1 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m EB [CB 256 ej] ->
      implM ssegs (chk_rest MOps (prims HO fo_nop sites) f 0 mi sw) s
        (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0 a1 a2 a3 a4 a5 a6 a7
                 z64 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 FA) (Z_to_bv 64 W) x6 (Z_to_bv 64 (mi + (2^64 - 2^32))) x8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x15058) fc None m1 (seg_rom ssegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x6 x8 m m1 R s CL FB lo MG FA EB ERR f magic ej junk W mi sw : ltac2:(SecDiet.SzSec.tyM 'chk_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_tail__body : ltac2:(SecDiet.SzSec.bodyP 'chk_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FERROR FMT FREAD FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF. pin_using (fun (FERROR FMT FREAD FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF : unit) => tt).
    intros G LO BU SPM TP ALN HinF SITES GL GR R1 R2 R3 E1 E2 D1 E8 MI3 WR SW5 MI1 ST MU WM FR ERRc MG4 HEB.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & A5 & _).
    cbn [cb_addr cb_size fst snd] in A1, A4, A5. unfold FILE_BLOCK in A4, A5.
    assert (MIB : (2^31 <= mi < 2^32)%Z) by (unfold TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in MI3; lia).
    (* [comment removed for export] *)
    assert (G1 : GIo K R s CL FB m1).
    { eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    assert (AG1 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m1).
    { eapply agrees_on_of_munch; [exact MU | exact WM |]. intros a _ [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|].
      destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. unfold rc_lo in *. lia. }
    assert (HEB1 : rw_cells ssegs m1 EB [CB 256 ej]).
    { eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB |].
      intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia. }
    clear MU WM HEB.
    unfold chk_rest. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_malloc e_calloc e_free e_last_errno prims read_fail_msg errmsg_for_errno].
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m1) as MU. pose proof (wmono_refl ssegs m1) as WM.
    ienter. do 2 step.
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 2 FR) as [FRA FR']. clear FR. cbn [firstn skipn cells_size csize Nat.add] in FRA, FR'.
    destruct (rw_cells_cut _ _ _ 1 FR') as [FRD FRS]. clear FR'. cbn [firstn skipn cells_size csize Nat.add] in FRD, FRS.
    replace (bv_unsigned sp + -112 + Z.of_nat 12 + Z.of_nat 20)%Z with (bv_unsigned sp + -80)%Z in FRS by lia.
    replace (bv_unsigned sp + -112 + Z.of_nat 12)%Z with (bv_unsigned sp + -100)%Z in FRD by lia.
    do 5 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G1' : GIo K R s CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G1 | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AG1' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
        by (eapply agrees_on_trans; [exact AG1|]; eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|];
            destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; unfold rc_lo in *; lia)
    end.
    clear G1 AG1 MU WM. rename G1' into G1. rename AG1' into AG1.
    (* [comment removed for export] *)
    name_sp sp (-112)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop].
      replace (sites SitePcapHdrRest + 0)%Z with (bv_unsigned sp + -100)%Z by (rewrite SITES; unfold sites_at, D_CHECK_HEADER; lia).
      eapply FREAD; [ split; [exact G1|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact FRD | right; rewrite Hsp; lia]. }
    intros got s' ms' PO. cbv beta in PO.
    destruct PO as (av & m2 & junk' & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & GOTL & GOTR & HD2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 86132)) with (Z_to_bv 64 86132) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch type of AG2 with agrees_on _ ?ma _ =>
    assert (KEEP : forall A cs, rw_cells ssegs ma A cs -> (bv_unsigned sp + -112 <= A)%Z ->
                   (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -100 \/ bv_unsigned sp + -80 <= A)%Z -> rw_cells ssegs m2 A cs)
      by (intros A cs HC HA HB; eapply agrees_rw_cells; [exact AG2 | exact HC | intros a Ha; split; [left; lia| lia]]) end.
    apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in FRA; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KEEP in MG4; [|lia|rewrite cells_size_map_C1, GL; lia].
    apply KEEP in HEB1; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear KEEP.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. lia. }
    assert (AG02 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m2).
    { eapply agrees_on_trans; [exact AG1|]. eapply agrees_on_weaken; [exact AG2|].
      intros a [[Ha|Ha] [Hn1 Hn2]]; [split; [left; lia| lia]|]. pose proof (CLB a Ha). unfold rc_lo in LO. split; [right; exact Ha| lia]. }
    clear AG1 AG2 FRD.
    pose proof (GIo_tls K _ _ _ _ _ G2) as [_ TB]. unfold tls_block_ok in TB.
    (* [comment removed for export] *)
    assert (FAILK : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s5' s6' s7' s8' t3' t4' t5' t6' : word) (m3 : mem) (ps3 : PState H hptr)
                           (msg : list Z) (junk3 : list byte) (ew : word) (hc : list cell),
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
                 s2' s3' (Z_to_bv 64 FA) s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15264) fc None m3 (seg_rom ssegs))).
    { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s5' s6' s7' s8' t3' t4' t5' t6' m3 ps3 msg junk3 ew hc MIx ST3 AG3 G3 FA3 Hhc FRS3 ERR3 MG3 HEB3 LEN3 RNG3 OFX.
      clear FRS FRA ERRc MG4 HEB1 HD2 MI1 ST MI2 ST2 G2 AG02 G1.
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
      exists junk3. split; [reflexivity|]. split; [reflexivity|]. split; [exact G'|]. split; [exact HEB'|]. split; [exact LEN3| exact RNG3]. }
    unfold zlength in *.
    assert (U64 : (usp0 R < 2^64)%Z) by (unfold usp0; pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as X; unfold bv_modulus in X; cbn in X; lia).
    pose proof (rw_cells_bound _ _ _ _ HEB1) as BEB. cbn [cells_size csize Nat.add] in BEB.
    destruct (Z.eq_dec (Z.of_nat (length got)) 20) as [L20|L20].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) L20). cbn [negb].
      apply (implM_bind_assoc ssegs).
      assert (HC32 : exists hc, rw_cells ssegs m2 (bv_unsigned sp + -112) hc /\ cells_size hc = 32%nat).
      { exists ([CB 8 (firstn 8 junk); C4 (Z_to_bv 64 (mi + (2 ^ 64 - 2 ^ 32)))] ++ [CB (length got) (map b8 got); CB (Z.to_nat 20 - length got) junk']).
        split; [eapply rw_cells_uncut; [exact FRA | exact HD2 | cbn; lia]| cbn [cells_size csize Nat.add app]; lia]. }
      destruct HC32 as (hc & FA2 & Hhc). clear FRA HD2. hide HEB1. hide MG4.
      ienter. step. rewrite (eqb_lits_false (Z.of_nat (length got)) 20) by lia. cbn [negb]. cbv iota. do 3 step.
      name_sp sp (-112)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G2|]. split; [rewrite Hsp; exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [|] ps3 ms3 PO; cbv beta in PO; destruct PO as (av3 & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO);
        unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hsp in *; unname_sp;
        replace (ret_pc (Z_to_bv 64 86396)) with (Z_to_bv 64 86396) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
        (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FRS; [|lia]); (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FA2; [|lia]);
        (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in ERRc; [|lia]); (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in MG4; [|lia]);
        (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in HEB1; [|lia]);
        (assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3)
          by (eapply agrees_on_trans; [exact AG02|]; eapply agrees_on_weaken; [exact AG3|]; intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]));
        clear MI2 AG3.
      + (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
        unfold utp in EN2. rewrite <- TP in EN2.
        eapply implM_pure; [reflexivity|]. cbn [fst snd].
        set (e := lc_errno (ps_libc s')) in *.
        cbn [Z.b2z]. step. if_false. do 10 step.
        replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
        assert (MSG : fmt_at m3 0x108d6 "error reading dump file"%string).
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m3 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        name_sp sp (-112)%Z.
        eapply evt_cut.
        { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 0x108d6%Z e "error reading dump file"%string [] ej);
            [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB1
             | right; rewrite Hsp; lia | exact E8 ].
          split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
        cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & junk4 & -> & MI4 & ST4 & AG4 & G4 & HEB4).
        rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 86428)) with (Z_to_bv 64 86428) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (KEEP4 : forall A cs, rw_cells ssegs m3 A cs -> (bv_unsigned sp + -112 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells ssegs m4 A cs).
        { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG4 | exact HC | intros a Ha; split; [left; lia| lia]]. }
        apply KEEP4 in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP4 in FA2; [|lia|rewrite Hhc; lia]. clear KEEP4.
        assert (ERR4 : rw_cells ssegs m4 ERR [C4 z64]) by (eapply agrees_rw_cells; [exact AG4 | exact ERRc | intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]]).
        assert (MG5 : rw_cells ssegs m4 MG (map (fun z => C1 (Z_to_bv 8 z)) magic))
          by (eapply agrees_rw_cells; [exact AG4 | exact MG4 | intros a Ha; rewrite cells_size_map_C1, GL in Ha; split; [left; lia| lia]]).
        hide HEB4. step. unhide HEB4.
        eapply FAILK; [assumption | assumption | | exact G4 | exact FA2 | exact Hhc | exact FRS | exact ERR4 | exact MG5 | exact HEB4
                      | pose proof (fmt_errmsg_length "error reading dump file"%string [] e); lia
                      | apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor] | congruence].
        eapply agrees_on_trans; [exact AG03|]. eapply agrees_on_weaken; [exact AG4|]. intros a [[Ha|Ha] [Hn _]]; (split; [|exact Hn]); [left; lia| right; exact Ha].
      + (* [comment removed for export] *)
        eapply implM_pure; [reflexivity|]. cbn [fst snd].
        cbn [Z.b2z]. step. if_true. do 8 step.
        assert (MSG : fmt_at m3 0x1050c "truncated dump file; tried to read %zu file header bytes, only got %zu"%string).
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m3 0x1050c (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %zu file header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                   MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        name_sp sp (-112)%Z.
        eapply evt_cut.
        { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 256%Z 0x1050c%Z
                    "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 24; AInt (Z.of_nat (length got))] ej);
            [| reflexivity | reflexivity | reflexivity | lia | exact MSG | vm_compute; reflexivity | cbn; lia | | exact HEB1 | right; rewrite Hsp; lia].
          { split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
            split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
          cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
        cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
        unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 86628)) with (Z_to_bv 64 86628) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -112 - STDIO_STACK, bv_unsigned sp + -112); (EB, EB + 256)]%Z a) m3 m4)
          by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
        unfold STDIO_STACK in AGS.
        assert (KEEP4 : forall A cs, rw_cells ssegs m3 A cs -> (bv_unsigned sp + -112 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells ssegs m4 A cs).
        { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AGS | exact HC | intros a Ha; cbn [outside]; lia]. }
        apply KEEP4 in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP4 in FA2; [|lia|rewrite Hhc; lia]. clear KEEP4.
        assert (ERR4 : rw_cells ssegs m4 ERR [C4 z64]) by (eapply agrees_rw_cells; [exact AGS | exact ERRc | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]).
        assert (MG5 : rw_cells ssegs m4 MG (map (fun z => C1 (Z_to_bv 8 z)) magic))
          by (eapply agrees_rw_cells; [exact AGS | exact MG4 | intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia]).
        assert (G4 : GIo K R s' CL FB m4).
        { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |].
          apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, STDIO_STACK; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
        change (Z.to_nat 256) with 256%nat in HEB4.
        replace (256 - length (Fmt.snprintf 256 "truncated dump file; tried to read %zu file header bytes, only got %zu" [AInt 24; AInt (Z.of_nat (length got))]) - 1)%nat
          with (255 - length (Fmt.snprintf 256 "truncated dump file; tried to read %zu file header bytes, only got %zu" [AInt 24; AInt (Z.of_nat (length got))]))%nat in HEB4 by lia.
        eapply FAILK; [assumption | assumption | | exact G4 | exact FA2 | exact Hhc | exact FRS | exact ERR4 | exact MG5 | exact HEB4
                      | pose proof (snprintf_length 256 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 24; AInt (Z.of_nat (length got))]) as LS;
                        change (Z.to_nat (256 - 1)) with 255%nat in LS; unfold Msg.trunc_file_header, PCAP_ERRBUF_SIZE; lia
                      | unfold Msg.trunc_file_header; apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] | congruence].
        eapply agrees_on_trans; [exact AG03|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|]. pose proof (CLB a Ha). unfold rc_lo in LO. split; [lia|]. split; [exact Hn1| exact Logic.I]. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) L20). cbn [negb].
    assert (CTX : chk_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m).
    { split; [exact G|]. repeat (split; [eassumption|]). eassumption. }
    assert (L20n : length got = 20%nat) by lia.
    destruct got as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|g8 [|g9 [|g10 [|g11 [|g12 [|g13 [|g14 [|g15 [|g16 [|g17 [|g18 [|g19 [|gx gr]]]]]]]]]]]]]]]]]]]]]; try (exfalso; cbn in L20n; lia).
    clear L20n L20 GOTL.
    pose proof GOTR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    assert (LJ : length junk' = 0%nat) by (destruct HD2 as [[WF _] _]; cbn in WF; lia).
    destruct junk' as [|jx jr]; [|discriminate LJ]. clear LJ.
    (* [comment removed for export] *)
    assert (HD5 : rw_cells ssegs m2 (bv_unsigned sp + -100)
              [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3)); CB 8 (map b8 [g4; g5; g6; g7; g8; g9; g10; g11]);
               C4 (Z_to_bv 64 (le4val g12 g13 g14 g15)); C4 (Z_to_bv 64 (le4val g16 g17 g18 g19))]).
    { eapply rw_cells_recell; [exact HD2 | cbn; repeat split; reflexivity |].
      cbn [cells_bytes cbytes]. rewrite (le2_lit g0 g1), (le2_lit g2 g3), (le4_lit g12 g13 g14 g15), (le4_lit g16 g17 g18 g19) by lia. reflexivity. }
    clear HD2.
    unfold get_le16, get_le32, zslice, zfirstn, zskipn.
    change (Z.to_nat 2) with 2%nat. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. change (Z.to_nat 12) with 12%nat. change (Z.to_nat 16) with 16%nat.
    cbn [firstn skipn].
    replace (Z.of_nat (length [g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; g12; g13; g14; g15; g16; g17; g18; g19])) with 20%Z by reflexivity.
    hide HEB1. hide MG4. hide ERRc.
    unfold implM. iprefix. step. if_false.
    destruct sw.
    - (* [comment removed for export] *)
      destruct SW5 as (W1 & W2 & W3).
      do 2 step. step. if_cases K1; [ try (zify_cond K1; exfalso; lia) | idtac ].
      do 2 step. step. if_cases K2; [ try (zify_cond K2; exfalso; lia) | idtac ].
      do 2 step. step. if_cases K3; [ try (zify_cond K3; exfalso; lia) | idtac ].
      eapply evt_cut.
      { eapply swap_block; [exact MI2 | | | | | | | | | | | | | | exact HD5]; lia. }
      cbv beta. intros ms' PO. destruct PO as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m4 & -> & MU4 & WM4 & MI4 & HD4). clear HD5.
      unhide HEB1. unhide MG4. unhide ERRc.
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -100, bv_unsigned sp + -80)]%Z a) m2 m4)
        by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
      assert (KEEP : forall A cs, rw_cells ssegs m2 A cs -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -100 \/ bv_unsigned sp + -80 <= A)%Z -> rw_cells ssegs m4 A cs).
      { intros A cs HC HA. eapply agrees_rw_cells; [exact AGS | exact HC | intros a Ha; cbn [outside]; lia]. }
      apply KEEP in FRA; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP in FRS; [|cbn [cells_size csize Nat.add]; lia].
      apply KEEP in ERRc; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP in MG4; [|rewrite cells_size_map_C1, GL; lia]. apply KEEP in HEB1; [|cbn [cells_size csize Nat.add]; lia].
      assert (G4 : GIo K R s' CL FB m4).
      { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU4 | exact WM4 |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (ST4 : stk ssegs m4 lo (bv_unsigned sp + -112)).
      { eapply stk_transport_disjoint; [exact ST2 | exact MU4 | exact WM4 | cbn [disjoint_from]; unfold rc_lo in LO; lia]. }
      assert (AG04 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m4).
      { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (CLB a Ha). unfold rc_lo in LO. lia. }
      rewrite (bswap16_bytes g0 g1), (bswap16_bytes g2 g3), (bswap32_bytes g12 g13 g14 g15), (bswap32_bytes g16 g17 g18 g19) by lia.
      cbv iota. rewrite !le_of_bytes_2, !le_of_bytes_4. change (Z.b2z true) with 1%Z.
      replace (g15 + 256 * g14 + 65536 * g13 + 16777216 * g12)%Z with (le4val g15 g14 g13 g12) by reflexivity.
      replace (g19 + 256 * g18 + 65536 * g17 + 16777216 * g16)%Z with (le4val g19 g18 g17 g16) by reflexivity.
      apply evt_done. eapply (chk_hdr HO K sites HFL SFL HPL SNPRINTF OPEN_COMMON MALLOC FREE) with (sw := true);
        [exact CTX | exact MI3 | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact MI4 | exact ST4 | exact AG04 | exact G4
        | exact FRA | exact HD4 | exact FRS | exact ERRc | exact MG4 | exact HEB1 | congruence].
    - (* [comment removed for export] *)
      subst W. cbv iota. rewrite !le_of_bytes_2, !le_of_bytes_4. change (Z.b2z false) with 0%Z.
      replace (g12 + 256 * g13 + 65536 * g14 + 16777216 * g15)%Z with (le4val g12 g13 g14 g15) by reflexivity.
      replace (g16 + 256 * g17 + 65536 * g18 + 16777216 * g19)%Z with (le4val g16 g17 g18 g19) by reflexivity.
      unhide HEB1. unhide MG4. unhide ERRc.
      destruct MI3 as [-> | [-> | ->]].
      + do 2 step. step. lit_branch. do 2 step. step. lit_branch.
        apply evt_done. eapply (chk_hdr HO K sites HFL SFL HPL SNPRINTF OPEN_COMMON MALLOC FREE) with (sw := false);
          [exact CTX | left; reflexivity | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact MI2 | exact ST2 | exact AG02 | exact G2
          | exact FRA | exact HD5 | exact FRS | exact ERRc | exact MG4 | exact HEB1 | congruence].
      + do 2 step. step. lit_branch. do 2 step. step. lit_branch. do 2 step. step. lit_branch.
        apply evt_done. eapply (chk_hdr HO K sites HFL SFL HPL SNPRINTF OPEN_COMMON MALLOC FREE) with (sw := false);
          [exact CTX | right; left; reflexivity | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact MI2 | exact ST2 | exact AG02 | exact G2
          | exact FRA | exact HD5 | exact FRS | exact ERRc | exact MG4 | exact HEB1 | congruence].
      + do 2 step. step. lit_branch.
        apply evt_done. eapply (chk_hdr HO K sites HFL SFL HPL SNPRINTF OPEN_COMMON MALLOC FREE) with (sw := false);
          [exact CTX | right; right; reflexivity | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact MI2 | exact ST2 | exact AG02 | exact G2
          | exact FRA | exact HD5 | exact FRS | exact ERRc | exact MG4 | exact HEB1 | congruence].
  Qed.
  End Sz1.
  Lemma chk_tail : ltac:(let t := eval cbv delta [chk_tail__stmt] in chk_tail__stmt in exact t).
  Proof using FERROR FMT FREAD FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x6 x8 m m1 R s CL FB lo MG FA EB ERR f magic ej junk W mi sw. ltac2:(SecDiet.SzSec.closeP 'chk_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition pcap_check_header_proof__stmt : Prop := pcap_check_header_stmt HO K sites.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo MG FA EB ERR f magic ej ec fuel : ltac2:(SecDiet.SzSec.tyM 'pcap_check_header_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_check_header_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_check_header_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FERROR FMT FREAD FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF. pin_using (fun (FERROR FMT FREAD FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF : unit) => tt).
    intros PRE HinF SITES -> -> -> -> -> HMG GR GL HEB HERR Hec R1 R2 R3 E1 E2 D1 E4 E8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct magic as [|m0 [|m1 [|m2 [|m3 [|? ?]]]]]; try discriminate GL. clear GL.
    pose proof GR as GR'. apply Forall_cons_iff in GR' as [G0 GR']. apply Forall_cons_iff in GR' as [G1 GR']. apply Forall_cons_iff in GR' as [G2 GR']. apply Forall_cons_iff in GR' as [G3 _].
    cbn [map] in HMG.
    destruct (rw_cells_forget _ _ _ _ HERR) as [ej0 ERRc]. clear HERR. cbn [cells_size] in ERRc. rewrite Hec in ERRc. change (4 + 0)%nat with 4%nat in ERRc.
    unfold PCAP_CHECK_HEADER_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (ERR, ERR + 4)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    (* [comment removed for export] *)
    assert (MG4 : rw_cells ssegs m MG [C1 (b8 m0); C1 (b8 m1); C1 (b8 m2); C1 (b8 m3)]).
    { eapply rw_cells_recell; [exact HMG | cbn; repeat split; exact Logic.I | reflexivity]. }
    clear HMG. hide HEB.
    pose proof (magic_cases m0 m1 m2 m3 G0 G1 G2 G3) as CASES. cbv zeta in CASES.
    destruct CASES as [C1' | [C2' | [C3' | [C4' | [C5' | [C6' | [NM1 NM2]]]]]]].
    7:{ (* [comment removed for export] *)
      unfold pcap_check_header. rewrite NM1, NM2. cbn [negb mo_ret mo_bind MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. unfold b8 in MG4.
      pose proof (magic_none m0 m1 m2 m3 G0 G1 G2 G3 NM1 NM2) as (N1 & N2 & N3 & N4 & N5 & N6).
      pose proof (magic_sx_range m0 m1 m2 m3 G0 G1 G2 G3) as WR.
      set (W := magic_sx m0 m1 m2 m3) in *.
      apply (implM_ret ssegs).
      carve_frame 112%nat ST.
      (lazymatch goal with
    | FRx : rw_cells ssegs ?mm ?A [CB 112 ?j] |- _ =>
        apply (rw_cells_split_CB ssegs mm A [] 112 j [] [32; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end).
      do 16 step.
      do 4 step. rewrite ?zxb_lit, ?sxb_lit by lia. do 9 step. rewrite (magic_word m0 m1 m2 m3) by lia. fold W.
      step. if_cases Kblt.
      1: step; step; if_cases K1; [ try (zify_cond K1; exfalso; lia) | idtac ].
      1: do 3 step; if_cases K2; [ try (zify_cond K2; exfalso; lia) | idtac ].
      1: do 3 step; if_cases K3; [ idtac | try (zify_cond K3; exfalso; lia) ].
      2: do 3 step; if_cases K4; [ try (zify_cond K4; exfalso; lia) | idtac ].
      2: do 3 step; if_cases K5; [ try (zify_cond K5; exfalso; lia) | idtac ].
      2: do 4 step; if_cases K6; [ try (zify_cond K6; exfalso; lia) | idtac ].
      2: step.
      all: do 13 step.
      all: release_frame FR ST (bv_unsigned sp).
      all: unhide HEB.
      all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGW : agrees_on (fun a => outside [(bv_unsigned sp - 112, bv_unsigned sp); (ERR, ERR + 4)]%Z a) m mm)
          by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
        assert (HEB' : rw_cells ssegs mm EB [CB 256 ej])
          by (eapply agrees_rw_cells; [exact AGW | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia]);
        assert (G' : GIo K R s CL FB mm)
          by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |];
              apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
        assert (MG' : rw_cells ssegs mm MG [CB 4 [Z_to_bv 8 m0; Z_to_bv 8 m1; Z_to_bv 8 m2; Z_to_bv 8 m3]])
          by (eapply rw_cells_recell; [exact MG4 | cbn; repeat split; exact Logic.I | reflexivity])
      end.
      all: apply evt_done; unfold check_header_post.
      all: lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, (Z_to_bv 64 0) end.
      all: split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      all: split; [solve [assumption | congruence] |].
      all: split; [assumption|]; split; [assumption|].
      all: split; [eapply agrees_on_weaken; [exact AGW|]; intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|];
                  destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; unfold rc_lo in LO; lia |].
      all: split; [exact MG'|]. all: split; [assumption|].
      all: split; [reflexivity|]; split; [reflexivity|]; split; [exact G'| exists ej; exact HEB']. }
    (* [comment removed for export] *)
    1: destruct C1' as (-> & -> & -> & ->). 2: destruct C2' as (-> & -> & -> & ->). 3: destruct C3' as (-> & -> & -> & ->).
    4: destruct C4' as (-> & -> & -> & ->). 5: destruct C5' as (-> & -> & -> & ->). 6: destruct C6' as (-> & -> & -> & ->).
    1: rewrite (chk_live_1 MOps (prims HO fo_nop sites)). 2: rewrite (chk_live_2 MOps (prims HO fo_nop sites)). 3: rewrite (chk_live_3 MOps (prims HO fo_nop sites)).
    4: rewrite (chk_live_4 MOps (prims HO fo_nop sites)). 5: rewrite (chk_live_5 MOps (prims HO fo_nop sites)). 6: rewrite (chk_live_6 MOps (prims HO fo_nop sites)).
    all: unfold b8 in MG4; ienter; carve_frame 112%nat ST; (lazymatch goal with     | FRx : rw_cells ssegs ?mm ?A [CB 112 ?j] |- _ =>         apply (rw_cells_split_CB ssegs mm A [] 112 j [] [32; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];         cbn [app mk_CB_cells] in FRx;         repeat match type of FRx with         | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end         end     end); do 20 step; rewrite ?zxb_lit, ?sxb_lit by lia.
    all: repeat match goal with |- context [Z_to_bv 64 (?a - 256 * (?a / 128))%Z] => let v := eval vm_compute in (a - 256 * (a/128))%Z in change (a - 256 * (a / 128))%Z with v end.
    all: steps_to 86104%Z.
    all: unhide HEB. all: apply evt_done.
    6: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [161; 178; 60; 77]%Z ej _ _ NSEC_TCPDUMP_MAGIC true).
    5: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [161; 178; 205; 52]%Z ej _ _ KUZNETZOV_TCPDUMP_MAGIC true).
    4: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [161; 178; 195; 212]%Z ej _ _ TCPDUMP_MAGIC true).
    3: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [77; 60; 178; 161]%Z ej _ _ NSEC_TCPDUMP_MAGIC false).
    2: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [52; 205; 178; 161]%Z ej _ _ KUZNETZOV_TCPDUMP_MAGIC false).
    1: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [212; 195; 178; 161]%Z ej _ _ TCPDUMP_MAGIC false).
    all: try exact G; try exact HinF; try exact SITES; try exact GR; try reflexivity; try assumption; try lia.
    all: eassumption.
  Qed.
  End Sz2.
  Theorem pcap_check_header_proof : ltac:(let t := eval cbv delta [pcap_check_header_proof__stmt] in pcap_check_header_proof__stmt in exact t).
  Proof using FERROR FMT FREAD FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF. red. unfold check_header_stmt_for. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo MG FA EB ERR f magic ej ec fuel. ltac2:(SecDiet.SzSec.closeP 'pcap_check_header_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Chk.

End WithCeil.
End F_sfpcap_chk.

(* [comment removed for export] *)
Module F_sfpcap_nextB.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_nextA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcap_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_nextA.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac natfold_term t :=
  match t with
  | context C[4120%nat] => let t1 := context C[Z.to_nat 4120] in natfold_term t1
  | context C[4136%nat] => let t1 := context C[Z.to_nat 4136] in natfold_term t1
  | _ => t
  end.
Local Ltac natfold_hyp H := let T := type of H in let U := natfold_term T in change U in H.
Local Ltac natfold_concl := lazymatch goal with |- ?G => let U := natfold_term G in change U end.
Local Ltac natfold_lits :=
  repeat match goal with
  | nfH : context [4120%nat] |- _ => natfold_hyp nfH
  | nfH : context [4136%nat] |- _ => natfold_hyp nfH
  end;
  lazymatch goal with
  | |- context [4120%nat] => natfold_concl
  | |- context [4136%nat] => natfold_concl
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (Z.sub (bv_unsigned (Z_to_bv _ _)) (bv_unsigned (Z_to_bv _ _))) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
(* [comment removed for export] *)
Local Ltac merge_all_lazy H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H; cbn [app] in H
  end.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
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
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma max_snaplen_le2 : forall d, (max_snaplen_for_dlt d <= 134217728)%Z.
Proof using Type. all: natfold_lits. pin_using tt. intros d. unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN. repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) end; lia. Qed.

Lemma zfirstn_length_le2 : forall n (l : list Z), (length (zfirstn n l) <= Z.to_nat n)%nat.
Proof using Type. all: natfold_lits. pin_using tt. intros. unfold zfirstn. rewrite length_firstn. lia. Qed.

(* [comment removed for export] *)
Lemma pv_wf : forall {hptr} (self f : hptr) swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl
                     (bq : hptr) bsz alloc data eb (bq' : hptr) bsz' alloc' data' eb',
  pcap_wf (F_sfpcap_nextA.pv self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl bq bsz alloc data eb) ->
  (0 <= bsz' <= 2^30)%Z -> (0 <= alloc' < 2^32)%Z -> (Z.of_nat (length data') <= alloc')%Z -> (bsz' <= alloc')%Z ->
  pcap_wf (F_sfpcap_nextA.pv self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl bq' bsz' alloc' data' eb').
Proof using Type. all: natfold_lits. pin_using tt.
  intros until eb'. intros WF B1 B2 B3 B4. unfold pcap_wf, F_sfpcap_nextA.pv in *.
  cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
       pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv] in *.
  repeat split; try (keep_hyps vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl bsz alloc data data' WF bsz' B1 alloc' B2 B3 B4; lia); try tauto.
Qed.

Section NpCtxB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA B Af : Z) (m : mem) (o : option hptr).
  Variables (self buffer f : hptr) (bufsize bufalloc : Z) (bufdata : list Z) (swapped : bool)
            (vmaj vmin snapshot linktype ltext prec brk : Z) (errbuf : list Z) (header : pkthdr)
            (hdrsize : Z) (lsw : lenswap_t) (scl : sf_scale_t) (j : pcap_junk) (pad bs : list byte).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 664 <= CEILZ)%Z.
  Hypothesis P5 : (P + 664 <= 65536 \/ 348160 <= P)%Z.  Hypothesis P6 : (P + 664 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize < 2^32)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.
  Hypothesis WHS : (hdrsize = 16 \/ hdrsize = 24)%Z.
  Hypothesis PPLEN : forall lt sw hdr d, length (snd (pcapint_post_process lt sw hdr d)) = length d.
  Hypothesis PPSEC : forall lt sw hdr d, h_sec (fst (pcapint_post_process lt sw hdr d)) = h_sec hdr /\ h_usec (fst (pcapint_post_process lt sw hdr d)) = h_usec hdr.
  Hypothesis PPRNG : forall lt sw hdr d, (0 <= h_caplen hdr <= Z.of_nat (length d))%Z -> (0 <= h_len hdr < 2^32)%Z -> (Z.of_nat (length d) < 2^31)%Z ->
     (0 <= h_caplen (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z /\ (0 <= h_len (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (F_sfpcap_nextA.pv self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl).
  #[local] Abbreviation np_fail_tail := (F_sfpcap_nextA.np_fail_tail K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation np_ok_tail := (F_sfpcap_nextA.np_ok_tail K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation np_snp := (F_sfpcap_nextA.np_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation np_fmt := (F_sfpcap_nextA.np_fmt K FMT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P2 P4).
  #[local] Abbreviation np_finish := (F_sfpcap_nextA.np_finish K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl
                               LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P5 P6 W9 PPLEN PPSEC PPRNG).
  #[local] Abbreviation np_nread := (F_sfpcap_nextA.np_nread HO K sites HFL SFL HAL FREAD FERROR FMT SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl
                              LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 HinF P1 P2 P4 P5 P6 W1 W5 W6 W7 W8 W9 W10 WHS PPLEN PPSEC PPRNG).
  #[local] Abbreviation np_normal := (F_sfpcap_nextA.np_normal HO K sites HFL SFL HPL HAL FREAD FERROR FMT SNPRINTF REALLOC PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA B Af m o self buffer f bufsize bufalloc bufdata swapped
                               vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize lsw scl
                               LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 HinF P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10 WHS PPLEN PPSEC PPRNG).
  #[local] Abbreviation np_CLc_facts := (F_sfpcap_nextA.np_CLc_facts K R CLc FB).
  #[local] Abbreviation PCAPR_errbuf := (F_sfpcap_nextA.PCAPR_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_p :=
    unfold F_sfpcap_nextA.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells
         sf_hdrsize sf_lengths_swapped sf_scale_type ifaces_ok set_bufdata set_errbuf set_buffer] in *;
    unfold PCAP_SF_TOTAL, PCAP_PRIV_OFF in *.

  (* [comment removed for export] *)
  Lemma discard_loop_S : forall fuel fp cap btd br,
    discard_loop MOps (prims HO fo_nop sites) (S fuel) fp cap btd br =
    (if (btd =? 0)%Z then mret (inr tt) else
     got <- e_fread (prims HO fo_nop sites) fp (DStack SiteDiscardBuf 0) (if 4096 <? btd then 4096 else btd)%Z ;;
     (if negb (zlength got =? (if 4096 <? btd then 4096 else btd))%Z
      then (m0 <- read_fail_msg MOps (prims HO fo_nop sites) fp (Msg.trunc_captured_u cap (br + zlength got)) ;; mret (inl m0))
      else discard_loop MOps (prims HO fo_nop sites) fuel fp cap (btd - zlength got) (br + zlength got))).
  Proof using Type. all: natfold_lits. pin_using tt. intros. reflexivity. Qed.

  Lemma discard_loop_0 : forall fuel fp cap br, discard_loop MOps (prims HO fo_nop sites) fuel fp cap 0 br = mret (inr tt).
  Proof using Type. all: natfold_lits. pin_using tt. intros. destruct fuel; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma np_discard : forall (fuel : nat)
      (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x5 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
      (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len btd bread : Z) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> Z.of_nat (length data) = snapshot -> (0 <= len < 2^32)%Z -> (0 <= cap < 2^31)%Z ->
      (0 < btd)%Z -> (btd <= 4096 * (Z.of_nat fuel - 1))%Z -> (0 <= bread)%Z -> (bread + btd <= cap)%Z -> ps_outfile ps = o ->
      implM ssegs (r <- discard_loop MOps (prims HO fo_nop sites) fuel f cap btd bread ;;
                   match r with
                   | inl m0 => mret ((-1)%Z, mkHdr sec usec cap len, set_errbuf m0 (pv bq bsz alloc data eb))
                   | inr _ => (let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec snapshot len) data in
                               mret (1%Z, hdr, set_bufdata d (pv bq bsz alloc data eb)))
                   end) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 bread) x5 (Z_to_bv 64 btd) x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x156a4) fc None m5 (seg_rom ssegs)).
  Proof using AD AH ALN BU FERROR FMT FREAD HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SITES SNPRINTF SP47 SPM SPW TP W1 W9. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SITES SNPRINTF SP47 SPM SPW TP W1 W9 : unit) => tt).
    induction fuel as [|fuel IH]; intros until fj; intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd DRNG DLEN Hl32 Hc31 Bpos Bfuel Br0 Brc OF5.
    { exfalso. cbn [Z.of_nat] in Bfuel. lia. }
    rewrite Nat2Z.inj_succ in Bfuel.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof W1 as W1'. unfold INT_MAX in W1'.
    rewrite discard_loop_S. replace (btd =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    set (n := (if 4096 <? btd then 4096 else btd)%Z).
    assert (Hn : (0 < n <= 4096)%Z /\ (n <= btd)%Z /\ (n = btd \/ (n = 4096 /\ 4096 < btd))%Z) by (subst n; destruct (Z.ltb_spec 4096 btd); lia).
    clearbody n.
    unfold read_fail_msg, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims].
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 1 FR5) as [FJ FS]. clear FR5. cbn [firstn skipn cells_size csize] in FJ, FS.
    apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat 4136) _ [] [16; Z.to_nat n; Z.to_nat 4120 - Z.to_nat n]%nat) in FJ; [| cbn; (keep_hyps CEILV sp R lo P HA DA fuel data btd dw n Hn; lia)]. cbn [mk_CB_cells app] in FJ.
    lazymatch type of FJ with rw_cells _ _ _ [CB _ ?l0; CB _ ?l1; CB _ ?l2] =>
      set (j0 := l0) in FJ; set (j1 := l1) in FJ; set (j2 := l2) in FJ; clearbody j0 j1 j2 end.
    destruct (rw_cells_cut _ _ _ 1 FJ) as [F0 F12]. clear FJ. cbn [firstn skipn cells_size csize] in F0, F12.
    destruct (rw_cells_cut _ _ _ 1 F12) as [F1 F2]. clear F12. cbn [firstn skipn cells_size csize] in F1, F2.
    lazymatch type of F1 with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -4192)%Z in F1 by lia end.
    (* [comment removed for export] *)
    lazymatch goal with |- implM _ ?c ?st ?Q _ =>
      assert (K78 : forall (a0v s5v : word) (mx : mem), s5v = Z_to_bv 64 n -> mx = m5 ->
        implM ssegs c st Q
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0v a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 bread) s5v (Z_to_bv 64 btd) x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x156b4) fc None mx (seg_rom ssegs)))
    end.
    2:{ pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
        hide F0. hide F1. hide F2. hide FS. hide HH. hide HD.
        unfold implM. iprefix. step. step. step. if_cases Kc; zify_cond Kc.
        - apply evt_done. apply (K78 _ _ m5); [f_equal; lia| reflexivity].
        - step. apply evt_done. apply (K78 _ _ m5); [f_equal; lia| reflexivity]. }
    intros a0v s5v mx -> ->.
    hide F0. hide F2. hide FS. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. do 5 step.
    (* [comment removed for export] *)
    name_sp sp (-4208)%Z.
    apply evt_done. apply (implM_bind_assoc ssegs). eapply (implM_bind ssegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop].
      replace (sites SiteDiscardBuf + 0)%Z with (bv_unsigned sp + -4192)%Z by (rewrite SITES; unfold sites_at, D_NEXT_PACKET; lia).
      eapply FREAD; [| exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact F1 | ].
      { split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      right. rewrite Hsp. lia. }
    intros got ps6 ms6 PO. cbv beta in PO.
    destruct PO as (av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp. cbv beta.
    replace (ret_pc (Z_to_bv 64 0x156c8)) with (Z_to_bv 64 0x156c8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide F0. unhide F2. unhide FS. unhide HH. unhide HD. clear F1.
    assert (KEEP : forall A cs, rw_cells ssegs m5 A cs -> (bv_unsigned sp + -4208 <= A)%Z ->
              (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -4192 \/ bv_unsigned sp + -4192 + n <= A)%Z -> rw_cells ssegs m6 A cs)
      by (intros A cs HC HA' HB; eapply agrees_rw_cells; [exact AG6 | exact HC | intros a Ha; split; [left; lia| lia]]).
    apply KEEP in F0; [| lia | cbn [cells_size csize]; lia]. apply KEEP in F2; [| lia | lia]. apply KEEP in FS; [| (keep_hyps CEILV sp R P HA DA fuel data dw; lia) | (keep_hyps CEILV ra sp s0 s1 s2 s3 s4 s5 s6 s7 R P HA DA fuel data btd dw n Hn; lia)].
    apply KEEP in HH; [| lia | lia]. apply KEEP in HD; [| lia | lia]. clear KEEP.
    assert (PC6 : PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m6).
    { eapply PCAPR_agree; [exact AG6 | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha).
      split; [right; apply in_block_app; right; exact Ha| unfold rc_lo in LO; lia]. }
    assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [split; [left; lia| unfold rc_lo in LO; lia]|].
      destruct (np_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [right; apply in_block_app; left; exact Ha| lia]. }
    (* [comment removed for export] *)
    pose proof (rw_cells_uncut _ _ _ _ _ F0 HD6 ltac:(cbn [cells_size csize]; lia)) as FJ.
    pose proof (rw_cells_uncut _ _ _ _ _ FJ F2 ltac:(cbn [cells_size csize app]; unfold zlength in GOTL; lia)) as FJ'. clear FJ F0 F2 HD6.
    cbn [app] in FJ'. merge_all_lazy FJ'.
    lazymatch type of FJ' with rw_cells _ _ _ [CB ?k _] => replace k with (Z.to_nat 4136) in FJ' by (cbn [cells_size csize Nat.add]; unfold zlength in GOTL; (keep_hyps CEILV sp R lo P HA DA fuel data btd dw n got Hn GOTL; lia)) end.
    pose proof (rw_cells_uncut _ _ _ _ _ FJ' FS ltac:(cbn [cells_size csize]; (keep_hyps CEILV sp R P HA DA fuel data dw; lia))) as FR6. clear FJ' FS. cbn [app] in FR6.
    clear MU WM ST5 MI5 G5 PC5 AG5.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
    hide HH. hide HD.
    unfold implM. iprefix. step.
    destruct (Z.eq_dec (zlength got) n) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite LEQ. rewrite Z.eqb_refl. cbn [negb].
      step. if_cases Kq; [ try (zify_cond Kq; exfalso; (keep_hyps CEILV sp R P HA DA fuel data btd dw n Kq; lia)) | idtac ].
      step.
      destruct (Z.eq_dec btd n) as [LAST|MORE].
      + (* [comment removed for export] *)
        step. if_cases Kz; [ try (zify_cond Kz; exfalso; (keep_hyps CEILV sp R lo P HA DA fuel data btd dw n LAST Kz; lia)) | idtac ].
        replace (btd - n)%Z with 0%Z by lia. rewrite discard_loop_0. rewrite mbind_mret.
        (* [comment removed for export] *)
        pose proof PC6 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & _)).
        unfold F_sfpcap_nextA.pv, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
        assert (EBX : Bx' = Bx) by congruence. subst Bx'. clear EPB.
        unfold F_sfpcap_nextA.pv, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
        cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
             pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
        clear MU WM. pose proof (munch_refl [(HA + 16, HA + 20)]%Z m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
        hide FR6.
        step. rewrite (sx32_small snapshot) by lia. unhide HH. step. step.
        unhide FR6. unhide HD. clear CELLS.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGP : agrees_on (fun a => outside [(HA + 16, HA + 20)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; cbn [outside cells_size csize] in Ha |- *; (keep_hyps CEILV sp R lo P HA DA fuel data dw a R1 Ha; lia)].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; lia].
        assert (G7 : GIo K R ps6 (CLc ++ pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU | exact WM |].
          apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo. lia. }
        assert (PC7 : PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m7).
        { eapply PCAPR_agree; [exact AGP | | exact PC6]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G6 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
        assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. lia. }
        apply evt_done. eapply np_finish.
        all: try exact FR6; try exact HH; try exact HD; try exact Hd; try exact G7; try exact PC7; try exact AG07; try exact DRNG; try exact Hl32; try reflexivity; try (keep_hyps CEILV sp R lo P HA DA snapshot fuel data dw DLEN W1'; lia).
        all: try eassumption. all: try congruence.
      + (* [comment removed for export] *)
        step. if_cases Kz; [ idtac | try (zify_cond Kz; exfalso; (keep_hyps CEILV sp R lo P HA DA fuel data cap btd bread dw n Hc31 Br0 Brc Hn MORE Kz; lia)) ].
        unhide HH. unhide HD.
        replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 btd) - bv_unsigned (Z_to_bv 64 n))) with (Z_to_bv 64 (btd - n)) by (rewrite !unsigned_lit by lia; reflexivity).
        replace (Z_to_bv 64 (n + bread)) with (Z_to_bv 64 (bread + n)) by (f_equal; lia).
        apply evt_done. eapply IH; try eassumption; try (keep_hyps CEILV sp R P HA DA fuel data btd dw n Hn MORE lo Bfuel bread got Br0 GOTL cap Brc; lia); try congruence.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      step. if_cases Kq; [ idtac | try (zify_cond Kq; exfalso; unfold zlength in *; (keep_hyps CEILV R btd n LNE Kq; lia)) ].
      do 2 step.
      apply evt_done. apply (implM_bind_assoc ssegs). apply (implM_bind_assoc ssegs). name_sp sp (-4208)%Z. eapply (implM_bind ssegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G6|]. split; [rewrite Hsp; exact ST6|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI6|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros r ps7 ms7 PO. cbv beta in PO. destruct PO as (av7 & m7 & E & MI7 & ST7 & AG7 & G7 & -> & -> & ERRNO).
      unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms7. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x15898)) with (Z_to_bv 64 0x15898) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide HH. unhide HD.
      assert (KEEP : forall A cs, rw_cells ssegs m6 A cs -> (bv_unsigned sp + -4208 <= A)%Z -> rw_cells ssegs m7 A cs)
        by (intros A cs HC HX; eapply agrees_rw_cells; [exact AG7 | exact HC | intros a Ha; left; lia]).
      apply KEEP in FR6; [| lia]. apply KEEP in HH; [| lia]. apply KEEP in HD; [| lia]. clear KEEP.
      assert (PC7 : PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m7).
      { eapply PCAPR_agree; [exact AG7 | | exact PC6]. intros a Ha. right. apply in_block_app. right. exact Ha. }
      assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
      { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AG7|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
      clear AG7 MU WM. hide FR6. hide HD. hide HH.
      pose proof (munch_refl ([] : list (Z * Z)) m7) as MU. pose proof (wmono_refl ssegs m7) as WM.
      destruct r.
      + (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN ER]. clear ERRNO. unfold utp in EN. rewrite <- TP in EN.
        pose proof (GIo_tls K _ _ _ _ _ G7) as [_ TB]. unfold tls_block_ok, utp in TB. rewrite <- TP in TB.
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        set (e := lc_errno (ps_libc ps6)) in *.
        unfold implM. iprefix. cbn [Z.b2z]. step. step. if_false. do 4 step. step. rewrite (sx32_s32 e) by lia. do 6 step.
        unhide FR6. unhide HD. unhide HH.
        apply evt_done. eapply np_fmt; [exact ST7 | exact FR6 | exact MI7 | | lia |].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m7 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))).
      + (* [comment removed for export] *)
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        unfold implM. iprefix. cbn [Z.b2z]. step. step. if_true.
        unhide HH. step. rewrite (sx32_small cap) by lia. hide HH. do 8 step.
        unhide FR6. unhide HD. unhide HH.
        apply evt_done. unfold Msg.trunc_captured_u, PCAP_ERRBUF_SIZE.
        eapply np_snp; [exact ST7 | exact FR6 | exact MI7 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m7 0x10c8d (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %u captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                     MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        { cbn [length firstn]. constructor; [reflexivity|]. constructor; [f_equal; lia| constructor]. }
        pose proof (snprintf_length 256 "truncated dump file; tried to read %u captured bytes, only got %zu"%string [AInt cap; AInt (bread + zlength got)]) as LS.
        change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS.
  Qed.
  Lemma subw_small : forall x y, (0 <= y <= x)%Z -> (x < 2^31)%Z ->
    Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) - bv_unsigned (Z_to_bv 64 y))) = Z_to_bv 64 (x - y).
  Proof using BU CEILV LO P1 R1 R2 SPW. all: natfold_lits. pin_using (fun (BU CEILV LO P1 R1 R2 SPW : unit) => tt). intros x y Hxy Hx. rewrite !unsigned_lit by lia. f_equal. apply bv_swrap32_small. lia. Qed.

  (* [comment removed for export] *)
  Definition np_oread__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (snapshot <= bsz)%Z -> (snapshot < cap)%Z -> (cap <= max_snaplen_for_dlt linktype)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (np_oread_model MOps (prims HO fo_nop sites) f snapshot (pv bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 Bx) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 cap) (Z_to_bv 64 snapshot) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15670) fc None m5 (seg_rom ssegs)).
  Section Sz8.
  Variables ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_oread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_oread__body : ltac2:(SecDiet.SzSec.bodyP 'np_oread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SITES SNPRINTF SP47 SPM SPW TP W1 W9. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SITES SNPRINTF SP47 SPM SPW TP W1 W9 : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hsb Hsc Hcm Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    pose proof PC5 as PC5'.
    destruct PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    norm_p. unfold sf_cells in PRIV. cbn [sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    subst Ix. assert (EBX : Bx' = Bx) by congruence. subst Bx'. clear EPB.
    pose proof WF as (_ & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W2', W3, W4, WBB.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (BP' : (Bx + alloc <= P \/ P + 664 <= Bx)%Z).
    { pose proof (PB_apart K _ _ _ _ _ _ (pv bq bsz alloc data eb) P Bx 0 G5 eq_refl) as [APB _]. unfold F_sfpcap_nextA.pv, psize, is_ng in APB. cbn [pc_bufalloc pc_priv] in APB. unfold PCAP_SF_TOTAL in APB. (keep_hyps CEILV sp R P HA DA Bx alloc data dw APB; lia). }
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat alloc) _ [] [Z.to_nat snapshot; Z.to_nat alloc - Z.to_nat snapshot]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. cbn [firstn skipn cells_size csize] in BD, BT.
    unfold np_oread_model, read_fail_msg, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims pc_buffer pc_linktype pc_swapped pc_bufdata set_bufdata set_errbuf
      pc_self pc_rfile pc_bufsize pc_bufalloc pc_version_major pc_version_minor pc_snapshot pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    hide BT. hide PRIV. hide CELLS. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. rewrite (sextw_small snapshot) by lia. do 3 step.
    name_sp sp (-4208)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop]. unfold blk_addr.
      rewrite (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G5 ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity)).
      rewrite Z.add_0_r.
      eapply FREAD; [| exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact BD | ].
      { split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      left. intros a Ha. apply in_block_app. right. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    intros got ps6 ms6 PO. cbv beta in PO.
    destruct PO as (av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp. cbv beta.
    replace (ret_pc (Z_to_bv 64 0x15680)) with (Z_to_bv 64 0x15680) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide BT. unhide PRIV. unhide CELLS. unhide HH. unhide HD.
    assert (KEEP : forall A cs, rw_cells ssegs m5 A cs ->
              ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664) \/ (Bx + snapshot <= A /\ A + Z.of_nat (cells_size cs) <= Bx + alloc))%Z ->
              rw_cells ssegs m6 A cs).
    { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|[HX|HX]].
      - split; [left; lia| unfold rc_lo in LO; lia].
      - split; [| lia]. right. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
      - split; [| lia]. right. apply in_block_app. right. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
    apply KEEP in CELLS; [| right; left; cbn [cells_size csize]; lia]. apply KEEP in PRIV; [| right; left; cbn [cells_size csize]; lia].
    apply KEEP in BT; [| right; right; cbn [cells_size csize]; lia]. clear KEEP.
    assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [split; [left; lia| unfold rc_lo in LO; lia]|].
      destruct (np_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [right; apply in_block_app; left; exact Ha|].
      intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    clear AG6 MI5 ST5 PC5' AG5 MU WM.
    (* [comment removed for export] *)
    pose proof (rw_cells_uncut _ _ _ _ _ HD6 BT ltac:(cbn [cells_size csize]; unfold zlength in GOTL; lia)) as BUF6. cbn [app] in BUF6. merge_all BUF6.
    replace (length got + (Z.to_nat snapshot - length got + (Z.to_nat alloc - Z.to_nat snapshot + 0)))%nat with (Z.to_nat alloc) in BUF6 by (unfold zlength in GOTL; lia).
    rewrite app_nil_r in BUF6. clear HD6 BT.
    assert (PC6 : PCAPR (hptr:=hptr) P (pv bq bsz alloc got eb) [(self, P, 664%Z); (bq, Bx, alloc)] FB m6).
    { exists Afx. split; [exact Hin|]. exists Bx, 0%Z, jx', padx, (map b8 got ++ junk6 ++ firstn (Z.to_nat alloc - Z.to_nat snapshot) (skipn (Z.to_nat snapshot) bsx')).
      split; [reflexivity|].
      split; [unfold F_sfpcap_nextA.pv, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF;
              cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
                   pk_next_pcap pk_cleanup_sf PK pc_rfile]; exact CELLS|].
      split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [unfold F_sfpcap_nextA.pv; cbn [pc_bufalloc]; exact BUF6|].
      split; [unfold F_sfpcap_nextA.pv; cbn [pc_bufdata]; replace (length got) with (length (map b8 got)) by (apply length_map);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      eapply pv_wf; [exact WF | clear - W2'; lia | clear - W3; lia | clear - GOTL Hsb WBB; unfold zlength in GOTL; lia | clear - WBB; lia]. }
    assert (G6' : GIo K R ps6 (CLc ++ pcap_blocks (pv bq bsz alloc got eb) P Bx 0) FB m6) by exact G6.
    hide BUF6. hide PRIV. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
    unfold implM. iprefix. step. step. rewrite (zx32_lit snapshot) by lia. step. rewrite (sextw_small snapshot) by lia.
    destruct (Z.eq_dec (zlength got) snapshot) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
      step. if_cases Kq; try (zify_cond Kq; exfalso; unfold zlength in *; (keep_hyps CEILV R LEQ Kq; lia)).
      step. rewrite (sx32_small cap) by lia.
      step. if_cases Kc; try (zify_cond Kc; exfalso; (keep_hyps CEILV sp R P HA DA snapshot Bx data cap dw Hsc Kc; lia)).
      step. rewrite (subw_small cap snapshot) by lia. do 2 step. rewrite (zext32_shifts_lit (cap - snapshot)) by lia.
      unhide BUF6. unhide PRIV. unhide HD. clear CELLS.
      rewrite LEQ.
      apply evt_done. eapply (np_discard (Z.to_nat ((cap - snapshot) / 4096 + 2)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps6 bq Bx bsz alloc got eb sec usec cap len (cap - snapshot) snapshot dw);
        [exact ST6 | exact FR5 | exact MI6 | exact G6' | exact PC6 | exact AG06 | exact HH | exact HD | exact Hd | exact GOTR
        | unfold zlength in LEQ; lia | exact Hl32 | lia | lia | | lia | lia | congruence ].
      rewrite Z2Nat.id by (Z.div_mod_to_equations; (keep_hyps CEILV R snapshot data cap dw q r Hsc H0 H1; lia)). Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      step. if_cases Kq; try (zify_cond Kq; exfalso; unfold zlength in *; (keep_hyps CEILV R LNE Kq; lia)).
      do 2 step.
      apply evt_done. apply (implM_bind_assoc ssegs). name_sp sp (-4208)%Z. eapply (implM_bind ssegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G6|]. split; [rewrite Hsp; exact ST6|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI6|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros r ps7 ms7 PO. cbv beta in PO. destruct PO as (av7 & m7 & E & MI7 & ST7 & AG7 & G7 & -> & -> & ERRNO).
      unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms7. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x157f4)) with (Z_to_bv 64 0x157f4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide BUF6. unhide PRIV. unhide HD.
      assert (KEEP : forall A cs, rw_cells ssegs m6 A cs -> (bv_unsigned sp + -4208 <= A)%Z -> rw_cells ssegs m7 A cs)
        by (intros A cs HC HX; eapply agrees_rw_cells; [exact AG7 | exact HC | intros a Ha; left; lia]).
      apply KEEP in FR5; [| lia]. apply KEEP in HH; [| lia]. apply KEEP in HD; [| lia]. clear KEEP.
      assert (PC7 : PCAPR (hptr:=hptr) P (pv bq bsz alloc got eb) [(self, P, 664%Z); (bq, Bx, alloc)] FB m7).
      { eapply PCAPR_agree; [exact AG7 | | exact PC6]. intros a Ha. right. apply in_block_app. right. exact Ha. }
      assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
      { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AG7|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
      clear AG7 MU WM CELLS. hide BUF6. hide PRIV. hide HD. hide HH.
      pose proof (munch_refl ([] : list (Z * Z)) m7) as MU. pose proof (wmono_refl ssegs m7) as WM.
      destruct r.
      + (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN ER]. clear ERRNO. unfold utp in EN. rewrite <- TP in EN.
        pose proof (GIo_tls K _ _ _ _ _ G7) as [_ TB]. unfold tls_block_ok, utp in TB. rewrite <- TP in TB.
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        set (e := lc_errno (ps_libc ps6)) in *.
        unfold implM. iprefix. cbn [Z.b2z]. step. step. if_false. do 4 step. step. rewrite (sx32_s32 e) by lia. do 6 step.
        unhide BUF6. unhide PRIV. unhide HD. unhide HH.
        apply evt_done. eapply np_fmt; [exact ST7 | exact FR5 | exact MI7 | | lia |].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m7 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))).
      + (* [comment removed for export] *)
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        unfold implM. iprefix. cbn [Z.b2z]. step. step. if_true. do 9 step.
        unhide BUF6. unhide PRIV. unhide HD. unhide HH.
        apply evt_done. unfold Msg.trunc_captured_d, PCAP_ERRBUF_SIZE.
        eapply np_snp; [exact ST7 | exact FR5 | exact MI7 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m7 0x1058d (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %d captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                     MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
        pose proof (snprintf_length 256 "truncated dump file; tried to read %d captured bytes, only got %zu"%string [AInt snapshot; AInt (zlength got)]) as LS.
        change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS.
  Qed.
  End Sz8.
  Lemma np_oread : ltac:(let t := eval cbv delta [np_oread__stmt] in np_oread__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SITES SNPRINTF SP47 SPM SPW TP W1 W9. all: natfold_lits. intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_oread__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[local] Abbreviation p0 := (F_sfpcap_nextA.p0 self buffer f bufsize bufalloc bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize lsw scl).
  #[local] Abbreviation pfx_realloc := (F_sfpcap_nextA.pfx_realloc sp R lo P HA DA LO BU R1 R2 SPW P1).

  (* [comment removed for export] *)
  Definition np_over__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks p0 P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P p0 (pcap_blocks p0 P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (snapshot < cap)%Z -> (cap <= max_snaplen_for_dlt linktype)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (np_over_model MOps (prims HO fo_nop sites) p0 (mkHdr sec usec cap len) cap len sec usec) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 snapshot) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 cap) (Z_to_bv 64 snapshot) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1564c) fc None m5 (seg_rom ssegs)).
  Section Sz9.
  Variables ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_over__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_over__body : ltac2:(SecDiet.SzSec.bodyP 'np_over__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W7 W8 W9 WHS : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hsc Hcm Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    pose proof (max_snaplen_le2 linktype) as MSL.
    pose proof PC5 as PC5'.
    destruct PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    unfold F_sfpcap_nextA.p0 in *. norm_p. unfold sf_cells in PRIV. cbn [sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    subst Ix. assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    pose proof WF as (_ & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W2', W3, W4, WBB.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (BP' : (B + bufalloc <= P \/ P + 664 <= B)%Z).
    { pose proof (PB_apart K _ _ _ _ _ _ (pv buffer bufsize bufalloc bufdata errbuf) P B 0 G5 eq_refl) as [APB _]. unfold F_sfpcap_nextA.pv, psize, is_ng in APB. cbn [pc_bufalloc pc_priv] in APB. unfold PCAP_SF_TOTAL in APB. lia. }
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
    unfold np_over_model, grow_buffer. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_realloc prims pc_bufsize pc_snapshot pc_rfile pc_buffer pc_bufdata
      pc_self pc_bufalloc pc_swapped pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    hide BUF. hide PRIV. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sx32_small bufsize) by lia. step.
    destruct (Z.ltb_spec bufsize cap) as [GROW|NOGROW].
    - (* [comment removed for export] *)
      replace (bufsize <? cap) with true by (symmetry; apply Z.ltb_lt; lia).
      step. if_cases Kb; try (zify_cond Kb; exfalso; (keep_hyps CEILV sp R P HA DA B bufsize bufdata cap dw GROW Kb; lia)).
      unhide BUF. step. step.
      (* [comment removed for export] *)
      apply evt_done. apply (implM_bind_assoc ssegs). name_sp sp (-4208)%Z. eapply (implM_bind ssegs).
      { replace (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) with ((CLc ++ [(self, P, 664%Z)]) ++ (buffer, B, bufalloc) :: []) in G5
          by (rewrite <- app_assoc; reflexivity).
        eapply REALLOC; [| reflexivity | reflexivity | lia | exact BUF].
        split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [bq'|] ps6 ms6 PO; cbv beta iota in PO.
      + destruct PO as (av & m6 & E & OFr & MI6 & ST6 & AG6 & (A' & junk6 & -> & G6 & NEW)).
        unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 0x15660)) with (Z_to_bv 64 0x15660) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite app_nil_r in AG6, G6.
        pose proof (GIo_block_ok K _ _ _ _ _ _ G6 ltac:(left; reflexivity)) as (N1 & N2 & N3 & N4 & N5 & N6). cbn [cb_addr cb_size fst snd] in N1, N2, N3, N4, N5, N6.
        assert (LBS : length bsx' = Z.to_nat bufalloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; exact (proj1 WFB)).
        unhide PRIV. unhide HH. unhide HD.
        assert (KEEP : forall A cs, rw_cells ssegs m5 A cs -> ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells ssegs m6 A cs).
        { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|HX]; [left; lia| right].
          apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
        apply KEEP in CELLS; [| right; cbn [cells_size csize]; lia]. apply KEEP in PRIV; [| right; cbn [cells_size csize]; lia]. clear KEEP.
        assert (G6' : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (bq', A', snapshot)]) FB m6).
        { eapply (GIo_perm K HPL); [exact G6|]. rewrite app_comm_cons. change ((self, P, 664%Z) :: [(bq', A', snapshot)]) with ([(self, P, 664%Z)] ++ [(bq', A', snapshot)]).
          rewrite app_assoc. apply Permutation.Permutation_cons_append. }
        assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
        pose proof (PB_apart K _ _ _ _ _ _ (pv bq' snapshot snapshot (zfirstn snapshot bufdata) errbuf) P A' 0 G6' eq_refl) as [APB' _].
        unfold F_sfpcap_nextA.pv, psize, is_ng in APB'. cbn [pc_bufalloc pc_priv] in APB'. unfold PCAP_SF_TOTAL in APB'.
        clear AG6 G6 ST5 MI5 AG5 PC5' G5 BUF MU WM.
        eapply (implM_retb ssegs). cbv beta iota. cbn [negb set_buffer pc_self pc_rfile pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                                                    pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
        hide NEW. hide PRIV. hide HH. hide HD.
        pose proof (munch_refl [(P + 20, P + 32)]%Z m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
        unfold implM. iprefix. step. if_cases Kz; try (zify_cond Kz; exfalso; clear - Kz N1 N3 N4; lia).
        step. step. rewrite (sx32_small snapshot) by lia. step.
        unhide NEW. unhide PRIV. unhide HH. unhide HD.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGP : agrees_on (fun a => outside [(P + 20, P + 32)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m6' end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in NEW; [| intros a Ha; cbn [outside cells_size csize] in Ha |- *; clear - Ha APB' W1' W3; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; cbn [outside cells_size csize] in Ha |- *; gio_ceil_fact; clear -CLO__ Ha LO BU R1 SPW L4; unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha LO BU R1 R2 SPW L4; unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in PRIV; [| intros a Ha; cbn [outside cells_size csize] in Ha |- *; clear - Ha; lia].
        assert (G6'' : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (bq', A', snapshot)]) FB m6').
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6' | exact MU | exact WM |].
          apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        assert (AG06' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6').
        { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
          destruct (np_CLc_facts _ _ _ _ G6' Ha) as [Hc Hnb]. split; [| exact Logic.I]. intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        merge_all NEW. replace (Z.to_nat (bufalloc `min` snapshot) + (Z.to_nat (snapshot - bufalloc `min` snapshot) + 0))%nat with (Z.to_nat snapshot) in NEW by (keep_hyps CEILV sp R lo P HA DA B bufalloc bufdata snapshot dw A' bsx' K3; lia). rewrite app_nil_r in NEW.
        apply evt_done. eapply (np_oread _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6' ps6 bq' A' snapshot snapshot (zfirstn snapshot bufdata) errbuf sec usec cap len dw fj);
          [exact ST6 | exact FR5 | exact MI6 | exact G6'' | | exact AG06' | exact HH | exact HD | exact Hd | lia | exact Hsc | exact Hcm | exact Hl32 | congruence].
        exists Afx. split; [exact Hin|]. exists A', 0%Z, jx', padx, (firstn (Z.to_nat (bufalloc `min` snapshot)) bsx' ++ junk6).
        split; [reflexivity|].
        split; [unfold F_sfpcap_nextA.pv, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF;
                cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
                     pk_next_pcap pk_cleanup_sf PK pc_rfile]; exact CELLS|].
        split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [unfold F_sfpcap_nextA.pv; cbn [pc_bufalloc]; exact NEW|].
        split; [unfold F_sfpcap_nextA.pv, zfirstn; cbn [pc_bufdata]; apply pfx_realloc; [exact PFX | lia | lia]|].
        split; [reflexivity|].
        pose proof (zfirstn_length_le2 snapshot bufdata) as ZL. eapply pv_wf; [exact WF | clear - Hsc Hcm MSL W1'; lia | clear - Hsc Hcm MSL W1'; lia | clear - ZL W1'; lia | lia].
      + (* [comment removed for export] *)
        destruct PO as (av & m6 & E & OFr & MI6 & ST6 & AG6 & -> & G6 & BUF6 & EN6).
        unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 0x15660)) with (Z_to_bv 64 0x15660) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite app_nil_r in AG6.
        replace ((CLc ++ [(self, P, 664%Z)]) ++ [(buffer, B, bufalloc)]) with (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) in G6 by (rewrite <- app_assoc; reflexivity).
        unhide PRIV. unhide HH. unhide HD.
        assert (KEEP : forall A cs, rw_cells ssegs m5 A cs -> ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells ssegs m6 A cs).
        { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|HX]; [left; lia| right].
          apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
        apply KEEP in CELLS; [| right; cbn [cells_size csize]; lia]. apply KEEP in PRIV; [| right; cbn [cells_size csize]; lia]. clear KEEP.
        assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
        assert (PC6 : PCAPR (hptr:=hptr) P (pv buffer bufsize bufalloc bufdata errbuf) [(self, P, 664%Z); (buffer, B, bufalloc)] FB m6).
        { exists Afx. split; [exact Hin|]. exists B, 0%Z, jx', padx, bsx'. split; [reflexivity|].
          split; [unfold F_sfpcap_nextA.pv, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF;
                  cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
                       pk_next_pcap pk_cleanup_sf PK pc_rfile]; exact CELLS|].
          split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [exact BUF6|]. split; [exact PFX|]. split; [reflexivity| exact WF]. }
        clear AG6 ST5 MI5 AG5 PC5' G5 BUF MU WM.
        (* [comment removed for export] *)
        pose proof PC6 as (Afy & _ & (By & Iy & jy & pady & bsy & EPBy & CELLSy & _ & _ & _ & _ & _)).
        apply pcap_cells_split4 in CELLSy as (_ & CE & _ & _); [|reflexivity].
        apply (rw_cells_split_CB ssegs m6 _ [] 304 _ [] [14; 242; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
        destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE']. cbn [firstn skipn cells_size csize] in CE1, CE'.
        destruct (rw_cells_cut _ _ _ 1 CE') as [CE2 _]. clear CE CE'. cbn [firstn skipn cells_size csize] in CE2.
        replace (P + 216 + Z.of_nat 14)%Z with (P + 230)%Z in CE2 by lia.
        eapply (implM_retb ssegs). cbv beta iota. cbn [negb].
        assert (LENM : length (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) = 14%nat) by (vm_compute; reflexivity).
        hide PRIV. hide HH. hide HD. hide CELLS. hide CE2. hide BUF6.
        pose proof (munch_refl [(P + 216, P + 216 + 14)]%Z m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
        unfold implM. iprefix. step. if_true. do 6 step.
        call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P + 216)%Z 0x10df2%Z 14%Z (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) (firstn 14 (pj_g jy)));
          [reflexivity | reflexivity | reflexivity
          | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m6 0x10df2 (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) MI6 ltac:(vm_compute; reflexivity) ltac:((keep_hyps CEILV sp R P HA DA B bufdata dw; lia)) ltac:(rewrite LENM; cbn; (keep_hyps CEILV sp R P HA DA B bufdata dw; lia))))
          | rewrite LENM; reflexivity | (keep_hyps CEILV sp R P HA DA B bufdata dw; lia) | exact CE1 | unfold rc_lo in LO; (keep_hyps CEILV sp R P HA DA B bufdata dw L5; lia) | (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA B self buffer bufalloc bufdata dw m6 ps6 L4; lia) | (keep_hyps CEILV sp R P HA DA B bufdata dw; lia) | exact MI6 |].
        unhide PRIV. unhide HH. unhide HD. unhide CELLS. unhide CE2. unhide BUF6.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P + 216, P + 216 + 14)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGW) in HH; [| intros a Ha; cbn [outside cells_size csize] in *; unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGW) in HD; [| intros a Ha; cbn [outside cells_size csize] in *; unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGW) in CE2; [| intros a Ha; cbn [outside cells_size csize] in *; lia].
        assert (G7 : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU | exact WM |].
          apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        assert (PC7 : PCAPR (hptr:=hptr) P (pv buffer bufsize bufalloc bufdata Msg.out_of_memory) [(self, P, 664%Z); (buffer, B, bufalloc)] FB m7).
        { lazymatch goal with PCm : rw_cells ssegs m7 (P + 216)%Z _ |- _ =>
            pose proof (rw_cells_uncut _ _ _ _ _ PCm CE2 ltac:(cbn; lia)) as EB7 end.
          change (pv buffer bufsize bufalloc bufdata Msg.out_of_memory) with (set_errbuf Msg.out_of_memory (pv buffer bufsize bufalloc bufdata errbuf)).
          eapply (PCAPR_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G6 PC6 AGW); [| exact EB7 | rewrite cells_size_app; cbn; lia].
          intros a Ha Hn. cbn [outside]. lia. }
        assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AGW|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
          destruct (np_CLc_facts _ _ _ _ G6 Ha) as [Hc Hnb]. split; [| exact Logic.I]. intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        step. apply evt_done.
        eapply np_fail_tail; [eassumption | exact FR5 | eassumption | ].
        split; [exact G7|]. split; [unfold F_sfpcap_nextA.pv in PC7; cbn [set_errbuf] ; exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence].
    - (* [comment removed for export] *)
      apply evt_done. eapply (implM_retb ssegs). cbv beta iota. cbn [negb].
      unfold implM. iprefix. step. if_cases Kb; [ idtac | try (zify_cond Kb; exfalso; (keep_hyps CEILV sp R P HA DA B bufsize bufdata cap dw NOGROW Kb; lia)) ].
      unhide BUF. unhide PRIV. unhide HH. unhide HD.
      apply evt_done. eapply (np_oread _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps buffer B bufsize bufalloc bufdata errbuf sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5' | exact AG5 | exact HH | exact HD | exact Hd | lia | exact Hsc | exact Hcm | exact Hl32 | exact OF5].
  Qed.
  End Sz9.
  Lemma np_over : ltac:(let t := eval cbv delta [np_over__stmt] in np_over__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W7 W8 W9 WHS. all: natfold_lits. intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_over__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpCtxB.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_nextA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcap_nextA2.
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
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma max_snaplen_le2 : forall d, (max_snaplen_for_dlt d <= 134217728)%Z.
Proof using Type. all: natfold_lits. pin_using tt. intros d. unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN. repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) end; lia. Qed.

Lemma zfirstn_length_le2 : forall n (l : list Z), (length (zfirstn n l) <= Z.to_nat n)%nat.
Proof using Type. all: natfold_lits. pin_using tt. intros. unfold zfirstn. rewrite length_firstn. lia. Qed.

(* [comment removed for export] *)
Lemma pv_wf : forall {hptr} (self f : hptr) swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl
                     (bq : hptr) bsz alloc data eb (bq' : hptr) bsz' alloc' data' eb',
  pcap_wf (S3.F_sfpcap_nextA.TwB.pv self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl bq bsz alloc data eb) ->
  (0 <= bsz' <= 2^30)%Z -> (0 <= alloc' < 2^32)%Z -> (Z.of_nat (length data') <= alloc')%Z -> (bsz' <= alloc')%Z ->
  pcap_wf (S3.F_sfpcap_nextA.TwB.pv self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl bq' bsz' alloc' data' eb').
Proof using Type. all: natfold_lits. pin_using tt.
  intros until eb'. intros WF B1 B2 B3 B4. unfold pcap_wf, S3.F_sfpcap_nextA.TwB.pv in *.
  cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
       pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv] in *.
  repeat split; try (keep_hyps vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl bsz alloc data data' WF bsz' B1 alloc' B2 B3 B4; lia); try tauto.
Qed.

Section NpCtxB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA B Af : Z) (m : mem) (o : option hptr).
  Variables (self buffer f : hptr) (bufsize bufalloc : Z) (bufdata : list Z) (swapped : bool)
            (vmaj vmin snapshot linktype ltext prec brk : Z) (errbuf : list Z) (header : pkthdr)
            (hdrsize : Z) (lsw : lenswap_t) (scl : sf_scale_t) (j : pcap_junk) (pad bs : list byte).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 664 <= CEILZ)%Z.
  Hypothesis P5 : (P + 664 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 664 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize < 2^32)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.
  Hypothesis WHS : (hdrsize = 16 \/ hdrsize = 24)%Z.
  Hypothesis PPLEN : forall lt sw hdr d, length (snd (pcapint_post_process lt sw hdr d)) = length d.
  Hypothesis PPSEC : forall lt sw hdr d, h_sec (fst (pcapint_post_process lt sw hdr d)) = h_sec hdr /\ h_usec (fst (pcapint_post_process lt sw hdr d)) = h_usec hdr.
  Hypothesis PPRNG : forall lt sw hdr d, (0 <= h_caplen hdr <= Z.of_nat (length d))%Z -> (0 <= h_len hdr < 2^32)%Z -> (Z.of_nat (length d) < 2^31)%Z ->
     (0 <= h_caplen (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z /\ (0 <= h_len (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (S3.F_sfpcap_nextA.TwB.pv self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl).
  #[local] Abbreviation np_fail_tail := (S3.F_sfpcap_nextA.TwB.np_fail_tail K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation np_ok_tail := (S3.F_sfpcap_nextA.TwB.np_ok_tail K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation np_snp := (S3.F_sfpcap_nextA.TwB.np_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation np_fmt := (S3.F_sfpcap_nextA.TwB.np_fmt K FMT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P2 P4).
  #[local] Abbreviation np_finish := (S3.F_sfpcap_nextA.TwB.np_finish K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl
                               LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P5 P6 W9 PPLEN PPSEC PPRNG).
  #[local] Abbreviation np_nread := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcap_nextA2.np_nread HO K sites HFL SFL HAL FREAD FERROR FMT SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f swapped vmaj vmin snapshot linktype ltext prec brk header hdrsize lsw scl
                              LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 HinF P1 P2 P4 P5 P6 W1 W5 W6 W7 W8 W9 W10 WHS PPLEN PPSEC PPRNG).
  #[local] Abbreviation np_normal := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcap_nextA2.np_normal HO K sites HFL SFL HPL HAL FREAD FERROR FMT SNPRINTF REALLOC PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA B Af m o self buffer f bufsize bufalloc bufdata swapped
                               vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize lsw scl
                               LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 HinF P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10 WHS PPLEN PPSEC PPRNG).
  #[local] Abbreviation np_CLc_facts := (S3.F_sfpcap_nextA.TwB.np_CLc_facts K R CLc FB).
  #[local] Abbreviation PCAPR_errbuf := (S3.F_sfpcap_nextA.TwB.PCAPR_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_p :=
    unfold S3.F_sfpcap_nextA.TwB.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells
         sf_hdrsize sf_lengths_swapped sf_scale_type ifaces_ok set_bufdata set_errbuf set_buffer] in *;
    unfold PCAP_SF_TOTAL, PCAP_PRIV_OFF in *.

  (* [comment removed for export] *)
  Lemma discard_loop_S : forall fuel fp cap btd br,
    discard_loop MOps (prims HO fo_nop sites) (S fuel) fp cap btd br =
    (if (btd =? 0)%Z then mret (inr tt) else
     got <- e_fread (prims HO fo_nop sites) fp (DStack SiteDiscardBuf 0) (if 4096 <? btd then 4096 else btd)%Z ;;
     (if negb (zlength got =? (if 4096 <? btd then 4096 else btd))%Z
      then (m0 <- read_fail_msg MOps (prims HO fo_nop sites) fp (Msg.trunc_captured_u cap (br + zlength got)) ;; mret (inl m0))
      else discard_loop MOps (prims HO fo_nop sites) fuel fp cap (btd - zlength got) (br + zlength got))).
  Proof using Type. all: natfold_lits. pin_using tt. intros. reflexivity. Qed.

  Lemma discard_loop_0 : forall fuel fp cap br, discard_loop MOps (prims HO fo_nop sites) fuel fp cap 0 br = mret (inr tt).
  Proof using Type. all: natfold_lits. pin_using tt. intros. destruct fuel; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma np_discard : forall (fuel : nat)
      (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x5 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
      (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len btd bread : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> Z.of_nat (length data) = snapshot -> (0 <= len < 2^32)%Z -> (0 <= cap < 2^31)%Z ->
      (0 < btd)%Z -> (btd <= 4096 * (Z.of_nat fuel - 1))%Z -> (0 <= bread)%Z -> (bread + btd <= cap)%Z -> ps_outfile ps = o ->
      implM usegs (r <- discard_loop MOps (prims HO fo_nop sites) fuel f cap btd bread ;;
                   match r with
                   | inl m0 => mret ((-1)%Z, mkHdr sec usec cap len, set_errbuf m0 (pv bq bsz alloc data eb))
                   | inr _ => (let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec snapshot len) data in
                               mret (1%Z, hdr, set_bufdata d (pv bq bsz alloc data eb)))
                   end) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 bread) x5 (Z_to_bv 64 btd) x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15c84) fc None m5 (seg_rom usegs)).
  Proof using AD AH ALN BU FERROR FMT FREAD HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SITES SNPRINTF SP47 SPM SPW TP W1 W9. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SITES SNPRINTF SP47 SPM SPW TP W1 W9 : unit) => tt).
    induction fuel as [|fuel IH]; intros until fj; intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd DRNG DLEN Hl32 Hc31 Bpos Bfuel Br0 Brc OF5.
    { exfalso. cbn [Z.of_nat] in Bfuel. lia. }
    rewrite Nat2Z.inj_succ in Bfuel.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof W1 as W1'. unfold INT_MAX in W1'.
    rewrite discard_loop_S. replace (btd =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    set (n := (if 4096 <? btd then 4096 else btd)%Z).
    assert (Hn : (0 < n <= 4096)%Z /\ (n <= btd)%Z /\ (n = btd \/ (n = 4096 /\ 4096 < btd))%Z) by (subst n; destruct (Z.ltb_spec 4096 btd); lia).
    clearbody n.
    unfold read_fail_msg, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims].
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 1 FR5) as [FJ FS]. clear FR5. cbn [firstn skipn cells_size csize] in FJ, FS.
    apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat 4136) _ [] [16; Z.to_nat n; Z.to_nat 4120 - Z.to_nat n]%nat) in FJ; [| cbn; (keep_hyps CEILV sp R lo P HA DA fuel data btd dw n Hn; lia)]. cbn [mk_CB_cells app] in FJ.
    lazymatch type of FJ with rw_cells _ _ _ [CB _ ?l0; CB _ ?l1; CB _ ?l2] =>
      set (j0 := l0) in FJ; set (j1 := l1) in FJ; set (j2 := l2) in FJ; clearbody j0 j1 j2 end.
    destruct (rw_cells_cut _ _ _ 1 FJ) as [F0 F12]. clear FJ. cbn [firstn skipn cells_size csize] in F0, F12.
    destruct (rw_cells_cut _ _ _ 1 F12) as [F1 F2]. clear F12. cbn [firstn skipn cells_size csize] in F1, F2.
    lazymatch type of F1 with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -4192)%Z in F1 by lia end.
    (* [comment removed for export] *)
    lazymatch goal with |- implM _ ?c ?st ?Q _ =>
      assert (K78 : forall (a0v s5v : word) (mx : mem), s5v = Z_to_bv 64 n -> mx = m5 ->
        implM usegs c st Q
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0v a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 bread) s5v (Z_to_bv 64 btd) x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15c94) fc None mx (seg_rom usegs)))
    end.
    2:{ pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
        hide F0. hide F1. hide F2. hide FS. hide HH. hide HD.
        unfold implM. iprefix. step. step. step. if_cases Kc; zify_cond Kc.
        - apply evt_done. apply (K78 _ _ m5); [f_equal; lia| reflexivity].
        - step. apply evt_done. apply (K78 _ _ m5); [f_equal; lia| reflexivity]. }
    intros a0v s5v mx -> ->.
    hide F0. hide F2. hide FS. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. do 5 step.
    (* [comment removed for export] *)
    name_sp sp (-4208)%Z.
    apply evt_done. apply (implM_bind_assoc usegs). eapply (implM_bind usegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop].
      replace (sites SiteDiscardBuf + 0)%Z with (bv_unsigned sp + -4192)%Z by (rewrite SITES; unfold sites_at, D_NEXT_PACKET; lia).
      eapply FREAD; [| exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact F1 | ].
      { split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      right. rewrite Hsp. lia. }
    intros got ps6 ms6 PO. cbv beta in PO.
    destruct PO as (av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp. cbv beta.
    replace (ret_pc (Z_to_bv 64 0x15ca8)) with (Z_to_bv 64 0x15ca8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide F0. unhide F2. unhide FS. unhide HH. unhide HD. clear F1.
    assert (KEEP : forall A cs, rw_cells usegs m5 A cs -> (bv_unsigned sp + -4208 <= A)%Z ->
              (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -4192 \/ bv_unsigned sp + -4192 + n <= A)%Z -> rw_cells usegs m6 A cs)
      by (intros A cs HC HA' HB; eapply agrees_rw_cells; [exact AG6 | exact HC | intros a Ha; split; [left; lia| lia]]).
    apply KEEP in F0; [| lia | cbn [cells_size csize]; lia]. apply KEEP in F2; [| lia | lia]. apply KEEP in FS; [| (keep_hyps CEILV sp R P HA DA fuel data dw; lia) | (keep_hyps CEILV ra sp s0 s1 s2 s3 s4 s5 s6 s7 R P HA DA fuel data btd dw n Hn; lia)].
    apply KEEP in HH; [| lia | lia]. apply KEEP in HD; [| lia | lia]. clear KEEP.
    assert (PC6 : PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m6).
    { eapply PCAPR_agree; [exact AG6 | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha).
      split; [right; apply in_block_app; right; exact Ha| unfold rc_lo in LO; lia]. }
    assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [split; [left; lia| unfold rc_lo in LO; lia]|].
      destruct (np_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [right; apply in_block_app; left; exact Ha| lia]. }
    (* [comment removed for export] *)
    pose proof (rw_cells_uncut _ _ _ _ _ F0 HD6 ltac:(cbn [cells_size csize]; lia)) as FJ.
    pose proof (rw_cells_uncut _ _ _ _ _ FJ F2 ltac:(cbn [cells_size csize app]; unfold zlength in GOTL; lia)) as FJ'. clear FJ F0 F2 HD6.
    cbn [app] in FJ'. merge_all_lazy FJ'.
    lazymatch type of FJ' with rw_cells _ _ _ [CB ?k _] => replace k with (Z.to_nat 4136) in FJ' by (cbn [cells_size csize Nat.add]; unfold zlength in GOTL; (keep_hyps CEILV sp R lo P HA DA fuel data btd dw n got Hn GOTL; lia)) end.
    pose proof (rw_cells_uncut _ _ _ _ _ FJ' FS ltac:(cbn [cells_size csize]; (keep_hyps CEILV sp R P HA DA fuel data dw; lia))) as FR6. clear FJ' FS. cbn [app] in FR6.
    clear MU WM ST5 MI5 G5 PC5 AG5.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
    hide HH. hide HD.
    unfold implM. iprefix. step.
    destruct (Z.eq_dec (zlength got) n) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite LEQ. rewrite Z.eqb_refl. cbn [negb].
      step. if_cases Kq; [ try (zify_cond Kq; exfalso; (keep_hyps CEILV sp R P HA DA fuel data btd dw n Kq; lia)) | idtac ].
      step.
      destruct (Z.eq_dec btd n) as [LAST|MORE].
      + (* [comment removed for export] *)
        step. if_cases Kz; [ try (zify_cond Kz; exfalso; (keep_hyps CEILV sp R lo P HA DA fuel data btd dw n LAST Kz; lia)) | idtac ].
        replace (btd - n)%Z with 0%Z by lia. rewrite discard_loop_0. rewrite mbind_mret.
        (* [comment removed for export] *)
        pose proof PC6 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & _)).
        unfold S3.F_sfpcap_nextA.TwB.pv, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
        assert (EBX : Bx' = Bx) by congruence. subst Bx'. clear EPB.
        unfold S3.F_sfpcap_nextA.TwB.pv, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
        cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
             pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
        clear MU WM. pose proof (munch_refl [(HA + 16, HA + 20)]%Z m6) as MU. pose proof (wmono_refl usegs m6) as WM.
        hide FR6.
        step. rewrite (sx32_small snapshot) by lia. unhide HH. step. step.
        unhide FR6. unhide HD. clear CELLS.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGP : agrees_on (fun a => outside [(HA + 16, HA + 20)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; cbn [outside cells_size csize] in Ha |- *; (keep_hyps CEILV sp R lo P HA DA fuel data dw a R1 Ha; lia)].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; lia].
        assert (G7 : GIo K R ps6 (CLc ++ pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU | exact WM |].
          apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo. lia. }
        assert (PC7 : PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m7).
        { eapply PCAPR_agree; [exact AGP | | exact PC6]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G6 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
        assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. lia. }
        apply evt_done. eapply np_finish.
        all: try exact FR6; try exact HH; try exact HD; try exact Hd; try exact G7; try exact PC7; try exact AG07; try exact DRNG; try exact Hl32; try reflexivity; try (keep_hyps CEILV sp R lo P HA DA snapshot fuel data dw DLEN W1'; lia).
        all: try eassumption. all: try congruence.
      + (* [comment removed for export] *)
        step. if_cases Kz; [ idtac | try (zify_cond Kz; exfalso; (keep_hyps CEILV sp R lo P HA DA fuel data cap btd bread dw n Hc31 Br0 Brc Hn MORE Kz; lia)) ].
        unhide HH. unhide HD.
        replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 btd) - bv_unsigned (Z_to_bv 64 n))) with (Z_to_bv 64 (btd - n)) by (rewrite !unsigned_lit by lia; reflexivity).
        replace (Z_to_bv 64 (n + bread)) with (Z_to_bv 64 (bread + n)) by (f_equal; lia).
        apply evt_done. eapply IH; try eassumption; try (keep_hyps CEILV sp R P HA DA fuel data btd dw n Hn MORE lo Bfuel bread got Br0 GOTL cap Brc; lia); try congruence.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      step. if_cases Kq; [ idtac | try (zify_cond Kq; exfalso; unfold zlength in *; (keep_hyps CEILV R btd n LNE Kq; lia)) ].
      do 2 step.
      apply evt_done. apply (implM_bind_assoc usegs). apply (implM_bind_assoc usegs). name_sp sp (-4208)%Z. eapply (implM_bind usegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G6|]. split; [rewrite Hsp; exact ST6|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI6|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros r ps7 ms7 PO. cbv beta in PO. destruct PO as (av7 & m7 & E & MI7 & ST7 & AG7 & G7 & -> & -> & ERRNO).
      unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms7. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x15e8c)) with (Z_to_bv 64 0x15e8c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide HH. unhide HD.
      assert (KEEP : forall A cs, rw_cells usegs m6 A cs -> (bv_unsigned sp + -4208 <= A)%Z -> rw_cells usegs m7 A cs)
        by (intros A cs HC HX; eapply agrees_rw_cells; [exact AG7 | exact HC | intros a Ha; left; lia]).
      apply KEEP in FR6; [| lia]. apply KEEP in HH; [| lia]. apply KEEP in HD; [| lia]. clear KEEP.
      assert (PC7 : PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m7).
      { eapply PCAPR_agree; [exact AG7 | | exact PC6]. intros a Ha. right. apply in_block_app. right. exact Ha. }
      assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
      { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AG7|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
      clear AG7 MU WM. hide FR6. hide HD. hide HH.
      pose proof (munch_refl ([] : list (Z * Z)) m7) as MU. pose proof (wmono_refl usegs m7) as WM.
      destruct r.
      + (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN ER]. clear ERRNO. unfold utp in EN. rewrite <- TP in EN.
        pose proof (GIo_tls K _ _ _ _ _ G7) as [_ TB]. unfold tls_block_ok_u, utp in TB. rewrite <- TP in TB.
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        set (e := lc_errno (ps_libc ps6)) in *.
        assert (E4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
        { destruct TB as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * 4 + 9)%Z. lia. }
        unfold implM. iprefix. cbn [Z.b2z]. step. if_false. do 5 step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(clear - TB; lia)).
        step. rewrite (and3_aligned (bv_unsigned tp + -164)) by (clear - TB E4; lia). step. if_false.
        step. rewrite (sx32_s32 e) by lia. do 4 step.
        unhide FR6. unhide HD. unhide HH.
        apply evt_done. eapply np_fmt; [exact ST7 | exact FR6 | exact MI7 | | lia |].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m7 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))).
      + (* [comment removed for export] *)
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        unfold implM. iprefix. cbn [Z.b2z]. step. if_true.
        unhide HH. step. rewrite (sx32_small cap) by lia. hide HH. do 8 step.
        unhide FR6. unhide HD. unhide HH.
        apply evt_done. unfold Msg.trunc_captured_u, PCAP_ERRBUF_SIZE.
        eapply np_snp; [exact ST7 | exact FR6 | exact MI7 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m7 0x10c8d (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %u captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                     MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        { cbn [length firstn]. constructor; [reflexivity|]. constructor; [f_equal; lia| constructor]. }
        pose proof (snprintf_length 256 "truncated dump file; tried to read %u captured bytes, only got %zu"%string [AInt cap; AInt (bread + zlength got)]) as LS.
        change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS.
  Qed.
  Lemma subw_small : forall x y, (0 <= y <= x)%Z -> (x < 2^31)%Z ->
    Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) - bv_unsigned (Z_to_bv 64 y))) = Z_to_bv 64 (x - y).
  Proof using BU CEILV LO P1 R1 R2 SPW. all: natfold_lits. pin_using (fun (BU CEILV LO P1 R1 R2 SPW : unit) => tt). intros x y Hxy Hx. rewrite !unsigned_lit by lia. f_equal. apply bv_swrap32_small. lia. Qed.

  (* [comment removed for export] *)
  Definition np_oread__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (snapshot <= bsz)%Z -> (snapshot < cap)%Z -> (cap <= max_snaplen_for_dlt linktype)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (np_oread_model MOps (prims HO fo_nop sites) f snapshot (pv bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 cap) (Z_to_bv 64 snapshot) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15c4c) fc None m5 (seg_rom usegs)).
  Section Sz8.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_oread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_oread__body : ltac2:(SecDiet.SzSec.bodyP 'np_oread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SITES SNPRINTF SP47 SPM SPW TP W1 W9. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SITES SNPRINTF SP47 SPM SPW TP W1 W9 : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hsb Hsc Hcm Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    pose proof PC5 as PC5'.
    destruct PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    norm_p. unfold sf_cells in PRIV. cbn [sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    subst Ix. assert (EBX : Bx' = Bx) by congruence. subst Bx'. clear EPB.
    pose proof WF as (_ & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W2', W3, W4, WBB.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (BP' : (Bx + alloc <= P \/ P + 664 <= Bx)%Z).
    { pose proof (PB_apart K _ _ _ _ _ _ (pv bq bsz alloc data eb) P Bx 0 G5 eq_refl) as [APB _]. unfold S3.F_sfpcap_nextA.TwB.pv, psize, is_ng in APB. cbn [pc_bufalloc pc_priv] in APB. unfold PCAP_SF_TOTAL in APB. lia. }
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat alloc) _ [] [Z.to_nat snapshot; Z.to_nat alloc - Z.to_nat snapshot]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. cbn [firstn skipn cells_size csize] in BD, BT.
    unfold np_oread_model, read_fail_msg, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims pc_buffer pc_linktype pc_swapped pc_bufdata set_bufdata set_errbuf
      pc_self pc_rfile pc_bufsize pc_bufalloc pc_version_major pc_version_minor pc_snapshot pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    hide BT. hide PRIV. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    step. step. rewrite (sx32_small snapshot) by lia. hide CELLS. do 3 step.
    name_sp sp (-4208)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop]. unfold blk_addr.
      rewrite (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G5 ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity)).
      rewrite Z.add_0_r.
      eapply FREAD; [| exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact BD | ].
      { split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      left. intros a Ha. apply in_block_app. right. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    intros got ps6 ms6 PO. cbv beta in PO.
    destruct PO as (av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp. cbv beta.
    replace (ret_pc (Z_to_bv 64 0x15c60)) with (Z_to_bv 64 0x15c60) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide BT. unhide PRIV. unhide CELLS. unhide HH. unhide HD.
    assert (KEEP : forall A cs, rw_cells usegs m5 A cs ->
              ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664) \/ (Bx + snapshot <= A /\ A + Z.of_nat (cells_size cs) <= Bx + alloc))%Z ->
              rw_cells usegs m6 A cs).
    { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|[HX|HX]].
      - split; [left; lia| unfold rc_lo in LO; lia].
      - split; [| lia]. right. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
      - split; [| lia]. right. apply in_block_app. right. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
    apply KEEP in CELLS; [| right; left; cbn [cells_size csize]; lia]. apply KEEP in PRIV; [| right; left; cbn [cells_size csize]; lia].
    apply KEEP in BT; [| right; right; cbn [cells_size csize]; lia]. clear KEEP.
    assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [split; [left; lia| unfold rc_lo in LO; lia]|].
      destruct (np_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [right; apply in_block_app; left; exact Ha|].
      intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    clear AG6 MI5 ST5 PC5' AG5 MU WM.
    (* [comment removed for export] *)
    pose proof (rw_cells_uncut _ _ _ _ _ HD6 BT ltac:(cbn [cells_size csize]; unfold zlength in GOTL; lia)) as BUF6. cbn [app] in BUF6. merge_all BUF6.
    replace (length got + (Z.to_nat snapshot - length got + (Z.to_nat alloc - Z.to_nat snapshot + 0)))%nat with (Z.to_nat alloc) in BUF6 by (unfold zlength in GOTL; lia).
    rewrite app_nil_r in BUF6. clear HD6 BT.
    assert (PC6 : PCAPR (hptr:=hptr) P (pv bq bsz alloc got eb) [(self, P, 664%Z); (bq, Bx, alloc)] FB m6).
    { exists Afx. split; [exact Hin|]. exists Bx, 0%Z, jx', padx, (map b8 got ++ junk6 ++ firstn (Z.to_nat alloc - Z.to_nat snapshot) (skipn (Z.to_nat snapshot) bsx')).
      split; [reflexivity|].
      split; [unfold S3.F_sfpcap_nextA.TwB.pv, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF;
              cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
                   pk_next_pcap pk_cleanup_sf PK pc_rfile]; exact CELLS|].
      split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [unfold S3.F_sfpcap_nextA.TwB.pv; cbn [pc_bufalloc]; exact BUF6|].
      split; [unfold S3.F_sfpcap_nextA.TwB.pv; cbn [pc_bufdata]; replace (length got) with (length (map b8 got)) by (apply length_map);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      eapply pv_wf; [exact WF | clear - W2'; lia | clear - W3; lia | clear - GOTL Hsb WBB; unfold zlength in GOTL; lia | clear - WBB; lia]. }
    assert (G6' : GIo K R ps6 (CLc ++ pcap_blocks (pv bq bsz alloc got eb) P Bx 0) FB m6) by exact G6.
    hide BUF6. hide PRIV. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
    unfold implM. iprefix. step. step. rewrite (zx32_lit snapshot) by lia. step. rewrite (sextw_small snapshot) by lia.
    destruct (Z.eq_dec (zlength got) snapshot) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
      step. if_cases Kq; try (zify_cond Kq; exfalso; unfold zlength in *; (keep_hyps CEILV R LEQ Kq; lia)).
      step. rewrite (sx32_small cap) by lia.
      step. if_cases Kc; try (zify_cond Kc; exfalso; (keep_hyps CEILV sp R P HA DA snapshot Bx data cap dw Hsc Kc; lia)).
      step. rewrite (subw_small cap snapshot) by lia. do 2 step. rewrite (zext32_shifts_lit (cap - snapshot)) by lia.
      unhide BUF6. unhide PRIV. unhide HD. clear CELLS.
      rewrite LEQ.
      apply evt_done. eapply (np_discard (Z.to_nat ((cap - snapshot) / 4096 + 2)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps6 bq Bx bsz alloc got eb sec usec cap len (cap - snapshot) snapshot dw);
        [exact ST6 | exact FR5 | exact MI6 | exact G6' | exact PC6 | exact AG06 | exact HH | exact HD | exact Hd | exact GOTR
        | unfold zlength in LEQ; lia | exact Hl32 | lia | lia | | lia | lia | congruence ].
      rewrite Z2Nat.id by (Z.div_mod_to_equations; (keep_hyps CEILV R snapshot data cap dw q r Hsc H0 H1; lia)). Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      step. if_cases Kq; try (zify_cond Kq; exfalso; unfold zlength in *; (keep_hyps CEILV R LNE Kq; lia)).
      do 2 step.
      apply evt_done. apply (implM_bind_assoc usegs). name_sp sp (-4208)%Z. eapply (implM_bind usegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G6|]. split; [rewrite Hsp; exact ST6|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI6|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros r ps7 ms7 PO. cbv beta in PO. destruct PO as (av7 & m7 & E & MI7 & ST7 & AG7 & G7 & -> & -> & ERRNO).
      unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms7. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x15dd4)) with (Z_to_bv 64 0x15dd4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide BUF6. unhide PRIV. unhide HD.
      assert (KEEP : forall A cs, rw_cells usegs m6 A cs -> (bv_unsigned sp + -4208 <= A)%Z -> rw_cells usegs m7 A cs)
        by (intros A cs HC HX; eapply agrees_rw_cells; [exact AG7 | exact HC | intros a Ha; left; lia]).
      apply KEEP in FR5; [| lia]. apply KEEP in HH; [| lia]. apply KEEP in HD; [| lia]. clear KEEP.
      assert (PC7 : PCAPR (hptr:=hptr) P (pv bq bsz alloc got eb) [(self, P, 664%Z); (bq, Bx, alloc)] FB m7).
      { eapply PCAPR_agree; [exact AG7 | | exact PC6]. intros a Ha. right. apply in_block_app. right. exact Ha. }
      assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
      { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AG7|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
      clear AG7 MU WM CELLS. hide BUF6. hide PRIV. hide HD. hide HH.
      pose proof (munch_refl ([] : list (Z * Z)) m7) as MU. pose proof (wmono_refl usegs m7) as WM.
      destruct r.
      + (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN ER]. clear ERRNO. unfold utp in EN. rewrite <- TP in EN.
        pose proof (GIo_tls K _ _ _ _ _ G7) as [_ TB]. unfold tls_block_ok_u, utp in TB. rewrite <- TP in TB.
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        set (e := lc_errno (ps_libc ps6)) in *.
        assert (E4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
        { destruct TB as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * 4 + 9)%Z. lia. }
        unfold implM. iprefix. cbn [Z.b2z]. step. if_false. do 5 step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(clear - TB; lia)).
        step. rewrite (and3_aligned (bv_unsigned tp + -164)) by (clear - TB E4; lia). step. if_false.
        step. rewrite (sx32_s32 e) by lia. do 4 step.
        unhide BUF6. unhide PRIV. unhide HD. unhide HH.
        apply evt_done. eapply np_fmt; [exact ST7 | exact FR5 | exact MI7 | | lia |].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m7 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))).
      + (* [comment removed for export] *)
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        unfold implM. iprefix. cbn [Z.b2z]. step. if_true. do 9 step.
        unhide BUF6. unhide PRIV. unhide HD. unhide HH.
        apply evt_done. unfold Msg.trunc_captured_d, PCAP_ERRBUF_SIZE.
        eapply np_snp; [exact ST7 | exact FR5 | exact MI7 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m7 0x1058d (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %d captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                     MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
        pose proof (snprintf_length 256 "truncated dump file; tried to read %d captured bytes, only got %zu"%string [AInt snapshot; AInt (zlength got)]) as LS.
        change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS.
  Qed.
  End Sz8.
  Lemma np_oread : ltac:(let t := eval cbv delta [np_oread__stmt] in np_oread__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SITES SNPRINTF SP47 SPM SPW TP W1 W9. all: natfold_lits. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_oread__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[local] Abbreviation p0 := (S3.F_sfpcap_nextA.TwB.p0 self buffer f bufsize bufalloc bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize lsw scl).

  (* [comment removed for export] *)
  Definition np_over__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks p0 P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P p0 (pcap_blocks p0 P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (snapshot < cap)%Z -> (cap <= max_snaplen_for_dlt linktype)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (np_over_model MOps (prims HO fo_nop sites) p0 (mkHdr sec usec cap len) cap len sec usec) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 snapshot) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 cap) (Z_to_bv 64 snapshot) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15c2c) fc None m5 (seg_rom usegs)).
  Section Sz9.
  Variables ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_over__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_over__body : ltac2:(SecDiet.SzSec.bodyP 'np_over__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W7 W8 W9 WHS : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hsc Hcm Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    pose proof (max_snaplen_le2 linktype) as MSL.
    pose proof PC5 as PC5'.
    destruct PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    unfold S3.F_sfpcap_nextA.TwB.p0 in *. norm_p. unfold sf_cells in PRIV. cbn [sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    subst Ix. assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    pose proof WF as (_ & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W2', W3, W4, WBB.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (BP' : (B + bufalloc <= P \/ P + 664 <= B)%Z).
    { pose proof (PB_apart K _ _ _ _ _ _ (pv buffer bufsize bufalloc bufdata errbuf) P B 0 G5 eq_refl) as [APB _]. unfold S3.F_sfpcap_nextA.TwB.pv, psize, is_ng in APB. cbn [pc_bufalloc pc_priv] in APB. unfold PCAP_SF_TOTAL in APB. lia. }
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
    unfold np_over_model, grow_buffer. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_realloc prims pc_bufsize pc_snapshot pc_rfile pc_buffer pc_bufdata
      pc_self pc_bufalloc pc_swapped pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    hide BUF. hide PRIV. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sx32_small bufsize) by lia.
    destruct (Z.ltb_spec bufsize cap) as [GROW|NOGROW].
    - (* [comment removed for export] *)
      replace (bufsize <? cap) with true by (symmetry; apply Z.ltb_lt; lia).
      step. if_cases Kb; try (zify_cond Kb; exfalso; (keep_hyps CEILV sp R P HA DA B bufsize bufdata cap dw GROW Kb; lia)).
      unhide BUF. step. step. step.
      (* [comment removed for export] *)
      apply evt_done. apply (implM_bind_assoc usegs). name_sp sp (-4208)%Z. eapply (implM_bind usegs).
      { replace (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) with ((CLc ++ [(self, P, 664%Z)]) ++ (buffer, B, bufalloc) :: []) in G5
          by (rewrite <- app_assoc; reflexivity).
        eapply REALLOC; [| reflexivity | reflexivity | lia | exact BUF].
        split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [bq'|] ps6 ms6 PO; cbv beta iota in PO.
      + destruct PO as (av & m6 & E & OFr & MI6 & ST6 & AG6 & (A' & junk6 & -> & G6 & NEW)).
        unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 0x15c40)) with (Z_to_bv 64 0x15c40) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite app_nil_r in AG6, G6.
        pose proof (GIo_block_ok K _ _ _ _ _ _ G6 ltac:(left; reflexivity)) as (N1 & N2 & N3 & N4 & N5 & N6). cbn [cb_addr cb_size fst snd] in N1, N2, N3, N4, N5, N6.
        assert (LBS : length bsx' = Z.to_nat bufalloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; exact (proj1 WFB)).
        unhide PRIV. unhide HH. unhide HD.
        assert (KEEP : forall A cs, rw_cells usegs m5 A cs -> ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells usegs m6 A cs).
        { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|HX]; [left; lia| right].
          apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
        apply KEEP in CELLS; [| right; cbn [cells_size csize]; lia]. apply KEEP in PRIV; [| right; cbn [cells_size csize]; lia]. clear KEEP.
        assert (G6' : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (bq', A', snapshot)]) FB m6).
        { eapply (GIo_perm K HPL); [exact G6|]. rewrite app_comm_cons. change ((self, P, 664%Z) :: [(bq', A', snapshot)]) with ([(self, P, 664%Z)] ++ [(bq', A', snapshot)]).
          rewrite app_assoc. apply Permutation.Permutation_cons_append. }
        assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
        pose proof (PB_apart K _ _ _ _ _ _ (pv bq' snapshot snapshot (zfirstn snapshot bufdata) errbuf) P A' 0 G6' eq_refl) as [APB' _].
        unfold S3.F_sfpcap_nextA.TwB.pv, psize, is_ng in APB'. cbn [pc_bufalloc pc_priv] in APB'. unfold PCAP_SF_TOTAL in APB'.
        clear AG6 G6 ST5 MI5 AG5 PC5' G5 BUF MU WM.
        eapply (implM_retb usegs). cbv beta iota. cbn [negb set_buffer pc_self pc_rfile pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                                                    pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
        hide NEW. hide PRIV. hide HH. hide HD.
        pose proof (munch_refl [(P + 20, P + 32)]%Z m6) as MU. pose proof (wmono_refl usegs m6) as WM.
        unfold implM. iprefix. step. if_cases Kz; try (zify_cond Kz; exfalso; clear - Kz N1 N3 N4; lia).
        step. step.
        unhide NEW. unhide PRIV. unhide HH. unhide HD.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGP : agrees_on (fun a => outside [(P + 20, P + 32)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m6' end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in NEW; [| intros a Ha; cbn [outside cells_size csize] in Ha |- *; clear - Ha APB' W1' W3; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; cbn [outside cells_size csize] in Ha |- *; gio_ceil_fact; clear -CLO__ Ha LO BU R1 SPW L4; unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha LO BU R1 R2 SPW L4; unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in PRIV; [| intros a Ha; cbn [outside cells_size csize] in Ha |- *; clear - Ha; lia].
        assert (G6'' : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (bq', A', snapshot)]) FB m6').
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6' | exact MU | exact WM |].
          apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        assert (AG06' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6').
        { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
          destruct (np_CLc_facts _ _ _ _ G6' Ha) as [Hc Hnb]. split; [| exact Logic.I]. intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        merge_all NEW. replace (Z.to_nat (bufalloc `min` snapshot) + (Z.to_nat (snapshot - bufalloc `min` snapshot) + 0))%nat with (Z.to_nat snapshot) in NEW by (keep_hyps CEILV sp R lo P HA DA B bufalloc bufdata snapshot dw A' bsx' K3; lia). rewrite app_nil_r in NEW.
        apply evt_done. eapply (np_oread _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6' ps6 bq' A' snapshot snapshot (zfirstn snapshot bufdata) errbuf sec usec cap len dw fj);
          [exact ST6 | exact FR5 | exact MI6 | exact G6'' | | exact AG06' | exact HH | exact HD | exact Hd | lia | exact Hsc | exact Hcm | exact Hl32 | congruence].
        exists Afx. split; [exact Hin|]. exists A', 0%Z, jx', padx, (firstn (Z.to_nat (bufalloc `min` snapshot)) bsx' ++ junk6).
        split; [reflexivity|].
        split; [unfold S3.F_sfpcap_nextA.TwB.pv, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF;
                cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
                     pk_next_pcap pk_cleanup_sf PK pc_rfile]; exact CELLS|].
        split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [unfold S3.F_sfpcap_nextA.TwB.pv; cbn [pc_bufalloc]; exact NEW|].
        split; [unfold S3.F_sfpcap_nextA.TwB.pv, zfirstn; cbn [pc_bufdata]; apply pfx_realloc; [exact PFX | lia | lia]|].
        split; [reflexivity|].
        pose proof (zfirstn_length_le2 snapshot bufdata) as ZL. eapply pv_wf; [exact WF | clear - Hsc Hcm MSL W1'; lia | clear - Hsc Hcm MSL W1'; lia | clear - ZL W1'; lia | lia].
      + (* [comment removed for export] *)
        destruct PO as (av & m6 & E & OFr & MI6 & ST6 & AG6 & -> & G6 & BUF6 & EN6).
        unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 0x15c40)) with (Z_to_bv 64 0x15c40) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite app_nil_r in AG6.
        replace ((CLc ++ [(self, P, 664%Z)]) ++ [(buffer, B, bufalloc)]) with (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) in G6 by (rewrite <- app_assoc; reflexivity).
        unhide PRIV. unhide HH. unhide HD.
        assert (KEEP : forall A cs, rw_cells usegs m5 A cs -> ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells usegs m6 A cs).
        { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|HX]; [left; lia| right].
          apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
        apply KEEP in CELLS; [| right; cbn [cells_size csize]; lia]. apply KEEP in PRIV; [| right; cbn [cells_size csize]; lia]. clear KEEP.
        assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
        assert (PC6 : PCAPR (hptr:=hptr) P (pv buffer bufsize bufalloc bufdata errbuf) [(self, P, 664%Z); (buffer, B, bufalloc)] FB m6).
        { exists Afx. split; [exact Hin|]. exists B, 0%Z, jx', padx, bsx'. split; [reflexivity|].
          split; [unfold S3.F_sfpcap_nextA.TwB.pv, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF;
                  cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
                       pk_next_pcap pk_cleanup_sf PK pc_rfile]; exact CELLS|].
          split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [exact BUF6|]. split; [exact PFX|]. split; [reflexivity| exact WF]. }
        clear AG6 ST5 MI5 AG5 PC5' G5 BUF MU WM.
        (* [comment removed for export] *)
        pose proof PC6 as (Afy & _ & (By & Iy & jy & pady & bsy & EPBy & CELLSy & _ & _ & _ & _ & _)).
        apply pcap_cells_split4 in CELLSy as (_ & CE & _ & _); [|reflexivity].
        apply (rw_cells_split_CB usegs m6 _ [] 304 _ [] [14; 242; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
        destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE']. cbn [firstn skipn cells_size csize] in CE1, CE'.
        destruct (rw_cells_cut _ _ _ 1 CE') as [CE2 _]. clear CE CE'. cbn [firstn skipn cells_size csize] in CE2.
        replace (P + 216 + Z.of_nat 14)%Z with (P + 230)%Z in CE2 by lia.
        eapply (implM_retb usegs). cbv beta iota. cbn [negb].
        assert (LENM : length (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) = 14%nat) by (vm_compute; reflexivity).
        hide PRIV. hide HH. hide HD. hide CELLS. hide CE2. hide BUF6.
        pose proof (munch_refl [(P + 216, P + 216 + 14)]%Z m6) as MU. pose proof (wmono_refl usegs m6) as WM.
        unfold implM. iprefix. step. if_true. do 6 step.
        call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P + 216)%Z 0x10df2%Z 14%Z (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) (firstn 14 (pj_g jy)));
          [reflexivity | reflexivity | reflexivity
          | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m6 0x10df2 (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) MI6 ltac:(vm_compute; reflexivity) ltac:((keep_hyps CEILV sp R P HA DA B bufdata dw; lia)) ltac:(rewrite LENM; cbn; (keep_hyps CEILV sp R P HA DA B bufdata dw; lia))))
          | rewrite LENM; reflexivity | (keep_hyps CEILV sp R P HA DA B bufdata dw; lia) | exact CE1 | unfold rc_lo in LO; (keep_hyps CEILV sp R P HA DA B bufdata dw L5; lia) | (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA B self buffer bufalloc bufdata dw m6 ps6 L4; lia) | (keep_hyps CEILV sp R P HA DA B bufdata dw; lia) | exact MI6 |].
        unhide PRIV. unhide HH. unhide HD. unhide CELLS. unhide CE2. unhide BUF6.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P + 216, P + 216 + 14)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGW) in HH; [| intros a Ha; cbn [outside cells_size csize] in *; unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGW) in HD; [| intros a Ha; cbn [outside cells_size csize] in *; unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGW) in CE2; [| intros a Ha; cbn [outside cells_size csize] in *; lia].
        assert (G7 : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU | exact WM |].
          apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        assert (PC7 : PCAPR (hptr:=hptr) P (pv buffer bufsize bufalloc bufdata Msg.out_of_memory) [(self, P, 664%Z); (buffer, B, bufalloc)] FB m7).
        { lazymatch goal with PCm : rw_cells usegs m7 (P + 216)%Z _ |- _ =>
            pose proof (rw_cells_uncut _ _ _ _ _ PCm CE2 ltac:(cbn; lia)) as EB7 end.
          change (pv buffer bufsize bufalloc bufdata Msg.out_of_memory) with (set_errbuf Msg.out_of_memory (pv buffer bufsize bufalloc bufdata errbuf)).
          eapply (PCAPR_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G6 PC6 AGW); [| exact EB7 | rewrite cells_size_app; cbn; lia].
          intros a Ha Hn. cbn [outside]. (keep_hyps CEILV sp R P HA DA B bufdata dw a Hn; lia). }
        assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AGW|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
          destruct (np_CLc_facts _ _ _ _ G6 Ha) as [Hc Hnb]. split; [| exact Logic.I]. intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        step. apply evt_done.
        eapply np_fail_tail; [eassumption | exact FR5 | eassumption | ].
        split; [exact G7|]. split; [unfold S3.F_sfpcap_nextA.TwB.pv in PC7; cbn [set_errbuf] ; exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence].
    - (* [comment removed for export] *)
      apply evt_done. eapply (implM_retb usegs). cbv beta iota. cbn [negb].
      unfold implM. iprefix. step. if_cases Kb; try (zify_cond Kb; exfalso; (keep_hyps CEILV sp R P HA DA B bufsize bufdata cap dw NOGROW Kb; lia)).
      unhide BUF. unhide PRIV. unhide HH. unhide HD.
      apply evt_done. eapply (np_oread _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps buffer B bufsize bufalloc bufdata errbuf sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5' | exact AG5 | exact HH | exact HD | exact Hd | lia | exact Hsc | exact Hcm | exact Hl32 | exact OF5].
  Qed.
  End Sz9.
  Lemma np_over : ltac:(let t := eval cbv delta [np_over__stmt] in np_over__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W7 W8 W9 WHS. all: natfold_lits. intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_over__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpCtxB.

End WithCeil.
End TwB.
End F_sfpcap_nextB.

(* [comment removed for export] *)
Module F_sfpcap_nextC.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_nextA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcap_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_nextA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_nextB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac natfold_term t :=
  match t with
  | context C[4136%nat] => let t1 := context C[Z.to_nat 4136] in natfold_term t1
  | _ => t
  end.
Local Ltac natfold_hyp H := let T := type of H in let U := natfold_term T in change U in H.
Local Ltac natfold_concl := lazymatch goal with |- ?G => let U := natfold_term G in change U end.
Local Ltac natfold_lits :=
  repeat match goal with
  | nfH : context [4136%nat] |- _ => natfold_hyp nfH
  end;
  lazymatch goal with
  | |- context [4136%nat] => natfold_concl
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Local Ltac cl_lit_hyps :=
  repeat match goal with
  | H : context [cells_size ?cs] |- _ =>
      tryif (match goal with H' := _ |- _ => constr_eq H' H end) then fail else
      (sl_spine_closed cs;
       let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
       change (cells_size cs) with n in H)
  end.
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (s32 _) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
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
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section NpCtxC.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA B Af : Z) (m : mem) (o : option hptr).
  Variables (self buffer f : hptr) (bufsize bufalloc : Z) (bufdata : list Z) (swapped : bool)
            (vmaj vmin snapshot linktype ltext prec brk : Z) (errbuf : list Z) (header : pkthdr)
            (hdrsize : Z).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 664 <= CEILZ)%Z.
  Hypothesis P5 : (P + 664 <= 65536 \/ 348160 <= P)%Z.  Hypothesis P6 : (P + 664 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize < 2^32)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.
  Hypothesis WHS : (hdrsize = 16 \/ hdrsize = 24)%Z.
  Hypothesis PPLEN : forall lt sw hdr d, length (snd (pcapint_post_process lt sw hdr d)) = length d.
  Hypothesis PPSEC : forall lt sw hdr d, h_sec (fst (pcapint_post_process lt sw hdr d)) = h_sec hdr /\ h_usec (fst (pcapint_post_process lt sw hdr d)) = h_usec hdr.
  Hypothesis PPRNG : forall lt sw hdr d, (0 <= h_caplen hdr <= Z.of_nat (length d))%Z -> (0 <= h_len hdr < 2^32)%Z -> (Z.of_nat (length d) < 2^31)%Z ->
     (0 <= h_caplen (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z /\ (0 <= h_len (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation np_fail_tail := (F_sfpcap_nextA.np_fail_tail K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation np_snp := (F_sfpcap_nextA.np_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation np_fmt := (F_sfpcap_nextA.np_fmt K FMT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P2 P4).
  #[local] Abbreviation np_CLc_facts := (F_sfpcap_nextA.np_CLc_facts K R CLc FB).
  #[local] Abbreviation np_normal := (fun (lsw : lenswap_t) (scl : sf_scale_t) =>
     F_sfpcap_nextA.np_normal HO K sites HFL SFL HPL HAL FREAD FERROR FMT SNPRINTF REALLOC PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA B Af m o self buffer f bufsize bufalloc bufdata swapped
                               vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize lsw scl
                               LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 HinF P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10 WHS PPLEN PPSEC PPRNG).
  #[local] Abbreviation np_over := (fun (lsw : lenswap_t) (scl : sf_scale_t) =>
     OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_nextB.np_over HO K sites HFL SFL HPL HAL FREAD FERROR FMT SNPRINTF REALLOC PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA B Af m o self buffer f bufsize bufalloc bufdata swapped
                               vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize lsw scl
                               LO BU SPM TP ALN SITES R1 R2 R3 AH AD SPW SP47 HinF P1 P2 P4 P5 P6 W1 W2 W7 W8 W9 W10 WHS PPLEN PPSEC PPRNG).
  #[local] Abbreviation p0 := (F_sfpcap_nextA.p0 self buffer f bufsize bufalloc bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize).

  Ltac norm_p :=
    unfold F_sfpcap_nextA.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells
         sf_hdrsize sf_lengths_swapped sf_scale_type ifaces_ok set_bufdata set_errbuf set_buffer] in *;
    unfold PCAP_SF_TOTAL, PCAP_PRIV_OFF in *.

  (* [comment removed for export] *)
  Definition np_dispatch__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap)%Z -> (cap <= max_snaplen_for_dlt linktype)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (if snapshot <? cap then np_over_model MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec cap len) cap len sec usec
                   else np_norm_model MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec cap len) cap) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 cap) (Z_to_bv 64 snapshot) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15644) fc None m5 (seg_rom ssegs)).
  Section Sz1.
  Variables lsw scl ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_dispatch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_dispatch__body : ltac2:(SecDiet.SzSec.bodyP 'np_dispatch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hc0 Hcm Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    hide HH. hide HD. hide FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sextw_small snapshot) by lia.
    destruct (Z.ltb_spec snapshot cap) as [LT|GE].
    - step. if_cases Kc; try (zify_cond Kc; exfalso; clear - Kc LT W1' Hc0 Hcm MSR; lia).
      unhide HH. unhide HD. unhide FR5.
      apply evt_done. eapply (np_over lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact LT | exact Hcm | exact Hl32 | exact OF5].
    - step. if_cases Kc; try (zify_cond Kc; exfalso; clear - Kc GE W1' Hc0 Hcm MSR; lia).
      unhide HH. unhide HD. unhide FR5.
      apply evt_done. eapply (np_normal lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | lia | exact Hcm | exact Hl32 | exact OF5].
  Qed.
  End Sz1.
  Lemma np_dispatch : ltac:(let t := eval cbv delta [np_dispatch__stmt] in np_dispatch__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_dispatch__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_caperr__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap < 2^32)%Z -> (max_snaplen_for_dlt linktype < cap)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (if snapshot <? cap then mret ((-1)%Z, mkHdr sec usec cap len, set_errbuf (Msg.invalid_caplen_snaplen cap snapshot) (p0 lsw scl))
                   else mret ((-1)%Z, mkHdr sec usec cap len, set_errbuf (Msg.invalid_caplen_maximum cap (max_snaplen_for_dlt linktype)) (p0 lsw scl))) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 (max_snaplen_for_dlt linktype)) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 (s32 cap)) (Z_to_bv 64 snapshot) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15610) fc None m5 (seg_rom ssegs)).
  Section Sz2.
  Variables lsw scl ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_caperr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_caperr__body : ltac2:(SecDiet.SzSec.bodyP 'np_caperr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. all: natfold_lits. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9 : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hc32 Hcm Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    pose proof (unsigned_s32 cap Hc32) as US.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & _)).
    unfold F_sfpcap_nextA.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold F_sfpcap_nextA.p0, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
    hide HH. hide HD. hide FR5. hide CELLS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sextw_small snapshot) by lia. step.
    destruct (Z.ltb_spec snapshot cap) as [LT|GE].
    - (* [comment removed for export] *)
      step. if_cases Kc; [ try (zify_cond Kc; exfalso; rewrite ?US in Kc; clear - Kc LT W1' Hc32; unfold s32 in *; destruct (Z.ltb_spec cap (2^31)); lia) | idtac ].
      do 7 step.
      unhide HH. unhide HD. unhide FR5. clear CELLS.
      unfold Msg.invalid_caplen_snaplen, PCAP_ERRBUF_SIZE. rewrite <- snp_caplen_snaplen_s32.
      apply evt_done. eapply np_snp; [exact ST5 | exact FR5 | exact MI5 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
      { split; [exact G5|]. split; [exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| exact OF5]. }
      { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m5 0x1095e (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "invalid packet capture length %u, bigger than snaplen of %d"%string) ++ [Z_to_bv 8 0])
                                   MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
      { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
      pose proof (snprintf_length 256 "invalid packet capture length %u, bigger than snaplen of %d"%string [AInt (s32 cap); AInt snapshot]) as LS.
      change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS.
    - (* [comment removed for export] *)
      step. if_cases Kc; [ idtac | try (zify_cond Kc; exfalso; rewrite ?US in Kc; clear - Kc GE W1' Hc32; unfold s32 in *; destruct (Z.ltb_spec cap (2^31)); lia) ].
      replace (s32 cap) with cap by (clear - GE W1' Hc32; unfold s32; Z.div_mod_to_equations; lia).
      unhide CELLS. step. rewrite (sx32_small linktype) by lia. step. hide CELLS.
      eapply evt_cut. { eapply max_snaplen_proof; [reflexivity | lia]. }
      cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & -> & ->).
      replace (ret_pc (Z_to_bv 64 0x156ec)) with (Z_to_bv 64 0x156ec) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      do 7 step.
      unhide HH. unhide HD. unhide FR5. clear CELLS.
      unfold Msg.invalid_caplen_maximum, PCAP_ERRBUF_SIZE.
      apply evt_done. eapply np_snp; [exact ST5 | exact FR5 | exact MI5 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
      { split; [exact G5|]. split; [exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| exact OF5]. }
      { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m5 0x10721 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "invalid packet capture length %u, bigger than maximum of %u"%string) ++ [Z_to_bv 8 0])
                                   MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
      { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
      pose proof (snprintf_length 256 "invalid packet capture length %u, bigger than maximum of %u"%string [AInt cap; AInt (max_snaplen_for_dlt linktype)]) as LS.
      change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS.
  Qed.
  End Sz2.
  Lemma np_caperr : ltac:(let t := eval cbv delta [np_caperr__stmt] in np_caperr__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_caperr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition np_chk__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 x6 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec cap len cw : Z) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap < 2^32)%Z -> (0 <= len < 2^32)%Z -> (0 <= cw < 2^64)%Z -> (cw mod 2^32 = cap)%Z -> ps_outfile ps = o ->
      implM ssegs (np_tail MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec cap len) cap len sec usec) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 x6 (Z_to_bv 64 cw) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x155f8) fc None m5 (seg_rom ssegs)).
  Section Sz3.
  Variables lsw scl ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 x6 t3' t4' t5' t6' m5 ps sec usec cap len cw dw fj : ltac2:(SecDiet.SzSec.tyM 'np_chk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_chk__body : ltac2:(SecDiet.SzSec.bodyP 'np_chk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hc32 Hl32 Hcw Hcwm OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    pose proof (unsigned_s32 cap Hc32) as US.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & _)).
    unfold F_sfpcap_nextA.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold F_sfpcap_nextA.p0, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
    unfold np_tail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims pc_snapshot pc_linktype F_sfpcap_nextA.p0].
    hide HD. hide FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sx32_small linktype) by lia. step. hide CELLS. hide HH.
    eapply evt_cut. { eapply max_snaplen_proof; [reflexivity | lia]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 0x15600)) with (Z_to_bv 64 0x15600) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide CELLS. unhide HH.
    step. rewrite (sx32_s32 cap) by lia. step. rewrite (zx32_lit snapshot) by lia. step. rewrite (sextw_mod cw) by lia. rewrite Hcwm.
    hide CELLS.
    destruct (Z.ltb_spec (max_snaplen_for_dlt linktype) cap) as [LT|GE].
    - step. if_cases Kc; [ try (zify_cond Kc; exfalso; rewrite ?US in Kc; clear - Kc LT MSR Hc32; unfold s32 in *; destruct (Z.ltb_spec cap (2^31)); lia) | idtac ].
      unhide HD. unhide FR5. clear CELLS.
      apply evt_done. eapply (np_caperr lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact Hc32 | exact LT | exact Hl32 | exact OF5].
    - step. if_cases Kc; [ idtac | try (zify_cond Kc; exfalso; rewrite ?US in Kc; clear - Kc GE MSR Hc32; unfold s32 in *; destruct (Z.ltb_spec cap (2^31)); lia) ].
      unhide HD. unhide FR5. clear CELLS.
      replace (s32 cap) with cap by (symmetry; apply s32_id; lia).
      apply evt_done. eapply (np_dispatch lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | lia | exact GE | exact Hl32 | exact OF5].
  Qed.
  End Sz3.
  Lemma np_chk : ltac:(let t := eval cbv delta [np_chk__stmt] in np_chk__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 x6 t3' t4' t5' t6' m5 ps sec usec cap len cw dw fj. ltac2:(SecDiet.SzSec.closeP 'np_chk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_chkB__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 x6 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec cap len cw : Z) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap < 2^32)%Z -> (0 <= len < 2^32)%Z -> (0 <= cw < 2^64)%Z -> (cw mod 2^32 = cap)%Z -> ps_outfile ps = o ->
      implM ssegs (np_tail MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec cap len) cap len sec usec) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 x6 (Z_to_bv 64 cw) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1562c) fc None m5 (seg_rom ssegs)).
  Section Sz4.
  Variables lsw scl ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 x6 t3' t4' t5' t6' m5 ps sec usec cap len cw dw fj : ltac2:(SecDiet.SzSec.tyM 'np_chkB__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_chkB__body : ltac2:(SecDiet.SzSec.bodyP 'np_chkB__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hc32 Hl32 Hcw Hcwm OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    pose proof (unsigned_s32 cap Hc32) as US.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & _)).
    unfold F_sfpcap_nextA.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold F_sfpcap_nextA.p0, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
    unfold np_tail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims pc_snapshot pc_linktype F_sfpcap_nextA.p0].
    hide HD. hide FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sx32_small linktype) by lia. step. hide CELLS. hide HH.
    eapply evt_cut. { eapply max_snaplen_proof; [reflexivity | lia]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 0x15634)) with (Z_to_bv 64 0x15634) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide CELLS. unhide HH.
    step. rewrite (sx32_s32 cap) by lia. step. rewrite (zx32_lit snapshot) by lia. step. rewrite (sextw_mod cw) by lia. rewrite Hcwm.
    hide CELLS.
    destruct (Z.ltb_spec (max_snaplen_for_dlt linktype) cap) as [LT|GE].
    - step. if_cases Kc; [ idtac | try (zify_cond Kc; exfalso; rewrite ?US in Kc; clear - Kc LT MSR Hc32; unfold s32 in *; destruct (Z.ltb_spec cap (2^31)); lia) ].
      unhide HD. unhide FR5. clear CELLS.
      apply evt_done. eapply (np_caperr lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact Hc32 | exact LT | exact Hl32 | exact OF5].
    - step. if_cases Kc; [ try (zify_cond Kc; exfalso; rewrite ?US in Kc; clear - Kc GE MSR Hc32; unfold s32 in *; destruct (Z.ltb_spec cap (2^31)); lia) | idtac ].
      unhide HD. unhide FR5. clear CELLS.
      replace (s32 cap) with cap by (symmetry; apply s32_id; lia).
      apply evt_done. eapply (np_dispatch lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | lia | exact GE | exact Hl32 | exact OF5].
  Qed.
  End Sz4.
  Lemma np_chkB : ltac:(let t := eval cbv delta [np_chkB__stmt] in np_chkB__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 x6 t3' t4' t5' t6' m5 ps sec usec cap len cw dw fj. ltac2:(SecDiet.SzSec.closeP 'np_chkB__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_lsw__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec capr lenr capx lenx : Z) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 capr); C4 (Z_to_bv 64 lenr)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= capx < 2^64)%Z -> (0 <= lenx < 2^64)%Z -> (capx mod 2^32 = capr)%Z -> (lenx mod 2^32 = lenr)%Z -> ps_outfile ps = o ->
      implM ssegs (let '(caplen, len) := match lsw with
                                        | NOT_SWAPPED => (capr, lenr)
                                        | MAYBE_SWAPPED => if capr <=? lenr then (capr, lenr) else (lenr, capr)
                                        | SWAPPED => (lenr, capr)
                                        end in
                   np_tail MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec caplen len) caplen len sec usec) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 capx) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 lenx) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x155d0) fc None m5 (seg_rom ssegs)).
  Section Sz5.
  Variables lsw scl ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec capr lenr capx lenx dw fj : ltac2:(SecDiet.SzSec.tyM 'np_lsw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_lsw__body : ltac2:(SecDiet.SzSec.bodyP 'np_lsw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hcx Hlx Hcr Hlr OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof W1 as W1'. unfold INT_MAX in W1'.
    assert (Rc : (0 <= capr < 2^32)%Z) by (rewrite <- Hcr; clear; Z.div_mod_to_equations; lia).
    assert (Rl : (0 <= lenr < 2^32)%Z) by (rewrite <- Hlr; clear; Z.div_mod_to_equations; lia).
    pose proof (unsigned_s32 capr Rc) as US1. pose proof (unsigned_s32 lenr Rl) as US2.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & _ & PRIV & _)).
    unfold F_sfpcap_nextA.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold F_sfpcap_nextA.p0, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV. cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    destruct (rw_cells_cut _ _ _ 3 PRIV) as [PRIV3 _]. clear PRIV. cbn [firstn] in PRIV3. rename PRIV3 into PRIV.
    (* [comment removed for export] *)
    assert (KSW : forall (a1v a2v : word) (mx : mem), mx = m5 ->
      implM ssegs (np_tail MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec lenr capr) lenr capr sec usec) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 capx) a1v a2v a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 lenx) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x155f0) fc None mx (seg_rom ssegs))).
    { intros a1v a2v mx ->.
      hide HD. hide FR5. hide PRIV.
      pose proof (munch_refl [(HA + 16, HA + 24)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
      unfold implM. iprefix. step. step.
      unhide HD. unhide FR5. unhide PRIV.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGP : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
        rename mm into m6 end.
      apply (agrees_rw_cells _ _ _ _ _ AGP) in FR5; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); clear - Ha R1; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R2; lia].
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |].
        apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo. lia. }
      assert (PC6 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m6).
      { eapply PCAPR_agree; [exact AGP | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. lia. }
      assert (HH6 : rw_cells ssegs m6 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 lenr); C4 (Z_to_bv 64 capr)]).
      { eapply rw_cells_recell; [exact HH | cbn; repeat split; exact Logic.I |].
        cbn [cells_bytes cbytes app]. rewrite (le4_mod32 lenx), (le4_mod32 capx), Hcr, Hlr by lia. reflexivity. }
      clear HH.
      apply evt_done. eapply (np_chk lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps sec usec lenr capr lenx dw fj);
        [eassumption | exact FR5 | eassumption | exact G6 | exact PC6 | exact AG6 | exact HH6 | exact HD | exact Hd | exact Rl | exact Rc | exact Hlx | exact Hlr | exact OF5]. }
    hide HD. hide FR5. hide HH.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sx32_small (lenswap_code lsw)) by (destruct lsw; cbn; lia). step.
    destruct lsw; cbn [lenswap_code].
    - (* [comment removed for export] *)
      step. if_false. step. step. if_true. step.
      unhide HD. unhide FR5. unhide HH.
      apply evt_done. eapply (np_chkB NOT_SWAPPED scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec capr lenr capx dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact Rc | exact Rl | exact Hcx | exact Hcr | exact OF5].
    - (* [comment removed for export] *)
      step. if_true. unhide HD. unhide FR5. unhide HH. apply evt_done. apply (KSW _ _ m5 eq_refl).
    - (* [comment removed for export] *)
      step. if_false. step. step. if_false.
      step. rewrite (sextw_mod capx) by lia. rewrite Hcr. step. rewrite (sextw_mod lenx) by lia. rewrite Hlr.
      destruct (Z.leb_spec capr lenr) as [LE|GT].
      + step. if_cases Kc; [ idtac | try (zify_cond Kc; exfalso; rewrite ?US1, ?US2 in Kc; clear - Kc LE Rc Rl; unfold s32 in *;
                                 destruct (Z.ltb_spec capr (2^31)); destruct (Z.ltb_spec lenr (2^31)); lia) ].
        step. unhide HD. unhide FR5. unhide HH.
        apply evt_done. eapply (np_chkB MAYBE_SWAPPED scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec capr lenr capx dw fj);
          [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact Rc | exact Rl | exact Hcx | exact Hcr | exact OF5].
      + step. if_cases Kc; [ try (zify_cond Kc; exfalso; rewrite ?US1, ?US2 in Kc; clear - Kc GT Rc Rl; unfold s32 in *;
                                 destruct (Z.ltb_spec capr (2^31)); destruct (Z.ltb_spec lenr (2^31)); lia) | idtac ].
        unhide HD. unhide FR5. unhide HH. apply evt_done. apply (KSW _ _ m5 eq_refl).
  Qed.
  End Sz5.
  Lemma np_lsw : ltac:(let t := eval cbv delta [np_lsw__stmt] in np_lsw__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec capr lenr capx lenx dw fj. ltac2:(SecDiet.SzSec.closeP 'np_lsw__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition np_body__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t)
           (ra' t0' t1' t2' a1' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (secx usecx capx lenx : Z) (hcs : list cell) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= secx < 2^64)%Z -> (0 <= usecx < 2^64)%Z -> (0 <= capx < 2^64)%Z -> (0 <= lenx < 2^64)%Z -> ps_outfile ps = o ->
      implM ssegs (np_body_model MOps (prims HO fo_nop sites) (p0 lsw scl) (secx mod 2^32) (usecx mod 2^32) (capx mod 2^32) (lenx mod 2^32)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 capx) a1' (Z_to_bv 64 secx) (Z_to_bv 64 usecx) a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 lenx) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15558) fc None m5 (seg_rom ssegs)).
  Section Sz6.
  Variables lsw scl ra' t0' t1' t2' a1' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps secx usecx capx lenx hcs dw fj : ltac2:(SecDiet.SzSec.tyM 'np_body__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_body__body : ltac2:(SecDiet.SzSec.bodyP 'np_body__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd Hsx Hux Hcx Hlx OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof W1 as W1'. unfold INT_MAX in W1'.
    assert (Rs : (0 <= secx mod 2^32 < 2^32)%Z) by (clear; Z.div_mod_to_equations; lia).
    assert (Ru : (0 <= usecx mod 2^32 < 2^32)%Z) by (clear; Z.div_mod_to_equations; lia).
    assert (Rc : (0 <= capx mod 2^32 < 2^32)%Z) by (clear; Z.div_mod_to_equations; lia).
    assert (Rl : (0 <= lenx mod 2^32 < 2^32)%Z) by (clear; Z.div_mod_to_equations; lia).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & _ & PRIV & _)).
    unfold F_sfpcap_nextA.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold F_sfpcap_nextA.p0, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV. cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    destruct (rw_cells_cut _ _ _ 3 PRIV) as [PRIV3 _]. clear PRIV. cbn [firstn] in PRIV3. rename PRIV3 into PRIV.
    (* [comment removed for export] *)
    rewrite <- (app_nil_r hcs) in HH. apply (rw_cells_merge ssegs m5 HA [] hcs []) in HH. cbn [app] in HH. rewrite Hh in HH.
    unfold np_body_model. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [sf_of pc_priv sf_scale_type sf_lengths_swapped F_sfpcap_nextA.p0].
    (* [comment removed for export] *)
    assert (K94 : forall (a1v a2v a3v a4v a5v : word) (usec' : Z) (m6 : mem),
      munch [(HA, HA + 24)]%Z m5 m6 -> wmono ssegs m5 m6 -> mem_inv ssegs m6 -> stk ssegs m6 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m6 HA [C8 (Z_to_bv 64 (secx mod 2^32)); C8 (Z_to_bv 64 usec'); C4 (Z_to_bv 64 capx); C4 (Z_to_bv 64 lenx)] ->
      implM ssegs (let '(caplen, len) := match lsw with
                                        | NOT_SWAPPED => ((capx mod 2^32)%Z, (lenx mod 2^32)%Z)
                                        | MAYBE_SWAPPED => if (capx mod 2^32 <=? lenx mod 2^32)%Z then ((capx mod 2^32)%Z, (lenx mod 2^32)%Z) else ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                        | SWAPPED => ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                        end in
                   np_tail MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr (secx mod 2^32) usec' caplen len) caplen len (secx mod 2^32) usec') ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 capx) a1v a2v a3v a4v a5v a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 lenx) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x155d0) fc None m6 (seg_rom ssegs))).
    { intros a1v a2v a3v a4v a5v usec' m6 MU WM MI6 ST6 HH6.
      assert (AGP : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      pose proof FR5 as FR6. apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); clear - Ha R1; lia].
      pose proof HD as HD6. apply (agrees_rw_cells _ _ _ _ _ AGP) in HD6; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R2; lia].
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |].
        apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo. lia. }
      assert (PC6 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m6).
      { eapply PCAPR_agree; [exact AGP | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. lia. }
      assert (HH6' : rw_cells ssegs m6 HA [C8 (Z_to_bv 64 (secx mod 2^32)); C8 (Z_to_bv 64 usec'); C4 (Z_to_bv 64 (capx mod 2^32)); C4 (Z_to_bv 64 (lenx mod 2^32))]).
      { eapply rw_cells_recell; [exact HH6 | cbn; repeat split; exact Logic.I |].
        cbn [cells_bytes cbytes app]. rewrite (le4_mod32 lenx), (le4_mod32 capx) by lia. reflexivity. }
      eapply (np_lsw lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps (secx mod 2^32) usec' (capx mod 2^32) (lenx mod 2^32) capx lenx dw fj);
        [exact ST6 | exact FR6 | exact MI6 | exact G6 | exact PC6 | exact AG6 | exact HH6' | exact HD6 | exact Hd | exact Hcx | exact Hlx | reflexivity | reflexivity | exact OF5]. }
    hide FR5. hide HD.
    pose proof (munch_refl [(HA, HA + 24)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. step. step. rewrite (sx32_small (sfscale_code scl)) by (destruct scl; cbn; lia). step.
    step. rewrite (zext32_shifts_mod usecx) by lia. step. rewrite (zext32_shifts_mod secx) by lia.
    step. step. step. step.
    destruct scl; cbn [sfscale_code].
    - (* [comment removed for export] *)
      step. if_false. step. step. if_true.
      apply evt_done. eapply K94; [exact MU | exact WM | eassumption | eassumption | exact HH].
    - (* [comment removed for export] *)
      step. if_false. step. step. if_false. step. step.
      fastfirst (first [ noevar_assumption | rewrite (usec_mul1000_word (usecx mod 2^32)) by lia
            | replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usecx mod 2 ^ 32)) * 1000))%Z with (Z_to_bv 64 ((usecx mod 2^32) * 1000))%Z by (rewrite unsigned_lit by lia; reflexivity)
            | idtac ]).
      step. step.
      apply evt_done. eapply K94; [exact MU | exact WM | eassumption | eassumption | exact HH].
    - (* [comment removed for export] *)
      step. if_true. step. step. step. step. step. rewrite (usec_div1000_word usecx) by lia. step.
      apply evt_done. eapply K94; [exact MU | exact WM | eassumption | eassumption | exact HH].
  Qed.
  End Sz6.
  Lemma np_body : ltac:(let t := eval cbv delta [np_body__stmt] in np_body__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a1' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps secx usecx capx lenx hcs dw fj. ltac2:(SecDiet.SzSec.closeP 'np_body__body "vvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpCtxC.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_nextA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcap_nextA2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_nextB.TwB.
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
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section NpCtxC.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA B Af : Z) (m : mem) (o : option hptr).
  Variables (self buffer f : hptr) (bufsize bufalloc : Z) (bufdata : list Z) (swapped : bool)
            (vmaj vmin snapshot linktype ltext prec brk : Z) (errbuf : list Z) (header : pkthdr)
            (hdrsize : Z).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 664 <= CEILZ)%Z.
  Hypothesis P5 : (P + 664 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 664 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize < 2^32)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.
  Hypothesis WHS : (hdrsize = 16 \/ hdrsize = 24)%Z.
  Hypothesis PPLEN : forall lt sw hdr d, length (snd (pcapint_post_process lt sw hdr d)) = length d.
  Hypothesis PPSEC : forall lt sw hdr d, h_sec (fst (pcapint_post_process lt sw hdr d)) = h_sec hdr /\ h_usec (fst (pcapint_post_process lt sw hdr d)) = h_usec hdr.
  Hypothesis PPRNG : forall lt sw hdr d, (0 <= h_caplen hdr <= Z.of_nat (length d))%Z -> (0 <= h_len hdr < 2^32)%Z -> (Z.of_nat (length d) < 2^31)%Z ->
     (0 <= h_caplen (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z /\ (0 <= h_len (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation np_fail_tail := (S3.F_sfpcap_nextA.TwB.np_fail_tail K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation np_snp := (S3.F_sfpcap_nextA.TwB.np_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation np_fmt := (S3.F_sfpcap_nextA.TwB.np_fmt K FMT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P2 P4).
  #[local] Abbreviation np_CLc_facts := (S3.F_sfpcap_nextA.TwB.np_CLc_facts K R CLc FB).
  #[local] Abbreviation np_normal := (fun (lsw : lenswap_t) (scl : sf_scale_t) =>
     OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcap_nextA2.np_normal HO K sites HFL SFL HPL HAL FREAD FERROR FMT SNPRINTF REALLOC PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA B Af m o self buffer f bufsize bufalloc bufdata swapped
                               vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize lsw scl
                               LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 HinF P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10 WHS PPLEN PPSEC PPRNG).
  #[local] Abbreviation np_over := (fun (lsw : lenswap_t) (scl : sf_scale_t) =>
     OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_nextB.TwB.np_over HO K sites HFL SFL HPL HAL FREAD FERROR FMT SNPRINTF REALLOC PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA B Af m o self buffer f bufsize bufalloc bufdata swapped
                               vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize lsw scl
                               LO BU SPM TP ALN SITES R1 R2 R3 AH AD SPW SP47 HinF P1 P2 P4 P5 P6 W1 W2 W7 W8 W9 W10 WHS PPLEN PPSEC PPRNG).
  #[local] Abbreviation p0 := (S3.F_sfpcap_nextA.TwB.p0 self buffer f bufsize bufalloc bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize).

  Ltac norm_p :=
    unfold S3.F_sfpcap_nextA.TwB.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells
         sf_hdrsize sf_lengths_swapped sf_scale_type ifaces_ok set_bufdata set_errbuf set_buffer] in *;
    unfold PCAP_SF_TOTAL, PCAP_PRIV_OFF in *.

  (* [comment removed for export] *)
  Definition np_dispatch__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap)%Z -> (cap <= max_snaplen_for_dlt linktype)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (if snapshot <? cap then np_over_model MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec cap len) cap len sec usec
                   else np_norm_model MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec cap len) cap) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 cap) (Z_to_bv 64 snapshot) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15c24) fc None m5 (seg_rom usegs)).
  Section Sz1.
  Variables lsw scl ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_dispatch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_dispatch__body : ltac2:(SecDiet.SzSec.bodyP 'np_dispatch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hc0 Hcm Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    hide HH. hide HD. hide FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sextw_small snapshot) by lia.
    destruct (Z.ltb_spec snapshot cap) as [LT|GE].
    - step. if_cases Kc; try (zify_cond Kc; exfalso; clear - Kc LT W1' Hc0 Hcm MSR; lia).
      unhide HH. unhide HD. unhide FR5.
      apply evt_done. eapply (np_over lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact LT | exact Hcm | exact Hl32 | exact OF5].
    - step. if_cases Kc; try (zify_cond Kc; exfalso; clear - Kc GE W1' Hc0 Hcm MSR; lia).
      unhide HH. unhide HD. unhide FR5.
      apply evt_done. eapply (np_normal lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | lia | exact Hcm | exact Hl32 | exact OF5].
  Qed.
  End Sz1.
  Lemma np_dispatch : ltac:(let t := eval cbv delta [np_dispatch__stmt] in np_dispatch__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_dispatch__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_caperr__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap < 2^32)%Z -> (max_snaplen_for_dlt linktype < cap)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (if snapshot <? cap then mret ((-1)%Z, mkHdr sec usec cap len, set_errbuf (Msg.invalid_caplen_snaplen cap snapshot) (p0 lsw scl))
                   else mret ((-1)%Z, mkHdr sec usec cap len, set_errbuf (Msg.invalid_caplen_maximum cap (max_snaplen_for_dlt linktype)) (p0 lsw scl))) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 (max_snaplen_for_dlt linktype)) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 (s32 cap)) (Z_to_bv 64 snapshot) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15c0c) fc None m5 (seg_rom usegs)).
  Section Sz2.
  Variables lsw scl ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_caperr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_caperr__body : ltac2:(SecDiet.SzSec.bodyP 'np_caperr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. all: natfold_lits. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9 : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hc32 Hcm Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    pose proof (unsigned_s32 cap Hc32) as US.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & _)).
    unfold S3.F_sfpcap_nextA.TwB.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold S3.F_sfpcap_nextA.TwB.p0, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
    hide HH. hide HD. hide FR5. hide CELLS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sextw_small snapshot) by lia. step.
    destruct (Z.ltb_spec snapshot cap) as [LT|GE].
    - (* [comment removed for export] *)
      step. if_cases Kc; [ try (zify_cond Kc; exfalso; rewrite ?US in Kc; clear - Kc LT W1' Hc32; unfold s32 in *; destruct (Z.ltb_spec cap (2^31)); lia) | idtac ].
      do 7 step.
      unhide HH. unhide HD. unhide FR5. clear CELLS.
      unfold Msg.invalid_caplen_snaplen, PCAP_ERRBUF_SIZE. rewrite <- snp_caplen_snaplen_s32.
      apply evt_done. eapply np_snp; [exact ST5 | exact FR5 | exact MI5 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
      { split; [exact G5|]. split; [exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| exact OF5]. }
      { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m5 0x1095e (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "invalid packet capture length %u, bigger than snaplen of %d"%string) ++ [Z_to_bv 8 0])
                                   MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
      { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
      pose proof (snprintf_length 256 "invalid packet capture length %u, bigger than snaplen of %d"%string [AInt (s32 cap); AInt snapshot]) as LS.
      change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS.
    - (* [comment removed for export] *)
      step. if_cases Kc; [ idtac | try (zify_cond Kc; exfalso; rewrite ?US in Kc; clear - Kc GE W1' Hc32; unfold s32 in *; destruct (Z.ltb_spec cap (2^31)); lia) ].
      replace (s32 cap) with cap by (clear - GE W1' Hc32; unfold s32; Z.div_mod_to_equations; lia).
      unhide CELLS. step. rewrite (sx32_small linktype) by lia. step. hide CELLS.
      eapply evt_cut. { eapply max_snaplen_proof; [reflexivity | lia]. }
      cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & -> & ->).
      replace (ret_pc (Z_to_bv 64 0x15ccc)) with (Z_to_bv 64 0x15ccc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      do 7 step.
      unhide HH. unhide HD. unhide FR5. clear CELLS.
      unfold Msg.invalid_caplen_maximum, PCAP_ERRBUF_SIZE.
      apply evt_done. eapply np_snp; [exact ST5 | exact FR5 | exact MI5 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
      { split; [exact G5|]. split; [exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| exact OF5]. }
      { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m5 0x10721 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "invalid packet capture length %u, bigger than maximum of %u"%string) ++ [Z_to_bv 8 0])
                                   MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
      { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
      pose proof (snprintf_length 256 "invalid packet capture length %u, bigger than maximum of %u"%string [AInt cap; AInt (max_snaplen_for_dlt linktype)]) as LS.
      change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS.
  Qed.
  End Sz2.
  Lemma np_caperr : ltac:(let t := eval cbv delta [np_caperr__stmt] in np_caperr__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_caperr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_chk__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 x6 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec cap len cw : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap < 2^32)%Z -> (0 <= len < 2^32)%Z -> (0 <= cw < 2^64)%Z -> (cw mod 2^32 = cap)%Z -> ps_outfile ps = o ->
      implM usegs (np_tail MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec cap len) cap len sec usec) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 x6 (Z_to_bv 64 cw) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15bf4) fc None m5 (seg_rom usegs)).
  Section Sz3.
  Variables lsw scl ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 x6 t3' t4' t5' t6' m5 ps sec usec cap len cw dw fj : ltac2:(SecDiet.SzSec.tyM 'np_chk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_chk__body : ltac2:(SecDiet.SzSec.bodyP 'np_chk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hc32 Hl32 Hcw Hcwm OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    pose proof (unsigned_s32 cap Hc32) as US.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & _)).
    unfold S3.F_sfpcap_nextA.TwB.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold S3.F_sfpcap_nextA.TwB.p0, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
    unfold np_tail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims pc_snapshot pc_linktype S3.F_sfpcap_nextA.TwB.p0].
    hide HD. hide FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sx32_small linktype) by lia. step. hide CELLS. hide HH.
    eapply evt_cut. { eapply max_snaplen_proof; [reflexivity | lia]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & -> & ->).
    replace (ret_pc (Z_to_bv 64 0x15bfc)) with (Z_to_bv 64 0x15bfc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide CELLS. unhide HH.
    step. rewrite (sx32_s32 cap) by lia. step. rewrite (zx32_lit snapshot) by lia. step. rewrite (sextw_mod cw) by lia. rewrite Hcwm.
    hide CELLS.
    destruct (Z.ltb_spec (max_snaplen_for_dlt linktype) cap) as [LT|GE].
    - step. if_cases Kc; [ try (zify_cond Kc; exfalso; rewrite ?US in Kc; clear - Kc LT MSR Hc32; unfold s32 in *; destruct (Z.ltb_spec cap (2^31)); lia) | idtac ].
      unhide HD. unhide FR5. clear CELLS.
      apply evt_done. eapply (np_caperr lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact Hc32 | exact LT | exact Hl32 | exact OF5].
    - step. if_cases Kc; [ idtac | try (zify_cond Kc; exfalso; rewrite ?US in Kc; clear - Kc GE MSR Hc32; unfold s32 in *; destruct (Z.ltb_spec cap (2^31)); lia) ].
      unhide HD. unhide FR5. clear CELLS.
      replace (s32 cap) with cap by (symmetry; apply s32_id; lia).
      apply evt_done. eapply (np_dispatch lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | lia | exact GE | exact Hl32 | exact OF5].
  Qed.
  End Sz3.
  Lemma np_chk : ltac:(let t := eval cbv delta [np_chk__stmt] in np_chk__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x4 x5 x6 t3' t4' t5' t6' m5 ps sec usec cap len cw dw fj. ltac2:(SecDiet.SzSec.closeP 'np_chk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_lsw__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec capr lenr capx lenx : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 capr); C4 (Z_to_bv 64 lenr)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= capx < 2^64)%Z -> (0 <= lenx < 2^64)%Z -> (capx mod 2^32 = capr)%Z -> (lenx mod 2^32 = lenr)%Z -> ps_outfile ps = o ->
      implM usegs (let '(caplen, len) := match lsw with
                                        | NOT_SWAPPED => (capr, lenr)
                                        | MAYBE_SWAPPED => if capr <=? lenr then (capr, lenr) else (lenr, capr)
                                        | SWAPPED => (lenr, capr)
                                        end in
                   np_tail MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec caplen len) caplen len sec usec) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 capx) (Z_to_bv 64 0) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 lenx) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15b7c) fc None m5 (seg_rom usegs)).
  Section Sz4.
  Variables lsw scl ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec capr lenr capx lenx dw fj : ltac2:(SecDiet.SzSec.tyM 'np_lsw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_lsw__body : ltac2:(SecDiet.SzSec.bodyP 'np_lsw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hcx Hlx Hcr Hlr OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof W1 as W1'. unfold INT_MAX in W1'.
    assert (Rc : (0 <= capr < 2^32)%Z) by (rewrite <- Hcr; clear; Z.div_mod_to_equations; lia).
    assert (Rl : (0 <= lenr < 2^32)%Z) by (rewrite <- Hlr; clear; Z.div_mod_to_equations; lia).
    pose proof (unsigned_s32 capr Rc) as US1. pose proof (unsigned_s32 lenr Rl) as US2.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & _ & PRIV & _)).
    unfold S3.F_sfpcap_nextA.TwB.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold S3.F_sfpcap_nextA.TwB.p0, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV. cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    destruct (rw_cells_cut _ _ _ 3 PRIV) as [PRIV3 _]. clear PRIV. cbn [firstn] in PRIV3. rename PRIV3 into PRIV.
    (* [comment removed for export] *)
    assert (KSW : forall (a1v a2v a3v : word) (mx : mem), mx = m5 ->
      implM usegs (np_tail MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec lenr capr) lenr capr sec usec) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 capx) a1v a2v a3v a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 lenx) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15bd4) fc None mx (seg_rom usegs))).
    { intros a1v a2v a3v mx ->.
      hide HD. hide FR5. hide PRIV.
      pose proof (munch_refl [(HA + 16, HA + 24)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
      unfold implM. iprefix. step. step. step. step. if_true.
      unhide HD. unhide FR5. unhide PRIV.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGP : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
        rename mm into m6 end.
      apply (agrees_rw_cells _ _ _ _ _ AGP) in FR5; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); clear - Ha R1; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R2; lia].
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |].
        apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo. lia. }
      assert (PC6 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m6).
      { eapply PCAPR_agree; [exact AGP | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. lia. }
      assert (HH6 : rw_cells usegs m6 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 lenr); C4 (Z_to_bv 64 capr)]).
      { eapply rw_cells_recell; [exact HH | cbn; repeat split; exact Logic.I |].
        cbn [cells_bytes cbytes app]. rewrite (le4_mod32 lenx), (le4_mod32 capx), Hcr, Hlr by lia. reflexivity. }
      clear HH.
      apply evt_done. eapply (np_chk lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps sec usec lenr capr lenx dw fj);
        [eassumption | exact FR5 | eassumption | exact G6 | exact PC6 | exact AG6 | exact HH6 | exact HD | exact Hd | exact Rl | exact Rc | exact Hlx | exact Hlr | exact OF5]. }
    hide HD. hide FR5. hide HH.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sx32_small (lenswap_code lsw)) by (destruct lsw; cbn; lia). step.
    destruct lsw; cbn [lenswap_code].
    - (* [comment removed for export] *)
      step. if_false. step. step. if_true. step. step. step. if_false.
      unhide HD. unhide FR5. unhide HH.
      apply evt_done. eapply (np_chk NOT_SWAPPED scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec capr lenr capx dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact Rc | exact Rl | exact Hcx | exact Hcr | exact OF5].
    - (* [comment removed for export] *)
      step. if_true. step. if_false. unhide HD. unhide FR5. unhide HH. apply evt_done. apply (KSW _ _ _ m5 eq_refl).
    - (* [comment removed for export] *)
      step. if_false. step. step. if_false. step. if_false.
      step. rewrite (sextw_mod capx) by lia. rewrite Hcr. step. rewrite (sextw_mod lenx) by lia. rewrite Hlr.
      destruct (Z.leb_spec capr lenr) as [LE|GT].
      + step. if_cases Kc; [ try (zify_cond Kc; exfalso; rewrite ?US1, ?US2 in Kc; clear - Kc LE Rc Rl; unfold s32 in *;
                                 destruct (Z.ltb_spec capr (2^31)); destruct (Z.ltb_spec lenr (2^31)); lia) | idtac ].
        step. step. step. if_true. unhide HD. unhide FR5. unhide HH.
        apply evt_done. eapply (np_chk MAYBE_SWAPPED scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps sec usec capr lenr capx dw fj);
          [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact Rc | exact Rl | exact Hcx | exact Hcr | exact OF5].
      + step. if_cases Kc; [ idtac | try (zify_cond Kc; exfalso; rewrite ?US1, ?US2 in Kc; clear - Kc GT Rc Rl; unfold s32 in *;
                                 destruct (Z.ltb_spec capr (2^31)); destruct (Z.ltb_spec lenr (2^31)); lia) ].
        unhide HD. unhide FR5. unhide HH. apply evt_done. apply (KSW _ _ _ m5 eq_refl).
  Qed.
  End Sz4.
  Lemma np_lsw : ltac:(let t := eval cbv delta [np_lsw__stmt] in np_lsw__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec capr lenr capx lenx dw fj. ltac2:(SecDiet.SzSec.closeP 'np_lsw__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition np_scale_up__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t) (ra' t0' t1' t2' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec capx lenx : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 capx); C4 (Z_to_bv 64 lenx)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= sec < 2^32)%Z -> (0 <= usec < 2^32)%Z -> (0 <= capx < 2^64)%Z -> (0 <= lenx < 2^64)%Z -> scl <> SF_SCALE_DOWN -> ps_outfile ps = o ->
      implM usegs (np_body_model MOps (prims HO fo_nop sites) (p0 lsw scl) sec usec (capx mod 2^32) (lenx mod 2^32)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 capx) (Z_to_bv 64 0) (Z_to_bv 64 (sfscale_code scl)) (Z_to_bv 64 usec) a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 lenx) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15ae0) fc None m5 (seg_rom usegs)).
  Section Sz5.
  Variables lsw scl ra' t0' t1' t2' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec capx lenx dw fj : ltac2:(SecDiet.SzSec.tyM 'np_scale_up__stmt "vvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_scale_up__body : ltac2:(SecDiet.SzSec.bodyP 'np_scale_up__stmt "vvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hs Hu Hcx Hlx NSD OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold np_body_model. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [sf_of pc_priv sf_scale_type sf_lengths_swapped S3.F_sfpcap_nextA.TwB.p0].
    hide HD. hide FR5.
    pose proof (munch_refl [(HA, HA + 24)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    (* [comment removed for export] *)
    assert (K40 : forall (a2v a4v : word) (usec' : Z) (m6 : mem),
      munch [(HA, HA + 24)]%Z m5 m6 -> wmono usegs m5 m6 -> mem_inv usegs m6 -> stk usegs m6 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m6 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec'); C4 (Z_to_bv 64 capx); C4 (Z_to_bv 64 lenx)] ->
      implM usegs (let '(caplen, len) := match lsw with
                                        | NOT_SWAPPED => ((capx mod 2^32)%Z, (lenx mod 2^32)%Z)
                                        | MAYBE_SWAPPED => if (capx mod 2^32 <=? lenx mod 2^32)%Z then ((capx mod 2^32)%Z, (lenx mod 2^32)%Z) else ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                        | SWAPPED => ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                        end in
                   np_tail MOps (prims HO fo_nop sites) (p0 lsw scl) (mkHdr sec usec' caplen len) caplen len sec usec') ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 capx) (Z_to_bv 64 0) a2v (Z_to_bv 64 usec) a4v a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 lenx) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15b7c) fc None m6 (seg_rom usegs))).
    { intros a2v a4v usec' m6 MU6 WM6 MI6 ST6 HH6. unhide HD. unhide FR5.
      assert (AGP : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      pose proof FR5 as FR6. apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); clear - Ha R1; lia].
      pose proof HD as HD6. apply (agrees_rw_cells _ _ _ _ _ AGP) in HD6; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R2; lia].
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |].
        apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo. lia. }
      assert (PC6 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m6).
      { eapply PCAPR_agree; [exact AGP | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. lia. }
      assert (HH6' : rw_cells usegs m6 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec'); C4 (Z_to_bv 64 (capx mod 2^32)); C4 (Z_to_bv 64 (lenx mod 2^32))]).
      { eapply rw_cells_recell; [exact HH6 | cbn; repeat split; exact Logic.I |].
        cbn [cells_bytes cbytes app]. rewrite (le4_mod32 lenx), (le4_mod32 capx) by lia. reflexivity. }
      eapply (np_lsw lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps sec usec' (capx mod 2^32) (lenx mod 2^32) capx lenx dw fj);
        [exact ST6 | exact FR6 | exact MI6 | exact G6 | exact PC6 | exact AG6 | exact HH6' | exact HD6 | exact Hd | exact Hcx | exact Hlx | reflexivity | reflexivity | exact OF5]. }
    unfold implM. iprefix. step.
    destruct scl; cbn [sfscale_code]; [ | | exfalso; apply NSD; reflexivity].
    - (* [comment removed for export] *)
      step. if_true.
      apply evt_done. eapply K40; [exact MU | exact WM | eassumption | eassumption | exact HH].
    - (* [comment removed for export] *)
      step. if_false. step. if_false. step. step. rewrite (mul_lit_l usec 1000) by lia. step. step.
      apply evt_done. eapply K40; [exact MU | exact WM | eassumption | eassumption | exact HH].
  Qed.
  End Sz5.
  Lemma np_scale_up : ltac:(let t := eval cbv delta [np_scale_up__stmt] in np_scale_up__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec capx lenx dw fj. ltac2:(SecDiet.SzSec.closeP 'np_scale_up__body "vvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_scale_down__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t) (ra' t0' t1' t2' a2' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec capx lenx : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 capx); C4 (Z_to_bv 64 lenx)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= sec < 2^32)%Z -> (0 <= usec < 2^32)%Z -> (0 <= capx < 2^64)%Z -> (0 <= lenx < 2^64)%Z -> scl = SF_SCALE_DOWN -> ps_outfile ps = o ->
      implM usegs (np_body_model MOps (prims HO fo_nop sites) (p0 lsw scl) sec usec (capx mod 2^32) (lenx mod 2^32)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 capx) (Z_to_bv 64 0) a2' (Z_to_bv 64 usec) a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 lenx) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15b64) fc None m5 (seg_rom usegs)).
  Section Sz6.
  Variables lsw scl ra' t0' t1' t2' a2' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec capx lenx dw fj : ltac2:(SecDiet.SzSec.tyM 'np_scale_down__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_scale_down__body : ltac2:(SecDiet.SzSec.bodyP 'np_scale_down__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hs Hu Hcx Hlx -> OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold np_body_model. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [sf_of pc_priv sf_scale_type sf_lengths_swapped S3.F_sfpcap_nextA.TwB.p0].
    hide HD. hide FR5.
    pose proof (munch_refl [(HA, HA + 24)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. if_false. step. step. step. rewrite (mul_lit_l usec 274877907) by lia.
    step. rewrite (usec_div1000_word_u3 usec) by lia. step.
    unhide HD. unhide FR5.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGP : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m6 end.
    apply (agrees_rw_cells _ _ _ _ _ AGP) in FR5; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); clear - Ha R1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R2; lia].
    assert (G6 : GIo K R ps (CLc ++ pcap_blocks (p0 lsw SF_SCALE_DOWN) P B 0) FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |].
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo. lia. }
    assert (PC6 : PCAPR (hptr:=hptr) P (p0 lsw SF_SCALE_DOWN) (pcap_blocks (p0 lsw SF_SCALE_DOWN) P B 0) FB m6).
    { eapply PCAPR_agree; [exact AGP | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
    assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. lia. }
    assert (HH6' : rw_cells usegs m6 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 (usec / 1000)); C4 (Z_to_bv 64 (capx mod 2^32)); C4 (Z_to_bv 64 (lenx mod 2^32))]).
    { eapply rw_cells_recell; [exact HH | cbn; repeat split; exact Logic.I |].
      cbn [cells_bytes cbytes app]. rewrite (le4_mod32 lenx), (le4_mod32 capx) by lia. reflexivity. }
    apply evt_done.
    eapply (np_lsw lsw SF_SCALE_DOWN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps sec (usec / 1000) (capx mod 2^32) (lenx mod 2^32) capx lenx dw fj);
      [eassumption | exact FR5 | eassumption | exact G6 | exact PC6 | exact AG6 | exact HH6' | exact HD | exact Hd | exact Hcx | exact Hlx | reflexivity | reflexivity | exact OF5].
  Qed.
  End Sz6.
  Lemma np_scale_down : ltac:(let t := eval cbv delta [np_scale_down__stmt] in np_scale_down__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a2' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec capx lenx dw fj. ltac2:(SecDiet.SzSec.closeP 'np_scale_down__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_hdr_sw__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t)
           (ra' t0' t1' t2' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (secx usecx capx lenx : Z) (hcs : list cell) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= secx < 2^64)%Z -> (0 <= usecx < 2^64)%Z -> (0 <= capx < 2^64)%Z -> (0 <= lenx < 2^64)%Z -> ps_outfile ps = o ->
      implM usegs (np_body_model MOps (prims HO fo_nop sites) (p0 lsw scl) (secx mod 2^32) (usecx mod 2^32) (capx mod 2^32) (lenx mod 2^32)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 capx) (Z_to_bv 64 0) (Z_to_bv 64 secx) (Z_to_bv 64 usecx) a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 lenx) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15ab4) fc None m5 (seg_rom usegs)).
  Section Sz7.
  Variables lsw scl ra' t0' t1' t2' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps secx usecx capx lenx hcs dw fj : ltac2:(SecDiet.SzSec.tyM 'np_hdr_sw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_hdr_sw__body : ltac2:(SecDiet.SzSec.bodyP 'np_hdr_sw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd Hsx Hux Hcx Hlx OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof W1 as W1'. unfold INT_MAX in W1'.
    assert (Rs : (0 <= secx mod 2^32 < 2^32)%Z) by (clear; Z.div_mod_to_equations; lia).
    assert (Ru : (0 <= usecx mod 2^32 < 2^32)%Z) by (clear; Z.div_mod_to_equations; lia).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & _ & PRIV & _)).
    unfold S3.F_sfpcap_nextA.TwB.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold S3.F_sfpcap_nextA.TwB.p0, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV. cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    destruct (rw_cells_cut _ _ _ 3 PRIV) as [PRIV3 _]. clear PRIV. cbn [firstn] in PRIV3. rename PRIV3 into PRIV.
    (* [comment removed for export] *)
    rewrite <- (app_nil_r hcs) in HH. apply (rw_cells_merge usegs m5 HA [] hcs []) in HH. cbn [app] in HH. rewrite Hh in HH.
    hide FR5. hide HD.
    pose proof (munch_refl [(HA, HA + 24)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    step. step. step. rewrite (zext32_shifts_mod secx) by lia. step. rewrite (zext32_shifts_mod usecx) by lia.
    step. step. step. step.
    step. rewrite (sx32_small (sfscale_code scl)) by (destruct scl; cbn; lia). step.
    unhide FR5. unhide HD.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGP : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m6 end.
    apply (agrees_rw_cells _ _ _ _ _ AGP) in FR5; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); clear - Ha R1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R2; lia].
    assert (G6 : GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |].
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo. lia. }
    assert (PC6 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m6).
    { eapply PCAPR_agree; [exact AGP | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
    assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. lia. }
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
    destruct scl; cbn [sfscale_code].
    - step. if_false. apply evt_done.
      eapply (np_scale_up lsw SF_PASS_THROUGH _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps (secx mod 2^32) (usecx mod 2^32) capx lenx dw fj);
        [eassumption | exact FR5 | eassumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact HD | exact Hd | exact Rs | exact Ru | exact Hcx | exact Hlx | discriminate | exact OF5].
    - step. if_false. apply evt_done.
      eapply (np_scale_up lsw SF_SCALE_UP _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps (secx mod 2^32) (usecx mod 2^32) capx lenx dw fj);
        [eassumption | exact FR5 | eassumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact HD | exact Hd | exact Rs | exact Ru | exact Hcx | exact Hlx | discriminate | exact OF5].
    - step. if_true. apply evt_done.
      eapply (np_scale_down lsw SF_SCALE_DOWN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps (secx mod 2^32) (usecx mod 2^32) capx lenx dw fj);
        [eassumption | exact FR5 | eassumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact HD | exact Hd | exact Rs | exact Ru | exact Hcx | exact Hlx | reflexivity | exact OF5].
  Qed.
  End Sz7.
  Lemma np_hdr_sw : ltac:(let t := eval cbv delta [np_hdr_sw__stmt] in np_hdr_sw__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps secx usecx capx lenx hcs dw fj. ltac2:(SecDiet.SzSec.closeP 'np_hdr_sw__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_unsw__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t)
           (ra' t0' t1' t2' a3' a4' a5' a6' a7' x4 x5 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 : Z) (rest : list cell) (hcs : list cell) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z [g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; g12; g13; g14; g15] ->
      rw_cells usegs m5 (bv_unsigned sp + -96)
        ([C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7)); C4 (Z_to_bv 64 (le4val g8 g9 g10 g11)); C4 (Z_to_bv 64 (le4val g12 g13 g14 g15))] ++ rest) ->
      ps_outfile ps = o ->
      implM usegs (np_body_model MOps (prims HO fo_nop sites) (p0 lsw scl) (le4val g0 g1 g2 g3) (le4val g4 g5 g6 g7) (le4val g8 g9 g10 g11) (le4val g12 g13 g14 g15)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA)
                 (Z_to_bv 64 (sxv g8 g9 g10 g11)) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -88)) a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 (Z_to_bv 64 (P + 648)) x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15b34) fc None m5 (seg_rom usegs)).
  Section Sz8.
  Variables lsw scl ra' t0' t1' t2' a3' a4' a5' a6' a7' x4 x5 x7 t3' t4' t5' t6' m5 ps g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest hcs dw fj : ltac2:(SecDiet.SzSec.tyM 'np_unsw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_unsw__body : ltac2:(SecDiet.SzSec.bodyP 'np_unsw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd GR HB OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof W1 as W1'. unfold INT_MAX in W1'.
    pose proof GR as GR'. do 16 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & _ & PRIV & _)).
    unfold S3.F_sfpcap_nextA.TwB.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold S3.F_sfpcap_nextA.TwB.p0, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV. cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    destruct (rw_cells_cut _ _ _ 3 PRIV) as [PRIV3 _]. clear PRIV. cbn [firstn] in PRIV3. rename PRIV3 into PRIV.
    rewrite <- (app_nil_r hcs) in HH. apply (rw_cells_merge usegs m5 HA [] hcs []) in HH. cbn [app] in HH. rewrite Hh in HH.
    hide FR5. hide HD.
    pose proof (munch_refl [(HA, HA + 24)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    step. if_false_by (eqz_false HA ltac:(clear - R1 R2 R3 SP47 LO BU SPW; unfold rc_lo, rc_spmain in *; lia)). step. if_false.
    step. rewrite (zx32_lit (le4val g0 g1 g2 g3)) by (unfold le4val; lia).
    step. rewrite (zx32_lit (le4val g4 g5 g6 g7)) by (unfold le4val; lia).
    step. rewrite (sx32_lit g12 g13 g14 g15) by lia.
    hide HB.
    step. step. step. step.
    step. rewrite (sx32_small (sfscale_code scl)) by (destruct scl; cbn; lia). step.
    unhide FR5. unhide HD. clear HB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGP : agrees_on (fun a => outside [(HA, HA + 24)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m6 end.
    apply (agrees_rw_cells _ _ _ _ _ AGP) in FR5; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); clear - Ha R1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R2; lia].
    assert (G6 : GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |].
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo. lia. }
    assert (PC6 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m6).
    { eapply PCAPR_agree; [exact AGP | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. unfold rc_lo in LO. lia. }
    assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside]. lia. }
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
    pose proof (sxv_range g8 g9 g10 g11) as X8. pose proof (sxv_range g12 g13 g14 g15) as X12.
    rewrite <- (sxv_mod32 g8 g9 g10 g11), <- (sxv_mod32 g12 g13 g14 g15) by lia.
    destruct scl; cbn [sfscale_code].
    - step. if_true. apply evt_done.
      eapply (np_scale_up lsw SF_PASS_THROUGH _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps (le4val g0 g1 g2 g3) (le4val g4 g5 g6 g7) (sxv g8 g9 g10 g11) (sxv g12 g13 g14 g15) dw fj);
        [eassumption | exact FR5 | eassumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact HD | exact Hd | unfold le4val; lia | unfold le4val; lia | lia | lia | discriminate | exact OF5].
    - step. if_true. apply evt_done.
      eapply (np_scale_up lsw SF_SCALE_UP _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps (le4val g0 g1 g2 g3) (le4val g4 g5 g6 g7) (sxv g8 g9 g10 g11) (sxv g12 g13 g14 g15) dw fj);
        [eassumption | exact FR5 | eassumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact HD | exact Hd | unfold le4val; lia | unfold le4val; lia | lia | lia | discriminate | exact OF5].
    - step. if_false. apply evt_done.
      eapply (np_scale_down lsw SF_SCALE_DOWN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps (le4val g0 g1 g2 g3) (le4val g4 g5 g6 g7) (sxv g8 g9 g10 g11) (sxv g12 g13 g14 g15) dw fj);
        [eassumption | exact FR5 | eassumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact HD | exact Hd | unfold le4val; lia | unfold le4val; lia | lia | lia | reflexivity | exact OF5].
  Qed.
  End Sz8.
  Lemma np_unsw : ltac:(let t := eval cbv delta [np_unsw__stmt] in np_unsw__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl ra' t0' t1' t2' a3' a4' a5' a6' a7' x4 x5 x7 t3' t4' t5' t6' m5 ps g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest hcs dw fj. ltac2:(SecDiet.SzSec.closeP 'np_unsw__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpCtxC.

End WithCeil.
End TwB.
End F_sfpcap_nextC.

(* [comment removed for export] *)
Module F_sfpcap_next.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_nextA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcap_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_nextA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_nextB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_nextC.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac natfold_term t :=
  match t with
  | context C[4112%nat] => let t1 := context C[Z.to_nat 4112] in natfold_term t1
  | context C[4136%nat] => let t1 := context C[Z.to_nat 4136] in natfold_term t1
  | context C[4208%nat] => let t1 := context C[Z.to_nat 4208] in natfold_term t1
  | _ => t
  end.
Local Ltac natfold_hyp H := let T := type of H in let U := natfold_term T in change U in H.
Local Ltac natfold_concl := lazymatch goal with |- ?G => let U := natfold_term G in change U end.
Local Ltac natfold_lits :=
  repeat match goal with
  | nfH : context [4112%nat] |- _ => natfold_hyp nfH
  | nfH : context [4136%nat] |- _ => natfold_hyp nfH
  | nfH : context [4208%nat] |- _ => natfold_hyp nfH
  end;
  lazymatch goal with
  | |- context [4112%nat] => natfold_concl
  | |- context [4136%nat] => natfold_concl
  | |- context [4208%nat] => natfold_concl
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Local Ltac cl_lit_hyps :=
  repeat match goal with
  | H : context [cells_size ?cs] |- _ =>
      tryif (match goal with H' := _ |- _ => constr_eq H' H end) then fail else
      (sl_spine_closed cs;
       let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
       change (cells_size cs) with n in H)
  end.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
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
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section NpCtxD.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA B Af : Z) (m : mem) (o : option hptr).
  Variables (self buffer f : hptr) (bufsize bufalloc : Z) (bufdata : list Z) (swapped : bool)
            (vmaj vmin snapshot linktype ltext prec brk : Z) (errbuf : list Z) (header : pkthdr)
            (hdrsize : Z).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 664 <= CEILZ)%Z.
  Hypothesis P5 : (P + 664 <= 65536 \/ 348160 <= P)%Z.  Hypothesis P6 : (P + 664 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize < 2^32)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.
  Hypothesis WHS : (hdrsize = 16 \/ hdrsize = 24)%Z.
  Hypothesis PPLEN : forall lt sw hdr d, length (snd (pcapint_post_process lt sw hdr d)) = length d.
  Hypothesis PPSEC : forall lt sw hdr d, h_sec (fst (pcapint_post_process lt sw hdr d)) = h_sec hdr /\ h_usec (fst (pcapint_post_process lt sw hdr d)) = h_usec hdr.
  Hypothesis PPRNG : forall lt sw hdr d, (0 <= h_caplen hdr <= Z.of_nat (length d))%Z -> (0 <= h_len hdr < 2^32)%Z -> (Z.of_nat (length d) < 2^31)%Z ->
     (0 <= h_caplen (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z /\ (0 <= h_len (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation np_epilogue := (F_sfpcap_nextA.np_epilogue ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo P HA DA BU).
  #[local] Abbreviation np_fail_tail := (F_sfpcap_nextA.np_fail_tail K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation np_snp := (F_sfpcap_nextA.np_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation np_fmt := (F_sfpcap_nextA.np_fmt K FMT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P2 P4).
  #[local] Abbreviation np_CLc_facts := (F_sfpcap_nextA.np_CLc_facts K R CLc FB).
  #[local] Abbreviation np_body := (fun (lsw : lenswap_t) (scl : sf_scale_t) =>
     OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_nextC.np_body HO K sites HFL SFL HPL HAL FREAD FERROR FMT SNPRINTF REALLOC PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA B Af m o self buffer f bufsize bufalloc bufdata swapped
                             vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize
                             LO BU SPM TP ALN SITES R1 R2 R3 AH AD SPW SP47 HinF P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10 WHS PPLEN PPSEC PPRNG lsw scl).
  #[local] Abbreviation p0 := (F_sfpcap_nextA.p0 self buffer f bufsize bufalloc bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize).


  (* [comment removed for export] *)
  Definition np_swap__stmt : Prop := forall (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' x4 x5 x6 x7 t3' t4' t5' t6' : word) (mx : mem)
           (g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 : Z) (rest : list cell),
      Forall (fun x => 0 <= x < 256)%Z [g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; g12; g13; g14; g15] ->
      rw_cells ssegs mx (bv_unsigned sp + -96)
        ([C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7)); C4 (Z_to_bv 64 (le4val g8 g9 g10 g11)); C4 (Z_to_bv 64 (le4val g12 g13 g14 g15))] ++ rest) ->
      evt ssegs (fun ms' => exists (t0v a1v a4v a5v a6v a7v a0v a2v a3v s7v : word),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0v t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0v a1v a2v a3v a4v a5v a6v a7v
                       (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 x6 s7v s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15558) fc None mx (seg_rom ssegs)
          /\ (bv_unsigned a0v mod 2^32 = le4val g11 g10 g9 g8)%Z /\ (bv_unsigned a2v mod 2^32 = le4val g3 g2 g1 g0)%Z
          /\ (bv_unsigned a3v mod 2^32 = le4val g7 g6 g5 g4)%Z /\ (bv_unsigned s7v mod 2^32 = le4val g15 g14 g13 g12)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA)
                 (Z_to_bv 64 (sxv g8 g9 g10 g11)) (Z_to_bv 64 (bv_unsigned sp + -88)) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15470) fc None mx (seg_rom ssegs)).
  Section Sz1.
  Variables ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' x4 x5 x6 x7 t3' t4' t5' t6' mx g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest : ltac2:(SecDiet.SzSec.tyM 'np_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_swap__body : ltac2:(SecDiet.SzSec.bodyP 'np_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CEILV. all: natfold_lits. pin_using (fun (CEILV : unit) => tt).
    intros GR HB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof GR as GR'. do 16 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl ssegs mx) as WM.
    do 4 step.
    step. rewrite (sx32_lit g0 g1 g2 g3) by lia. step. rewrite (sx32_lit g4 g5 g6 g7) by lia. step. rewrite (sx32_lit g12 g13 g14 g15) by lia.
    do 35 step.
    apply evt_done. do 10 eexists. split; [reflexivity|].
    assert (SW : forall a b c d, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z ->
      (bv_unsigned (Z_to_bv 64
        (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (sxv a b c d))) 24)))
                                                (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (sxv a b c d))) 65280))) 8))))))
               (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (sxv a b c d))) 8))) 65280)))
                                                (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (sxv a b c d)))) 24))))))))) mod 2^32
       = le4val d c b a)%Z).
    { intros a b c d Ha Hb Hc Hd.
      rewrite (swap32_val (Z_to_bv 64 (sxv a b c d)) a b c d ((d / 128) * 4294967295));
        [ unfold le4val; Z.div_mod_to_equations; (keep_hyps a b c d q r q0 r0 r1 q1 Ha Hb Hc Hd H21 H22; lia) | (keep_hyps a Ha; lia) | (keep_hyps b Hb; lia) | (keep_hyps c Hc; lia) | (keep_hyps d Hd; lia) | Z.div_mod_to_equations; (keep_hyps d q r Hd H16 H17; lia) |].
      rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia). unfold sxv, le4val. lia. }
    repeat split; apply SW; lia.
  Qed.
  End Sz1.
  Lemma np_swap : ltac:(let t := eval cbv delta [np_swap__stmt] in np_swap__stmt in exact t).
  Proof using CEILV. all: natfold_lits. intros ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' x4 x5 x6 x7 t3' t4' t5' t6' mx g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest. ltac2:(SecDiet.SzSec.closeP 'np_swap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac merge_all_lin H :=
    lazymatch type of H with
    | rw_cells ?s ?m ?A ?cs =>
        change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
        cbn [cells_size csize cells_bytes cbytes app] in H
    end.
  Definition np_main__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t)
      (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ps : PState H hptr) (hcs : list cell) (dw : cell),
      stk ssegs m lo (bv_unsigned sp) -> mem_inv ssegs m ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m ->
      rw_cells ssegs m HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m DA [dw] -> csize dw = 8%nat -> ps_outfile ps = o ->
      implM ssegs (pcap_next_packet MOps (prims HO fo_nop sites) (p0 lsw scl)) ps POSTQ
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 DA) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x153f0) fc None m (seg_rom ssegs)).
  Section Sz2.
  Variables lsw scl t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ps hcs dw : ltac2:(SecDiet.SzSec.tyM 'np_main__stmt "vvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_main__body : ltac2:(SecDiet.SzSec.bodyP 'np_main__stmt "vvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
    intros ST MI G PC HH Hh HD Hd OF0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof W1 as W1'. unfold INT_MAX in W1'.
    pose proof PC as PC'.
    destruct PC as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & _)).
    unfold F_sfpcap_nextA.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold F_sfpcap_nextA.p0, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
    unfold F_sfpcap_nextA.p0, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV. cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    destruct (rw_cells_cut _ _ _ 3 PRIV) as [PRIV3 _]. clear PRIV. cbn [firstn] in PRIV3. rename PRIV3 into PRIV.
    assert (EAF : Afx = Af).
    { pose proof (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact Hin)) as E1.
      pose proof (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as E2. cbn [pc_rfile F_sfpcap_nextA.p0] in E1. congruence. }
    subst Afx.
    (* [comment removed for export] *)
    rewrite (np_model_eq MOps (prims HO fo_nop sites)). unfold F_sfpcap_nextA.p0. cbn [sf_of pc_priv sf_hdrsize pc_rfile pc_swapped].
    unfold read_fail_msg, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims].
    hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp - 4208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold implM. iprefix.
    hide CELLS. hide PRIV.
    carve_frame (Z.to_nat 4208) ST.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB ssegs _ _ [] (Z.to_nat 4208) _ [] [Z.to_nat 4136; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB _ ?t] =>
      lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in pose (j := t); change t with j in FR; clearbody j end.
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 1 FR) as [FRL FRH]. clear FR. (cbn [firstn skipn] in FRL, FRH; sl_lit_sizes_in FRH; cbn [firstn skipn cells_size csize Nat.add] in FRH).
    lazymatch type of FRH with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -72)%Z in FRH by lia end.
    pose proof (munch_refl [(bv_unsigned sp - 72, bv_unsigned sp)]%Z m) as MUL.
    hide FRL.
    do 12 step.
    unhide FRL.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGL : agrees_on (fun a => outside [(bv_unsigned sp - 72, bv_unsigned sp)]%Z a) m mm) by (eapply agrees_on_of_munch; [exact MUL | exact WM | intros a _ Ho; exact Ho]) end.
    clear MUL.
    apply (agrees_rw_cells _ _ _ _ _ AGL) in FRL; [| intros a Ha; (sl_lit_sizes_in Ha; cbn [outside cells_size csize Nat.add] in Ha |- *); clear - Ha; lia]. clear AGL.
    pose proof (rw_cells_uncut _ _ _ _ _ FRL FRH ltac:(sl_lit_sizes; cbn [cells_size csize Nat.add]; lia)) as FR. clear FRL FRH. cbn [app] in FR.
    (* [comment removed for export] *)
    unhide HH. unhide HD. unhide CELLS. unhide PRIV.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGP : agrees_on (fun a => outside [(bv_unsigned sp - 4208, bv_unsigned sp)]%Z a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m0 end.
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; clear - Ha R1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R1 R2; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in CELLS; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); gio_ceil_fact; clear -CLO__ Ha P4 LO BU SPW; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in PRIV; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); gio_ceil_fact; clear -CLO__ Ha P4 LO BU SPW; unfold rc_lo in LO; lia].
    assert (G0 : GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m0).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM |].
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo. lia. }
    assert (PC0 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m0).
    { eapply PCAPR_agree; [exact AGP | | exact PC']. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha). cbn [outside]. unfold rc_lo in LO. lia. }
    assert (AG0 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m0).
    { eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [lia|].
      destruct (np_CLc_facts _ _ _ _ G Ha) as [Hc _]. unfold rc_lo in LO. lia. }
    clear MU WM PC'.
    do 12 step.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB ssegs _ _ [] (Z.to_nat 4136) _ [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [Z.to_nat 4112; Z.to_nat hdrsize; 24 - Z.to_nat hdrsize]%nat) in FR; [| cbn [sum_nat]; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw WHS; lia)].
    cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ (CB _ ?l0 :: CB _ ?l1 :: CB _ ?l2 :: _) =>
      pose (j0 := l0); change l0 with j0 in FR; pose (j1 := l1); change l1 with j1 in FR; pose (j2 := l2); change l2 with j2 in FR; clearbody j0 j1 j2 end.
    destruct (rw_cells_cut _ _ _ 1 FR) as [F0 F123]. clear FR. (cbn [firstn skipn] in F0, F123; sl_lit_sizes_in F0; sl_lit_sizes_in F123; cbn [firstn skipn cells_size csize Nat.add] in F0, F123).
    destruct (rw_cells_cut _ _ _ 1 F123) as [F1 F23]. clear F123. (cbn [firstn skipn] in F1, F23; sl_lit_sizes_in F1; sl_lit_sizes_in F23; cbn [firstn skipn cells_size csize Nat.add] in F1, F23).
    destruct (rw_cells_cut _ _ _ 1 F23) as [F2 FS]. clear F23. (cbn [firstn skipn] in F2, FS; sl_lit_sizes_in F2; sl_lit_sizes_in FS; cbn [firstn skipn cells_size csize Nat.add] in F2, FS).
    lazymatch type of F1 with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -96)%Z in F1 by lia end.
    (* [comment removed for export] *)
    lazymatch type of F2 with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -96 + hdrsize)%Z in F2 by lia end.
    lazymatch type of FS with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -72)%Z in FS by lia end.
    (* [comment removed for export] *)
    hide F0. hide F2. hide FS. hide PRIV. hide CELLS. hide HH. hide HD.
    name_sp sp (-4208)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop].
      replace (sites SiteSfHdr + 0)%Z with (bv_unsigned sp + -96)%Z by (rewrite SITES; unfold sites_at, D_NEXT_PACKET; lia).
      eapply FREAD; [| exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact F1 | ].
      { split; [exact G0|]. split; [rewrite Hsp; eassumption|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [eassumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      right. rewrite Hsp. lia. }
    intros got ps2 ms2 PO. cbv beta in PO.
    destruct PO as (av & m2 & junk2 & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & GOTL & GOTR & HB).
    unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms2. rewrite Hsp in *. unname_sp. cbv beta.
    replace (ret_pc (Z_to_bv 64 0x15450)) with (Z_to_bv 64 0x15450) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide F0. unhide F2. unhide FS. unhide PRIV. unhide CELLS. unhide HH. unhide HD. clear F1.
    assert (KEEP : forall A cs, rw_cells ssegs m0 A cs ->
              ((bv_unsigned sp + -4208 <= A /\ (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -96 \/ bv_unsigned sp + -96 + hdrsize <= A))
               \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells ssegs m2 A cs).
    { intros A cs HC HX. eapply agrees_rw_cells; [exact AG2 | exact HC | intros a Ha]. destruct HX as [[HX HY]|[HX HY]].
      - split; [left; lia| lia].
      - split; [right; apply in_block_app; right; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd psize is_ng pc_priv F_sfpcap_nextA.p0 pc_bufalloc]; unfold PCAP_SF_TOTAL; lia| unfold rc_lo in LO; lia]. }
    apply KEEP in F0; [| left; split; [(keep_hyps CEILV sp R P HA DA hcs dw; lia)| (sl_lit_sizes; cbn [cells_size csize Nat.add]); (keep_hyps CEILV sp R P HA DA hdrsize hcs dw; lia)]]. apply KEEP in F2; [| left; split; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw j2 WHS; lia)]. apply KEEP in FS; [| left; split; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw ra s0 s1 s2 s3 s4 s5 s6 s7 WHS; lia)].
    apply KEEP in HH; [| left; split; [lia| rewrite Hh; lia]]. apply KEEP in HD; [| left; split; [lia| cbn [cells_size]; rewrite Hd; lia]].
    apply KEEP in CELLS; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. apply KEEP in PRIV; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. clear KEEP.
    assert (PC2 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m2).
    { eapply PCAPR_agree; [exact AG2 | | exact PC0]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha).
      split; [right; apply in_block_app; right; exact Ha| unfold rc_lo in LO; lia]. }
    assert (AG02 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m2).
    { eapply agrees_on_trans; [exact AG0|]. eapply agrees_on_weaken; [exact AG2|]. intros a [[Ha|Ha] [Hn1 Hn2]]; [split; [left; lia| unfold rc_lo in LO; lia]|].
      destruct (np_CLc_facts _ _ _ _ G Ha) as [Hc Hnb]. split; [right; apply in_block_app; left; exact Ha| lia]. }
    clear AG2 PC0 G0 AG0 ST MI.
    hide F0. hide F2. hide FS. hide HH. hide HD. hide HB. hide CELLS.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl ssegs m2) as WM.
    unfold implM. iprefix. step.
    destruct (Z.eq_dec (zlength got) hdrsize) as [LEQ|LNE].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      step. if_cases Kq; [ idtac | try (zify_cond Kq; exfalso; clear - Kq LNE GOTL WHS; unfold zlength in *; (keep_hyps LNE Kq; lia)) ].
      do 3 step.
      (* [comment removed for export] *)
      unhide F0. unhide F2. unhide FS. unhide HB.
      pose proof (rw_cells_uncut _ _ _ _ _ F0 HB ltac:(cbn [cells_size csize]; lia)) as FJ.
      pose proof (rw_cells_uncut _ _ _ _ _ FJ F2 ltac:(cbn [cells_size csize app]; unfold zlength in GOTL; lia)) as FJ'. clear FJ F0 F2 HB.
      cbn [app] in FJ'. merge_all_lin FJ'.
      lazymatch type of FJ' with rw_cells _ _ _ [CB ?k _] => replace k with (Z.to_nat 4136) in FJ' by (unfold zlength in GOTL; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw got WHS GOTL; lia)) end.
      pose proof (rw_cells_uncut _ _ _ _ _ FJ' FS ltac:(cbn [cells_size csize]; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw got WHS; lia))) as FR. clear FJ' FS. cbn [app] in FR.
      hide FR.
      apply evt_done. name_sp sp (-4208)%Z. eapply (implM_bind ssegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G2|]. split; [rewrite Hsp; exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI2|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros r ps3 ms3 PO. cbv beta in PO. destruct PO as (av3 & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO).
      unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x15524)) with (Z_to_bv 64 0x15524) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide FR. unhide HH. unhide HD. unhide CELLS.
      assert (KEEP : forall A cs, rw_cells ssegs m2 A cs -> (bv_unsigned sp + -4208 <= A)%Z -> rw_cells ssegs m3 A cs)
        by (intros A cs HC HX; eapply agrees_rw_cells; [exact AG3 | exact HC | intros a Ha; left; lia]).
      apply KEEP in FR; [| lia]. apply KEEP in HH; [| lia]. apply KEEP in HD; [| lia]. clear KEEP.
      assert (PC3 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m3).
      { eapply PCAPR_agree; [exact AG3 | | exact PC2]. intros a Ha. right. apply in_block_app. right. exact Ha. }
      assert (AG03 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m3).
      { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
      clear AG3 MU WM CELLS. hide FR. hide HD. hide HH.
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl ssegs m3) as WM.
      destruct r.
      + (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN ER]. clear ERRNO. unfold utp in EN. rewrite <- TP in EN.
        pose proof (GIo_tls K _ _ _ _ _ G3) as [_ TB]. unfold tls_block_ok, utp in TB. rewrite <- TP in TB.
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        set (e := lc_errno (ps_libc ps2)) in *.
        unfold implM. iprefix. cbn [Z.b2z]. step. if_false. step. do 4 step. step. rewrite (sx32_s32 e) by lia. do 5 step.
        unhide FR. unhide HD. unhide HH.
        apply evt_done. eapply np_fmt; [exact ST3 | exact FR | exact MI3 | | lia |].
        { split; [exact G3|]. split; [exact PC3|]. split; [exact AG03|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m3 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))).
      + (* [comment removed for export] *)
        unfold implM. iprefix. cbn [Z.b2z]. step. if_true.
        destruct (Z.eq_dec (zlength got) 0) as [Z0|NZ].
        * rewrite Z0. cbn [Z.eqb negb]. rewrite Z0 in *.
          step. if_true.
          unhide FR. unhide HD. unhide HH.
          apply evt_done. apply (implM_ret ssegs). step. step.
          eapply np_epilogue; [exact ST3 | exact FR | exact MI3 |].
          intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST4.
          subst POSTQ. unfold next_packet_post. all: natfold_lits. exists (Z_to_bv 64 0), m3, (pcap_blocks (p0 lsw scl) P B 0), dw.
          split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
          split; [congruence|]. split; [exact MI3|]. split; [exact ST4|]. split; [exact AG03|]. split; [exact G3|].
          split; [intros _; exact PC3|]. split; [intros _; apply PCAPR_closable_of; exact PC3|].
          split; [reflexivity|]. split; [lia|]. split; [intros X; exfalso; lia|]. split; [intros _; exists hcs; split; [exact Hh| exact HH]|].
          split; [exact HD| exact Hd].
        * rewrite (proj2 (Z.eqb_neq _ _) NZ). cbn [negb].
          step. if_cases Kz; [ try (zify_cond Kz; exfalso; clear - Kz NZ GOTL WHS; unfold zlength in *; (keep_hyps NZ Kz; lia)) | idtac ].
          do 8 step.
          unhide FR. unhide HD. unhide HH.
          apply evt_done. unfold Msg.trunc_header, PCAP_ERRBUF_SIZE.
          eapply np_snp; [exact ST3 | exact FR | exact MI3 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
          { split; [exact G3|]. split; [exact PC3|]. split; [exact AG03|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| congruence]. }
          { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m3 0x103a3 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %zu header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                       MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
          { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
          pose proof (snprintf_length 256 "truncated dump file; tried to read %zu header bytes, only got %zu"%string [AInt hdrsize; AInt (zlength got)]) as LS.
          change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS. }
   
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
    step. if_cases Kq; [ try (zify_cond Kq; exfalso; clear - Kq LEQ GOTL WHS; unfold zlength in *; (keep_hyps LEQ Kq; lia)) | idtac ].
    assert (L16 : (16 <= length got)%nat) by (unfold zlength in LEQ; lia).
    destruct got as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|g8 [|g9 [|g10 [|g11 [|g12 [|g13 [|g14 [|g15 rest]]]]]]]]]]]]]]]];
      try (exfalso; cbn [length] in L16; (keep_hyps CEILV sp R P HA DA hcs dw L16; lia)). clear L16.
    pose proof GOTR as GR'. do 16 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']).
    pose proof (get_le32_hdr g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest) as (E0 & E4 & E8 & E12). cbv zeta in E0, E4, E8, E12.
    rewrite E0, E4, E8, E12. clear E0 E4 E8 E12.
    (* [comment removed for export] *)
    unhide HB.
    assert (LJ : length junk2 = (Z.to_nat hdrsize - (16 + length rest))%nat) by (destruct HB as [[WF _] _]; cbn in WF; cbn [length] in WF |- *; lia).
    assert (HB4 : rw_cells ssegs m2 (bv_unsigned sp + -96)
              ([C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7)); C4 (Z_to_bv 64 (le4val g8 g9 g10 g11)); C4 (Z_to_bv 64 (le4val g12 g13 g14 g15))]
               ++ [CB (length rest) (map b8 rest); CB (length junk2) junk2])).
    { eapply rw_cells_recell; [exact HB | cbn; rewrite length_map; repeat split; try exact Logic.I; cbn [length] in LEQ |- *; unfold zlength in LEQ; cbn [length] in LEQ; lia |].
      cbn [cells_bytes cbytes app map]. rewrite (le4_lit g0 g1 g2 g3), (le4_lit g4 g5 g6 g7), (le4_lit g8 g9 g10 g11), (le4_lit g12 g13 g14 g15) by (keep_hyps CEILV sp R P HA DA hdrsize hcs dw g0 rest junk2 H0 g1 H1 g2 H2 g3 H3 g4 H4 g5 H5 g6 H6 g7 H7 g8 H8 g9 H9 g10 H10 g11 H11 g12 H12 g13 H13 g14 H14 g15 H15; lia).
      cbn [app]. rewrite app_nil_r. reflexivity. }
    hide HB. unhide CELLS.
    step. step. step. step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; (keep_hyps CEILV sp R P HA DA hdrsize hcs dw rest junk2; lia)). step. rewrite (sx32_lit g8 g9 g10 g11) by lia.
    hide CELLS.
    (* [comment removed for export] *)
    assert (FRJ : forall mx, rw_cells ssegs mx (bv_unsigned sp + -4208) [CB (Z.to_nat 4112) j0] ->
              rw_cells ssegs mx (bv_unsigned sp + -96) [CB (length (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: g8 :: g9 :: g10 :: g11 :: g12 :: g13 :: g14 :: g15 :: rest))
                 (map b8 (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: g8 :: g9 :: g10 :: g11 :: g12 :: g13 :: g14 :: g15 :: rest)); CB (Z.to_nat hdrsize - length (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: g8 :: g9 :: g10 :: g11 :: g12 :: g13 :: g14 :: g15 :: rest)) junk2] ->
              rw_cells ssegs mx (bv_unsigned sp + -96 + hdrsize) [CB (24 - Z.to_nat hdrsize) j2] ->
              rw_cells ssegs mx (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              exists fj, rw_cells ssegs mx (bv_unsigned sp + -4208) [CB (Z.to_nat 4136) fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { intros mx X0 XB X2 XS.
      pose proof (rw_cells_uncut _ _ _ _ _ X0 XB ltac:(cbn [cells_size csize]; lia)) as FJ.
      pose proof (rw_cells_uncut _ _ _ _ _ FJ X2 ltac:(cbn [cells_size csize app]; unfold zlength in LEQ; lia)) as FJ'. clear FJ.
      cbn [app] in FJ'. merge_all_lin FJ'.
      lazymatch type of FJ' with rw_cells _ _ _ [CB ?k _] => replace k with (Z.to_nat 4136) in FJ' by (unfold zlength in LEQ; cbn [length] in LEQ |- *; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw rest junk2 WHS LEQ; lia)) end.
      pose proof (rw_cells_uncut _ _ _ _ _ FJ' XS ltac:(cbn [cells_size csize]; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw rest junk2 WHS; lia))) as FR'. cbn [app] in FR'. eexists. exact FR'. }
    destruct (Bool.bool_dec swapped true) as [ES|ES]; [| apply Bool.not_true_is_false in ES].
    - (* [comment removed for export] *)
      rewrite !(if_b_true swapped _ _ ES). replace (Z.b2z swapped) with 1%Z by (rewrite ES; reflexivity).
      step. if_false.
      unhide HB.
      eapply evt_cut. { eapply (np_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15); [| exact HB4]. repeat (apply Forall_cons; [assumption|]). apply Forall_nil. }
      cbv beta. intros ms' PO. destruct PO as (t0v & a1v & a4v & a5v & a6v & a7v & a0v & a2v & a3v & s7v & -> & Fc & Fs & Fu & Fl).
      rewrite (bswap32_le4val g0 g1 g2 g3), (bswap32_le4val g4 g5 g6 g7), (bswap32_le4val g8 g9 g10 g11), (bswap32_le4val g12 g13 g14 g15) by (keep_hyps CEILV sp R P HA DA hdrsize hcs dw g0 rest junk2 a0v a2v a3v s7v H0 g1 H1 g2 H2 g3 H3 g4 H4 g5 H5 g6 H6 g7 H7 g8 H8 g9 H9 g10 H10 g11 H11 g12 H12 g13 H13 g14 H14 g15 H15; lia).
      rewrite <- (Z_to_bv_bv_unsigned a0v), <- (Z_to_bv_bv_unsigned a2v), <- (Z_to_bv_bv_unsigned a3v), <- (Z_to_bv_bv_unsigned s7v).
      rewrite <- Fc, <- Fs, <- Fu, <- Fl.
      unhide F0. unhide F2. unhide FS. unhide HH. unhide HD.
      destruct (FRJ m2 F0 HB F2 FS) as [fj FR].
      pose proof (bv_unsigned_in_range 64 a0v). pose proof (bv_unsigned_in_range 64 a2v). pose proof (bv_unsigned_in_range 64 a3v). pose proof (bv_unsigned_in_range 64 s7v).
      unfold bv_modulus in *.
      apply evt_done. eapply (np_body lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 ps2 (bv_unsigned a2v) (bv_unsigned a3v) (bv_unsigned a0v) (bv_unsigned s7v) hcs dw fj);
        [exact ST2 | exact FR | exact MI2 | exact G2 | exact PC2 | exact AG02 | exact HH | exact Hh | exact HD | exact Hd | lia | lia | lia | lia | congruence].
    - (* [comment removed for export] *)
      rewrite !(if_b_false swapped _ _ ES). replace (Z.b2z swapped) with 0%Z by (rewrite ES; reflexivity).
      step. if_true.
      unhide HB.
      step. rewrite (sx32_lit g0 g1 g2 g3) by lia. step. rewrite (sx32_lit g4 g5 g6 g7) by lia. step. rewrite (sx32_lit g12 g13 g14 g15) by lia.
      rewrite <- (sxv_mod32 g0 g1 g2 g3), <- (sxv_mod32 g4 g5 g6 g7), <- (sxv_mod32 g8 g9 g10 g11), <- (sxv_mod32 g12 g13 g14 g15) by (keep_hyps CEILV sp R P HA DA hdrsize hcs dw g0 rest junk2 H0 g1 H1 g2 H2 g3 H3 g4 H4 g5 H5 g6 H6 g7 H7 g8 H8 g9 H9 g10 H10 g11 H11 g12 H12 g13 H13 g14 H14 g15 H15; lia).
      unhide F0. unhide F2. unhide FS. unhide HH. unhide HD.
      destruct (FRJ m2 F0 HB F2 FS) as [fj FR].
      pose proof (sxv_range g0 g1 g2 g3). pose proof (sxv_range g4 g5 g6 g7). pose proof (sxv_range g8 g9 g10 g11). pose proof (sxv_range g12 g13 g14 g15).
      apply evt_done. eapply (np_body lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 ps2 (sxv g0 g1 g2 g3) (sxv g4 g5 g6 g7) (sxv g8 g9 g10 g11) (sxv g12 g13 g14 g15) hcs dw fj);
        [exact ST2 | exact FR | exact MI2 | exact G2 | exact PC2 | exact AG02 | exact HH | exact Hh | exact HD | exact Hd | (keep_hyps CEILV sp R P HA DA hdrsize hcs dw g0 g1 g2 g3 rest junk2 H0 H1 H2 H3 H16; lia) | (keep_hyps CEILV sp R P HA DA hdrsize hcs dw g0 g1 g2 g3 g4 g5 g6 g7 rest junk2 H4 H5 H6 H7 H17; lia) | (keep_hyps CEILV sp R P HA DA hdrsize hcs dw g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 rest junk2 H8 H9 H10 H11 H18; lia) | (keep_hyps CEILV sp R P HA DA hdrsize hcs dw g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest junk2 H12 H13 H14 H15 H19; lia) | congruence].
  Qed.
  End Sz2.
  Lemma np_main : ltac:(let t := eval cbv delta [np_main__stmt] in np_main__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ps hcs dw. ltac2:(SecDiet.SzSec.closeP 'np_main__body "vvvvvvvvvvvvvvvvv"). Qed.
End NpCtxD.

Section NpThm.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis PP : post_process_stmt.

  Definition pcap_next_packet_proof__stmt : Prop := pcap_next_packet_stmt HO K sites.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HA DA p fuel hcs dc : ltac2:(SecDiet.SzSec.tyM 'pcap_next_packet_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_next_packet_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_next_packet_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FERROR FMT FREAD HAL HFL HPL PP REALLOC SFL SNPRINTF. all: natfold_lits. pin_using (fun (FERROR FMT FREAD HAL HFL HPL PP REALLOC SFL SNPRINTF : unit) => tt).
    intros PRE PC NG SITES -> -> -> HHA Hhcs HDA Hdc R1 R2 R3 AH AD.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. unfold rc_lo in LO. unfold PCAP_L2_STACK in BU.
    destruct p as [self rfile bufsize bufalloc buffer bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header priv].
    destruct priv as [sf|ng oif]; [| discriminate NG]. clear NG. destruct sf as [hdrsize lsw scl].
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & _ & _ & _ & _ & IFS & WF)).
    cbn [pc_priv ifaces_ok] in IFS. subst I.
    unfold pcap_wf in WF. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
         pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in WF.
    destruct WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & WHS & WBB).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    unfold psize, is_ng in P3, P4, P5, P6. cbn [pc_priv] in P3, P4, P5, P6. unfold PCAP_SF_TOTAL in P3, P4, P5, P6.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & _ & _).
    cbn [cb_addr cb_size fst snd] in A1, A4. unfold FILE_BLOCK in A4.
    rewrite EPB in G, PC.
    unfold next_packet_op, PcapRep.np_entry, is_ng. cbn [pc_priv pk_next_pcap PK].
    eapply np_main; try eassumption; try reflexivity; try (keep_hyps CEILV sp R P HA DA hcs dc bufdata SPW bufsize W2; lia).
    - exact pp_length.
    - exact pp_sec.
    - exact pp_range.
  Qed.
  End Sz3.
  Theorem pcap_next_packet_proof : ltac:(let t := eval cbv delta [pcap_next_packet_proof__stmt] in pcap_next_packet_proof__stmt in exact t).
  Proof using FERROR FMT FREAD HAL HFL HPL PP REALLOC SFL SNPRINTF. all: natfold_lits. red. unfold next_packet_op_stmt_for. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HA DA p fuel hcs dc. ltac2:(SecDiet.SzSec.closeP 'pcap_next_packet_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpThm.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_nextA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcap_nextA2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_nextB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_nextC.TwB.
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
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section NpCtxD.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA B Af : Z) (m : mem) (o : option hptr).
  Variables (self buffer f : hptr) (bufsize bufalloc : Z) (bufdata : list Z) (swapped : bool)
            (vmaj vmin snapshot linktype ltext prec brk : Z) (errbuf : list Z) (header : pkthdr)
            (hdrsize : Z).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 664 <= CEILZ)%Z.
  Hypothesis P5 : (P + 664 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 664 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize < 2^32)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.
  Hypothesis WHS : (hdrsize = 16 \/ hdrsize = 24)%Z.
  Hypothesis PPLEN : forall lt sw hdr d, length (snd (pcapint_post_process lt sw hdr d)) = length d.
  Hypothesis PPSEC : forall lt sw hdr d, h_sec (fst (pcapint_post_process lt sw hdr d)) = h_sec hdr /\ h_usec (fst (pcapint_post_process lt sw hdr d)) = h_usec hdr.
  Hypothesis PPRNG : forall lt sw hdr d, (0 <= h_caplen hdr <= Z.of_nat (length d))%Z -> (0 <= h_len hdr < 2^32)%Z -> (Z.of_nat (length d) < 2^31)%Z ->
     (0 <= h_caplen (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z /\ (0 <= h_len (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation np_epilogue := (S3.F_sfpcap_nextA.TwB.np_epilogue ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo P HA DA BU).
  #[local] Abbreviation np_fail_tail := (S3.F_sfpcap_nextA.TwB.np_fail_tail K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation np_snp := (S3.F_sfpcap_nextA.TwB.np_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation np_fmt := (S3.F_sfpcap_nextA.TwB.np_fmt K FMT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P2 P4).
  #[local] Abbreviation np_CLc_facts := (S3.F_sfpcap_nextA.TwB.np_CLc_facts K R CLc FB).
  #[local] Abbreviation np_hdr_sw := (fun (lsw : lenswap_t) (scl : sf_scale_t) =>
     OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_nextC.TwB.np_hdr_sw HO K sites HFL SFL HPL HAL FREAD FERROR FMT SNPRINTF REALLOC PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA B Af m o self buffer f bufsize bufalloc bufdata swapped
                             vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize
                             LO BU SPM TP ALN SITES R1 R2 R3 AH AD SPW SP47 HinF P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10 WHS PPLEN PPSEC PPRNG lsw scl).
  #[local] Abbreviation np_unsw := (fun (lsw : lenswap_t) (scl : sf_scale_t) =>
     OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_nextC.TwB.np_unsw HO K sites HFL SFL HPL HAL FREAD FERROR FMT SNPRINTF REALLOC PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA B Af m o self buffer f bufsize bufalloc bufdata swapped
                             vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize
                             LO BU SPM TP ALN SITES R1 R2 R3 AH AD SPW SP47 HinF P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10 WHS PPLEN PPSEC PPRNG lsw scl).
  #[local] Abbreviation p0 := (S3.F_sfpcap_nextA.TwB.p0 self buffer f bufsize bufalloc bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header hdrsize).


  (* [comment removed for export] *)
  Definition np_swap__stmt : Prop := forall (ra' t0' t1' t2' a3' a4' a5' a6' a7' x4 x5 x6 x7 t3' t4' t5' t6' : word) (mx : mem)
           (g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 : Z) (rest : list cell),
      Forall (fun x => 0 <= x < 256)%Z [g0; g1; g2; g3; g4; g5; g6; g7; g8; g9; g10; g11; g12; g13; g14; g15] ->
      rw_cells usegs mx (bv_unsigned sp + -96)
        ([C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7)); C4 (Z_to_bv 64 (le4val g8 g9 g10 g11)); C4 (Z_to_bv 64 (le4val g12 g13 g14 g15))] ++ rest) ->
      evt usegs (fun ms' => exists (t0v t1v a4v a5v a6v a7v a0v a2v a3v s7v : word),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0v t1v t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0v (Z_to_bv 64 0) a2v a3v a4v a5v a6v a7v
                       (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 x6 s7v s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15ab4) fc None mx (seg_rom usegs)
          /\ (bv_unsigned a0v mod 2^32 = le4val g11 g10 g9 g8)%Z /\ (bv_unsigned a2v mod 2^32 = le4val g3 g2 g1 g0)%Z
          /\ (bv_unsigned a3v mod 2^32 = le4val g7 g6 g5 g4)%Z /\ (bv_unsigned s7v mod 2^32 = le4val g15 g14 g13 g12)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA)
                 (Z_to_bv 64 (sxv g8 g9 g10 g11)) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -88)) a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15a10) fc None mx (seg_rom usegs)).
  Section Sz1.
  Variables ra' t0' t1' t2' a3' a4' a5' a6' a7' x4 x5 x6 x7 t3' t4' t5' t6' mx g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest : ltac2:(SecDiet.SzSec.tyM 'np_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_swap__body : ltac2:(SecDiet.SzSec.bodyP 'np_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CEILV. all: natfold_lits. pin_using (fun (CEILV : unit) => tt).
 intros GR HB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof GR as GR'. do 16 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl ([] : list (Z * Z)) mx) as MU. pose proof (wmono_refl usegs mx) as WM.
    do 4 step.
    step. rewrite (sx32_lit g0 g1 g2 g3) by lia. step. rewrite (sx32_lit g4 g5 g6 g7) by lia. step. rewrite (sx32_lit g12 g13 g14 g15) by lia.
    do 34 step.
    apply evt_done. do 10 eexists. split; [reflexivity|].
    assert (SW : forall a b c d, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z ->
      (bv_unsigned (Z_to_bv 64
        (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (sxv a b c d))) 24)))
                                                (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (sxv a b c d))) 65280))) 8))))))
               (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (sxv a b c d))) 8))) 65280)))
                                                (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (sxv a b c d)))) 24))))))))) mod 2^32
       = le4val d c b a)%Z).
    { intros a b c d Ha Hb Hc Hd.
      rewrite (swap32_val (Z_to_bv 64 (sxv a b c d)) a b c d ((d / 128) * 4294967295));
        [ unfold le4val; Z.div_mod_to_equations; (keep_hyps a b c d q r q0 r0 r1 q1 Ha Hb Hc Hd H21 H22; lia) | (keep_hyps a Ha; lia) | (keep_hyps b Hb; lia) | (keep_hyps c Hc; lia) | (keep_hyps d Hd; lia) | Z.div_mod_to_equations; (keep_hyps d q r Hd H16 H17; lia) |].
      rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia). unfold sxv, le4val. lia. }
    repeat split; apply SW; lia.
  Qed.
  End Sz1.
  Lemma np_swap : ltac:(let t := eval cbv delta [np_swap__stmt] in np_swap__stmt in exact t).
  Proof using CEILV. all: natfold_lits. intros ra' t0' t1' t2' a3' a4' a5' a6' a7' x4 x5 x6 x7 t3' t4' t5' t6' mx g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest. ltac2:(SecDiet.SzSec.closeP 'np_swap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac merge_all_lin H :=
    lazymatch type of H with
    | rw_cells ?s ?m ?A ?cs =>
        change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
        cbn [cells_size csize cells_bytes cbytes app] in H
    end.
  Definition np_main__stmt : Prop := forall (lsw : lenswap_t) (scl : sf_scale_t)
      (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ps : PState H hptr) (hcs : list cell) (dw : cell),
      stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m ->
      GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m ->
      PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m ->
      rw_cells usegs m HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m DA [dw] -> csize dw = 8%nat -> ps_outfile ps = o ->
      implM usegs (pcap_next_packet MOps (prims HO fo_nop sites) (p0 lsw scl)) ps POSTQ
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 DA) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1596c) fc None m (seg_rom usegs)).
  Section Sz2.
  Variables lsw scl t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ps hcs dw : ltac2:(SecDiet.SzSec.tyM 'np_main__stmt "vvvvvvvvvvvvvvvvv" @lsw).
  Lemma np_main__body : ltac2:(SecDiet.SzSec.bodyP 'np_main__stmt "vvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
 intros ST MI G PC HH Hh HD Hd OF0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof W1 as W1'. unfold INT_MAX in W1'.
    pose proof PC as PC'.
    destruct PC as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & _)).
    unfold S3.F_sfpcap_nextA.TwB.p0, pcap_blocks, psize, is_ng in EPB. cbn [pc_bufalloc pc_priv] in EPB.
    assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    unfold S3.F_sfpcap_nextA.TwB.p0, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_bufalloc pc_buffer pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv
         pk_next_pcap pk_cleanup_sf PK pc_rfile] in CELLS.
    unfold S3.F_sfpcap_nextA.TwB.p0, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV. cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    destruct (rw_cells_cut _ _ _ 3 PRIV) as [PRIV3 _]. clear PRIV. cbn [firstn] in PRIV3. rename PRIV3 into PRIV.
    assert (EAF : Afx = Af).
    { pose proof (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact Hin)) as E1.
      pose proof (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as E2. cbn [pc_rfile S3.F_sfpcap_nextA.TwB.p0] in E1. congruence. }
    subst Afx.
    (* [comment removed for export] *)
    rewrite (np_model_eq MOps (prims HO fo_nop sites)). unfold S3.F_sfpcap_nextA.TwB.p0. cbn [sf_of pc_priv sf_hdrsize pc_rfile pc_swapped].
    unfold read_fail_msg, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims].
    hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp - 4208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.
    hide CELLS. hide PRIV.
    carve_frame (Z.to_nat 4208) ST.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs _ _ [] (Z.to_nat 4208) _ [] [Z.to_nat 4136; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB _ ?t] =>
      lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in pose (j := t); change t with j in FR; clearbody j end.
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 1 FR) as [FRL FRH]. clear FR. (cbn [firstn skipn] in FRL, FRH; sl_lit_sizes_in FRH; cbn [firstn skipn cells_size csize Nat.add] in FRH).
    lazymatch type of FRH with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -72)%Z in FRH by lia end.
    pose proof (munch_refl [(bv_unsigned sp - 72, bv_unsigned sp)]%Z m) as MUL.
    hide FRL.
    do 12 step.
    unhide FRL.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGL : agrees_on (fun a => outside [(bv_unsigned sp - 72, bv_unsigned sp)]%Z a) m mm) by (eapply agrees_on_of_munch; [exact MUL | exact WM | intros a _ Ho; exact Ho]) end.
    clear MUL.
    apply (agrees_rw_cells _ _ _ _ _ AGL) in FRL; [| intros a Ha; (sl_lit_sizes_in Ha; cbn [outside cells_size csize Nat.add] in Ha |- *); clear - Ha; lia]. clear AGL.
    pose proof (rw_cells_uncut _ _ _ _ _ FRL FRH ltac:(sl_lit_sizes; cbn [cells_size csize Nat.add]; lia)) as FR. clear FRL FRH. cbn [app] in FR.
    (* [comment removed for export] *)
    unhide HH. unhide HD. unhide CELLS. unhide PRIV.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGP : agrees_on (fun a => outside [(bv_unsigned sp - 4208, bv_unsigned sp)]%Z a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m0 end.
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; clear - Ha R1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R1 R2; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in CELLS; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); gio_ceil_fact; clear -CLO__ Ha P4 LO BU SPW; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in PRIV; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); gio_ceil_fact; clear -CLO__ Ha P4 LO BU SPW; unfold rc_lo in LO; lia].
    assert (G0 : GIo K R ps (CLc ++ pcap_blocks (p0 lsw scl) P B 0) FB m0).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM |].
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo. lia. }
    assert (PC0 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m0).
    { eapply PCAPR_agree; [exact AGP | | exact PC']. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha). cbn [outside]. unfold rc_lo in LO. lia. }
    assert (AG0 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m0).
    { eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [lia|].
      destruct (np_CLc_facts _ _ _ _ G Ha) as [Hc _]. unfold rc_lo in LO. lia. }
    clear MU WM PC'.
    assert (P8 : (P mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r P); apply aligned16_8; [exact P2| reflexivity]).
    pose proof (aligned16_8 P 648 P2 eq_refl) as P648.
    step. if_false_by (eqz_false P ltac:(clear - P1 P4; lia)). step. step. rewrite (and7_aligned P) by (clear - P1 P4 P8; lia). step. if_false.
    step. step. if_false_by (eqz_false (P + 648) ltac:(clear - P1 P4; lia)). step. rewrite (and7_aligned (P + 648)) by (clear - P1 P4 P648; lia). step. if_false.
    do 10 step.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs _ _ [] (Z.to_nat 4136) _ [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [Z.to_nat 4112; Z.to_nat hdrsize; 24 - Z.to_nat hdrsize]%nat) in FR; [| cbn [sum_nat]; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw WHS; lia)].
    cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ (CB _ ?l0 :: CB _ ?l1 :: CB _ ?l2 :: _) =>
      pose (j0 := l0); change l0 with j0 in FR; pose (j1 := l1); change l1 with j1 in FR; pose (j2 := l2); change l2 with j2 in FR; clearbody j0 j1 j2 end.
    destruct (rw_cells_cut _ _ _ 1 FR) as [F0 F123]. clear FR. (cbn [firstn skipn] in F0, F123; sl_lit_sizes_in F0; sl_lit_sizes_in F123; cbn [firstn skipn cells_size csize Nat.add] in F0, F123).
    destruct (rw_cells_cut _ _ _ 1 F123) as [F1 F23]. clear F123. (cbn [firstn skipn] in F1, F23; sl_lit_sizes_in F1; sl_lit_sizes_in F23; cbn [firstn skipn cells_size csize Nat.add] in F1, F23).
    destruct (rw_cells_cut _ _ _ 1 F23) as [F2 FS]. clear F23. (cbn [firstn skipn] in F2, FS; sl_lit_sizes_in F2; sl_lit_sizes_in FS; cbn [firstn skipn cells_size csize Nat.add] in F2, FS).
    lazymatch type of F1 with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -96)%Z in F1 by lia end.
    (* [comment removed for export] *)
    lazymatch type of F2 with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -96 + hdrsize)%Z in F2 by lia end.
    lazymatch type of FS with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -72)%Z in FS by lia end.
    (* [comment removed for export] *)
    hide F0. hide F2. hide FS. hide PRIV. hide CELLS. hide HH. hide HD.
    name_sp sp (-4208)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop].
      replace (sites SiteSfHdr + 0)%Z with (bv_unsigned sp + -96)%Z by (rewrite SITES; unfold sites_at, D_NEXT_PACKET; lia).
      eapply FREAD; [| exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact F1 | ].
      { split; [exact G0|]. split; [rewrite Hsp; eassumption|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [eassumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      right. rewrite Hsp. lia. }
    intros got ps2 ms2 PO. cbv beta in PO.
    destruct PO as (av & m2 & junk2 & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & GOTL & GOTR & HB).
    unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms2. rewrite Hsp in *. unname_sp. cbv beta.
    replace (ret_pc (Z_to_bv 64 0x159e4)) with (Z_to_bv 64 0x159e4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide F0. unhide F2. unhide FS. unhide PRIV. unhide CELLS. unhide HH. unhide HD. clear F1.
    assert (KEEP : forall A cs, rw_cells usegs m0 A cs ->
              ((bv_unsigned sp + -4208 <= A /\ (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -96 \/ bv_unsigned sp + -96 + hdrsize <= A))
               \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells usegs m2 A cs).
    { intros A cs HC HX. eapply agrees_rw_cells; [exact AG2 | exact HC | intros a Ha]. destruct HX as [[HX HY]|[HX HY]].
      - split; [left; lia| lia].
      - split; [right; apply in_block_app; right; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd psize is_ng pc_priv S3.F_sfpcap_nextA.TwB.p0 pc_bufalloc]; unfold PCAP_SF_TOTAL; lia| unfold rc_lo in LO; lia]. }
    apply KEEP in F0; [| left; split; [(keep_hyps CEILV sp R P HA DA hcs dw; lia)| (sl_lit_sizes; cbn [cells_size csize Nat.add]); (keep_hyps CEILV sp R P HA DA hdrsize hcs dw; lia)]]. apply KEEP in F2; [| left; split; lia]. apply KEEP in FS; [| left; split; lia].
    apply KEEP in HH; [| left; split; [lia| rewrite Hh; lia]]. apply KEEP in HD; [| left; split; [lia| cbn [cells_size]; rewrite Hd; lia]].
    apply KEEP in CELLS; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. apply KEEP in PRIV; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. clear KEEP.
    assert (PC2 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m2).
    { eapply PCAPR_agree; [exact AG2 | | exact PC0]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha).
      split; [right; apply in_block_app; right; exact Ha| unfold rc_lo in LO; lia]. }
    assert (AG02 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m2).
    { eapply agrees_on_trans; [exact AG0|]. eapply agrees_on_weaken; [exact AG2|]. intros a [[Ha|Ha] [Hn1 Hn2]]; [split; [left; lia| unfold rc_lo in LO; lia]|].
      destruct (np_CLc_facts _ _ _ _ G Ha) as [Hc Hnb]. split; [right; apply in_block_app; left; exact Ha| lia]. }
    clear AG2 PC0 G0 AG0 ST MI.
    hide F0. hide F2. hide FS. hide HH. hide HD. hide HB. hide CELLS.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    unfold implM. iprefix. step.
    destruct (Z.eq_dec (zlength got) hdrsize) as [LEQ|LNE].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      step. if_cases Kq; [ idtac | try (zify_cond Kq; exfalso; clear - Kq LNE GOTL WHS; unfold zlength in *; (keep_hyps LNE Kq; lia)) ].
      do 3 step.
      (* [comment removed for export] *)
      unhide F0. unhide F2. unhide FS. unhide HB.
      pose proof (rw_cells_uncut _ _ _ _ _ F0 HB ltac:(cbn [cells_size csize]; lia)) as FJ.
      pose proof (rw_cells_uncut _ _ _ _ _ FJ F2 ltac:(cbn [cells_size csize app]; unfold zlength in GOTL; lia)) as FJ'. clear FJ F0 F2 HB.
      cbn [app] in FJ'. merge_all_lin FJ'.
      lazymatch type of FJ' with rw_cells _ _ _ [CB ?k _] => replace k with (Z.to_nat 4136) in FJ' by (unfold zlength in GOTL; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw got WHS GOTL; lia)) end.
      pose proof (rw_cells_uncut _ _ _ _ _ FJ' FS ltac:(cbn [cells_size csize]; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw got WHS; lia))) as FR. clear FJ' FS. cbn [app] in FR.
      hide FR.
      apply evt_done. name_sp sp (-4208)%Z. eapply (implM_bind usegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G2|]. split; [rewrite Hsp; exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI2|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros r ps3 ms3 PO. cbv beta in PO. destruct PO as (av3 & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO).
      unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x15b04)) with (Z_to_bv 64 0x15b04) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide FR. unhide HH. unhide HD. unhide CELLS.
      assert (KEEP : forall A cs, rw_cells usegs m2 A cs -> (bv_unsigned sp + -4208 <= A)%Z -> rw_cells usegs m3 A cs)
        by (intros A cs HC HX; eapply agrees_rw_cells; [exact AG3 | exact HC | intros a Ha; left; lia]).
      apply KEEP in FR; [| lia]. apply KEEP in HH; [| lia]. apply KEEP in HD; [| lia]. clear KEEP.
      assert (PC3 : PCAPR (hptr:=hptr) P (p0 lsw scl) (pcap_blocks (p0 lsw scl) P B 0) FB m3).
      { eapply PCAPR_agree; [exact AG3 | | exact PC2]. intros a Ha. right. apply in_block_app. right. exact Ha. }
      assert (AG03 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m3).
      { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
      clear AG3 MU WM CELLS. hide FR. hide HD. hide HH.
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      destruct r.
      + (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN ER]. clear ERRNO. unfold utp in EN. rewrite <- TP in EN.
        pose proof (GIo_tls K _ _ _ _ _ G3) as [_ TB]. unfold tls_block_ok_u, utp in TB. rewrite <- TP in TB.
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        set (e := lc_errno (ps_libc ps2)) in *.
        assert (E4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
        { destruct TB as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * 4 + 9)%Z. lia. }
        unfold implM. iprefix. cbn [Z.b2z]. step. if_false. do 5 step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(clear - TB; lia)).
        step. rewrite (and3_aligned (bv_unsigned tp + -164)) by (clear - TB E4; lia). step. if_false.
        step. rewrite (sx32_s32 e) by lia. do 3 step.
        unhide FR. unhide HD. unhide HH.
        apply evt_done. eapply np_fmt; [exact ST3 | exact FR | exact MI3 | | lia |].
        { split; [exact G3|]. split; [exact PC3|]. split; [exact AG03|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m3 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))).
      + (* [comment removed for export] *)
        unfold implM. iprefix. cbn [Z.b2z]. step. if_true.
        destruct (Z.eq_dec (zlength got) 0) as [Z0|NZ].
        * rewrite Z0. cbn [Z.eqb negb]. rewrite Z0 in *.
          step. if_true.
          unhide FR. unhide HD. unhide HH.
          apply evt_done. apply (implM_ret usegs). step. step.
          eapply np_epilogue; [exact ST3 | exact FR | exact MI3 |].
          intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST4.
          subst POSTQ. unfold next_packet_post. all: natfold_lits. exists (Z_to_bv 64 0), m3, (pcap_blocks (p0 lsw scl) P B 0), dw.
          split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
          split; [congruence|]. split; [exact MI3|]. split; [exact ST4|]. split; [exact AG03|]. split; [exact G3|].
          split; [intros _; exact PC3|]. split; [intros _; apply PCAPR_closable_of; exact PC3|].
          split; [reflexivity|]. split; [lia|]. split; [intros X; exfalso; lia|]. split; [intros _; exists hcs; split; [exact Hh| exact HH]|].
          split; [exact HD| exact Hd].
        * rewrite (proj2 (Z.eqb_neq _ _) NZ). cbn [negb].
          step. if_cases Kz; [ try (zify_cond Kz; exfalso; clear - Kz NZ GOTL WHS; unfold zlength in *; (keep_hyps NZ Kz; lia)) | idtac ].
          do 8 step.
          unhide FR. unhide HD. unhide HH.
          apply evt_done. unfold Msg.trunc_header, PCAP_ERRBUF_SIZE.
          eapply np_snp; [exact ST3 | exact FR | exact MI3 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
          { split; [exact G3|]. split; [exact PC3|]. split; [exact AG03|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| congruence]. }
          { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m3 0x103a3 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %zu header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                       MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
          { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
          pose proof (snprintf_length 256 "truncated dump file; tried to read %zu header bytes, only got %zu"%string [AInt hdrsize; AInt (zlength got)]) as LS.
          change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS. }
   
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
    step. if_cases Kq; [ try (zify_cond Kq; exfalso; clear - Kq LEQ GOTL WHS; unfold zlength in *; (keep_hyps LEQ Kq; lia)) | idtac ].
    assert (L16 : (16 <= length got)%nat) by (unfold zlength in LEQ; lia).
    destruct got as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|g8 [|g9 [|g10 [|g11 [|g12 [|g13 [|g14 [|g15 rest]]]]]]]]]]]]]]]];
      try (exfalso; cbn [length] in L16; (keep_hyps CEILV sp R P HA DA hcs dw L16; lia)). clear L16.
    pose proof GOTR as GR'. do 16 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']).
    pose proof (get_le32_hdr g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest) as (E0 & E4 & E8 & E12). cbv zeta in E0, E4, E8, E12.
    rewrite E0, E4, E8, E12. clear E0 E4 E8 E12.
    (* [comment removed for export] *)
    unhide HB.
    assert (LJ : length junk2 = (Z.to_nat hdrsize - (16 + length rest))%nat) by (destruct HB as [[WF _] _]; cbn in WF; cbn [length] in WF |- *; lia).
    assert (HB4 : rw_cells usegs m2 (bv_unsigned sp + -96)
              ([C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7)); C4 (Z_to_bv 64 (le4val g8 g9 g10 g11)); C4 (Z_to_bv 64 (le4val g12 g13 g14 g15))]
               ++ [CB (length rest) (map b8 rest); CB (length junk2) junk2])).
    { eapply rw_cells_recell; [exact HB | cbn; rewrite length_map; repeat split; try exact Logic.I; cbn [length] in LEQ |- *; unfold zlength in LEQ; cbn [length] in LEQ; lia |].
      cbn [cells_bytes cbytes app map]. rewrite (le4_lit g0 g1 g2 g3), (le4_lit g4 g5 g6 g7), (le4_lit g8 g9 g10 g11), (le4_lit g12 g13 g14 g15) by (keep_hyps CEILV sp R P HA DA hdrsize hcs dw g0 rest junk2 H0 g1 H1 g2 H2 g3 H3 g4 H4 g5 H5 g6 H6 g7 H7 g8 H8 g9 H9 g10 H10 g11 H11 g12 H12 g13 H13 g14 H14 g15 H15; lia).
      cbn [app]. rewrite app_nil_r. reflexivity. }
    hide HB. unhide CELLS.
    step. step. step. step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; (keep_hyps CEILV sp R P HA DA hdrsize hcs dw rest junk2; lia)). step. rewrite (sx32_lit g8 g9 g10 g11) by lia.
    step. rewrite (and7_aligned HA) by (clear - AH R1 R2 R3 SP47 RSP; unfold rc_spmain in *; lia).
    hide CELLS.
    (* [comment removed for export] *)
    assert (FRJ : forall mx, rw_cells usegs mx (bv_unsigned sp + -4208) [CB (Z.to_nat 4112) j0] ->
              rw_cells usegs mx (bv_unsigned sp + -96) [CB (length (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: g8 :: g9 :: g10 :: g11 :: g12 :: g13 :: g14 :: g15 :: rest))
                 (map b8 (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: g8 :: g9 :: g10 :: g11 :: g12 :: g13 :: g14 :: g15 :: rest)); CB (Z.to_nat hdrsize - length (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: g6 :: g7 :: g8 :: g9 :: g10 :: g11 :: g12 :: g13 :: g14 :: g15 :: rest)) junk2] ->
              rw_cells usegs mx (bv_unsigned sp + -96 + hdrsize) [CB (24 - Z.to_nat hdrsize) j2] ->
              rw_cells usegs mx (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              exists fj, rw_cells usegs mx (bv_unsigned sp + -4208) [CB (Z.to_nat 4136) fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { intros mx X0 XB X2 XS.
      pose proof (rw_cells_uncut _ _ _ _ _ X0 XB ltac:(cbn [cells_size csize]; lia)) as FJ.
      pose proof (rw_cells_uncut _ _ _ _ _ FJ X2 ltac:(cbn [cells_size csize app]; unfold zlength in LEQ; lia)) as FJ'. clear FJ.
      cbn [app] in FJ'. merge_all_lin FJ'.
      lazymatch type of FJ' with rw_cells _ _ _ [CB ?k _] => replace k with (Z.to_nat 4136) in FJ' by (unfold zlength in LEQ; cbn [length] in LEQ |- *; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw rest junk2 WHS LEQ; lia)) end.
      pose proof (rw_cells_uncut _ _ _ _ _ FJ' XS ltac:(cbn [cells_size csize]; (keep_hyps CEILV sp R lo P HA DA hdrsize hcs dw rest junk2 WHS; lia))) as FR'. cbn [app] in FR'. eexists. exact FR'. }
    destruct (Bool.bool_dec swapped true) as [ES|ES]; [| apply Bool.not_true_is_false in ES].
    - (* [comment removed for export] *)
      rewrite !(if_b_true swapped _ _ ES). replace (Z.b2z swapped) with 1%Z by (rewrite ES; reflexivity).
      step. if_false.
      step. if_false_by (eqz_false HA ltac:(clear - R1 R2 R3 SP47 LO BU SPW; unfold rc_lo, rc_spmain in *; lia)). step. if_false.
      unhide HB.
      eapply evt_cut. { eapply (np_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15); [| exact HB4]. repeat (apply Forall_cons; [assumption|]). apply Forall_nil. }
      cbv beta. intros ms' PO. destruct PO as (t0v & t1v & a4v & a5v & a6v & a7v & a0v & a2v & a3v & s7v & -> & Fc & Fs & Fu & Fl).
      rewrite (bswap32_le4val g0 g1 g2 g3), (bswap32_le4val g4 g5 g6 g7), (bswap32_le4val g8 g9 g10 g11), (bswap32_le4val g12 g13 g14 g15) by (keep_hyps CEILV sp R P HA DA hdrsize hcs dw g0 rest junk2 a0v a2v a3v s7v H0 g1 H1 g2 H2 g3 H3 g4 H4 g5 H5 g6 H6 g7 H7 g8 H8 g9 H9 g10 H10 g11 H11 g12 H12 g13 H13 g14 H14 g15 H15; lia).
      rewrite <- (Z_to_bv_bv_unsigned a0v), <- (Z_to_bv_bv_unsigned a2v), <- (Z_to_bv_bv_unsigned a3v), <- (Z_to_bv_bv_unsigned s7v).
      rewrite <- Fc, <- Fs, <- Fu, <- Fl.
      unhide F0. unhide F2. unhide FS. unhide HH. unhide HD.
      destruct (FRJ m2 F0 HB F2 FS) as [fj FR].
      pose proof (bv_unsigned_in_range 64 a0v). pose proof (bv_unsigned_in_range 64 a2v). pose proof (bv_unsigned_in_range 64 a3v). pose proof (bv_unsigned_in_range 64 s7v).
      unfold bv_modulus in *.
      apply evt_done. eapply (np_hdr_sw lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 ps2 (bv_unsigned a2v) (bv_unsigned a3v) (bv_unsigned a0v) (bv_unsigned s7v) hcs dw fj);
        [exact ST2 | exact FR | exact MI2 | exact G2 | exact PC2 | exact AG02 | exact HH | exact Hh | exact HD | exact Hd | lia | lia | lia | lia | congruence].
    - (* [comment removed for export] *)
      rewrite !(if_b_false swapped _ _ ES). replace (Z.b2z swapped) with 0%Z by (rewrite ES; reflexivity).
      step. if_true.
      unhide HB. unhide F0. unhide F2. unhide FS. unhide HH. unhide HD.
      destruct (FRJ m2 F0 HB F2 FS) as [fj FR].
      apply evt_done. eapply (np_unsw lsw scl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 ps2 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 _ hcs dw fj);
        [exact ST2 | exact FR | exact MI2 | exact G2 | exact PC2 | exact AG02 | exact HH | exact Hh | exact HD | exact Hd | repeat (apply Forall_cons; [assumption|]); apply Forall_nil | exact HB4 | congruence].
  Qed.
  End Sz2.
  Lemma np_main : ltac:(let t := eval cbv delta [np_main__stmt] in np_main__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros lsw scl t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ps hcs dw. ltac2:(SecDiet.SzSec.closeP 'np_main__body "vvvvvvvvvvvvvvvvv"). Qed.
End NpCtxD.

Section NpThm.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis PP : post_process_stmt.

  Definition pcap_next_packet_proof__stmt : Prop := pcap_next_packet_stmt HO K sites.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HA DA p fuel hcs dc : ltac2:(SecDiet.SzSec.tyM 'pcap_next_packet_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_next_packet_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_next_packet_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FERROR FMT FREAD HAL HFL HPL PP REALLOC SFL SNPRINTF. all: natfold_lits. pin_using (fun (FERROR FMT FREAD HAL HFL HPL PP REALLOC SFL SNPRINTF : unit) => tt).
 intros PRE PC NG SITES -> -> -> HHA Hhcs HDA Hdc R1 R2 R3 AH AD.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. unfold rc_lo in LO. unfold PCAP_L2_STACK in BU.
    destruct p as [self rfile bufsize bufalloc buffer bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header priv].
    destruct priv as [sf|ng oif]; [| discriminate NG]. clear NG. destruct sf as [hdrsize lsw scl].
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & _ & _ & _ & _ & IFS & WF)).
    cbn [pc_priv ifaces_ok] in IFS. subst I.
    unfold pcap_wf in WF. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
         pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in WF.
    destruct WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & WHS & WBB).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    unfold psize, is_ng in P3, P4, P5, P6. cbn [pc_priv] in P3, P4, P5, P6. unfold PCAP_SF_TOTAL in P3, P4, P5, P6.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & _ & _).
    cbn [cb_addr cb_size fst snd] in A1, A4. unfold FILE_BLOCK in A4.
    rewrite EPB in G, PC.
    unfold next_packet_op, S3.PcapRep.TwB.np_entry, is_ng. cbn [pc_priv pk_next_pcap PK].
    eapply np_main; try eassumption; try reflexivity; try (keep_hyps CEILV sp R P HA DA hcs dc bufdata SPW bufsize W2; lia).
    - exact pp_length.
    - exact pp_sec.
    - exact pp_range.
  Qed.
  End Sz3.
  Theorem pcap_next_packet_proof : ltac:(let t := eval cbv delta [pcap_next_packet_proof__stmt] in pcap_next_packet_proof__stmt in exact t).
  Proof using FERROR FMT FREAD HAL HFL HPL PP REALLOC SFL SNPRINTF. all: natfold_lits. red. unfold next_packet_op_stmt_for. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HA DA p fuel hcs dc. ltac2:(SecDiet.SzSec.closeP 'pcap_next_packet_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpThm.

End WithCeil.
End TwB.
End F_sfpcap_next.
