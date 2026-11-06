(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkB__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From Stdlib Require Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcapng_ai__U3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_chkD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfpcap_chk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcap_swap.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require Import F_sfpcap_chkA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkB__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_chkB.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcap_chkF.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
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
           (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x7 : word)
           (m m1 : mem) (R : rctx) (s : PState H hptr) (CL FB : list cblock) (lo MG FA EB ERR : Z) (f : hptr)
           (magic : list Z) (ej junk : list byte) (W mi : Z) (sw : bool),
      GIo K R s CL FB m -> (usp0 R - 8388608 <= lo)%Z -> (lo + 81920 <= bv_unsigned sp)%Z -> (bv_unsigned sp <= rc_spmain R)%Z ->
      tp = rc_tp R -> (bv_unsigned sp mod 16 = 0)%Z ->
      In (f, FA, FILE_BLOCK) FB -> sites = sites_at (bv_unsigned sp + D_CHECK_HEADER) ->
      length magic = 4%nat -> Forall (fun z => 0 <= z < 256)%Z magic ->
      (bv_unsigned sp <= ERR)%Z -> (ERR + 4 <= MG)%Z -> (MG + 4 <= rc_spmain R)%Z ->
      (bv_unsigned sp <= EB)%Z -> (EB + 256 <= rc_spmain R)%Z -> (EB + 256 <= ERR \/ MG + 4 <= EB)%Z -> (ERR mod 4 = 0)%Z -> (EB mod 8 = 0)%Z ->
      (mi = TCPDUMP_MAGIC \/ mi = KUZNETZOV_TCPDUMP_MAGIC \/ mi = NSEC_TCPDUMP_MAGIC) -> (0 <= W < 2^64)%Z ->
      (if sw then W <> 18446744072127431636 /\ W <> 18446744072127434036 /\ W <> 18446744072127396941 else W = mi + (2^64 - 2^32))%Z ->
      mem_inv usegs m1 -> stk usegs m1 lo (bv_unsigned sp + -96) ->
      munch [(bv_unsigned sp + -96, bv_unsigned sp); (ERR, ERR + 4)]%Z m m1 -> wmono usegs m m1 ->
      rw_cells usegs m1 (bv_unsigned sp + -96) [CB 24 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m1 ERR [C4 z64] -> rw_cells usegs m1 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m EB [CB 256 ej] ->
      implM usegs (chk_rest MOps (prims HO fo_nop sites) f 0 mi sw) s
        (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0 a1 a2 a3 a4 a5 a6 a7
                 z64 (Z_to_bv 64 FA) (Z_to_bv 64 W) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 (Z.b2z sw)) x7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x15588) fc None m1 (seg_rom usegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x7 m m1 R s CL FB lo MG FA EB ERR f magic ej junk W mi sw : ltac2:(SecDiet.SzSec.tyM 'chk_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_tail__body : ltac2:(SecDiet.SzSec.bodyP 'chk_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FERROR FMT FREAD FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF. pin_using (fun (FERROR FMT FREAD FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF : unit) => tt).
    intros G LO BU SPM TP ALN HinF SITES GL GR R1 R2 R3 E1 E2 D1 E4 E8 MI3 WR SW5 MI1 ST MU WM FR ERRc MG4 HEB.
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
    assert (HEB1 : rw_cells usegs m1 EB [CB 256 ej]).
    { eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB |].
      intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia. }
    clear MU WM HEB.
    unfold chk_rest. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_malloc e_calloc e_free e_last_errno prims read_fail_msg errmsg_for_errno].
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs _ _ [] 24 _ [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [4; 20]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    lazymatch type of FR with rw_cells _ _ _ (CB _ ?l0 :: CB _ ?l1 :: _) => set (j0 := l0) in FR; set (j1 := l1) in FR; clearbody j0 j1 end.
    ienter. do 2 step.
    destruct (rw_cells_cut _ _ _ 1 FR) as [FRA FR']. clear FR. cbn [firstn skipn cells_size csize Nat.add] in FRA, FR'.
    destruct (rw_cells_cut _ _ _ 1 FR') as [FRD FRS]. clear FR'. cbn [firstn skipn cells_size csize Nat.add] in FRD, FRS.
    replace (bv_unsigned sp + -96 + Z.of_nat 4 + Z.of_nat 20)%Z with (bv_unsigned sp + -72)%Z in FRS by lia.
    replace (bv_unsigned sp + -96 + Z.of_nat 4)%Z with (bv_unsigned sp + -92)%Z in FRD by lia.
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
    name_sp sp (-96)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop].
      replace (sites SitePcapHdrRest + 0)%Z with (bv_unsigned sp + -92)%Z by (rewrite SITES; unfold sites_at, D_CHECK_HEADER; lia).
      eapply FREAD; [ split; [exact G1|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact FRD | right; rewrite Hsp; lia]. }
    intros got s' ms' PO. cbv beta in PO.
    destruct PO as (av & m2 & junk' & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & GOTL & GOTR & HD2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 87460)) with (Z_to_bv 64 87460) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch type of AG2 with agrees_on _ ?ma _ =>
    assert (KEEP : forall A cs, rw_cells usegs ma A cs -> (bv_unsigned sp + -96 <= A)%Z ->
                   (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -92 \/ bv_unsigned sp + -72 <= A)%Z -> rw_cells usegs m2 A cs)
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
    pose proof (GIo_tls K _ _ _ _ _ G2) as [_ TB]. unfold tls_block_ok_u in TB.
    pose proof TB as TB'. unfold utp in TB'. rewrite <- TP in TB'.
    assert (CTX : U3.F_sfpcap_chkA.chk_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m).
    { split; [exact G|]. repeat (split; [eassumption|]). eassumption. }
    unfold zlength in *.
    assert (U64 : (usp0 R < 2^64)%Z) by (unfold usp0; pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as X; unfold bv_modulus in X; cbn in X; lia).
    pose proof (rw_cells_bound _ _ _ _ HEB1) as BEB. cbn [cells_size csize Nat.add] in BEB.
    destruct (Z.eq_dec (Z.of_nat (length got)) 20) as [L20|L20].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) L20). cbn [negb].
      apply (implM_bind_assoc usegs).
      assert (HC32 : exists hc, rw_cells usegs m2 (bv_unsigned sp + -96) hc /\ cells_size hc = 24%nat).
      { exists ([C4 (Z_to_bv 64 (mi + (2 ^ 64 - 2 ^ 32)))] ++ [CB (length got) (map b8 got); CB (Z.to_nat 20 - length got) junk']).
        split; [eapply rw_cells_uncut; [exact FRA | exact HD2 | cbn; lia]| cbn [cells_size csize Nat.add app]; lia]. }
      destruct HC32 as (hc & FA2 & Hhc). clear FRA HD2. hide HEB1. hide MG4.
      ienter. step. rewrite (eqb_lits_false (Z.of_nat (length got)) 20) by lia. cbn [negb]. cbv iota. do 3 step.
      name_sp sp (-96)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G2|]. split; [rewrite Hsp; exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [|] ps3 ms3 PO; cbv beta in PO; destruct PO as (av3 & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO);
        unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hsp in *; unname_sp;
        replace (ret_pc (Z_to_bv 64 87724)) with (Z_to_bv 64 87724) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
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
        assert (T4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
        { destruct TB' as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [tq Hq]. apply Z.mod_divide; [lia|]. exists (tq * 4 + 9)%Z. lia. }
        cbn [Z.b2z]. step. if_false. do 5 step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(clear - TB'; lia)).
        step. rewrite (and3_aligned (bv_unsigned tp + -164)) by (clear - TB' T4; lia). step. if_false. do 6 step.
        replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
        assert (MSG : fmt_at m3 0x108d6 "error reading dump file"%string).
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m3 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        name_sp sp (-96)%Z.
        eapply evt_cut.
        { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 0x108d6%Z e "error reading dump file"%string [] ej);
            [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB1
             | right; rewrite Hsp; lia | exact E8 ].
          split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
        cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & junk4 & -> & MI4 & ST4 & AG4 & G4 & HEB4).
        rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 87768)) with (Z_to_bv 64 87768) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (KEEP4 : forall A cs, rw_cells usegs m3 A cs -> (bv_unsigned sp + -96 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells usegs m4 A cs).
        { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG4 | exact HC | intros a Ha; split; [left; lia| lia]]. }
        apply KEEP4 in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP4 in FA2; [|lia|rewrite Hhc; lia]. clear KEEP4.
        assert (ERR4 : rw_cells usegs m4 ERR [C4 z64]) by (eapply agrees_rw_cells; [exact AG4 | exact ERRc | intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]]).
        assert (MG5 : rw_cells usegs m4 MG (map (fun z => C1 (Z_to_bv 8 z)) magic))
          by (eapply agrees_rw_cells; [exact AG4 | exact MG4 | intros a Ha; rewrite cells_size_map_C1, GL in Ha; split; [left; lia| lia]]).
        hide HEB4. step. unhide HEB4.
        eapply (U3.F_sfpcap_chkA.chk_fail K sites HFL SFL); [exact CTX | assumption | assumption | | exact G4 | exact FA2 | exact Hhc | exact FRS | exact ERR4 | exact MG5 | exact HEB4
                      | pose proof (fmt_errmsg_length "error reading dump file"%string [] e); lia
                      | apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor] | congruence].
        eapply agrees_on_trans; [exact AG03|]. eapply agrees_on_weaken; [exact AG4|]. intros a [[Ha|Ha] [Hn _]]; (split; [|exact Hn]); [left; lia| right; exact Ha].
      + (* [comment removed for export] *)
        eapply implM_pure; [reflexivity|]. cbn [fst snd].
        cbn [Z.b2z]. step. if_true. do 8 step.
        assert (MSG : fmt_at m3 0x1050c "truncated dump file; tried to read %zu file header bytes, only got %zu"%string).
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m3 0x1050c (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %zu file header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                   MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        name_sp sp (-96)%Z.
        eapply evt_cut.
        { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 256%Z 0x1050c%Z
                    "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 24; AInt (Z.of_nat (length got))] ej);
            [| reflexivity | reflexivity | reflexivity | lia | exact MSG | vm_compute; reflexivity | cbn; lia | | exact HEB1 | right; rewrite Hsp; lia].
          { split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
            split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
          cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
        cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
        unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 87988)) with (Z_to_bv 64 87988) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -96 - STDIO_STACK, bv_unsigned sp + -96); (EB, EB + 256)]%Z a) m3 m4)
          by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
        unfold STDIO_STACK in AGS.
        assert (KEEP4 : forall A cs, rw_cells usegs m3 A cs -> (bv_unsigned sp + -96 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells usegs m4 A cs).
        { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AGS | exact HC | intros a Ha; cbn [outside]; lia]. }
        apply KEEP4 in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP4 in FA2; [|lia|rewrite Hhc; lia]. clear KEEP4.
        assert (ERR4 : rw_cells usegs m4 ERR [C4 z64]) by (eapply agrees_rw_cells; [exact AGS | exact ERRc | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]).
        assert (MG5 : rw_cells usegs m4 MG (map (fun z => C1 (Z_to_bv 8 z)) magic))
          by (eapply agrees_rw_cells; [exact AGS | exact MG4 | intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia]).
        assert (G4 : GIo K R s' CL FB m4).
        { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |].
          apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, STDIO_STACK; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
        change (Z.to_nat 256) with 256%nat in HEB4.
        replace (256 - length (Fmt.snprintf 256 "truncated dump file; tried to read %zu file header bytes, only got %zu" [AInt 24; AInt (Z.of_nat (length got))]) - 1)%nat
          with (255 - length (Fmt.snprintf 256 "truncated dump file; tried to read %zu file header bytes, only got %zu" [AInt 24; AInt (Z.of_nat (length got))]))%nat in HEB4 by lia.
        eapply (U3.F_sfpcap_chkA.chk_fail K sites HFL SFL); [exact CTX | assumption | assumption | | exact G4 | exact FA2 | exact Hhc | exact FRS | exact ERR4 | exact MG5 | exact HEB4
                      | pose proof (snprintf_length 256 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 24; AInt (Z.of_nat (length got))]) as LS;
                        change (Z.to_nat (256 - 1)) with 255%nat in LS; unfold Msg.trunc_file_header, PCAP_ERRBUF_SIZE; lia
                      | unfold Msg.trunc_file_header; apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] | congruence].
        eapply agrees_on_trans; [exact AG03|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|]. pose proof (CLB a Ha). unfold rc_lo in LO. split; [lia|]. split; [exact Hn1| exact Logic.I]. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) L20). cbn [negb].
    assert (L20n : length got = 20%nat) by lia.
    destruct got as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|g8 [|g9 [|g10 [|g11 [|g12 [|g13 [|g14 [|g15 [|g16 [|g17 [|g18 [|g19 [|gx gr]]]]]]]]]]]]]]]]]]]]]; try (exfalso; cbn in L20n; lia).
    clear L20n L20 GOTL.
    pose proof GOTR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    assert (LJ : length junk' = 0%nat) by (destruct HD2 as [[WF _] _]; cbn in WF; lia).
    destruct junk' as [|jx jr]; [|discriminate LJ]. clear LJ.
    (* [comment removed for export] *)
    assert (HD5 : rw_cells usegs m2 (bv_unsigned sp + -92)
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
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -92, bv_unsigned sp + -72)]%Z a) m2 m4)
        by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
      assert (KEEP : forall A cs, rw_cells usegs m2 A cs -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -92 \/ bv_unsigned sp + -72 <= A)%Z -> rw_cells usegs m4 A cs).
      { intros A cs HC HA. eapply agrees_rw_cells; [exact AGS | exact HC | intros a Ha; cbn [outside]; lia]. }
      apply KEEP in FRA; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP in FRS; [|cbn [cells_size csize Nat.add]; lia].
      apply KEEP in ERRc; [|cbn [cells_size csize Nat.add]; lia]. apply KEEP in MG4; [|rewrite cells_size_map_C1, GL; lia]. apply KEEP in HEB1; [|cbn [cells_size csize Nat.add]; lia].
      assert (G4 : GIo K R s' CL FB m4).
      { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU4 | exact WM4 |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (ST4 : stk usegs m4 lo (bv_unsigned sp + -96)).
      { eapply stk_transport_disjoint; [exact ST2 | exact MU4 | exact WM4 | cbn [disjoint_from]; unfold rc_lo in LO; lia]. }
      assert (AG04 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m4).
      { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (CLB a Ha). unfold rc_lo in LO. lia. }
      rewrite (bswap16_bytes g0 g1), (bswap16_bytes g2 g3), (bswap32_bytes g12 g13 g14 g15), (bswap32_bytes g16 g17 g18 g19) by lia.
      cbv iota. rewrite !le_of_bytes_2, !le_of_bytes_4. change (Z.b2z true) with 1%Z.
      replace (g15 + 256 * g14 + 65536 * g13 + 16777216 * g12)%Z with (le4val g15 g14 g13 g12) by reflexivity.
      replace (g19 + 256 * g18 + 65536 * g17 + 16777216 * g16)%Z with (le4val g19 g18 g17 g16) by reflexivity.
      apply evt_done. eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_chkB.TwB.chk_hdr HO K sites HFL SFL HPL SNPRINTF OPEN_COMMON MALLOC FREE) with (sw := true);
        [exact CTX | exact MI3 | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact MI4 | exact ST4 | exact AG04 | exact G4
        | exact FRA | exact HD4 | exact FRS | exact ERRc | exact MG4 | exact HEB1 | congruence].
    - (* [comment removed for export] *)
      subst W. cbv iota. rewrite !le_of_bytes_2, !le_of_bytes_4. change (Z.b2z false) with 0%Z.
      replace (g12 + 256 * g13 + 65536 * g14 + 16777216 * g15)%Z with (le4val g12 g13 g14 g15) by reflexivity.
      replace (g16 + 256 * g17 + 65536 * g18 + 16777216 * g19)%Z with (le4val g16 g17 g18 g19) by reflexivity.
      unhide HEB1. unhide MG4. unhide ERRc.
      destruct MI3 as [-> | [-> | ->]].
      + do 2 step. step. lit_branch. do 2 step. step. lit_branch.
        apply evt_done. eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_chkB.TwB.chk_hdr HO K sites HFL SFL HPL SNPRINTF OPEN_COMMON MALLOC FREE) with (sw := false);
          [exact CTX | left; reflexivity | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact MI2 | exact ST2 | exact AG02 | exact G2
          | exact FRA | exact HD5 | exact FRS | exact ERRc | exact MG4 | exact HEB1 | congruence].
      + do 2 step. step. lit_branch. do 2 step. step. lit_branch. do 2 step. step. lit_branch.
        apply evt_done. eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_chkB.TwB.chk_hdr HO K sites HFL SFL HPL SNPRINTF OPEN_COMMON MALLOC FREE) with (sw := false);
          [exact CTX | right; left; reflexivity | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact MI2 | exact ST2 | exact AG02 | exact G2
          | exact FRA | exact HD5 | exact FRS | exact ERRc | exact MG4 | exact HEB1 | congruence].
      + do 2 step. step. lit_branch.
        apply evt_done. eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkB__S3.F_sfpcap_chkB.TwB.chk_hdr HO K sites HFL SFL HPL SNPRINTF OPEN_COMMON MALLOC FREE) with (sw := false);
          [exact CTX | right; right; reflexivity | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact MI2 | exact ST2 | exact AG02 | exact G2
          | exact FRA | exact HD5 | exact FRS | exact ERRc | exact MG4 | exact HEB1 | congruence].
  Qed.
  End Sz1.
  Lemma chk_tail : ltac:(let t := eval cbv delta [chk_tail__stmt] in chk_tail__stmt in exact t).
  Proof using FERROR FMT FREAD FREE HFL HPL MALLOC OPEN_COMMON SFL SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x7 m m1 R s CL FB lo MG FA EB ERR f magic ej junk W mi sw. ltac2:(SecDiet.SzSec.closeP 'chk_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

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
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (ERR, ERR + 4)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (ERRR : (0 < ERR /\ ERR + 4 < 2^64)%Z) by (unfold rc_spmain in *; pose proof (GIo_sp47 K _ _ _ _ _ G); lia).
    (* [comment removed for export] *)
    assert (MG4 : rw_cells usegs m MG [C1 (b8 m0); C1 (b8 m1); C1 (b8 m2); C1 (b8 m3)]).
    { eapply rw_cells_recell; [exact HMG | cbn; repeat split; exact Logic.I | reflexivity]. }
    clear HMG. hide HEB.
    pose proof (magic_cases m0 m1 m2 m3 G0 G1 G2 G3) as CASES. cbv zeta in CASES.
    destruct CASES as [C1' | [C2' | [C3' | [C4' | [C5' | [C6' | [NM1 NM2]]]]]]].
    7:{ (* [comment removed for export] *)
      unfold pcap_check_header. rewrite NM1, NM2. cbn [negb mo_ret mo_bind MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. unfold b8 in MG4.
      pose proof (magic_none m0 m1 m2 m3 G0 G1 G2 G3 NM1 NM2) as (N1 & N2 & N3 & N4 & N5 & N6).
      pose proof (magic_sx_range m0 m1 m2 m3 G0 G1 G2 G3) as WR.
      set (W := magic_sx m0 m1 m2 m3) in *.
      apply (implM_ret usegs).
      carve_frame 96%nat ST.
      (lazymatch goal with
    | FRx : rw_cells usegs ?mm ?A [CB 96 ?j] |- _ =>
        apply (rw_cells_split_CB usegs mm A [] 96 j [] [24; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end).
      do 10 step.
      step. if_false_by (eqz_false ERR ltac:(clear - ERRR; lia)). do 2 step. step. rewrite (and3_aligned ERR) by (clear - ERRR E4; lia). step. if_false. do 3 pstep.
      do 4 step. rewrite ?zxb_lit, ?sxb_lit by lia. do 8 step. rewrite (magic_word m0 m1 m2 m3) by lia. fold W.
      step. if_cases Kblt.
      1: do 2 step; if_cases K4; [ try (zify_cond K4; exfalso; lia) | idtac ].
      1: do 3 step; if_cases K5; [ try (zify_cond K5; exfalso; lia) | idtac ].
      1: do 4 step; if_cases K6; [ idtac | try (zify_cond K6; exfalso; lia) ].
      2: do 3 step; if_cases K1; [ try (zify_cond K1; exfalso; lia) | idtac ].
      2: do 3 step; if_cases K2; [ try (zify_cond K2; exfalso; lia) | idtac ].
      2: do 6 step; if_cases K3; [ try (zify_cond K3; exfalso; lia) | idtac ].
      2: step.
      all: do 11 step.
      all: release_frame FR ST (bv_unsigned sp).
      all: unhide HEB.
      all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGW : agrees_on (fun a => outside [(bv_unsigned sp - 96, bv_unsigned sp); (ERR, ERR + 4)]%Z a) m mm)
          by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
        assert (HEB' : rw_cells usegs mm EB [CB 256 ej])
          by (eapply agrees_rw_cells; [exact AGW | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; unfold rc_lo in LO; lia]);
        assert (G' : GIo K R s CL FB mm)
          by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |];
              apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
        assert (MG' : rw_cells usegs mm MG [CB 4 [Z_to_bv 8 m0; Z_to_bv 8 m1; Z_to_bv 8 m2; Z_to_bv 8 m3]])
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
    all: unfold b8 in MG4; ienter; carve_frame 96%nat ST; (lazymatch goal with     | FRx : rw_cells usegs ?mm ?A [CB 96 ?j] |- _ =>         apply (rw_cells_split_CB usegs mm A [] 96 j [] [24; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];         cbn [app mk_CB_cells] in FRx;         repeat match type of FRx with         | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end         end     end); do 10 step; step; if_false_by (eqz_false ERR ltac:(clear - ERRR; lia)); do 2 step; step;
         rewrite (and3_aligned ERR) by (clear - ERRR E4; lia); step; if_false; do 3 pstep; do 4 step; rewrite ?zxb_lit, ?sxb_lit by lia.
    all: repeat match goal with |- context [Z_to_bv 64 (?a - 256 * (?a / 128))%Z] => let v := eval vm_compute in (a - 256 * (a/128))%Z in change (a - 256 * (a / 128))%Z with v end.
    all: steps_to 87432%Z.
    all: unhide HEB. all: apply evt_done.
    6: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [161; 178; 60; 77]%Z ej _ _ NSEC_TCPDUMP_MAGIC true).
    5: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [161; 178; 205; 52]%Z ej _ _ KUZNETZOV_TCPDUMP_MAGIC true).
    4: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [161; 178; 195; 212]%Z ej _ _ TCPDUMP_MAGIC true).
    3: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [77; 60; 178; 161]%Z ej _ _ NSEC_TCPDUMP_MAGIC false).
    2: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [52; 205; 178; 161]%Z ej _ _ KUZNETZOV_TCPDUMP_MAGIC false).
    1: eapply (chk_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ R s CL FB lo MG FA EB ERR f [212; 195; 178; 161]%Z ej _ _ TCPDUMP_MAGIC false).
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
Module F_sfpcapng_chkE.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require Import F_sfpcap_chkA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcapng_chkK. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_chkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_chkF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkB.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcapng_ai__U3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcapng_ai__U3.F_sfpcapng_chkC. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_chkD__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_sfpcapng_chkD.TwB.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Ubsan.
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
Lemma swap16_word : forall a b, (0 <= a < 256)%Z -> (0 <= b < 256)%Z ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zx16 (Z_to_bv 64 (a + 256 * b)))) 8)))
                    (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (zx16 (Z_to_bv 64 (a + 256 * b)))) 8))))
  = Z_to_bv 64 (b + 256 * a + 65536 * b)%Z.
Proof using Type. pin_using tt.
  intros a b Ha Hb. apply bv_eq. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.swap16_val _ a b); [| lia | lia | apply unsigned_zx16; lia]. rewrite unsigned_lit by lia. reflexivity.
Qed.
Lemma shl48_lit : forall x, (0 <= x < 65536)%Z -> Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 48) = Z_to_bv 64 (x * 2 ^ 48)%Z.
Proof using Type. pin_using tt. intros x Hx. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sextw_low : forall (w : word) x hi, (bv_unsigned w = x + 4294967296 * hi)%Z -> (0 <= x < 2^31)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned w + 0)) = Z_to_bv 64 x.
Proof using Type. pin_using tt. intros w x hi E Hx. rewrite (swrap32_low _ x hi E). rewrite s32_small by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma le4_low : forall (w : word) x hi, (bv_unsigned w = x + 4294967296 * hi)%Z -> (0 <= x < 2^32)%Z -> (0 <= hi < 2^32)%Z ->
  le4 w = map b8 (le_bytes 4 x).
Proof using Type. pin_using tt.
  intros w x hi E Hx Hhi. replace w with (Z_to_bv 64 (x + 4294967296 * hi)) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  rewrite le4_mod32 by lia. apply le4_le_bytes. lia.
Qed.
End WithCeil.


(* [comment removed for export] *)
Lemma msg_ok_b : forall l : list Z, forallb (fun z => (0 <? z)%Z && (z <? 256)%Z) l = true -> Forall (fun z => 0 < z < 256)%Z l.
Proof. intros l H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. Qed.
Ltac msg_ok := first [ apply msg_ok_b; vm_compute; reflexivity
                     | vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]] ].
Ltac prsMG GL := intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; repeat match goal with |- _ /\ _ => split end; fastfirst (first [lia | left; lia | exact Logic.I]).

Section WithCeil.
Context {CEILV : CEIL}.
Definition land2_cases__stmt : Prop := forall x, (0 <= x)%Z -> Z.land x 2 = 0%Z \/ Z.land x 2 = 2%Z.
Section Sz5.
Variables x : ltac2:(SecDiet.SzSec.tyM 'land2_cases__stmt "v" @x).
Lemma land2_cases__body : ltac2:(SecDiet.SzSec.bodyP 'land2_cases__stmt "v").
Proof using Type. pin_using tt.
  intros Hx.
 destruct (Z.testbit x 1) eqn:E.
  - right. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
    destruct (Z.eq_dec n 1) as [->|Hn1]; [rewrite E; reflexivity|].
    replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|].
    change 2%Z with (2^1)%Z. rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
  - left. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec n 1) as [->|Hn1]; [rewrite E; reflexivity|].
    replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|].
    change 2%Z with (2^1)%Z. rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.
End Sz5.
Lemma land2_cases : ltac:(let t := eval cbv delta [land2_cases__stmt] in land2_cases__stmt in exact t).
Proof using Type. intros x. ltac2:(SecDiet.SzSec.closeP 'land2_cases__body "v"). Qed.
Lemma lor2_eqb2 : forall x, (0 <= x)%Z -> (Z.lor x 2 =? 2)%Z = ((x =? 0) || (x =? 2))%Z.
Proof using Type. pin_using tt.
  intros x Hx.
  pose proof (Z.add_lor_land x 2) as A. pose proof (land2_cases x Hx) as B.
  destruct (Z.eq_dec x 0) as [->|N0]; [reflexivity|]. destruct (Z.eq_dec x 2) as [->|N2]; [reflexivity|].
  destruct (Z.eq_dec x 1) as [->|N1]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq x 0) N0), (proj2 (Z.eqb_neq x 2) N2). cbn. apply Z.eqb_neq. lia.
Qed.
Lemma lor2_range : forall x, (0 <= x < 65536)%Z -> (0 <= Z.lor x 2 < 65538)%Z.
Proof using Type. pin_using tt. intros x Hx. pose proof (Z.add_lor_land x 2) as A. pose proof (land2_cases x ltac:(lia)). pose proof (proj2 (Z.lor_nonneg x 2) ltac:(lia)). lia. Qed.

Section ChkNg.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREE : free_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z).
  Hypothesis CTX : ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m.
  #[local] Notation POSTQ := (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
  #[local] Notation AGQ := (ngc_AGQ sp CL EB ERR m).
  #[local] Notation FRS := (ngc_FRS ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
  #[local] Notation PR := (prims HO fo_nop sites).

  Open Scope bv_scope.

  Hypothesis OPEN_COMMON : open_offline_common_stmt HO K sites.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis RBYTES : read_bytes_stmt HO K sites.
  Hypothesis RB : read_block_stmt HO K sites.
  Hypothesis AI : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Definition ngc_fill__stmt : Prop := forall (fuel : nat) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w7 w9 : word) (sw : bool) (TL hi7 hi9 : Z)
           (m1 : mem) (ps1 : PS) (hc : list cell) (ew : word) (e : list byte),
      (bv_unsigned w9 = TL + 4294967296 * hi9)%Z -> (0 <= hi9 < 2^32)%Z -> (28 <= TL <= 1048576)%Z ->
      (bv_unsigned w7 = BYTE_ORDER_MAGIC + 4294967296 * hi7)%Z -> (0 <= hi7 < 2^32)%Z ->
      mem_inv usegs m1 -> stk usegs m1 lo (bv_unsigned sp + -128) -> AGQ m1 -> GIo K R ps1 CL FB m1 -> ps_outfile ps1 = ps_outfile s ->
      rw_cells usegs m1 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat -> FRS m1 ->
      rw_cells usegs m1 ERR [C4 ew] -> rw_cells usegs m1 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m1 EB [CB 256 e] ->
      implM usegs (ngc_open MOps PR fuel f 0 BT_SHB sw TL) ps1 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 FA) (Z_to_bv 64 (Z.b2z sw)) s4 w7 s6 (Z_to_bv 64 0) w9 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x16cf0) fc None m1 (seg_rom usegs)).
  Section Sz8.
  Variables fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w7 w9 sw TL hi7 hi9 m1 ps1 hc ew e : ltac2:(SecDiet.SzSec.tyM 'ngc_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AI CTX FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. pin_using (fun (AI CTX FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF : unit) => tt).
 intros W9 HI9 TLR W7 HI7 MI1 ST1 AG1 G1 OF1 HC1 Hhc FRS1 ERR1 MG1 HEB1.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    unfold ngc_open. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. unfold PCAP_TSTAMP_PRECISION_MICRO. cbn [Z.eqb mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims].
    hide HC1. hide FRS1. hide ERR1. hide MG1.
    unfold implM. iprefix.
    do 4 step.
    apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind usegs).
    { eapply (OPEN_COMMON _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 R ps1 CL FB lo EB PCAP_NG_SF_TOTAL e);
        [ split; [exact G1|]; split; [rewrite Hsp; exact ST1|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L1B_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI1|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | reflexivity | reflexivity | right; reflexivity | exact HEB1 | right; rewrite Hsp; lia | exact E8 ]. }
    intros r ps2 ms2 PO. destruct PO as (a0v & m2 & E & OF2 & MI2 & ST2 & AG2 & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms2. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x16d00)) with (Z_to_bv 64 0x16d00) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide HC1. unhide FRS1. unhide ERR1. unhide MG1.
    transport HC1 m2 AG2 ltac:(intros a Ha; rewrite Hhc in Ha; split; [left; lia| lia]).
    unfold ngc_FRS in FRS1. transport FRS1 m2 AG2 ltac:(prs). transport ERR1 m2 AG2 ltac:(prs). transport MG1 m2 AG2 ltac:(prsMG GL).
    assert (AG12 : AGQ m2).
    { unfold ngc_AGQ in AG1 |- *. eapply agrees_on_trans; [exact AG1|]. eapply agrees_on_weaken; [exact AG2|]. intros a [Ha [Hn _]]. split; [| exact Hn].
      destruct Ha as [Ha|Ha]; [left; lia| right; exact Ha]. }
    clear AG1 AG2 MI1 ST1.
    destruct r as [msg | q].
    { (* [comment removed for export] *)
      destruct RM as (junk2 & -> & G2 & HEB2 & LENM & MOK). cbv iota. apply (implM_ret usegs).
      hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB2.
      step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB2.
      eapply (ngc_err_exit K sites HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m);
        [ exact CTX | right; right; split; reflexivity | exact MI2 | exact ST2 | exact AG12 | exact G2 | exact HC1 | exact Hhc | exact FRS1 | exact ERR1 | exact MG1 | exact HEB2
        | exact LENM | exact MOK | rewrite OF2; exact OF1 ]. }
    (* [comment removed for export] *)
    destruct RM as (P & -> & G2 & CELLS0 & HEB2).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    cbn [cb_addr cb_size fst snd] in P1, P2, P3, P4, P5, P6. unfold PCAP_NG_SF_TOTAL in P4, P5, P6.
    assert (NPB2 : forall a, in_block CL a -> ~ (P <= a < P + 680)%Z).
    { intros a Ha Hin. destruct (GIo_CLc_facts K R ps2 [(q, P, PCAP_NG_SF_TOTAL)] CL FB m2 a G2
                 ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; exact Hin)) as [_ Hn]. exact (Hn Ha). }
    apply blank_recell_ng in CELLS0. unfold ngcells0, ngcells, ng_cells, ng0, pad0 in CELLS0. cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size] in CELLS0.
    destruct (rw_cells_cut _ _ _ 33 CELLS0) as [CELLS NG]. clear CELLS0.
    cbn [firstn skipn cells_size csize Nat.add app] in CELLS, NG.
    replace (P + Z.of_nat 648)%Z with (P + 648)%Z in NG by lia.
    cbv iota.
    set (BS0 := (if 2048 <? TL then TL else 2048)%Z).
    assert (BS0R : (1 <= BS0 <= 2^21 /\ TL <= BS0 /\ 2048 <= BS0)%Z) by (subst BS0; destruct (Z.ltb_spec 2048 TL); lia).
    unfold ngc_buf. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. fold BS0. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_free prims].
    hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB2.
    unfold implM. iprefix.
    step. rewrite (eqb_lits_false P 0) by lia. cbv iota.
    assert (PM8 : (P mod 8 = 0)%Z) by (clear - P2; Z.div_mod_to_equations; lia).
    assert (PM8' : ((P + 648) mod 8 = 0)%Z) by (clear - P2; Z.div_mod_to_equations; lia).
    step. rewrite (and7_aligned P) by lia. step. if_false.
    step. step.
    pose proof (munch_refl [(P, P + 680)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    step. step.
    step. if_false. step. if_false.
    step. rewrite (eqb_lits_false (P + 648) 0) by lia. cbv iota.
    step. rewrite (and7_aligned (P + 648)%Z) by lia. step. if_false.
    step. step. step. pstep.
    step. rewrite (sextw_low w9 TL hi9 W9) by lia.
    step. step. pstep.
    step. unfold bv_ltu. rewrite (unsigned_lit 2048), (unsigned_lit TL) by lia.
    (* [comment removed for export] *)
    assert (K740 : forall (m3 : mem),
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -128) -> munch [(P, P + 680)]%Z m2 m3 -> wmono usegs m2 m3 ->
      rw_cells usegs m3 P (ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0))
                             (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0))) ->
      rw_cells usegs m3 (P + 648) [C8 (Z_to_bv 64 1000000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0)] ->
      evt usegs (fun ms1 => impl usegs (at_node usegs) (npeek usegs)
           ((Monad.mbind (pmalloc HO BS0)
               (fun b => match b with
                         | Some buf => Monad.mbind (read_bytes MOps PR f (DHeap buf 12) (TL - 12) true)
                                        (fun x : rb_status * list Z => let '(st, data) := x in ngc_after_rb MOps PR fuel 0 sw (ngc_p0 q f 0 BT_SHB sw TL buf 1000000) st data)
                         | None => Monad.mbind (pfree HO q) (fun _ => Monad.mret (@CH_Err hptr hptr Msg.out_of_memory))
                         end)) ps2)
           (epost (fun p0 => POSTQ (fst p0) (snd p0))) ms1)
        (MS (mkR (Z_to_bv 64 0x16d00) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x x0 x1 (Z_to_bv 64 ERR) (Z_to_bv 64 EB)
                 (Z_to_bv 64 P) (Z_to_bv 64 BS0) (Z_to_bv 64 2048) (Z_to_bv 64 0) x5 x6 x7 x8
                 (Z_to_bv 64 FA) (Z_to_bv 64 (Z.b2z sw)) s4 w7 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 0) w9 s9 s10 s11 x9 x10 x11 x12)
            F (Z_to_bv 64 0x16d6c) fc None m3 (seg_rom usegs))).
    2: { destruct (Z.lt_ge_cases 2048 TL) as [LT|GE].
         - rewrite (proj2 (Z.ltb_lt _ _) LT). cbv iota. replace (Z_to_bv 64 TL) with (Z_to_bv 64 BS0) by (subst BS0; rewrite (proj2 (Z.ltb_lt _ _) LT); reflexivity).
           eapply K740; [assumption | assumption | exact MU | exact WM | exact CELLS | exact NG].
         - rewrite (proj2 (Z.ltb_ge _ _) GE). cbv iota. step. replace (Z_to_bv 64 2048) with (Z_to_bv 64 BS0) at 1 by (subst BS0; rewrite (proj2 (Z.ltb_ge _ _) GE); reflexivity).
           eapply K740; [assumption | assumption | exact MU | exact WM | exact CELLS | exact NG]. }
    clear MU WM CELLS NG. intros m3 MI3 ST3 MU WM CELLS NG.
    unfold ngcells in CELLS.
    step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3' end.
    assert (AGS23 : agrees_on (fun a => outside [(P, P + 680)]%Z a) m2 m3') by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    assert (G3 : GIo K R ps2 ((q, P, PCAP_NG_SF_TOTAL) :: CL) FB m3').
    { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. right.
      unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (AG13 : AGQ m3').
    { unfold ngc_AGQ in AG12 |- *. eapply agrees_on_trans; [exact AG12|]. eapply agrees_on_weaken; [exact AGS23|].
      intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB2 a Ha). lia. }
    unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB2.
    transport HC1 m3' AGS23 ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). transport FRS1 m3' AGS23 ltac:(prs).
    transport ERR1 m3' AGS23 ltac:(prs). transport MG1 m3' AGS23 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport HEB2 m3' AGS23 ltac:(prs).
    clear MU WM AGS23 MI2 ST2 G2. rename ST3 into ST3'.
    (* [comment removed for export] *)
    hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB2. hide CELLS. hide NG.
    apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind usegs).
    { eapply (MALLOCS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3' R ps2 ((q, P, PCAP_NG_SF_TOTAL) :: CL) FB lo BS0); [| reflexivity | lia].
      split; [exact G3|]. split; [rewrite Hsp; exact ST3'|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    intros bo ps3 ms3 PO. cbv beta in PO. destruct PO as (a0v & m4 & E & OF3 & MI4 & ST4 & AG4 & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x16d7c)) with (Z_to_bv 64 0x16d7c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INP3 : forall a, (P <= a < P + 680)%Z -> in_block ((q, P, PCAP_NG_SF_TOTAL) :: CL) a).
    { intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB2. unhide CELLS. unhide NG.
    transport HC1 m4 AG4 ltac:(intros a Ha; rewrite Hhc in Ha; left; lia). transport FRS1 m4 AG4 ltac:(prs). transport ERR1 m4 AG4 ltac:(prs).
    transport MG1 m4 AG4 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; left; lia). transport HEB2 m4 AG4 ltac:(prs).
    transport CELLS m4 AG4 ltac:(prs). transport NG m4 AG4 ltac:(prs).
    assert (AG14 : AGQ m4).
    { unfold ngc_AGQ in AG13 |- *. eapply agrees_on_trans; [exact AG13|]. eapply agrees_on_weaken; [exact AG4|].
      intros a [[Ha|Ha] _]; [left; lia| right]. unfold in_block in Ha |- *. apply Exists_cons_tl. exact Ha. }
    clear AG4 AG13 ST3' G3.
    hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB2. hide NG.
    unfold implM. iprefix. step.
    pose proof (munch_refl [(P, P + 680)]%Z m4) as MU4. pose proof (wmono_refl usegs m4) as WM4.
    destruct bo as [qb|].
    2: { (* [comment removed for export] *)
      destruct RM as (-> & G4 & _). cbv iota.
      pstep. step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
      step. step. step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
      assert (AGS45 : agrees_on (fun a => outside [(P, P + 680)]%Z a) m4 m5) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
      assert (G5 : GIo K R ps3 ((q, P, PCAP_NG_SF_TOTAL) :: CL) FB m5).
      { eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MU4 | exact WM4 |]. apply Forall_cons; [| apply Forall_nil]. right.
        unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
      assert (AG15 : AGQ m5).
      { unfold ngc_AGQ in AG14 |- *. eapply agrees_on_trans; [exact AG14|]. eapply agrees_on_weaken; [exact AGS45|].
        intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB2 a Ha). lia. }
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB2.
      transport HC1 m5 AGS45 ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). transport FRS1 m5 AGS45 ltac:(prs).
      transport ERR1 m5 AGS45 ltac:(prs). transport MG1 m5 AGS45 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport HEB2 m5 AGS45 ltac:(prs).
      clear MU4 WM4 CELLS NG AG14 G4.
      (* [comment removed for export] *)
      assert (LE : length e = 256%nat) by (destruct HEB2 as [[WF _] _]; cbn in WF; (keep_hyps CEILV sp R MG EB ERR TL hi7 hi9 e P WF; tauto)).
      pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [14%nat; 242%nat] HEB2 ltac:(cbn; lia)) as HE'. clear HEB2. cbn [mk_CB_cells app] in HE'.
      destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
      hide HC1. hide FRS1. hide ERR1. hide MG1. hide HE2.
      assert (LENM : length (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) = 14%nat) by (vm_compute; reflexivity).
      eapply evt_cut.
      { eapply (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB 0x10df2%Z 14%Z (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) (firstn 14 e));
          [ reflexivity | reflexivity | reflexivity
          | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m5 0x10df2 (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite LENM; cbn; lia)))
          | rewrite LENM; reflexivity | lia | exact HE1 | lia | lia | lia | assumption ]. }
      cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m6 & -> & MU6 & WM6 & MI6 & HE1' & _). clear HE1.
      replace (ret_pc (Z_to_bv 64 0x16fc8)) with (Z_to_bv 64 0x16fc8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      assert (AGS56 : agrees_on (fun a => outside [(EB, EB + 14)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      assert (ST6 : stk usegs m6 lo (bv_unsigned sp + -128)).
      { eapply stk_transport_disjoint; [eassumption | exact MU6 | exact WM6 | cbn [disjoint_from]; unfold rc_lo in *; lia]. }
      assert (G6 : GIo K R ps3 ((q, P, PCAP_NG_SF_TOTAL) :: CL) FB m6).
      { eapply (GIo_client_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (AG16 : AGQ m6).
      { unfold ngc_AGQ in AG15 |- *. eapply agrees_on_trans; [exact AG15|]. eapply agrees_on_weaken; [exact AGS56|]. intros a [_ [Hn _]]; cbn [outside]. lia. }
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HE2.
      transport HC1 m6 AGS56 ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). transport FRS1 m6 AGS56 ltac:(prs).
      transport ERR1 m6 AGS56 ltac:(prs). transport MG1 m6 AGS56 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport HE2 m6 AGS56 ltac:(prs).
      assert (HEB6 : rw_cells usegs m6 EB [CB (length Msg.out_of_memory + 1) (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]); CB (255 - length Msg.out_of_memory) (skipn 14 e)]).
      { join_cells HE1' HE2.
        eapply rw_cells_recell; [exact HE1' | pose proof (proj1 (proj1 HE1')) as WF; cbn in WF |- *; rewrite ?length_app, ?length_map, ?length_skipn in *;
                                               assert (LOM : length Msg.out_of_memory = 13%nat) by (vm_compute; reflexivity); rewrite ?LOM, ?LE in *; cbn; repeat split; try lia; tauto |].
        cbn [cells_bytes cbytes app]. rewrite ?firstn_all2 by (rewrite length_skipn, LE; lia). rewrite !app_nil_r, <- app_assoc. reflexivity. }
      hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB6.
      step. step.
      (* [comment removed for export] *)
      apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind usegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 R ps3 [] CL FB q P PCAP_NG_SF_TOTAL lo); [| reflexivity].
        split; [exact G6|]. split; [rewrite Hsp; exact ST6|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI6|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [] ps7 ms7 PO. cbv beta in PO. destruct PO as (av7 & m7 & E & OF7 & MI7 & ST7 & AG7 & G7).
      unfold hpost_regs in E. destruct_exs E. subst ms7. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x16fd0)) with (Z_to_bv 64 0x16fd0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in G7, AG7.
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB6.
      transport HC1 m7 AG7 ltac:(intros a Ha; left; lia). transport FRS1 m7 AG7 ltac:(intros a Ha; left; lia). transport ERR1 m7 AG7 ltac:(intros a Ha; left; lia).
      transport MG1 m7 AG7 ltac:(intros a Ha; left; lia). transport HEB6 m7 AG7 ltac:(intros a Ha; left; lia).
      assert (AG17 : AGQ m7).
      { unfold ngc_AGQ in AG16 |- *. eapply agrees_on_trans; [exact AG16|]. eapply agrees_on_weaken; [exact AG7|]. intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]. }
      apply (implM_ret usegs).
      hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB6. step. unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB6.
      eapply (ngc_err_exit K sites HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m);
        [ exact CTX | right; left; reflexivity | exact MI7 | exact ST7 | exact AG17 | exact G7 | exact HC1 | exact Hhc | exact FRS1 | exact ERR1 | exact MG1 | exact HEB6
        | replace (length Msg.out_of_memory) with 13%nat by (vm_compute; reflexivity); lia | msg_ok | rewrite OF7, OF3, OF2; exact OF1 ]. }
    (* [comment removed for export] *)
    destruct RM as (B & bjunk & -> & G4 & HBUF). cbv iota.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G4 ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & B5 & B6). cbn [cb_addr cb_size fst snd] in B1, B2, B3, B4, B5, B6.
    pose proof (blocks2_apart K _ _ _ _ _ _ _ _ _ _ _ G4 ltac:(lia) ltac:(unfold PCAP_NG_SF_TOTAL; lia)) as APB. unfold PCAP_NG_SF_TOTAL in APB.
    assert (NPB4 : forall a, in_block CL a -> ~ (P <= a < P + 680)%Z /\ ~ (B <= a < B + BS0)%Z).
    { intros a Ha. pose proof (GIo_perm K HPL _ _ _ _ _ _ G4 (Permutation_app_comm [(qb, B, BS0); (q, P, PCAP_NG_SF_TOTAL)] CL)) as G4'.
      destruct (GIo_CLc_facts K R ps3 CL _ FB m4 a G4' Ha) as [_ Hn]. split; intros Hin; apply Hn; unfold in_block.
      - apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia.
      - apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    clear MU4 WM4. pose proof (munch_refl [(P, P + 680); (B, B + 12)]%Z m4) as MU4. pose proof (wmono_refl usegs m4) as WM4.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [4%nat; 4%nat; 4%nat; Z.to_nat (TL - 12); Z.to_nat (BS0 - TL)] HBUF ltac:(cbn; lia)) as HB'. clear HBUF. cbn [mk_CB_cells app] in HB'.
    destruct (rw_cells_cut _ _ _ 3 HB') as [HBH X]. destruct (rw_cells_cut _ _ _ 1 X) as [HBD HBR]. clear HB' X.
    cbn [firstn skipn cells_size csize Nat.add app] in HBH, HBD, HBR.
    lazymatch type of HBD with rw_cells _ _ ?A _ => replace A with (B + 12)%Z in HBD by lia end.
    lazymatch type of HBR with rw_cells _ _ ?A [CB ?n ?j] => replace A with (B + TL)%Z in HBR by lia; replace n with (Z.to_nat (BS0 - TL)) in HBR by lia end.
    hide HBD. hide HBR. unhide NG.
    assert (BM4 : (B mod 4 = 0)%Z) by (clear - B2; Z.div_mod_to_equations; lia).
    assert (AND4 : Z.land (bv_unsigned (Z_to_bv 64 (B + 8))) 4 = 0%Z).
    { change 4%Z with (Z.land 7 4) at 1. rewrite Z.land_assoc. rewrite (and7_aligned (B + 8)%Z) by (fastfirst (first [ noevar_assumption |lia | clear - B2 B1 B4; Z.div_mod_to_equations; lia])). reflexivity. }
    step. step. rewrite (eqb_lits_false B 0) by lia. cbv iota.
    step. rewrite (and7_aligned (P + 648)%Z) by lia. step. if_false.
    step. step. step. pstep.
    step. if_cases Kc; [zify_cond Kc; exfalso; lia|]. clear Kc.
    step. rewrite (and3_aligned B) by lia. step. if_false.
    step. step. rewrite AND4. step.
    pstep. step. step. if_false.
    step. step.
    step. if_cases Kc; [zify_cond Kc; exfalso; lia|]. clear Kc.
    step. step. rewrite (sextw_low w9 TL hi9 W9) by lia. step.
    step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
    assert (AGS45 : agrees_on (fun a => outside [(P, P + 680); (B, B + 12)]%Z a) m4 m5) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (G5 : GIo K R ps3 ((qb, B, BS0) :: (q, P, PCAP_NG_SF_TOTAL) :: CL) FB m5).
    { eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MU4 | exact WM4 |]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; unfold iv_in_block.
      - apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia.
      - apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (AG15 : AGQ m5).
    { unfold ngc_AGQ in AG14 |- *. eapply agrees_on_trans; [exact AG14|]. eapply agrees_on_weaken; [exact AGS45|].
      intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB4 a Ha). (keep_hyps CEILV sp R lo EB ERR magic TL hc P B a BS0R H0; lia). }
    unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB2. unhide HBD. unhide HBR.
    transport HC1 m5 AGS45 ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). transport FRS1 m5 AGS45 ltac:(prs).
    transport ERR1 m5 AGS45 ltac:(prs). transport MG1 m5 AGS45 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport HEB2 m5 AGS45 ltac:(prs).
    transport HBD m5 AGS45 ltac:((keep_hyps CEILV sp R lo EB ERR magic TL hc P B bjunk BS0R APB; prs)). transport HBR m5 AGS45 ltac:((keep_hyps CEILV sp R lo EB ERR magic TL hc P B bjunk TLR APB; prs)).
    clear MU4 WM4 AGS45 G4 AG14.
    (* [comment removed for export] *)
    hide HC1. hide FRS1. hide ERR1. hide MG1. hide CELLS. hide NG. hide HBH. hide HBR.
    apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind usegs).
    { eapply (RBYTES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 R ps3 ((qb, B, BS0) :: (q, P, PCAP_NG_SF_TOTAL) :: CL) FB f FA (B + 12)%Z (TL - 12)%Z EB lo true (DHeap qb 12));
        [ split; [exact G5|]; split; [rewrite Hsp; eassumption|]; split; [unfold rc_lo; lia|]; split; [unfold READ_BYTES_STACK, PCAP_L1_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | exact HinF
        | unfold eval_rdest, blk_addr; cbn [fo_site fo_nop]; rewrite (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G5 ltac:(apply in_or_app; left; left; reflexivity)); reflexivity
        | reflexivity | reflexivity | f_equal; lia | reflexivity | reflexivity | lia
        | exact HBD | left; intros a Ha; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia
        | exact HEB2 | left; rewrite Hsp; lia | lia | exact E8 ]. }
    intros [st got] ps5 ms5 PO. cbv beta in PO.
    destruct PO as (a0v & m6 & junk' & E & OF5 & MI6 & ST6 & AG5 & G6 & HD6 & GR6 & GL6 & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x16df4)) with (Z_to_bv 64 0x16df4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide CELLS. unhide NG. unhide HBH. unhide HBR.
    assert (INPB : forall a, (P <= a < P + 680 \/ B <= a < B + BS0)%Z -> in_block ((qb, B, BS0) :: (q, P, PCAP_NG_SF_TOTAL) :: CL) a).
    { intros a [Ha|Ha]; unfold in_block; [apply Exists_cons_tl, Exists_cons_hd| apply Exists_cons_hd]; cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia. }
    transport HC1 m6 AG5 ltac:(intros a Ha; rewrite Hhc in Ha; split; [left; lia| lia]). transport FRS1 m6 AG5 ltac:(prs). transport ERR1 m6 AG5 ltac:((keep_hyps CEILV H hptr K sp R CL FB lo MG EB ERR magic TL hc ew q P qb B ps5 m6 LO BU R1 R2 D1 BS0R B4 G6; prs)).
    transport MG1 m6 AG5 ltac:(prsMG GL).
    transport CELLS m6 AG5 ltac:((keep_hyps CEILV H hptr K sp R CL FB lo EB ERR magic sw TL hc q P qb B ps5 m6 LO BU E1 P4 BS0R APB G6 INPB; prs)). transport NG m6 AG5 ltac:((keep_hyps CEILV H hptr K sp R CL FB lo EB ERR magic TL hc q P qb B ps5 m6 LO BU E1 P4 BS0R APB G6 INPB; prs)). transport HBH m6 AG5 ltac:(prs). transport HBR m6 AG5 ltac:((keep_hyps CEILV H hptr K sp R CL FB lo EB ERR magic TL hc q P qb B bjunk ps5 m6 TLR LO BU E1 B4 G6 INPB; prs)).
    assert (AG16 : AGQ m6).
    { unfold ngc_AGQ in AG15 |- *. eapply agrees_on_trans; [exact AG15|]. eapply agrees_on_weaken; [exact AG5|].
      intros a [[Ha|Ha] [Hn _]]; [split; [left; lia| lia]|]. pose proof (CLB a Ha). pose proof (NPB4 a Ha). split; [right; unfold in_block in Ha |- *; do 2 apply Exists_cons_tl; exact Ha| (keep_hyps CEILV sp R lo EB ERR magic TL hc P B a BS0R Hn H1; lia)]. }
    clear AG5 AG15 G5.
    hide HC1. hide FRS1. hide ERR1. hide MG1. hide CELLS. hide NG. hide HBH. hide HBR. hide HD6.
    unfold implM. iprefix. step. step.
    destruct st as [ | | msg].
    2: { (* [comment removed for export] *) destruct RM as (_ & _ & X & _). discriminate X. }
    2: { (* [comment removed for export] *)
      destruct RM as (junk6 & -> & HEB6 & LENM & MOK).
      change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 (-1))) with true. cbv iota.
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide CELLS. unhide NG.
      apply evt_done. unfold ngc_after_rb. unfold ngc_fail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims free_opt ng_ifaces_ptr_of pc_buffer pc_self pc_priv ngc_p0 set_bufdata].
      destruct (rw_cells_cut _ _ _ 4 CELLS) as [_ X1]. destruct (rw_cells_cut _ _ _ 1 X1) as [HPB _]. cbn [firstn skipn cells_size csize Nat.add app] in HPB.
      replace (P + Z.of_nat 24)%Z with (P + 24)%Z in HPB by lia.
      destruct (rw_cells_cut _ _ _ 5 NG) as [_ HPI]. cbn [firstn skipn cells_size csize Nat.add app] in HPI.
      replace (P + 648 + Z.of_nat 24)%Z with (P + 672)%Z in HPI by lia.
      eapply (ngc_fail3 HO K sites HFL SFL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m) with (i := None) (ni := 0%Z);
        [ exact CTX | exact MI6 | exact ST6 | exact AG16 | cbn [app]; eapply (GIo_perm K HPL); [exact G6| apply Permutation.perm_swap]
        | reflexivity | exact HC1 | exact Hhc | exact FRS1 | exact ERR1 | exact MG1 | exact HEB6
        | exact LENM | exact MOK | rewrite OF5, OF3, OF2; exact OF1 | exact HPB | exact HPI | lia | lia | lia ]. }
    (* [comment removed for export] *)
    destruct RM as (-> & GLn & HEB6).
    change (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 (-1))) with false. cbv iota.
    unfold zlength in GLn, GL6.
    (* [comment removed for export] *)
    destruct got as [|g0 [|g1 [|g2 [|g3 rest]]]]; try (exfalso; cbn [length] in GLn; (keep_hyps CEILV sp R lo EB ERR magic TL hc P B TLR GLn g0 g1 g2; lia)).
    pose proof (Forall_inv GR6) as X0. pose proof (Forall_inv (Forall_inv_tail GR6)) as X1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GR6))) as X2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GR6)))) as X3.
    cbv beta in X0, X1, X2, X3.
    assert (Lrest : Z.of_nat (length rest) = (TL - 16)%Z) by (cbn [length] in GLn; lia).
    unhide HD6. destruct (rw_cells_cut _ _ _ 1 HD6) as [HDg _]. clear HD6. cbn [firstn skipn cells_size csize Nat.add app map] in HDg.
    pose proof (rw_cells_recell _ _ _ [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3)); CB (length rest) (map b8 rest)] HDg
                  ltac:(cbn; rewrite ?length_map; repeat split; fastfirst (first [reflexivity | lia | exact Logic.I]))
                  ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by lia; rewrite !app_nil_r; reflexivity)) as HDV. clear HDg.
    (* [comment removed for export] *)
    set (HDR := le_bytes 4 BT_SHB ++ le_bytes 4 TL ++ le_bytes 4 BYTE_ORDER_MAGIC).
    assert (LHDR : length HDR = 12%nat) by (subst HDR; rewrite !length_app, !length_le_bytes; reflexivity).
    assert (GHDR : Forall (fun z => 0 <= z < 256)%Z HDR).
    { subst HDR. apply (proj2 (Forall_app _ _ _)). split; [apply le_bytes_4_range|]. apply (proj2 (Forall_app _ _ _)). split; apply le_bytes_4_range. }
    assert (BHDR : map b8 HDR = le4 (Z_to_bv 64 168627466) ++ le4 w9 ++ le4 w7).
    { subst HDR. rewrite !map_app. rewrite (le4_low w9 TL hi9 W9), (le4_low w7 BYTE_ORDER_MAGIC hi7 W7) by (unfold BYTE_ORDER_MAGIC; lia).
      rewrite (le4_le_bytes 168627466) by lia. reflexivity. }
    unfold ngc_after_rb. cbn [pc_bufdata ngc_p0 set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_snapshot pc_linktype pc_linktype_ext pc_priv].
    fold BS0. fold HDR.
    (* [comment removed for export] *)
    assert (KVER : forall (a1x a2x a3x : word) (m7 : mem) (v0 v1 v2 v3 : Z) (jr : list byte),
      (0 <= v0 < 256)%Z -> (0 <= v1 < 256)%Z -> (0 <= v2 < 256)%Z -> (0 <= v3 < 256)%Z ->
      mem_inv usegs m7 -> stk usegs m7 lo (bv_unsigned sp + -128) -> AGQ m7 -> GIo K R ps5 ((qb, B, BS0) :: (q, P, PCAP_NG_SF_TOTAL) :: CL) FB m7 ->
      rw_cells usegs m7 (bv_unsigned sp + -128) hc -> FRS m7 -> rw_cells usegs m7 ERR [C4 ew] -> rw_cells usegs m7 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) ->
      rw_cells usegs m7 EB [CB 256 e] ->
      rw_cells usegs m7 P (ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0))
                             (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0))) ->
      rw_cells usegs m7 (P + 648) [C8 (Z_to_bv 64 1000000); C4 (Z_to_bv 64 16777216); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0)] ->
      rw_cells usegs m7 B [C4 (Z_to_bv 64 168627466); C4 w9; C4 w7] ->
      rw_cells usegs m7 (B + 12) [C2 (Z_to_bv 64 (v0 + 256 * v1)); C2 (Z_to_bv 64 (v2 + 256 * v3)); CB (length rest) (map b8 rest)] ->
      rw_cells usegs m7 (B + TL) [CB (Z.to_nat (BS0 - TL)) jr] ->
      Forall (fun z => 0 <= z < 256)%Z rest ->
      evt usegs (fun ms1 => impl usegs (at_node usegs) (npeek usegs)
           ((if negb ((v0 + 256 * v1 =? 1) && ((v2 + 256 * v3 =? 0) || (v2 + 256 * v3 =? 2)))%Z
             then ngc_fail MOps PR (Msg.unsupported_pcapng_version (v0 + 256 * v1) (v2 + 256 * v3))
                    (mkPcap q f BS0 BS0 qb (HDR ++ v0 :: v1 :: v2 :: v3 :: rest) sw 0 0 0 0 0 0 0 [] hdr0 (PrivNg (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []) None))
             else ngc_find MOps PR fuel 0
                    (mkPcap q f BS0 BS0 qb (HDR ++ v0 :: v1 :: v2 :: v3 :: rest) sw (v0 + 256 * v1) (v2 + 256 * v3) 0 0 0 0 0 [] hdr0 (PrivNg (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []) None))) ps5)
           (epost (fun p0 => POSTQ (fst p0) (snd p0))) ms1)
        (MS (mkR (Z_to_bv 64 0x16df4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x27 x28 x29 (Z_to_bv 64 ERR) (Z_to_bv 64 EB)
                 (Z_to_bv 64 P) a1x a2x a3x x33 x34 x35 x36
                 (Z_to_bv 64 FA) (Z_to_bv 64 P) (Z_to_bv 64 B) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 0) (Z_to_bv 64 1) s9 s10 s11 x37 x38 x39 x40)
            F (Z_to_bv 64 0x16e30) fc None m7 (seg_rom usegs))).
    { intros until jr. intros V0 V1 V2 V3 MI7 ST7 AG7 G7 HC7 FRS7 ERR7 MG7 HEB7 CELLS7 NG7 HBH7 HDV7 HBR7 GRr.
      clear HEB6 GLn GL6 GR6.
      hide HC7. hide FRS7. hide ERR7. hide MG7. hide HEB7. hide CELLS7. hide NG7. hide HBH7. hide HBR7.
      step. rewrite (zx16_lit (v0 + 256 * v1)) by lia. step. step.
      set (MAJ := (v0 + 256 * v1)%Z) in *. set (MIN := (v2 + 256 * v3)%Z) in *.
      assert (MAJR : (0 <= MAJ < 65536)%Z) by lia. assert (MINR : (0 <= MIN < 65536)%Z) by lia.
      (* [comment removed for export] *)
      assert (VERR : forall (a1y a2y s5y : word) (m8 : mem),
        mem_inv usegs m8 -> stk usegs m8 lo (bv_unsigned sp + -128) -> m8 = m7 ->
        evt usegs (fun ms1 => impl usegs (at_node usegs) (npeek usegs)
             (ngc_fail MOps PR (Msg.unsupported_pcapng_version MAJ MIN)
                      (mkPcap q f BS0 BS0 qb (HDR ++ v0 :: v1 :: v2 :: v3 :: rest) sw 0 0 0 0 0 0 0 [] hdr0 (PrivNg (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []) None)) ps5)
             (epost (fun p0 => POSTQ (fst p0) (snd p0))) ms1)
          (MS (mkR (Z_to_bv 64 0x16df4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x27 x28 x29 (Z_to_bv 64 ERR) (Z_to_bv 64 EB)
                   (Z_to_bv 64 P) a1y a2y (Z_to_bv 64 MAJ) x33 x34 x35 x36
                   (Z_to_bv 64 FA) (Z_to_bv 64 P) (Z_to_bv 64 B) s5y (Z_to_bv 64 (P + 648)) (Z_to_bv 64 0) (Z_to_bv 64 1) s9 s10 s11 x37 x38 x39 x40)
              F (Z_to_bv 64 0x16fd4) fc None m8 (seg_rom usegs))).
      { intros a1y a2y s5y m8 MI8 ST8 ->.
        step. rewrite (zx16_lit MIN) by lia.
        do 5 step.
        unhide HC7. unhide FRS7. unhide ERR7. unhide MG7. unhide HEB7. unhide CELLS7. unhide NG7.
        assert (MSG : fmt_at m7 0x105d0 "unsupported pcapng savefile version %u.%u"%string)
          by (apply (fmt_at_intro m7 _ _ MI8); [vm_compute; reflexivity| lia| cbn; lia]).
        destruct (rw_cells_cut _ _ _ 4 CELLS7) as [_ Y1]. destruct (rw_cells_cut _ _ _ 1 Y1) as [HPB _]. cbn [firstn skipn cells_size csize Nat.add app] in HPB.
        replace (P + Z.of_nat 24)%Z with (P + 24)%Z in HPB by lia.
        destruct (rw_cells_cut _ _ _ 5 NG7) as [_ HPI]. cbn [firstn skipn cells_size csize Nat.add app] in HPI.
        replace (P + 648 + Z.of_nat 24)%Z with (P + 672)%Z in HPI by lia.
        apply evt_done.
        eapply (ngc_snp_fail HO K sites HFL SFL HPL FREE SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX q P sw BS0 0 ew
                   (conj P1 P4)
                   _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 MAJ) (Z_to_bv 64 MIN) _ _ _ _ _ 0x16fec m7 ps5
                   "unsupported pcapng savefile version %u.%u"%string [AInt MAJ; AInt MIN] 0x105d0 (Msg.unsupported_pcapng_version MAJ MIN) (HDR ++ v0 :: v1 :: v2 :: v3 :: rest)
                   qb None (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []) B 0 BS0 e hc);
          [ reflexivity | exact MI8 | exact ST8 | exact AG7 | cbn [IBLK app]; eapply (GIo_perm K HPL); [exact G7| apply Permutation.perm_swap] | rewrite OF5, OF3, OF2; exact OF1
          | reflexivity | exact HC7 | exact Hhc | exact FRS7 | exact ERR7 | exact MG7 | exact HEB7 | exact HPB | exact HPI | lia | lia
          | exact MSG | reflexivity | cbn; lia | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
          | vm_compute; reflexivity | apply args_ok_ints2 | unfold Msg.unsupported_pcapng_version, PCAP_ERRBUF_SIZE; reflexivity ]. }
      destruct (Z.eq_dec MAJ 1) as [M1|M1].
      2: { rewrite (eqb_lits_false MAJ 1) by lia. rewrite (proj2 (Z.eqb_neq _ _) M1). cbn [negb andb]. cbv iota. eapply VERR; [exact MI7 | exact ST7 | reflexivity]. }
      rewrite (eqb_lits_eq MAJ 1 M1). cbn [negb]. cbv iota.
      step. rewrite (zx16_lit MIN) by lia. hide HDV7. step. step. step.
      unfold bv_eqb at 1. rewrite (unsigned_lit MIN), (unsigned_lit 2) by lia. rewrite (unsigned_lit (Z.lor MIN 2)) by (pose proof (lor2_range MIN MINR); lia).
      rewrite (lor2_eqb2 MIN) by lia. rewrite (proj2 (Z.eqb_eq _ _) M1). cbn [andb].
      destruct ((MIN =? 0) || (MIN =? 2)) eqn:MOK; cbn [negb]; cbv iota.
      2: { eapply VERR; [exact MI7 | exact ST7 | reflexivity]. }
      (* [comment removed for export] *)
      unhide CELLS7. unhide NG7. unfold ngcells in CELLS7.
      pose proof (munch_refl [(P, P + 680)]%Z m7) as MU7. pose proof (wmono_refl usegs m7) as WM7.
      step. pstep. step. pstep. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m9 end.
      assert (AGS79 : agrees_on (fun a => outside [(P, P + 680)]%Z a) m7 m9) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
      assert (G9 : GIo K R ps5 ((q, P, 680%Z) :: (qb, B, BS0) :: CL) FB m9).
      { eapply (GIo_perm K HPL); [| apply Permutation.perm_swap]. unfold PCAP_NG_SF_TOTAL in G7.
        eapply (GIo_client_frame K HFL SFL); [exact G7 | exact MU7 | exact WM7 |]. apply Forall_cons; [| apply Forall_nil]. right.
        unfold iv_in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (AG9 : AGQ m9).
      { unfold ngc_AGQ in AG7 |- *. eapply agrees_on_trans; [exact AG7|]. eapply agrees_on_weaken; [exact AGS79|].
        intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB4 a Ha). lia. }
      unhide HC7. unhide FRS7. unhide ERR7. unhide MG7. unhide HEB7. unhide HBH7. unhide HBR7. unhide HDV7.
      transport HC7 m9 AGS79 ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). unfold ngc_FRS in FRS7. transport FRS7 m9 AGS79 ltac:(prs).
      transport ERR7 m9 AGS79 ltac:(prs). transport MG7 m9 AGS79 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport HEB7 m9 AGS79 ltac:(prs).
      transport HBH7 m9 AGS79 ltac:((keep_hyps CEILV sp R lo EB ERR magic w7 w9 TL hc P B rest v0 v1 v2 v3 BS0R APB; prs)). transport HBR7 m9 AGS79 ltac:((keep_hyps CEILV sp R lo EB ERR magic TL hc P B rest v0 v1 v2 v3 jr TLR APB; prs)). transport HDV7 m9 AGS79 ltac:((keep_hyps CEILV sp R lo EB ERR magic TL hc P B rest v0 v1 v2 v3 BS0R APB Lrest; prs)).
      (* [comment removed for export] *)
      assert (Ljr : length jr = Z.to_nat (BS0 - TL)) by (pose proof (proj1 (proj1 HBR7)) as WF; cbn in WF; lia).
      assert (BUF9 : rw_cells usegs m9 B [CB (Z.to_nat BS0) (map b8 (HDR ++ v0 :: v1 :: v2 :: v3 :: rest) ++ jr)]).
      { replace (B + 12)%Z with (B + Z.of_nat (cells_size [C4 (Z_to_bv 64 168627466); C4 w9; C4 w7]))%Z in HDV7 by (cbn; lia).
        pose proof (rw_cells_uncut _ _ _ _ _ HBH7 HDV7 ltac:(cbn; lia)) as J1.
        replace (B + TL)%Z with (B + Z.of_nat (cells_size ([C4 (Z_to_bv 64 168627466); C4 w9; C4 w7] ++ [C2 (Z_to_bv 64 (v0 + 256 * v1)); C2 (Z_to_bv 64 (v2 + 256 * v3)); CB (length rest) (map b8 rest)])))%Z in HBR7
          by (rewrite cells_size_app; cbn [cells_size csize Nat.add]; lia).
        pose proof (rw_cells_uncut _ _ _ _ _ J1 HBR7 ltac:(reflexivity)) as J2. cbn [app] in J2.
        eapply rw_cells_recell; [exact J2 | cbn; rewrite ?length_app, ?length_map; cbn; rewrite ?length_app, ?LHDR; cbn; repeat split; try exact Logic.I; lia |].
        cbn [cells_bytes cbytes app]. cbv delta [MAJ MIN]. rewrite map_app, BHDR. cbn [map app]. rewrite !le2_lit by lia. rewrite !app_nil_r, <- !app_assoc. reflexivity. }
      clear HBH7 HDV7 HBR7.
      rewrite M1. apply evt_done.
      eapply (ngc_loop HO K sites HFL SFL HPL FREE SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX q P sw BS0 MIN ew
                (conj P1 P4) P2 ltac:(lia) ltac:(lia) RB AI fuel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1)) m9 ps5 qb B BS0 (HDR ++ v0 :: v1 :: v2 :: v3 :: rest)
                (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []) None 0 pad0 _ e hc); [vm_compute; reflexivity|].
      split; [exact MI7|]. split; [exact ST7|]. split; [exact AG9|]. split; [cbn [IBLK app]; exact G9|]. split; [rewrite OF5, OF3, OF2; exact OF1|].
      split; [exact HC7|]. split; [exact Hhc|]. split; [exact FRS7|]. split; [exact ERR7|]. split; [exact MG7|]. split; [exact HEB7|].
      split; [exact CELLS7|]. split; [unfold ng_cells, pad0, INITIAL_MAX_BLOCKSIZE; cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact NG7|].
      split; [reflexivity|]. split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
      split; [unfold ifaces_ok; cbn; repeat split; reflexivity|].
      split; [exact BUF9|].
      split; [cbn [pc_bufdata ngc_p]; apply firstn_len_app'; rewrite length_map; reflexivity|].
      split; [cbn [pc_bufdata ngc_p]; rewrite length_app, LHDR; cbn [length]; lia|]. split; [lia|]. split; [lia|].
      cbn [pc_bufdata ngc_p]. apply Forall_app. split; [exact GHDR|]. repeat (constructor; [cbv beta; lia|]). exact GRr. }
    unhide CELLS.
    step. step. rewrite (sx32_small (Z.b2z sw)) by (destruct sw; cbn; lia). step.
    destruct sw; cbn [Z.b2z].
    - (* [comment removed for export] *)
      rewrite (eqb_lits_false 1 0) by lia. cbv iota.
      pose proof (munch_refl [(B + 12, B + 16)]%Z m6) as MUv. pose proof (wmono_refl usegs m6) as WMv.
      hide CELLS. hide HEB6.
      do 10 step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m7 end.
      rewrite (swap16_word g0 g1), (swap16_word g2 g3) in HDV |- * by lia.
      pose proof (rw_cells_recell _ _ _ [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2)); CB (length rest) (map b8 rest)] HDV
                    ltac:(cbn; rewrite ?length_map; repeat split; fastfirst (first [reflexivity | lia | exact Logic.I]))
                    ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by (keep_hyps CEILV sp R EB ERR magic TL hc P B g0 g1 g2 g3 rest X1 X0 X3 X2; lia);
                          rewrite (le2_of_val (Z_to_bv 64 (g1 + 256 * g0 + 65536 * g1)) g1 g0 g1) by (fastfirst (first [(keep_hyps CEILV sp R EB ERR magic TL hc P B g0 g1 g2 g3 rest X1 X0; lia) | rewrite unsigned_lit by (keep_hyps CEILV sp R lo EB ERR magic TL hc P B g0 g1 g2 g3 rest X0 X1; lia); (keep_hyps CEILV sp R EB ERR magic TL hc P B g0 g1 g2 g3 rest; lia)]));
                          rewrite (le2_of_val (Z_to_bv 64 (g3 + 256 * g2 + 65536 * g3)) g3 g2 g3) by (fastfirst (first [(keep_hyps CEILV sp R EB ERR magic TL hc P B g0 g1 g2 g3 rest X3 X2; lia) | rewrite unsigned_lit by (keep_hyps CEILV sp R lo EB ERR magic TL hc P B g0 g1 g2 g3 rest X2 X3; lia); (keep_hyps CEILV sp R EB ERR magic TL hc P B g0 g1 g2 g3 rest; lia)])); reflexivity)) as HDV'. clear HDV.
      assert (AGSv : agrees_on (fun a => outside [(B + 12, B + 16)]%Z a) m6 m7) by (eapply agrees_on_of_munch; [exact MUv | exact WMv | intros a _ Ho; exact Ho]).
      assert (G7 : GIo K R ps5 ((qb, B, BS0) :: (q, P, PCAP_NG_SF_TOTAL) :: CL) FB m7).
      { eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MUv | exact WMv |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (AG17 : AGQ m7).
      { unfold ngc_AGQ in AG16 |- *. eapply agrees_on_trans; [exact AG16|]. eapply agrees_on_weaken; [exact AGSv|].
        intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB4 a Ha). (keep_hyps CEILV sp R lo EB ERR magic TL hc P B g0 g1 g2 g3 rest a BS0R H0; lia). }
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide CELLS. unhide NG. unhide HBH. unhide HBR. unhide HEB6.
      transport HC1 m7 AGSv ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). transport FRS1 m7 AGSv ltac:(prs). transport ERR1 m7 AGSv ltac:(prs).
      transport MG1 m7 AGSv ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport CELLS m7 AGSv ltac:((keep_hyps CEILV sp R lo EB ERR magic TL hc P B g0 g1 g2 g3 rest BS0R APB; prs)). transport NG m7 AGSv ltac:((keep_hyps CEILV sp R lo EB ERR magic TL hc P B g0 g1 g2 g3 rest BS0R APB; prs)).
      transport HBH m7 AGSv ltac:(prs). transport HBR m7 AGSv ltac:(prs). transport HEB6 m7 AGSv ltac:(prs).
      (* [comment removed for export] *)
      assert (SW12 : swap_field 2 14 (swap_field 2 12 (HDR ++ g0 :: g1 :: g2 :: g3 :: rest)) = HDR ++ g1 :: g0 :: g3 :: g2 :: rest).
      { replace 12%Z with (Z.of_nat (length HDR)) by lia. rewrite swap2_at. replace 14%Z with (Z.of_nat (length HDR) + 2)%Z by lia. rewrite swap2_at2. reflexivity. }
      rewrite !SW12. cbn [pc_bufdata set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_snapshot pc_linktype pc_linktype_ext pc_priv].
      replace (get_le16 (HDR ++ g1 :: g0 :: g3 :: g2 :: rest) 12) with (g1 + 256 * g0)%Z by (replace 12%Z with (Z.of_nat (length HDR)) by lia; symmetry; apply get_le16_at).
      replace (get_le16 (HDR ++ g1 :: g0 :: g3 :: g2 :: rest) 14) with (g3 + 256 * g2)%Z by (replace 14%Z with (Z.of_nat (length HDR) + 2)%Z by lia; symmetry; apply get_le16_at2).
      eapply (KVER _ _ _ m7 g1 g0 g3 g2);
        [ lia | lia | lia | lia | assumption | assumption | exact AG17 | exact G7 | exact HC1 | exact FRS1 | exact ERR1 | exact MG1 | exact HEB6 | exact CELLS | exact NG
        | exact HBH | exact HDV' | exact HBR | do 4 apply Forall_inv_tail in GR6; exact GR6 ].
    - (* [comment removed for export] *)
      rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide NG. unhide HBH. unhide HBR.
      cbn [pc_bufdata set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_snapshot pc_linktype pc_linktype_ext pc_priv].
      replace (get_le16 (HDR ++ g0 :: g1 :: g2 :: g3 :: rest) 12) with (g0 + 256 * g1)%Z by (replace 12%Z with (Z.of_nat (length HDR)) by lia; symmetry; apply get_le16_at).
      replace (get_le16 (HDR ++ g0 :: g1 :: g2 :: g3 :: rest) 14) with (g2 + 256 * g3)%Z by (replace 14%Z with (Z.of_nat (length HDR) + 2)%Z by lia; symmetry; apply get_le16_at2).
      eapply (KVER _ _ _ m6 g0 g1 g2 g3);
        [ lia | lia | lia | lia | assumption | assumption | exact AG16 | exact G6 | exact HC1 | exact FRS1 | exact ERR1 | exact MG1 | exact HEB6 | exact CELLS | exact NG
        | exact HBH | exact HDV | exact HBR | do 4 apply Forall_inv_tail in GR6; exact GR6 ].
  Qed.
  End Sz8.
  Lemma ngc_fill : ltac:(let t := eval cbv delta [ngc_fill__stmt] in ngc_fill__stmt in exact t).
  Proof using AI CTX FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. intros fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w7 w9 sw TL hi7 hi9 m1 ps1 hc ew e. ltac2:(SecDiet.SzSec.closeP 'ngc_fill__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkNg.

End WithCeil.
End F_sfpcapng_chkE.
