(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module Stdio_glue_fo.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fmodeflags OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_strchr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
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

(* [comment removed for export] *)
Local Ltac at_node_solve__p0  :=
  at_node_red; split_spine;
  first [ reflexivity
        | idtac ].
Local Ltac at_node_solve__p1  :=
  at_node_red; split_spine;
  first [ reflexivity
        | lia ].
Local Ltac at_node_solve__p2  :=
  at_node_red; split_spine;
  first [ reflexivity
        | lia ].
Local Ltac at_node_solve__p3  :=
  at_node_red; split_spine;
  first [ reflexivity
        | idtac ].
Local Ltac at_node_solve__p4  :=
  at_node_red; split_spine;
  first [ reflexivity
        | lia ].
Local Ltac at_node_solve__p5  :=
  at_node_red; split_spine;
  first [ reflexivity
        | lia ].
Section WithCeil.
Context {CEILV : CEIL}.
Section GlueFo.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).
  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.spo_facts K KST).
  #[local] Notation GIo_stdio_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.GIo_stdio_step K KST HFL).
  #[local] Notation GIo_stdio_step_same := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.GIo_stdio_step_same K KST HFL).
  #[local] Notation keeps_of_stdio := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.keeps_of_stdio K).
  #[local] Notation client_range_lo := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.client_range_lo K).

  (* [comment removed for export] *)
  Definition malloc_stmt_8k : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo n : Z),
      std_pre_o K sp tp R s CL FB lo 8192 m -> a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
      implM ssegs (pmalloc HO n) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIo K R s' CL FB m' /\ enomem_at R s' m'
              | Some q => exists A junk, a0v = Z_to_bv 64 A /\ GIo K R s' ((q, A, n) :: CL) FB m'
                          /\ rw_cells ssegs m' A [CB (Z.to_nat n) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom ssegs)).
  Hypothesis MALLOC8K : malloc_stmt_8k.

  (* [comment removed for export] *)
  Lemma GIo_stdio_step_err : forall R (s : PS) CL FB m m' W SP l' (e' : word),
    GIo K R s CL FB m -> munch W m m' -> wmono ssegs m m' ->
    Forall (fun iv => stdio_iv R CL FB SP iv \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160)) W -> SP <= rc_spmain R ->
    rw_cells ssegs m' (utp R + -164) [C4 e'] ->
    STDIOR l' FB m' ->
    GIo K R (set_libc l' s) CL FB m'.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros R s CL FB m m' W SP l' e' G MU WM HW HSP ERR SR'.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA].
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold rc_spmain in HSP. unfold stdio_iv, rc_spmain in HW.
    assert (OUT : forall a, 0 <= a < 2^64 ->
              ~ (CEILZ <= a < usp0 R - 48) -> ~ in_block (CL ++ FB) a -> ~ (0x23660 <= a < 0x23930) -> ~ (0x54148 <= a < 0x54970) ->
              ~ (utp R - 164 <= a < utp R - 160) -> outside W a).
    { intros a Ha N1 N2 N3 N4 N5. eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd].
      destruct Hiv as [[X|[X|[X|X]]]|X]; cbn [fst snd] in X; try (keep_hyps CEILV R a lo hi N1 X N3 N4 N5; lia).
      intros Hin. apply N2. eapply in_block_of_iv; [exact X| cbn [fst snd]; lia]. }
    assert (BF : forall a, in_block (CL ++ FB) a -> 0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x55000 <= a) /\ (a < utp R - 200 \/ utp R - 200 + 4096 <= a)).
    { intros a Ha. exact (in_block_facts (utp R) (CL ++ FB) a BO Ha). }
    unfold GIo, set_libc. cbn [ps_heap ps_libc ps_outfile ps_tls].
    split.
    { eapply HFL; [exact HH| exact MU| exact WM|].
      apply Forall_forall. intros [lo hi] Hiv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as X. unfold heap_client_iv in *. cbn [fst snd] in *.
      destruct X as [[X|[X|[X|X]]]|X]; [left; lia | right; left; exact X | right; right; left; lia | right; right; left; lia | right; right; right; lia]. }
    split; [apply (proj2 (KST l' R FB m')); exact SR'|].
    split. { eapply HARNR_agree; [| |exact HA]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split. { unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e & A1 & A2 & A3 & A4 & A5 & A6 & Ht); subst z x. exists t, e'.
             assert (AG : agrees_on (fun a => core_tls_fp R a /\ ~ (utp R - 164 <= a < utp R - 160)) m m').
             { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [Hp Hn]. unfold core_tls_fp in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R a TBC Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R a Hp H1; lia)| (keep_hyps CEILV R a TBI Hp; lia)| (keep_hyps CEILV R a TBI Hp; lia)| exact Hn]. }
             Ltac trt AG A := eapply agrees_rw_cells; [exact AG | exact A | intros a Ha; unfold core_tls_fp; sl_lit_sizes_in Ha; cbn in Ha; lia].
             split; [trt AG A1|]. split; [exact ERR|]. split; [trt AG A3|]. split; [trt AG A4|]. split; [trt AG A5|]. split; [trt AG A6| exact Ht]. }
    split. { eapply PCAP_TLS_agree; [| |exact PT]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split. { eapply CORE_LIBC_agree; [| |exact CLI]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split. { eapply CORE_MISC_agree; [| |exact CM]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split. { eapply CORE_EXIT_agree; [| |exact CE]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split. { eapply CORE_STK_agree; [| |exact CS]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split; [exact Etls|]. split; [exact TB|]. split; [exact BOK| exact SPW].
  Qed.

  Definition keeps_of_stdio_err__stmt : Prop := forall R (s : PS) CL FB m m' W SP,
    GIo K R s CL FB m -> munch W m m' -> wmono ssegs m m' ->
    Forall (fun iv => (CEILZ <= fst iv /\ snd iv <= SP) \/ iv_in_block FB iv
                      \/ (0x23660 <= fst iv /\ snd iv <= 0x23930) \/ (0x54148 <= fst iv /\ snd iv <= 0x54970)
                      \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160)) W ->
    CEILZ <= SP ->
    agrees_on (client_keeps CL SP) m m'.
  Section Sz1.
  Variables R s CL FB m m' W SP : ltac2:(SecDiet.SzSec.tyM 'keeps_of_stdio_err__stmt "vvvvvvvv" @R).
  Lemma keeps_of_stdio_err__body : ltac2:(SecDiet.SzSec.bodyP 'keeps_of_stdio_err__stmt "vvvvvvvv").
  Proof using Type. pin_using tt.
    intros G MU WM HW HSP.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    eapply agrees_on_weaken.
    - eapply (keeps_of_stdio R s CL FB m m' W SP (fun a => utp R - 164 <= a < utp R - 160)); [exact G| exact MU| exact WM| | exact HSP].
      eapply Forall_impl; [| exact HW]. intros iv [X|[X|[X|[X|X]]]]; [left| right; left| right; right; left| right; right; right; left| right; right; right; right]; try exact X.
      intros a Ha. lia.
    - intros a Hk. split; [exact Hk|]. intros Hr. destruct Hk as [Hk|Hk]; [lia|].
      destruct (in_block_facts _ _ a BO1 Hk) as (F1 & F2 & F3 & F4). lia.
  Qed.
  End Sz1.
  Lemma keeps_of_stdio_err : ltac:(let t := eval cbv delta [keeps_of_stdio_err__stmt] in keeps_of_stdio_err__stmt in exact t).
  Proof using Type. intros R s CL FB m m' W SP. ltac2:(SecDiet.SzSec.closeP 'keeps_of_stdio_err__body "vvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition STDIOR_keep__stmt : Prop := forall (l : libc_st hptr) FB (CL : list cblk) R m m' W,
    STDIOR l FB m -> blocks_ok (utp R) (CL ++ FB) -> tls_block_ok (utp R - 200) -> munch W m m' -> wmono ssegs m m' ->
    Forall (fun iv => CEILZ <= fst iv \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160)) W ->
    STDIOR l FB m'.
  Section Sz2.
  Variables l FB CL R m m' W : ltac2:(SecDiet.SzSec.tyM 'STDIOR_keep__stmt "vvvvvvv" @l).
  Lemma STDIOR_keep__body : ltac2:(SecDiet.SzSec.bodyP 'STDIOR_keep__stmt "vvvvvvv").
  Proof using Type. pin_using tt.
    intros SR BOK TB MU WM HW.
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    unfold tls_block_ok in TB. destruct TB as (TBA & TB0 & TBC & TBI).
    eapply (STDIOR_agree l FB m m' (fun a => a < CEILZ /\ ~ (utp R - 200 <= a < utp R - 200 + 4096))); [exact SR| | |].
    - eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [Hc Hn].
      eapply outside_of_Forall; [exact HW|]. intros [lo hi] [X|X]; cbn [fst snd] in *; lia.
    - intros a Ha. unfold GI.stdio_static in Ha. lia.
    - intros a Ha. destruct (in_block_facts _ _ a BO2 Ha) as (_ & X & _ & Y). lia.
  Qed.
  End Sz2.
  Lemma STDIOR_keep : ltac:(let t := eval cbv delta [STDIOR_keep__stmt] in STDIOR_keep__stmt in exact t).
  Proof using Type. intros l FB CL R m m' W. ltac2:(SecDiet.SzSec.closeP 'STDIOR_keep__body "vvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mode_lit_facts__stmt : Prop := forall wr MODE md, mode_lit wr MODE md ->
    exists slack,
      ro_bytes ssegs MODE (md ++ Z_to_bv 8 0 :: slack)
      /\ (0x10000 <= MODE /\ MODE + Z.of_nat (length md) + 1 + Z.of_nat (length slack) <= 0x13000)
      /\ ~ In (Z_to_bv 8 0) md
      /\ (- (MODE + Z.of_nat (length md) + 1)) mod 8 <= Z.of_nat (length slack)
      /\ (mode_m0 md = 114 \/ mode_m0 md = 119)
      /\ mode_m0 md = (if wr then 119 else 114)
      /\ fmodeflags md = (if wr then 577 else 0)
      /\ has_byte 43 md = false /\ has_byte 101 md = false.
  Section Sz3.
  Variables wr MODE md : ltac2:(SecDiet.SzSec.tyM 'mode_lit_facts__stmt "vvv" @wr).
  Lemma mode_lit_facts__body : ltac2:(SecDiet.SzSec.bodyP 'mode_lit_facts__stmt "vvv").
  Proof using Type. pin_using tt.
    intros ML.
 unfold mode_lit, STR_RB in ML. destruct wr.
    - destruct ML as [[-> ->] | [-> ->]].
      + exists [Z_to_bv 8 97; Z_to_bv 8 110; Z_to_bv 8 32; Z_to_bv 8 105].
        split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try lia; try reflexivity. intros [X|[]]. discriminate X. right; reflexivity.
      + exists [Z_to_bv 8 65; Z_to_bv 8 32; Z_to_bv 8 110; Z_to_bv 8 117; Z_to_bv 8 108; Z_to_bv 8 108].
        split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try lia; try reflexivity. intros [X|[X|[]]]; discriminate X. right; reflexivity.
    - destruct ML as [-> ->].
      exists [Z_to_bv 8 109; Z_to_bv 8 97].
      split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try lia; try reflexivity. intros [X|[X|[]]]; discriminate X. left; reflexivity.
  Qed.
  End Sz3.
  Lemma mode_lit_facts : ltac:(let t := eval cbv delta [mode_lit_facts__stmt] in mode_lit_facts__stmt in exact t).
  Proof using Type. intros wr MODE md. ltac2:(SecDiet.SzSec.closeP 'mode_lit_facts__body "vvv"). Qed.

  (* [comment removed for export] *)
  Definition files_R_newhead__stmt : Prop := forall m m' fs (FB : list cblk) A,
    files_R m 0 fs FB ->
    (forall q1 A1 n1 f1 FB', FB = (q1, A1, n1) :: FB' ->
        FILE_R m f1 A1 (A1 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK 0 (hd_addr FB') -> heap_file_inv f1 ->
        FILE_R m' f1 A1 (A1 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK A (hd_addr FB')) ->
    (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) (tl FB) ->
        FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
        FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
    files_R m' A fs FB.
  Section Sz4.
  Variables m m' A : ltac2:(SecDiet.SzSec.tyM 'files_R_newhead__stmt "vvkkv" @m).
  Lemma files_R_newhead__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_newhead__stmt "vvkkv").
  Proof using Type. pin_using tt.
    intros fs FB FS HHD HTL.
    destruct fs as [|[q1 f1] fs]; destruct FB as [|[[q1' A1] n1] FB]; cbn in FS |- *; try exact FS.
    destruct FS as (-> & -> & B0 & Bhi & FR & INV & REST).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
    split; [exact (HHD q1 A1 FILE_ALLOC f1 FB eq_refl FR INV)|]. split; [exact INV|].
    eapply files_R_frame; [exact REST|]. intros q2 A2 n2 f2 pv2 nx2 HIN2. apply (HTL q2 A2 n2 f2 pv2 nx2). exact HIN2.
  Qed.
  End Sz4.
  Lemma files_R_newhead : ltac:(let t := eval cbv delta [files_R_newhead__stmt] in files_R_newhead__stmt in exact t).
  Proof using Type. intros m m' fs FB A. ltac2:(SecDiet.SzSec.closeP 'files_R_newhead__body "vvkkv"). Qed.

  (* [comment removed for export] *)
  Lemma fcells_split_prev : forall flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
    fcells flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl =
    [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 re); C8 (Z_to_bv 64 cf);
     C8 (Z_to_bv 64 we); C8 (Z_to_bv 64 wp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wb);
     C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 wf); C8 (Z_to_bv 64 sf); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bs)]
    ++ [C8 (Z_to_bv 64 pv)]
    ++ [C8 (Z_to_bv 64 nx); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
        C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0); CB 80 tl].
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Lemma FILE_R_prev_cell : forall m f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx -> rw_cells ssegs m (Fp + 104) [C8 (Z_to_bv 64 pv)].
  Proof using Type. pin_using tt.
    intros m f Fp BA cf rf sf pv nx (flags & mode & rp & tail & bufbytes & FC & _).
    rewrite fcells_split_prev in FC. apply (proj1 (rw_cells_app ssegs m Fp _ _)) in FC as [_ FC].
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in FC as [FC _]. cbn [cells_size csize Nat.add] in FC.
    replace (Fp + Z.of_nat 104) with (Fp + 104) in FC by lia. exact FC.
  Qed.

  (* [comment removed for export] *)
  Definition FILE_R_set_prev__stmt : Prop := forall m m' f Fp BA cf rf sf pv pv' nx W,
    FILE_R m f Fp BA cf rf sf pv nx ->
    munch W m m' -> wmono ssegs m m' ->
    Forall (fun iv : Z * Z => (Fp + 232 <= fst iv \/ snd iv <= Fp) \/ (fst iv = Fp + 104 /\ snd iv = Fp + 112)) W ->
    Forall (fun iv : Z * Z => BA + f_bufsize f <= fst iv \/ snd iv <= BA) W ->
    0 <= f_bufsize f ->
    rw_cells ssegs m' (Fp + 104) [C8 (Z_to_bv 64 pv')] ->
    FILE_R m' f Fp BA cf rf sf pv' nx.
  Section Sz7.
  Variables m m' f Fp BA cf rf sf pv pv' nx W : ltac2:(SecDiet.SzSec.tyM 'FILE_R_set_prev__stmt "vvvvvvvvvvvv" @m).
  Lemma FILE_R_set_prev__body : ltac2:(SecDiet.SzSec.bodyP 'FILE_R_set_prev__stmt "vvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FR MU WM D1 D2 BS PC.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - rewrite fcells_split_prev in FC |- *.
      apply (proj1 (rw_cells_app ssegs m Fp _ _)) in FC as [FCa FC]. apply (proj1 (rw_cells_app ssegs m _ [_] _)) in FC as [_ FCb].
      cbn [cells_size csize Nat.add] in FCa, FCb |- *.
      apply (proj2 (rw_cells_app ssegs m' Fp _ _)). split.
      + eapply rw_cells_transport; [exact FCa| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
        apply disjoint_from_Forall. eapply Forall_impl; [| exact D1]. intros [lo hi]; cbn; lia.
      + apply (proj2 (rw_cells_app ssegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
        * replace (Fp + Z.of_nat 104) with (Fp + 104) by lia. exact PC.
        * eapply rw_cells_transport; [exact FCb| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
          apply disjoint_from_Forall. eapply Forall_impl; [| exact D1]. intros [lo hi]; cbn; lia.
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      apply disjoint_from_Forall. eapply Forall_impl; [| exact D2]. intros [lo hi]; cbn; lia.
  Qed.
  End Sz7.
  Lemma FILE_R_set_prev : ltac:(let t := eval cbv delta [FILE_R_set_prev__stmt] in FILE_R_set_prev__stmt in exact t).
  Proof using Type. intros m m' f Fp BA cf rf sf pv pv' nx W. ltac2:(SecDiet.SzSec.closeP 'FILE_R_set_prev__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma HARNR_cons : forall (o : option hptr) (b : cblk) FB m, HARNR o FB m -> HARNR o (b :: FB) m.
  Proof using Type. pin_using tt.
    intros o b FB m (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    destruct o as [q'|]; [|exact H3]. destruct H3 as (A' & HIn & HC). exists A'. split; [right; exact HIn| exact HC].
  Qed.

  (* [comment removed for export] *)
  Lemma fopen_finish : forall R (sM : PS) (CL FB : list cblk) m3 m7 W q A fd (wr : bool) (fl : Z) junk2 SP,
    GIo K R sM ((q, A, FILE_ALLOC) :: CL) FB m3 ->
    munch W m3 m7 -> wmono ssegs m3 m7 ->
    Forall (fun iv : Z * Z => (CEILZ <= fst iv /\ snd iv <= SP) \/ (fst iv = A /\ snd iv = A + 232) \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                              \/ (FB <> [] /\ fst iv = hd_addr FB + 104 /\ snd iv = hd_addr FB + 112)) W ->
    CEILZ <= SP -> SP <= rc_spmain R ->
    rw_cells ssegs m7 A (file_cells (Z_to_bv 64 fl) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ F_STDIO_WRITE F_STDIO_SEEK (A + 240) 1024 0 (hd_addr FB) fd
                          (Z_to_bv 64 0) 4294967295 (repeat (Z_to_bv 8 0) 80)) ->
    rw_cells ssegs m7 (A + 232) [CB 1032 junk2] ->
    rw_cells ssegs m7 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells ssegs m7 A_OFL_HEAD [C8 (Z_to_bv 64 A)] ->
    (hd_addr FB <> 0 -> rw_cells ssegs m7 (hd_addr FB + 104) [C8 (Z_to_bv 64 A)]) ->
    fl = (if wr then 4 else 8) -> 3 <= fd <= 4096 ->
    GIo K R (set_libc (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) sM) CL ((q, A, FILE_ALLOC) :: FB) m7
    /\ agrees_on (client_keeps CL SP) m3 m7.
  Proof using EQB HAL HFL HPL KST. pin_using (fun (EQB HAL HFL HPL KST : unit) => tt).
    intros R sM CL FB m3 m7 W q A fd wr fl junk2 SP G MU WM HW CSP HSP FC7 BLK7 OL7 OH7 OLDP7 -> HFD.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA].
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold rc_spmain in HSP.
    apply (proj1 (KST _ R _ _)) in HS as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; left; left; reflexivity)) as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6).
    unfold cb_addr, cb_size, FILE_ALLOC in BK1, BK2, BK3, BK4, BK5, BK6. cbn [fst snd] in BK1, BK2, BK3, BK4, BK5, BK6.
    pose proof (blocks_apart_app_inv _ _ BA) as (BAc & BA2 & BAX). cbn [blocks_apart] in BAc. destruct BAc as [APc BAc'].
    assert (APf : Forall (apart (q, A, FILE_ALLOC)) FB).
    { apply Forall_forall. intros b Hb. apply (BAX (q, A, FILE_ALLOC) b); [left; reflexivity| exact Hb]. }
    pose proof BO as BO'. apply Forall_cons_iff in BO' as [_ BO']. apply Forall_app in BO' as [BOCL BOFB].
    (* [comment removed for export] *)
    assert (HDB : forall q1 A1' n1 FB', FB = (q1, A1', n1) :: FB' ->
              n1 = FILE_ALLOC /\ 0 < A1' /\ A1' + 1264 <= CEILZ /\ (A1' + 1264 <= 0x10000 \/ 0x55000 <= A1')
              /\ (A1' + 1264 <= utp R - 200 \/ utp R - 200 + 4096 <= A1')
              /\ (A + 1264 <= A1' \/ A1' + 1264 <= A) /\ Forall (apart (q1, A1', n1)) FB').
    { intros q1 A1' n1 FB' E. rewrite E in FS, BOFB, APf, BA2.
      destruct (lc_files (ps_libc sM)) as [|[q1' f1] fs']; [exfalso; exact FS|].
      cbn in FS. destruct FS as (Eq1 & En1 & B0 & Bhi & FR1h & INV1 & REST1). subst n1.
      apply Forall_cons_iff in BOFB as [(K1 & K2 & K3 & K4 & K5 & K6) _]. unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3, K4, K5, K6. cbn [fst snd] in K1, K2, K3, K4, K5, K6.
      apply Forall_cons_iff in APf as [AP _]. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP.
      cbn [blocks_apart] in BA2. destruct BA2 as [APh _].
      unfold FILE_ALLOC in *. repeat split; try (keep_hyps CEILV R A A1' B0 K4 K5 K6 AP; lia). exact APh. }
    (* [comment removed for export] *)
    set (P37 := fun a : Z => ~ (CEILZ <= a < SP) /\ ~ (A <= a < A + 232) /\ ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8)
                             /\ ~ (FB <> [] /\ hd_addr FB + 104 <= a < hd_addr FB + 112)).
    assert (AG : agrees_on P37 m3 m7).
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha (N1 & N2 & N3 & N4).
      eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd] in Hiv |- *.
      destruct Hiv as [X|[X|[X|(Xne & X1 & X2)]]]; [(keep_hyps CEILV R A SP a lo' hi' N1 X; lia)| (keep_hyps CEILV R A SP a lo' hi' N2 X; lia)| (keep_hyps CEILV R A SP a lo' hi' N3 X; lia)|]. intros Hin. apply N4. split; [exact Xne| lia]. }
    (* [comment removed for export] *)
    assert (OUT : forall a, 0 <= a < 2^64 ->
              ~ (CEILZ <= a < usp0 R - 48) -> ~ in_block (((q, A, FILE_ALLOC) :: CL) ++ FB) a -> ~ (0x23660 <= a < 0x23930) -> ~ (0x54148 <= a < 0x54970) -> outside W a).
    { intros a Ha N1 N2 N3 N4. eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd].
      destruct Hiv as [X|[X|[X|(Xne & X1 & X2)]]]; cbn [fst snd] in *.
      - (keep_hyps CEILV R A SP a lo' hi' HSP N1 X; lia).
      - intros Hin. apply N2. apply (proj2 (in_block_In _ _)). exists (q, A, FILE_ALLOC).
        split; [apply in_or_app; left; left; reflexivity| unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
      - unfold A_OFL_HEAD in X. lia.
      - intros Hin. apply N2. destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
        destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _). apply (proj2 (in_block_In _ _)). exists (q1, A1', n1).
        split; [apply in_or_app; right; left; reflexivity| unfold cb_addr, cb_size; cbn [fst snd]; subst n1; unfold FILE_ALLOC; lia]. }
    assert (BF : forall a, in_block (((q, A, FILE_ALLOC) :: CL) ++ FB) a -> 0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x55000 <= a) /\ (a < utp R - 200 \/ utp R - 200 + 4096 <= a)).
    { intros a Ha. exact (in_block_facts (utp R) _ a BO Ha). }
    (* [comment removed for export] *)
    assert (FBn : forall q2 A2 n2, In (q2, A2, n2) FB -> n2 = FILE_ALLOC /\ 0 < A2).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m3 0 _ FB q2 A2 n2 FS ND HIN) as (f & pv & nx & _ & _ & En & B0 & _). split; [exact En| exact B0]. }
    (* [comment removed for export] *)
    assert (HSt : forall a, GI.stdio_static a -> ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8) -> P37 a).
    { intros a Hs Hn. unfold GI.stdio_static, A_OFL_HEAD in *. subst P37. cbn beta.
      split; [lia|]. split; [lia|]. split; [exact Hn|].
      intros (Xne & Xr). destruct FB as [|[[q1 A1'] n1] FB']; [exact (Xne eq_refl)|]. cbn [hd_addr] in Xr.
      destruct (HDB q1 A1' n1 FB' eq_refl) as (_ & _ & _ & K4 & _). (keep_hyps CEILV R A1' A a Hs Xr K4; lia). }
    (* [comment removed for export] *)
    assert (HBl : forall q2 A2 n2 a, In (q2, A2, n2) FB -> A2 <= a < A2 + 1264 -> ~ (A2 = hd_addr FB /\ A2 + 104 <= a < A2 + 112) -> P37 a).
    { intros q2 A2 n2 a HIN Ha Hn. destruct (FBn _ _ _ HIN) as [-> B0].
      pose proof (proj1 (Forall_forall _ _) BOFB _ HIN) as (K1 & K2 & K3 & K4 & K5 & K6). unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3, K4, K5, K6. cbn [fst snd] in K1, K2, K3, K4, K5, K6.
      pose proof (proj1 (Forall_forall _ _) APf _ HIN) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP.
      subst P37. cbn beta. unfold A_OFL_HEAD. split; [lia|]. split; [lia|]. split; [(keep_hyps CEILV hptr R FB A A2 a Ha K5; lia)|].
      intros (Xne & Xr). destruct FB as [|[[q1 A1'] n1] FB']; [exact (Xne eq_refl)|]. cbn [hd_addr] in Xr, Hn.
      destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _ & _ & _ & _ & _ & APh).
      destruct HIN as [E|HIN].
      - injection E as <- <- _. apply Hn. split; [reflexivity| lia].
      - pose proof (proj1 (Forall_forall _ _) APh _ HIN) as AP2. unfold apart, cb_addr, cb_size in AP2. cbn [fst snd] in AP2. subst n1. unfold FILE_ALLOC in AP2. lia. }
    (* [comment removed for export] *)
    assert (SR7 : STDIOR (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) ((q, A, FILE_ALLOC) :: FB) m7).
    { unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files hd_addr].
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED in *.
      Ltac tra7 AG HSt X := eapply agrees_rw_cells; [exact AG | exact X | intros a Ha; cbn in Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]].
      split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SEbs; intros a Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]. }
      split; [tra7 AG HSt U1|]. split; [tra7 AG HSt U2|]. split; [tra7 AG HSt U3|]. split; [exact OL7|]. split; [exact OH7|].
      split.
      - cbn [files_R]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [unfold FILE_ALLOC; lia|].
        split.
        { (* [comment removed for export] *)
          exists (Z_to_bv 64 (if wr then 4 else 8)), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), (firstn 1024 (skipn 8 junk2)).
          cbn [f_rbuf f_wbuf f_wactive f_bufsize f_fd f_nord f_nowr f_eof f_stdoutw f_lbf_nl fdopen_file wfn_of lbf_of zlength length Z.of_nat Z.add].
          split. { unfold fcells, FILE_BUF_OFF, BUFSIZ. exact FC7. }
          split. { unfold flags_ok. cbn [f_nord f_nowr f_eof f_chan]. unfold F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM. destruct wr; rewrite unsigned_lit by lia; cbn; repeat split; reflexivity. }
          split. { pose proof (rw_cells_split_CB ssegs m7 (A + 232) [] 1032 junk2 [] [8%nat; 1024%nat] BLK7 eq_refl) as B2.
                   cbn [app mk_CB_cells] in B2. apply rw_cells_split2 in B2 as [_ B2]. cbn [csize] in B2.
                   unfold FILE_BUF_OFF, BUFSIZ. replace (A + 232 + Z.of_nat 8) with (A + 240) in B2 by lia. exact B2. }
          split; [reflexivity|]. split; [intros _; reflexivity|]. split; [unfold BUFSIZ, zlength; cbn; lia|].
          split; [intros X; exfalso; exact (X eq_refl)|]. fastfirst (first [ noevar_assumption |split; [lia|]; split; [unfold zlength; cbn; lia| reflexivity] | unfold zlength; cbn; lia]). }
        split.
        { unfold heap_file_inv. cbn. destruct wr; cbn.
          all: split; [reflexivity|]; split; [lia|]; split; [reflexivity|]; split; [reflexivity|].
          all: split; [intros X; first [discriminate X | split; reflexivity] |]; split; [intros X; first [discriminate X | reflexivity]| apply Forall_nil]. }
        (* [comment removed for export] *)
        eapply files_R_newhead; [exact FS| |].
        + intros q1 A1' n1 f1 FB' E FR1 INV1.
          destruct (HDB q1 A1' n1 FB' E) as (En1 & B01 & KC & KS & KT & AP1 & APh).
          pose proof INV1 as (_ & _ & BS1 & _).
          eapply (FILE_R_set_prev m3 m7 f1 A1' _ _ _ _ 0 A (hd_addr FB') W); [exact FR1| exact MU| exact WM| | | rewrite BS1; unfold BUFSIZ; lia|].
          * eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in *.
            destruct X as [X|[X|[X|(Xne & X1 & X2)]]]; [left; (keep_hyps CEILV R A SP A1' lo' hi' KC X; lia)| left; (keep_hyps CEILV R A A1' lo' hi' AP1 X; lia)| left; unfold A_OFL_HEAD in X; (keep_hyps CEILV R A A1' lo' hi' KS X; lia)| right]. rewrite E in X1, X2. cbn [hd_addr] in X1, X2. lia.
          * rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in *.
            destruct X as [X|[X|[X|(Xne & X1 & X2)]]]; [(keep_hyps CEILV R A SP A1' lo' hi' KC X; lia)| (keep_hyps CEILV R A A1' lo' hi' AP1 X; lia)| unfold A_OFL_HEAD in X; (keep_hyps CEILV R A A1' lo' hi' KS X; lia)|]. rewrite E in X1, X2. cbn [hd_addr] in X1, X2. lia.
          * rewrite E in OLDP7. cbn [hd_addr] in OLDP7. apply OLDP7. lia.
        + intros q2 A2 n2 f2 pv2 nx2 HIN2 FR2 INV2.
          assert (HIN2' : In (q2, A2, n2) FB) by (destruct FB as [|b FB']; [exact HIN2| right; exact HIN2]).
          pose proof INV2 as (_ & _ & BS2 & _).
          assert (NH : A2 <> hd_addr FB).
          { destruct FB as [|[[q1 A1'] n1] FB']; [exact (False_ind _ HIN2)|]. cbn [hd_addr tl] in HIN2 |- *.
            destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _ & _ & _ & _ & _ & APh).
            pose proof (proj1 (Forall_forall _ _) APh _ HIN2) as AP2. unfold apart, cb_addr, cb_size in AP2. cbn [fst snd] in AP2.
            destruct (FBn _ _ _ HIN2') as [-> _]. subst n1. unfold FILE_ALLOC in AP2. lia. }
          eapply FILE_R_agree; [exact FR2| exact AG| |].
          * intros a Ha. eapply (HBl q2 A2 n2 a HIN2'); [lia|]. intros [X _]. exact (NH X).
          * rewrite BS2. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HBl q2 A2 n2 a HIN2'); [lia|]. intros [X _]. exact (NH X).
      - (* [comment removed for export] *)
        cbn [map fst]. apply List.NoDup_cons; [| exact ND].
        intros HIn. rewrite <- (files_R_toks m3 0 _ FB FS) in HIn. apply in_map_iff in HIn as ([[qb Ab] nb] & Eb & HbIn). cbn in Eb. subst qb.
        pose proof (HAL _ _ _ _ (q, A, FILE_ALLOC) HH ltac:(apply in_or_app; left; left; reflexivity)) as E1.
        pose proof (HAL _ _ _ _ (q, Ab, nb) HH ltac:(apply in_or_app; right; exact HbIn)) as E2.
        cbn [cb_tok cb_addr fst snd] in E1, E2.
        pose proof (proj1 (Forall_forall _ _) APf _ HbIn) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP.
        destruct (FBn _ _ _ HbIn) as [-> _]. unfold FILE_ALLOC in AP. lia. }
    split.
    - (* [comment removed for export] *)
      unfold GIo, set_libc. cbn [ps_heap ps_libc ps_outfile ps_tls].
      split.
      { eapply HPL; [| apply Permutation.Permutation_middle].
        eapply HFL; [exact HH| exact MU| exact WM|].
        apply Forall_forall. intros [lo' hi'] Hiv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as X. unfold heap_client_iv. cbn [fst snd] in *.
        destruct X as [X|[X|[X|(Xne & X1 & X2)]]].
        + left; lia.
        + right; left. unfold iv_in_block. apply Exists_exists. exists (q, A, FILE_ALLOC).
          split; [first [apply in_or_app; left; left; reflexivity | left; reflexivity] | unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
        + right; right; left. unfold A_OFL_HEAD in X. lia.
        + right; left. destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
          destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _). unfold iv_in_block. apply Exists_exists. exists (q1, A1', n1).
          split; [first [apply in_or_app; right; left; reflexivity | right; apply in_or_app; right; left; reflexivity] | unfold cb_addr, cb_size; cbn [fst snd]; subst n1; unfold FILE_ALLOC; lia]. }
      split; [apply (proj2 (KST _ R _ m7)); exact SR7|].
      split. { apply HARNR_cons. eapply HARNR_agree; [| |exact HA]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split. { eapply CORE_TLS_agree; [| |exact CT]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| clear - Hp TBC; (keep_hyps CEILV R a TBC Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R A a Hp H1; lia)| (keep_hyps CEILV R A a TBI Hp; lia)| (keep_hyps CEILV R A a TBI Hp; lia)]. }
      split. { eapply PCAP_TLS_agree; [| |exact PT]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split. { eapply CORE_LIBC_agree; [| |exact CLI]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R A a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R A a Hp H1; lia)| (keep_hyps CEILV R A a Hp; lia)| (keep_hyps CEILV R A a Hp; lia)]. }
      split. { eapply CORE_MISC_agree; [| |exact CM]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R A a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R A a Hp H1; lia)| (keep_hyps CEILV R A a Hp; lia)| (keep_hyps CEILV R A a Hp; lia)]. }
      split. { eapply CORE_EXIT_agree; [| |exact CE]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R A a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R A a Hp H1; lia)| (keep_hyps CEILV R A a Hp; lia)| (keep_hyps CEILV R A a Hp; lia)]. }
      split. { eapply CORE_STK_agree; [| |exact CS]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split; [exact Etls|]. split; [exact TB|]. split; [| exact SPW].
      eapply blocks_ok_perm; [apply Permutation.Permutation_middle| exact BOK].
    - (* [comment removed for export] *)
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hk.
      eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd].
      destruct Hk as [Hk|Hk].
      + destruct Hiv as [X|[X|[X|(Xne & X1 & X2)]]]; cbn [fst snd] in *; [lia| lia| unfold A_OFL_HEAD in X; lia|].
        destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
        destruct (HDB q1 A1' n1 FB' eq_refl) as (_ & _ & KC & _). lia.
      + pose proof (in_block_facts (utp R) CL a BOCL Hk) as (F1 & F2 & F3 & F4).
        apply in_block_In in Hk as ([[qb Ab] nb] & HbIn & Hb). unfold cb_addr, cb_size in Hb. cbn [fst snd] in Hb.
        destruct Hiv as [X|[X|[X|(Xne & X1 & X2)]]]; cbn [fst snd].
        * cbn [fst snd] in X. lia.
        * cbn [fst snd] in X. pose proof (proj1 (Forall_forall _ _) APc _ HbIn) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. (keep_hyps CEILV R A a Ab nb lo' hi' Hb X AP; lia).
        * cbn [fst snd] in X. unfold A_OFL_HEAD in X. lia.
        * cbn [fst snd] in X1, X2. destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
          destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _).
          pose proof (BAX (qb, Ab, nb) (q1, A1', n1) ltac:(right; exact HbIn) ltac:(left; reflexivity)) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. subst n1. unfold FILE_ALLOC in AP. (keep_hyps CEILV R A1' A a Ab nb lo' hi' Hb X1 X2 AP; lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fopen_o_proof__stmt : Prop := fopen_stmt_o HO K.
  Section Sz9.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME MODE name md wr : ltac2:(SecDiet.SzSec.tyM 'fopen_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fopen_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB HAL HFL HPL KST MALLOC8K. pin_using (fun (EQB HAL HFL HPL KST MALLOC8K : unit) => tt).
    intros SPO -> -> HNAME NNUL NLEN NOK NCR HMODE MLIT.
    (* [comment removed for export] *)
    assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
   (* [comment removed for export] *)
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct (mode_lit_facts wr MODE md MLIT) as (slack & ROMD & MDR & NONUL & PAD & M0 & M0W & FMV & NOPLUS & NOE).
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    assert (TPR : utp R + -200 = 0x339d0) by (unfold utp in *; lia).
    assert (TPLO : utp R + -160 <= lo) by (unfold utp, rc_lo in *; lia).
    assert (TP200 : 200 <= utp R) by (unfold utp in *; lia).
    unfold utp in TPR, TPLO, TP200.
    (* [comment removed for export] *)
    assert (NSEP : NAME + (Z.of_nat (length name) + 1) <= lo \/ bv_unsigned sp <= NAME).
    { destruct NCR as [NCR | NCR].
      - destruct (client_range_lo R s CL FB m (bv_unsigned sp) NAME (Z.of_nat (length name) + 1) lo G NCR ltac:(lia) LOR ltac:(lia)) as (_ & C2 & _). exact C2.
      - left. lia. }
    pose proof CT as (tlst & errv & _ & ERR & _).
    unfold s_fopen, Stdio.fopen.
    apply implM_sysk.
    eapply evt_cut.
    { eapply (fopen_S1 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack);
        first [exact ROMD | exact ST | exact MI | exact MDR | exact NONUL | exact PAD | exact M0 | exact NOPLUS | exact NOE | lia
              | match goal with |- ?g => idtac "S1 side:" g end]. }
    cbv beta. intros ms1 PO. destruct PO as (x1 & u0 & u1 & u2 & b4 & b5 & b6 & u3 & u4 & u5 & u6 & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (HNAME1 : bytes_at ssegs m1 NAME (name ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact HNAME| exact MU1|]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
    assert (ERR1 : rw_cells ssegs m1 (bv_unsigned (rc_tp R) + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. lia. }
    destruct SSP as [GOT GUARD].
    assert (SSP1 : ssp_cells m1 (rc_canary R)).
    { split; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1| unfold got_ssp, ssp_guard; cbn; lia]). }
    step_ecall. split.
    { destruct wr; cbn [open_name_ok] in NOK; rewrite FMV; at_node_solve__p0.
      all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
      all: first [exact NNUL | exact NOK | exact (proj1 NOK) | exact (proj2 NOK)   (* [comment removed for export] *)
                 | rewrite unsigned_lit by lia; exact HNAME1 | vm_compute; reflexivity
                 | match goal with |- ?g => idtac "ATNODE:" g end]. }
    intros rsp a Hdec.
    assert (HD : match a with SErr e => rsp = efferr e /\ 1 <= e <= 4095 | SVal v => rsp = eff0 (Z_to_bv 64 v) /\ 3 <= v <= 4096 end).
    { assert (Hdec' : dec_open rsp = Some a) by (destruct wr; exact Hdec).
      unfold dec_open in Hdec'. apply dec_plain_Some in Hdec'. destruct a as [e|v]; [exact Hdec'|].
      destruct Hdec' as (E & OK & R'). split; [exact E|]. apply andb_prop in OK. destruct OK as [O1 O2]. apply Z.leb_le in O1. apply Z.leb_le in O2. lia. }
    clear Hdec. destruct a as [e|fd].
    - (* [comment removed for export] *)
      destruct HD as [-> HE].
      apply implM_upd_lc. apply implM_ret. unfold efferr, eff0. sys_nret.
      eapply evt_mono.
      { eapply (fopen_S2_fail ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack);
          first [exact FR1 | exact ERR1 | exact HE | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact M0 | exact MDR | exact NONUL | exact PAD | exact NOPLUS | exact NOE | exact ROMD | lia
                | match goal with |- ?g => idtac "S2F side:" g end]. }
      cbv beta. intros ms' PO. destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
      eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|].
      split. { eapply (keeps_of_stdio_err R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU'| exact WM'| | lia].
               apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; right; right; cbn; unfold utp; lia| apply Forall_nil]. }
      split; [reflexivity|].
      split. { eapply (GIo_stdio_step_err R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU'| exact WM'| | exact SPM| unfold utp; exact ERR'|].
               - apply Forall_cons; [left; left; cbn; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil].
               - cbn [ps_libc set_libc set_errno_lc]. eapply (STDIOR_keep _ FB CL R m m'); [exact SR| exact BOK| exact TB| exact MU'| exact WM'|].
                 apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil]. }
      cbn [ps_libc set_libc set_errno_lc lc_errno]. unfold utp. split; [exact ERR'| lia].
    - (* [comment removed for export] *)
      destruct HD as [-> HFD].
      eapply implM_evt.
      { unfold eff0. sys_nret. eapply (fopen_S2_ok ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack);
            first [exact ROMD | exact FR1 | exact ERR1 | exact SSP1 | exact HFD | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact MDR | exact NONUL | exact PAD | exact M0 | exact NOPLUS | exact NOE | (keep_hyps CEILV sp R lo NAME MODE name md slack LOB LOR SPW SPM SP47 NB TPR TPLO TP200; lia)
                  | destruct wr; rewrite FMV; [right | left]; reflexivity
                  | match goal with |- ?g => idtac "S2OK side:" g end ]. }
      cbv beta. intros ms2 PO. destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & sv2 & j0 & m2 & -> & FRO2 & FRI2 & ERR2 & SSP2 & MU2 & WM2 & MI2 & ST2).
      name_sp sp (-96).
      assert (TLSLO : bv_unsigned (rc_tp R) + -160 <= lo) by exact TPLO.
      eapply implM_bind.
      { pose proof MALLOC8K as MK. unfold malloc_stmt_8k in MK. eapply MK; [| reflexivity | unfold FILE_ALLOC; lia].
        split.
        { pose proof (GIo_stdio_step_err R s CL FB m m2 _ (bv_unsigned sp) (ps_libc s) errv G MU2 WM2) as G2.
          destruct s as [sh sl so st']; cbn [set_libc ps_libc] in G2 |- *. apply G2.
          - apply Forall_cons; [left; left; cbn; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil].
          - exact SPM.
          - unfold utp. exact ERR2.
          - eapply (STDIOR_keep _ FB CL R m m2); [exact SR| exact BOK| exact TB| exact MU2| exact WM2|].
            apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil]. }
        split; [rewrite Hsp; exact ST2|]. split; [exact LOR|]. split; [rewrite Hsp; lia|]. split; [rewrite Hsp; lia|].
        split; [exact MI2|]. split; [reflexivity|]. rewrite Hsp. apply aln16_add; [exact AL| reflexivity]. }
      cbv beta. intros po sM ms3 PO3.
      destruct PO3 as (a0v & m3 & REGS & OF3 & MI3 & ST3 & AG3 & RES).
      unfold hpost_regs in REGS. destruct REGS as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & ->).
      rewrite Hsp in ST3, AG3. subst sp0.
      replace (ret_pc (Z_to_bv 64 0x1b268)) with (Z_to_bv 64 0x1b268 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FRO3 : rw_cells ssegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply keeps_rw_cells_stack; [exact AG3| exact FRO2| lia]).
      assert (FRI3 : rw_cells ssegs m3 (bv_unsigned sp + -96) [CB 16 j0; C8 (rc_canary R); C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b120)])
        by (eapply keeps_rw_cells_stack; [exact AG3| exact FRI2| lia]).
      (* [comment removed for export] *)
      assert (AG03 : agrees_on (client_keeps CL (bv_unsigned sp)) m m3).
      { eapply agrees_on_trans.
        - eapply (keeps_of_stdio_err R s CL FB m m2 _ (bv_unsigned sp)); [exact G| exact MU2| exact WM2| | lia].
          apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; right; right; cbn; unfold utp; lia| apply Forall_nil].
        - eapply client_keeps_weaken; [exact AG3| lia| intros a Ha; exact Ha]. }
      destruct po as [q|].
      + (* [comment removed for export] *)
        destruct RES as (A & junk & -> & G3 & BLK).
        pose proof G3 as (HH3 & HS3 & HA3 & CT3 & PT3 & CLI3 & CM3 & CE3 & CS3 & Etls3 & TB3 & BOK3 & SPW3).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(apply in_or_app; left; left; reflexivity)) as (A1 & A2 & A3 & A4 & A5 & A6).
        unfold cb_addr, cb_size, FILE_ALLOC in A1, A2, A3, A4, A5, A6. cbn [fst snd] in A1, A2, A3, A4, A5, A6.
        pose proof (core_ssp R m3 CLI3) as SSP3.
        apply (proj1 (KST _ R _ _)) in HS3 as SR3.
        eapply implM_evt.
        { eapply (fopen_S6 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (P := A) (MODE := MODE) (md := md) (slack := slack);
            first [exact ROMD | exact BLK | exact FRO3 | exact FRI3 | exact SSP3 | exact HFD | exact ST3 | exact MI3 | exact MDR | exact NONUL | exact PAD | exact M0 | exact NOPLUS | exact NOE | (keep_hyps CEILV sp R lo NAME MODE name md slack A LOB LOR SPW3 SPM SP47 TPLO A1 A5 A4; lia)
                  | match goal with |- ?g => idtac "S6 side:" g end ]. }
        cbv beta. intros ms4 PO4.
        destruct PO4 as (x1' & e0 & e1 & e2 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & m4 & -> & FC4 & BLK4 & FRO4 & (sv2' & j0' & FRI4) & SSP4 & MU4 & WM4 & MI4 & ST4).
        (* [comment removed for export] *)
        pose proof CLI3 as (LC3 & _). unfold libc_cells in LC3.
        apply (proj1 (rw_cells_app ssegs m3 _ [_] _)) in LC3 as [_ LC3]. apply (proj1 (rw_cells_app ssegs m3 _ [_] _)) in LC3 as [THR3 LC3].
        apply (proj1 (rw_cells_app ssegs m3 _ [_] _)) in LC3 as [_ LC3]. apply (proj1 (rw_cells_app ssegs m3 _ [_] _)) in LC3 as [NL3 _].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in THR3, NL3.
        assert (THR4 : rw_cells ssegs m4 0x53d29 [C1 (Z_to_bv 8 0)]) by (eapply rw_cells_transport; [exact THR3| exact MU4| exact WM4| cbn; (keep_hyps CEILV sp R lo NAME MODE name md slack A LOR SPW3 A5; lia)]).
        assert (NL4 : rw_cells ssegs m4 NEED_LOCKS [C1 (Z_to_bv 8 0)]) by (unfold NEED_LOCKS; eapply rw_cells_transport; [exact NL3| exact MU4| exact WM4| cbn; (keep_hyps CEILV sp R lo NAME MODE name md slack A LOR SPW3 A5; lia)]).
        pose proof SR3 as (SO3 & SOI3 & SE3 & SEI3 & SIN3 & U13 & U23 & U33 & OL3 & OH3 & FS3 & ND3).
        assert (OL4 : rw_cells ssegs m4 A_OFL_LOCK [C4 (Z_to_bv 64 0)]) by (unfold A_OFL_LOCK in *; eapply rw_cells_transport; [exact OL3| exact MU4| exact WM4| cbn; (keep_hyps CEILV sp R lo NAME MODE name md slack A LOR SPW3 A5; lia)]).
        assert (OH4 : rw_cells ssegs m4 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr FB))]) by (unfold A_OFL_HEAD in *; eapply rw_cells_transport; [exact OH3| exact MU4| exact WM4| cbn; (keep_hyps CEILV sp R lo NAME MODE name md slack A LOR SPW3 A5; lia)]).
        (* [comment removed for export] *)
        pose proof BOK3 as [BO3 BA3].
        assert (HDF : hd_addr FB = 0 \/ (hd_addr FB <> 0 /\ (exists pvo : word, rw_cells ssegs m4 (hd_addr FB + 104) [C8 pvo])
                     /\ hd_addr FB + 232 <= lo /\ (hd_addr FB + 232 <= A \/ A + 1264 <= hd_addr FB) /\ (hd_addr FB + 232 <= 0x10000 \/ 0x55000 <= hd_addr FB))).
        { destruct FB as [|[[q1 Ah] n1] FB']; [left; reflexivity| right]. cbn [hd_addr].
          destruct (lc_files (ps_libc sM)) as [|[q1' f1] fs'] eqn:EFS; [exfalso; exact FS3|].
          cbn in FS3. destruct FS3 as (Eq1 & -> & B0 & Bhi & FR1h & INV1 & REST1).
          pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(apply in_or_app; right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
          unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3, K4, K5, K6. cbn [fst snd] in K1, K2, K3, K4, K5, K6.
          destruct (GIo_apart K R sM _ _ m3 (q, A, 1264) (q1, Ah, FILE_ALLOC) G3 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; right; left; reflexivity)) as [E|AP].
          { exfalso. pose proof (blocks_apart_app_inv _ _ BA3) as (BAc & _ & BAX). cbn in BAc. destruct BAc as [BAq _].
            assert (EA : A = Ah) by congruence. unfold FILE_ALLOC in *.
            pose proof (BAX (q, A, 1264) (q1, Ah, 1264) ltac:(left; reflexivity) ltac:(left; reflexivity)) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. (keep_hyps CEILV sp R NAME MODE name md Ah slack A EA AP; lia). }
          unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP.
          split; [lia|]. split.
          { exists (Z_to_bv 64 0). eapply rw_cells_transport; [exact (FILE_R_prev_cell _ _ _ _ _ _ _ _ _ FR1h)| exact MU4| exact WM4| cbn; (keep_hyps CEILV sp R lo NAME MODE name md Ah slack A LOR SPW3 K4 AP; lia)]. }
          unfold rc_lo in *. (keep_hyps CEILV sp R lo NAME MODE name md Ah slack A LOR SPW3 K4 K5 AP; lia). }
        assert (HDR : 0 <= hd_addr FB /\ hd_addr FB + 232 < 2^63).
        { destruct FB as [|[[q1 Ah] n1] FB']; cbn [hd_addr]; [lia|].
          destruct (lc_files (ps_libc sM)) as [|[q1' f1] fs'] eqn:EFS; [exfalso; exact FS3|].
          cbn in FS3. destruct FS3 as (_ & _ & B0 & Bhi & _). unfold FILE_ALLOC in Bhi. lia. }
        (* [comment removed for export] *)
        assert (FIN : forall (x1'' e0' e1' e2' a0' a1' a2' a3' e4' e5' e6' e7' e8' e9' e10' e11' : word),
          evt ssegs ((fun (r : option hptr) (s' : PS) (ms' : machine_state) =>
                       exists a0v m', hpost_regs ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
                         /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
                         /\ match r with
                            | None => a0v = Z_to_bv 64 0 /\ GIo K R s' CL FB m' /\ rw_cells ssegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))] /\ 0 <= lc_errno (ps_libc s') < 2^31
                            | Some f => exists Af, a0v = Z_to_bv 64 Af /\ GIo K R s' CL ((f, Af, FILE_BLOCK) :: FB) m'
                            end)
                     (Some q) (set_libc (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) sM))
            (MS (mkR x1'' (Z_to_bv 64 (bv_unsigned sp + -96)) gp (rc_tp R) e0' e1' e2' (Z_to_bv 64 A) (Z_to_bv 64 fd)
                     a0' a1' a2' a3' e4' e5' e6' e7' (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 e8' e9' e10' e11')
                F (Z_to_bv 64 0x1b37c) fc None m4 (seg_rom ssegs))).
        { intros.
          eapply evt_mono.
          { eapply (fopen_S7 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (hd := hd_addr FB) (m2 := m3) (fl := if mode_m0 md =? 114 then 8 else 4) (MODE := MODE) (md := md) (slack := slack);
              first [exact FC4 | exact BLK4 | exact FRO4 | exact FRI4 | exact SSP4 | exact THR4 | exact NL4 | exact OL4 | exact OH4 | exact HDF | exact MU4 | exact WM4 | exact ST4 | exact MI4
                    | exact MDR | exact NONUL | exact PAD | exact M0 | exact NOPLUS | exact NOE | exact HFD | (keep_hyps CEILV sp R lo NAME MODE name md slack A LOB LOR SPW3 SPM SP47 TPLO A1 A5 A4 hptr FB HDR; lia)
                    | unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps CEILV hptr sp R FB lo NAME MODE name md slack A x Hx; lia)
                    | match goal with |- ?g => idtac "S7 side:" g end ]. }
          cbv beta. intros ms7 PO7.
          destruct PO7 as (f0' & f1' & f2' & g1 & g2 & g3 & g4 & g5 & g6 & g7 & f3' & f4' & f5' & f6' & m7 & -> & FC7 & BLK7 & OL7 & OH7 & OLDP7 & SSP7 & MU7 & WM7 & MI7 & ST7).
          eexists _, m7. split; [unfold hpost_regs; repeat eexists; reflexivity|].
          split; [destruct sM as [xh xl xo xt]; cbn [ps_outfile set_libc] in OF3 |- *; exact OF3|].
          split; [exact MI7|]. split; [exact ST7|].
          assert (HWX : exists W', munch W' m3 m7
                    /\ Forall (fun iv : Z * Z => (CEILZ <= fst iv /\ snd iv <= bv_unsigned sp) \/ (fst iv = A /\ snd iv = A + 232) \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                                                \/ (FB <> [] /\ fst iv = hd_addr FB + 104 /\ snd iv = hd_addr FB + 112)) W').
          { revert MU7. destruct (Z.eqb_spec (hd_addr FB) 0) as [E|NE]; intros MU7.
            - exists [(lo, bv_unsigned sp); (A, A + 232); (A_OFL_HEAD, A_OFL_HEAD + 8)]. split.
              + eapply munch_weaken; [| exact MU7]. unfold sub_fp. intros x Ox. cbn [outside] in Ox |- *. destruct Ox as (O1 & O2 & O3 & _).
                split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [lia| exact I].
              + apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; split; reflexivity|].
                apply Forall_cons; [right; right; left; split; reflexivity| apply Forall_nil].
            - exists [(lo, bv_unsigned sp); (A, A + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd_addr FB + 104, hd_addr FB + 112)]. split.
              + exact MU7.
              + apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; split; reflexivity|].
                apply Forall_cons; [right; right; left; split; reflexivity|]. apply Forall_cons; [| apply Forall_nil].
                right; right; right. cbn [fst snd]. split; [| split; reflexivity]. intros EFB. apply NE. rewrite EFB. reflexivity. }
          destruct HWX as (W' & MU7' & HW').
          assert (EFL7 : (if mode_m0 md =? 114 then 8 else 4) = (if wr then 4 else 8)) by (rewrite M0W; destruct wr; reflexivity).
          destruct (fopen_finish R sM CL FB m3 m7 W' q A fd wr _ (skipn 232 junk) (bv_unsigned sp) G3 MU7' WM7 HW' ltac:(lia) SPM FC7 BLK7 OL7 OH7 OLDP7 EFL7 HFD) as [G7 AG7].
          split; [eapply agrees_on_trans; [exact AG03| exact AG7]|].
          exists A. split; [reflexivity| exact G7]. }
        destruct wr.
        * (* [comment removed for export] *)
          assert (EFL : (mode_m0 md =? 114) = false) by (rewrite M0W; reflexivity). rewrite EFL in FC4 |- *.
          apply implM_bind_assoc. apply implM_sysk.
          eapply evt_cut. { eapply fopen_br_w with (fd := fd). lia. }
          cbv beta. intros ms5 ->.
          step_ecall. split. { at_node_solve__p1. }
          intros rsp a Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
          destruct a as [e'|v]; [| destruct Hdec as (_ & X & _); discriminate X]. destruct Hdec as [-> HE'].
          cbn beta iota. apply implM_retb. apply implM_upd_lc. apply implM_ret. unfold efferr, eff0. sys_nret.
          eapply evt_cut. { eapply (fopen_ioctl_ret gp (rc_tp R) F fc 0 [] []) with (e := e'). exact HE'. }
          cbv beta. intros ms6 ->. apply FIN.
        * (* [comment removed for export] *)
          assert (EFL : (mode_m0 md =? 114) = true) by (rewrite M0W; reflexivity). rewrite EFL in FC4 |- *.
          apply implM_retb. apply implM_upd_lc. apply implM_ret.
          eapply evt_cut. { eapply fopen_br_r. }
          cbv beta. intros ms5 ->. apply FIN.
      + (* [comment removed for export] *)
        destruct RES as (-> & G3 & [EEN ERR3]).
        pose proof G3 as (HH3 & HS3 & HA3 & CT3 & PT3 & CLI3 & CM3 & CE3 & CS3 & Etls3 & TB3 & BOK3 & SPW3).
        pose proof (core_ssp R m3 CLI3) as SSP3.
        apply implM_upd_lc. apply implM_sysk.
        eapply evt_cut. { eapply (fopen_S4 sp gp (rc_tp R) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MODE md slack); [exact FRI3 | exact SSP3 | exact HFD | exact MI3]. }
        cbv beta. intros ms4 PO4. destruct_exs PO4. subst ms4.
        step_ecall. split. { at_node_solve__p2. }
        intros rsp a Hdec. unfold dec_close in Hdec. apply dec_plain_Some in Hdec.
        release_frame FRI3 ST3 (bv_unsigned sp + -32).
        assert (TAILN : forall mm (a0w : word) x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6',
          mm = m3 ->
          evt ssegs ((fun (r : option hptr) (s' : PS) (ms' : machine_state) =>
                       exists a0v m', hpost_regs ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
                         /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
                         /\ match r with
                            | None => a0v = Z_to_bv 64 0 /\ GIo K R s' CL FB m' /\ rw_cells ssegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))] /\ 0 <= lc_errno (ps_libc s') < 2^31
                            | Some f => exists Af, a0v = Z_to_bv 64 Af /\ GIo K R s' CL ((f, Af, FILE_BLOCK) :: FB) m'
                            end)
                     None (set_libc (set_errno_lc ENOMEM (ps_libc sM)) sM))
            (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -32)) gp (rc_tp R) t0' t1' t2' (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                     a0w a1' a2' a3' a4' a5' a6' (Z_to_bv 64 57) sv2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x1b134) fc None mm (seg_rom ssegs))).
        { intros until t6'. intros ->.
          eapply evt_mono. { eapply (fopen_S5 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (W := []) (MODE := MODE) (md := md) (slack := slack); fastfirst (first [ noevar_assumption |exact FRO3| exact ST3| exact MI3| apply munch_refl| apply wmono_refl| lia]). }
          cbv beta. intros ms' PO. destruct PO as (f0' & f1' & f2' & g1 & g2 & g3 & g4 & g5 & g6 & g7 & f3' & f4' & f5' & f6' & -> & _ & _ & MI' & ST').
          eexists _, m3. split; [unfold hpost_regs; repeat eexists; reflexivity|].
          split; [destruct sM as [xh xl xo xt]; cbn [ps_outfile set_libc] in OF3 |- *; exact OF3|].
          split; [exact MI'|]. split; [exact ST'|]. split; [exact AG03|]. split; [reflexivity|].
          split. { pose proof (GIo_stdio_step R sM CL FB m3 m3 [] (bv_unsigned sp) (set_errno_lc ENOMEM (ps_libc sM)) G3 (munch_refl [] m3) (wmono_refl ssegs m3) (Forall_nil _) SPM) as G3'.
                   apply G3'. pose proof (proj1 (KST _ R _ _) HS3) as SR3'. unfold STDIOR in SR3' |- *. destruct (ps_libc sM) as [xso xse xfs xer]; cbn [lc_stdout lc_stderr lc_files set_errno_lc] in SR3' |- *. exact SR3'. }
          cbn [ps_libc set_libc set_errno_lc lc_errno]. unfold ENOMEM. split; [exact ERR3| lia]. }
        destruct a as [e'|v].
        * destruct Hdec as [-> HE']. apply implM_ret. unfold efferr, eff0. sys_nret. apply TAILN. reflexivity.
        * destruct Hdec as (-> & _ & HV). apply implM_ret. unfold eff0. sys_nret. apply TAILN. reflexivity.
  Qed.
  End Sz9.
  Theorem fopen_o_proof : ltac:(let t := eval cbv delta [fopen_o_proof__stmt] in fopen_o_proof__stmt in exact t).
  Proof using EQB HAL HFL HPL KST MALLOC8K. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME MODE name md wr. ltac2:(SecDiet.SzSec.closeP 'fopen_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueFo.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fmodeflags.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_strchr.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.
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

Section WithCeil.
Context {CEILV : CEIL}.
Section GlueFo.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).
  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.spo_facts K KST).
  #[local] Notation GIo_stdio_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.GIo_stdio_step K KST HFL).
  #[local] Notation GIo_stdio_step_same := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.GIo_stdio_step_same K KST HFL).
  #[local] Notation keeps_of_stdio := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.keeps_of_stdio K).
  #[local] Notation client_range_lo := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.client_range_lo K).

  (* [comment removed for export] *)
  Definition malloc_stmt_8k : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo n : Z),
      std_pre_o K sp tp R s CL FB lo 8192 m -> a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
      implM usegs (pmalloc HO n) s
        (fun r s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIo K R s' CL FB m' /\ enomem_at R s' m'
              | Some q => exists A junk, a0v = Z_to_bv 64 A /\ GIo K R s' ((q, A, n) :: CL) FB m'
                          /\ rw_cells usegs m' A [CB (Z.to_nat n) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom usegs)).
  Hypothesis MALLOC8K : malloc_stmt_8k.

  (* [comment removed for export] *)
  Lemma GIo_stdio_step_err : forall R (s : PS) CL FB m m' W SP l' (e' : word),
    GIo K R s CL FB m -> munch W m m' -> wmono usegs m m' ->
    Forall (fun iv => stdio_iv R CL FB SP iv \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160)) W -> SP <= rc_spmain R ->
    rw_cells usegs m' (utp R + -164) [C4 e'] ->
    STDIOR l' FB m' ->
    GIo K R (set_libc l' s) CL FB m'.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros R s CL FB m m' W SP l' e' G MU WM HW HSP ERR SR'.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA].
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold rc_spmain in HSP. unfold stdio_iv, rc_spmain in HW.
    assert (OUT : forall a, 0 <= a < 2^64 ->
              ~ (CEILZ <= a < usp0 R - 48) -> ~ in_block (CL ++ FB) a -> ~ (0x23e20 <= a < 0x240f0) -> ~ (0x54908 <= a < 0x55130) ->
              ~ (utp R - 164 <= a < utp R - 160) -> outside W a).
    { intros a Ha N1 N2 N3 N4 N5. eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd].
      destruct Hiv as [[X|[X|[X|X]]]|X]; cbn [fst snd] in X; try (keep_hyps CEILV R a lo hi N1 X N3 N4 N5; lia).
      intros Hin. apply N2. eapply in_block_of_iv; [exact X| cbn [fst snd]; lia]. }
    assert (BF : forall a, in_block (CL ++ FB) a -> 0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x56000 <= a) /\ (a < utp R - 200 \/ utp R - 200 + 4096 <= a)).
    { intros a Ha. exact (in_block_facts (utp R) (CL ++ FB) a BO Ha). }
    unfold GIo, set_libc. cbn [ps_heap ps_libc ps_outfile ps_tls].
    split.
    { eapply HFL; [exact HH| exact MU| exact WM|].
      apply Forall_forall. intros [lo hi] Hiv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as X. unfold heap_client_iv in *. cbn [fst snd] in *.
      destruct X as [[X|[X|[X|X]]]|X]; [left; lia | right; left; exact X | right; right; left; lia | right; right; left; lia | right; right; right; lia]. }
    split; [apply (proj2 (KST l' R FB m')); exact SR'|].
    split. { eapply HARNR_agree; [| |exact HA]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split. { unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e & A1 & A2 & A3 & A4 & A5 & A6 & Ht); subst z x. exists t, e'.
             assert (AG : agrees_on (fun a => core_tls_fp R a /\ ~ (utp R - 164 <= a < utp R - 160)) m m').
             { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [Hp Hn]. unfold core_tls_fp in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R a TBC Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R a Hp H1; lia)| (keep_hyps CEILV R a TBI Hp; lia)| (keep_hyps CEILV R a TBI Hp; lia)| exact Hn]. }
             Ltac trt AG A := eapply agrees_rw_cells; [exact AG | exact A | intros a Ha; unfold core_tls_fp; sl_lit_sizes_in Ha; cbn in Ha; lia].
             split; [trt AG A1|]. split; [exact ERR|]. split; [trt AG A3|]. split; [trt AG A4|]. split; [trt AG A5|]. split; [trt AG A6| exact Ht]. }
    split. { eapply PCAP_TLS_agree; [| |exact PT]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split. { eapply CORE_LIBC_agree; [| |exact CLI]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split. { eapply CORE_MISC_agree; [| |exact CM]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split. { eapply CORE_EXIT_agree; [| |exact CE]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split. { eapply CORE_STK_agree; [| |exact CS]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia| lia]. }
    split; [exact Etls|]. split; [exact TB|]. split; [exact BOK| exact SPW].
  Qed.

  Definition keeps_of_stdio_err__stmt : Prop := forall R (s : PS) CL FB m m' W SP,
    GIo K R s CL FB m -> munch W m m' -> wmono usegs m m' ->
    Forall (fun iv => (CEILZ <= fst iv /\ snd iv <= SP) \/ iv_in_block FB iv
                      \/ (0x23e20 <= fst iv /\ snd iv <= 0x240f0) \/ (0x54908 <= fst iv /\ snd iv <= 0x55130)
                      \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160)) W ->
    CEILZ <= SP ->
    agrees_on (client_keeps CL SP) m m'.
  Section Sz1.
  Variables R s CL FB m m' W SP : ltac2:(SecDiet.SzSec.tyM 'keeps_of_stdio_err__stmt "vvvvvvvv" @R).
  Lemma keeps_of_stdio_err__body : ltac2:(SecDiet.SzSec.bodyP 'keeps_of_stdio_err__stmt "vvvvvvvv").
  Proof using Type. pin_using tt.
    intros G MU WM HW HSP.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    eapply agrees_on_weaken.
    - eapply (keeps_of_stdio R s CL FB m m' W SP (fun a => utp R - 164 <= a < utp R - 160)); [exact G| exact MU| exact WM| | exact HSP].
      eapply Forall_impl; [| exact HW]. intros iv [X|[X|[X|[X|X]]]]; [left| right; left| right; right; left| right; right; right; left| right; right; right; right]; try exact X.
      intros a Ha. lia.
    - intros a Hk. split; [exact Hk|]. intros Hr. destruct Hk as [Hk|Hk]; [lia|].
      destruct (in_block_facts _ _ a BO1 Hk) as (F1 & F2 & F3 & F4). lia.
  Qed.
  End Sz1.
  Lemma keeps_of_stdio_err : ltac:(let t := eval cbv delta [keeps_of_stdio_err__stmt] in keeps_of_stdio_err__stmt in exact t).
  Proof using Type. intros R s CL FB m m' W SP. ltac2:(SecDiet.SzSec.closeP 'keeps_of_stdio_err__body "vvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition STDIOR_keep__stmt : Prop := forall (l : libc_st hptr) FB (CL : list cblk) R m m' W,
    STDIOR l FB m -> blocks_ok (utp R) (CL ++ FB) -> tls_block_ok_u (utp R - 200) -> munch W m m' -> wmono usegs m m' ->
    Forall (fun iv => CEILZ <= fst iv \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160)) W ->
    STDIOR l FB m'.
  Section Sz2.
  Variables l FB CL R m m' W : ltac2:(SecDiet.SzSec.tyM 'STDIOR_keep__stmt "vvvvvvv" @l).
  Lemma STDIOR_keep__body : ltac2:(SecDiet.SzSec.bodyP 'STDIOR_keep__stmt "vvvvvvv").
  Proof using Type. pin_using tt.
    intros SR BOK TB MU WM HW.
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    unfold tls_block_ok_u in TB. destruct TB as (TBA & TB0 & TBC & TBI).
    eapply (STDIOR_agree l FB m m' (fun a => a < CEILZ /\ ~ (utp R - 200 <= a < utp R - 200 + 4096))); [exact SR| | |].
    - eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [Hc Hn].
      eapply outside_of_Forall; [exact HW|]. intros [lo hi] [X|X]; cbn [fst snd] in *; lia.
    - intros a Ha. unfold S3.GI.TwB.stdio_static in Ha. lia.
    - intros a Ha. destruct (in_block_facts _ _ a BO2 Ha) as (_ & X & _ & Y). lia.
  Qed.
  End Sz2.
  Lemma STDIOR_keep : ltac:(let t := eval cbv delta [STDIOR_keep__stmt] in STDIOR_keep__stmt in exact t).
  Proof using Type. intros l FB CL R m m' W. ltac2:(SecDiet.SzSec.closeP 'STDIOR_keep__body "vvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mode_lit_facts__stmt : Prop := forall wr MODE md, mode_lit wr MODE md ->
    exists slack,
      ro_bytes usegs MODE (md ++ Z_to_bv 8 0 :: slack)
      /\ (0x10000 <= MODE /\ MODE + Z.of_nat (length md) + 1 + Z.of_nat (length slack) <= 0x13000)
      /\ ~ In (Z_to_bv 8 0) md
      /\ (- (MODE + Z.of_nat (length md) + 1)) mod 8 <= Z.of_nat (length slack)
      /\ (mode_m0 md = 114 \/ mode_m0 md = 119)
      /\ mode_m0 md = (if wr then 119 else 114)
      /\ fmodeflags md = (if wr then 577 else 0)
      /\ has_byte 43 md = false /\ has_byte 101 md = false.
  Section Sz3.
  Variables wr MODE md : ltac2:(SecDiet.SzSec.tyM 'mode_lit_facts__stmt "vvv" @wr).
  Lemma mode_lit_facts__body : ltac2:(SecDiet.SzSec.bodyP 'mode_lit_facts__stmt "vvv").
  Proof using Type. pin_using tt.
    intros ML.
 unfold mode_lit, STR_RB in ML. destruct wr.
    - destruct ML as [[-> ->] | [-> ->]].
      + exists [Z_to_bv 8 97; Z_to_bv 8 110; Z_to_bv 8 32; Z_to_bv 8 105].
        split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try lia; try reflexivity. intros [X|[]]. discriminate X. right; reflexivity.
      + exists [Z_to_bv 8 65; Z_to_bv 8 32; Z_to_bv 8 110; Z_to_bv 8 117; Z_to_bv 8 108; Z_to_bv 8 108].
        split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try lia; try reflexivity. intros [X|[X|[]]]; discriminate X. right; reflexivity.
    - destruct ML as [-> ->].
      exists [Z_to_bv 8 109; Z_to_bv 8 97].
      split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try lia; try reflexivity. intros [X|[X|[]]]; discriminate X. left; reflexivity.
  Qed.
  End Sz3.
  Lemma mode_lit_facts : ltac:(let t := eval cbv delta [mode_lit_facts__stmt] in mode_lit_facts__stmt in exact t).
  Proof using Type. intros wr MODE md. ltac2:(SecDiet.SzSec.closeP 'mode_lit_facts__body "vvv"). Qed.

  (* [comment removed for export] *)
  Definition files_R_newhead__stmt : Prop := forall m m' fs (FB : list cblk) A,
    files_R m 0 fs FB ->
    (forall q1 A1 n1 f1 FB', FB = (q1, A1, n1) :: FB' ->
        FILE_R m f1 A1 (A1 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK 0 (hd_addr FB') -> heap_file_inv f1 ->
        FILE_R m' f1 A1 (A1 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK A (hd_addr FB')) ->
    (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) (tl FB) ->
        FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
        FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
    files_R m' A fs FB.
  Section Sz4.
  Variables m m' A : ltac2:(SecDiet.SzSec.tyM 'files_R_newhead__stmt "vvkkv" @m).
  Lemma files_R_newhead__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_newhead__stmt "vvkkv").
  Proof using Type. pin_using tt.
    intros fs FB FS HHD HTL.
    destruct fs as [|[q1 f1] fs]; destruct FB as [|[[q1' A1] n1] FB]; cbn in FS |- *; try exact FS.
    destruct FS as (-> & -> & B0 & Bhi & FR & INV & REST).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
    split; [exact (HHD q1 A1 FILE_ALLOC f1 FB eq_refl FR INV)|]. split; [exact INV|].
    eapply files_R_frame; [exact REST|]. intros q2 A2 n2 f2 pv2 nx2 HIN2. apply (HTL q2 A2 n2 f2 pv2 nx2). exact HIN2.
  Qed.
  End Sz4.
  Lemma files_R_newhead : ltac:(let t := eval cbv delta [files_R_newhead__stmt] in files_R_newhead__stmt in exact t).
  Proof using Type. intros m m' fs FB A. ltac2:(SecDiet.SzSec.closeP 'files_R_newhead__body "vvkkv"). Qed.

  (* [comment removed for export] *)
  Lemma fcells_split_prev : forall flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
    fcells flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl =
    [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 re); C8 (Z_to_bv 64 cf);
     C8 (Z_to_bv 64 we); C8 (Z_to_bv 64 wp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wb);
     C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 wf); C8 (Z_to_bv 64 sf); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bs)]
    ++ [C8 (Z_to_bv 64 pv)]
    ++ [C8 (Z_to_bv 64 nx); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
        C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0); CB 80 tl].
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Lemma FILE_R_prev_cell : forall m f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx -> rw_cells usegs m (Fp + 104) [C8 (Z_to_bv 64 pv)].
  Proof using Type. pin_using tt.
    intros m f Fp BA cf rf sf pv nx (flags & mode & rp & tail & bufbytes & FC & _).
    rewrite fcells_split_prev in FC. apply (proj1 (rw_cells_app usegs m Fp _ _)) in FC as [_ FC].
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in FC as [FC _]. cbn [cells_size csize Nat.add] in FC.
    replace (Fp + Z.of_nat 104) with (Fp + 104) in FC by lia. exact FC.
  Qed.

  (* [comment removed for export] *)
  Definition FILE_R_set_prev__stmt : Prop := forall m m' f Fp BA cf rf sf pv pv' nx W,
    FILE_R m f Fp BA cf rf sf pv nx ->
    munch W m m' -> wmono usegs m m' ->
    Forall (fun iv : Z * Z => (Fp + 232 <= fst iv \/ snd iv <= Fp) \/ (fst iv = Fp + 104 /\ snd iv = Fp + 112)) W ->
    Forall (fun iv : Z * Z => BA + f_bufsize f <= fst iv \/ snd iv <= BA) W ->
    0 <= f_bufsize f ->
    rw_cells usegs m' (Fp + 104) [C8 (Z_to_bv 64 pv')] ->
    FILE_R m' f Fp BA cf rf sf pv' nx.
  Section Sz7.
  Variables m m' f Fp BA cf rf sf pv pv' nx W : ltac2:(SecDiet.SzSec.tyM 'FILE_R_set_prev__stmt "vvvvvvvvvvvv" @m).
  Lemma FILE_R_set_prev__body : ltac2:(SecDiet.SzSec.bodyP 'FILE_R_set_prev__stmt "vvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FR MU WM D1 D2 BS PC.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - rewrite fcells_split_prev in FC |- *.
      apply (proj1 (rw_cells_app usegs m Fp _ _)) in FC as [FCa FC]. apply (proj1 (rw_cells_app usegs m _ [_] _)) in FC as [_ FCb].
      cbn [cells_size csize Nat.add] in FCa, FCb |- *.
      apply (proj2 (rw_cells_app usegs m' Fp _ _)). split.
      + eapply rw_cells_transport; [exact FCa| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
        apply disjoint_from_Forall. eapply Forall_impl; [| exact D1]. intros [lo hi]; cbn; lia.
      + apply (proj2 (rw_cells_app usegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
        * replace (Fp + Z.of_nat 104) with (Fp + 104) by lia. exact PC.
        * eapply rw_cells_transport; [exact FCb| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
          apply disjoint_from_Forall. eapply Forall_impl; [| exact D1]. intros [lo hi]; cbn; lia.
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      apply disjoint_from_Forall. eapply Forall_impl; [| exact D2]. intros [lo hi]; cbn; lia.
  Qed.
  End Sz7.
  Lemma FILE_R_set_prev : ltac:(let t := eval cbv delta [FILE_R_set_prev__stmt] in FILE_R_set_prev__stmt in exact t).
  Proof using Type. intros m m' f Fp BA cf rf sf pv pv' nx W. ltac2:(SecDiet.SzSec.closeP 'FILE_R_set_prev__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma HARNR_cons : forall (o : option hptr) (b : cblk) FB m, HARNR o FB m -> HARNR o (b :: FB) m.
  Proof using Type. pin_using tt.
    intros o b FB m (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    destruct o as [q'|]; [|exact H3]. destruct H3 as (A' & HIn & HC). exists A'. split; [right; exact HIn| exact HC].
  Qed.

  (* [comment removed for export] *)
  Lemma fopen_finish : forall R (sM : PS) (CL FB : list cblk) m3 m7 W q A fd (wr : bool) (fl : Z) junk2 SP,
    GIo K R sM ((q, A, FILE_ALLOC) :: CL) FB m3 ->
    munch W m3 m7 -> wmono usegs m3 m7 ->
    Forall (fun iv : Z * Z => (CEILZ <= fst iv /\ snd iv <= SP) \/ (fst iv = A /\ snd iv = A + 232) \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                              \/ (FB <> [] /\ fst iv = hd_addr FB + 104 /\ snd iv = hd_addr FB + 112)) W ->
    CEILZ <= SP -> SP <= rc_spmain R ->
    rw_cells usegs m7 A (file_cells (Z_to_bv 64 fl) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ F_STDIO_WRITE F_STDIO_SEEK (A + 240) 1024 0 (hd_addr FB) fd
                          (Z_to_bv 64 0) 4294967295 (repeat (Z_to_bv 8 0) 80)) ->
    rw_cells usegs m7 (A + 232) [CB 1032 junk2] ->
    rw_cells usegs m7 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells usegs m7 A_OFL_HEAD [C8 (Z_to_bv 64 A)] ->
    (hd_addr FB <> 0 -> rw_cells usegs m7 (hd_addr FB + 104) [C8 (Z_to_bv 64 A)]) ->
    fl = (if wr then 4 else 8) -> 3 <= fd <= 4096 ->
    GIo K R (set_libc (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) sM) CL ((q, A, FILE_ALLOC) :: FB) m7
    /\ agrees_on (client_keeps CL SP) m3 m7.
  Proof using EQB HAL HFL HPL KST. pin_using (fun (EQB HAL HFL HPL KST : unit) => tt).
    intros R sM CL FB m3 m7 W q A fd wr fl junk2 SP G MU WM HW CSP HSP FC7 BLK7 OL7 OH7 OLDP7 -> HFD.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA].
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold rc_spmain in HSP.
    apply (proj1 (KST _ R _ _)) in HS as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; left; left; reflexivity)) as (BK1 & BK2 & BK3 & BK4 & BK5 & BK6).
    unfold cb_addr, cb_size, FILE_ALLOC in BK1, BK2, BK3, BK4, BK5, BK6. cbn [fst snd] in BK1, BK2, BK3, BK4, BK5, BK6.
    pose proof (blocks_apart_app_inv _ _ BA) as (BAc & BA2 & BAX). cbn [blocks_apart] in BAc. destruct BAc as [APc BAc'].
    assert (APf : Forall (apart (q, A, FILE_ALLOC)) FB).
    { apply Forall_forall. intros b Hb. apply (BAX (q, A, FILE_ALLOC) b); [left; reflexivity| exact Hb]. }
    pose proof BO as BO'. apply Forall_cons_iff in BO' as [_ BO']. apply Forall_app in BO' as [BOCL BOFB].
    (* [comment removed for export] *)
    assert (HDB : forall q1 A1' n1 FB', FB = (q1, A1', n1) :: FB' ->
              n1 = FILE_ALLOC /\ 0 < A1' /\ A1' + 1264 <= CEILZ /\ (A1' + 1264 <= 0x10000 \/ 0x56000 <= A1')
              /\ (A1' + 1264 <= utp R - 200 \/ utp R - 200 + 4096 <= A1')
              /\ (A + 1264 <= A1' \/ A1' + 1264 <= A) /\ Forall (apart (q1, A1', n1)) FB').
    { intros q1 A1' n1 FB' E. rewrite E in FS, BOFB, APf, BA2.
      destruct (lc_files (ps_libc sM)) as [|[q1' f1] fs']; [exfalso; exact FS|].
      cbn in FS. destruct FS as (Eq1 & En1 & B0 & Bhi & FR1h & INV1 & REST1). subst n1.
      apply Forall_cons_iff in BOFB as [(K1 & K2 & K3 & K4 & K5 & K6) _]. unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3, K4, K5, K6. cbn [fst snd] in K1, K2, K3, K4, K5, K6.
      apply Forall_cons_iff in APf as [AP _]. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP.
      cbn [blocks_apart] in BA2. destruct BA2 as [APh _].
      unfold FILE_ALLOC in *. repeat split; try (keep_hyps CEILV R A A1' B0 K4 K5 K6 AP; lia). exact APh. }
    (* [comment removed for export] *)
    set (P37 := fun a : Z => ~ (CEILZ <= a < SP) /\ ~ (A <= a < A + 232) /\ ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8)
                             /\ ~ (FB <> [] /\ hd_addr FB + 104 <= a < hd_addr FB + 112)).
    assert (AG : agrees_on P37 m3 m7).
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha (N1 & N2 & N3 & N4).
      eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd] in Hiv |- *.
      destruct Hiv as [X|[X|[X|(Xne & X1 & X2)]]]; [(keep_hyps CEILV R A SP a lo' hi' N1 X; lia)| (keep_hyps CEILV R A SP a lo' hi' N2 X; lia)| (keep_hyps CEILV R A SP a lo' hi' N3 X; lia)|]. intros Hin. apply N4. split; [exact Xne| lia]. }
    (* [comment removed for export] *)
    assert (OUT : forall a, 0 <= a < 2^64 ->
              ~ (CEILZ <= a < usp0 R - 48) -> ~ in_block (((q, A, FILE_ALLOC) :: CL) ++ FB) a -> ~ (0x23e20 <= a < 0x240f0) -> ~ (0x54908 <= a < 0x55130) -> outside W a).
    { intros a Ha N1 N2 N3 N4. eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd].
      destruct Hiv as [X|[X|[X|(Xne & X1 & X2)]]]; cbn [fst snd] in *.
      - (keep_hyps CEILV R A SP a lo' hi' HSP N1 X; lia).
      - intros Hin. apply N2. apply (proj2 (in_block_In _ _)). exists (q, A, FILE_ALLOC).
        split; [apply in_or_app; left; left; reflexivity| unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
      - unfold A_OFL_HEAD in X. lia.
      - intros Hin. apply N2. destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
        destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _). apply (proj2 (in_block_In _ _)). exists (q1, A1', n1).
        split; [apply in_or_app; right; left; reflexivity| unfold cb_addr, cb_size; cbn [fst snd]; subst n1; unfold FILE_ALLOC; lia]. }
    assert (BF : forall a, in_block (((q, A, FILE_ALLOC) :: CL) ++ FB) a -> 0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x56000 <= a) /\ (a < utp R - 200 \/ utp R - 200 + 4096 <= a)).
    { intros a Ha. exact (in_block_facts (utp R) _ a BO Ha). }
    (* [comment removed for export] *)
    assert (FBn : forall q2 A2 n2, In (q2, A2, n2) FB -> n2 = FILE_ALLOC /\ 0 < A2).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m3 0 _ FB q2 A2 n2 FS ND HIN) as (f & pv & nx & _ & _ & En & B0 & _). split; [exact En| exact B0]. }
    (* [comment removed for export] *)
    assert (HSt : forall a, S3.GI.TwB.stdio_static a -> ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8) -> P37 a).
    { intros a Hs Hn. unfold S3.GI.TwB.stdio_static, A_OFL_HEAD in *. subst P37. cbn beta.
      split; [lia|]. split; [lia|]. split; [exact Hn|].
      intros (Xne & Xr). destruct FB as [|[[q1 A1'] n1] FB']; [exact (Xne eq_refl)|]. cbn [hd_addr] in Xr.
      destruct (HDB q1 A1' n1 FB' eq_refl) as (_ & _ & _ & K4 & _). (keep_hyps CEILV R A1' A a Hs Xr K4; lia). }
    (* [comment removed for export] *)
    assert (HBl : forall q2 A2 n2 a, In (q2, A2, n2) FB -> A2 <= a < A2 + 1264 -> ~ (A2 = hd_addr FB /\ A2 + 104 <= a < A2 + 112) -> P37 a).
    { intros q2 A2 n2 a HIN Ha Hn. destruct (FBn _ _ _ HIN) as [-> B0].
      pose proof (proj1 (Forall_forall _ _) BOFB _ HIN) as (K1 & K2 & K3 & K4 & K5 & K6). unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3, K4, K5, K6. cbn [fst snd] in K1, K2, K3, K4, K5, K6.
      pose proof (proj1 (Forall_forall _ _) APf _ HIN) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP.
      subst P37. cbn beta. unfold A_OFL_HEAD. split; [lia|]. split; [(keep_hyps CEILV hptr R FB A A2 a Ha AP; lia)|]. split; [(keep_hyps CEILV hptr R FB A A2 a Ha K5; lia)|].
      intros (Xne & Xr). destruct FB as [|[[q1 A1'] n1] FB']; [exact (Xne eq_refl)|]. cbn [hd_addr] in Xr, Hn.
      destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _ & _ & _ & _ & _ & APh).
      destruct HIN as [E|HIN].
      - injection E as <- <- _. apply Hn. split; [reflexivity| lia].
      - pose proof (proj1 (Forall_forall _ _) APh _ HIN) as AP2. unfold apart, cb_addr, cb_size in AP2. cbn [fst snd] in AP2. subst n1. unfold FILE_ALLOC in AP2. (keep_hyps CEILV R A1' A A2 a Ha Xr AP2; lia). }
    (* [comment removed for export] *)
    assert (SR7 : STDIOR (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) ((q, A, FILE_ALLOC) :: FB) m7).
    { unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files hd_addr].
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED in *.
      Ltac tra7 AG HSt X := eapply agrees_rw_cells; [exact AG | exact X | intros a Ha; cbn in Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]].
      split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SEbs; intros a Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]. }
      split; [tra7 AG HSt U1|]. split; [tra7 AG HSt U2|]. split; [tra7 AG HSt U3|]. split; [exact OL7|]. split; [exact OH7|].
      split.
      - cbn [files_R]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [unfold FILE_ALLOC; lia|].
        split.
        { (* [comment removed for export] *)
          exists (Z_to_bv 64 (if wr then 4 else 8)), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), (firstn 1024 (skipn 8 junk2)).
          cbn [f_rbuf f_wbuf f_wactive f_bufsize f_fd f_nord f_nowr f_eof f_stdoutw f_lbf_nl fdopen_file wfn_of lbf_of zlength length Z.of_nat Z.add].
          split. { unfold fcells, FILE_BUF_OFF, BUFSIZ. exact FC7. }
          split. { unfold flags_ok. cbn [f_nord f_nowr f_eof f_chan]. unfold F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM. destruct wr; rewrite unsigned_lit by lia; cbn; repeat split; reflexivity. }
          split. { pose proof (rw_cells_split_CB usegs m7 (A + 232) [] 1032 junk2 [] [8%nat; 1024%nat] BLK7 eq_refl) as B2.
                   cbn [app mk_CB_cells] in B2. apply rw_cells_split2 in B2 as [_ B2]. cbn [csize] in B2.
                   unfold FILE_BUF_OFF, BUFSIZ. replace (A + 232 + Z.of_nat 8) with (A + 240) in B2 by lia. exact B2. }
          split; [reflexivity|]. split; [intros _; reflexivity|]. split; [unfold BUFSIZ, zlength; cbn; lia|].
          split; [intros X; exfalso; exact (X eq_refl)|]. fastfirst (first [ noevar_assumption |split; [lia|]; split; [unfold zlength; cbn; lia| reflexivity] | unfold zlength; cbn; lia]). }
        split.
        { unfold heap_file_inv. cbn. destruct wr; cbn.
          all: split; [reflexivity|]; split; [lia|]; split; [reflexivity|]; split; [reflexivity|].
          all: split; [intros X; first [discriminate X | split; reflexivity] |]; split; [intros X; first [discriminate X | reflexivity]| apply Forall_nil]. }
        (* [comment removed for export] *)
        eapply files_R_newhead; [exact FS| |].
        + intros q1 A1' n1 f1 FB' E FR1 INV1.
          destruct (HDB q1 A1' n1 FB' E) as (En1 & B01 & KC & KS & KT & AP1 & APh).
          pose proof INV1 as (_ & _ & BS1 & _).
          eapply (FILE_R_set_prev m3 m7 f1 A1' _ _ _ _ 0 A (hd_addr FB') W); [exact FR1| exact MU| exact WM| | | rewrite BS1; unfold BUFSIZ; lia|].
          * eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in *.
            destruct X as [X|[X|[X|(Xne & X1 & X2)]]]; [left; (keep_hyps CEILV R A SP A1' lo' hi' KC X; lia)| left; (keep_hyps CEILV R A A1' lo' hi' AP1 X; lia)| left; unfold A_OFL_HEAD in X; (keep_hyps CEILV R A A1' lo' hi' KS X; lia)| right]. rewrite E in X1, X2. cbn [hd_addr] in X1, X2. lia.
          * rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in *.
            destruct X as [X|[X|[X|(Xne & X1 & X2)]]]; [(keep_hyps CEILV R A SP A1' lo' hi' KC X; lia)| (keep_hyps CEILV R A A1' lo' hi' AP1 X; lia)| unfold A_OFL_HEAD in X; (keep_hyps CEILV R A A1' lo' hi' KS X; lia)|]. rewrite E in X1, X2. cbn [hd_addr] in X1, X2. lia.
          * rewrite E in OLDP7. cbn [hd_addr] in OLDP7. apply OLDP7. lia.
        + intros q2 A2 n2 f2 pv2 nx2 HIN2 FR2 INV2.
          assert (HIN2' : In (q2, A2, n2) FB) by (destruct FB as [|b FB']; [exact HIN2| right; exact HIN2]).
          pose proof INV2 as (_ & _ & BS2 & _).
          assert (NH : A2 <> hd_addr FB).
          { destruct FB as [|[[q1 A1'] n1] FB']; [exact (False_ind _ HIN2)|]. cbn [hd_addr tl] in HIN2 |- *.
            destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _ & _ & _ & _ & _ & APh).
            pose proof (proj1 (Forall_forall _ _) APh _ HIN2) as AP2. unfold apart, cb_addr, cb_size in AP2. cbn [fst snd] in AP2.
            destruct (FBn _ _ _ HIN2') as [-> _]. subst n1. unfold FILE_ALLOC in AP2. lia. }
          eapply FILE_R_agree; [exact FR2| exact AG| |].
          * intros a Ha. eapply (HBl q2 A2 n2 a HIN2'); [lia|]. intros [X _]. exact (NH X).
          * rewrite BS2. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HBl q2 A2 n2 a HIN2'); [lia|]. intros [X _]. exact (NH X).
      - (* [comment removed for export] *)
        cbn [map fst]. apply List.NoDup_cons; [| exact ND].
        intros HIn. rewrite <- (files_R_toks m3 0 _ FB FS) in HIn. apply in_map_iff in HIn as ([[qb Ab] nb] & Eb & HbIn). cbn in Eb. subst qb.
        pose proof (HAL _ _ _ _ (q, A, FILE_ALLOC) HH ltac:(apply in_or_app; left; left; reflexivity)) as E1.
        pose proof (HAL _ _ _ _ (q, Ab, nb) HH ltac:(apply in_or_app; right; exact HbIn)) as E2.
        cbn [cb_tok cb_addr fst snd] in E1, E2.
        pose proof (proj1 (Forall_forall _ _) APf _ HbIn) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP.
        destruct (FBn _ _ _ HbIn) as [-> _]. unfold FILE_ALLOC in AP. lia. }
    split.
    - (* [comment removed for export] *)
      unfold GIo, set_libc. cbn [ps_heap ps_libc ps_outfile ps_tls].
      split.
      { eapply HPL; [| apply Permutation.Permutation_middle].
        eapply HFL; [exact HH| exact MU| exact WM|].
        apply Forall_forall. intros [lo' hi'] Hiv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as X. unfold heap_client_iv. cbn [fst snd] in *.
        destruct X as [X|[X|[X|(Xne & X1 & X2)]]].
        + left; lia.
        + right; left. unfold iv_in_block. apply Exists_exists. exists (q, A, FILE_ALLOC).
          split; [first [apply in_or_app; left; left; reflexivity | left; reflexivity] | unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
        + right; right; left. unfold A_OFL_HEAD in X. lia.
        + right; left. destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
          destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _). unfold iv_in_block. apply Exists_exists. exists (q1, A1', n1).
          split; [first [apply in_or_app; right; left; reflexivity | right; apply in_or_app; right; left; reflexivity] | unfold cb_addr, cb_size; cbn [fst snd]; subst n1; unfold FILE_ALLOC; lia]. }
      split; [apply (proj2 (KST _ R _ m7)); exact SR7|].
      split. { apply HARNR_cons. eapply HARNR_agree; [| |exact HA]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split. { eapply CORE_TLS_agree; [| |exact CT]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| clear - Hp TBC; (keep_hyps CEILV R a TBC Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R A a Hp H1; lia)| (keep_hyps CEILV R A a TBI Hp; lia)| (keep_hyps CEILV R A a TBI Hp; lia)]. }
      split. { eapply PCAP_TLS_agree; [| |exact PT]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split. { eapply CORE_LIBC_agree; [| |exact CLI]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R A a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R A a Hp H1; lia)| (keep_hyps CEILV R A a Hp; lia)| (keep_hyps CEILV R A a Hp; lia)]. }
      split. { eapply CORE_MISC_agree; [| |exact CM]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R A a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R A a Hp H1; lia)| (keep_hyps CEILV R A a Hp; lia)| (keep_hyps CEILV R A a Hp; lia)]. }
      split. { eapply CORE_EXIT_agree; [| |exact CE]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R A a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R A a Hp H1; lia)| (keep_hyps CEILV R A a Hp; lia)| (keep_hyps CEILV R A a Hp; lia)]. }
      split. { eapply CORE_STK_agree; [| |exact CS]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split; [exact Etls|]. split; [exact TB|]. split; [| exact SPW].
      eapply blocks_ok_perm; [apply Permutation.Permutation_middle| exact BOK].
    - (* [comment removed for export] *)
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hk.
      eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd].
      destruct Hk as [Hk|Hk].
      + destruct Hiv as [X|[X|[X|(Xne & X1 & X2)]]]; cbn [fst snd] in *; [lia| lia| unfold A_OFL_HEAD in X; lia|].
        destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
        destruct (HDB q1 A1' n1 FB' eq_refl) as (_ & _ & KC & _). lia.
      + pose proof (in_block_facts (utp R) CL a BOCL Hk) as (F1 & F2 & F3 & F4).
        apply in_block_In in Hk as ([[qb Ab] nb] & HbIn & Hb). unfold cb_addr, cb_size in Hb. cbn [fst snd] in Hb.
        destruct Hiv as [X|[X|[X|(Xne & X1 & X2)]]]; cbn [fst snd].
        * cbn [fst snd] in X. lia.
        * cbn [fst snd] in X. pose proof (proj1 (Forall_forall _ _) APc _ HbIn) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. (keep_hyps CEILV R A a Ab nb lo' hi' Hb X AP; lia).
        * cbn [fst snd] in X. unfold A_OFL_HEAD in X. lia.
        * cbn [fst snd] in X1, X2. destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
          destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _).
          pose proof (BAX (qb, Ab, nb) (q1, A1', n1) ltac:(right; exact HbIn) ltac:(left; reflexivity)) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. subst n1. unfold FILE_ALLOC in AP. (keep_hyps CEILV R A1' A a Ab nb lo' hi' Hb X1 X2 AP; lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fopen_o_proof__stmt : Prop := fopen_stmt_o HO K.
  Section Sz9.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME MODE name md wr : ltac2:(SecDiet.SzSec.tyM 'fopen_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fopen_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB HAL HFL HPL KST MALLOC8K. pin_using (fun (EQB HAL HFL HPL KST MALLOC8K : unit) => tt).
 intros SPO -> -> HNAME NNUL NLEN NOK NCR HMODE MLIT.   (* [comment removed for export] *)
 (* [comment removed for export] *)
 assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct (mode_lit_facts wr MODE md MLIT) as (slack & ROMD & MDR & NONUL & PAD & M0 & M0W & FMV & NOPLUS & NOE).
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    assert (TPR : utp R + -200 = 0x34190) by (unfold utp in *; lia).
    assert (TPLO : utp R + -160 <= lo) by (unfold utp, rc_lo in *; lia).
    assert (TP200 : 200 <= utp R) by (unfold utp in *; lia).
    unfold utp in TPR, TPLO, TP200.
    (* [comment removed for export] *)
    assert (NSEP : NAME + (Z.of_nat (length name) + 1) <= lo \/ bv_unsigned sp <= NAME).
    { destruct NCR as [NCR | NCR].
      - destruct (client_range_lo R s CL FB m (bv_unsigned sp) NAME (Z.of_nat (length name) + 1) lo G NCR ltac:(lia) LOR ltac:(lia)) as (_ & C2 & _). exact C2.
      - left. lia. }
    pose proof CT as (tlst & errv & _ & ERR & _).
    unfold s_fopen, Stdio.fopen.
    apply implM_sysk.
    eapply evt_cut.
    { eapply (fopen_S1 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack);
        first [exact ROMD | exact ST | exact MI | exact MDR | exact NONUL | exact PAD | exact M0 | exact NOPLUS | exact NOE | (keep_hyps CEILV sp R lo NAME MODE name md slack LOB LOR SPW SPM SP47 NB TPR TPLO; lia)
              | match goal with |- ?g => idtac "S1 side:" g end]. }
    cbv beta. intros ms1 PO. destruct PO as (x1 & u0 & u1 & u2 & b4 & b5 & b6 & u3 & u4 & u5 & u6 & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (HNAME1 : bytes_at usegs m1 NAME (name ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact HNAME| exact MU1|]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
    assert (ERR1 : rw_cells usegs m1 (bv_unsigned (rc_tp R) + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. lia. }
    destruct SSP as [GOT GUARD].
    assert (SSP1 : ssp_cells m1 (rc_canary R)).
    { split; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1| unfold got_ssp, ssp_guard; cbn; lia]). }
    step_ecall. split.
    { destruct wr; cbn [open_name_ok] in NOK; rewrite FMV; at_node_solve__p3.
      all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
      all: first [exact NNUL | exact NOK | exact (proj1 NOK) | exact (proj2 NOK)   (* [comment removed for export] *)
                 | rewrite unsigned_lit by lia; exact HNAME1 | vm_compute; reflexivity
                 | match goal with |- ?g => idtac "ATNODE:" g end]. }
    intros rsp a Hdec.
    assert (HD : match a with SErr e => rsp = efferr e /\ 1 <= e <= 4095 | SVal v => rsp = eff0 (Z_to_bv 64 v) /\ 3 <= v <= 4096 end).
    { assert (Hdec' : dec_open rsp = Some a) by (destruct wr; exact Hdec).
      unfold dec_open in Hdec'. apply dec_plain_Some in Hdec'. destruct a as [e|v]; [exact Hdec'|].
      destruct Hdec' as (E & OK & R'). split; [exact E|]. apply andb_prop in OK. destruct OK as [O1 O2]. apply Z.leb_le in O1. apply Z.leb_le in O2. lia. }
    clear Hdec. destruct a as [e|fd].
    - (* [comment removed for export] *)
      destruct HD as [-> HE].
      apply implM_upd_lc. apply implM_ret. unfold efferr, eff0. sys_nret.
      eapply evt_mono.
      { eapply (fopen_S2_fail ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack);
          first [exact FR1 | exact ERR1 | exact HE | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact M0 | exact MDR | exact NONUL | exact PAD | exact NOPLUS | exact NOE | exact ROMD | lia
                | match goal with |- ?g => idtac "S2F side:" g end]. }
      cbv beta. intros ms' PO. destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
      eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|].
      split. { eapply (keeps_of_stdio_err R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU'| exact WM'| | lia].
               apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; right; right; cbn; unfold utp; lia| apply Forall_nil]. }
      split; [reflexivity|].
      split. { eapply (GIo_stdio_step_err R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU'| exact WM'| | exact SPM| unfold utp; exact ERR'|].
               - apply Forall_cons; [left; left; cbn; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil].
               - cbn [ps_libc set_libc set_errno_lc]. eapply (STDIOR_keep _ FB CL R m m'); [exact SR| exact BOK| exact TB| exact MU'| exact WM'|].
                 apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil]. }
      cbn [ps_libc set_libc set_errno_lc lc_errno]. unfold utp. split; [exact ERR'| lia].
    - (* [comment removed for export] *)
      destruct HD as [-> HFD].
      eapply implM_evt.
      { unfold eff0. sys_nret. eapply (fopen_S2_ok ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack);
            first [exact ROMD | exact FR1 | exact ERR1 | exact SSP1 | exact HFD | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact MDR | exact NONUL | exact PAD | exact M0 | exact NOPLUS | exact NOE | (keep_hyps CEILV sp R lo NAME MODE name md slack LOB LOR SPW SPM SP47 NB TPR TPLO TP200; lia)
                  | destruct wr; rewrite FMV; [right | left]; reflexivity
                  | match goal with |- ?g => idtac "S2OK side:" g end ]. }
      cbv beta. intros ms2 PO. destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & sv2 & j0 & m2 & -> & FRO2 & FRI2 & ERR2 & SSP2 & MU2 & WM2 & MI2 & ST2).
      name_sp sp (-96).
      assert (TLSLO : bv_unsigned (rc_tp R) + -160 <= lo) by exact TPLO.
      eapply implM_bind.
      { pose proof MALLOC8K as MK. unfold malloc_stmt_8k in MK. eapply MK; [| reflexivity | unfold FILE_ALLOC; lia].
        split.
        { pose proof (GIo_stdio_step_err R s CL FB m m2 _ (bv_unsigned sp) (ps_libc s) errv G MU2 WM2) as G2.
          destruct s as [sh sl so st']; cbn [set_libc ps_libc] in G2 |- *. apply G2.
          - apply Forall_cons; [left; left; cbn; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil].
          - exact SPM.
          - unfold utp. exact ERR2.
          - eapply (STDIOR_keep _ FB CL R m m2); [exact SR| exact BOK| exact TB| exact MU2| exact WM2|].
            apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil]. }
        split; [rewrite Hsp; exact ST2|]. split; [exact LOR|]. split; [rewrite Hsp; lia|]. split; [rewrite Hsp; lia|].
        split; [exact MI2|]. split; [reflexivity|]. rewrite Hsp. apply aln16_add; [exact AL| reflexivity]. }
      cbv beta. intros po sM ms3 PO3.
      destruct PO3 as (a0v & m3 & REGS & OF3 & MI3 & ST3 & AG3 & RES).
      unfold hpost_regs in REGS. destruct REGS as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & ->).
      rewrite Hsp in ST3, AG3. subst sp0.
      replace (ret_pc (Z_to_bv 64 0x1ba28)) with (Z_to_bv 64 0x1ba28 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FRO3 : rw_cells usegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply keeps_rw_cells_stack; [exact AG3| exact FRO2| lia]).
      assert (FRI3 : rw_cells usegs m3 (bv_unsigned sp + -96) [CB 16 j0; C8 (rc_canary R); C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x1b8e0)])
        by (eapply keeps_rw_cells_stack; [exact AG3| exact FRI2| lia]).
      (* [comment removed for export] *)
      assert (AG03 : agrees_on (client_keeps CL (bv_unsigned sp)) m m3).
      { eapply agrees_on_trans.
        - eapply (keeps_of_stdio_err R s CL FB m m2 _ (bv_unsigned sp)); [exact G| exact MU2| exact WM2| | lia].
          apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; right; right; cbn; unfold utp; lia| apply Forall_nil].
        - eapply client_keeps_weaken; [exact AG3| lia| intros a Ha; exact Ha]. }
      destruct po as [q|].
      + (* [comment removed for export] *)
        destruct RES as (A & junk & -> & G3 & BLK).
        pose proof G3 as (HH3 & HS3 & HA3 & CT3 & PT3 & CLI3 & CM3 & CE3 & CS3 & Etls3 & TB3 & BOK3 & SPW3).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(apply in_or_app; left; left; reflexivity)) as (A1 & A2 & A3 & A4 & A5 & A6).
        unfold cb_addr, cb_size, FILE_ALLOC in A1, A2, A3, A4, A5, A6. cbn [fst snd] in A1, A2, A3, A4, A5, A6.
        pose proof (core_ssp R m3 CLI3) as SSP3.
        apply (proj1 (KST _ R _ _)) in HS3 as SR3.
        eapply implM_evt.
        { eapply (fopen_S6 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (P := A) (MODE := MODE) (md := md) (slack := slack);
            first [exact ROMD | exact BLK | exact FRO3 | exact FRI3 | exact SSP3 | exact HFD | exact ST3 | exact MI3 | exact MDR | exact NONUL | exact PAD | exact M0 | exact NOPLUS | exact NOE | (keep_hyps CEILV sp R lo NAME MODE name md slack A LOB LOR SPW3 SPM SP47 TPLO A1 A5 A4; lia)
                  | match goal with |- ?g => idtac "S6 side:" g end ]. }
        cbv beta. intros ms4 PO4.
        destruct PO4 as (x1' & e0 & e1 & e2 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & m4 & -> & FC4 & BLK4 & FRO4 & (sv2' & j0' & FRI4) & SSP4 & MU4 & WM4 & MI4 & ST4).
        (* [comment removed for export] *)
        pose proof CLI3 as (LC3 & _). unfold libc_cells in LC3.
        apply (proj1 (rw_cells_app usegs m3 _ [_] _)) in LC3 as [_ LC3]. apply (proj1 (rw_cells_app usegs m3 _ [_] _)) in LC3 as [THR3 LC3].
        apply (proj1 (rw_cells_app usegs m3 _ [_] _)) in LC3 as [_ LC3]. apply (proj1 (rw_cells_app usegs m3 _ [_] _)) in LC3 as [NL3 _].
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in THR3, NL3.
        assert (THR4 : rw_cells usegs m4 0x544e9 [C1 (Z_to_bv 8 0)]) by (eapply rw_cells_transport; [exact THR3| exact MU4| exact WM4| cbn; (keep_hyps CEILV sp R lo NAME MODE name md slack A LOR SPW3 A5; lia)]).
        assert (NL4 : rw_cells usegs m4 NEED_LOCKS [C1 (Z_to_bv 8 0)]) by (unfold NEED_LOCKS; eapply rw_cells_transport; [exact NL3| exact MU4| exact WM4| cbn; (keep_hyps CEILV sp R lo NAME MODE name md slack A LOR SPW3 A5; lia)]).
        pose proof SR3 as (SO3 & SOI3 & SE3 & SEI3 & SIN3 & U13 & U23 & U33 & OL3 & OH3 & FS3 & ND3).
        assert (OL4 : rw_cells usegs m4 A_OFL_LOCK [C4 (Z_to_bv 64 0)]) by (unfold A_OFL_LOCK in *; eapply rw_cells_transport; [exact OL3| exact MU4| exact WM4| cbn; (keep_hyps CEILV sp R lo NAME MODE name md slack A LOR SPW3 A5; lia)]).
        assert (OH4 : rw_cells usegs m4 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr FB))]) by (unfold A_OFL_HEAD in *; eapply rw_cells_transport; [exact OH3| exact MU4| exact WM4| cbn; (keep_hyps CEILV sp R lo NAME MODE name md slack A LOR SPW3 A5; lia)]).
        (* [comment removed for export] *)
        pose proof BOK3 as [BO3 BA3].
        assert (HDF : hd_addr FB = 0 \/ (hd_addr FB <> 0 /\ (exists pvo : word, rw_cells usegs m4 (hd_addr FB + 104) [C8 pvo])
                     /\ hd_addr FB + 232 <= lo /\ (hd_addr FB + 232 <= A \/ A + 1264 <= hd_addr FB) /\ (hd_addr FB + 232 <= 0x10000 \/ 0x56000 <= hd_addr FB))).
        { destruct FB as [|[[q1 Ah] n1] FB']; [left; reflexivity| right]. cbn [hd_addr].
          destruct (lc_files (ps_libc sM)) as [|[q1' f1] fs'] eqn:EFS; [exfalso; exact FS3|].
          cbn in FS3. destruct FS3 as (Eq1 & -> & B0 & Bhi & FR1h & INV1 & REST1).
          pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(apply in_or_app; right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
          unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3, K4, K5, K6. cbn [fst snd] in K1, K2, K3, K4, K5, K6.
          destruct (GIo_apart K R sM _ _ m3 (q, A, 1264) (q1, Ah, FILE_ALLOC) G3 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; right; left; reflexivity)) as [E|AP].
          { exfalso. pose proof (blocks_apart_app_inv _ _ BA3) as (BAc & _ & BAX). cbn in BAc. destruct BAc as [BAq _].
            assert (EA : A = Ah) by congruence. unfold FILE_ALLOC in *.
            pose proof (BAX (q, A, 1264) (q1, Ah, 1264) ltac:(left; reflexivity) ltac:(left; reflexivity)) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. (keep_hyps CEILV sp R NAME MODE name md Ah slack A EA AP; lia). }
          unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP.
          split; [lia|]. split.
          { exists (Z_to_bv 64 0). eapply rw_cells_transport; [exact (FILE_R_prev_cell _ _ _ _ _ _ _ _ _ FR1h)| exact MU4| exact WM4| cbn; (keep_hyps CEILV sp R lo NAME MODE name md Ah slack A LOR SPW3 K4 AP; lia)]. }
          unfold rc_lo in *. (keep_hyps CEILV sp R lo NAME MODE name md Ah slack A LOR SPW3 K4 K5 AP; lia). }
        assert (HDR : 0 <= hd_addr FB /\ hd_addr FB + 232 < 2^63).
        { destruct FB as [|[[q1 Ah] n1] FB']; cbn [hd_addr]; [lia|].
          destruct (lc_files (ps_libc sM)) as [|[q1' f1] fs'] eqn:EFS; [exfalso; exact FS3|].
          cbn in FS3. destruct FS3 as (_ & _ & B0 & Bhi & _). unfold FILE_ALLOC in Bhi. lia. }
        (* [comment removed for export] *)
        assert (FIN : forall (x1'' e0' e1' e2' a0' a1' a2' a3' e4' e5' e6' e7' e8' e9' e10' e11' : word),
          evt usegs ((fun (r : option hptr) (s' : PS) (ms' : machine_state) =>
                       exists a0v m', hpost_regs ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
                         /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
                         /\ match r with
                            | None => a0v = Z_to_bv 64 0 /\ GIo K R s' CL FB m' /\ rw_cells usegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))] /\ 0 <= lc_errno (ps_libc s') < 2^31
                            | Some f => exists Af, a0v = Z_to_bv 64 Af /\ GIo K R s' CL ((f, Af, FILE_BLOCK) :: FB) m'
                            end)
                     (Some q) (set_libc (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) sM))
            (MS (mkR x1'' (Z_to_bv 64 (bv_unsigned sp + -96)) gp (rc_tp R) e0' e1' e2' (Z_to_bv 64 A) (Z_to_bv 64 fd)
                     a0' a1' a2' a3' e4' e5' e6' e7' (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 e8' e9' e10' e11')
                F (Z_to_bv 64 0x1bb3c) fc None m4 (seg_rom usegs))).
        { intros.
          eapply evt_mono.
          { eapply (fopen_S7 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (hd := hd_addr FB) (m2 := m3) (fl := if mode_m0 md =? 114 then 8 else 4) (MODE := MODE) (md := md) (slack := slack);
              first [exact FC4 | exact BLK4 | exact FRO4 | exact FRI4 | exact SSP4 | exact THR4 | exact NL4 | exact OL4 | exact OH4 | exact HDF | exact MU4 | exact WM4 | exact ST4 | exact MI4
                    | exact MDR | exact NONUL | exact PAD | exact M0 | exact NOPLUS | exact NOE | exact HFD | (keep_hyps CEILV sp R lo NAME MODE name md slack A LOB LOR SPW3 SPM SP47 TPLO A1 A5 A4 hptr FB HDR; lia)
                    | unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps CEILV hptr sp R FB lo NAME MODE name md slack A x Hx; lia)
                    | match goal with |- ?g => idtac "S7 side:" g end ]. }
          cbv beta. intros ms7 PO7.
          destruct PO7 as (f0' & f1' & f2' & g1 & g2 & g3 & g4 & g5 & g6 & g7 & f3' & f4' & f5' & f6' & m7 & -> & FC7 & BLK7 & OL7 & OH7 & OLDP7 & SSP7 & MU7 & WM7 & MI7 & ST7).
          eexists _, m7. split; [unfold hpost_regs; repeat eexists; reflexivity|].
          split; [destruct sM as [xh xl xo xt]; cbn [ps_outfile set_libc] in OF3 |- *; exact OF3|].
          split; [exact MI7|]. split; [exact ST7|].
          assert (HWX : exists W', munch W' m3 m7
                    /\ Forall (fun iv : Z * Z => (CEILZ <= fst iv /\ snd iv <= bv_unsigned sp) \/ (fst iv = A /\ snd iv = A + 232) \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                                                \/ (FB <> [] /\ fst iv = hd_addr FB + 104 /\ snd iv = hd_addr FB + 112)) W').
          { revert MU7. destruct (Z.eqb_spec (hd_addr FB) 0) as [E|NE]; intros MU7.
            - exists [(lo, bv_unsigned sp); (A, A + 232); (A_OFL_HEAD, A_OFL_HEAD + 8)]. split.
              + eapply munch_weaken; [| exact MU7]. unfold sub_fp. intros x Ox. cbn [outside] in Ox |- *. destruct Ox as (O1 & O2 & O3 & _).
                split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [lia| exact I].
              + apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; split; reflexivity|].
                apply Forall_cons; [right; right; left; split; reflexivity| apply Forall_nil].
            - exists [(lo, bv_unsigned sp); (A, A + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd_addr FB + 104, hd_addr FB + 112)]. split.
              + exact MU7.
              + apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; split; reflexivity|].
                apply Forall_cons; [right; right; left; split; reflexivity|]. apply Forall_cons; [| apply Forall_nil].
                right; right; right. cbn [fst snd]. split; [| split; reflexivity]. intros EFB. apply NE. rewrite EFB. reflexivity. }
          destruct HWX as (W' & MU7' & HW').
          assert (EFL7 : (if mode_m0 md =? 114 then 8 else 4) = (if wr then 4 else 8)) by (rewrite M0W; destruct wr; reflexivity).
          destruct (fopen_finish R sM CL FB m3 m7 W' q A fd wr _ (skipn 232 junk) (bv_unsigned sp) G3 MU7' WM7 HW' ltac:(lia) SPM FC7 BLK7 OL7 OH7 OLDP7 EFL7 HFD) as [G7 AG7].
          split; [eapply agrees_on_trans; [exact AG03| exact AG7]|].
          exists A. split; [reflexivity| exact G7]. }
        destruct wr.
        * (* [comment removed for export] *)
          assert (EFL : (mode_m0 md =? 114) = false) by (rewrite M0W; reflexivity). rewrite EFL in FC4 |- *.
          apply implM_bind_assoc. apply implM_sysk.
          eapply evt_cut. { eapply fopen_br_w with (fd := fd). lia. }
          cbv beta. intros ms5 ->.
          step_ecall. split. { at_node_solve__p4. }
          intros rsp a Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
          destruct a as [e'|v]; [| destruct Hdec as (_ & X & _); discriminate X]. destruct Hdec as [-> HE'].
          cbn beta iota. apply implM_retb. apply implM_upd_lc. apply implM_ret. unfold efferr, eff0. sys_nret.
          eapply evt_cut. { eapply (fopen_ioctl_ret gp (rc_tp R) F fc 0 [] []) with (e := e'). exact HE'. }
          cbv beta. intros ms6 ->. apply FIN.
        * (* [comment removed for export] *)
          assert (EFL : (mode_m0 md =? 114) = true) by (rewrite M0W; reflexivity). rewrite EFL in FC4 |- *.
          apply implM_retb. apply implM_upd_lc. apply implM_ret.
          eapply evt_cut. { eapply fopen_br_r. }
          cbv beta. intros ms5 ->. apply FIN.
      + (* [comment removed for export] *)
        destruct RES as (-> & G3 & [EEN ERR3]).
        pose proof G3 as (HH3 & HS3 & HA3 & CT3 & PT3 & CLI3 & CM3 & CE3 & CS3 & Etls3 & TB3 & BOK3 & SPW3).
        pose proof (core_ssp R m3 CLI3) as SSP3.
        apply implM_upd_lc. apply implM_sysk.
        eapply evt_cut. { eapply (fopen_S4 sp gp (rc_tp R) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MODE md slack); [exact FRI3 | exact SSP3 | exact HFD | exact MI3]. }
        cbv beta. intros ms4 PO4. destruct_exs PO4. subst ms4.
        step_ecall. split. { at_node_solve__p5. }
        intros rsp a Hdec. unfold dec_close in Hdec. apply dec_plain_Some in Hdec.
        release_frame FRI3 ST3 (bv_unsigned sp + -32).
        assert (TAILN : forall mm (a0w : word) x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6',
          mm = m3 ->
          evt usegs ((fun (r : option hptr) (s' : PS) (ms' : machine_state) =>
                       exists a0v m', hpost_regs ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
                         /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
                         /\ match r with
                            | None => a0v = Z_to_bv 64 0 /\ GIo K R s' CL FB m' /\ rw_cells usegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))] /\ 0 <= lc_errno (ps_libc s') < 2^31
                            | Some f => exists Af, a0v = Z_to_bv 64 Af /\ GIo K R s' CL ((f, Af, FILE_BLOCK) :: FB) m'
                            end)
                     None (set_libc (set_errno_lc ENOMEM (ps_libc sM)) sM))
            (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -32)) gp (rc_tp R) t0' t1' t2' (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                     a0w a1' a2' a3' a4' a5' a6' (Z_to_bv 64 57) sv2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x1b8f4) fc None mm (seg_rom usegs))).
        { intros until t6'. intros ->.
          eapply evt_mono. { eapply (fopen_S5 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc) with (lo := lo) (W := []) (MODE := MODE) (md := md) (slack := slack); fastfirst (first [ noevar_assumption |exact FRO3| exact ST3| exact MI3| apply munch_refl| apply wmono_refl| lia]). }
          cbv beta. intros ms' PO. destruct PO as (f0' & f1' & f2' & g1 & g2 & g3 & g4 & g5 & g6 & g7 & f3' & f4' & f5' & f6' & -> & _ & _ & MI' & ST').
          eexists _, m3. split; [unfold hpost_regs; repeat eexists; reflexivity|].
          split; [destruct sM as [xh xl xo xt]; cbn [ps_outfile set_libc] in OF3 |- *; exact OF3|].
          split; [exact MI'|]. split; [exact ST'|]. split; [exact AG03|]. split; [reflexivity|].
          split. { pose proof (GIo_stdio_step R sM CL FB m3 m3 [] (bv_unsigned sp) (set_errno_lc ENOMEM (ps_libc sM)) G3 (munch_refl [] m3) (wmono_refl usegs m3) (Forall_nil _) SPM) as G3'.
                   apply G3'. pose proof (proj1 (KST _ R _ _) HS3) as SR3'. unfold STDIOR in SR3' |- *. destruct (ps_libc sM) as [xso xse xfs xer]; cbn [lc_stdout lc_stderr lc_files set_errno_lc] in SR3' |- *. exact SR3'. }
          cbn [ps_libc set_libc set_errno_lc lc_errno]. unfold ENOMEM. split; [exact ERR3| lia]. }
        destruct a as [e'|v].
        * destruct Hdec as [-> HE']. apply implM_ret. unfold efferr, eff0. sys_nret. apply TAILN. reflexivity.
        * destruct Hdec as (-> & _ & HV). apply implM_ret. unfold eff0. sys_nret. apply TAILN. reflexivity.
  Qed.
  End Sz9.
  Theorem fopen_o_proof : ltac:(let t := eval cbv delta [fopen_o_proof__stmt] in fopen_o_proof__stmt in exact t).
  Proof using EQB HAL HFL HPL KST MALLOC8K. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME MODE name md wr. ltac2:(SecDiet.SzSec.closeP 'fopen_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueFo.

End WithCeil.
End TwB.
End Stdio_glue_fo.

(* [comment removed for export] *)
Module Stdio_glue_fc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fmodeflags OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_strchr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fclose OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section Relink.
  Lemma fcells_split_links : forall flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
    fcells flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl =
    [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 re); C8 (Z_to_bv 64 cf);
     C8 (Z_to_bv 64 we); C8 (Z_to_bv 64 wp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wb);
     C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 wf); C8 (Z_to_bv 64 sf); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bs)]
    ++ [C8 (Z_to_bv 64 pv)] ++ [C8 (Z_to_bv 64 nx)]
    ++ [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
        C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0); CB 80 tl].
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition FILE_R_link_cells__stmt : Prop := forall m f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx ->
    rw_cells ssegs m (Fp + 104) [C8 (Z_to_bv 64 pv)] /\ rw_cells ssegs m (Fp + 112) [C8 (Z_to_bv 64 nx)].
  Section Sz2.
  Variables m f Fp BA cf rf sf pv nx : ltac2:(SecDiet.SzSec.tyM 'FILE_R_link_cells__stmt "vvvvvvvvv" @m).
  Lemma FILE_R_link_cells__body : ltac2:(SecDiet.SzSec.bodyP 'FILE_R_link_cells__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros (flags & mode & rp & tail & bufbytes & FC & _).
    rewrite fcells_split_links in FC. apply (proj1 (rw_cells_app ssegs m Fp _ _)) in FC as [_ FC].
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in FC as [FP FC]. apply (proj1 (rw_cells_app ssegs m _ [_] _)) in FC as [FN _].
    cbn [cells_size csize Nat.add] in FP, FN.
    replace (Fp + Z.of_nat 104) with (Fp + 104) in FP by lia.
    replace (Fp + Z.of_nat 104 + Z.of_nat 8) with (Fp + 112) in FN by lia.
    split; [exact FP| exact FN].
  Qed.
  End Sz2.
  Lemma FILE_R_link_cells : ltac:(let t := eval cbv delta [FILE_R_link_cells__stmt] in FILE_R_link_cells__stmt in exact t).
  Proof using Type. intros m f Fp BA cf rf sf pv nx. ltac2:(SecDiet.SzSec.closeP 'FILE_R_link_cells__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition FILE_R_relink__stmt : Prop := forall (P : Z -> Prop) m m' f Fp BA cf rf sf pv nx pv' nx',
    FILE_R m f Fp BA cf rf sf pv nx ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> ~ (Fp + 104 <= a < Fp + 120) -> P a) ->
    (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    rw_cells ssegs m' (Fp + 104) [C8 (Z_to_bv 64 pv')] -> rw_cells ssegs m' (Fp + 112) [C8 (Z_to_bv 64 nx')] ->
    FILE_R m' f Fp BA cf rf sf pv' nx'.
  Section Sz3.
  Variables P m m' f Fp BA cf rf sf pv nx pv' nx' : ltac2:(SecDiet.SzSec.tyM 'FILE_R_relink__stmt "vvvvvvvvvvvvv" @P).
  Lemma FILE_R_relink__body : ltac2:(SecDiet.SzSec.bodyP 'FILE_R_relink__stmt "vvvvvvvvvvvvv").
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros FR AG HP1 HP2 PC NC.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - rewrite fcells_split_links in FC |- *.
      apply (proj1 (rw_cells_app ssegs m Fp _ _)) in FC as [FCa FC]. apply (proj1 (rw_cells_app ssegs m _ [_] _)) in FC as [_ FC].
      apply (proj1 (rw_cells_app ssegs m _ [_] _)) in FC as [_ FCb].
      cbn [cells_size csize Nat.add] in FCa, FCb |- *.
      apply (proj2 (rw_cells_app ssegs m' Fp _ _)). split.
      + eapply agrees_rw_cells; [exact AG| exact FCa|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP1; lia.
      + apply (proj2 (rw_cells_app ssegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
        * replace (Fp + Z.of_nat 104) with (Fp + 104) by lia. exact PC.
        * apply (proj2 (rw_cells_app ssegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
          -- replace (Fp + Z.of_nat 104 + Z.of_nat 8) with (Fp + 112) by lia. exact NC.
          -- eapply agrees_rw_cells; [exact AG| exact FCb|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP1; lia.
    - pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
      eapply agrees_rw_cells; [exact AG | exact BUF |]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP2. lia.
  Qed.
  End Sz3.
  Lemma FILE_R_relink : ltac:(let t := eval cbv delta [FILE_R_relink__stmt] in FILE_R_relink__stmt in exact t).
  Proof using CEILV. intros P m m' f Fp BA cf rf sf pv nx pv' nx'. ltac2:(SecDiet.SzSec.closeP 'FILE_R_relink__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma FILE_R_relink_same : forall (P : Z -> Prop) m m' f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> P a) -> (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    FILE_R m' f Fp BA cf rf sf pv nx.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros P m m' f Fp BA cf rf sf pv nx FR AG HP1 HP2.
    pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR) as [PC NC].
    eapply FILE_R_relink; [exact FR| exact AG| intros a Ha _; apply HP1; exact Ha| exact HP2| |].
    - eapply agrees_rw_cells; [exact AG| exact PC|]. cbn. intros a Ha. apply HP1. lia.
    - eapply agrees_rw_cells; [exact AG| exact NC|]. cbn. intros a Ha. apply HP1. lia.
  Qed.
End Relink.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Unlink.
  Context {hptr : Type} (ptr_eqb : hptr -> hptr -> bool).
  Hypothesis EQB : forall p q, ptr_eqb p q = true <-> p = q.
  #[local] Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  Fixpoint last_addr (prev : Z) (FB : list cblk) : Z :=
    match FB with [] => prev | (_, A, _) :: FB' => last_addr A FB' end.

  Lemma last_addr_app : forall prev (F1 F2 : list cblk), last_addr prev (F1 ++ F2) = last_addr (last_addr prev F1) F2.
  Proof using Type. pin_using tt. intros prev F1; revert prev. induction F1 as [|[[q A] n] F1 IH]; intros prev F2; cbn; [reflexivity| apply IH]. Qed.

  Lemma last_addr_In : forall prev (FB : list cblk), FB <> [] -> exists q n, In (q, last_addr prev FB, n) FB.
  Proof using Type. pin_using tt.
    intros prev FB; revert prev. induction FB as [|[[q A] n] FB IH]; intros prev NE; [exfalso; exact (NE eq_refl)|].
    cbn. destruct FB as [|b FB'].
    - exists q, n. left. reflexivity.
    - destruct (IH A ltac:(discriminate)) as (q' & n' & HIN). exists q', n'. right. exact HIN.
  Qed.

  Lemma hd_addr_app : forall (F1 F2 : list cblk), F1 <> [] -> hd_addr (F1 ++ F2) = hd_addr F1.
  Proof using Type. pin_using tt. intros [|[[q A] n] F1] F2 NE; [exfalso; exact (NE eq_refl)| reflexivity]. Qed.

  Lemma hd_addr_In : forall (FB : list cblk), FB <> [] -> exists q n, In (q, hd_addr FB, n) FB.
  Proof using Type. pin_using tt. intros [|[[q A] n] FB] NE; [exfalso; exact (NE eq_refl)|]. exists q, n. left. reflexivity. Qed.

  Lemma NoDup_files_remove : forall fs q, List.NoDup (map fst fs) -> List.NoDup (map fst (files_remove ptr_eqb fs q)).
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q ND; cbn; [constructor|].
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    destruct (ptr_eqb k q); [exact ND|]. cbn. constructor; [| apply IH; exact ND].
    intros HIn. apply NI. eapply (files_remove_keys ptr_eqb). exact HIn.
  Qed.

  (* [comment removed for export] *)
  Definition files_R_mid__stmt : Prop := forall m prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    exists f,
      files_lookup ptr_eqb fs q = Some f /\ In (q, f) fs /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK (last_addr prev F1) (hd_addr F2)
      /\ heap_file_inv f
      /\ (F1 <> [] -> rw_cells ssegs m (last_addr prev F1 + 112) [C8 (Z_to_bv 64 A)] /\ 0 < last_addr prev F1)
      /\ (F2 <> [] -> rw_cells ssegs m (hd_addr F2 + 104) [C8 (Z_to_bv 64 A)] /\ 0 < hd_addr F2).
  Section Sz10.
  Variables m prev fs : ltac2:(SecDiet.SzSec.tyM 'files_R_mid__stmt "vvvk" @m).
  Lemma files_R_mid__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_mid__stmt "vvvk").
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND.
    - cbn [app] in FS. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      exists f. cbn [files_lookup last_addr]. rewrite (eqb_refl' ptr_eqb EQB).
      split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact FR|]. split; [exact INV|]. split; [intros NE; exfalso; exact (NE eq_refl)|].
      intros NE2. destruct F2 as [|[[q2 A2] n2] F2']; [exfalso; exact (NE2 eq_refl)|]. cbn [hd_addr].
      destruct fs' as [|[q2' f2] fs'']; [exact (False_ind _ REST)|]. cbn [files_R] in REST.
      destruct REST as (_ & _ & B0 & _ & FR2 & _). split; [| exact B0].
      exact (proj1 (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR2)).
    - cbn [app] in FS. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A10 & A1hi & FR1 & INV1 & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      destruct (IH A1 fs' F2 q A n REST ND) as (f & LK & INf & En & A0 & Ahi & FR & INV & HP & HN).
      assert (NE : q1 <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact INf).
      exists f. cbn [files_lookup]. rewrite (eqb_neq ptr_eqb EQB _ _ NE).
      split; [exact LK|]. split; [right; exact INf|]. split; [exact En|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact FR|]. split; [exact INV|]. split; [| exact HN].
      intros _. cbn [last_addr]. destruct F1 as [|b F1'].
      + cbn [last_addr app hd_addr] in FR1 |- *. split; [| exact A10]. exact (proj2 (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR1)).
      + apply HP. discriminate.
  Qed.
  End Sz10.
  Lemma files_R_mid : ltac:(let t := eval cbv delta [files_R_mid__stmt] in files_R_mid__stmt in exact t).
  Proof using EQB. intros m prev fs F1. ltac2:(SecDiet.SzSec.closeP 'files_R_mid__body "vvvk"). Qed.

  (* [comment removed for export] *)
  Definition files_remove_mid__stmt : Prop := forall m prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    exists fs1 f fs2, fs = fs1 ++ (q, f) :: fs2 /\ length fs1 = length F1 /\ files_remove ptr_eqb fs q = fs1 ++ fs2.
  Section Sz11.
  Variables m prev fs : ltac2:(SecDiet.SzSec.tyM 'files_remove_mid__stmt "vvvk" @m).
  Lemma files_remove_mid__body : ltac2:(SecDiet.SzSec.bodyP 'files_remove_mid__stmt "vvvk").
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND.
    - cbn [app] in FS. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & _).
      exists [], f, fs'. cbn. rewrite (eqb_refl' ptr_eqb EQB). repeat split; reflexivity.
    - cbn [app] in FS. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & _ & _ & _ & _ & _ & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      destruct (IH A1 fs' F2 q A n REST ND) as (fs1 & f & fs2 & -> & L & RM).
      assert (NE : q1 <> q).
      { intros ->. apply NI. rewrite map_app. apply in_or_app. right. left. reflexivity. }
      exists ((q1, f1) :: fs1), f, fs2. cbn. rewrite (eqb_neq ptr_eqb EQB _ _ NE), RM, L. repeat split; reflexivity.
  Qed.
  End Sz11.
  Lemma files_remove_mid : ltac:(let t := eval cbv delta [files_remove_mid__stmt] in files_remove_mid__stmt in exact t).
  Proof using EQB. intros m prev fs F1. ltac2:(SecDiet.SzSec.closeP 'files_remove_mid__body "vvvk"). Qed.

  (* [comment removed for export] *)
  Definition files_R_unlink__stmt : Prop := forall (P : Z -> Prop) m m' prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    agrees_on P m m' ->
    (forall q2 A2 n2 a, In (q2, A2, n2) (F1 ++ F2) -> A2 <= a < A2 + 1264 ->
          ~ (A2 = last_addr prev F1 /\ A2 + 112 <= a < A2 + 120) -> ~ (A2 = hd_addr F2 /\ A2 + 104 <= a < A2 + 112) -> P a) ->
    (forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) (F1 ++ (q, A, n) :: F2) -> In (q3, A3, n3) (F1 ++ (q, A, n) :: F2) -> A2 = A3 -> q2 = q3) ->
    (F1 <> [] -> rw_cells ssegs m' (last_addr prev F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]) ->
    (F2 <> [] -> rw_cells ssegs m' (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr prev F1))]) ->
    prev <> A -> (forall q2 A2 n2, In (q2, A2, n2) (F1 ++ (q, A, n) :: F2) -> A2 <> prev) ->
    files_R m' prev (files_remove ptr_eqb fs q) (F1 ++ F2).
  Section Sz12.
  Variables P m m' prev fs : ltac2:(SecDiet.SzSec.tyM 'files_R_unlink__stmt "vvvvvk" @P).
  Lemma files_R_unlink__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_unlink__stmt "vvvvvk").
  Proof using CEILV EQB. pin_using (fun (CEILV EQB : unit) => tt).
    intros F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND AG HP DIST LP LN PA PNA.
    - (* [comment removed for export] *)
      cbn [app] in FS |- *. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      cbn [files_remove]. rewrite (eqb_refl' ptr_eqb EQB).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      cbn [last_addr] in LN, HP.
      destruct F2 as [|[[q2 A2] n2] F2']; destruct fs' as [|[q2' f2] fs'']; try exact (False_ind _ REST); [exact I|].
      cbn [files_R] in REST |- *. destruct REST as (<- & -> & B0 & Bhi & FR2 & INV2 & REST2).
      cbn [hd_addr] in LN, HP.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
      pose proof INV2 as (_ & _ & BS2 & _).
      split.
      { pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR2) as [_ NC2].
        assert (A2P : A2 <> prev) by (eapply (PNA q2 A2 FILE_ALLOC); right; left; reflexivity).
        eapply (FILE_R_relink P); [exact FR2| exact AG| | | exact (LN ltac:(discriminate))|].
        - intros a Ha Hn. eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X) | intros [_ X]; lia].
        - rewrite BS2. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X)| intros [_ X]; lia].
        - eapply agrees_rw_cells; [exact AG| exact NC2|]. cbn. intros a Ha.
          eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X)| intros [_ X]; lia]. }
      split; [exact INV2|].
      eapply files_R_frame; [exact REST2|].
      intros q3 A3 n3 f3 pv3 nx3 HIN3 FR3 INV3. pose proof INV3 as (_ & _ & BS3 & _).
      assert (N3A : A3 <> A2).
      { intros E. pose proof (DIST q3 A3 n3 q2 A2 FILE_ALLOC ltac:(right; right; exact HIN3) ltac:(right; left; reflexivity) E) as Eq.
        subst q3 A3. apply List.NoDup_cons_iff in ND as [NI2 _]. apply NI2.
        pose proof (files_R_toks _ _ _ _ REST2) as TK. pose proof (in_map cb_tok _ _ HIN3) as X. cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
      assert (N3P : A3 <> prev) by (eapply PNA; right; right; exact HIN3).
      eapply (FILE_R_relink_same P); [exact FR3| exact AG| |].
      + intros a Ha. eapply (HP q3 A3 n3 a); [right; exact HIN3| lia| intros [X _]; exact (N3P X)| intros [X _]; exact (N3A X)].
      + rewrite BS3. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q3 A3 n3 a); [right; exact HIN3| lia| intros [X _]; exact (N3P X)| intros [X _]; exact (N3A X)].
    - (* [comment removed for export] *)
      cbn [app] in FS |- *. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A10 & A1hi & FR1 & INV1 & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      pose proof (files_R_mid m A1 fs' F1 F2 q A n REST ND) as (f & _ & INf & _).
      assert (NE : q1 <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact INf).
      cbn [files_remove]. rewrite (eqb_neq ptr_eqb EQB _ _ NE). cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A10|]. split; [exact A1hi|].
      pose proof INV1 as (_ & _ & BS1 & _).
      assert (A1A : A1 <> A).
      { intros E. pose proof (DIST q1 A1 FILE_ALLOC q A n ltac:(left; reflexivity) ltac:(apply in_or_app; right; left; reflexivity) E) as Eq. exact (NE Eq). }
      assert (A1F2 : F2 <> [] -> A1 <> hd_addr F2).
      { intros NE2 E. destruct (hd_addr_In F2 NE2) as (q2 & n2 & HIN2).
        pose proof (DIST q1 A1 FILE_ALLOC q2 (hd_addr F2) n2 ltac:(left; reflexivity) ltac:(apply in_or_app; right; right; exact HIN2) E) as Eq.
        subst q2. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
        pose proof (in_map cb_tok _ _ (in_or_app F1 ((q, A, n) :: F2) (q1, hd_addr F2, n2) (or_intror (or_intror HIN2)))) as X.
        cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
      split.
      { destruct F1 as [|[[q1b A1b] n1b] F1'].
        - (* [comment removed for export] *)
          cbn [last_addr app hd_addr] in FR1, LP |- *.
          pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR1) as [PC1 _].
          eapply (FILE_R_relink P); [exact FR1| exact AG| | | | exact (LP ltac:(discriminate))].
          + intros a Ha Hn. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia|].
            intros [E _]. exact (A1F2 ltac:(intros E2; rewrite E2 in E; cbn in E; lia) E).
          + rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia| intros [_ X]; lia].
          + eapply agrees_rw_cells; [exact AG| exact PC1|]. cbn. intros a Ha.
            eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia|].
            intros [X _]. exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X).
        - (* [comment removed for export] *)
          cbn [last_addr app hd_addr] in FR1 |- *.
          assert (A1L : A1 <> last_addr A1b F1').
          { intros E. destruct (last_addr_In A1b F1' ) as (ql & nl & HINl).
            all: cycle 1.
            { pose proof (DIST q1 A1 FILE_ALLOC ql (last_addr A1b F1') nl ltac:(left; reflexivity) ltac:(right; right; apply in_or_app; left; exact HINl) E) as Eq.
              subst ql. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
              pose proof (in_map cb_tok _ _ (or_intror (in_or_app F1' ((q, A, n) :: F2) (q1, last_addr A1b F1', nl) (or_introl HINl)) : In (q1, last_addr A1b F1', nl) (((q1b, A1b, n1b) :: F1') ++ (q, A, n) :: F2))) as X.
              cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
            (* [comment removed for export] *)
            intros E'. subst F1'. cbn in E.
            pose proof (DIST q1 A1 FILE_ALLOC q1b A1b n1b ltac:(left; reflexivity) ltac:(right; left; reflexivity) E) as Eq.
            subst q1b. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
            pose proof (in_map cb_tok _ _ (or_introl eq_refl : In (q1, A1b, n1b) (((q1, A1b, n1b) :: []) ++ (q, A, n) :: F2))) as X.
            cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
          eapply (FILE_R_relink_same P); [exact FR1| exact AG| |].
          + intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A1L X)| intros [X _]].
            exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X).
          + rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A1L X)| intros [X _]].
            exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X). }
      split; [exact INV1|].
      eapply (IH A1 fs' F2 q A n); [exact REST| exact ND| exact AG| | | intros _; exact (LP ltac:(discriminate))| exact LN| exact A1A|].
      + intros q2 A2 n2 a HIN2. apply (HP q2 A2 n2 a). right. exact HIN2.
      + intros q2 A2 n2 q3 A3 n3 HIN2 HIN3. apply (DIST q2 A2 n2 q3 A3 n3); right; assumption.
      + intros q2 A2 n2 HIN2 E. subst A2.
        pose proof (DIST q1 A1 FILE_ALLOC q2 A1 n2 ltac:(left; reflexivity) ltac:(right; exact HIN2) eq_refl) as Eq. subst q2.
        apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
        pose proof (in_map cb_tok _ _ HIN2) as X. cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK).
  Qed.
  End Sz12.
  Lemma files_R_unlink : ltac:(let t := eval cbv delta [files_R_unlink__stmt] in files_R_unlink__stmt in exact t).
  Proof using CEILV EQB. intros P m m' prev fs F1. ltac2:(SecDiet.SzSec.closeP 'files_R_unlink__body "vvvvvk"). Qed.
End Unlink.

Section GlueFc.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).
  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.spo_facts K KST).
  #[local] Notation GIo_stdio_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.GIo_stdio_step K KST HFL).
  #[local] Notation keeps_of_stdio := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.keeps_of_stdio K).

  (* [comment removed for export] *)
  Definition free_stmt_8k : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (C1 C2 FB : list cblk) (q : hptr) (A n lo : Z),
      std_pre_o K sp tp R s (C1 ++ (q, A, n) :: C2) FB lo 8192 m -> a0 = Z_to_bv 64 A ->
      implM ssegs (pfree HO q) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ GIo K R s' (C1 ++ C2) FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom ssegs)).
  Hypothesis FREE8K : free_stmt_8k.

  (* [comment removed for export] *)
  Lemma HARNR_remove : forall (o : option hptr) (F1 F2 : list cblk) q A n m,
    o <> Some q -> HARNR o (F1 ++ (q, A, n) :: F2) m -> HARNR o (F1 ++ F2) m.
  Proof using Type. pin_using tt.
    intros o F1 F2 q A n m NO (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    destruct o as [q'|]; [|exact H3]. destruct H3 as (A' & HIn & HC). exists A'. split; [| exact HC].
    apply in_app_or in HIn. apply in_or_app. destruct HIn as [X|[X|X]]; [left; exact X| | right; exact X].
    exfalso. apply NO. injection X as -> _ _. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma munch_drop_empty : forall (W : list (Z * Z)) m m', munch W m m' -> munch (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W) m m'.
  Proof using Type. pin_using tt.
    intros W m m' MU. eapply munch_weaken; [| exact MU]. unfold sub_fp. clear MU.
    induction W as [|[lo hi] W IH]; intros x Hx; cbn in *; [exact I|].
    destruct (lo <? hi) eqn:E; cbn in Hx.
    - destruct Hx as [H1 H2]. split; [exact H1| apply IH; exact H2].
    - apply Z.ltb_ge in E. split; [lia| apply IH; exact Hx].
  Qed.
  Lemma Forall_drop_empty : forall (Q : Z * Z -> Prop) W,
    Forall (fun iv => snd iv <= fst iv \/ Q iv) W -> Forall Q (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W).
  Proof using Type. pin_using tt.
    intros Q W HF. induction HF as [|iv W HQ HF IH]; cbn; [constructor|].
    destruct (fst iv <? snd iv) eqn:E; [| exact IH]. apply Z.ltb_lt in E.
    constructor; [| exact IH]. destruct HQ as [HQ|HQ]; [lia| exact HQ].
  Qed.

  (* [comment removed for export] *)
  Lemma fclose_finish : forall R (s : PS) (CL F1 F2 : list cblk) m m4 W q A SP,
    GIo K R s CL (F1 ++ (q, A, FILE_ALLOC) :: F2) m ->
    ps_outfile s <> Some q ->
    munch W m m4 -> wmono ssegs m m4 ->
    Forall (fun iv : Z * Z => snd iv <= fst iv \/ (CEILZ <= fst iv /\ snd iv <= SP) \/ (A <= fst iv /\ snd iv <= A + 1264)
                              \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                              \/ (F1 <> [] /\ fst iv = last_addr 0 F1 + 112 /\ snd iv = last_addr 0 F1 + 120)
                              \/ (F2 <> [] /\ fst iv = hd_addr F2 + 104 /\ snd iv = hd_addr F2 + 112)) W ->
    CEILZ <= SP -> SP <= rc_spmain R ->
    rw_cells ssegs m4 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells ssegs m4 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ F2)))] ->
    (F1 <> [] -> rw_cells ssegs m4 (last_addr 0 F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]) ->
    (F2 <> [] -> rw_cells ssegs m4 (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr 0 F1))]) ->
    GIo K R (set_libc (set_files (files_remove eqb (lc_files (ps_libc s)) q) (ps_libc s)) s) (CL ++ [(q, A, FILE_ALLOC)]) (F1 ++ F2) m4
    /\ agrees_on (client_keeps CL SP) m m4.
  Proof using EQB HFL HPL KST. pin_using (fun (EQB HFL HPL KST : unit) => tt).
    intros R s CL F1 F2 m m4 W0 q A SP G NOF MU0 WM HW0 CSP HSP OL4 OH4 LP4 LN4.
    pose proof (munch_drop_empty _ _ _ MU0) as MU. pose proof (Forall_drop_empty _ _ HW0) as HW. cbv beta in HW.
    remember (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W0) as W eqn:EW. clear EW MU0 HW0.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA].
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold rc_spmain in HSP.
    apply (proj1 (KST _ R _ _)) in HS as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    set (FB := F1 ++ (q, A, FILE_ALLOC) :: F2) in *.
    assert (INb : In (q, A, FILE_ALLOC) FB) by (subst FB; apply in_or_app; right; left; reflexivity).
    assert (INFB : forall b, In b (F1 ++ F2) -> In b FB).
    { intros b Hb. subst FB. apply in_app_or in Hb. apply in_or_app. destruct Hb as [X|X]; [left; exact X| right; right; exact X]. }
    pose proof BO as BO'. apply Forall_app in BO' as [BOCL BOFB].
    pose proof (blocks_apart_app_inv _ _ BA) as (BAc & BAf & BAX).
    (* [comment removed for export] *)
    assert (FBn : forall q2 A2 n2, In (q2, A2, n2) FB -> n2 = FILE_ALLOC /\ 0 < A2).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m 0 _ FB q2 A2 n2 FS ND HIN) as (f & pv & nx & _ & _ & En & B0 & _). split; [exact En| exact B0]. }
    assert (BKF : forall q2 A2 n2, In (q2, A2, n2) FB ->
              0 < A2 /\ A2 + 1264 <= CEILZ /\ (A2 + 1264 <= 0x10000 \/ 0x55000 <= A2) /\ (A2 + 1264 <= utp R - 200 \/ utp R - 200 + 4096 <= A2)).
    { intros q2 A2 n2 HIN. destruct (FBn _ _ _ HIN) as [-> B0].
      pose proof (proj1 (Forall_forall _ _) BOFB _ HIN) as (K1 & K2 & K3 & K4 & K5 & K6).
      unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3, K4, K5, K6 |- *. cbn [fst snd] in K1, K2, K3, K4, K5, K6. lia. }
    (* [comment removed for export] *)
    assert (APF : forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) FB -> In (q3, A3, n3) FB -> A2 <> A3 -> A2 + 1264 <= A3 \/ A3 + 1264 <= A2).
    { intros q2 A2 n2 q3 A3 n3 HIN2 HIN3 NE. destruct (FBn _ _ _ HIN2) as [-> _]. destruct (FBn _ _ _ HIN3) as [-> _].
      destruct (blocks_apart_In _ _ _ BAf HIN2 HIN3) as [E|AP]; [exfalso; apply NE; injection E as E1 E2; exact E2|].
      unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. exact AP. }
    assert (DIST : forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) FB -> In (q3, A3, n3) FB -> A2 = A3 -> q2 = q3).
    { intros q2 A2 n2 q3 A3 n3 HIN2 HIN3 E. destruct (FBn _ _ _ HIN2) as [-> _]. destruct (FBn _ _ _ HIN3) as [-> _].
      destruct (blocks_apart_In _ _ _ BAf HIN2 HIN3) as [E'|AP]; [injection E' as E1 E2; exact E1|].
      unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
    pose proof (BKF _ _ _ INb) as (BK1 & BK2 & BK3 & BK4).
    (* [comment removed for export] *)
    assert (HL : F1 <> [] -> exists ql nl, In (ql, last_addr 0 F1, nl) F1) by (intros NE; exact (last_addr_In 0 F1 NE)).
    assert (HN : F2 <> [] -> exists qn nn, In (qn, hd_addr F2, nn) F2) by (intros NE; exact (hd_addr_In F2 NE)).
    (* [comment removed for export] *)
    set (P4 := fun a : Z => ~ (CEILZ <= a < SP) /\ ~ (A <= a < A + 1264) /\ ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8)
                            /\ ~ (F1 <> [] /\ last_addr 0 F1 + 112 <= a < last_addr 0 F1 + 120)
                            /\ ~ (F2 <> [] /\ hd_addr F2 + 104 <= a < hd_addr F2 + 112)).
    assert (AG : agrees_on P4 m m4).
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha (N1 & N2 & N3 & N4 & N5).
      eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd] in Hiv |- *.
      destruct Hiv as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]]; [(keep_hyps CEILV R A SP a lo' hi' N1 X; lia)| (keep_hyps CEILV R A SP a lo' hi' N2 X; lia)| (keep_hyps CEILV R A SP a lo' hi' N3 X; lia)| |].
      - intros Hin. apply N4. split; [exact Xne| lia].
      - intros Hin. apply N5. split; [exact Xne| lia]. }
    (* [comment removed for export] *)
    assert (OUT : forall a, 0 <= a < 2^64 ->
              ~ (CEILZ <= a < usp0 R - 48) -> ~ in_block (CL ++ FB) a -> ~ (0x23660 <= a < 0x23930) -> ~ (0x54148 <= a < 0x54970) -> outside W a).
    { intros a Ha N1 N2 N3 N4. eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd].
      destruct Hiv as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]]; cbn [fst snd] in *.
      - (keep_hyps CEILV R SP a lo' hi' HSP N1 X; lia).
      - intros Hin. apply N2. apply (proj2 (in_block_In _ _)). exists (q, A, FILE_ALLOC).
        split; [apply in_or_app; right; exact INb| unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
      - unfold A_OFL_HEAD in X. lia.
      - intros Hin. apply N2. destruct (HL Xne) as (ql & nl & HINl). destruct (FBn ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as [Enl _].
        apply (proj2 (in_block_In _ _)). exists (ql, last_addr 0 F1, nl).
        split; [apply in_or_app; right; subst FB; apply in_or_app; left; exact HINl| unfold cb_addr, cb_size; cbn [fst snd]; subst nl; unfold FILE_ALLOC; lia].
      - intros Hin. apply N2. destruct (HN Xne) as (qn & nn & HINn). destruct (FBn qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as [Enn _].
        apply (proj2 (in_block_In _ _)). exists (qn, hd_addr F2, nn).
        split; [apply in_or_app; right; subst FB; apply in_or_app; right; right; exact HINn| unfold cb_addr, cb_size; cbn [fst snd]; subst nn; unfold FILE_ALLOC; lia]. }
    assert (BF : forall a, in_block (CL ++ FB) a -> 0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x55000 <= a) /\ (a < utp R - 200 \/ utp R - 200 + 4096 <= a)).
    { intros a Ha. exact (in_block_facts (utp R) _ a BO Ha). }
    (* [comment removed for export] *)
    assert (HSt : forall a, GI.stdio_static a -> ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8) -> P4 a).
    { intros a Hs Hn. unfold GI.stdio_static, A_OFL_HEAD in *. subst P4. cbn beta.
      split; [lia|]. split; [lia|]. split; [exact Hn|]. split.
      - intros (Xne & Xr). destruct (HL Xne) as (ql & nl & HINl).
        destruct (BKF ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as (_ & _ & K3 & _). (keep_hyps CEILV hptr R F1 F2 m4 A a Hs Xr K3; lia).
      - intros (Xne & Xr). destruct (HN Xne) as (qn & nn & HINn).
        destruct (BKF qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as (_ & _ & K3 & _). (keep_hyps CEILV hptr R F1 F2 m4 A a Hs Xr K3; lia). }
    (* [comment removed for export] *)
    assert (SR4 : STDIOR (set_files (files_remove eqb (lc_files (ps_libc s)) q) (ps_libc s)) (F1 ++ F2) m4).
    { unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED in *.
      Ltac tra4 AG HSt X := eapply agrees_rw_cells; [exact AG | exact X | intros a Ha; cbn in Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]].
      split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SEbs; intros a Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HSt; [unfold GI.stdio_static; lia| unfold A_OFL_HEAD; lia]. }
      split; [tra4 AG HSt U1|]. split; [tra4 AG HSt U2|]. split; [tra4 AG HSt U3|]. split; [exact OL4|]. split; [exact OH4|].
      split; [| apply (NoDup_files_remove eqb); exact ND].
      subst FB. eapply (files_R_unlink eqb EQB P4); [exact FS| exact ND| exact AG| | exact DIST| exact LP4| exact LN4| lia|].
      - intros q2 A2 n2 a HIN2 Ha Hn1 Hn2.
        assert (HIN2' : In (q2, A2, n2) (F1 ++ (q, A, FILE_ALLOC) :: F2)) by (apply INFB; exact HIN2).
        destruct (BKF _ _ _ HIN2') as (K1 & K2 & K3 & K4).
        assert (NA : A2 <> A).
        { intros E. pose proof (DIST q2 A2 n2 q A FILE_ALLOC HIN2' INb E) as Eq.
          (* [comment removed for export] *)
          pose proof (files_R_toks m 0 _ _ FS) as TK.
          assert (NDT : List.NoDup (map cb_tok (F1 ++ (q, A, FILE_ALLOC) :: F2))) by (rewrite TK; exact ND).
          rewrite map_app in NDT. cbn [map cb_tok fst snd] in NDT. apply List.NoDup_remove_1 in NDT as NDT'.
          apply (List.NoDup_remove_2 _ _ _ NDT). rewrite <- map_app. subst q2.
          change q with (cb_tok (q, A2, n2)). apply in_map. exact HIN2. }
        pose proof (APF _ _ _ _ _ _ HIN2' INb NA) as APA.
        subst P4. cbn beta. unfold A_OFL_HEAD. split; [lia|]. split; [(keep_hyps CEILV hptr R F1 F2 A A2 a Ha APA; lia)|]. split; [(keep_hyps CEILV hptr R F1 F2 A2 a Ha K3; lia)|]. split.
        + intros (Xne & Xr). destruct (HL Xne) as (ql & nl & HINl).
          destruct (Z.eq_dec A2 (last_addr 0 F1)) as [E|NE]; [apply Hn1; split; [exact E| lia]|].
          pose proof (APF _ _ _ _ _ _ HIN2' (INFB _ (in_or_app F1 F2 _ (or_introl HINl))) NE) as AP. (keep_hyps CEILV hptr R F1 F2 m4 A2 a Ha Xr AP; lia).
        + intros (Xne & Xr). destruct (HN Xne) as (qn & nn & HINn).
          destruct (Z.eq_dec A2 (hd_addr F2)) as [E|NE]; [apply Hn2; split; [exact E| lia]|].
          pose proof (APF _ _ _ _ _ _ HIN2' (INFB _ (in_or_app F1 F2 _ (or_intror HINn))) NE) as AP. (keep_hyps CEILV hptr R F1 F2 m4 A2 a Ha Xr AP; lia).
      - intros q2 A2 n2 HIN2. destruct (BKF _ _ _ HIN2) as (K1 & _). lia. }
    split.
    - (* [comment removed for export] *)
      unfold GIo, set_libc. cbn [ps_heap ps_libc ps_outfile ps_tls].
      assert (PERM : Permutation.Permutation (CL ++ FB) ((CL ++ [(q, A, FILE_ALLOC)]) ++ (F1 ++ F2))).
      { subst FB. rewrite <- app_assoc. apply Permutation.Permutation_app_head. cbn [app].
        apply Permutation.Permutation_sym. apply Permutation.Permutation_middle. }
      split.
      { eapply HPL; [| exact PERM].
        eapply HFL; [exact HH| exact MU| exact WM|].
        apply Forall_forall. intros [lo' hi'] Hiv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as X. unfold heap_client_iv. cbn [fst snd] in *.
        destruct X as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]].
        + left; lia.
        + right; left. unfold iv_in_block. apply Exists_exists. exists (q, A, FILE_ALLOC).
          split; [apply in_or_app; right; exact INb | unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
        + right; right; left. unfold A_OFL_HEAD in X. lia.
        + right; left. destruct (HL Xne) as (ql & nl & HINl). destruct (FBn ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as [Enl _].
          unfold iv_in_block. apply Exists_exists. exists (ql, last_addr 0 F1, nl).
          split; [apply in_or_app; right; subst FB; apply in_or_app; left; exact HINl| unfold cb_addr, cb_size; cbn [fst snd]; subst nl; unfold FILE_ALLOC; lia].
        + right; left. destruct (HN Xne) as (qn & nn & HINn). destruct (FBn qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as [Enn _].
          unfold iv_in_block. apply Exists_exists. exists (qn, hd_addr F2, nn).
          split; [apply in_or_app; right; subst FB; apply in_or_app; right; right; exact HINn| unfold cb_addr, cb_size; cbn [fst snd]; subst nn; unfold FILE_ALLOC; lia]. }
      split; [apply (proj2 (KST _ R _ m4)); exact SR4|].
      split. { subst FB. eapply HARNR_remove; [exact NOF|]. eapply HARNR_agree; [| |exact HA]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split. { eapply CORE_TLS_agree; [| |exact CT]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| clear - Hp TBC; (keep_hyps CEILV R a TBC Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R a Hp H1; lia)| (keep_hyps CEILV R A a TBI Hp; lia)| (keep_hyps CEILV R A a TBI Hp; lia)]. }
      split. { eapply PCAP_TLS_agree; [| |exact PT]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split. { eapply CORE_LIBC_agree; [| |exact CLI]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R a Hp H1; lia)| (keep_hyps CEILV R a Hp; lia)| (keep_hyps CEILV R a Hp; lia)]. }
      split. { eapply CORE_MISC_agree; [| |exact CM]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R a Hp H1; lia)| (keep_hyps CEILV R a Hp; lia)| (keep_hyps CEILV R a Hp; lia)]. }
      split. { eapply CORE_EXIT_agree; [| |exact CE]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R a Hp H1; lia)| (keep_hyps CEILV R a Hp; lia)| (keep_hyps CEILV R a Hp; lia)]. }
      split. { eapply CORE_STK_agree; [| |exact CS]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split; [exact Etls|]. split; [exact TB|]. split; [| exact SPW].
      eapply blocks_ok_perm; [exact PERM| exact BOK].
    - (* [comment removed for export] *)
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hk.
      eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd].
      destruct Hk as [Hk|Hk].
      + destruct Hiv as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]]; cbn [fst snd] in *; [lia| lia| unfold A_OFL_HEAD in X; lia| |].
        * destruct (HL Xne) as (ql & nl & HINl). destruct (BKF ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as (_ & K2 & _). lia.
        * destruct (HN Xne) as (qn & nn & HINn). destruct (BKF qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as (_ & K2 & _). lia.
      + pose proof (in_block_facts (utp R) CL a BOCL Hk) as (G1 & G2 & G3 & G4).
        apply in_block_In in Hk as ([[qb Ab] nb] & HbIn & Hb). unfold cb_addr, cb_size in Hb. cbn [fst snd] in Hb.
        assert (APb : forall q2 A2 n2, In (q2, A2, n2) FB -> Ab + nb <= A2 \/ A2 + 1264 <= Ab).
        { intros q2 A2 n2 HIN2. destruct (FBn _ _ _ HIN2) as [-> _].
          pose proof (BAX (qb, Ab, nb) (q2, A2, FILE_ALLOC) HbIn HIN2) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. exact AP. }
        destruct Hiv as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]]; cbn [fst snd].
        * cbn [fst snd] in X. lia.
        * cbn [fst snd] in X. pose proof (APb _ _ _ INb). (keep_hyps CEILV R A a Ab nb lo' hi' Hb X H0; lia).
        * cbn [fst snd] in X. unfold A_OFL_HEAD in X. lia.
        * cbn [fst snd] in X1, X2. destruct (HL Xne) as (ql & nl & HINl). pose proof (APb ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)). (keep_hyps CEILV hptr R F1 F2 m4 a Ab nb lo' hi' Hb X1 X2 H0; lia).
        * cbn [fst snd] in X1, X2. destruct (HN Xne) as (qn & nn & HINn). pose proof (APb qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)). (keep_hyps CEILV hptr R F1 F2 m4 a Ab nb lo' hi' Hb X1 X2 H0; lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma libc_need_locks : forall R m, CORE_LIBC R m -> rw_cells ssegs m NEED_LOCKS [C1 (Z_to_bv 8 0)].
  Proof using Type. pin_using tt.
    intros R m (LC & _). unfold libc_cells in LC.
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in LC as [_ LC]. apply (proj1 (rw_cells_app ssegs m _ [_] _)) in LC as [_ LC].
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in LC as [_ LC]. apply (proj1 (rw_cells_app ssegs m _ [_] _)) in LC as [NL _].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in NL. unfold NEED_LOCKS. exact NL.
  Qed.

  Theorem fclose_o_proof : fclose_stmt_o HO K.
  Proof using EQB FREE8K HFL HPL KST. pin_using (fun (EQB FREE8K HFL HPL KST : unit) => tt).
    intros until lo. intros SPO -> NOF.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK, FILE_BLOCK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof BOK as [BO BA]. pose proof BO as BO'. apply Forall_app in BO' as [BOCL BOFB].
    pose proof (blocks_apart_app_inv _ _ BA) as (BAc & BAf & BAX).
    pose proof (blocks_apart_app_inv _ _ BAf) as (BA1 & BA2 & BAX12). cbn [blocks_apart] in BA2. destruct BA2 as [APfF2 BA2'].
    (* [comment removed for export] *)
    destruct (files_R_mid eqb EQB m 0 _ F1 F2 f Af FILE_ALLOC FS ND) as (fm & LK & INf & _ & A0 & Ahi & FR & INV & HPV & HNX).
    remember (last_addr 0 F1) as pv eqn:Epv. remember (hd_addr F2) as nx eqn:Enx.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof INV as (ICH & IFD & IBS & INN & INW & INR & IRB). rewrite ICH in FLperm.
    (* [comment removed for export] *)
    assert (BKF : forall q2 A2 n2, In (q2, A2, n2) (F1 ++ (f, Af, FILE_ALLOC) :: F2) ->
              0 < A2 /\ A2 + n2 <= CEILZ /\ (A2 + n2 <= 0x10000 \/ 0x55000 <= A2) /\ (A2 + n2 <= utp R - 200 \/ utp R - 200 + 4096 <= A2) /\ n2 = FILE_ALLOC).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m 0 _ _ q2 A2 n2 FS ND HIN) as (f' & pv' & nx' & _ & _ & En & B0 & _).
      pose proof (proj1 (Forall_forall _ _) BOFB _ HIN) as (K1 & K2 & K3 & K4 & K5 & K6).
      unfold cb_addr, cb_size in K1, K2, K3, K4, K5, K6. cbn [fst snd] in K1, K2, K3, K4, K5, K6. subst n2. unfold FILE_ALLOC in *. lia. }
    pose proof (BKF f Af FILE_ALLOC ltac:(apply in_or_app; right; left; reflexivity)) as (FK1 & FK2 & FK3 & FK4 & _). unfold FILE_ALLOC in FK2, FK3, FK4.
    assert (PVF : pv <> 0 -> (pv + 1264 <= Af \/ Af + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x55000 <= pv) /\ 0 < pv).
    { intros NE. assert (NE1 : F1 <> []) by (intros E; apply NE; rewrite Epv, E; reflexivity).
      destruct (last_addr_In 0 F1 NE1) as (ql & nl & HINl). rewrite <- Epv in HINl.
      destruct (BKF ql pv nl ltac:(apply in_or_app; left; exact HINl)) as (K1 & K2 & K3 & K4 & ->).
      pose proof (BAX12 _ _ HINl (or_introl eq_refl)) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP.
      unfold rc_lo, FILE_ALLOC in *. lia. }
    assert (NXF : nx <> 0 -> (nx + 1264 <= Af \/ Af + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x55000 <= nx) /\ 0 < nx).
    { intros NE. assert (NE2 : F2 <> []) by (intros E; apply NE; rewrite Enx, E; reflexivity).
      destruct (hd_addr_In F2 NE2) as (qn & nn & HINn). rewrite <- Enx in HINn.
      destruct (BKF qn nx nn ltac:(apply in_or_app; right; right; exact HINn)) as (K1 & K2 & K3 & K4 & ->).
      pose proof (proj1 (Forall_forall _ _) APfF2 _ HINn) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP.
      unfold rc_lo, FILE_ALLOC in *. (keep_hyps CEILV sp m R Af lo nx LOR SPWu__ K1 K3 K2 AP; lia). }
    assert (PN : pv <> 0 -> nx <> 0 -> pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx).
    { intros NE NE'. assert (NE1 : F1 <> []) by (intros E; apply NE; rewrite Epv, E; reflexivity).
      assert (NE2 : F2 <> []) by (intros E; apply NE'; rewrite Enx, E; reflexivity).
      destruct (last_addr_In 0 F1 NE1) as (ql & nl & HINl). rewrite <- Epv in HINl.
      destruct (hd_addr_In F2 NE2) as (qn & nn & HINn). rewrite <- Enx in HINn.
      destruct (BKF ql pv nl ltac:(apply in_or_app; left; exact HINl)) as (_ & _ & _ & _ & ->).
      destruct (BKF qn nx nn ltac:(apply in_or_app; right; right; exact HINn)) as (_ & _ & _ & _ & ->).
      pose proof (BAX12 _ _ HINl (or_intror HINn)) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
    assert (PV0 : 0 <= pv) by (destruct (Z.eq_dec pv 0) as [E|NE]; [lia| destruct (PVF NE); lia]).
    assert (PVHI : pv + 1264 < 2^63) by (destruct (Z.eq_dec pv 0) as [E|NE]; [lia| destruct (PVF NE); unfold rc_lo in *; lia]).
    assert (NX0 : 0 <= nx) by (destruct (Z.eq_dec nx 0) as [E|NE]; [lia| destruct (NXF NE); lia]).
    assert (NXHI : nx + 1264 < 2^63) by (destruct (Z.eq_dec nx 0) as [E|NE]; [lia| destruct (NXF NE); unfold rc_lo in *; lia]).
    assert (HDR : 0 <= hd_addr (F1 ++ (f, Af, FILE_ALLOC) :: F2) < 2^64).
    { destruct F1 as [|[[q1 A1] n1] F1']; cbn [hd_addr app]; [lia|].
      destruct (BKF q1 A1 n1 ltac:(left; reflexivity)) as (K1 & K2 & K3 & K4 & En). rewrite En in K2. unfold FILE_ALLOC in K2. lia. }
    pose proof (libc_need_locks R m CLI) as NL.
    destruct SSP as [GOT GUARD].
    (* [comment removed for export] *)
    unfold s_fclose, Stdio.fclose.
    eapply implM_lookup_file; [exact LK|].
    eapply implM_evt.
    { eapply (fclose_S1 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo); [lia| exact ST| exact MI]. }
    cbv beta. intros ms1 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    name_sp sp (-48).
    Ltac tr1 H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn; unfold got_ssp, ssp_guard, A_OFL_LOCK, A_OFL_HEAD, NEED_LOCKS; lia].
    assert (FC1 : rw_cells ssegs m1 Af (fcells flags rp (rp + zlength (f_rbuf fm)) F_STDIO_CLOSE
              (if f_wactive fm then Af + FILE_BUF_OFF + f_bufsize fm else 0) (if f_wactive fm then Af + FILE_BUF_OFF + zlength (f_wbuf fm) else 0) (if f_wactive fm then Af + FILE_BUF_OFF else 0)
              F_STDIO_READ (wfn_of fm) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode (lbf_of fm) tail)).
    { eapply rw_cells_transport; [exact FC| exact MU1| exact WM1|]. unfold fcells. rewrite file_cells_size. cbn. lia. }
    assert (BUF1 : rw_cells ssegs m1 (Af + FILE_BUF_OFF) [CB (Z.to_nat (f_bufsize fm)) bufbytes]).
    { eapply rw_cells_transport; [exact BUF| exact MU1| exact WM1|]. rewrite IBS. unfold BUFSIZ, FILE_BUF_OFF. cbn. lia. }
    assert (SSP1 : ssp_cells m1 (rc_canary R)) by (split; [tr1 GOT MU1 WM1| tr1 GUARD MU1 WM1]).
    (* [comment removed for export] *)
    apply implM_bind_assoc.
    eapply implM_bind.
    { rewrite <- Hsp in ST1.
      eapply (fflush_spec (St:=PS)) with (f := fm) (Fp := Af) (flags := flags) (rp := rp) (closefn := F_STDIO_CLOSE) (readfn := F_STDIO_READ)
          (B := Af + FILE_BUF_OFF) (prev := pv) (next := nx) (mode := mode) (tail := tail) (bufbytes := bufbytes) (lo := lo) (canary := rc_canary R);
        first [ exact FC1 | exact FLsvb | exact BUF1 | exact BP | exact WB0 | exact WBL | intros _; exact ICH | exact RP0 | exact RPHI | reflexivity
              | rewrite ICH; exact IFD | exact ST1 | exact SSP1 | exact MI1
              | rewrite ?IBS; unfold FFLUSH_DEPTH, BUFSIZ, FILE_BUF_OFF, got_ssp, ssp_guard; rewrite ?Hsp; unfold rc_lo in *; (keep_hyps CEILV sp R lo LOB LOR SPWu__ SPM SP47 Af A0 FK2 FK3; lia)
              | match goal with |- ?g => idtac "FF side:" g end ]. }
    cbv beta. intros f1 st2 ms2 (-> & TRI & PO2).
    destruct PO2 as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & mode2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
    unfold ff_W, FFLUSH_DEPTH in MU2. rewrite Hsp in MU2, ST2.
    replace (ret_pc (Z_to_bv 64 0x1ab74)) with (Z_to_bv 64 0x1ab74 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof TRI as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & _).
    subst sp0.
    (* [comment removed for export] *)
    eapply implM_bind.
    { eapply implM_evt.
      { eapply (fclose_S2 sp gp (rc_tp R) s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af); [exact FC2| exact MI2]. }
      cbv beta. intros ms3 ->. rewrite T1.
      eapply (stdio_close_spec (St:=PS)) with (fd := f_fd fm) (lo := lo); first [unfold fcells in FC2; exact FC2 | reflexivity | exact IFD | exact ST2 | exact MI2 | rewrite ?unsigned_lit by lia; first [exact ST2 | lia]
              | match goal with |- ?g => idtac "CL side:" g end]. }
    cbv beta. intros [] st3 ms3 (-> & PO3).
    destruct PO3 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    rewrite ?unsigned_lit in MU3, ST3 by lia.
    replace (ret_pc (Z_to_bv 64 0x1ab9c)) with (Z_to_bv 64 0x1ab9c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply implM_upd_lc.
    (* [comment removed for export] *)
    assert (MU13 : munch [(lo, bv_unsigned sp); (Af, Af + 232)] m m3).
    { apply (munch_trans _ m m1 m3); [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia|].
      apply (munch_trans _ m1 m2 m3); [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros; (keep_hyps CEILV sp R Af lo pv nx x LOB H0; lia). }
    assert (WM13 : wmono ssegs m m3) by (eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]).
    assert (FC3 : rw_cells ssegs m3 Af (fclose_cells flags F_STDIO_CLOSE F_STDIO_READ (wfn_of f1) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode2 (lbf_of f1) tail)).
    { apply fclose_cells_recast; [| exact GLN]. unfold fcells in FC2. eapply rw_cells_transport; [exact FC2| exact MU3| exact WM3| rewrite file_cells_size; cbn; lia]. }
    assert (NL3 : rw_cells ssegs m3 NEED_LOCKS [C1 (Z_to_bv 8 0)]) by (tr1 NL MU13 WM13).
    assert (OL3 : rw_cells ssegs m3 A_OFL_LOCK [C4 (Z_to_bv 64 0)]) by (tr1 OL MU13 WM13).
    assert (OH3 : rw_cells ssegs m3 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ (f, Af, FILE_ALLOC) :: F2)))]) by (tr1 OH MU13 WM13).
    assert (FR3 : rw_cells ssegs m3 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport ssegs [(lo, bv_unsigned sp + -48); (Af, Af + 232)] m1 m3); [exact FR1| | |].
      - apply (munch_trans _ m1 m2 m3); [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros; (keep_hyps CEILV sp R Af lo pv nx x LOB H0; lia).
      - eapply wmono_trans; [exact WM2| exact WM3].
      - cbn. lia. }
    assert (PVC3 : pv <> 0 -> rw_cells ssegs m3 (pv + 112) [C8 (Z_to_bv 64 Af)]).
    { intros NE. destruct (PVF NE) as (P1 & P2 & P3 & P4). destruct (HPV ltac:(intros E; apply NE; rewrite Epv, E; reflexivity)) as [PC _].
      eapply rw_cells_transport; [exact PC| exact MU13| exact WM13| cbn; lia]. }
    assert (NXC3 : nx <> 0 -> rw_cells ssegs m3 (nx + 104) [C8 (Z_to_bv 64 Af)]).
    { intros NE. destruct (NXF NE) as (N1 & N2 & N3 & N4). destruct (HNX ltac:(intros E; apply NE; rewrite Enx, E; reflexivity)) as [NC _].
      eapply rw_cells_transport; [exact NC| exact MU13| exact WM13| cbn; lia]. }
    (* [comment removed for export] *)
    eapply implM_evt with (P := fun ms' => implM ssegs (pfree HO f) _ _ ms'); [| intros ms' X; exact X].
    { eapply evt_cut.
      { eapply (fclose_S3a sp gp (rc_tp R) s2 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo); [lia| lia| lia| exact FC3| exact FLperm| exact NL3| exact ST3| exact MI3]. }
      cbv beta. intros ms4 PO4. destruct PO4 as (x1' & a1' & a2' & a3' & m4 & -> & MU4 & WM4 & MI4 & ST4).
      assert (MU4' : munch (fcW sp pv nx) m3 m4).
      { eapply munch_weaken; [| exact MU4]. unfold sub_fp, fcW. cbn [outside]. intros x (O1 & _). split; [exact O1| exact I]. }
      assert (FC4 : rw_cells ssegs m4 Af (fclose_cells flags F_STDIO_CLOSE F_STDIO_READ (wfn_of f1) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode2 (lbf_of f1) tail)).
      { eapply rw_cells_transport; [exact FC3| exact MU4| exact WM4| unfold fclose_cells; cbn; lia]. }
      assert (OL4 : rw_cells ssegs m4 A_OFL_LOCK [C4 (Z_to_bv 64 0)]) by (tr1 OL3 MU4 WM4).
      assert (OH4 : rw_cells ssegs m4 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ (f, Af, FILE_ALLOC) :: F2)))]) by (tr1 OH3 MU4 WM4).
      assert (PVC4 : pv <> 0 -> rw_cells ssegs m4 (pv + 112) [C8 (Z_to_bv 64 Af)]).
      { intros NE. destruct (PVF NE) as (P1 & P2 & P3 & P4). eapply rw_cells_transport; [exact (PVC3 NE)| exact MU4| exact WM4| cbn; lia]. }
      assert (NXC4 : nx <> 0 -> rw_cells ssegs m4 (nx + 104) [C8 (Z_to_bv 64 Af)]).
      { intros NE. destruct (NXF NE) as (N1 & N2 & N3 & N4). eapply rw_cells_transport; [exact (NXC3 NE)| exact MU4| exact WM4| cbn; lia]. }
      eapply evt_cut.
      { eapply (fclose_S3b sp gp (rc_tp R) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo FK3 flags mode2 F_STDIO_READ (wfn_of f1) (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) (lbf_of f1) tail m3 PV0 PVHI PVF NXF PN);
          [exact FC4| exact PVC4| exact NXC4| exact OH4| exact ST4| exact MU4'| exact WM4| exact MI4]. }
      cbv beta. intros ms5 PO5. destruct PO5 as (m5 & -> & FC5 & PVC5 & NXC5 & OH5 & ST5 & MU5 & WM5 & MI5).
      eapply evt_cut.
      { eapply (fclose_S3c sp gp (rc_tp R) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo FK3 flags mode2 F_STDIO_READ (wfn_of f1) (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) (lbf_of f1) tail m3 NX0 NXHI PVF NXF PN);
          [exact FC5| exact PVC5| exact NXC5| exact OH5| exact ST5| exact MU5| exact WM5| exact MI5]. }
      cbv beta. intros ms6 PO6. destruct PO6 as (a1'' & m6 & -> & FC6 & PVC6 & NXC6 & OH6 & ST6 & MU6 & WM6 & MI6).
      eapply evt_cut.
      { eapply (fclose_S3d sp gp (rc_tp R) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo ltac:(lia) A0 ltac:(lia) FK3 flags mode2 F_STDIO_READ (wfn_of f1) (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) (lbf_of f1) tail m3 PVHI NXHI PVF NXF PN);
          [exact FC6| exact PVC6| exact NXC6| exact OH6| exact HDR| exact ST6| exact MU6| exact WM6| exact MI6]. }
      cbv beta. intros ms7 PO7. destruct PO7 as (a0'' & m7 & -> & FC7 & PVC7 & NXC7 & OH7 & ST7 & MU7 & WM7 & MI7).
      unfold fcW in MU7.
      assert (OL7 : rw_cells ssegs m7 A_OFL_LOCK [C4 (Z_to_bv 64 0)]).
      { eapply rw_cells_transport; [exact OL3| exact MU7| exact WM7|]. cbn. unfold A_OFL_LOCK, A_OFL_HEAD. destruct (pv =? 0); destruct (nx =? 0); (keep_hyps CEILV sp R Af lo pv nx LOR LOB SPW PVF NXF; lia). }
      eapply evt_cut. { eapply (fclose_S3e sp gp (rc_tp R) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo); [lia| lia| lia| exact FC7| exact OL7| exact MI7]. }
      cbv beta. intros ms8 PO8. destruct PO8 as (b1 & b2 & b3 & b4 & b5 & ->). apply evt_done.
      (* [comment removed for export] *)
      assert (MUT : munch [(lo, bv_unsigned sp); (Af, Af + 232); (bv_unsigned sp - 64, bv_unsigned sp - 48);
                           (pv + 112, pv + (if pv =? 0 then 112 else 120)); (nx + 104, nx + (if nx =? 0 then 104 else 112));
                           (A_OFL_HEAD, A_OFL_HEAD + 8)] m m7).
      { apply (munch_trans _ m m3 m7); [eapply munch_weaken; [| exact MU13]| eapply munch_weaken; [| exact MU7]];
          unfold sub_fp; cbn [outside]; intros x Hx; destruct (pv =? 0); destruct (nx =? 0); (keep_hyps CEILV sp R Af lo pv nx x Hx; lia). }
      assert (WMT : wmono ssegs m m7) by (eapply wmono_trans; [exact WM13| exact WM7]).
      assert (NE1 : F1 <> [] -> pv <> 0).
      { intros NE E. destruct (last_addr_In 0 F1 NE) as (ql & nl & HINl). rewrite <- Epv, E in HINl.
        destruct (BKF ql 0 nl ltac:(apply in_or_app; left; exact HINl)) as (K1 & _). lia. }
      assert (NE2 : F2 <> [] -> nx <> 0).
      { intros NE E. destruct (hd_addr_In F2 NE) as (qn & nn & HINn). rewrite <- Enx, E in HINn.
        destruct (BKF qn 0 nn ltac:(apply in_or_app; right; right; exact HINn)) as (K1 & _). lia. }
      assert (OH7' : rw_cells ssegs m7 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ F2)))]).
      { destruct F1 as [|[[q1 A1] n1] F1']; cbn [hd_addr app] in OH7 |- *.
        - rewrite Z.eqb_refl in OH7. rewrite <- Enx. exact OH7.
        - replace (A1 =? Af) with false in OH7; [exact OH7|]. symmetry. apply Z.eqb_neq.
          pose proof (BAX12 (q1, A1, n1) (f, Af, FILE_ALLOC) ltac:(left; reflexivity) ltac:(left; reflexivity)) as AP.
          destruct (BKF q1 A1 n1 ltac:(left; reflexivity)) as (_ & _ & _ & _ & ->).
          unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. (keep_hyps CEILV sp R A1 Af lo pv nx AP; lia). }
      assert (LP7 : F1 <> [] -> rw_cells ssegs m7 (last_addr 0 F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]).
      { intros NE. rewrite <- Epv, <- Enx. exact (PVC7 (NE1 NE)). }
      assert (LN7 : F2 <> [] -> rw_cells ssegs m7 (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr 0 F1))]).
      { intros NE. rewrite <- Epv, <- Enx. exact (NXC7 (NE2 NE)). }
      assert (HWT : Forall (fun iv : Z * Z => snd iv <= fst iv \/ (CEILZ <= fst iv /\ snd iv <= bv_unsigned sp) \/ (Af <= fst iv /\ snd iv <= Af + 1264)
                              \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                              \/ (F1 <> [] /\ fst iv = last_addr 0 F1 + 112 /\ snd iv = last_addr 0 F1 + 120)
                              \/ (F2 <> [] /\ fst iv = hd_addr F2 + 104 /\ snd iv = hd_addr F2 + 112))
                [(lo, bv_unsigned sp); (Af, Af + 232); (bv_unsigned sp - 64, bv_unsigned sp - 48);
                 (pv + 112, pv + (if pv =? 0 then 112 else 120)); (nx + 104, nx + (if nx =? 0 then 104 else 112)); (A_OFL_HEAD, A_OFL_HEAD + 8)]).
      { apply Forall_cons; [cbn [fst snd]; right; left; unfold rc_lo in *; lia|].
        apply Forall_cons; [cbn [fst snd]; right; right; left; lia|].
        apply Forall_cons; [cbn [fst snd]; right; left; unfold rc_lo in *; lia|].
        apply Forall_cons.
        { cbn [fst snd]. destruct (Z.eqb_spec pv 0) as [E|NE]; [left; lia|]. right; right; right; right; left.
          split; [intros EF; apply NE; rewrite Epv, EF; reflexivity|]. rewrite <- Epv. split; reflexivity. }
        apply Forall_cons.
        { cbn [fst snd]. destruct (Z.eqb_spec nx 0) as [E|NE]; [left; lia|]. right; right; right; right; right.
          split; [intros EF; apply NE; rewrite Enx, EF; reflexivity|]. rewrite <- Enx. split; reflexivity. }
        apply Forall_cons; [cbn [fst snd]; right; right; right; left; split; reflexivity| apply Forall_nil]. }
      destruct (fclose_finish R s CL F1 F2 m m7 _ f Af (bv_unsigned sp) G NOF MUT WMT HWT ltac:(unfold rc_lo in *; lia) SPM OL7 OH7' LP7 LN7) as [G7 AG7].
      (* [comment removed for export] *)
      assert (FR7 : rw_cells ssegs m7 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rw_cells_transport; [exact FR3| exact MU7| exact WM7|]. cbn. unfold A_OFL_HEAD.
        destruct (Z.eqb_spec pv 0) as [E|NE]; [| destruct (PVF NE) as (P1 & P2 & P3 & P4)];
        destruct (Z.eqb_spec nx 0) as [E'|NE']; try destruct (NXF NE') as (N1 & N2 & N3 & N4); (keep_hyps CEILV sp R lo pv nx LOR LOB SPW E E' N2 P2; lia). }
      name_sp sp (-48).
      eapply implM_post_evt.
      { pose proof FREE8K as FK. unfold free_stmt_8k in FK. unfold FREE_ENTRY'.
        eapply FK with (C1 := CL) (C2 := []) (n := FILE_ALLOC) (lo := lo); [| reflexivity].
        split; [exact G7|]. split; [rewrite Hsp; exact ST7|]. split; [exact LOR|]. split; [rewrite Hsp; lia|]. split; [rewrite Hsp; lia|].
        split; [exact MI7|]. split; [reflexivity|]. rewrite Hsp. apply aln16_add; [exact AL| reflexivity]. }
      cbv beta. intros [] st9 ms9 PO9. destruct PO9 as (a0v & m9 & REGS & OF9 & MI9 & ST9 & AG9 & G9).
      unfold hpost_regs in REGS. destruct REGS as (e0 & e1 & e2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & e3 & e4 & e5 & e6 & ->).
      rewrite Hsp in ST9, AG9. subst sp0.
      replace (ret_pc (Z_to_bv 64 FCLOSE_FREE_RA)) with (Z_to_bv 64 FCLOSE_FREE_RA : word) by (unfold FCLOSE_FREE_RA; symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR9 : rw_cells ssegs m9 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply keeps_rw_cells_stack; [exact AG9| exact FR7| lia]).
      eapply evt_mono. { eapply (fclose_S4 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo); [lia| exact FR9| exact ST9| exact MI9]. }
      cbv beta. intros ms10 [-> ST10].
      eexists _, m9. split; [unfold hpost_regs; repeat eexists; reflexivity|].
      split; [destruct s as [xh xl xo xt]; cbn [ps_outfile set_libc] in OF9 |- *; exact OF9|].
      split; [exact MI9|]. split; [exact ST10|].
      split. { eapply agrees_on_trans; [exact AG7|]. eapply client_keeps_weaken; [exact AG9| lia| intros a Ha; rewrite app_nil_r; exact Ha]. }
      rewrite app_nil_r in G9. exact G9. }
  Qed.
End GlueFc.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fmodeflags.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_strchr.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fclose.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.TwB.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section Relink.
  Lemma fcells_split_links : forall flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
    fcells flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl =
    [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 re); C8 (Z_to_bv 64 cf);
     C8 (Z_to_bv 64 we); C8 (Z_to_bv 64 wp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wb);
     C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 wf); C8 (Z_to_bv 64 sf); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bs)]
    ++ [C8 (Z_to_bv 64 pv)] ++ [C8 (Z_to_bv 64 nx)]
    ++ [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
        C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0); CB 80 tl].
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition FILE_R_link_cells__stmt : Prop := forall m f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx ->
    rw_cells usegs m (Fp + 104) [C8 (Z_to_bv 64 pv)] /\ rw_cells usegs m (Fp + 112) [C8 (Z_to_bv 64 nx)].
  Section Sz2.
  Variables m f Fp BA cf rf sf pv nx : ltac2:(SecDiet.SzSec.tyM 'FILE_R_link_cells__stmt "vvvvvvvvv" @m).
  Lemma FILE_R_link_cells__body : ltac2:(SecDiet.SzSec.bodyP 'FILE_R_link_cells__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros (flags & mode & rp & tail & bufbytes & FC & _).
    rewrite fcells_split_links in FC. apply (proj1 (rw_cells_app usegs m Fp _ _)) in FC as [_ FC].
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in FC as [FP FC]. apply (proj1 (rw_cells_app usegs m _ [_] _)) in FC as [FN _].
    cbn [cells_size csize Nat.add] in FP, FN.
    replace (Fp + Z.of_nat 104) with (Fp + 104) in FP by lia.
    replace (Fp + Z.of_nat 104 + Z.of_nat 8) with (Fp + 112) in FN by lia.
    split; [exact FP| exact FN].
  Qed.
  End Sz2.
  Lemma FILE_R_link_cells : ltac:(let t := eval cbv delta [FILE_R_link_cells__stmt] in FILE_R_link_cells__stmt in exact t).
  Proof using Type. intros m f Fp BA cf rf sf pv nx. ltac2:(SecDiet.SzSec.closeP 'FILE_R_link_cells__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition FILE_R_relink__stmt : Prop := forall (P : Z -> Prop) m m' f Fp BA cf rf sf pv nx pv' nx',
    FILE_R m f Fp BA cf rf sf pv nx ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> ~ (Fp + 104 <= a < Fp + 120) -> P a) ->
    (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    rw_cells usegs m' (Fp + 104) [C8 (Z_to_bv 64 pv')] -> rw_cells usegs m' (Fp + 112) [C8 (Z_to_bv 64 nx')] ->
    FILE_R m' f Fp BA cf rf sf pv' nx'.
  Section Sz3.
  Variables P m m' f Fp BA cf rf sf pv nx pv' nx' : ltac2:(SecDiet.SzSec.tyM 'FILE_R_relink__stmt "vvvvvvvvvvvvv" @P).
  Lemma FILE_R_relink__body : ltac2:(SecDiet.SzSec.bodyP 'FILE_R_relink__stmt "vvvvvvvvvvvvv").
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros FR AG HP1 HP2 PC NC.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - rewrite fcells_split_links in FC |- *.
      apply (proj1 (rw_cells_app usegs m Fp _ _)) in FC as [FCa FC]. apply (proj1 (rw_cells_app usegs m _ [_] _)) in FC as [_ FC].
      apply (proj1 (rw_cells_app usegs m _ [_] _)) in FC as [_ FCb].
      cbn [cells_size csize Nat.add] in FCa, FCb |- *.
      apply (proj2 (rw_cells_app usegs m' Fp _ _)). split.
      + eapply agrees_rw_cells; [exact AG| exact FCa|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP1; lia.
      + apply (proj2 (rw_cells_app usegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
        * replace (Fp + Z.of_nat 104) with (Fp + 104) by lia. exact PC.
        * apply (proj2 (rw_cells_app usegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
          -- replace (Fp + Z.of_nat 104 + Z.of_nat 8) with (Fp + 112) by lia. exact NC.
          -- eapply agrees_rw_cells; [exact AG| exact FCb|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP1; lia.
    - pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
      eapply agrees_rw_cells; [exact AG | exact BUF |]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP2. lia.
  Qed.
  End Sz3.
  Lemma FILE_R_relink : ltac:(let t := eval cbv delta [FILE_R_relink__stmt] in FILE_R_relink__stmt in exact t).
  Proof using CEILV. intros P m m' f Fp BA cf rf sf pv nx pv' nx'. ltac2:(SecDiet.SzSec.closeP 'FILE_R_relink__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma FILE_R_relink_same : forall (P : Z -> Prop) m m' f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> P a) -> (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    FILE_R m' f Fp BA cf rf sf pv nx.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros P m m' f Fp BA cf rf sf pv nx FR AG HP1 HP2.
    pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR) as [PC NC].
    eapply FILE_R_relink; [exact FR| exact AG| intros a Ha _; apply HP1; exact Ha| exact HP2| |].
    - eapply agrees_rw_cells; [exact AG| exact PC|]. cbn. intros a Ha. apply HP1. lia.
    - eapply agrees_rw_cells; [exact AG| exact NC|]. cbn. intros a Ha. apply HP1. lia.
  Qed.
End Relink.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Unlink.
  Context {hptr : Type} (ptr_eqb : hptr -> hptr -> bool).
  Hypothesis EQB : forall p q, ptr_eqb p q = true <-> p = q.
  #[local] Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  Fixpoint last_addr (prev : Z) (FB : list cblk) : Z :=
    match FB with [] => prev | (_, A, _) :: FB' => last_addr A FB' end.

  Lemma last_addr_app : forall prev (F1 F2 : list cblk), last_addr prev (F1 ++ F2) = last_addr (last_addr prev F1) F2.
  Proof using Type. pin_using tt. intros prev F1; revert prev. induction F1 as [|[[q A] n] F1 IH]; intros prev F2; cbn; [reflexivity| apply IH]. Qed.

  Lemma last_addr_In : forall prev (FB : list cblk), FB <> [] -> exists q n, In (q, last_addr prev FB, n) FB.
  Proof using Type. pin_using tt.
    intros prev FB; revert prev. induction FB as [|[[q A] n] FB IH]; intros prev NE; [exfalso; exact (NE eq_refl)|].
    cbn. destruct FB as [|b FB'].
    - exists q, n. left. reflexivity.
    - destruct (IH A ltac:(discriminate)) as (q' & n' & HIN). exists q', n'. right. exact HIN.
  Qed.

  Lemma hd_addr_app : forall (F1 F2 : list cblk), F1 <> [] -> hd_addr (F1 ++ F2) = hd_addr F1.
  Proof using Type. pin_using tt. intros [|[[q A] n] F1] F2 NE; [exfalso; exact (NE eq_refl)| reflexivity]. Qed.

  Lemma hd_addr_In : forall (FB : list cblk), FB <> [] -> exists q n, In (q, hd_addr FB, n) FB.
  Proof using Type. pin_using tt. intros [|[[q A] n] FB] NE; [exfalso; exact (NE eq_refl)|]. exists q, n. left. reflexivity. Qed.

  Lemma NoDup_files_remove : forall fs q, List.NoDup (map fst fs) -> List.NoDup (map fst (files_remove ptr_eqb fs q)).
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q ND; cbn; [constructor|].
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    destruct (ptr_eqb k q); [exact ND|]. cbn. constructor; [| apply IH; exact ND].
    intros HIn. apply NI. eapply (files_remove_keys ptr_eqb). exact HIn.
  Qed.

  (* [comment removed for export] *)
  Definition files_R_mid__stmt : Prop := forall m prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    exists f,
      files_lookup ptr_eqb fs q = Some f /\ In (q, f) fs /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK (last_addr prev F1) (hd_addr F2)
      /\ heap_file_inv f
      /\ (F1 <> [] -> rw_cells usegs m (last_addr prev F1 + 112) [C8 (Z_to_bv 64 A)] /\ 0 < last_addr prev F1)
      /\ (F2 <> [] -> rw_cells usegs m (hd_addr F2 + 104) [C8 (Z_to_bv 64 A)] /\ 0 < hd_addr F2).
  Section Sz10.
  Variables m prev fs : ltac2:(SecDiet.SzSec.tyM 'files_R_mid__stmt "vvvk" @m).
  Lemma files_R_mid__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_mid__stmt "vvvk").
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND.
    - cbn [app] in FS. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      exists f. cbn [files_lookup last_addr]. rewrite (eqb_refl' ptr_eqb EQB).
      split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact FR|]. split; [exact INV|]. split; [intros NE; exfalso; exact (NE eq_refl)|].
      intros NE2. destruct F2 as [|[[q2 A2] n2] F2']; [exfalso; exact (NE2 eq_refl)|]. cbn [hd_addr].
      destruct fs' as [|[q2' f2] fs'']; [exact (False_ind _ REST)|]. cbn [files_R] in REST.
      destruct REST as (_ & _ & B0 & _ & FR2 & _). split; [| exact B0].
      exact (proj1 (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR2)).
    - cbn [app] in FS. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A10 & A1hi & FR1 & INV1 & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      destruct (IH A1 fs' F2 q A n REST ND) as (f & LK & INf & En & A0 & Ahi & FR & INV & HP & HN).
      assert (NE : q1 <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact INf).
      exists f. cbn [files_lookup]. rewrite (eqb_neq ptr_eqb EQB _ _ NE).
      split; [exact LK|]. split; [right; exact INf|]. split; [exact En|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact FR|]. split; [exact INV|]. split; [| exact HN].
      intros _. cbn [last_addr]. destruct F1 as [|b F1'].
      + cbn [last_addr app hd_addr] in FR1 |- *. split; [| exact A10]. exact (proj2 (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR1)).
      + apply HP. discriminate.
  Qed.
  End Sz10.
  Lemma files_R_mid : ltac:(let t := eval cbv delta [files_R_mid__stmt] in files_R_mid__stmt in exact t).
  Proof using EQB. intros m prev fs F1. ltac2:(SecDiet.SzSec.closeP 'files_R_mid__body "vvvk"). Qed.

  (* [comment removed for export] *)
  Definition files_remove_mid__stmt : Prop := forall m prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    exists fs1 f fs2, fs = fs1 ++ (q, f) :: fs2 /\ length fs1 = length F1 /\ files_remove ptr_eqb fs q = fs1 ++ fs2.
  Section Sz11.
  Variables m prev fs : ltac2:(SecDiet.SzSec.tyM 'files_remove_mid__stmt "vvvk" @m).
  Lemma files_remove_mid__body : ltac2:(SecDiet.SzSec.bodyP 'files_remove_mid__stmt "vvvk").
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND.
    - cbn [app] in FS. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & _).
      exists [], f, fs'. cbn. rewrite (eqb_refl' ptr_eqb EQB). repeat split; reflexivity.
    - cbn [app] in FS. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & _ & _ & _ & _ & _ & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      destruct (IH A1 fs' F2 q A n REST ND) as (fs1 & f & fs2 & -> & L & RM).
      assert (NE : q1 <> q).
      { intros ->. apply NI. rewrite map_app. apply in_or_app. right. left. reflexivity. }
      exists ((q1, f1) :: fs1), f, fs2. cbn. rewrite (eqb_neq ptr_eqb EQB _ _ NE), RM, L. repeat split; reflexivity.
  Qed.
  End Sz11.
  Lemma files_remove_mid : ltac:(let t := eval cbv delta [files_remove_mid__stmt] in files_remove_mid__stmt in exact t).
  Proof using EQB. intros m prev fs F1. ltac2:(SecDiet.SzSec.closeP 'files_remove_mid__body "vvvk"). Qed.

  (* [comment removed for export] *)
  Definition files_R_unlink__stmt : Prop := forall (P : Z -> Prop) m m' prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    agrees_on P m m' ->
    (forall q2 A2 n2 a, In (q2, A2, n2) (F1 ++ F2) -> A2 <= a < A2 + 1264 ->
          ~ (A2 = last_addr prev F1 /\ A2 + 112 <= a < A2 + 120) -> ~ (A2 = hd_addr F2 /\ A2 + 104 <= a < A2 + 112) -> P a) ->
    (forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) (F1 ++ (q, A, n) :: F2) -> In (q3, A3, n3) (F1 ++ (q, A, n) :: F2) -> A2 = A3 -> q2 = q3) ->
    (F1 <> [] -> rw_cells usegs m' (last_addr prev F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]) ->
    (F2 <> [] -> rw_cells usegs m' (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr prev F1))]) ->
    prev <> A -> (forall q2 A2 n2, In (q2, A2, n2) (F1 ++ (q, A, n) :: F2) -> A2 <> prev) ->
    files_R m' prev (files_remove ptr_eqb fs q) (F1 ++ F2).
  Section Sz12.
  Variables P m m' prev fs : ltac2:(SecDiet.SzSec.tyM 'files_R_unlink__stmt "vvvvvk" @P).
  Lemma files_R_unlink__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_unlink__stmt "vvvvvk").
  Proof using CEILV EQB. pin_using (fun (CEILV EQB : unit) => tt).
    intros F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND AG HP DIST LP LN PA PNA.
    - (* [comment removed for export] *)
      cbn [app] in FS |- *. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      cbn [files_remove]. rewrite (eqb_refl' ptr_eqb EQB).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      cbn [last_addr] in LN, HP.
      destruct F2 as [|[[q2 A2] n2] F2']; destruct fs' as [|[q2' f2] fs'']; try exact (False_ind _ REST); [exact I|].
      cbn [files_R] in REST |- *. destruct REST as (<- & -> & B0 & Bhi & FR2 & INV2 & REST2).
      cbn [hd_addr] in LN, HP.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
      pose proof INV2 as (_ & _ & BS2 & _).
      split.
      { pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR2) as [_ NC2].
        assert (A2P : A2 <> prev) by (eapply (PNA q2 A2 FILE_ALLOC); right; left; reflexivity).
        eapply (FILE_R_relink P); [exact FR2| exact AG| | | exact (LN ltac:(discriminate))|].
        - intros a Ha Hn. eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X) | intros [_ X]; lia].
        - rewrite BS2. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X)| intros [_ X]; lia].
        - eapply agrees_rw_cells; [exact AG| exact NC2|]. cbn. intros a Ha.
          eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X)| intros [_ X]; lia]. }
      split; [exact INV2|].
      eapply files_R_frame; [exact REST2|].
      intros q3 A3 n3 f3 pv3 nx3 HIN3 FR3 INV3. pose proof INV3 as (_ & _ & BS3 & _).
      assert (N3A : A3 <> A2).
      { intros E. pose proof (DIST q3 A3 n3 q2 A2 FILE_ALLOC ltac:(right; right; exact HIN3) ltac:(right; left; reflexivity) E) as Eq.
        subst q3 A3. apply List.NoDup_cons_iff in ND as [NI2 _]. apply NI2.
        pose proof (files_R_toks _ _ _ _ REST2) as TK. pose proof (in_map cb_tok _ _ HIN3) as X. cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
      assert (N3P : A3 <> prev) by (eapply PNA; right; right; exact HIN3).
      eapply (FILE_R_relink_same P); [exact FR3| exact AG| |].
      + intros a Ha. eapply (HP q3 A3 n3 a); [right; exact HIN3| lia| intros [X _]; exact (N3P X)| intros [X _]; exact (N3A X)].
      + rewrite BS3. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q3 A3 n3 a); [right; exact HIN3| lia| intros [X _]; exact (N3P X)| intros [X _]; exact (N3A X)].
    - (* [comment removed for export] *)
      cbn [app] in FS |- *. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A10 & A1hi & FR1 & INV1 & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      pose proof (files_R_mid m A1 fs' F1 F2 q A n REST ND) as (f & _ & INf & _).
      assert (NE : q1 <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact INf).
      cbn [files_remove]. rewrite (eqb_neq ptr_eqb EQB _ _ NE). cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A10|]. split; [exact A1hi|].
      pose proof INV1 as (_ & _ & BS1 & _).
      assert (A1A : A1 <> A).
      { intros E. pose proof (DIST q1 A1 FILE_ALLOC q A n ltac:(left; reflexivity) ltac:(apply in_or_app; right; left; reflexivity) E) as Eq. exact (NE Eq). }
      assert (A1F2 : F2 <> [] -> A1 <> hd_addr F2).
      { intros NE2 E. destruct (hd_addr_In F2 NE2) as (q2 & n2 & HIN2).
        pose proof (DIST q1 A1 FILE_ALLOC q2 (hd_addr F2) n2 ltac:(left; reflexivity) ltac:(apply in_or_app; right; right; exact HIN2) E) as Eq.
        subst q2. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
        pose proof (in_map cb_tok _ _ (in_or_app F1 ((q, A, n) :: F2) (q1, hd_addr F2, n2) (or_intror (or_intror HIN2)))) as X.
        cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
      split.
      { destruct F1 as [|[[q1b A1b] n1b] F1'].
        - (* [comment removed for export] *)
          cbn [last_addr app hd_addr] in FR1, LP |- *.
          pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR1) as [PC1 _].
          eapply (FILE_R_relink P); [exact FR1| exact AG| | | | exact (LP ltac:(discriminate))].
          + intros a Ha Hn. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia|].
            intros [E _]. exact (A1F2 ltac:(intros E2; rewrite E2 in E; cbn in E; lia) E).
          + rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia| intros [_ X]; lia].
          + eapply agrees_rw_cells; [exact AG| exact PC1|]. cbn. intros a Ha.
            eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia|].
            intros [X _]. exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X).
        - (* [comment removed for export] *)
          cbn [last_addr app hd_addr] in FR1 |- *.
          assert (A1L : A1 <> last_addr A1b F1').
          { intros E. destruct (last_addr_In A1b F1' ) as (ql & nl & HINl).
            all: cycle 1.
            { pose proof (DIST q1 A1 FILE_ALLOC ql (last_addr A1b F1') nl ltac:(left; reflexivity) ltac:(right; right; apply in_or_app; left; exact HINl) E) as Eq.
              subst ql. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
              pose proof (in_map cb_tok _ _ (or_intror (in_or_app F1' ((q, A, n) :: F2) (q1, last_addr A1b F1', nl) (or_introl HINl)) : In (q1, last_addr A1b F1', nl) (((q1b, A1b, n1b) :: F1') ++ (q, A, n) :: F2))) as X.
              cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
            (* [comment removed for export] *)
            intros E'. subst F1'. cbn in E.
            pose proof (DIST q1 A1 FILE_ALLOC q1b A1b n1b ltac:(left; reflexivity) ltac:(right; left; reflexivity) E) as Eq.
            subst q1b. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
            pose proof (in_map cb_tok _ _ (or_introl eq_refl : In (q1, A1b, n1b) (((q1, A1b, n1b) :: []) ++ (q, A, n) :: F2))) as X.
            cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
          eapply (FILE_R_relink_same P); [exact FR1| exact AG| |].
          + intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A1L X)| intros [X _]].
            exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X).
          + rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A1L X)| intros [X _]].
            exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X). }
      split; [exact INV1|].
      eapply (IH A1 fs' F2 q A n); [exact REST| exact ND| exact AG| | | intros _; exact (LP ltac:(discriminate))| exact LN| exact A1A|].
      + intros q2 A2 n2 a HIN2. apply (HP q2 A2 n2 a). right. exact HIN2.
      + intros q2 A2 n2 q3 A3 n3 HIN2 HIN3. apply (DIST q2 A2 n2 q3 A3 n3); right; assumption.
      + intros q2 A2 n2 HIN2 E. subst A2.
        pose proof (DIST q1 A1 FILE_ALLOC q2 A1 n2 ltac:(left; reflexivity) ltac:(right; exact HIN2) eq_refl) as Eq. subst q2.
        apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
        pose proof (in_map cb_tok _ _ HIN2) as X. cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK).
  Qed.
  End Sz12.
  Lemma files_R_unlink : ltac:(let t := eval cbv delta [files_R_unlink__stmt] in files_R_unlink__stmt in exact t).
  Proof using CEILV EQB. intros P m m' prev fs F1. ltac2:(SecDiet.SzSec.closeP 'files_R_unlink__body "vvvvvk"). Qed.
End Unlink.

Section GlueFc.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).
  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.spo_facts K KST).
  #[local] Notation GIo_stdio_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.GIo_stdio_step K KST HFL).
  #[local] Notation keeps_of_stdio := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.keeps_of_stdio K).

  (* [comment removed for export] *)
  Definition free_stmt_8k : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (C1 C2 FB : list cblk) (q : hptr) (A n lo : Z),
      std_pre_o K sp tp R s (C1 ++ (q, A, n) :: C2) FB lo 8192 m -> a0 = Z_to_bv 64 A ->
      implM usegs (pfree HO q) s
        (fun _ s' ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ GIo K R s' (C1 ++ C2) FB m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom usegs)).
  Hypothesis FREE8K : free_stmt_8k.

  (* [comment removed for export] *)
  Lemma HARNR_remove : forall (o : option hptr) (F1 F2 : list cblk) q A n m,
    o <> Some q -> HARNR o (F1 ++ (q, A, n) :: F2) m -> HARNR o (F1 ++ F2) m.
  Proof using Type. pin_using tt.
    intros o F1 F2 q A n m NO (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    destruct o as [q'|]; [|exact H3]. destruct H3 as (A' & HIn & HC). exists A'. split; [| exact HC].
    apply in_app_or in HIn. apply in_or_app. destruct HIn as [X|[X|X]]; [left; exact X| | right; exact X].
    exfalso. apply NO. injection X as -> _ _. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma munch_drop_empty : forall (W : list (Z * Z)) m m', munch W m m' -> munch (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W) m m'.
  Proof using Type. pin_using tt.
    intros W m m' MU. eapply munch_weaken; [| exact MU]. unfold sub_fp. clear MU.
    induction W as [|[lo hi] W IH]; intros x Hx; cbn in *; [exact I|].
    destruct (lo <? hi) eqn:E; cbn in Hx.
    - destruct Hx as [H1 H2]. split; [exact H1| apply IH; exact H2].
    - apply Z.ltb_ge in E. split; [lia| apply IH; exact Hx].
  Qed.
  Lemma Forall_drop_empty : forall (Q : Z * Z -> Prop) W,
    Forall (fun iv => snd iv <= fst iv \/ Q iv) W -> Forall Q (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W).
  Proof using Type. pin_using tt.
    intros Q W HF. induction HF as [|iv W HQ HF IH]; cbn; [constructor|].
    destruct (fst iv <? snd iv) eqn:E; [| exact IH]. apply Z.ltb_lt in E.
    constructor; [| exact IH]. destruct HQ as [HQ|HQ]; [lia| exact HQ].
  Qed.

  (* [comment removed for export] *)
  Lemma fclose_finish : forall R (s : PS) (CL F1 F2 : list cblk) m m4 W q A SP,
    GIo K R s CL (F1 ++ (q, A, FILE_ALLOC) :: F2) m ->
    ps_outfile s <> Some q ->
    munch W m m4 -> wmono usegs m m4 ->
    Forall (fun iv : Z * Z => snd iv <= fst iv \/ (CEILZ <= fst iv /\ snd iv <= SP) \/ (A <= fst iv /\ snd iv <= A + 1264)
                              \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                              \/ (F1 <> [] /\ fst iv = last_addr 0 F1 + 112 /\ snd iv = last_addr 0 F1 + 120)
                              \/ (F2 <> [] /\ fst iv = hd_addr F2 + 104 /\ snd iv = hd_addr F2 + 112)) W ->
    CEILZ <= SP -> SP <= rc_spmain R ->
    rw_cells usegs m4 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells usegs m4 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ F2)))] ->
    (F1 <> [] -> rw_cells usegs m4 (last_addr 0 F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]) ->
    (F2 <> [] -> rw_cells usegs m4 (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr 0 F1))]) ->
    GIo K R (set_libc (set_files (files_remove eqb (lc_files (ps_libc s)) q) (ps_libc s)) s) (CL ++ [(q, A, FILE_ALLOC)]) (F1 ++ F2) m4
    /\ agrees_on (client_keeps CL SP) m m4.
  Proof using EQB HFL HPL KST. pin_using (fun (EQB HFL HPL KST : unit) => tt).
    intros R s CL F1 F2 m m4 W0 q A SP G NOF MU0 WM HW0 CSP HSP OL4 OH4 LP4 LN4.
    pose proof (munch_drop_empty _ _ _ MU0) as MU. pose proof (Forall_drop_empty _ _ HW0) as HW. cbv beta in HW.
    remember (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W0) as W eqn:EW. clear EW MU0 HW0.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA].
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold rc_spmain in HSP.
    apply (proj1 (KST _ R _ _)) in HS as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    set (FB := F1 ++ (q, A, FILE_ALLOC) :: F2) in *.
    assert (INb : In (q, A, FILE_ALLOC) FB) by (subst FB; apply in_or_app; right; left; reflexivity).
    assert (INFB : forall b, In b (F1 ++ F2) -> In b FB).
    { intros b Hb. subst FB. apply in_app_or in Hb. apply in_or_app. destruct Hb as [X|X]; [left; exact X| right; right; exact X]. }
    pose proof BO as BO'. apply Forall_app in BO' as [BOCL BOFB].
    pose proof (blocks_apart_app_inv _ _ BA) as (BAc & BAf & BAX).
    (* [comment removed for export] *)
    assert (FBn : forall q2 A2 n2, In (q2, A2, n2) FB -> n2 = FILE_ALLOC /\ 0 < A2).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m 0 _ FB q2 A2 n2 FS ND HIN) as (f & pv & nx & _ & _ & En & B0 & _). split; [exact En| exact B0]. }
    assert (BKF : forall q2 A2 n2, In (q2, A2, n2) FB ->
              0 < A2 /\ A2 + 1264 <= CEILZ /\ (A2 + 1264 <= 0x10000 \/ 0x56000 <= A2) /\ (A2 + 1264 <= utp R - 200 \/ utp R - 200 + 4096 <= A2)).
    { intros q2 A2 n2 HIN. destruct (FBn _ _ _ HIN) as [-> B0].
      pose proof (proj1 (Forall_forall _ _) BOFB _ HIN) as (K1 & K2 & K3 & K4 & K5 & K6).
      unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3, K4, K5, K6 |- *. cbn [fst snd] in K1, K2, K3, K4, K5, K6. lia. }
    (* [comment removed for export] *)
    assert (APF : forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) FB -> In (q3, A3, n3) FB -> A2 <> A3 -> A2 + 1264 <= A3 \/ A3 + 1264 <= A2).
    { intros q2 A2 n2 q3 A3 n3 HIN2 HIN3 NE. destruct (FBn _ _ _ HIN2) as [-> _]. destruct (FBn _ _ _ HIN3) as [-> _].
      destruct (blocks_apart_In _ _ _ BAf HIN2 HIN3) as [E|AP]; [exfalso; apply NE; injection E as E1 E2; exact E2|].
      unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. exact AP. }
    assert (DIST : forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) FB -> In (q3, A3, n3) FB -> A2 = A3 -> q2 = q3).
    { intros q2 A2 n2 q3 A3 n3 HIN2 HIN3 E. destruct (FBn _ _ _ HIN2) as [-> _]. destruct (FBn _ _ _ HIN3) as [-> _].
      destruct (blocks_apart_In _ _ _ BAf HIN2 HIN3) as [E'|AP]; [injection E' as E1 E2; exact E1|].
      unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
    pose proof (BKF _ _ _ INb) as (BK1 & BK2 & BK3 & BK4).
    (* [comment removed for export] *)
    assert (HL : F1 <> [] -> exists ql nl, In (ql, last_addr 0 F1, nl) F1) by (intros NE; exact (last_addr_In 0 F1 NE)).
    assert (HN : F2 <> [] -> exists qn nn, In (qn, hd_addr F2, nn) F2) by (intros NE; exact (hd_addr_In F2 NE)).
    (* [comment removed for export] *)
    set (P4 := fun a : Z => ~ (CEILZ <= a < SP) /\ ~ (A <= a < A + 1264) /\ ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8)
                            /\ ~ (F1 <> [] /\ last_addr 0 F1 + 112 <= a < last_addr 0 F1 + 120)
                            /\ ~ (F2 <> [] /\ hd_addr F2 + 104 <= a < hd_addr F2 + 112)).
    assert (AG : agrees_on P4 m m4).
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha (N1 & N2 & N3 & N4 & N5).
      eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd] in Hiv |- *.
      destruct Hiv as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]]; [(keep_hyps CEILV R A SP a lo' hi' N1 X; lia)| (keep_hyps CEILV R A SP a lo' hi' N2 X; lia)| (keep_hyps CEILV R A SP a lo' hi' N3 X; lia)| |].
      - intros Hin. apply N4. split; [exact Xne| lia].
      - intros Hin. apply N5. split; [exact Xne| lia]. }
    (* [comment removed for export] *)
    assert (OUT : forall a, 0 <= a < 2^64 ->
              ~ (CEILZ <= a < usp0 R - 48) -> ~ in_block (CL ++ FB) a -> ~ (0x23e20 <= a < 0x240f0) -> ~ (0x54908 <= a < 0x55130) -> outside W a).
    { intros a Ha N1 N2 N3 N4. eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd].
      destruct Hiv as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]]; cbn [fst snd] in *.
      - (keep_hyps CEILV R SP a lo' hi' HSP N1 X; lia).
      - intros Hin. apply N2. apply (proj2 (in_block_In _ _)). exists (q, A, FILE_ALLOC).
        split; [apply in_or_app; right; exact INb| unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
      - unfold A_OFL_HEAD in X. lia.
      - intros Hin. apply N2. destruct (HL Xne) as (ql & nl & HINl). destruct (FBn ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as [Enl _].
        apply (proj2 (in_block_In _ _)). exists (ql, last_addr 0 F1, nl).
        split; [apply in_or_app; right; subst FB; apply in_or_app; left; exact HINl| unfold cb_addr, cb_size; cbn [fst snd]; subst nl; unfold FILE_ALLOC; lia].
      - intros Hin. apply N2. destruct (HN Xne) as (qn & nn & HINn). destruct (FBn qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as [Enn _].
        apply (proj2 (in_block_In _ _)). exists (qn, hd_addr F2, nn).
        split; [apply in_or_app; right; subst FB; apply in_or_app; right; right; exact HINn| unfold cb_addr, cb_size; cbn [fst snd]; subst nn; unfold FILE_ALLOC; lia]. }
    assert (BF : forall a, in_block (CL ++ FB) a -> 0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x56000 <= a) /\ (a < utp R - 200 \/ utp R - 200 + 4096 <= a)).
    { intros a Ha. exact (in_block_facts (utp R) _ a BO Ha). }
    (* [comment removed for export] *)
    assert (HSt : forall a, S3.GI.TwB.stdio_static a -> ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8) -> P4 a).
    { intros a Hs Hn. unfold S3.GI.TwB.stdio_static, A_OFL_HEAD in *. subst P4. cbn beta.
      split; [lia|]. split; [lia|]. split; [exact Hn|]. split.
      - intros (Xne & Xr). destruct (HL Xne) as (ql & nl & HINl).
        destruct (BKF ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as (_ & _ & K3 & _). (keep_hyps CEILV hptr R F1 F2 m4 A a Hs Xr K3; lia).
      - intros (Xne & Xr). destruct (HN Xne) as (qn & nn & HINn).
        destruct (BKF qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as (_ & _ & K3 & _). (keep_hyps CEILV hptr R F1 F2 m4 A a Hs Xr K3; lia). }
    (* [comment removed for export] *)
    assert (SR4 : STDIOR (set_files (files_remove eqb (lc_files (ps_libc s)) q) (ps_libc s)) (F1 ++ F2) m4).
    { unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED in *.
      Ltac tra4 AG HSt X := eapply agrees_rw_cells; [exact AG | exact X | intros a Ha; cbn in Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]].
      split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SEbs; intros a Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HSt; [unfold S3.GI.TwB.stdio_static; lia| unfold A_OFL_HEAD; lia]. }
      split; [tra4 AG HSt U1|]. split; [tra4 AG HSt U2|]. split; [tra4 AG HSt U3|]. split; [exact OL4|]. split; [exact OH4|].
      split; [| apply (NoDup_files_remove eqb); exact ND].
      subst FB. eapply (files_R_unlink eqb EQB P4); [exact FS| exact ND| exact AG| | exact DIST| exact LP4| exact LN4| lia|].
      - intros q2 A2 n2 a HIN2 Ha Hn1 Hn2.
        assert (HIN2' : In (q2, A2, n2) (F1 ++ (q, A, FILE_ALLOC) :: F2)) by (apply INFB; exact HIN2).
        destruct (BKF _ _ _ HIN2') as (K1 & K2 & K3 & K4).
        assert (NA : A2 <> A).
        { intros E. pose proof (DIST q2 A2 n2 q A FILE_ALLOC HIN2' INb E) as Eq.
          (* [comment removed for export] *)
          pose proof (files_R_toks m 0 _ _ FS) as TK.
          assert (NDT : List.NoDup (map cb_tok (F1 ++ (q, A, FILE_ALLOC) :: F2))) by (rewrite TK; exact ND).
          rewrite map_app in NDT. cbn [map cb_tok fst snd] in NDT. apply List.NoDup_remove_1 in NDT as NDT'.
          apply (List.NoDup_remove_2 _ _ _ NDT). rewrite <- map_app. subst q2.
          change q with (cb_tok (q, A2, n2)). apply in_map. exact HIN2. }
        pose proof (APF _ _ _ _ _ _ HIN2' INb NA) as APA.
        subst P4. cbn beta. unfold A_OFL_HEAD. split; [lia|]. split; [(keep_hyps CEILV hptr R F1 F2 A A2 a Ha APA; lia)|]. split; [(keep_hyps CEILV hptr R F1 F2 A2 a Ha K3; lia)|]. split.
        + intros (Xne & Xr). destruct (HL Xne) as (ql & nl & HINl).
          destruct (Z.eq_dec A2 (last_addr 0 F1)) as [E|NE]; [apply Hn1; split; [exact E| lia]|].
          pose proof (APF _ _ _ _ _ _ HIN2' (INFB _ (in_or_app F1 F2 _ (or_introl HINl))) NE) as AP. (keep_hyps CEILV hptr R F1 F2 m4 A2 a Ha Xr AP; lia).
        + intros (Xne & Xr). destruct (HN Xne) as (qn & nn & HINn).
          destruct (Z.eq_dec A2 (hd_addr F2)) as [E|NE]; [apply Hn2; split; [exact E| lia]|].
          pose proof (APF _ _ _ _ _ _ HIN2' (INFB _ (in_or_app F1 F2 _ (or_intror HINn))) NE) as AP. (keep_hyps CEILV hptr R F1 F2 m4 A2 a Ha Xr AP; lia).
      - intros q2 A2 n2 HIN2. destruct (BKF _ _ _ HIN2) as (K1 & _). lia. }
    split.
    - (* [comment removed for export] *)
      unfold GIo, set_libc. cbn [ps_heap ps_libc ps_outfile ps_tls].
      assert (PERM : Permutation.Permutation (CL ++ FB) ((CL ++ [(q, A, FILE_ALLOC)]) ++ (F1 ++ F2))).
      { subst FB. rewrite <- app_assoc. apply Permutation.Permutation_app_head. cbn [app].
        apply Permutation.Permutation_sym. apply Permutation.Permutation_middle. }
      split.
      { eapply HPL; [| exact PERM].
        eapply HFL; [exact HH| exact MU| exact WM|].
        apply Forall_forall. intros [lo' hi'] Hiv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as X. unfold heap_client_iv. cbn [fst snd] in *.
        destruct X as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]].
        + left; lia.
        + right; left. unfold iv_in_block. apply Exists_exists. exists (q, A, FILE_ALLOC).
          split; [apply in_or_app; right; exact INb | unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
        + right; right; left. unfold A_OFL_HEAD in X. lia.
        + right; left. destruct (HL Xne) as (ql & nl & HINl). destruct (FBn ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as [Enl _].
          unfold iv_in_block. apply Exists_exists. exists (ql, last_addr 0 F1, nl).
          split; [apply in_or_app; right; subst FB; apply in_or_app; left; exact HINl| unfold cb_addr, cb_size; cbn [fst snd]; subst nl; unfold FILE_ALLOC; lia].
        + right; left. destruct (HN Xne) as (qn & nn & HINn). destruct (FBn qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as [Enn _].
          unfold iv_in_block. apply Exists_exists. exists (qn, hd_addr F2, nn).
          split; [apply in_or_app; right; subst FB; apply in_or_app; right; right; exact HINn| unfold cb_addr, cb_size; cbn [fst snd]; subst nn; unfold FILE_ALLOC; lia]. }
      split; [apply (proj2 (KST _ R _ m4)); exact SR4|].
      split. { subst FB. eapply HARNR_remove; [exact NOF|]. eapply HARNR_agree; [| |exact HA]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split. { eapply CORE_TLS_agree; [| |exact CT]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| clear - Hp TBC; (keep_hyps CEILV R a TBC Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R a Hp H1; lia)| (keep_hyps CEILV R A a TBI Hp; lia)| (keep_hyps CEILV R A a TBI Hp; lia)]. }
      split. { eapply PCAP_TLS_agree; [| |exact PT]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split. { eapply CORE_LIBC_agree; [| |exact CLI]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R a Hp H1; lia)| (keep_hyps CEILV R a Hp; lia)| (keep_hyps CEILV R a Hp; lia)]. }
      split. { eapply CORE_MISC_agree; [| |exact CM]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R a Hp H1; lia)| (keep_hyps CEILV R a Hp; lia)| (keep_hyps CEILV R a Hp; lia)]. }
      split. { eapply CORE_EXIT_agree; [| |exact CE]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| (keep_hyps CEILV R a Hp; lia)| intros Hb; destruct (BF a Hb); (keep_hyps CEILV R a Hp H1; lia)| (keep_hyps CEILV R a Hp; lia)| (keep_hyps CEILV R a Hp; lia)]. }
      split. { eapply CORE_STK_agree; [| |exact CS]. 2:{ intros a Hp; exact Hp. }
               eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
               apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
      split; [exact Etls|]. split; [exact TB|]. split; [| exact SPW].
      eapply blocks_ok_perm; [exact PERM| exact BOK].
    - (* [comment removed for export] *)
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hk.
      eapply outside_of_Forall; [exact HW|]. intros [lo' hi'] Hiv; cbn [fst snd].
      destruct Hk as [Hk|Hk].
      + destruct Hiv as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]]; cbn [fst snd] in *; [lia| lia| unfold A_OFL_HEAD in X; lia| |].
        * destruct (HL Xne) as (ql & nl & HINl). destruct (BKF ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as (_ & K2 & _). lia.
        * destruct (HN Xne) as (qn & nn & HINn). destruct (BKF qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as (_ & K2 & _). lia.
      + pose proof (in_block_facts (utp R) CL a BOCL Hk) as (G1 & G2 & G3 & G4).
        apply in_block_In in Hk as ([[qb Ab] nb] & HbIn & Hb). unfold cb_addr, cb_size in Hb. cbn [fst snd] in Hb.
        assert (APb : forall q2 A2 n2, In (q2, A2, n2) FB -> Ab + nb <= A2 \/ A2 + 1264 <= Ab).
        { intros q2 A2 n2 HIN2. destruct (FBn _ _ _ HIN2) as [-> _].
          pose proof (BAX (qb, Ab, nb) (q2, A2, FILE_ALLOC) HbIn HIN2) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. exact AP. }
        destruct Hiv as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]]; cbn [fst snd].
        * cbn [fst snd] in X. lia.
        * cbn [fst snd] in X. pose proof (APb _ _ _ INb). (keep_hyps CEILV R A a Ab nb lo' hi' Hb X H0; lia).
        * cbn [fst snd] in X. unfold A_OFL_HEAD in X. lia.
        * cbn [fst snd] in X1, X2. destruct (HL Xne) as (ql & nl & HINl). pose proof (APb ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)). (keep_hyps CEILV hptr R F1 F2 m4 a Ab nb lo' hi' Hb X1 X2 H0; lia).
        * cbn [fst snd] in X1, X2. destruct (HN Xne) as (qn & nn & HINn). pose proof (APb qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)). (keep_hyps CEILV hptr R F1 F2 m4 a Ab nb lo' hi' Hb X1 X2 H0; lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma libc_need_locks : forall R m, CORE_LIBC R m -> rw_cells usegs m NEED_LOCKS [C1 (Z_to_bv 8 0)].
  Proof using Type. pin_using tt.
    intros R m (LC & _). unfold libc_cells in LC.
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in LC as [_ LC]. apply (proj1 (rw_cells_app usegs m _ [_] _)) in LC as [_ LC].
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in LC as [_ LC]. apply (proj1 (rw_cells_app usegs m _ [_] _)) in LC as [NL _].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in NL. unfold NEED_LOCKS. exact NL.
  Qed.

  Theorem fclose_o_proof : fclose_stmt_o HO K.
  Proof using EQB FREE8K HFL HPL KST. pin_using (fun (EQB FREE8K HFL HPL KST : unit) => tt).
    intros until lo. intros SPO -> NOF.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK, FILE_BLOCK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof BOK as [BO BA]. pose proof BO as BO'. apply Forall_app in BO' as [BOCL BOFB].
    pose proof (blocks_apart_app_inv _ _ BA) as (BAc & BAf & BAX).
    pose proof (blocks_apart_app_inv _ _ BAf) as (BA1 & BA2 & BAX12). cbn [blocks_apart] in BA2. destruct BA2 as [APfF2 BA2'].
    (* [comment removed for export] *)
    destruct (files_R_mid eqb EQB m 0 _ F1 F2 f Af FILE_ALLOC FS ND) as (fm & LK & INf & _ & A0 & Ahi & FR & INV & HPV & HNX).
    remember (last_addr 0 F1) as pv eqn:Epv. remember (hd_addr F2) as nx eqn:Enx.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof INV as (ICH & IFD & IBS & INN & INW & INR & IRB). rewrite ICH in FLperm.
    (* [comment removed for export] *)
    assert (BKF : forall q2 A2 n2, In (q2, A2, n2) (F1 ++ (f, Af, FILE_ALLOC) :: F2) ->
              0 < A2 /\ A2 + n2 <= CEILZ /\ (A2 + n2 <= 0x10000 \/ 0x56000 <= A2) /\ (A2 + n2 <= utp R - 200 \/ utp R - 200 + 4096 <= A2) /\ n2 = FILE_ALLOC).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m 0 _ _ q2 A2 n2 FS ND HIN) as (f' & pv' & nx' & _ & _ & En & B0 & _).
      pose proof (proj1 (Forall_forall _ _) BOFB _ HIN) as (K1 & K2 & K3 & K4 & K5 & K6).
      unfold cb_addr, cb_size in K1, K2, K3, K4, K5, K6. cbn [fst snd] in K1, K2, K3, K4, K5, K6. subst n2. unfold FILE_ALLOC in *. lia. }
    pose proof (BKF f Af FILE_ALLOC ltac:(apply in_or_app; right; left; reflexivity)) as (FK1 & FK2 & FK3 & FK4 & _). unfold FILE_ALLOC in FK2, FK3, FK4.
    assert (PVF : pv <> 0 -> (pv + 1264 <= Af \/ Af + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x56000 <= pv) /\ 0 < pv).
    { intros NE. assert (NE1 : F1 <> []) by (intros E; apply NE; rewrite Epv, E; reflexivity).
      destruct (last_addr_In 0 F1 NE1) as (ql & nl & HINl). rewrite <- Epv in HINl.
      destruct (BKF ql pv nl ltac:(apply in_or_app; left; exact HINl)) as (K1 & K2 & K3 & K4 & ->).
      pose proof (BAX12 _ _ HINl (or_introl eq_refl)) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP.
      unfold rc_lo, FILE_ALLOC in *. lia. }
    assert (NXF : nx <> 0 -> (nx + 1264 <= Af \/ Af + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x56000 <= nx) /\ 0 < nx).
    { intros NE. assert (NE2 : F2 <> []) by (intros E; apply NE; rewrite Enx, E; reflexivity).
      destruct (hd_addr_In F2 NE2) as (qn & nn & HINn). rewrite <- Enx in HINn.
      destruct (BKF qn nx nn ltac:(apply in_or_app; right; right; exact HINn)) as (K1 & K2 & K3 & K4 & ->).
      pose proof (proj1 (Forall_forall _ _) APfF2 _ HINn) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP.
      unfold rc_lo, FILE_ALLOC in *. (keep_hyps CEILV sp m R Af lo nx LOR SPWu__ K1 K3 K2 AP; lia). }
    assert (PN : pv <> 0 -> nx <> 0 -> pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx).
    { intros NE NE'. assert (NE1 : F1 <> []) by (intros E; apply NE; rewrite Epv, E; reflexivity).
      assert (NE2 : F2 <> []) by (intros E; apply NE'; rewrite Enx, E; reflexivity).
      destruct (last_addr_In 0 F1 NE1) as (ql & nl & HINl). rewrite <- Epv in HINl.
      destruct (hd_addr_In F2 NE2) as (qn & nn & HINn). rewrite <- Enx in HINn.
      destruct (BKF ql pv nl ltac:(apply in_or_app; left; exact HINl)) as (_ & _ & _ & _ & ->).
      destruct (BKF qn nx nn ltac:(apply in_or_app; right; right; exact HINn)) as (_ & _ & _ & _ & ->).
      pose proof (BAX12 _ _ HINl (or_intror HINn)) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
    assert (PV0 : 0 <= pv) by (destruct (Z.eq_dec pv 0) as [E|NE]; [lia| destruct (PVF NE); lia]).
    assert (PVHI : pv + 1264 < 2^63) by (destruct (Z.eq_dec pv 0) as [E|NE]; [lia| destruct (PVF NE); unfold rc_lo in *; lia]).
    assert (NX0 : 0 <= nx) by (destruct (Z.eq_dec nx 0) as [E|NE]; [lia| destruct (NXF NE); lia]).
    assert (NXHI : nx + 1264 < 2^63) by (destruct (Z.eq_dec nx 0) as [E|NE]; [lia| destruct (NXF NE); unfold rc_lo in *; lia]).
    assert (HDR : 0 <= hd_addr (F1 ++ (f, Af, FILE_ALLOC) :: F2) < 2^64).
    { destruct F1 as [|[[q1 A1] n1] F1']; cbn [hd_addr app]; [lia|].
      destruct (BKF q1 A1 n1 ltac:(left; reflexivity)) as (K1 & K2 & K3 & K4 & En). rewrite En in K2. unfold FILE_ALLOC in K2. lia. }
    pose proof (libc_need_locks R m CLI) as NL.
    destruct SSP as [GOT GUARD].
    (* [comment removed for export] *)
    unfold s_fclose, Stdio.fclose.
    eapply implM_lookup_file; [exact LK|].
    eapply implM_evt.
    { eapply (fclose_S1 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo); [lia| exact ST| exact MI]. }
    cbv beta. intros ms1 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    name_sp sp (-48).
    Ltac tr1 H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn; unfold got_ssp, ssp_guard, A_OFL_LOCK, A_OFL_HEAD, NEED_LOCKS; lia].
    assert (FC1 : rw_cells usegs m1 Af (fcells flags rp (rp + zlength (f_rbuf fm)) F_STDIO_CLOSE
              (if f_wactive fm then Af + FILE_BUF_OFF + f_bufsize fm else 0) (if f_wactive fm then Af + FILE_BUF_OFF + zlength (f_wbuf fm) else 0) (if f_wactive fm then Af + FILE_BUF_OFF else 0)
              F_STDIO_READ (wfn_of fm) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode (lbf_of fm) tail)).
    { eapply rw_cells_transport; [exact FC| exact MU1| exact WM1|]. unfold fcells. rewrite file_cells_size. cbn. lia. }
    assert (BUF1 : rw_cells usegs m1 (Af + FILE_BUF_OFF) [CB (Z.to_nat (f_bufsize fm)) bufbytes]).
    { eapply rw_cells_transport; [exact BUF| exact MU1| exact WM1|]. rewrite IBS. unfold BUFSIZ, FILE_BUF_OFF. cbn. lia. }
    assert (SSP1 : ssp_cells m1 (rc_canary R)) by (split; [tr1 GOT MU1 WM1| tr1 GUARD MU1 WM1]).
    (* [comment removed for export] *)
    apply implM_bind_assoc.
    eapply implM_bind.
    { rewrite <- Hsp in ST1.
      eapply (fflush_spec (St:=PS)) with (f := fm) (Fp := Af) (flags := flags) (rp := rp) (closefn := F_STDIO_CLOSE) (readfn := F_STDIO_READ)
          (B := Af + FILE_BUF_OFF) (prev := pv) (next := nx) (mode := mode) (tail := tail) (bufbytes := bufbytes) (lo := lo) (canary := rc_canary R);
        first [ exact FC1 | exact FLsvb | exact BUF1 | exact BP | exact WB0 | exact WBL | intros _; exact ICH | exact RP0 | exact RPHI | reflexivity
              | rewrite ICH; exact IFD | exact ST1 | exact SSP1 | exact MI1
              | rewrite ?IBS; unfold FFLUSH_DEPTH, BUFSIZ, FILE_BUF_OFF, got_ssp, ssp_guard; rewrite ?Hsp; unfold rc_lo in *; (keep_hyps CEILV sp R lo LOB LOR SPWu__ SPM SP47 Af A0 FK2 FK3; lia)
              | match goal with |- ?g => idtac "FF side:" g end ]. }
    cbv beta. intros f1 st2 ms2 (-> & TRI & PO2).
    destruct PO2 as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & mode2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
    unfold ff_W, FFLUSH_DEPTH in MU2. rewrite Hsp in MU2, ST2.
    replace (ret_pc (Z_to_bv 64 0x1b334)) with (Z_to_bv 64 0x1b334 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof TRI as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & _).
    subst sp0.
    (* [comment removed for export] *)
    eapply implM_bind.
    { eapply implM_evt.
      { eapply (fclose_S2 sp gp (rc_tp R) s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af); [exact FC2| exact MI2]. }
      cbv beta. intros ms3 ->. rewrite T1.
      eapply (stdio_close_spec (St:=PS)) with (fd := f_fd fm) (lo := lo); first [unfold fcells in FC2; exact FC2 | reflexivity | exact IFD | exact ST2 | exact MI2 | rewrite ?unsigned_lit by lia; first [exact ST2 | lia]
              | match goal with |- ?g => idtac "CL side:" g end]. }
    cbv beta. intros [] st3 ms3 (-> & PO3).
    destruct PO3 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    rewrite ?unsigned_lit in MU3, ST3 by lia.
    replace (ret_pc (Z_to_bv 64 0x1b35c)) with (Z_to_bv 64 0x1b35c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply implM_upd_lc.
    (* [comment removed for export] *)
    assert (MU13 : munch [(lo, bv_unsigned sp); (Af, Af + 232)] m m3).
    { apply (munch_trans _ m m1 m3); [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia|].
      apply (munch_trans _ m1 m2 m3); [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros; (keep_hyps CEILV sp R Af lo pv nx x LOB H0; lia). }
    assert (WM13 : wmono usegs m m3) by (eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]).
    assert (FC3 : rw_cells usegs m3 Af (fclose_cells flags F_STDIO_CLOSE F_STDIO_READ (wfn_of f1) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode2 (lbf_of f1) tail)).
    { apply fclose_cells_recast; [| exact GLN]. unfold fcells in FC2. eapply rw_cells_transport; [exact FC2| exact MU3| exact WM3| rewrite file_cells_size; cbn; lia]. }
    assert (NL3 : rw_cells usegs m3 NEED_LOCKS [C1 (Z_to_bv 8 0)]) by (tr1 NL MU13 WM13).
    assert (OL3 : rw_cells usegs m3 A_OFL_LOCK [C4 (Z_to_bv 64 0)]) by (tr1 OL MU13 WM13).
    assert (OH3 : rw_cells usegs m3 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ (f, Af, FILE_ALLOC) :: F2)))]) by (tr1 OH MU13 WM13).
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport usegs [(lo, bv_unsigned sp + -48); (Af, Af + 232)] m1 m3); [exact FR1| | |].
      - apply (munch_trans _ m1 m2 m3); [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros; (keep_hyps CEILV sp R Af lo pv nx x LOB H0; lia).
      - eapply wmono_trans; [exact WM2| exact WM3].
      - cbn. lia. }
    assert (PVC3 : pv <> 0 -> rw_cells usegs m3 (pv + 112) [C8 (Z_to_bv 64 Af)]).
    { intros NE. destruct (PVF NE) as (P1 & P2 & P3 & P4). destruct (HPV ltac:(intros E; apply NE; rewrite Epv, E; reflexivity)) as [PC _].
      eapply rw_cells_transport; [exact PC| exact MU13| exact WM13| cbn; lia]. }
    assert (NXC3 : nx <> 0 -> rw_cells usegs m3 (nx + 104) [C8 (Z_to_bv 64 Af)]).
    { intros NE. destruct (NXF NE) as (N1 & N2 & N3 & N4). destruct (HNX ltac:(intros E; apply NE; rewrite Enx, E; reflexivity)) as [NC _].
      eapply rw_cells_transport; [exact NC| exact MU13| exact WM13| cbn; lia]. }
    (* [comment removed for export] *)
    eapply implM_evt with (P := fun ms' => implM usegs (pfree HO f) _ _ ms'); [| intros ms' X; exact X].
    { eapply evt_cut.
      { eapply (fclose_S3a sp gp (rc_tp R) s2 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo); [lia| lia| lia| exact FC3| exact FLperm| exact NL3| exact ST3| exact MI3]. }
      cbv beta. intros ms4 PO4. destruct PO4 as (x1' & a1' & a2' & a3' & m4 & -> & MU4 & WM4 & MI4 & ST4).
      assert (MU4' : munch (fcW sp pv nx) m3 m4).
      { eapply munch_weaken; [| exact MU4]. unfold sub_fp, fcW. cbn [outside]. intros x (O1 & _). split; [exact O1| exact I]. }
      assert (FC4 : rw_cells usegs m4 Af (fclose_cells flags F_STDIO_CLOSE F_STDIO_READ (wfn_of f1) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode2 (lbf_of f1) tail)).
      { eapply rw_cells_transport; [exact FC3| exact MU4| exact WM4| unfold fclose_cells; cbn; lia]. }
      assert (OL4 : rw_cells usegs m4 A_OFL_LOCK [C4 (Z_to_bv 64 0)]) by (tr1 OL3 MU4 WM4).
      assert (OH4 : rw_cells usegs m4 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ (f, Af, FILE_ALLOC) :: F2)))]) by (tr1 OH3 MU4 WM4).
      assert (PVC4 : pv <> 0 -> rw_cells usegs m4 (pv + 112) [C8 (Z_to_bv 64 Af)]).
      { intros NE. destruct (PVF NE) as (P1 & P2 & P3 & P4). eapply rw_cells_transport; [exact (PVC3 NE)| exact MU4| exact WM4| cbn; lia]. }
      assert (NXC4 : nx <> 0 -> rw_cells usegs m4 (nx + 104) [C8 (Z_to_bv 64 Af)]).
      { intros NE. destruct (NXF NE) as (N1 & N2 & N3 & N4). eapply rw_cells_transport; [exact (NXC3 NE)| exact MU4| exact WM4| cbn; lia]. }
      eapply evt_cut.
      { eapply (fclose_S3b sp gp (rc_tp R) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo FK3 flags mode2 F_STDIO_READ (wfn_of f1) (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) (lbf_of f1) tail m3 PV0 PVHI PVF NXF PN);
          [exact FC4| exact PVC4| exact NXC4| exact OH4| exact ST4| exact MU4'| exact WM4| exact MI4]. }
      cbv beta. intros ms5 PO5. destruct PO5 as (m5 & -> & FC5 & PVC5 & NXC5 & OH5 & ST5 & MU5 & WM5 & MI5).
      eapply evt_cut.
      { eapply (fclose_S3c sp gp (rc_tp R) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo FK3 flags mode2 F_STDIO_READ (wfn_of f1) (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) (lbf_of f1) tail m3 NX0 NXHI PVF NXF PN);
          [exact FC5| exact PVC5| exact NXC5| exact OH5| exact ST5| exact MU5| exact WM5| exact MI5]. }
      cbv beta. intros ms6 PO6. destruct PO6 as (a1'' & m6 & -> & FC6 & PVC6 & NXC6 & OH6 & ST6 & MU6 & WM6 & MI6).
      eapply evt_cut.
      { eapply (fclose_S3d sp gp (rc_tp R) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo ltac:(lia) A0 ltac:(lia) FK3 flags mode2 F_STDIO_READ (wfn_of f1) (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) (lbf_of f1) tail m3 PVHI NXHI PVF NXF PN);
          [exact FC6| exact PVC6| exact NXC6| exact OH6| exact HDR| exact ST6| exact MU6| exact WM6| exact MI6]. }
      cbv beta. intros ms7 PO7. destruct PO7 as (a0'' & m7 & -> & FC7 & PVC7 & NXC7 & OH7 & ST7 & MU7 & WM7 & MI7).
      unfold fcW in MU7.
      assert (OL7 : rw_cells usegs m7 A_OFL_LOCK [C4 (Z_to_bv 64 0)]).
      { eapply rw_cells_transport; [exact OL3| exact MU7| exact WM7|]. cbn. unfold A_OFL_LOCK, A_OFL_HEAD. destruct (pv =? 0); destruct (nx =? 0); (keep_hyps CEILV sp R Af lo pv nx LOR LOB SPW PVF NXF; lia). }
      eapply evt_cut. { eapply (fclose_S3e sp gp (rc_tp R) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo); [lia| lia| lia| exact FC7| exact OL7| exact MI7]. }
      cbv beta. intros ms8 PO8. destruct PO8 as (b1 & b2 & b3 & b4 & b5 & ->). apply evt_done.
      (* [comment removed for export] *)
      assert (MUT : munch [(lo, bv_unsigned sp); (Af, Af + 232); (bv_unsigned sp - 64, bv_unsigned sp - 48);
                           (pv + 112, pv + (if pv =? 0 then 112 else 120)); (nx + 104, nx + (if nx =? 0 then 104 else 112));
                           (A_OFL_HEAD, A_OFL_HEAD + 8)] m m7).
      { apply (munch_trans _ m m3 m7); [eapply munch_weaken; [| exact MU13]| eapply munch_weaken; [| exact MU7]];
          unfold sub_fp; cbn [outside]; intros x Hx; destruct (pv =? 0); destruct (nx =? 0); (keep_hyps CEILV sp R Af lo pv nx x Hx; lia). }
      assert (WMT : wmono usegs m m7) by (eapply wmono_trans; [exact WM13| exact WM7]).
      assert (NE1 : F1 <> [] -> pv <> 0).
      { intros NE E. destruct (last_addr_In 0 F1 NE) as (ql & nl & HINl). rewrite <- Epv, E in HINl.
        destruct (BKF ql 0 nl ltac:(apply in_or_app; left; exact HINl)) as (K1 & _). lia. }
      assert (NE2 : F2 <> [] -> nx <> 0).
      { intros NE E. destruct (hd_addr_In F2 NE) as (qn & nn & HINn). rewrite <- Enx, E in HINn.
        destruct (BKF qn 0 nn ltac:(apply in_or_app; right; right; exact HINn)) as (K1 & _). lia. }
      assert (OH7' : rw_cells usegs m7 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ F2)))]).
      { destruct F1 as [|[[q1 A1] n1] F1']; cbn [hd_addr app] in OH7 |- *.
        - rewrite Z.eqb_refl in OH7. rewrite <- Enx. exact OH7.
        - replace (A1 =? Af) with false in OH7; [exact OH7|]. symmetry. apply Z.eqb_neq.
          pose proof (BAX12 (q1, A1, n1) (f, Af, FILE_ALLOC) ltac:(left; reflexivity) ltac:(left; reflexivity)) as AP.
          destruct (BKF q1 A1 n1 ltac:(left; reflexivity)) as (_ & _ & _ & _ & ->).
          unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. (keep_hyps CEILV sp R A1 Af lo pv nx AP; lia). }
      assert (LP7 : F1 <> [] -> rw_cells usegs m7 (last_addr 0 F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]).
      { intros NE. rewrite <- Epv, <- Enx. exact (PVC7 (NE1 NE)). }
      assert (LN7 : F2 <> [] -> rw_cells usegs m7 (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr 0 F1))]).
      { intros NE. rewrite <- Epv, <- Enx. exact (NXC7 (NE2 NE)). }
      assert (HWT : Forall (fun iv : Z * Z => snd iv <= fst iv \/ (CEILZ <= fst iv /\ snd iv <= bv_unsigned sp) \/ (Af <= fst iv /\ snd iv <= Af + 1264)
                              \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                              \/ (F1 <> [] /\ fst iv = last_addr 0 F1 + 112 /\ snd iv = last_addr 0 F1 + 120)
                              \/ (F2 <> [] /\ fst iv = hd_addr F2 + 104 /\ snd iv = hd_addr F2 + 112))
                [(lo, bv_unsigned sp); (Af, Af + 232); (bv_unsigned sp - 64, bv_unsigned sp - 48);
                 (pv + 112, pv + (if pv =? 0 then 112 else 120)); (nx + 104, nx + (if nx =? 0 then 104 else 112)); (A_OFL_HEAD, A_OFL_HEAD + 8)]).
      { apply Forall_cons; [cbn [fst snd]; right; left; unfold rc_lo in *; lia|].
        apply Forall_cons; [cbn [fst snd]; right; right; left; lia|].
        apply Forall_cons; [cbn [fst snd]; right; left; unfold rc_lo in *; lia|].
        apply Forall_cons.
        { cbn [fst snd]. destruct (Z.eqb_spec pv 0) as [E|NE]; [left; lia|]. right; right; right; right; left.
          split; [intros EF; apply NE; rewrite Epv, EF; reflexivity|]. rewrite <- Epv. split; reflexivity. }
        apply Forall_cons.
        { cbn [fst snd]. destruct (Z.eqb_spec nx 0) as [E|NE]; [left; lia|]. right; right; right; right; right.
          split; [intros EF; apply NE; rewrite Enx, EF; reflexivity|]. rewrite <- Enx. split; reflexivity. }
        apply Forall_cons; [cbn [fst snd]; right; right; right; left; split; reflexivity| apply Forall_nil]. }
      destruct (fclose_finish R s CL F1 F2 m m7 _ f Af (bv_unsigned sp) G NOF MUT WMT HWT ltac:(unfold rc_lo in *; lia) SPM OL7 OH7' LP7 LN7) as [G7 AG7].
      (* [comment removed for export] *)
      assert (FR7 : rw_cells usegs m7 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rw_cells_transport; [exact FR3| exact MU7| exact WM7|]. cbn. unfold A_OFL_HEAD.
        destruct (Z.eqb_spec pv 0) as [E|NE]; [| destruct (PVF NE) as (P1 & P2 & P3 & P4)];
        destruct (Z.eqb_spec nx 0) as [E'|NE']; try destruct (NXF NE') as (N1 & N2 & N3 & N4); lia. }
      name_sp sp (-48).
      eapply implM_post_evt.
      { pose proof FREE8K as FK. unfold free_stmt_8k in FK. unfold FREE_ENTRY'.
        eapply FK with (C1 := CL) (C2 := []) (n := FILE_ALLOC) (lo := lo); [| reflexivity].
        split; [exact G7|]. split; [rewrite Hsp; exact ST7|]. split; [exact LOR|]. split; [rewrite Hsp; lia|]. split; [rewrite Hsp; lia|].
        split; [exact MI7|]. split; [reflexivity|]. rewrite Hsp. apply aln16_add; [exact AL| reflexivity]. }
      cbv beta. intros [] st9 ms9 PO9. destruct PO9 as (a0v & m9 & REGS & OF9 & MI9 & ST9 & AG9 & G9).
      unfold hpost_regs in REGS. destruct REGS as (e0 & e1 & e2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & e3 & e4 & e5 & e6 & ->).
      rewrite Hsp in ST9, AG9. subst sp0.
      replace (ret_pc (Z_to_bv 64 FCLOSE_FREE_RA)) with (Z_to_bv 64 FCLOSE_FREE_RA : word) by (unfold FCLOSE_FREE_RA; symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR9 : rw_cells usegs m9 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply keeps_rw_cells_stack; [exact AG9| exact FR7| lia]).
      eapply evt_mono. { eapply (fclose_S4 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo); [lia| exact FR9| exact ST9| exact MI9]. }
      cbv beta. intros ms10 [-> ST10].
      eexists _, m9. split; [unfold hpost_regs; repeat eexists; reflexivity|].
      split; [destruct s as [xh xl xo xt]; cbn [ps_outfile set_libc] in OF9 |- *; exact OF9|].
      split; [exact MI9|]. split; [exact ST10|].
      split. { eapply agrees_on_trans; [exact AG7|]. eapply client_keeps_weaken; [exact AG9| lia| intros a Ha; rewrite app_nil_r; exact Ha]. }
      rewrite app_nil_r in G9. exact G9. }
  Qed.
End GlueFc.

End WithCeil.
End TwB.
End Stdio_glue_fc.

(* [comment removed for export] *)
Module Stdio_glue_exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_stdio_exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fc.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.


Section WithCeil.
Context {CEILV : CEIL}.
Definition STDIO_EXIT_FRAME : Z := 160.    (* [comment removed for export] *)

Section GlueExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).

  (* [comment removed for export] *)
  #[local] Definition Pstat (sp : word) (a : Z) : Prop := GI.stdio_static a \/ (bv_unsigned sp - 16 <= a < bv_unsigned sp).

  (* [comment removed for export] *)
  Definition loop_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : PS) (J : Z) (lo : Z) (canary : word) (m : mem) : unit -> PS -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 s0' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 J) fc None m' (seg_rom ssegs)
      /\ agrees_on (Pstat sp) m m' /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp + -16) /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Lemma exit_loop : forall fs (FB : list cblk) (prev : Z) (mi : mem) (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : PS) (lo u : Z) (canary : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    files_R mi prev fs FB -> List.NoDup (map fst fs) ->
    Forall (block_ok u) FB -> blocks_apart FB ->
    stk ssegs mi lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - STDIO_EXIT_FRAME -> CEILZ <= lo ->
    bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
    ssp_cells mi canary -> mem_inv ssegs mi ->
    implM ssegs (close_files fs) st
      (loop_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st 0x1ae94 lo canary mi)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 (hd_addr FB)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (if hd_addr FB =? 0 then 0x1ae94 else EXIT_LOOP)) fc None mi (seg_rom ssegs)).
  Proof using Type. pin_using tt.
    induction fs as [|[q f] fs IH]; intros FB prev mi sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo u canary x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      FS ND BO BA ST LO CLO SP47 SSP MI.
    - destruct FB as [|b FB']; [| exact (False_ind _ FS)]. cbn [hd_addr]. rewrite Z.eqb_refl. cbn [close_files].
      apply implM_ret. apply evt_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [intros a Ha Hp; split; [reflexivity| intros X; exact X]|]. split; [exact MI|]. split; [exact ST| exact SSP].
    - destruct FB as [|[[q' A] n] FB']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      apply Forall_cons_iff in BO as [(K1 & K2 & K3 & K4 & K5 & K6) BO]. unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3, K4, K5, K6. cbn [fst snd] in K1, K2, K3, K4, K5, K6.
      cbn [blocks_apart] in BA. destruct BA as [APA BA].
      cbn [hd_addr]. replace (A =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
      pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
      pose proof INV as (ICH & IFD & IBS & INN & INW & INR & IRB).
      unfold STDIO_EXIT_FRAME in LO.
      cbn [close_files].
      name_sp sp (-16).
      eapply implM_bind.
      { eapply (exit_body sp0 gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st A flags F_STDIO_CLOSE F_STDIO_READ (A + FILE_BUF_OFF) prev (hd_addr FB') tail lo canary mi);
          rewrite ?Hsp; first [ exact FC | exact FLsvb | exact BUF | exact BP | exact WB0 | exact WBL | intros _; exact ICH | exact RP0 | exact RPHI
                               | rewrite ICH; exact IFD | exact ST | exact SSP | exact MI
                               | rewrite ?IBS; unfold EXIT_DEPTH, BUFSIZ, FILE_BUF_OFF, got_ssp, ssp_guard; lia
                               | match goal with |- ?g => idtac "XB side:" g end ]. }
      cbv beta. intros [] st1 ms1 (-> & PO).
      destruct PO as (x1' & v0 & v1 & v2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m' & -> & MU & WM & MI' & ST' & NXC & SSP').
      rewrite Hsp in ST'. unfold ex_W, EXIT_DEPTH in MU. rewrite Hsp in MU.
      (* [comment removed for export] *)
      assert (HDR' : 0 <= hd_addr FB' < 2^64).
      { destruct FB' as [|[[q2 A2] n2] FB'']; cbn [hd_addr]; [lia|]. apply Forall_cons_iff in BO as [(J1 & J2 & J3 & J4 & _) _]. unfold cb_addr, cb_size in J1, J2, J3, J4. cbn [fst snd] in J1, J2, J3, J4. lia. }
      eapply implM_evt. { eapply (exit_next sp0 gp tp); [exact NXC| lia| lia| exact HDR'| exact MI']. }
      cbv beta. intros ms2 ->. subst sp0.
      (* [comment removed for export] *)
      assert (AG : agrees_on (fun a => ~ (bv_unsigned sp - 16 - 144 <= a < bv_unsigned sp - 16) /\ ~ (A <= a < A + 232)) mi m').
      { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [N1 N2]. cbn [outside]. repeat split; lia. }
      assert (REST' : files_R m' A fs FB').
      { eapply files_R_agree; [exact REST| exact AG|]. intros a Hin.
        apply in_block_In in Hin as ([[qb Ab] nb] & HbIn & Hb). unfold cb_addr, cb_size in Hb. cbn [fst snd] in Hb.
        pose proof (proj1 (Forall_forall _ _) BO _ HbIn) as (J1 & J2 & J3 & J4 & _). unfold cb_addr, cb_size in J1, J2, J3, J4. cbn [fst snd] in J1, J2, J3, J4.
        pose proof (proj1 (Forall_forall _ _) APA _ HbIn) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
      eapply implM_mono.
      { eapply (IH FB' A m'); [exact REST'| exact ND| exact BO| exact BA| exact ST'| unfold STDIO_EXIT_FRAME; lia| exact CLO| exact SP47| exact SSP'| exact MI']. }
      cbv beta. intros [] st2 ms3 (-> & PO). destruct_exs PO. destruct PO as (-> & AG2 & MI2 & ST2 & SSP2).
      split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [| split; [exact MI2| split; [exact ST2| exact SSP2]]].
      eapply agrees_on_trans; [| exact AG2]. eapply agrees_on_weaken; [exact AG|].
      intros a [Hs|Hs]; [| lia]. unfold GI.stdio_static in Hs. unfold rc_lo in *. lia.
  Qed.

  Lemma libc_need_locks' : forall m cdt thr sec tm1 auxv th ts ta tc ps loc,
    rw_cells ssegs m 0x53d28 (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) -> rw_cells ssegs m NEED_LOCKS [C1 (Z_to_bv 8 0)].
  Proof using Type. pin_using tt.
    intros until loc. intros LC. unfold libc_cells in LC.
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in LC as [_ LC]. apply (proj1 (rw_cells_app ssegs m _ [_] _)) in LC as [_ LC].
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in LC as [_ LC]. apply (proj1 (rw_cells_app ssegs m _ [_] _)) in LC as [NL _].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in NL. unfold NEED_LOCKS. exact NL.
  Qed.

  Theorem stdio_exit_proof : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.stdio_exit_stmt (s_stdio_exit (H:=H)) (SXGI K) STDIO_EXIT_FRAME.
  Proof using KST. pin_using (fun (KST : unit) => tt).
    intros until loc. intros ST SX LIBCC MI LO CLO SP47.   (* [comment removed for export] *)
    destruct SX as (R & CL & FB & Etp & HH & HS & HA & CT & PT & CLI & CM & Etls & TB & BOK).
    apply (proj1 (KST _ R _ _)) in HS as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof BOK as [BO BA]. apply Forall_app in BO as [BOCL BOFB]. pose proof (blocks_apart_app_inv _ _ BA) as (_ & BAf & _).
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (libc_need_locks' _ _ _ _ _ _ _ _ _ _ _ _ LIBCC) as NL.
    pose proof (core_ssp R m CLI) as SSP.
    subst tp. unfold STDIO_EXIT_FRAME in LO.
    assert (HDR : 0 <= hd_addr FB < 2^64).
    { destruct FB as [|[[q1 A1] n1] FB']; cbn [hd_addr]; [lia|]. apply Forall_cons_iff in BOFB as [(J1 & J2 & J3 & J4 & _) _].
      unfold cb_addr, cb_size in J1, J2, J3, J4. cbn [fst snd] in J1, J2, J3, J4. lia. }
    unfold s_stdio_exit, Stdio.stdio_exit. apply implM_rd_lc.
    (* [comment removed for export] *)
    eapply implM_evt.
    { eapply (exit_entry ra sp gp (rc_tp R) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (hd_addr FB) lo m);
        [exact OH| exact HDR| exact NL| exact ST| lia| lia| exact MI]. }
    cbv beta. intros ms1 PO. destruct PO as (x1 & b0 & b1 & b2 & b3 & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (AG1 : agrees_on (fun a => a < bv_unsigned sp - 32 \/ bv_unsigned sp <= a) m m1).
    { eapply agrees_on_of_munch; [exact MU1| exact WM1|]. intros a Ha Hp. cbn [outside]. split; [lia| exact I]. }
    assert (BKF : forall a, in_block FB a -> 0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x55000 <= a) /\ (a < utp R - 200 \/ utp R - 200 + 4096 <= a))
      by (intros a Ha; exact (in_block_facts (utp R) FB a BOFB Ha)).
    assert (FS1 : files_R m1 0 (lc_files (ps_libc s)) FB).
    { eapply files_R_agree; [exact FS| exact AG1| intros a Ha; destruct (BKF a Ha); lia]. }
    assert (SSP1 : ssp_cells m1 (rc_canary R)).
    { destruct SSP as [G1 G2]. split; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1| unfold got_ssp, ssp_guard; cbn; lia]). }
    (* [comment removed for export] *)
    eapply implM_bind.
    { eapply (exit_loop (lc_files (ps_libc s)) FB 0 m1 sp gp (rc_tp R) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo (utp R) (rc_canary R));
        [exact FS1| exact ND| exact BOFB| exact BAf| exact ST1| unfold STDIO_EXIT_FRAME; lia| exact CLO| exact SP47| exact SSP1| exact MI1]. }
    cbv beta. intros [] st2 ms2 (-> & PO). destruct_exs PO. destruct PO as (-> & AG2 & MI2 & ST2 & SSP2).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    (* [comment removed for export] *)
    assert (AG02 : agrees_on GI.stdio_static m m2).
    { eapply agrees_on_trans; [| eapply agrees_on_weaken; [exact AG2| intros a Ha; left; exact Ha]].
      eapply agrees_on_weaken; [exact AG1|]. intros a Hs. unfold GI.stdio_static in Hs. lia. }
    Ltac trs AG X := eapply agrees_rw_cells; [exact AG | exact X | intros a Ha; unfold GI.stdio_static, A_STDIN_USED, A_STDOUT_USED, A_STDERR_USED, A_STDIN in *; cbn in Ha; lia].
    assert (U22 : rw_cells ssegs m2 A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)]) by (trs AG02 U2).
    assert (U32 : rw_cells ssegs m2 A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)]) by (trs AG02 U3).
    assert (SIN2 : rw_cells ssegs m2 A_STDIN stdin_cells).
    { eapply agrees_rw_cells; [exact AG02| exact SIN|]. unfold stdin_cells. rewrite file_cells_size. intros a Ha. unfold GI.stdio_static, A_STDIN in *. lia. }
    pose proof SOI as (OCH & OFD & OBS & ONRD & ONWR & OEOF & ORB & _).
    assert (SO2 : FILE_R m2 (lc_stdout (ps_libc s)) A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { eapply FILE_R_agree; [exact SO| exact AG02| |]; intros a Ha; unfold GI.stdio_static, A_STDOUT, A_STDOUT_BUF in *; [lia|]. rewrite OBS in Ha. unfold BUFSIZ in Ha. lia. }
    assert (FR2 : rw_cells ssegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply agrees_rw_cells; [exact AG2| exact FR1|]. intros a Ha. right. cbn in Ha. lia. }
    (* [comment removed for export] *)
    eapply implM_evt. { eapply (exit_stdin (Z_to_bv 64 (bv_unsigned sp + -16)) gp (rc_tp R)); [exact U22| exact SIN2| exact MI2]. }
    cbv beta. intros ms3 (c0 & c1 & ->).
    (* [comment removed for export] *)
    destruct SO2 as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    name_sp sp (-16).
    eapply implM_bind.
    { eapply (exit_stdout sp0 gp (rc_tp R)) with (f := lc_stdout (ps_libc s)) (lo := lo) (canary := rc_canary R) (flags := flags) (mode := mode) (rp := rp) (tail := tail) (bufbytes := bufbytes) (m := m2) (st := s);
        rewrite ?Hsp; first [ exact U32 | exact FC | exact FLsvb | exact BUF | exact BP | exact WB0 | exact ORB | exact OCH | exact OBS | exact WBL | exact ST2 | exact SSP2 | exact MI2
                             | rewrite OFD; left; reflexivity | unfold EXIT_DEPTH; lia | unfold zlength in *; lia
                             | match goal with |- ?g => idtac "XO side:" g end ]. }
    cbv beta. intros [] st4 ms4 (-> & PO). destruct_exs PO. destruct PO as (-> & MU4 & WM4 & MI4 & ST4 & SSP4).
    lazymatch type of MI4 with mem_inv _ ?mm => rename mm into m4 end.
    rewrite Hsp in ST4. unfold ex_W, EXIT_DEPTH in MU4. rewrite Hsp in MU4. subst sp0.
    (* [comment removed for export] *)
    pose proof SEI as (ECH & EFD & EBS & ENRD & ENWR & EEOF & ERB & _).
    assert (SE4 : FILE_R m4 (lc_stderr (ps_libc s)) A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { eapply FILE_R_agree; [exact SE| |intros a Ha; exact Ha| intros a Ha; rewrite EBS in Ha; lia].
      eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG02| intros a Ha; unfold GI.stdio_static, A_STDERR in *; lia]|].
      eapply agrees_on_of_munch; [exact MU4| exact WM4|]. intros a Ha Hp. unfold A_STDERR, A_STDOUT in *. cbn [outside]. lia. }
    assert (U14 : rw_cells ssegs m4 A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)]).
    { eapply rw_cells_transport; [trs AG02 U1| exact MU4| exact WM4| unfold A_STDERR_USED, A_STDOUT; cbn; lia]. }
    assert (FR4 : rw_cells ssegs m4 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR2| exact MU4| exact WM4| unfold A_STDOUT; cbn; lia]. }
    destruct SE4 as (flags' & mode' & rp' & tail' & bufbytes' & FC' & FL' & BUF' & BP' & WB0' & WBL' & RR' & RP0' & RPHI' & GLN').
    assert (EWB : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite EBS in WBL'. unfold zlength in WBL'. cbn in WBL'. lia. }
    unfold close_file. rewrite EWB. apply implM_retb. unfold sync_read_pos. rewrite ERB. apply implM_ret.
    eapply evt_mono.
    { eapply (exit_stderr ra sp gp (rc_tp R)) with (f := lc_stderr (ps_libc s)) (lo := lo); first
        [ exact U14 | exact FC' | exact EWB | exact ERB | exact FR4 | exact ST4 | exact MI4 | lia | unfold zlength in *; lia
        | match goal with |- ?g => idtac "XE side:" g end ]. }
    cbv beta. intros ms5 (d0 & d1 & -> & ST5).
    unfold stdio_exit_post. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity.
  Qed.
End GlueExit.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_stdio_exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fc.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
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


Section WithCeil.
Context {CEILV : CEIL}.
Definition STDIO_EXIT_FRAME : Z := 160.    (* [comment removed for export] *)

Section GlueExit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).

  (* [comment removed for export] *)
  #[local] Definition Pstat (sp : word) (a : Z) : Prop := S3.GI.TwB.stdio_static a \/ (bv_unsigned sp - 16 <= a < bv_unsigned sp).

  (* [comment removed for export] *)
  Definition loop_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : PS) (J : Z) (lo : Z) (canary : word) (m : mem) : unit -> PS -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 s0' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 J) fc None m' (seg_rom usegs)
      /\ agrees_on (Pstat sp) m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -16) /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Lemma exit_loop : forall fs (FB : list cblk) (prev : Z) (mi : mem) (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : PS) (lo u : Z) (canary : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    files_R mi prev fs FB -> List.NoDup (map fst fs) ->
    Forall (block_ok u) FB -> blocks_apart FB ->
    stk usegs mi lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - STDIO_EXIT_FRAME -> CEILZ <= lo ->
    bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
    ssp_cells mi canary -> mem_inv usegs mi ->
    implM usegs (close_files fs) st
      (loop_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st 0x1b654 lo canary mi)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 (hd_addr FB)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (if hd_addr FB =? 0 then 0x1b654 else EXIT_LOOP)) fc None mi (seg_rom usegs)).
  Proof using Type. pin_using tt.
    induction fs as [|[q f] fs IH]; intros FB prev mi sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo u canary x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      FS ND BO BA ST LO CLO SP47 SSP MI.
    - destruct FB as [|b FB']; [| exact (False_ind _ FS)]. cbn [hd_addr]. rewrite Z.eqb_refl. cbn [close_files].
      apply implM_ret. apply evt_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [intros a Ha Hp; split; [reflexivity| intros X; exact X]|]. split; [exact MI|]. split; [exact ST| exact SSP].
    - destruct FB as [|[[q' A] n] FB']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      apply Forall_cons_iff in BO as [(K1 & K2 & K3 & K4 & K5 & K6) BO]. unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3, K4, K5, K6. cbn [fst snd] in K1, K2, K3, K4, K5, K6.
      cbn [blocks_apart] in BA. destruct BA as [APA BA].
      cbn [hd_addr]. replace (A =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
      pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
      pose proof INV as (ICH & IFD & IBS & INN & INW & INR & IRB).
      unfold STDIO_EXIT_FRAME in LO.
      cbn [close_files].
      name_sp sp (-16).
      eapply implM_bind.
      { eapply (exit_body sp0 gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st A flags F_STDIO_CLOSE F_STDIO_READ (A + FILE_BUF_OFF) prev (hd_addr FB') tail lo canary mi);
          rewrite ?Hsp; first [ exact FC | exact FLsvb | exact BUF | exact BP | exact WB0 | exact WBL | intros _; exact ICH | exact RP0 | exact RPHI
                               | rewrite ICH; exact IFD | exact ST | exact SSP | exact MI
                               | rewrite ?IBS; unfold EXIT_DEPTH, BUFSIZ, FILE_BUF_OFF, got_ssp, ssp_guard; lia
                               | match goal with |- ?g => idtac "XB side:" g end ]. }
      cbv beta. intros [] st1 ms1 (-> & PO).
      destruct PO as (x1' & v0 & v1 & v2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m' & -> & MU & WM & MI' & ST' & NXC & SSP').
      rewrite Hsp in ST'. unfold ex_W, EXIT_DEPTH in MU. rewrite Hsp in MU.
      (* [comment removed for export] *)
      assert (HDR' : 0 <= hd_addr FB' < 2^64).
      { destruct FB' as [|[[q2 A2] n2] FB'']; cbn [hd_addr]; [lia|]. apply Forall_cons_iff in BO as [(J1 & J2 & J3 & J4 & _) _]. unfold cb_addr, cb_size in J1, J2, J3, J4. cbn [fst snd] in J1, J2, J3, J4. lia. }
      eapply implM_evt. { eapply (exit_next sp0 gp tp); [exact NXC| lia| lia| exact HDR'| exact MI']. }
      cbv beta. intros ms2 ->. subst sp0.
      (* [comment removed for export] *)
      assert (AG : agrees_on (fun a => ~ (bv_unsigned sp - 16 - 144 <= a < bv_unsigned sp - 16) /\ ~ (A <= a < A + 232)) mi m').
      { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [N1 N2]. cbn [outside]. repeat split; lia. }
      assert (REST' : files_R m' A fs FB').
      { eapply files_R_agree; [exact REST| exact AG|]. intros a Hin.
        apply in_block_In in Hin as ([[qb Ab] nb] & HbIn & Hb). unfold cb_addr, cb_size in Hb. cbn [fst snd] in Hb.
        pose proof (proj1 (Forall_forall _ _) BO _ HbIn) as (J1 & J2 & J3 & J4 & _). unfold cb_addr, cb_size in J1, J2, J3, J4. cbn [fst snd] in J1, J2, J3, J4.
        pose proof (proj1 (Forall_forall _ _) APA _ HbIn) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
      eapply implM_mono.
      { eapply (IH FB' A m'); [exact REST'| exact ND| exact BO| exact BA| exact ST'| unfold STDIO_EXIT_FRAME; lia| exact CLO| exact SP47| exact SSP'| exact MI']. }
      cbv beta. intros [] st2 ms3 (-> & PO). destruct_exs PO. destruct PO as (-> & AG2 & MI2 & ST2 & SSP2).
      split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [| split; [exact MI2| split; [exact ST2| exact SSP2]]].
      eapply agrees_on_trans; [| exact AG2]. eapply agrees_on_weaken; [exact AG|].
      intros a [Hs|Hs]; [| lia]. unfold S3.GI.TwB.stdio_static in Hs. unfold rc_lo in *. lia.
  Qed.

  Lemma libc_need_locks' : forall m cdt thr sec tm1 auxv th ts ta tc ps loc,
    rw_cells usegs m 0x544e8 (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) -> rw_cells usegs m NEED_LOCKS [C1 (Z_to_bv 8 0)].
  Proof using Type. pin_using tt.
    intros until loc. intros LC. unfold libc_cells in LC.
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in LC as [_ LC]. apply (proj1 (rw_cells_app usegs m _ [_] _)) in LC as [_ LC].
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in LC as [_ LC]. apply (proj1 (rw_cells_app usegs m _ [_] _)) in LC as [NL _].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in NL. unfold NEED_LOCKS. exact NL.
  Qed.

  Theorem stdio_exit_proof : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB.stdio_exit_stmt (s_stdio_exit (H:=H)) (SXGI K) STDIO_EXIT_FRAME.
  Proof using KST. pin_using (fun (KST : unit) => tt).
    intros until loc. intros ST SX LIBCC MI LO CLO SP47.   (* [comment removed for export] *)
    destruct SX as (R & CL & FB & Etp & HH & HS & HA & CT & PT & CLI & CM & Etls & TB & BOK).
    apply (proj1 (KST _ R _ _)) in HS as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof BOK as [BO BA]. apply Forall_app in BO as [BOCL BOFB]. pose proof (blocks_apart_app_inv _ _ BA) as (_ & BAf & _).
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (libc_need_locks' _ _ _ _ _ _ _ _ _ _ _ _ LIBCC) as NL.
    pose proof (core_ssp R m CLI) as SSP.
    subst tp. unfold STDIO_EXIT_FRAME in LO.
    assert (HDR : 0 <= hd_addr FB < 2^64).
    { destruct FB as [|[[q1 A1] n1] FB']; cbn [hd_addr]; [lia|]. apply Forall_cons_iff in BOFB as [(J1 & J2 & J3 & J4 & _) _].
      unfold cb_addr, cb_size in J1, J2, J3, J4. cbn [fst snd] in J1, J2, J3, J4. lia. }
    unfold s_stdio_exit, Stdio.stdio_exit. apply implM_rd_lc.
    (* [comment removed for export] *)
    eapply implM_evt.
    { eapply (exit_entry ra sp gp (rc_tp R) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (hd_addr FB) lo m);
        [exact OH| exact HDR| exact NL| exact ST| lia| lia| exact MI]. }
    cbv beta. intros ms1 PO. destruct PO as (x1 & b0 & b1 & b2 & b3 & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (AG1 : agrees_on (fun a => a < bv_unsigned sp - 32 \/ bv_unsigned sp <= a) m m1).
    { eapply agrees_on_of_munch; [exact MU1| exact WM1|]. intros a Ha Hp. cbn [outside]. split; [lia| exact I]. }
    assert (BKF : forall a, in_block FB a -> 0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x56000 <= a) /\ (a < utp R - 200 \/ utp R - 200 + 4096 <= a))
      by (intros a Ha; exact (in_block_facts (utp R) FB a BOFB Ha)).
    assert (FS1 : files_R m1 0 (lc_files (ps_libc s)) FB).
    { eapply files_R_agree; [exact FS| exact AG1| intros a Ha; destruct (BKF a Ha); lia]. }
    assert (SSP1 : ssp_cells m1 (rc_canary R)).
    { destruct SSP as [G1 G2]. split; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1| unfold got_ssp, ssp_guard; cbn; lia]). }
    (* [comment removed for export] *)
    eapply implM_bind.
    { eapply (exit_loop (lc_files (ps_libc s)) FB 0 m1 sp gp (rc_tp R) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo (utp R) (rc_canary R));
        [exact FS1| exact ND| exact BOFB| exact BAf| exact ST1| unfold STDIO_EXIT_FRAME; lia| exact CLO| exact SP47| exact SSP1| exact MI1]. }
    cbv beta. intros [] st2 ms2 (-> & PO). destruct_exs PO. destruct PO as (-> & AG2 & MI2 & ST2 & SSP2).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    (* [comment removed for export] *)
    assert (AG02 : agrees_on S3.GI.TwB.stdio_static m m2).
    { eapply agrees_on_trans; [| eapply agrees_on_weaken; [exact AG2| intros a Ha; left; exact Ha]].
      eapply agrees_on_weaken; [exact AG1|]. intros a Hs. unfold S3.GI.TwB.stdio_static in Hs. lia. }
    Ltac trs AG X := eapply agrees_rw_cells; [exact AG | exact X | intros a Ha; unfold S3.GI.TwB.stdio_static, A_STDIN_USED, A_STDOUT_USED, A_STDERR_USED, A_STDIN in *; cbn in Ha; lia].
    assert (U22 : rw_cells usegs m2 A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)]) by (trs AG02 U2).
    assert (U32 : rw_cells usegs m2 A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)]) by (trs AG02 U3).
    assert (SIN2 : rw_cells usegs m2 A_STDIN stdin_cells).
    { eapply agrees_rw_cells; [exact AG02| exact SIN|]. unfold stdin_cells. rewrite file_cells_size. intros a Ha. unfold S3.GI.TwB.stdio_static, A_STDIN in *. lia. }
    pose proof SOI as (OCH & OFD & OBS & ONRD & ONWR & OEOF & ORB & _).
    assert (SO2 : FILE_R m2 (lc_stdout (ps_libc s)) A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { eapply FILE_R_agree; [exact SO| exact AG02| |]; intros a Ha; unfold S3.GI.TwB.stdio_static, A_STDOUT, A_STDOUT_BUF in *; [lia|]. rewrite OBS in Ha. unfold BUFSIZ in Ha. lia. }
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply agrees_rw_cells; [exact AG2| exact FR1|]. intros a Ha. right. cbn in Ha. lia. }
    (* [comment removed for export] *)
    eapply implM_evt. { eapply (exit_stdin (Z_to_bv 64 (bv_unsigned sp + -16)) gp (rc_tp R)); [exact U22| exact SIN2| exact MI2]. }
    cbv beta. intros ms3 (c0 & c1 & ->).
    (* [comment removed for export] *)
    destruct SO2 as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    name_sp sp (-16).
    eapply implM_bind.
    { eapply (exit_stdout sp0 gp (rc_tp R)) with (f := lc_stdout (ps_libc s)) (lo := lo) (canary := rc_canary R) (flags := flags) (mode := mode) (rp := rp) (tail := tail) (bufbytes := bufbytes) (m := m2) (st := s);
        rewrite ?Hsp; first [ exact U32 | exact FC | exact FLsvb | exact BUF | exact BP | exact WB0 | exact ORB | exact OCH | exact OBS | exact WBL | exact ST2 | exact SSP2 | exact MI2
                             | rewrite OFD; left; reflexivity | unfold EXIT_DEPTH; lia | unfold zlength in *; lia
                             | match goal with |- ?g => idtac "XO side:" g end ]. }
    cbv beta. intros [] st4 ms4 (-> & PO). destruct_exs PO. destruct PO as (-> & MU4 & WM4 & MI4 & ST4 & SSP4).
    lazymatch type of MI4 with mem_inv _ ?mm => rename mm into m4 end.
    rewrite Hsp in ST4. unfold ex_W, EXIT_DEPTH in MU4. rewrite Hsp in MU4. subst sp0.
    (* [comment removed for export] *)
    pose proof SEI as (ECH & EFD & EBS & ENRD & ENWR & EEOF & ERB & _).
    assert (SE4 : FILE_R m4 (lc_stderr (ps_libc s)) A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { eapply FILE_R_agree; [exact SE| |intros a Ha; exact Ha| intros a Ha; rewrite EBS in Ha; lia].
      eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG02| intros a Ha; unfold S3.GI.TwB.stdio_static, A_STDERR in *; lia]|].
      eapply agrees_on_of_munch; [exact MU4| exact WM4|]. intros a Ha Hp. unfold A_STDERR, A_STDOUT in *. cbn [outside]. lia. }
    assert (U14 : rw_cells usegs m4 A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)]).
    { eapply rw_cells_transport; [trs AG02 U1| exact MU4| exact WM4| unfold A_STDERR_USED, A_STDOUT; cbn; lia]. }
    assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR2| exact MU4| exact WM4| unfold A_STDOUT; cbn; lia]. }
    destruct SE4 as (flags' & mode' & rp' & tail' & bufbytes' & FC' & FL' & BUF' & BP' & WB0' & WBL' & RR' & RP0' & RPHI' & GLN').
    assert (EWB : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite EBS in WBL'. unfold zlength in WBL'. cbn in WBL'. lia. }
    unfold close_file. rewrite EWB. apply implM_retb. unfold sync_read_pos. rewrite ERB. apply implM_ret.
    eapply evt_mono.
    { eapply (exit_stderr ra sp gp (rc_tp R)) with (f := lc_stderr (ps_libc s)) (lo := lo); first
        [ exact U14 | exact FC' | exact EWB | exact ERB | exact FR4 | exact ST4 | exact MI4 | lia | unfold zlength in *; lia
        | match goal with |- ?g => idtac "XE side:" g end ]. }
    cbv beta. intros ms5 (d0 & d1 & -> & ST5).
    unfold stdio_exit_post. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity.
  Qed.
End GlueExit.

End WithCeil.
End TwB.
End Stdio_glue_exit.

(* [comment removed for export] *)
Module Stdio_glue_sys.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_unlink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.


Section WithCeil.
Context {CEILV : CEIL}.
Section GlueSys.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.spo_facts K KST).
  #[local] Notation GIo_stdio_step_err := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.GIo_stdio_step_err K KST HFL).
  #[local] Notation STDIOR_keep := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.STDIOR_keep).
  #[local] Notation keeps_of_stdio_err := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.keeps_of_stdio_err K).

  (* [comment removed for export] *)
  Definition client_bytes_keep__stmt : Prop := forall R (s : PS) (CL FB : list cblk) m m' W SP S (bs : list byte),
    GIo K R s CL FB m -> client_range R CL SP S (Z.of_nat (length bs)) -> bytes_at ssegs m S bs ->
    munch W m m' -> wmono ssegs m m' ->
    Forall (fun iv : Z * Z => (CEILZ <= fst iv /\ snd iv <= SP) \/ (utp R - 200 <= fst iv /\ snd iv <= utp R - 200 + 4096)
                              \/ (0x10000 <= fst iv /\ snd iv <= 0x55000)) W ->
    CEILZ <= SP -> bytes_at ssegs m' S bs.
  Section Sz1.
  Variables R s CL FB m m' W SP S bs : ltac2:(SecDiet.SzSec.tyM 'client_bytes_keep__stmt "vvvvvvvvvv" @R).
  Lemma client_bytes_keep__body : ltac2:(SecDiet.SzSec.bodyP 'client_bytes_keep__stmt "vvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G CR HB MU WM HW CSP.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    unfold tls_block_ok in TB. destruct TB as (TBA & TB0 & TBC & TBI).
    eapply agrees_bytes_at; [| exact HB| intros a Ha; exact Ha].
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hr.
    eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd] in *.
    destruct CR as [CR|CR].
    - pose proof (in_block_facts (utp R) CL a BO1 (CR a Hr)) as (F1 & F2 & F3 & F4). lia.
    - unfold rc_spmain in CR. lia.
  Qed.
  End Sz1.
  Lemma client_bytes_keep : ltac:(let t := eval cbv delta [client_bytes_keep__stmt] in client_bytes_keep__stmt in exact t).
  Proof using Type. intros R s CL FB m m' W SP S bs. ltac2:(SecDiet.SzSec.closeP 'client_bytes_keep__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition sysret_tail_GI__stmt : Prop := forall (ra sp gp : word) (R : rctx) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m m1 : mem) (s : PS) (CL FB : list cblk) (lo : Z) (J : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv : word) (jk : list byte),
    std_pre_o K sp (rc_tp R) R s CL FB lo 65536 m ->
    rw_cells ssegs m (utp R + -164) [C4 errv] ->
    (J = 0x21538 \/ J = 0x1ba98 \/ J = 0x214c8) ->
    rw_cells ssegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
    rw_cells ssegs m1 (bv_unsigned (rc_tp R) + -164) [C4 errv] ->
    stk ssegs m1 lo (bv_unsigned sp + -16) -> mem_inv ssegs m1 ->
    munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned (rc_tp R) + -164, bv_unsigned (rc_tp R) + -160)] m m1 -> wmono ssegs m m1 ->
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    evt ssegs (fun ms' => exists a0v m', hpost_regs ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
         /\ GIo K R (set_libc (match errno_of r with Some e => set_errno_lc e (ps_libc s) | None => ps_libc s end) s) CL FB m'
         /\ a0v = Z_to_bv 64 (match errno_of r with Some _ => -1 | None => 0 end)
         /\ rw_cells ssegs m' (utp R + -164) [C4 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp (rc_tp R) t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J) fc None m1 (seg_rom ssegs)).
  Section Sz2.
  Variables ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv jk : ltac2:(SecDiet.SzSec.tyM 'sysret_tail_GI__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma sysret_tail_GI__body : ltac2:(SecDiet.SzSec.bodyP 'sysret_tail_GI__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros SPO ERR HJ FR1 ERR1 ST1 MI1 MU1 WM1 HR.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    eapply evt_mono.
    { eapply (sysret_tail ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo errv) with (m0 := m);
        first [exact HJ | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact HR | unfold utp, rc_lo in *; lia
              | match goal with |- ?g => idtac "TL side:" g end]. }
    cbv beta. intros ms' PO. destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply (keeps_of_stdio_err R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU'| exact WM'| | unfold rc_lo in *; lia].
             apply Forall_cons; [left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; right; right; right; cbn; unfold utp; lia| apply Forall_nil]. }
    split. { eapply (GIo_stdio_step_err R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU'| exact WM'| | exact SPM| unfold utp; exact ERR'|].
             - apply Forall_cons; [left; left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil].
             - assert (SRk : STDIOR (ps_libc s) FB m').
               { eapply (STDIOR_keep _ FB CL R m m'); [exact SR| exact BOK| exact TB| exact MU'| exact WM'|].
                 apply Forall_cons; [left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil]. }
               unfold STDIOR in SRk |- *. destruct (errno_of r); destruct (ps_libc s) as [xso xse xfs xer]; cbn [lc_stdout lc_stderr lc_files set_errno_lc] in SRk |- *; exact SRk. }
    split; [reflexivity|]. unfold utp. exact ERR'.
  Qed.
  End Sz2.
  Lemma sysret_tail_GI : ltac:(let t := eval cbv delta [sysret_tail_GI__stmt] in sysret_tail_GI__stmt in exact t).
  Proof using HFL KST. intros ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv jk. ltac2:(SecDiet.SzSec.closeP 'sysret_tail_GI__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  #[local] Definition WSE (sp tp : word) : list (Z * Z) :=
    [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)].
  Lemma munch_add_errno : forall (sp tp : word) m m1,
    munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 -> munch (WSE sp tp) m m1.
  Proof using Type. pin_using tt. intros sp tp m m1 MU. eapply munch_weaken; [| exact MU]. unfold sub_fp, WSE. cbn [outside]. intros x (O1 & O2 & _). split; [exact O1| exact I]. Qed.

  Definition unlink_o_proof__stmt : Prop := unlink_stmt_o K.
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME name : ltac2:(SecDiet.SzSec.tyM 'unlink_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma unlink_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'unlink_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros SPO -> HNAME NNUL NLEN NCR NOK.
    (* [comment removed for export] *)
    assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    pose proof CT as (tlst & errv & _ & ERR & _).
    destruct NOK as (NS & ND1 & ND2 & NLM).
    unfold s_unlink, Stdio.unlink.
    apply implM_sysk.
    eapply evt_cut.
    { eapply (unlink_S1 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exact ST| exact MI]. }
    cbv beta. intros ms1 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (HNAME1 : bytes_at ssegs m1 NAME (name ++ [Z_to_bv 8 0])).
    { eapply (client_bytes_keep R s CL FB m m1); [exact G| rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; exact NCR| exact HNAME| exact MU1| exact WM1| | unfold rc_lo in *; lia].
      apply Forall_cons; [left; cbn; unfold rc_lo in *; lia| apply Forall_nil]. }
    assert (ERR1 : rw_cells ssegs m1 (bv_unsigned (rc_tp R) + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold utp, rc_lo in *. lia. }
    apply (munch_add_errno sp (rc_tp R)) in MU1. unfold WSE in MU1.
    step_ecall. split.
    { at_node_solve.
      all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
      all: first [exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME1
                 | intros E; apply (f_equal (@length byte)) in E; cbn in E; lia
                 | match goal with |- ?g => idtac "ATNODE:" g end]. }
    intros rsp a Hdec. unfold dec_unlink in Hdec. apply dec_plain_Some in Hdec.
    destruct a as [e|v].
    - destruct Hdec as [-> HE]. apply implM_upd_lc. apply implM_ret. unfold efferr, eff0. sys_nret.
      eapply evt_mono.
      { eapply (sysret_tail_GI ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo) with (r := errno_ret e);
          first [exact SPO | exact ERR | left; reflexivity | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                | exists e; left; split; [reflexivity| exact HE]]. }
      cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_errno_ret e HE) in *.
      eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity| right; reflexivity].
    - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. apply implM_ret. unfold eff0. sys_nret.
      eapply evt_mono.
      { eapply (sysret_tail_GI ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo) with (r := Z_to_bv 64 0);
          first [exact SPO | exact ERR | left; reflexivity | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                | exists 1; right; reflexivity]. }
      cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
      eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity| left; reflexivity].
  Qed.
  End Sz4.
  Theorem unlink_o_proof : ltac:(let t := eval cbv delta [unlink_o_proof__stmt] in unlink_o_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME name. ltac2:(SecDiet.SzSec.closeP 'unlink_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition remove_o_proof__stmt : Prop := remove_stmt_o K.
  Section Sz5.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME name : ltac2:(SecDiet.SzSec.tyM 'remove_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma remove_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'remove_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros SPO -> HNAME NNUL NLEN NCR NOK.
    (* [comment removed for export] *)
    assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    pose proof CT as (tlst & errv & _ & ERR & _).
    destruct NOK as (NS & ND1 & ND2 & NLM).
    unfold s_remove, Stdio.remove.
    (* [comment removed for export] *)
    assert (FIN : forall (r : word) (m1 : mem) (jk : list byte) (a2' : word),
      (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
      rw_cells ssegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
      munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 -> wmono ssegs m m1 -> mem_inv ssegs m1 ->
      stk ssegs m1 lo (bv_unsigned sp + -16) ->
      implM ssegs (match (match errno_of r with Some e => SErr e | None => SVal 0 end : sret) with
                   | SErr e => set_errno ps_libc set_libc e ;;; mret (-1) | SVal _ => mret 0 end) s
        (fun rv s' ms' => exists a0v m', hpost_regs ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIo K R s' CL FB m' /\ a0v = Z_to_bv 64 rv
           /\ (rv = 0 \/ (rv = -1 /\ rw_cells ssegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))] /\ 0 <= lc_errno (ps_libc s') < 2^31)))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp (rc_tp R) t0 t1 t2 s0 s1 r (Z_to_bv 64 NAME) a2' (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1ba98) fc None m1 (seg_rom ssegs))).
    { intros r m1 jk a2' HR FR1 MU1 WM1 MI1 ST1.
      assert (ERR1 : rw_cells ssegs m1 (bv_unsigned (rc_tp R) + -164) [C4 errv]).
      { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold utp, rc_lo in *. lia. }
      apply (munch_add_errno sp (rc_tp R)) in MU1. unfold WSE in MU1.
      destruct HR as (e & [[-> HE] | ->]).
      - rewrite (errno_of_errno_ret e HE). apply implM_upd_lc. apply implM_ret.
        eapply evt_mono.
        { eapply (sysret_tail_GI ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo) with (r := errno_ret e);
            first [exact SPO | exact ERR | right; left; reflexivity | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                  | exists e; left; split; [reflexivity| exact HE]]. }
        cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_errno_ret e HE) in *.
        eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity|].
        right. split; [reflexivity|]. cbn [ps_libc set_libc set_errno_lc lc_errno]. split; [exact ERR'| lia].
      - rewrite (errno_of_lit 0) by lia. apply implM_ret.
        eapply evt_mono.
        { eapply (sysret_tail_GI ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo) with (r := Z_to_bv 64 0);
            first [exact SPO | exact ERR | right; left; reflexivity | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                  | exists 1; right; reflexivity]. }
        cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
        eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity| left; reflexivity]. }
    (* [comment removed for export] *)
    apply implM_sysk.
    eapply evt_cut. { apply (remove_S1 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc). }
    cbv beta. intros ms1 ->.
    step_ecall. split.
    { at_node_solve.
      all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
      all: first [exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME
                 | intros E; apply (f_equal (@length byte)) in E; cbn in E; lia
                 | match goal with |- ?g => idtac "ATNODE1:" g end]. }
    intros rsp a Hdec. unfold dec_unlink in Hdec. apply dec_plain_Some in Hdec.
    destruct a as [e|v].
    - destruct Hdec as [-> HE]. unfold efferr, eff0. sys_nret.
      destruct (Z.eqb_spec e EISDIR) as [E21|NE21].
      + (* [comment removed for export] *)
        subst e. cbv iota beta.
        apply implM_sysk.
        eapply evt_cut. { eapply (remove_S2 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exists EISDIR; left; split; [reflexivity| unfold EISDIR; lia] | exact ST| exact MI]. }
        cbv beta. intros ms2 [[_ ->] | [NE _]]; [| exfalso; exact (NE eq_refl)].
        step_ecall. split.
        { at_node_solve.
          all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
          all: first [exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME
                     | intros E; apply (f_equal (@length byte)) in E; cbn in E; lia
                     | match goal with |- ?g => idtac "ATNODE2:" g end]. }
        intros rsp2 a2x Hdec2. unfold dec_unlink in Hdec2. apply dec_plain_Some in Hdec2.
        assert (HR2 : exists (r2 : word) (e2 : Z), (a2x = SErr e2 /\ r2 = errno_ret e2 /\ 1 <= e2 <= 4095) \/ (a2x = SVal 0 /\ r2 = Z_to_bv 64 0)).
        { destruct a2x as [e2|v2]; [destruct Hdec2 as [-> HE2]; exists (errno_ret e2), e2; left; repeat split; try reflexivity; lia|].
          destruct Hdec2 as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v2. exists (Z_to_bv 64 0), 1. right. split; reflexivity. }
        destruct HR2 as (r2 & e2 & [(-> & -> & HE2) | (-> & ->)]).
        * destruct Hdec2 as [-> _]. unfold efferr, eff0. sys_nret.
          eapply implM_evt. { eapply (remove_S3 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exists e2; left; split; [reflexivity| exact HE2] | exact ST| exact MI]. }
          cbv beta. intros ms3 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
          pose proof (FIN (errno_ret e2) m1 jk (Z_to_bv 64 512) ltac:(exists e2; left; split; [reflexivity| exact HE2]) FR1 MU1 WM1 MI1 ST1) as X.
          rewrite (errno_of_errno_ret e2 HE2) in X. exact X.
        * destruct Hdec2 as (-> & _). unfold eff0. sys_nret.
          eapply implM_evt. { eapply (remove_S3 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exists 1; right; reflexivity | exact ST| exact MI]. }
          cbv beta. intros ms3 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
          pose proof (FIN (Z_to_bv 64 0) m1 jk (Z_to_bv 64 512) ltac:(exists 1; right; reflexivity) FR1 MU1 WM1 MI1 ST1) as X.
          rewrite (errno_of_lit 0) in X by lia. exact X.
      + (* [comment removed for export] *)
        cbv iota beta. apply implM_retb.
        eapply implM_evt. { eapply (remove_S2 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exists e; left; split; [reflexivity| exact HE] | exact ST| exact MI]. }
        cbv beta. intros ms2 [[E _] | [_ PO]].
        { exfalso. apply NE21. pose proof (f_equal bv_unsigned E) as E'. rewrite !errno_ret_unsigned in E' by (unfold EISDIR; lia). unfold two_pow_64, EISDIR in *. lia. }
        destruct PO as (jk & m1 & a2' & -> & FR1 & MU1 & WM1 & MI1 & ST1).
        pose proof (FIN (errno_ret e) m1 jk a2' ltac:(exists e; left; split; [reflexivity| exact HE]) FR1 MU1 WM1 MI1 ST1) as X.
        rewrite (errno_of_errno_ret e HE) in X. exact X.
    - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. unfold eff0. sys_nret. apply implM_retb.
      eapply implM_evt. { eapply (remove_S2 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exists 1; right; reflexivity | exact ST| exact MI]. }
      cbv beta. intros ms2 [[E _] | [_ PO]].
      { exfalso. pose proof (f_equal bv_unsigned E) as E'. rewrite unsigned_lit, errno_ret_unsigned in E' by (unfold EISDIR; lia). unfold two_pow_64, EISDIR in *. lia. }
      destruct PO as (jk & m1 & a2' & -> & FR1 & MU1 & WM1 & MI1 & ST1).
      pose proof (FIN (Z_to_bv 64 0) m1 jk a2' ltac:(exists 1; right; reflexivity) FR1 MU1 WM1 MI1 ST1) as X.
      rewrite (errno_of_lit 0) in X by lia. exact X.
  Qed.
  End Sz5.
  Theorem remove_o_proof : ltac:(let t := eval cbv delta [remove_o_proof__stmt] in remove_o_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME name. ltac2:(SecDiet.SzSec.closeP 'remove_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition close_o_proof__stmt : Prop := close_stmt_o K.
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo fd : ltac2:(SecDiet.SzSec.tyM 'close_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma close_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'close_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros SPO -> FD.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof CT as (tlst & errv & _ & ERR & _).
    unfold s_close, Stdio.close.
    apply implM_sysk.
    eapply evt_cut.
    { eapply (close_S1 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| lia| exact ST| exact MI]. }
    cbv beta. intros ms1 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (ERR1 : rw_cells ssegs m1 (bv_unsigned (rc_tp R) + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold utp, rc_lo in *. lia. }
    apply (munch_add_errno sp (rc_tp R)) in MU1. unfold WSE in MU1.
    step_ecall. split. { at_node_solve. }
    intros rsp a Hdec. unfold dec_close_ok in Hdec.
    destruct (dec_close rsp) as [[e|v]|] eqn:E; try discriminate Hdec.
    unfold dec_close in E. apply dec_plain_Some in E. destruct E as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v.
    apply implM_ret. unfold eff0. sys_nret.
    eapply evt_cut. { apply (close_S2 sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc). }
    cbv beta. intros ms2 [a1' ->].
    eapply evt_mono.
    { eapply (sysret_tail_GI ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo) with (r := Z_to_bv 64 0);
        first [exact SPO | exact ERR | right; right; reflexivity | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
              | exists 1; right; reflexivity]. }
    cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
    eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|].
    destruct s as [sh sl so st']. cbn [set_libc ps_libc ps_heap ps_outfile ps_tls] in G'. exact G'.
  Qed.
  End Sz6.
  Theorem close_o_proof : ltac:(let t := eval cbv delta [close_o_proof__stmt] in close_o_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo fd. ltac2:(SecDiet.SzSec.closeP 'close_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueSys.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_unlink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.TwB.
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


Section WithCeil.
Context {CEILV : CEIL}.
Section GlueSys.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.spo_facts K KST).
  #[local] Notation GIo_stdio_step_err := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.TwB.GIo_stdio_step_err K KST HFL).
  #[local] Notation STDIOR_keep := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.TwB.STDIOR_keep).
  #[local] Notation keeps_of_stdio_err := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.TwB.keeps_of_stdio_err K).

  (* [comment removed for export] *)
  Definition client_bytes_keep__stmt : Prop := forall R (s : PS) (CL FB : list cblk) m m' W SP S (bs : list byte),
    GIo K R s CL FB m -> client_range R CL SP S (Z.of_nat (length bs)) -> bytes_at usegs m S bs ->
    munch W m m' -> wmono usegs m m' ->
    Forall (fun iv : Z * Z => (CEILZ <= fst iv /\ snd iv <= SP) \/ (utp R - 200 <= fst iv /\ snd iv <= utp R - 200 + 4096)
                              \/ (0x10000 <= fst iv /\ snd iv <= 0x56000)) W ->
    CEILZ <= SP -> bytes_at usegs m' S bs.
  Section Sz1.
  Variables R s CL FB m m' W SP S bs : ltac2:(SecDiet.SzSec.tyM 'client_bytes_keep__stmt "vvvvvvvvvv" @R).
  Lemma client_bytes_keep__body : ltac2:(SecDiet.SzSec.bodyP 'client_bytes_keep__stmt "vvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G CR HB MU WM HW CSP.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    unfold tls_block_ok_u in TB. destruct TB as (TBA & TB0 & TBC & TBI).
    eapply agrees_bytes_at; [| exact HB| intros a Ha; exact Ha].
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hr.
    eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd] in *.
    destruct CR as [CR|CR].
    - pose proof (in_block_facts (utp R) CL a BO1 (CR a Hr)) as (F1 & F2 & F3 & F4). lia.
    - unfold rc_spmain in CR. lia.
  Qed.
  End Sz1.
  Lemma client_bytes_keep : ltac:(let t := eval cbv delta [client_bytes_keep__stmt] in client_bytes_keep__stmt in exact t).
  Proof using Type. intros R s CL FB m m' W SP S bs. ltac2:(SecDiet.SzSec.closeP 'client_bytes_keep__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition sysret_tail_GI__stmt : Prop := forall (ra sp gp : word) (R : rctx) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m m1 : mem) (s : PS) (CL FB : list cblk) (lo : Z) (J : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv : word) (jk : list byte),
    std_pre_o K sp (rc_tp R) R s CL FB lo 65536 m ->
    rw_cells usegs m (utp R + -164) [C4 errv] ->
    (J = 0x21cf8 \/ J = 0x1c258 \/ J = 0x21c88) ->
    rw_cells usegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
    rw_cells usegs m1 (bv_unsigned (rc_tp R) + -164) [C4 errv] ->
    stk usegs m1 lo (bv_unsigned sp + -16) -> mem_inv usegs m1 ->
    munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned (rc_tp R) + -164, bv_unsigned (rc_tp R) + -160)] m m1 -> wmono usegs m m1 ->
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    evt usegs (fun ms' => exists a0v m', hpost_regs ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
         /\ GIo K R (set_libc (match errno_of r with Some e => set_errno_lc e (ps_libc s) | None => ps_libc s end) s) CL FB m'
         /\ a0v = Z_to_bv 64 (match errno_of r with Some _ => -1 | None => 0 end)
         /\ rw_cells usegs m' (utp R + -164) [C4 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp (rc_tp R) t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J) fc None m1 (seg_rom usegs)).
  Section Sz2.
  Variables ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv jk : ltac2:(SecDiet.SzSec.tyM 'sysret_tail_GI__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma sysret_tail_GI__body : ltac2:(SecDiet.SzSec.bodyP 'sysret_tail_GI__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
 intros SPO ERR HJ FR1 ERR1 ST1 MI1 MU1 WM1 HR.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    eapply evt_mono.
    { eapply (sysret_tail ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo errv) with (m0 := m);
        first [exact HJ | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact HR | unfold utp, rc_lo in *; lia
              | match goal with |- ?g => idtac "TL side:" g end]. }
    cbv beta. intros ms' PO. destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply (keeps_of_stdio_err R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU'| exact WM'| | unfold rc_lo in *; lia].
             apply Forall_cons; [left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; right; right; right; cbn; unfold utp; lia| apply Forall_nil]. }
    split. { eapply (GIo_stdio_step_err R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU'| exact WM'| | exact SPM| unfold utp; exact ERR'|].
             - apply Forall_cons; [left; left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil].
             - assert (SRk : STDIOR (ps_libc s) FB m').
               { eapply (STDIOR_keep _ FB CL R m m'); [exact SR| exact BOK| exact TB| exact MU'| exact WM'|].
                 apply Forall_cons; [left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil]. }
               unfold STDIOR in SRk |- *. destruct (errno_of r); destruct (ps_libc s) as [xso xse xfs xer]; cbn [lc_stdout lc_stderr lc_files set_errno_lc] in SRk |- *; exact SRk. }
    split; [reflexivity|]. unfold utp. exact ERR'.
  Qed.
  End Sz2.
  Lemma sysret_tail_GI : ltac:(let t := eval cbv delta [sysret_tail_GI__stmt] in sysret_tail_GI__stmt in exact t).
  Proof using HFL KST. intros ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv jk. ltac2:(SecDiet.SzSec.closeP 'sysret_tail_GI__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  #[local] Definition WSE (sp tp : word) : list (Z * Z) :=
    [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)].
  Lemma munch_add_errno : forall (sp tp : word) m m1,
    munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 -> munch (WSE sp tp) m m1.
  Proof using Type. pin_using tt. intros sp tp m m1 MU. eapply munch_weaken; [| exact MU]. unfold sub_fp, WSE. cbn [outside]. intros x (O1 & O2 & _). split; [exact O1| exact I]. Qed.

  Definition unlink_o_proof__stmt : Prop := unlink_stmt_o K.
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME name : ltac2:(SecDiet.SzSec.tyM 'unlink_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma unlink_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'unlink_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
 intros SPO -> HNAME NNUL NLEN NCR NOK.
 (* [comment removed for export] *)
 assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    pose proof CT as (tlst & errv & _ & ERR & _).
    destruct NOK as (NS & ND1 & ND2 & NLM).
    unfold s_unlink, Stdio.unlink.
    apply implM_sysk.
    eapply evt_cut.
    { eapply (unlink_S1 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exact ST| exact MI]. }
    cbv beta. intros ms1 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (HNAME1 : bytes_at usegs m1 NAME (name ++ [Z_to_bv 8 0])).
    { eapply (client_bytes_keep R s CL FB m m1); [exact G| rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; exact NCR| exact HNAME| exact MU1| exact WM1| | unfold rc_lo in *; lia].
      apply Forall_cons; [left; cbn; unfold rc_lo in *; lia| apply Forall_nil]. }
    assert (ERR1 : rw_cells usegs m1 (bv_unsigned (rc_tp R) + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold utp, rc_lo in *. lia. }
    apply (munch_add_errno sp (rc_tp R)) in MU1. unfold WSE in MU1.
    step_ecall. split.
    { at_node_solve.
      all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
      all: first [exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME1
                 | intros E; apply (f_equal (@length byte)) in E; cbn in E; lia
                 | match goal with |- ?g => idtac "ATNODE:" g end]. }
    intros rsp a Hdec. unfold dec_unlink in Hdec. apply dec_plain_Some in Hdec.
    destruct a as [e|v].
    - destruct Hdec as [-> HE]. apply implM_upd_lc. apply implM_ret. unfold efferr, eff0. sys_nret.
      eapply evt_mono.
      { eapply (sysret_tail_GI ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo) with (r := errno_ret e);
          first [exact SPO | exact ERR | left; reflexivity | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                | exists e; left; split; [reflexivity| exact HE]]. }
      cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_errno_ret e HE) in *.
      eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity| right; reflexivity].
    - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. apply implM_ret. unfold eff0. sys_nret.
      eapply evt_mono.
      { eapply (sysret_tail_GI ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo) with (r := Z_to_bv 64 0);
          first [exact SPO | exact ERR | left; reflexivity | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                | exists 1; right; reflexivity]. }
      cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
      eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity| left; reflexivity].
  Qed.
  End Sz4.
  Theorem unlink_o_proof : ltac:(let t := eval cbv delta [unlink_o_proof__stmt] in unlink_o_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME name. ltac2:(SecDiet.SzSec.closeP 'unlink_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition remove_o_proof__stmt : Prop := remove_stmt_o K.
  Section Sz5.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME name : ltac2:(SecDiet.SzSec.tyM 'remove_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma remove_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'remove_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
 intros SPO -> HNAME NNUL NLEN NCR NOK.
 (* [comment removed for export] *)
 assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    pose proof CT as (tlst & errv & _ & ERR & _).
    destruct NOK as (NS & ND1 & ND2 & NLM).
    unfold s_remove, Stdio.remove.
    (* [comment removed for export] *)
    assert (FIN : forall (r : word) (m1 : mem) (jk : list byte) (a2' : word),
      (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
      rw_cells usegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
      munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
      stk usegs m1 lo (bv_unsigned sp + -16) ->
      implM usegs (match (match errno_of r with Some e => SErr e | None => SVal 0 end : sret) with
                   | SErr e => set_errno ps_libc set_libc e ;;; mret (-1) | SVal _ => mret 0 end) s
        (fun rv s' ms' => exists a0v m', hpost_regs ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
           /\ GIo K R s' CL FB m' /\ a0v = Z_to_bv 64 rv
           /\ (rv = 0 \/ (rv = -1 /\ rw_cells usegs m' (utp R + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))] /\ 0 <= lc_errno (ps_libc s') < 2^31)))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp (rc_tp R) t0 t1 t2 s0 s1 r (Z_to_bv 64 NAME) a2' (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1c258) fc None m1 (seg_rom usegs))).
    { intros r m1 jk a2' HR FR1 MU1 WM1 MI1 ST1.
      assert (ERR1 : rw_cells usegs m1 (bv_unsigned (rc_tp R) + -164) [C4 errv]).
      { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold utp, rc_lo in *. lia. }
      apply (munch_add_errno sp (rc_tp R)) in MU1. unfold WSE in MU1.
      destruct HR as (e & [[-> HE] | ->]).
      - rewrite (errno_of_errno_ret e HE). apply implM_upd_lc. apply implM_ret.
        eapply evt_mono.
        { eapply (sysret_tail_GI ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo) with (r := errno_ret e);
            first [exact SPO | exact ERR | right; left; reflexivity | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                  | exists e; left; split; [reflexivity| exact HE]]. }
        cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_errno_ret e HE) in *.
        eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity|].
        right. split; [reflexivity|]. cbn [ps_libc set_libc set_errno_lc lc_errno]. split; [exact ERR'| lia].
      - rewrite (errno_of_lit 0) by lia. apply implM_ret.
        eapply evt_mono.
        { eapply (sysret_tail_GI ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo) with (r := Z_to_bv 64 0);
            first [exact SPO | exact ERR | right; left; reflexivity | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                  | exists 1; right; reflexivity]. }
        cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
        eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity| left; reflexivity]. }
    (* [comment removed for export] *)
    apply implM_sysk.
    eapply evt_cut. { apply (remove_S1 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc). }
    cbv beta. intros ms1 ->.
    step_ecall. split.
    { at_node_solve.
      all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
      all: first [exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME
                 | intros E; apply (f_equal (@length byte)) in E; cbn in E; lia
                 | match goal with |- ?g => idtac "ATNODE1:" g end]. }
    intros rsp a Hdec. unfold dec_unlink in Hdec. apply dec_plain_Some in Hdec.
    destruct a as [e|v].
    - destruct Hdec as [-> HE]. unfold efferr, eff0. sys_nret.
      destruct (Z.eqb_spec e EISDIR) as [E21|NE21].
      + (* [comment removed for export] *)
        subst e. cbv iota beta.
        apply implM_sysk.
        eapply evt_cut. { eapply (remove_S2 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exists EISDIR; left; split; [reflexivity| unfold EISDIR; lia] | exact ST| exact MI]. }
        cbv beta. intros ms2 [[_ ->] | [NE _]]; [| exfalso; exact (NE eq_refl)].
        step_ecall. split.
        { at_node_solve.
          all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
          all: first [exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME
                     | intros E; apply (f_equal (@length byte)) in E; cbn in E; lia
                     | match goal with |- ?g => idtac "ATNODE2:" g end]. }
        intros rsp2 a2x Hdec2. unfold dec_unlink in Hdec2. apply dec_plain_Some in Hdec2.
        assert (HR2 : exists (r2 : word) (e2 : Z), (a2x = SErr e2 /\ r2 = errno_ret e2 /\ 1 <= e2 <= 4095) \/ (a2x = SVal 0 /\ r2 = Z_to_bv 64 0)).
        { destruct a2x as [e2|v2]; [destruct Hdec2 as [-> HE2]; exists (errno_ret e2), e2; left; repeat split; try reflexivity; lia|].
          destruct Hdec2 as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v2. exists (Z_to_bv 64 0), 1. right. split; reflexivity. }
        destruct HR2 as (r2 & e2 & [(-> & -> & HE2) | (-> & ->)]).
        * destruct Hdec2 as [-> _]. unfold efferr, eff0. sys_nret.
          eapply implM_evt. { eapply (remove_S3 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exists e2; left; split; [reflexivity| exact HE2] | exact ST| exact MI]. }
          cbv beta. intros ms3 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
          pose proof (FIN (errno_ret e2) m1 jk (Z_to_bv 64 512) ltac:(exists e2; left; split; [reflexivity| exact HE2]) FR1 MU1 WM1 MI1 ST1) as X.
          rewrite (errno_of_errno_ret e2 HE2) in X. exact X.
        * destruct Hdec2 as (-> & _). unfold eff0. sys_nret.
          eapply implM_evt. { eapply (remove_S3 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exists 1; right; reflexivity | exact ST| exact MI]. }
          cbv beta. intros ms3 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
          pose proof (FIN (Z_to_bv 64 0) m1 jk (Z_to_bv 64 512) ltac:(exists 1; right; reflexivity) FR1 MU1 WM1 MI1 ST1) as X.
          rewrite (errno_of_lit 0) in X by lia. exact X.
      + (* [comment removed for export] *)
        cbv iota beta. apply implM_retb.
        eapply implM_evt. { eapply (remove_S2 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exists e; left; split; [reflexivity| exact HE] | exact ST| exact MI]. }
        cbv beta. intros ms2 [[E _] | [_ PO]].
        { exfalso. apply NE21. pose proof (f_equal bv_unsigned E) as E'. rewrite !errno_ret_unsigned in E' by (unfold EISDIR; lia). unfold two_pow_64, EISDIR in *. lia. }
        destruct PO as (jk & m1 & a2' & -> & FR1 & MU1 & WM1 & MI1 & ST1).
        pose proof (FIN (errno_ret e) m1 jk a2' ltac:(exists e; left; split; [reflexivity| exact HE]) FR1 MU1 WM1 MI1 ST1) as X.
        rewrite (errno_of_errno_ret e HE) in X. exact X.
    - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. unfold eff0. sys_nret. apply implM_retb.
      eapply implM_evt. { eapply (remove_S2 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| exists 1; right; reflexivity | exact ST| exact MI]. }
      cbv beta. intros ms2 [[E _] | [_ PO]].
      { exfalso. pose proof (f_equal bv_unsigned E) as E'. rewrite unsigned_lit, errno_ret_unsigned in E' by (unfold EISDIR; lia). unfold two_pow_64, EISDIR in *. lia. }
      destruct PO as (jk & m1 & a2' & -> & FR1 & MU1 & WM1 & MI1 & ST1).
      pose proof (FIN (Z_to_bv 64 0) m1 jk a2' ltac:(exists 1; right; reflexivity) FR1 MU1 WM1 MI1 ST1) as X.
      rewrite (errno_of_lit 0) in X by lia. exact X.
  Qed.
  End Sz5.
  Theorem remove_o_proof : ltac:(let t := eval cbv delta [remove_o_proof__stmt] in remove_o_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME name. ltac2:(SecDiet.SzSec.closeP 'remove_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition close_o_proof__stmt : Prop := close_stmt_o K.
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo fd : ltac2:(SecDiet.SzSec.tyM 'close_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma close_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'close_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
 intros SPO -> FD.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof CT as (tlst & errv & _ & ERR & _).
    unfold s_close, Stdio.close.
    apply implM_sysk.
    eapply evt_cut.
    { eapply (close_S1 ra sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [lia| lia| exact ST| exact MI]. }
    cbv beta. intros ms1 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (ERR1 : rw_cells usegs m1 (bv_unsigned (rc_tp R) + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold utp, rc_lo in *. lia. }
    apply (munch_add_errno sp (rc_tp R)) in MU1. unfold WSE in MU1.
    step_ecall. split. { at_node_solve. }
    intros rsp a Hdec. unfold dec_close_ok in Hdec.
    destruct (dec_close rsp) as [[e|v]|] eqn:E; try discriminate Hdec.
    unfold dec_close in E. apply dec_plain_Some in E. destruct E as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v.
    apply implM_ret. unfold eff0. sys_nret.
    eapply evt_cut. { apply (close_S2 sp gp (rc_tp R) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc). }
    cbv beta. intros ms2 [a1' ->].
    eapply evt_mono.
    { eapply (sysret_tail_GI ra sp gp R s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB lo) with (r := Z_to_bv 64 0);
        first [exact SPO | exact ERR | right; right; reflexivity | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
              | exists 1; right; reflexivity]. }
    cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
    eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|].
    destruct s as [sh sl so st']. cbn [set_libc ps_libc ps_heap ps_outfile ps_tls] in G'. exact G'.
  Qed.
  End Sz6.
  Theorem close_o_proof : ltac:(let t := eval cbv delta [close_o_proof__stmt] in close_o_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo fd. ltac2:(SecDiet.SzSec.closeP 'close_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueSys.

End WithCeil.
End TwB.
End Stdio_glue_sys.

(* [comment removed for export] *)
Module Stdio_glue_mk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.CallKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blk__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_mkstemp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_sys.
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


Section WithCeil.
Context {CEILV : CEIL}.
Section GlueMk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.spo_facts K KST).
  #[local] Notation GIo_stdio_step_err := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.GIo_stdio_step_err K KST HFL).
  #[local] Notation STDIOR_agree := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.STDIOR_agree).
  #[local] Notation keeps_of_stdio := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.keeps_of_stdio K).
  #[local] Notation client_range_lo := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.client_range_lo K).

  (* [comment removed for export] *)
  Lemma tmpl_Z : map bv_unsigned (map PcapRep.b8 TEMPLATE) = TEMPLATE.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpl_TMPL0 : map PcapRep.b8 TEMPLATE ++ [Z_to_bv 8 0] = TMPL0.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpl_len : length (map PcapRep.b8 TEMPLATE) = 29%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma seal_TEMPLATE : seal_name TEMPLATE = Some TMPNAME.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpn_bytes : TMPN0 = map PcapRep.b8 TMPNAME ++ [Z_to_bv 8 0].
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpn_tobytes : to_bytes TMPNAME = TMPN.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma TMPN0_len : length TMPN0 = 25%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma TMPN_nonul : ~ In (Z_to_bv 8 0) TMPN.
  Proof using Type. pin_using tt. unfold TMPN, TMPNAME. cbn. intuition discriminate. Qed.
  Lemma TMPNAME_range : Forall (fun z => 0 < z < 256) TMPNAME.
  Proof using Type. pin_using tt. unfold TMPNAME. cbn. repeat (constructor; [lia|]). constructor. Qed.
  Lemma TMPNAME_len : length TMPNAME = 24%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma TMPNAME_path : Namei.path_has_slash (map PcapRep.b8 TMPNAME) = false
                       /\ map PcapRep.b8 TMPNAME <> Uapi.dot_path /\ map PcapRep.b8 TMPNAME <> Namei.dotdot_path.
  Proof using Type. pin_using tt.
    split; [vm_compute; reflexivity|].
    split; intros E; apply (f_equal (@length byte)) in E; vm_compute in E; discriminate E.
  Qed.

  (* [comment removed for export] *)
  Definition client_cover__stmt : Prop := forall R (CL FB : list cblk) SP D n (W0 : list (Z * Z)) m m',
    client_range R CL SP D n -> 0 < n -> CEILZ <= SP ->
    munch (W0 ++ [(D, D + n)]) m m' ->
    exists W', munch (W0 ++ W') m m' /\ Forall (stdio_iv R CL FB SP) W'.
  Section Sz12.
  Variables R CL FB SP D n W0 m m' : ltac2:(SecDiet.SzSec.tyM 'client_cover__stmt "vvvvvvvvv" @R).
  Lemma client_cover__body : ltac2:(SecDiet.SzSec.bodyP 'client_cover__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros CR NP CSP MU.
    assert (OA : forall W1 W2 y, outside (W1 ++ W2) y <-> outside W1 y /\ outside W2 y).
    { induction W1 as [|[u v] W1 IH]; intros W2 y; cbn in *; [tauto|]. rewrite IH. tauto. }
    destruct CR as [CR|CR].
    - exists (map (fun b : cblk => (Z.max D (cb_addr b), Z.min (D + n) (cb_addr b + cb_size b))) CL). split.
      + intros x Hx. apply MU. apply OA in Hx as [O1 O2]. apply OA. split; [exact O1|]. cbn [outside]. split; [| exact I].
        intros HDn. pose proof (CR (bv_unsigned x) HDn) as Hb. apply in_block_In in Hb as (b & HbIn & Hb).
        assert (OM : forall (L : list cblk) y, outside (map (fun b : cblk => (Z.max D (cb_addr b), Z.min (D + n) (cb_addr b + cb_size b))) L) y ->
                       forall b', In b' L -> ~ (Z.max D (cb_addr b') <= y < Z.min (D + n) (cb_addr b' + cb_size b'))).
        { induction L as [|c L IHL]; intros y Hy b' Hb'; [destruct Hb'|]. cbn in Hy. destruct Hy as [Y1 Y2]. destruct Hb' as [<-|Hb']; [exact Y1| apply IHL; assumption]. }
        apply (OM CL (bv_unsigned x) O2 b HbIn). lia.
      + apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b & <- & HbIn). unfold stdio_iv. right; left.
        unfold iv_in_block. apply Exists_exists. exists b. split; [apply in_or_app; left; exact HbIn| cbn [fst snd]; lia].
    - exists [(D, D + n)]. split; [exact MU|]. apply Forall_cons; [| apply Forall_nil]. unfold stdio_iv. left. cbn [fst snd]. destruct CR. lia.
  Qed.
  End Sz12.
  Lemma client_cover : ltac:(let t := eval cbv delta [client_cover__stmt] in client_cover__stmt in exact t).
  Proof using Type. intros R CL FB SP D n W0 m m'. ltac2:(SecDiet.SzSec.closeP 'client_cover__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition STDIOR_keep_cr__stmt : Prop := forall (l : libc_st hptr) FB (CL : list cblk) R m m' W SP D n,
    STDIOR l FB m -> blocks_ok (utp R) (CL ++ FB) -> tls_block_ok (utp R - 200) -> munch W m m' -> wmono ssegs m m' ->
    client_range R CL SP D n -> CEILZ <= SP ->
    Forall (fun iv : Z * Z => CEILZ <= fst iv \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160) \/ (D <= fst iv /\ snd iv <= D + n)) W ->
    STDIOR l FB m'.
  Section Sz13.
  Variables l FB CL R m m' W SP D n : ltac2:(SecDiet.SzSec.tyM 'STDIOR_keep_cr__stmt "vvvvvvvvvv" @l).
  Lemma STDIOR_keep_cr__body : ltac2:(SecDiet.SzSec.bodyP 'STDIOR_keep_cr__stmt "vvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros SR BOK TB MU WM CR CSP HW.
    pose proof BOK as [BO BA]. pose proof BO as BO'. apply Forall_app in BO'. destruct BO' as [BO1 BO2].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    unfold tls_block_ok in TB. destruct TB as (TBA & TB0 & TBC & TBI).
    eapply (STDIOR_agree l FB m m' (fun a => GI.stdio_static a \/ in_block FB a)); [exact SR| | intros a Ha; left; exact Ha | intros a Ha; right; exact Ha].
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha HP.
    eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd] in Hiv |- *. intros Hin.
    destruct HP as [HS0|HB].
    - unfold GI.stdio_static in HS0. destruct Hiv as [X|[X|X]]; [lia| lia|].
      destruct CR as [CR|CR]; [| lia].
      destruct (in_block_facts (utp R) CL a BO1 (CR a ltac:(lia))) as (_ & _ & F3 & _). lia.
    - destruct (in_block_facts (utp R) FB a BO2 HB) as (F1 & F2 & F3 & F4).
      destruct Hiv as [X|[X|X]]; [lia| lia|].
      destruct CR as [CR|CR]; [| lia].
      pose proof (CR a ltac:(lia)) as HC. apply in_block_In in HC as (b & HbIn & Hb). apply in_block_In in HB as (b' & Hb'In & Hb').
      pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia.
  Qed.
  End Sz13.
  Lemma STDIOR_keep_cr : ltac:(let t := eval cbv delta [STDIOR_keep_cr__stmt] in STDIOR_keep_cr__stmt in exact t).
  Proof using Type. intros l FB CL R m m' W SP D n. ltac2:(SecDiet.SzSec.closeP 'STDIOR_keep_cr__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition keeps_cr__stmt : Prop := forall R (s : PS) CL FB m m' W SP D n,
    GIo K R s CL FB m -> munch W m m' -> wmono ssegs m m' ->
    Forall (fun iv : Z * Z => (CEILZ <= fst iv /\ snd iv <= SP) \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160) \/ (D <= fst iv /\ snd iv <= D + n)) W ->
    CEILZ <= SP ->
    agrees_on (fun a => client_keeps CL SP a /\ ~ (D <= a < D + n)) m m'.
  Section Sz14.
  Variables R s CL FB m m' W SP D n : ltac2:(SecDiet.SzSec.tyM 'keeps_cr__stmt "vvvvvvvvvv" @R).
  Lemma keeps_cr__body : ltac2:(SecDiet.SzSec.bodyP 'keeps_cr__stmt "vvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G MU WM HW HSP.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    eapply agrees_on_weaken.
    - eapply (keeps_of_stdio R s CL FB m m' W SP (fun a => (utp R - 164 <= a < utp R - 160) \/ (D <= a < D + n))); [exact G| exact MU| exact WM| | exact HSP].
      eapply Forall_impl; [| exact HW]. cbv beta. intros iv [X|[X|X]].
      + left; exact X.
      + right; right; right; right. intros a Ha. left. lia.
      + right; right; right; right. intros a Ha. right. lia.
    - cbv beta. intros a [Hk HN]. split; [exact Hk|]. intros [Hr|Hr]; [| exact (HN Hr)].
      destruct Hk as [Hk|Hk]; [lia|]. destruct (in_block_facts _ _ a BO1 Hk) as (F1 & F2 & F3 & F4). lia.
  Qed.
  End Sz14.
  Lemma keeps_cr : ltac:(let t := eval cbv delta [keeps_cr__stmt] in keeps_cr__stmt in exact t).
  Proof using Type. intros R s CL FB m m' W SP D n. ltac2:(SecDiet.SzSec.closeP 'keeps_cr__body "vvvvvvvvvv"). Qed.

  Definition mkstemp_o_proof__stmt : Prop := mkstemp_stmt_o K.
  Section Sz15.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME n tmpl buf : ltac2:(SecDiet.SzSec.tyM 'mkstemp_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma mkstemp_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'mkstemp_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros SPO -> BUF FST NNUL -> NLE NMAX NCR.
    (* [comment removed for export] *)
    assert (NMAXZ : (Z.of_nat n <= 4096)%Z) by (clear - NMAX; lia). clear NMAX.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK in *. rewrite tmpl_len in NLE, FST.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof CT as (tlst & errv & _ & ERR & _).
    destruct SSP as [GOT GUARD].
    destruct (client_range_lo R s CL FB m (bv_unsigned sp) NAME (Z.of_nat n) lo G NCR ltac:(lia) LOR ltac:(lia)) as (N0 & NSEP & NHI & NROM').
    assert (NROM : NAME + Z.of_nat n <= 0x10000 \/ 0x55000 <= NAME) by (unfold rc_lo in *; lia).
    assert (NTLS : NAME + Z.of_nat n <= utp R - 164 \/ utp R - 160 <= NAME).
    { destruct NCR as [CR|CR].
      - pose proof BOK as [BO _]. apply Forall_app in BO as [BO1 _].
        destruct (Z_lt_le_dec (Z.max NAME (utp R - 164)) (NAME + Z.of_nat n)) as [LT|GE]; [| left; lia].
        destruct (Z_lt_le_dec NAME (utp R - 160)) as [LT2|GE2]; [| right; exact GE2].
        exfalso. pose proof (in_block_facts (utp R) CL (Z.max NAME (utp R - 164)) BO1 (CR (Z.max NAME (utp R - 164)) ltac:(lia))) as (_ & _ & _ & F4). lia.
      - unfold rc_spmain in CR. unfold rc_lo in *. lia. }
    (* [comment removed for export] *)
    pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as [LB _].
    assert (LR : length (skipn 30 buf) = (n - 30)%nat) by (rewrite length_skipn; lia).
    pose proof (rw_cells_split_CB ssegs m NAME [] n buf [] [30%nat; (n - 30)%nat] BUF ltac:(cbn; lia)) as BUF2.
    cbn [app mk_CB_cells] in BUF2. rewrite tmpl_TMPL0 in FST. change (29 + 1)%nat with 30%nat in FST. rewrite FST in BUF2.
    rewrite (firstn_all2 (n := (n - 30)%nat) (skipn 30 buf)) in BUF2 by lia.
    set (rest := skipn 30 buf) in *. clearbody rest.
    (* [comment removed for export] *)
    unfold s_mkstemp, Stdio.mkstemp. rewrite tmpl_Z, seal_TEMPLATE, tmpn_tobytes. unfold MKSTEMP_MODE.
    (* [comment removed for export] *)
    eapply implM_evt.
    { eapply mk_S1 with (lo := lo) (n := n) (NAME := NAME); first [exact BUF2 | exact ST | exact MI | unfold rc_lo in *; lia | match goal with |- ?g => idtac "S1 side:" g end]. }
    cbv beta. intros ms1 PO. destruct PO as (x1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (BUF1 : rw_cells ssegs m1 NAME [CB 30 TMPL0; CB (n - 30) rest]).
    { eapply rw_cells_transport; [exact BUF2| exact MU1| exact WM1|]. cbn. lia. }
    (* [comment removed for export] *)
    eapply implM_evt.
    { eapply mk_S2 with (n := n) (NAME := NAME); first [exact BUF1 | exact MI1 | unfold rc_lo in *; lia | match goal with |- ?g => idtac "S2 side:" g end]. }
    cbv beta. intros ms2 (b4' & ->).
    (* [comment removed for export] *)
    eapply implM_evt.
    { eapply mk_S3 with (lo := lo) (n := n) (NAME := NAME); first [exact BUF1 | exact FR1 | exact ST1 | exact MI1 | unfold rc_lo in *; lia | match goal with |- ?g => idtac "S3 side:" g end]. }
    cbv beta. intros ms3 PO. destruct PO as (x1' & v0 & v1 & v2 & a0' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & BUF3 & FR3 & MU3 & WM3 & MI3 & ST3).
    (* [comment removed for export] *)
    eapply implM_evt.
    { eapply mk_S4 with (lo := lo) (n := n) (NAME := NAME) (sA := sp); first [exact FR3 | exact ST3 | exact MI3 | unfold rc_lo in *; lia | match goal with |- ?g => idtac "S4 side:" g end]. }
    cbv beta. intros ms4 (-> & ST4).
    (* [comment removed for export] *)
    assert (MU13 : munch [(bv_unsigned sp - 64, bv_unsigned sp); (NAME, NAME + 30)] m m3).
    { apply (munch_trans _ m m1 m3); [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros; lia. }
    assert (WM13 : wmono ssegs m m3) by (eapply wmono_trans; [exact WM1| exact WM3]).
    assert (ERR3 : rw_cells ssegs m3 (bv_unsigned (rc_tp R) + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU13| exact WM13|]. cbn. unfold utp, rc_lo in *. lia. }
    assert (GOT3 : rw_cells ssegs m3 got_ssp [C8 (Z_to_bv 64 ssp_guard)]).
    { eapply rw_cells_transport; [exact GOT| exact MU13| exact WM13|]. unfold got_ssp, ssp_guard. cbn. unfold rc_lo in *. lia. }
    assert (GUARD3 : rw_cells ssegs m3 ssp_guard [C8 (rc_canary R)]).
    { eapply rw_cells_transport; [exact GUARD| exact MU13| exact WM13|]. unfold got_ssp, ssp_guard. cbn. unfold rc_lo in *. lia. }
    assert (STR3 : bytes_at ssegs m3 NAME (TMPN ++ [Z_to_bv 8 0])).
    { pose proof (proj2 (proj1 BUF3)) as X. cbn [cells_bytes cbytes] in X.
      rewrite <- TMPN0_eq, <- (app_assoc (TMPN ++ [Z_to_bv 8 0]) (skipn 25 SEALED0)) in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X as [X _].
      exact X. }
    (* [comment removed for export] *)
    eapply (implM_msys_of_enode ssegs); [reflexivity | |].
    { eapply (open_w_spec ra sp gp (rc_tp R)) with (lo := lo) (path := TMPN) (errv := errv) (canary := rc_canary R);
        first [exact ST4 | rewrite unsigned_lit by lia; exact STR3 | exact ERR3 | exact GOT3 | exact GUARD3 | exact MI3 | reflexivity | exact TMPN_nonul
              | rewrite ?unsigned_lit by lia; rewrite ?TMPN_len; unfold utp, rc_lo, got_ssp, ssp_guard in *; lia
              | left; vm_compute; reflexivity   (* [comment removed for export] *)
              | match goal with |- ?g => idtac "OW side:" g end]. }
    intros r ms' PO. unfold open_post in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m' & -> & MU' & WM' & MI' & ST' & ERR' & STR' & GOT' & GUARD' & Hr).
    (* [comment removed for export] *)
    assert (MUT : munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned (rc_tp R) + -164, bv_unsigned (rc_tp R) + -160); (NAME, NAME + Z.of_nat n)] m m').
    { apply (munch_trans _ m m3 m'); [eapply munch_weaken; [| exact MU13] | eapply munch_weaken; [| exact MU']]; unfold sub_fp; cbn [outside]; intros; lia. }
    assert (WMT : wmono ssegs m m') by (eapply wmono_trans; [exact WM13| exact WM']).
    destruct (client_cover R CL FB (bv_unsigned sp) NAME (Z.of_nat n)
                [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned (rc_tp R) + -164, bv_unsigned (rc_tp R) + -160)] m m'
                NCR ltac:(lia) ltac:(unfold rc_lo in *; lia) MUT) as (W' & MUW & HW').
    (* [comment removed for export] *)
    assert (BUF' : rw_cells ssegs m' NAME [CB n ((TMPN0 ++ skipn 25 SEALED0) ++ rest)]).
    { assert (B3' : rw_cells ssegs m' NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]).
      { eapply rw_cells_transport; [exact BUF3| exact MU'| exact WM'|]. cbn. unfold utp in *. lia. }
      eapply (rw_cells_recast m' NAME _ _ B3').
      - cbn [cells_wf cell_wf]. split; [| exact I]. rewrite !length_app. change (length TMPN0) with 25%nat. change (length (skipn 25 SEALED0)) with 5%nat. lia.
      - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
      - cbn. lia. }
    assert (FSTn : firstn (length TMPNAME + 1) ((TMPN0 ++ skipn 25 SEALED0) ++ rest) = map PcapRep.b8 TMPNAME ++ [Z_to_bv 8 0]).
    { rewrite TMPNAME_len. change (24 + 1)%nat with 25%nat. rewrite <- app_assoc, firstn_app, TMPN0_len, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite firstn_all2 by (rewrite TMPN0_len; lia). exact tmpn_bytes. }
    assert (SRk : STDIOR (ps_libc s) FB m').
    { eapply (STDIOR_keep_cr (ps_libc s) FB CL R m m' _ (bv_unsigned sp) NAME (Z.of_nat n)); [exact SR| exact BOK| exact TB| exact MUT| exact WMT| exact NCR| unfold rc_lo in *; lia|].
      apply Forall_cons; [left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; left; cbn; unfold utp; lia|].
      apply Forall_cons; [right; right; cbn; lia| apply Forall_nil]. }
    assert (AGk : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (NAME <= a < NAME + Z.of_nat n)) m m').
    { eapply (keeps_cr R s CL FB m m' _ (bv_unsigned sp) NAME (Z.of_nat n)); [exact G| exact MUT| exact WMT| | unfold rc_lo in *; lia].
      apply Forall_cons; [left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; left; cbn; unfold utp; lia|].
      apply Forall_cons; [right; right; cbn; lia| apply Forall_nil]. }
    assert (HWT : Forall (fun iv : Z * Z => stdio_iv R CL FB (bv_unsigned sp) iv \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160))
                    ([(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned (rc_tp R) + -164, bv_unsigned (rc_tp R) + -160)] ++ W')).
    { apply Forall_app. split; [| eapply Forall_impl; [| exact HW']; intros iv X; left; exact X].
      apply Forall_cons; [left; left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil]. }
    destruct r as [e|fd]; cbn [open_ret open_errno] in ERR' |- *.
    - (* [comment removed for export] *)
      apply implM_upd_lc. apply implM_ret. apply evt_done.
      eexists _, m', _. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AGk|].
      split. { eapply (GIo_stdio_step_err R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MUW| exact WMT| exact HWT| exact SPM| unfold utp; exact ERR'|].
               unfold STDIOR in SRk |- *. destruct (ps_libc s) as [xso xse xfs xer]; cbn [lc_stdout lc_stderr lc_files set_errno_lc] in SRk |- *; exact SRk. }
      cbn [fst snd]. split; [reflexivity|]. split; [left; reflexivity|].
      split; [exact BUF'|]. split; [exact FSTn|]. split; [exact TMPNAME_range|].
      split; [rewrite TMPNAME_len, tmpl_len; lia|]. intros _. exact TMPNAME_path.
    - (* [comment removed for export] *)
      apply implM_ret. apply evt_done.
      eexists _, m', _. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AGk|].
      split. { pose proof (GIo_stdio_step_err R s CL FB m m' _ (bv_unsigned sp) (ps_libc s) _ G MUW WMT HWT SPM ltac:(unfold utp; exact ERR') SRk) as G'.
               destruct s as [sh sl so st']. cbn [set_libc ps_libc ps_heap ps_outfile ps_tls] in G'. exact G'. }
      cbn [fst snd]. split; [reflexivity|]. split; [right; lia|].
      split; [exact BUF'|]. split; [exact FSTn|]. split; [exact TMPNAME_range|].
      split; [rewrite TMPNAME_len, tmpl_len; lia|]. intros _. exact TMPNAME_path.
  Qed.
  End Sz15.
  Theorem mkstemp_o_proof : ltac:(let t := eval cbv delta [mkstemp_o_proof__stmt] in mkstemp_o_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME n tmpl buf. ltac2:(SecDiet.SzSec.closeP 'mkstemp_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueMk.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.CallKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_mkstemp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_sys.TwB.
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


Section WithCeil.
Context {CEILV : CEIL}.
Section GlueMk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.spo_facts K KST).
  #[local] Notation GIo_stdio_step_err := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Stdio_glue_fo__S3.Stdio_glue_fo.TwB.GIo_stdio_step_err K KST HFL).
  #[local] Notation STDIOR_agree := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.STDIOR_agree).
  #[local] Notation keeps_of_stdio := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.keeps_of_stdio K).
  #[local] Notation client_range_lo := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.client_range_lo K).

  (* [comment removed for export] *)
  Lemma tmpl_Z : map bv_unsigned (map S3.PcapRep.TwB.b8 TEMPLATE) = TEMPLATE.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpl_TMPL0 : map S3.PcapRep.TwB.b8 TEMPLATE ++ [Z_to_bv 8 0] = TMPL0.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpl_len : length (map S3.PcapRep.TwB.b8 TEMPLATE) = 29%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma seal_TEMPLATE : seal_name TEMPLATE = Some TMPNAME.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpn_bytes : TMPN0 = map S3.PcapRep.TwB.b8 TMPNAME ++ [Z_to_bv 8 0].
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpn_tobytes : to_bytes TMPNAME = TMPN.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma TMPN0_len : length TMPN0 = 25%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma TMPN_nonul : ~ In (Z_to_bv 8 0) TMPN.
  Proof using Type. pin_using tt. unfold TMPN, TMPNAME. cbn. intuition discriminate. Qed.
  Lemma TMPNAME_range : Forall (fun z => 0 < z < 256) TMPNAME.
  Proof using Type. pin_using tt. unfold TMPNAME. cbn. repeat (constructor; [lia|]). constructor. Qed.
  Lemma TMPNAME_len : length TMPNAME = 24%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma TMPNAME_path : Namei.path_has_slash (map S3.PcapRep.TwB.b8 TMPNAME) = false
                       /\ map S3.PcapRep.TwB.b8 TMPNAME <> Uapi.dot_path /\ map S3.PcapRep.TwB.b8 TMPNAME <> Namei.dotdot_path.
  Proof using Type. pin_using tt.
    split; [vm_compute; reflexivity|].
    split; intros E; apply (f_equal (@length byte)) in E; vm_compute in E; discriminate E.
  Qed.

  (* [comment removed for export] *)
  Definition client_cover__stmt : Prop := forall R (CL FB : list cblk) SP D n (W0 : list (Z * Z)) m m',
    client_range R CL SP D n -> 0 < n -> CEILZ <= SP ->
    munch (W0 ++ [(D, D + n)]) m m' ->
    exists W', munch (W0 ++ W') m m' /\ Forall (stdio_iv R CL FB SP) W'.
  Section Sz12.
  Variables R CL FB SP D n W0 m m' : ltac2:(SecDiet.SzSec.tyM 'client_cover__stmt "vvvvvvvvv" @R).
  Lemma client_cover__body : ltac2:(SecDiet.SzSec.bodyP 'client_cover__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros CR NP CSP MU.
    assert (OA : forall W1 W2 y, outside (W1 ++ W2) y <-> outside W1 y /\ outside W2 y).
    { induction W1 as [|[u v] W1 IH]; intros W2 y; cbn in *; [tauto|]. rewrite IH. tauto. }
    destruct CR as [CR|CR].
    - exists (map (fun b : cblk => (Z.max D (cb_addr b), Z.min (D + n) (cb_addr b + cb_size b))) CL). split.
      + intros x Hx. apply MU. apply OA in Hx as [O1 O2]. apply OA. split; [exact O1|]. cbn [outside]. split; [| exact I].
        intros HDn. pose proof (CR (bv_unsigned x) HDn) as Hb. apply in_block_In in Hb as (b & HbIn & Hb).
        assert (OM : forall (L : list cblk) y, outside (map (fun b : cblk => (Z.max D (cb_addr b), Z.min (D + n) (cb_addr b + cb_size b))) L) y ->
                       forall b', In b' L -> ~ (Z.max D (cb_addr b') <= y < Z.min (D + n) (cb_addr b' + cb_size b'))).
        { induction L as [|c L IHL]; intros y Hy b' Hb'; [destruct Hb'|]. cbn in Hy. destruct Hy as [Y1 Y2]. destruct Hb' as [<-|Hb']; [exact Y1| apply IHL; assumption]. }
        apply (OM CL (bv_unsigned x) O2 b HbIn). lia.
      + apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b & <- & HbIn). unfold stdio_iv. right; left.
        unfold iv_in_block. apply Exists_exists. exists b. split; [apply in_or_app; left; exact HbIn| cbn [fst snd]; lia].
    - exists [(D, D + n)]. split; [exact MU|]. apply Forall_cons; [| apply Forall_nil]. unfold stdio_iv. left. cbn [fst snd]. destruct CR. lia.
  Qed.
  End Sz12.
  Lemma client_cover : ltac:(let t := eval cbv delta [client_cover__stmt] in client_cover__stmt in exact t).
  Proof using Type. intros R CL FB SP D n W0 m m'. ltac2:(SecDiet.SzSec.closeP 'client_cover__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition STDIOR_keep_cr__stmt : Prop := forall (l : libc_st hptr) FB (CL : list cblk) R m m' W SP D n,
    STDIOR l FB m -> blocks_ok (utp R) (CL ++ FB) -> tls_block_ok_u (utp R - 200) -> munch W m m' -> wmono usegs m m' ->
    client_range R CL SP D n -> CEILZ <= SP ->
    Forall (fun iv : Z * Z => CEILZ <= fst iv \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160) \/ (D <= fst iv /\ snd iv <= D + n)) W ->
    STDIOR l FB m'.
  Section Sz13.
  Variables l FB CL R m m' W SP D n : ltac2:(SecDiet.SzSec.tyM 'STDIOR_keep_cr__stmt "vvvvvvvvvv" @l).
  Lemma STDIOR_keep_cr__body : ltac2:(SecDiet.SzSec.bodyP 'STDIOR_keep_cr__stmt "vvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros SR BOK TB MU WM CR CSP HW.
    pose proof BOK as [BO BA]. pose proof BO as BO'. apply Forall_app in BO'. destruct BO' as [BO1 BO2].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    unfold tls_block_ok_u in TB. destruct TB as (TBA & TB0 & TBC & TBI).
    eapply (STDIOR_agree l FB m m' (fun a => S3.GI.TwB.stdio_static a \/ in_block FB a)); [exact SR| | intros a Ha; left; exact Ha | intros a Ha; right; exact Ha].
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha HP.
    eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd] in Hiv |- *. intros Hin.
    destruct HP as [HS0|HB].
    - unfold S3.GI.TwB.stdio_static in HS0. destruct Hiv as [X|[X|X]]; [lia| lia|].
      destruct CR as [CR|CR]; [| lia].
      destruct (in_block_facts (utp R) CL a BO1 (CR a ltac:(lia))) as (_ & _ & F3 & _). lia.
    - destruct (in_block_facts (utp R) FB a BO2 HB) as (F1 & F2 & F3 & F4).
      destruct Hiv as [X|[X|X]]; [lia| lia|].
      destruct CR as [CR|CR]; [| lia].
      pose proof (CR a ltac:(lia)) as HC. apply in_block_In in HC as (b & HbIn & Hb). apply in_block_In in HB as (b' & Hb'In & Hb').
      pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia.
  Qed.
  End Sz13.
  Lemma STDIOR_keep_cr : ltac:(let t := eval cbv delta [STDIOR_keep_cr__stmt] in STDIOR_keep_cr__stmt in exact t).
  Proof using Type. intros l FB CL R m m' W SP D n. ltac2:(SecDiet.SzSec.closeP 'STDIOR_keep_cr__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition keeps_cr__stmt : Prop := forall R (s : PS) CL FB m m' W SP D n,
    GIo K R s CL FB m -> munch W m m' -> wmono usegs m m' ->
    Forall (fun iv : Z * Z => (CEILZ <= fst iv /\ snd iv <= SP) \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160) \/ (D <= fst iv /\ snd iv <= D + n)) W ->
    CEILZ <= SP ->
    agrees_on (fun a => client_keeps CL SP a /\ ~ (D <= a < D + n)) m m'.
  Section Sz14.
  Variables R s CL FB m m' W SP D n : ltac2:(SecDiet.SzSec.tyM 'keeps_cr__stmt "vvvvvvvvvv" @R).
  Lemma keeps_cr__body : ltac2:(SecDiet.SzSec.bodyP 'keeps_cr__stmt "vvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G MU WM HW HSP.
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    eapply agrees_on_weaken.
    - eapply (keeps_of_stdio R s CL FB m m' W SP (fun a => (utp R - 164 <= a < utp R - 160) \/ (D <= a < D + n))); [exact G| exact MU| exact WM| | exact HSP].
      eapply Forall_impl; [| exact HW]. cbv beta. intros iv [X|[X|X]].
      + left; exact X.
      + right; right; right; right. intros a Ha. left. lia.
      + right; right; right; right. intros a Ha. right. lia.
    - cbv beta. intros a [Hk HN]. split; [exact Hk|]. intros [Hr|Hr]; [| exact (HN Hr)].
      destruct Hk as [Hk|Hk]; [lia|]. destruct (in_block_facts _ _ a BO1 Hk) as (F1 & F2 & F3 & F4). lia.
  Qed.
  End Sz14.
  Lemma keeps_cr : ltac:(let t := eval cbv delta [keeps_cr__stmt] in keeps_cr__stmt in exact t).
  Proof using Type. intros R s CL FB m m' W SP D n. ltac2:(SecDiet.SzSec.closeP 'keeps_cr__body "vvvvvvvvvv"). Qed.

  Definition mkstemp_o_proof__stmt : Prop := mkstemp_stmt_o K.
  Section Sz15.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME n tmpl buf : ltac2:(SecDiet.SzSec.tyM 'mkstemp_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma mkstemp_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'mkstemp_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
 intros SPO -> BUF FST NNUL -> NLE NMAX NCR.
 (* [comment removed for export] *)
 assert (NMAXZ : (Z.of_nat n <= 4096)%Z) by (clear - NMAX; lia). clear NMAX.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK' & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    subst tp. unfold STDIO_STACK in *. rewrite tmpl_len in NLE, FST.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof CT as (tlst & errv & _ & ERR & _).
    destruct SSP as [GOT GUARD].
    destruct (client_range_lo R s CL FB m (bv_unsigned sp) NAME (Z.of_nat n) lo G NCR ltac:(lia) LOR ltac:(lia)) as (N0 & NSEP & NHI & NROM').
    assert (NROM : NAME + Z.of_nat n <= 0x10000 \/ 0x56000 <= NAME) by (unfold rc_lo in *; lia).
    assert (NTLS : NAME + Z.of_nat n <= utp R - 164 \/ utp R - 160 <= NAME).
    { destruct NCR as [CR|CR].
      - pose proof BOK as [BO _]. apply Forall_app in BO as [BO1 _].
        destruct (Z_lt_le_dec (Z.max NAME (utp R - 164)) (NAME + Z.of_nat n)) as [LT|GE]; [| left; lia].
        destruct (Z_lt_le_dec NAME (utp R - 160)) as [LT2|GE2]; [| right; exact GE2].
        exfalso. pose proof (in_block_facts (utp R) CL (Z.max NAME (utp R - 164)) BO1 (CR (Z.max NAME (utp R - 164)) ltac:(lia))) as (_ & _ & _ & F4). lia.
      - unfold rc_spmain in CR. unfold rc_lo in *. lia. }
    (* [comment removed for export] *)
    pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as [LB _].
    assert (LR : length (skipn 30 buf) = (n - 30)%nat) by (rewrite length_skipn; lia).
    pose proof (rw_cells_split_CB usegs m NAME [] n buf [] [30%nat; (n - 30)%nat] BUF ltac:(cbn; lia)) as BUF2.
    cbn [app mk_CB_cells] in BUF2. rewrite tmpl_TMPL0 in FST. change (29 + 1)%nat with 30%nat in FST. rewrite FST in BUF2.
    rewrite (firstn_all2 (n := (n - 30)%nat) (skipn 30 buf)) in BUF2 by lia.
    set (rest := skipn 30 buf) in *. clearbody rest.
    (* [comment removed for export] *)
    unfold s_mkstemp, Stdio.mkstemp. rewrite tmpl_Z, seal_TEMPLATE, tmpn_tobytes. unfold MKSTEMP_MODE.
    (* [comment removed for export] *)
    eapply implM_evt.
    { eapply mk_S1 with (lo := lo) (n := n) (NAME := NAME); first [exact BUF2 | exact ST | exact MI | unfold rc_lo in *; lia | match goal with |- ?g => idtac "S1 side:" g end]. }
    cbv beta. intros ms1 PO. destruct PO as (x1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (BUF1 : rw_cells usegs m1 NAME [CB 30 TMPL0; CB (n - 30) rest]).
    { eapply rw_cells_transport; [exact BUF2| exact MU1| exact WM1|]. cbn. lia. }
    (* [comment removed for export] *)
    eapply implM_evt.
    { eapply mk_S2 with (n := n) (NAME := NAME); first [exact BUF1 | exact MI1 | unfold rc_lo in *; lia | match goal with |- ?g => idtac "S2 side:" g end]. }
    cbv beta. intros ms2 (b4' & ->).
    (* [comment removed for export] *)
    eapply implM_evt.
    { eapply mk_S3 with (lo := lo) (n := n) (NAME := NAME); first [exact BUF1 | exact FR1 | exact ST1 | exact MI1 | unfold rc_lo in *; lia | match goal with |- ?g => idtac "S3 side:" g end]. }
    cbv beta. intros ms3 PO. destruct PO as (x1' & v0 & v1 & v2 & a0' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & BUF3 & FR3 & MU3 & WM3 & MI3 & ST3).
    (* [comment removed for export] *)
    eapply implM_evt.
    { eapply mk_S4 with (lo := lo) (n := n) (NAME := NAME) (sA := sp); first [exact FR3 | exact ST3 | exact MI3 | unfold rc_lo in *; lia | match goal with |- ?g => idtac "S4 side:" g end]. }
    cbv beta. intros ms4 (-> & ST4).
    (* [comment removed for export] *)
    assert (MU13 : munch [(bv_unsigned sp - 64, bv_unsigned sp); (NAME, NAME + 30)] m m3).
    { apply (munch_trans _ m m1 m3); [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros; lia. }
    assert (WM13 : wmono usegs m m3) by (eapply wmono_trans; [exact WM1| exact WM3]).
    assert (ERR3 : rw_cells usegs m3 (bv_unsigned (rc_tp R) + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU13| exact WM13|]. cbn. unfold utp, rc_lo in *. lia. }
    assert (GOT3 : rw_cells usegs m3 got_ssp [C8 (Z_to_bv 64 ssp_guard)]).
    { eapply rw_cells_transport; [exact GOT| exact MU13| exact WM13|]. unfold got_ssp, ssp_guard. cbn. unfold rc_lo in *. lia. }
    assert (GUARD3 : rw_cells usegs m3 ssp_guard [C8 (rc_canary R)]).
    { eapply rw_cells_transport; [exact GUARD| exact MU13| exact WM13|]. unfold got_ssp, ssp_guard. cbn. unfold rc_lo in *. lia. }
    assert (STR3 : bytes_at usegs m3 NAME (TMPN ++ [Z_to_bv 8 0])).
    { pose proof (proj2 (proj1 BUF3)) as X. cbn [cells_bytes cbytes] in X.
      rewrite <- TMPN0_eq, <- (app_assoc (TMPN ++ [Z_to_bv 8 0]) (skipn 25 SEALED0)) in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X as [X _].
      exact X. }
    (* [comment removed for export] *)
    eapply (implM_msys_of_enode usegs); [reflexivity | |].
    { eapply (open_w_spec ra sp gp (rc_tp R)) with (lo := lo) (path := TMPN) (errv := errv) (canary := rc_canary R);
        first [exact ST4 | rewrite unsigned_lit by lia; exact STR3 | exact ERR3 | exact GOT3 | exact GUARD3 | exact MI3 | reflexivity | exact TMPN_nonul
              | rewrite ?unsigned_lit by lia; rewrite ?TMPN_len; unfold utp, rc_lo, got_ssp, ssp_guard in *; lia
              | left; vm_compute; reflexivity   (* [comment removed for export] *)
              | match goal with |- ?g => idtac "OW side:" g end]. }
    intros r ms' PO. unfold open_post in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m' & -> & MU' & WM' & MI' & ST' & ERR' & STR' & GOT' & GUARD' & Hr).
    (* [comment removed for export] *)
    assert (MUT : munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned (rc_tp R) + -164, bv_unsigned (rc_tp R) + -160); (NAME, NAME + Z.of_nat n)] m m').
    { apply (munch_trans _ m m3 m'); [eapply munch_weaken; [| exact MU13] | eapply munch_weaken; [| exact MU']]; unfold sub_fp; cbn [outside]; intros; lia. }
    assert (WMT : wmono usegs m m') by (eapply wmono_trans; [exact WM13| exact WM']).
    destruct (client_cover R CL FB (bv_unsigned sp) NAME (Z.of_nat n)
                [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned (rc_tp R) + -164, bv_unsigned (rc_tp R) + -160)] m m'
                NCR ltac:(lia) ltac:(unfold rc_lo in *; lia) MUT) as (W' & MUW & HW').
    (* [comment removed for export] *)
    assert (BUF' : rw_cells usegs m' NAME [CB n ((TMPN0 ++ skipn 25 SEALED0) ++ rest)]).
    { assert (B3' : rw_cells usegs m' NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]).
      { eapply rw_cells_transport; [exact BUF3| exact MU'| exact WM'|]. cbn. unfold utp in *. lia. }
      eapply (rw_cells_recast m' NAME _ _ B3').
      - cbn [cells_wf cell_wf]. split; [| exact I]. rewrite !length_app. change (length TMPN0) with 25%nat. change (length (skipn 25 SEALED0)) with 5%nat. lia.
      - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
      - cbn. lia. }
    assert (FSTn : firstn (length TMPNAME + 1) ((TMPN0 ++ skipn 25 SEALED0) ++ rest) = map S3.PcapRep.TwB.b8 TMPNAME ++ [Z_to_bv 8 0]).
    { rewrite TMPNAME_len. change (24 + 1)%nat with 25%nat. rewrite <- app_assoc, firstn_app, TMPN0_len, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite firstn_all2 by (rewrite TMPN0_len; lia). exact tmpn_bytes. }
    assert (SRk : STDIOR (ps_libc s) FB m').
    { eapply (STDIOR_keep_cr (ps_libc s) FB CL R m m' _ (bv_unsigned sp) NAME (Z.of_nat n)); [exact SR| exact BOK| exact TB| exact MUT| exact WMT| exact NCR| unfold rc_lo in *; lia|].
      apply Forall_cons; [left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; left; cbn; unfold utp; lia|].
      apply Forall_cons; [right; right; cbn; lia| apply Forall_nil]. }
    assert (AGk : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (NAME <= a < NAME + Z.of_nat n)) m m').
    { eapply (keeps_cr R s CL FB m m' _ (bv_unsigned sp) NAME (Z.of_nat n)); [exact G| exact MUT| exact WMT| | unfold rc_lo in *; lia].
      apply Forall_cons; [left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; left; cbn; unfold utp; lia|].
      apply Forall_cons; [right; right; cbn; lia| apply Forall_nil]. }
    assert (HWT : Forall (fun iv : Z * Z => stdio_iv R CL FB (bv_unsigned sp) iv \/ (fst iv = utp R - 164 /\ snd iv = utp R - 160))
                    ([(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned (rc_tp R) + -164, bv_unsigned (rc_tp R) + -160)] ++ W')).
    { apply Forall_app. split; [| eapply Forall_impl; [| exact HW']; intros iv X; left; exact X].
      apply Forall_cons; [left; left; cbn; unfold rc_lo in *; lia|]. apply Forall_cons; [right; cbn; unfold utp; lia| apply Forall_nil]. }
    destruct r as [e|fd]; cbn [open_ret open_errno] in ERR' |- *.
    - (* [comment removed for export] *)
      apply implM_upd_lc. apply implM_ret. apply evt_done.
      eexists _, m', _. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AGk|].
      split. { eapply (GIo_stdio_step_err R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MUW| exact WMT| exact HWT| exact SPM| unfold utp; exact ERR'|].
               unfold STDIOR in SRk |- *. destruct (ps_libc s) as [xso xse xfs xer]; cbn [lc_stdout lc_stderr lc_files set_errno_lc] in SRk |- *; exact SRk. }
      cbn [fst snd]. split; [reflexivity|]. split; [left; reflexivity|].
      split; [exact BUF'|]. split; [exact FSTn|]. split; [exact TMPNAME_range|].
      split; [rewrite TMPNAME_len, tmpl_len; lia|]. intros _. exact TMPNAME_path.
    - (* [comment removed for export] *)
      apply implM_ret. apply evt_done.
      eexists _, m', _. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AGk|].
      split. { pose proof (GIo_stdio_step_err R s CL FB m m' _ (bv_unsigned sp) (ps_libc s) _ G MUW WMT HWT SPM ltac:(unfold utp; exact ERR') SRk) as G'.
               destruct s as [sh sl so st']. cbn [set_libc ps_libc ps_heap ps_outfile ps_tls] in G'. exact G'. }
      cbn [fst snd]. split; [reflexivity|]. split; [right; lia|].
      split; [exact BUF'|]. split; [exact FSTn|]. split; [exact TMPNAME_range|].
      split; [rewrite TMPNAME_len, tmpl_len; lia|]. intros _. exact TMPNAME_path.
  Qed.
  End Sz15.
  Theorem mkstemp_o_proof : ltac:(let t := eval cbv delta [mkstemp_o_proof__stmt] in mkstemp_o_proof__stmt in exact t).
  Proof using HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME n tmpl buf. ltac2:(SecDiet.SzSec.closeP 'mkstemp_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueMk.

End WithCeil.
End TwB.
End Stdio_glue_mk.
