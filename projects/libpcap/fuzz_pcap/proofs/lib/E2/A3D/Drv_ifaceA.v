(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MAIN_ENTRY : Z := 0x84120.          (* [comment removed for export] *)
Definition TARGET_ALLOC_INIT_ENTRY : Z := 0x843e4.   (* [comment removed for export] *)
Definition TARGET_ALLOC_COUNT_ENTRY : Z := 0x843e8.  (* [comment removed for export] *)
Definition TARGET_RUN_ENTRY : Z := 0x843f0.    (* [comment removed for export] *)
Definition EMIT_PRINTF_ENTRY : Z := 0x84578.   (* [comment removed for export] *)
Definition OPEN_ENTRY : Z := 0x94a38.          (* [comment removed for export] *)
Definition READ_ENTRY : Z := 0x44488.          (* [comment removed for export] *)
Definition MEMCPY_I_ENTRY : Z := 0x54960.      (* [comment removed for export] *)
Definition VPRINTF_ENTRY : Z := 0x4449c.       (* [comment removed for export] *)
Definition EXIT_ENTRY : Z := 0x947c4.          (* [comment removed for export] *)
Definition GOT_STDERR : Z := 0xa6110.          (* [comment removed for export] *)
Definition STDERR_P : Z := 0xa53a0.            (* [comment removed for export] *)
Definition STDERR_FILE : Z := 0xa9ab0.         (* [comment removed for export] *)
Definition GOT_FUZZ_INIT : Z := 0xa6118.       (* [comment removed for export] *)
Definition DRV_INIT_FLAG : Z := 0x5e0c50.      (* [comment removed for export] *)
Definition DRV_EMPTY : Z := 0x5e0c60.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DRV_IN_CB : Z := 0x5e0c54.          (* [comment removed for export] *)
Definition ATEXIT_ENTRY : Z := 0x946ac.        (* [comment removed for export] *)
Definition GUARD_ENTRY : Z := 0x84548.         (* [comment removed for export] *)
Definition ATX_CALL : Z := 0x94770.            (* [comment removed for export] *)
Definition COV_HOOK : Z := 0x73b80.            (* [comment removed for export] *)
Definition ATX : Z := 0x601608.                (* [comment removed for export] *)
Definition LOCK_ENTRY : Z := 0x9f074.          (* [comment removed for export] *)
Definition UNLOCK_ENTRY : Z := 0x9f2fc.        (* [comment removed for export] *)
Definition READ_STAGE : Z := 0x5d0c50.         (* [comment removed for export] *)
Definition FMT_D : Z := 0x1488a.               (* [comment removed for export] *)
Definition FMT_USAGE : Z := 0x1590b.           (* [comment removed for export] *)
Definition FMT_CANNOT_OPEN : Z := 0x1d902.     (* [comment removed for export] *)
Definition FMT_READ_ERROR : Z := 0x1d917.      (* [comment removed for export] *)
Definition FMT_TOO_BIG : Z := 0x197df.         (* [comment removed for export] *)
Definition MSG_OOM : Z := 0x14876.             (* [comment removed for export] *)
Definition MSG_SHORT_HDR : Z := 0x1fa85.       (* [comment removed for export] *)
Definition MSG_CFG_OVERRUN : Z := 0x1591c.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DRV_RODATA_LO : Z := 0x10000.
Definition DRV_RODATA_HI : Z := 0x21020.

Definition TARGET_RUN_STACK : Z := FUZZ_STACK + 80 + STDIO_STACK.   (* [comment removed for export] *)
Definition READ_I_STACK : Z := 2208.           (* [comment removed for export] *)
Definition MEMCPY_I_STACK : Z := 2240.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition drv_traces : list (list Z) :=
  [ [AMALLOC_PC; 0x84174]; [AMALLOC_PC; 0x841c8]; [AFREE_PC; 0x841ec]; [AFREE_PC; 0x8431c];     (* [comment removed for export] *)
    [AMALLOC_PC]; [AFREE_PC];                                                                    (* [comment removed for export] *)
    [AMALLOC_PC; 0x84454]; [AFREE_PC; 0x844e8] ].                                                (* [comment removed for export] *)
Definition traces_drv (L : alayout) : Prop := forall tr, In tr drv_traces -> In tr (al_U L).
(* [comment removed for export] *)
Definition RA_FUZZ : Z := 0x844bc.

(* [comment removed for export] *)
Definition ATX_KEEP : list (Z * Z) := [(DRV_INIT_FLAG, DRV_INIT_FLAG + 8); (ATX, ATX + 544)].          (* [comment removed for export] *)
Definition ATX_DOM : list (Z * Z) := ATX_KEEP ++ [(0x601848, 0x601850)].                             (* [comment removed for export] *)
(* [comment removed for export] *)
Definition atx_cells (reg : bool) (cb : Z) (m : mem) : Prop :=
     rw_cells asegs m 0x5e0c50 [C1 (Z_to_bv 8 (Z.b2z reg))]                               (* [comment removed for export] *)
  /\ rw_cells asegs m 0x5e0c54 [C1 (Z_to_bv 8 cb)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601608 [C1 (Z_to_bv 8 0)]                                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x60160c [C4 (Z_to_bv 64 0)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601610 [C4 (Z_to_bv 64 (1 + Z.b2z reg))]                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601618 [C8 (Z_to_bv 64 0x601620)]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601620 [C8 (Z_to_bv 64 0)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601628 [C8 (Z_to_bv 64 0x94770)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601630 [C8 (Z_to_bv 64 (if reg then 0x94770 else 0))]             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601728 [C8 (Z_to_bv 64 0x73b80)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601730 [C8 (Z_to_bv 64 (if reg then 0x84548 else 0))]             (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word), rw_cells asegs m 0x601848 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]).   (* [comment removed for export] *)

Section DrvIfaces.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation GIO := GIOA.
  #[local] Abbreviation SPOA := (std_pre_o GIOA).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rs_iv (iv : Z * Z) : Prop := READ_STAGE <= fst iv /\ snd iv <= READ_STAGE + 65536.
  Definition drv_ivA (CL : list cblk) (iv : Z * Z) : Prop := client_ivA [] CL iv \/ rs_iv iv.

  Record gia_drv_laws (USP : Z) (SB : list byte) : Prop := mkGD {
    (* [comment removed for export] *)
    gd_errno : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> exists e : word, rw_cells asegs m (ATP + -164) [C4 e];
    (* [comment removed for export] *)
    gd_misc : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 rw_cells asegs m GOT_STDERR [C8 (Z_to_bv 64 STDERR_P)] /\ rw_cells asegs m STDERR_P [C8 (Z_to_bv 64 STDERR_FILE)]
                 /\ rw_cells asegs m GOT_FUZZ_INIT [C8 (Z_to_bv 64 0)];
    (* [comment removed for export] *)
    gd_canary : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 rw_cells asegs m 0xa6160 [C8 (Z_to_bv 64 0x6015f8)] /\ exists c : word, rw_cells asegs m 0x6015f8 [C8 c];
    (* [comment removed for export] *)
    gd_args : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> mobjA RNG m USP (Z.of_nat (length SB) - 16);   (* [comment removed for export] *)
    (* [comment removed for export] *)
    gd_unp : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 unpoisoned m DRV_RODATA_LO DRV_RODATA_HI /\ unpoisoned m READ_STAGE (READ_STAGE + 65536);
    (* [comment removed for export] *)
    gd_frame : forall L RNG s CL FB FL m m' W, GIOA L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
                 Forall (drv_ivA CL) W -> GIOA L RNG s CL FB FL m';
    gd_frame_errno : forall L RNG s CL FB FL m m' W (e : word), GIOA L RNG s CL FB FL m ->
                 munch ((ATP + -164, ATP + -160) :: W) m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W ->
                 rw_cells asegs m' (ATP + -164) [C4 e] -> GIOA L RNG s CL FB FL m'
  }.

  (* [comment removed for export] *)
  Record gia_atx_laws : Prop := mkGA {
    (* [comment removed for export] *)
    ga_get : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> exists reg : bool, atx_cells reg 0 m;
    (* [comment removed for export] *)
    ga_frame : forall L RNG s CL FB FL m m' W (reg' : bool), GIOA L RNG s CL FB FL m ->
                 munch (ATX_KEEP ++ W) m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W ->
                 atx_cells reg' 0 m' -> GIOA L RNG s CL FB FL m'
  }.

  (* [comment removed for export] *)
  Variable GIOA1 : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Record gia_cb_laws : Prop := mkGCB {
    gc_set : forall L RNG s CL FB FL m m', GIOA L RNG s CL FB FL m -> munch [(DRV_IN_CB, DRV_IN_CB + 1)] m m' -> wmono asegs m m' ->
                 rw_cells asegs m' 0x5e0c54 [C1 (Z_to_bv 8 1)] -> GIOA1 L RNG s CL FB FL m';
    gc_cell : forall L RNG s CL FB FL m, GIOA1 L RNG s CL FB FL m -> exists reg : bool, atx_cells reg 1 m;
    gc_clr : forall L RNG s CL FB FL m m', GIOA1 L RNG s CL FB FL m -> munch [(DRV_IN_CB, DRV_IN_CB + 1)] m m' -> wmono asegs m m' ->
                 rw_cells asegs m' 0x5e0c54 [C1 (Z_to_bv 8 0)] -> GIOA L RNG s CL FB FL m'
  }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition std_pre_d (L : alayout) (RNG : footprint) (sp tp : word) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo budget : Z) (m : mem) : Prop :=
    GIOA L RNG s CL FB FL m /\ stk asegs m lo (bv_unsigned sp) /\ ATOP + 4096 <= lo /\ lo + budget <= bv_unsigned sp
    /\ (bv_unsigned sp < 2^47 /\ al_top L <= 2^47) /\ mem_inv asegs m /\ tp = Z_to_bv 64 ATP /\ bv_unsigned sp mod 16 = 0
    /\ (rng RNG lo (al_top L - lo) /\ rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG).

  #[using="Type"] Lemma std_pre_o_d : forall L RNG sp tp s CL FB FL lo budget m,
    std_pre_o GIOA L RNG sp tp s CL FB FL lo budget m -> 0 <= budget -> std_pre_d L RNG sp tp s CL FB FL lo budget m.
  Proof.
    intros L RNG sp tp s CL FB FL lo budget m (G & ST & LO & BU & (S1 & S2) & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS) HB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    split; [exact G|]. split; [exact ST|]. split; [exact LO|]. split; [exact BU|]. split; [split; [lia| exact S2]|].
    split; [exact MI|]. split; [exact TPE|]. split; [exact ALN|].
    split; [exact RSTK|]. split; [eapply rng_sub'; [exact RSTK| lia]|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
  Qed.

  (* [comment removed for export] *)
  Definition malloc_stmt_d : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo n : Z),
      std_pre_d L RNG sp tp s CL FB FL lo MALLOC_STACK m -> a0 = Z_to_bv 64 n -> 1 <= n < 2^29 - 2^16 ->
      unw_okA L RNG m lo AMALLOC_PC sp s0 ra ->
      implMG RNG (pmalloc HO n) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => False
              | Some q => exists A junk, a0v = Z_to_bv 64 A /\ GIO L RNG' s' ((q, A, n) :: CL) FB FL m'
                          /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom asegs)).

  Definition free_stmt_d : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (C1 C2 FB : list cblk) (FL : list fblock) (q : hptr) (A n lo : Z),
      std_pre_d L RNG sp tp s (C1 ++ (q, A, n) :: C2) FB FL lo FREE_STACK m -> a0 = Z_to_bv 64 A ->
      unw_okA L RNG m lo AFREE_PC sp s0 ra ->
      implMG RNG (pfree HO q) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' (C1 ++ C2) FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition out_post_o (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo : Z) (m : mem)
      : unit -> PS -> footprint -> machine_state -> Prop :=
    fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
       /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
       /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
       /\ GIO L RNG' s' CL FB FL m'.

  (* [comment removed for export] *)
  Definition eprintf_s_stmt_o (FMT fl : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo P : Z) (str slack : list byte),
      std_pre_d L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      bv_unsigned sp - 32 <= al_top L ->          (* [comment removed for export] *)
      a0 = Z_to_bv 64 STDERR_FILE -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      mobjA RNG m FMT (fl + 1) ->
      bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->   (* [comment removed for export] *)
      mobjA RNG m P (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) ->
      (forall a, P <= a < P + Z.of_nat (length str) + 1 -> client_keeps FL CL (bv_unsigned sp) a) ->
      implMG RNG (@eprintf PS hptr ps_libc set_libc (mk (map bv_unsigned str))) s
        (out_post_o ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition eprintf_i_stmt_o (FMT fl v : Z) (ps : list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo : Z),
      std_pre_d L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      bv_unsigned sp - 32 <= al_top L ->          (* [comment removed for export] *)
      a0 = Z_to_bv 64 STDERR_FILE -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 v ->
      mobjA RNG m FMT (fl + 1) ->
      implMG RNG (@eprintf PS hptr ps_libc set_libc ps) s
        (out_post_o ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition efwrite_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo MSG : Z) (bs : list byte),
      std_pre_d L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 MSG -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 STDERR_FILE ->
      bytes_at asegs m MSG bs -> (DRV_RODATA_LO <= MSG /\ MSG + Z.of_nat (length bs) <= DRV_RODATA_HI) -> (1 <= length bs)%nat ->
      mobjA RNG m MSG (Z.of_nat (length bs)) ->
      implMG RNG (@efwrite PS hptr ps_libc set_libc (map bv_unsigned bs)) s
        (out_post_o ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition vprintf_d_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo AP v : Z) (rest : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 FMT_D -> a1 = Z_to_bv 64 AP -> -2^31 <= v < 2^31 ->
      mobjA RNG m FMT_D 4 ->
      rw_cells asegs m AP [C8 (Z_to_bv 64 v); CB 48 rest] -> bv_unsigned sp <= AP -> AP + 56 <= al_top L ->
      implMG RNG (@printf PS hptr ps_libc set_libc (pieces_emit_d v)) s
        (out_post_o ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition target_run_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL : list cblk) (lo : Z) (m : mem) : Z -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' FB',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m m'
      /\ GIO L RNG' s' CL FB' [] m' /\ 0 <= r <= 2.

  Definition target_run_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo A Lc : Z) (content : list byte),
      std_pre_d L RNG sp tp s CL FB [] lo TARGET_RUN_STACK m -> bv_unsigned sp - 48 < al_top L ->     (* [comment removed for export] *)
      traces_drv L -> traces_fuzz_one TP L RA_FUZZ [] ->
      bytes_at asegs m A content -> 0 <= Lc -> 6 + Lc <= Z.of_nat (length content) -> Z.of_nat (length content) <= 2^26 ->
      (exists b, In b CL /\ cb_addr b <= A /\ A + Z.of_nat (length content) <= cb_addr b + cb_size b) ->
      a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 Lc -> a2 = Z_to_bv 64 (A + 6 + Lc) -> a3 = Z_to_bv 64 (Z.of_nat (length content) - 6 - Lc) ->
      implMG RNG (run HO FO sites (firstn (Z.to_nat Lc) (skipn 2 (map bv_unsigned content)))
                               (skipn (Z.to_nat (6 + Lc)) (map bv_unsigned content))) s
        (target_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TARGET_RUN_ENTRY) fc None m (seg_rom asegs)).
End DrvIfaces.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MAIN_ENTRY : Z := 0x84188.          (* [comment removed for export] *)
Definition TARGET_ALLOC_INIT_ENTRY : Z := 0x8444c.   (* [comment removed for export] *)
Definition TARGET_ALLOC_COUNT_ENTRY : Z := 0x84450.  (* [comment removed for export] *)
Definition TARGET_RUN_ENTRY : Z := 0x84458.    (* [comment removed for export] *)
Definition EMIT_PRINTF_ENTRY : Z := 0x845e0.   (* [comment removed for export] *)
Definition OPEN_ENTRY : Z := 0x94e1c.          (* [comment removed for export] *)
Definition READ_ENTRY : Z := 0x444f0.          (* [comment removed for export] *)
Definition MEMCPY_I_ENTRY : Z := 0x549c8.      (* [comment removed for export] *)
Definition VPRINTF_ENTRY : Z := 0x44504.       (* [comment removed for export] *)
Definition EXIT_ENTRY : Z := 0x94ba8.          (* [comment removed for export] *)
Definition GOT_STDERR : Z := 0xa64f0.          (* [comment removed for export] *)
Definition STDERR_P : Z := 0xa5780.            (* [comment removed for export] *)
Definition STDERR_FILE : Z := 0xa9e90.         (* [comment removed for export] *)
Definition GOT_FUZZ_INIT : Z := 0xa64f8.       (* [comment removed for export] *)
Definition DRV_INIT_FLAG : Z := 0x5e1050.      (* [comment removed for export] *)
Definition DRV_EMPTY : Z := 0x5e1060.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DRV_IN_CB : Z := 0x5e1054.          (* [comment removed for export] *)
Definition ATEXIT_ENTRY : Z := 0x94a90.        (* [comment removed for export] *)
Definition GUARD_ENTRY : Z := 0x845b0.         (* [comment removed for export] *)
Definition ATX_CALL : Z := 0x94b54.            (* [comment removed for export] *)
Definition COV_HOOK : Z := 0x73be8.            (* [comment removed for export] *)
Definition ATX : Z := 0x601a08.                (* [comment removed for export] *)
Definition LOCK_ENTRY : Z := 0x9f458.          (* [comment removed for export] *)
Definition UNLOCK_ENTRY : Z := 0x9f6e0.        (* [comment removed for export] *)
Definition READ_STAGE : Z := 0x5d1050.         (* [comment removed for export] *)
Definition FMT_D : Z := 0x1488a.               (* [comment removed for export] *)
Definition FMT_USAGE : Z := 0x1590b.           (* [comment removed for export] *)
Definition FMT_CANNOT_OPEN : Z := 0x1d902.     (* [comment removed for export] *)
Definition FMT_READ_ERROR : Z := 0x1d917.      (* [comment removed for export] *)
Definition FMT_TOO_BIG : Z := 0x197df.         (* [comment removed for export] *)
Definition MSG_OOM : Z := 0x14876.             (* [comment removed for export] *)
Definition MSG_SHORT_HDR : Z := 0x1fa85.       (* [comment removed for export] *)
Definition MSG_CFG_OVERRUN : Z := 0x1591c.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DRV_RODATA_LO : Z := 0x10000.
Definition DRV_RODATA_HI : Z := 0x21020.

Definition TARGET_RUN_STACK : Z := FUZZ_STACK + 80 + STDIO_STACK.   (* [comment removed for export] *)
Definition READ_I_STACK : Z := 2208.           (* [comment removed for export] *)
Definition MEMCPY_I_STACK : Z := 2240.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition drv_traces : list (list Z) :=
  [ [AMALLOC_PC; 0x841dc]; [AMALLOC_PC; 0x84230]; [AFREE_PC; 0x84254]; [AFREE_PC; 0x84384];     (* [comment removed for export] *)
    [AMALLOC_PC]; [AFREE_PC];                                                                    (* [comment removed for export] *)
    [AMALLOC_PC; 0x844bc]; [AFREE_PC; 0x84550] ].                                                (* [comment removed for export] *)
Definition traces_drv (L : alayout) : Prop := forall tr, In tr drv_traces -> In tr (al_U L).
(* [comment removed for export] *)
Definition RA_FUZZ : Z := 0x84524.

(* [comment removed for export] *)
Definition ATX_KEEP : list (Z * Z) := [(DRV_INIT_FLAG, DRV_INIT_FLAG + 8); (ATX, ATX + 544)].          (* [comment removed for export] *)
Definition ATX_DOM : list (Z * Z) := ATX_KEEP ++ [(0x601c48, 0x601c50)].                             (* [comment removed for export] *)
(* [comment removed for export] *)
Definition atx_cells (reg : bool) (cb : Z) (m : mem) : Prop :=
     rw_cells asegs m 0x5e1050 [C1 (Z_to_bv 8 (Z.b2z reg))]                               (* [comment removed for export] *)
  /\ rw_cells asegs m 0x5e1054 [C1 (Z_to_bv 8 cb)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601a08 [C1 (Z_to_bv 8 0)]                                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601a0c [C4 (Z_to_bv 64 0)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601a10 [C4 (Z_to_bv 64 (1 + Z.b2z reg))]                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601a18 [C8 (Z_to_bv 64 0x601a20)]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601a20 [C8 (Z_to_bv 64 0)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601a28 [C8 (Z_to_bv 64 0x94b54)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601a30 [C8 (Z_to_bv 64 (if reg then 0x94b54 else 0))]             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601b28 [C8 (Z_to_bv 64 0x73be8)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601b30 [C8 (Z_to_bv 64 (if reg then 0x845b0 else 0))]             (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word), rw_cells asegs m 0x601c48 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]).   (* [comment removed for export] *)

Section DrvIfaces.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation GIO := GIOA.
  #[local] Abbreviation SPOA := (std_pre_o GIOA).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rs_iv (iv : Z * Z) : Prop := READ_STAGE <= fst iv /\ snd iv <= READ_STAGE + 65536.
  Definition drv_ivA (CL : list cblk) (iv : Z * Z) : Prop := client_ivA [] CL iv \/ rs_iv iv.

  Record gia_drv_laws (USP : Z) (SB : list byte) : Prop := mkGD {
    (* [comment removed for export] *)
    gd_errno : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> exists e : word, rw_cells asegs m (ATP + -164) [C4 e];
    (* [comment removed for export] *)
    gd_misc : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 rw_cells asegs m GOT_STDERR [C8 (Z_to_bv 64 STDERR_P)] /\ rw_cells asegs m STDERR_P [C8 (Z_to_bv 64 STDERR_FILE)]
                 /\ rw_cells asegs m GOT_FUZZ_INIT [C8 (Z_to_bv 64 0)];
    (* [comment removed for export] *)
    gd_canary : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 rw_cells asegs m 0xa6540 [C8 (Z_to_bv 64 0x6019f8)] /\ exists c : word, rw_cells asegs m 0x6019f8 [C8 c];
    (* [comment removed for export] *)
    gd_args : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> mobjA RNG m USP (Z.of_nat (length SB) - 16);   (* [comment removed for export] *)
    (* [comment removed for export] *)
    gd_unp : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 unpoisoned m DRV_RODATA_LO DRV_RODATA_HI /\ unpoisoned m READ_STAGE (READ_STAGE + 65536);
    (* [comment removed for export] *)
    gd_frame : forall L RNG s CL FB FL m m' W, GIOA L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
                 Forall (drv_ivA CL) W -> GIOA L RNG s CL FB FL m';
    gd_frame_errno : forall L RNG s CL FB FL m m' W (e : word), GIOA L RNG s CL FB FL m ->
                 munch ((ATP + -164, ATP + -160) :: W) m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W ->
                 rw_cells asegs m' (ATP + -164) [C4 e] -> GIOA L RNG s CL FB FL m'
  }.

  (* [comment removed for export] *)
  Record gia_atx_laws : Prop := mkGA {
    (* [comment removed for export] *)
    ga_get : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> exists reg : bool, atx_cells reg 0 m;
    (* [comment removed for export] *)
    ga_frame : forall L RNG s CL FB FL m m' W (reg' : bool), GIOA L RNG s CL FB FL m ->
                 munch (ATX_KEEP ++ W) m m' -> wmono asegs m m' -> Forall (drv_ivA CL) W ->
                 atx_cells reg' 0 m' -> GIOA L RNG s CL FB FL m'
  }.

  (* [comment removed for export] *)
  Variable GIOA1 : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Record gia_cb_laws : Prop := mkGCB {
    gc_set : forall L RNG s CL FB FL m m', GIOA L RNG s CL FB FL m -> munch [(DRV_IN_CB, DRV_IN_CB + 1)] m m' -> wmono asegs m m' ->
                 rw_cells asegs m' 0x5e1054 [C1 (Z_to_bv 8 1)] -> GIOA1 L RNG s CL FB FL m';
    gc_cell : forall L RNG s CL FB FL m, GIOA1 L RNG s CL FB FL m -> exists reg : bool, atx_cells reg 1 m;
    gc_clr : forall L RNG s CL FB FL m m', GIOA1 L RNG s CL FB FL m -> munch [(DRV_IN_CB, DRV_IN_CB + 1)] m m' -> wmono asegs m m' ->
                 rw_cells asegs m' 0x5e1054 [C1 (Z_to_bv 8 0)] -> GIOA L RNG s CL FB FL m'
  }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition std_pre_d (L : alayout) (RNG : footprint) (sp tp : word) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo budget : Z) (m : mem) : Prop :=
    GIOA L RNG s CL FB FL m /\ stk asegs m lo (bv_unsigned sp) /\ ATOP + 4096 <= lo /\ lo + budget <= bv_unsigned sp
    /\ (bv_unsigned sp < 2^47 /\ al_top L <= 2^47) /\ mem_inv asegs m /\ tp = Z_to_bv 64 ATP /\ bv_unsigned sp mod 16 = 0
    /\ (rng RNG lo (al_top L - lo) /\ rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG).

  #[using="Type"] Lemma std_pre_o_d : forall L RNG sp tp s CL FB FL lo budget m,
    std_pre_o GIOA L RNG sp tp s CL FB FL lo budget m -> 0 <= budget -> std_pre_d L RNG sp tp s CL FB FL lo budget m.
  Proof.
    intros L RNG sp tp s CL FB FL lo budget m (G & ST & LO & BU & (S1 & S2) & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS) HB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    split; [exact G|]. split; [exact ST|]. split; [exact LO|]. split; [exact BU|]. split; [split; [lia| exact S2]|].
    split; [exact MI|]. split; [exact TPE|]. split; [exact ALN|].
    split; [exact RSTK|]. split; [eapply rng_sub'; [exact RSTK| lia]|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
  Qed.

  (* [comment removed for export] *)
  Definition malloc_stmt_d : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo n : Z),
      std_pre_d L RNG sp tp s CL FB FL lo MALLOC_STACK m -> a0 = Z_to_bv 64 n -> 1 <= n < 2^29 - 2^16 ->
      unw_okA L RNG m lo AMALLOC_PC sp s0 ra ->
      implMG RNG (pmalloc HO n) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => False
              | Some q => exists A junk, a0v = Z_to_bv 64 A /\ GIO L RNG' s' ((q, A, n) :: CL) FB FL m'
                          /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom asegs)).

  Definition free_stmt_d : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (C1 C2 FB : list cblk) (FL : list fblock) (q : hptr) (A n lo : Z),
      std_pre_d L RNG sp tp s (C1 ++ (q, A, n) :: C2) FB FL lo FREE_STACK m -> a0 = Z_to_bv 64 A ->
      unw_okA L RNG m lo AFREE_PC sp s0 ra ->
      implMG RNG (pfree HO q) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' (C1 ++ C2) FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition out_post_o (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo : Z) (m : mem)
      : unit -> PS -> footprint -> machine_state -> Prop :=
    fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
       /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
       /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
       /\ GIO L RNG' s' CL FB FL m'.

  (* [comment removed for export] *)
  Definition eprintf_s_stmt_o (FMT fl : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo P : Z) (str slack : list byte),
      std_pre_d L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      bv_unsigned sp - 32 <= al_top L ->          (* [comment removed for export] *)
      a0 = Z_to_bv 64 STDERR_FILE -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      mobjA RNG m FMT (fl + 1) ->
      bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->   (* [comment removed for export] *)
      mobjA RNG m P (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) ->
      (forall a, P <= a < P + Z.of_nat (length str) + 1 -> client_keeps FL CL (bv_unsigned sp) a) ->
      implMG RNG (@eprintf PS hptr ps_libc set_libc (mk (map bv_unsigned str))) s
        (out_post_o ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition eprintf_i_stmt_o (FMT fl v : Z) (ps : list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo : Z),
      std_pre_d L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      bv_unsigned sp - 32 <= al_top L ->          (* [comment removed for export] *)
      a0 = Z_to_bv 64 STDERR_FILE -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 v ->
      mobjA RNG m FMT (fl + 1) ->
      implMG RNG (@eprintf PS hptr ps_libc set_libc ps) s
        (out_post_o ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition efwrite_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo MSG : Z) (bs : list byte),
      std_pre_d L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 MSG -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 STDERR_FILE ->
      bytes_at asegs m MSG bs -> (DRV_RODATA_LO <= MSG /\ MSG + Z.of_nat (length bs) <= DRV_RODATA_HI) -> (1 <= length bs)%nat ->
      mobjA RNG m MSG (Z.of_nat (length bs)) ->
      implMG RNG (@efwrite PS hptr ps_libc set_libc (map bv_unsigned bs)) s
        (out_post_o ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition vprintf_d_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo AP v : Z) (rest : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 FMT_D -> a1 = Z_to_bv 64 AP -> -2^31 <= v < 2^31 ->
      mobjA RNG m FMT_D 4 ->
      rw_cells asegs m AP [C8 (Z_to_bv 64 v); CB 48 rest] -> bv_unsigned sp <= AP -> AP + 56 <= al_top L ->
      implMG RNG (@printf PS hptr ps_libc set_libc (pieces_emit_d v)) s
        (out_post_o ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition target_run_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL : list cblk) (lo : Z) (m : mem) : Z -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' FB',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m m'
      /\ GIO L RNG' s' CL FB' [] m' /\ 0 <= r <= 2.

  Definition target_run_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo A Lc : Z) (content : list byte),
      std_pre_d L RNG sp tp s CL FB [] lo TARGET_RUN_STACK m -> bv_unsigned sp - 48 < al_top L ->     (* [comment removed for export] *)
      traces_drv L -> traces_fuzz_one TP L RA_FUZZ [] ->
      bytes_at asegs m A content -> 0 <= Lc -> 6 + Lc <= Z.of_nat (length content) -> Z.of_nat (length content) <= 2^26 ->
      (exists b, In b CL /\ cb_addr b <= A /\ A + Z.of_nat (length content) <= cb_addr b + cb_size b) ->
      a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 Lc -> a2 = Z_to_bv 64 (A + 6 + Lc) -> a3 = Z_to_bv 64 (Z.of_nat (length content) - 6 - Lc) ->
      implMG RNG (run HO FO sites (firstn (Z.to_nat Lc) (skipn 2 (map bv_unsigned content)))
                               (skipn (Z.to_nat (6 + Lc)) (map bv_unsigned content))) s
        (target_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TARGET_RUN_ENTRY) fc None m (seg_rom asegs)).
End DrvIfaces.
End TwB.
