(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_atexitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvFactsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_atexitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ _ _ => apply implMG_from_evtF end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

(* [comment removed for export] *)
#[using="Type"] Lemma reg_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (reg : bool),
  stk asegs m lo (bv_unsigned sp) ->
  atx_cells reg 0 m ->
  rw_cells asegs m 0xa6118 [C8 (Z_to_bv 64 0)] ->       (* [comment removed for export] *)
  mem_inv asegs m -> (lo <= bv_unsigned sp - 48)%Z -> (ATOP + 4096 <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  a1 = Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (Z.b2z reg))) -> s4 = Z_to_bv 64 0x5e0c50 ->
  evtF asegs RNG (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x84438) fc None m' (seg_rom asegs)
      /\ munch [(0x5e0c50, 0x5e0c58); (0x601608, 0x601828); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ atx_cells true 0 m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x84434) fc None m (seg_rom asegs)).
Proof.
  intros until reg. intros ST ATXC GLI MI LO KH RSTK RIMG -> ->.
  destruct ATXC as (IFL & CBC & FIN & ALK & SLOT & HEAD & NEXT & F0 & F1 & A0 & A1 & (cdt & thr & sec & tm1 & LIBC)).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  pose proof (munch_refl [(0x5e0c50, 0x5e0c58); (0x601608, 0x601828); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  destruct reg; cbn [Z.b2z] in *.
  - (* [comment removed for export] *)
    zstep. if_false.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    unfold atx_cells. cbn [Z.b2z]. repeat (split; [assumption|]). exists cdt, thr, sec, tm1. exact LIBC.
  - (* [comment removed for export] *)
    change (1 + 0)%Z with 1%Z in SLOT.
    zstep. if_true. zstep. zstep. zstep. zstep. zstep.
    call atexitA_spec; [ first [exact ST | exact FIN | exact ALK | exact SLOT | exact HEAD | exact F1 | exact A1 | exact LIBC | exact MI | exact KH | exact RSTK | exact RIMG | lia] .. |].
    zstep. if_true. zstep. zstep. zstep. if_true.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    unfold atx_cells. cbn [Z.b2z]. change (1 + 1)%Z with 2%Z.
    repeat (split; [first [eassumption | hyp_by_addr]|]). exists cdt, thr, sec, tm1. first [eassumption | hyp_by_addr].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma target_alloc_init_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TARGET_ALLOC_INIT_ENTRY) fc None m (seg_rom asegs)).
Proof. intros. unfold TARGET_ALLOC_INIT_ENTRY. zstep. apply evtF_done. reflexivity. Qed.

#[using="Type"] Lemma target_alloc_count_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TARGET_ALLOC_COUNT_ENTRY) fc None m (seg_rom asegs)).
Proof. intros. unfold TARGET_ALLOC_COUNT_ENTRY. zstep. zstep. apply evtF_done. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ranges_apart : forall S D n, (0 < n)%Z ->
  (forall a, S <= a < S + n -> ~ (D <= a < D + n))%Z -> (S + n <= D \/ D + n <= S)%Z.
Proof.
  intros S D n Hn H.
  destruct (Z_lt_le_dec S (D + n)); [|right; lia]. destruct (Z_lt_le_dec D (S + n)); [|left; lia].
  exfalso. destruct (Z_le_gt_dec D S).
  - apply (H S); lia.
  - apply (H D); lia.
Qed.

#[using="Type"] Lemma land3_range : forall c, (0 <= Z.land c 3 <= 3)%Z.
Proof. intros c. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia. pose proof (Z.mod_pos_bound c (2^2) ltac:(lia)). lia. Qed.

#[using="Type"] Lemma eqz_cond_false : forall z, (0 < z < 2^64)%Z -> bv_eqb (Z_to_bv 64 z) z64 = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.
#[using="Type"] Lemma nez_cond : forall z, (0 < z < 2^64)%Z -> negb (bv_eqb (Z_to_bv 64 z) z64) = true.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. Qed.

Section TargetRun.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Variables (USP : Z) (SB : list byte).
  (* [comment removed for export] *)
  Variable GIOA1 : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GL1 : gia_laws FO GIOA1 fflagA.
  Hypothesis GD : gia_drv_laws GIOA USP SB.
  Hypothesis GA : gia_atx_laws GIOA.
  Hypothesis GCB : gia_cb_laws GIOA GIOA1.
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis FUZZ : fuzz_one_stmt HO FO sites GIOA1 TP.
  Hypothesis VPR : vprintf_d_stmt_o GIOA.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).

  (* [comment removed for export] *)
  Let drv_lit_mobjA := drv_lit_mobjA FO GIOA fflagA USP SB GL GD.
  Let drv_stack_writes := drv_stack_writes FO GIOA fflagA GL.
  Let drv_keeps := drv_keeps FO GIOA fflagA GL.
  Let data_loc_cobjA := data_loc_cobjA FO GIOA fflagA GL.
  Let block_mobjA := block_mobjA FO GIOA fflagA GL.
  Let drv_keeps1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvFactsA.drv_keeps FO GIOA1 fflagA GL1.
  Let data_loc_cobjA1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvFactsA.data_loc_cobjA FO GIOA1 fflagA GL1.

  (* [comment removed for export] *)
  Ltac aln_fin := first [ assumption | lia | Z.div_mod_to_equations; lia ].
  Ltac aln :=
    first [ assumption
          | (match goal with H : bv_unsigned ?x = _ |- (bv_unsigned ?x mod 16 = 0)%Z => rewrite H end; aln_fin)
          | (rewrite unsigned_lit by lia; aln_fin)
          | aln_fin ].

  (* [comment removed for export] *)
  Definition emit_printf_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo v : Z),
    std_pre_o GIOA L RNG sp tp s CL FB [] lo (80 + STDIO_STACK) m ->
    a1 = Z_to_bv 64 v -> (- 2^31 <= v < 2^31)%Z ->
    implMG RNG (@emit_d PS hptr ps_libc set_libc v) s
      (out_post_o GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB [] lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EMIT_PRINTF_ENTRY) fc None m (seg_rom asegs)).
  Section Zd1.   (* [comment removed for export] *)
  Variable ra : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 0).
  Variable sp : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 1).
  Variable gp : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 2).
  Variable tp : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 3).
  Variable t0 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 4).
  Variable t1 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 5).
  Variable t2 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 6).
  Variable s0 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 7).
  Variable s1 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 8).
  Variable a0 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 9).
  Variable a1 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 10).
  Variable a2 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 11).
  Variable a3 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 12).
  Variable a4 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 13).
  Variable a5 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 14).
  Variable a6 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 15).
  Variable a7 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 16).
  Variable s2 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 17).
  Variable s3 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 18).
  Variable s4 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 19).
  Variable s5 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 20).
  Variable s6 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 21).
  Variable s7 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 22).
  Variable s8 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 23).
  Variable s9 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 24).
  Variable s10 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 25).
  Variable s11 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 26).
  Variable t3 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 27).
  Variable t4 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 28).
  Variable t5 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 29).
  Variable t6 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 30).
  Variable F : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 31).
  Variable fc : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 32).
  Variable m : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 33).
  Variable L : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 34).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 35).
  Variable s : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 36).
  Variable CL : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 37).
  Variable FB : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 38).
  Variable lo : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 39).
  Variable v : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 40).
  #[using="FO fflagA USP SB GL GD VPR drv_lit_mobjA drv_stack_writes"] Lemma emit_printf_spec__body : ltac:(let T := type of (fun (h : emit_printf_spec__stmt) => h ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB lo v) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (RNG, (s, (CL, (FB, (lo, v))))))))))))))))))))))))))))))))))))))))) as _.
 intros (G & ST & LO & BUD & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS) Ea1 Hv.
    unfold STDIO_STACK in BUD. unfold EMIT_PRINTF_ENTRY.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    subst a1.
    ienterG.
    carve_frame 80%nat ST.
    zsteps_to 0x4449c%Z.
    (* [comment removed for export] *)
    destruct (drv_stack_writes L RNG s CL FB m m0 _ (bv_unsigned sp) G MU WM) as [G1 AG0];
      [constructor; [cbn [fst snd]; lia| constructor] | lia |].
    clear MU WM.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs m0 _ [_; _; _] _)) in FR as [FR1 FR2]. cbn [cells_size csize Nat.add] in FR2.
    apply (rw_cells_merge asegs m0 _ [C8 (Z_to_bv 64 v)] [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] []) in FR2.
    cbn [cells_size csize cells_bytes cbytes Nat.add app] in FR2.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in FR2 by lia.
    name_sp sp (-80)%Z.
    apply evtF_done. unfold emit_d. eapply implMG_post_evtF.
    { eapply VPR with (AP := (bv_unsigned sp + -56)%Z) (v := v).
      { split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI|]. split; [exact TPE|]. split; [rewrite Hsp; aln|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
      - reflexivity.
      - reflexivity.
      - exact Hv.
      - eapply drv_lit_mobjA; [exact G1 | exact RIMG | exact RISH | unfold FMT_D; lia | unfold FMT_D, DRV_RODATA_HI; lia | lia].
      - exact FR2.
      - rewrite Hsp. lia.
      - lia. }
    intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI' ST' AG G'; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. clear MI. rename MI' into MI.
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
    replace (ret_pc (Z_to_bv 64 542132)) with (Z_to_bv 64 542132) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite Hsp in *.
    apply (keeps_rw_cells_stack [] CL _ _ _ _ _ AG) in FR1; [|lia].
    apply (keeps_rw_cells_stack [] CL _ _ _ _ _ AG) in FR2; [|lia].
    unname_sp.
    zstep. zstep. zstep.
    release_frame FR1 ST' (bv_unsigned sp + -56)%Z. release_frame FR2 ST' (bv_unsigned sp).
    apply evtF_done. unfold out_post_o. split; [exact FP|].
    eexists _, _. split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); cbv delta [mkR]; reflexivity|].
    split; [exact OF|]. split; [exact MI|]. split; [exact ST'|]. split; [| exact G'].
    eapply keeps_trans; [exact AG0 | exact AG | lia | intros a Ha; exact Ha | intros a Ha; exact Ha].
  Qed.
  End Zd1.
  #[using="FO fflagA USP SB GL GD VPR drv_lit_mobjA drv_stack_writes"] Lemma emit_printf_spec : ltac:(let t := eval cbv delta [emit_printf_spec__stmt] in emit_printf_spec__stmt in exact t).
  Proof. exact emit_printf_spec__body. Qed.

  (* [comment removed for export] *)
  Ltac tr_hide H := lazymatch type of H with ?T => let X := fresh "AUX" in pose (X := T); change T with X in H end.
  Ltac tr_unhide H := lazymatch type of H with ?X => subst X end.
  (* [comment removed for export] *)
  Ltac spo_tac G ST MI Hsp :=
    split; [exact G|]; split; [rewrite Hsp; exact ST|]; split; [lia|];
    split; [unfold FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK, MALLOC_STACK, FREE_STACK in *; rewrite Hsp; lia|];
    split; [rewrite Hsp; lia|]; split; [exact MI|]; split; [assumption|]; split; [rewrite Hsp; aln|];
    split; [assumption|]; split; [assumption|]; split; assumption.

  (* [comment removed for export] *)
  Definition loop_post (spi gp tp s0 s1 s2 s4 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL : list cblk) (lo : Z) (bad : bool) (m : mem) : bool -> PS -> footprint -> machine_state -> Prop :=
    fun bad' s' RNG' ms' => fp_le RNG RNG' /\ exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3' m' FB',
      ms' = MS (mkR ra' spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3' s4 (Z_to_bv 64 0) (Z_to_bv 64 (Z.b2z bad)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x844e0) fc None m' (seg_rom asegs)
      /\ bad' = bad /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned spi)
      /\ agrees_on (client_keeps [] CL (bv_unsigned spi)) m m' /\ GIOA L RNG' s' CL FB' [] m'.

  #[using="fflagA USP SB GL GL1 GD GA GCB FUZZ VPR drv_lit_mobjA drv_stack_writes drv_keeps drv_keeps1 data_loc_cobjA1"] Lemma loop_spec : forall (n : nat) (ra spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo D : Z) (data : list byte) (bad : bool),
    (1 <= n <= 4)%nat ->
    std_pre_o GIOA L RNG spi tp s CL FB [] lo FUZZ_STACK m -> traces_fuzz_one TP L RA_FUZZ [] ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s5 = Z_to_bv 64 (Z.of_nat n) -> s4 = Z_to_bv 64 DRV_INIT_FLAG ->
    s6 = Z_to_bv 64 (Z.b2z bad) -> s7 = Z_to_bv 64 (-2) ->
    bytes_at asegs m D data -> data_loc CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (call_loop (@emit_d PS hptr ps_libc set_libc) (harness_call HO FO sites) n (map bv_unsigned data) bad) s
      (loop_post spi gp tp s0 s1 s2 s4 s7 s8 s9 s10 s11 F fc L RNG CL lo bad m)
      (MS (mkR ra spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x844a8) fc None m (seg_rom asegs)).
  Proof.
    induction n as [|n IH]; [intros; lia|].
    intros until bad. intros Hn (G & ST & LO & BUD & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS) TRF Es0 Es1 Es5 Es4 Es6 Es7 SRC HK HD.
    pose proof BUD as BUD'. unfold FUZZ_STACK, PCAP_L4_STACK in BUD'.
    pose proof (bv_unsigned_in_range 64 spi) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
    subst s0 s1 s5 s4 s6 s7. unfold DRV_INIT_FLAG.
    cbn [call_loop].
    (* [comment removed for export] *)
    destruct (ga_get _ GA _ _ _ _ _ _ _ G) as (reg & ATXC). destruct ATXC as (_ & CBC & _).
    pose proof (munch_refl [(0x5e0c54, 0x5e0c55)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    tr_hide SRC.
    ienterG. zstep. zstep.
    tr_unhide SRC.
    lazymatch type of MU with munch _ _ ?mb =>
      assert (G1 : GIOA1 L RNG s CL FB [] mb);
      [ eapply (gc_set _ _ GCB); [exact G | exact MU | exact WM | exact CBC]
      | assert (AG0 : agrees_on (client_keeps [] CL (bv_unsigned spi)) m mb);
        [ eapply (drv_keeps L RNG s [] CL FB m mb _ (bv_unsigned spi)); [exact G | exact MU | exact WM | | lia];
          constructor; [right; right; right; right; left; cbn [fst snd]; unfold DRV_INIT_FLAG; lia | constructor] | ] ]
    end.
    apply (agrees_bytes_at _ _ _ _ _ AG0) in SRC; [| intros a Ha; right; left; eapply data_loc_keeps; eassumption].
    clear MU WM G CBC reg.
    zstep. zstep. zstep.
    apply evtF_done. eapply implMG_bind.
    { eapply FUZZ with (trC := @nil Z) (D := D) (data := data);
        [ | eapply (ucaller_data depth_fuzz_one _ _ _ _ _ RA_FUZZ); [rewrite unsigned_lit by lia; lia | reflexivity | unfold RA_FUZZ, ACLIENT_LO, ACLIENT_HI; lia | unfold depth_fuzz_one; lia]
          | rewrite unsigned_lit by (unfold RA_FUZZ; lia); exact TRF | reflexivity | reflexivity | exact SRC | eapply data_loc_cobjA1; eassumption | exact HD].
      split; [exact G1|]. split; [exact ST|]. split; [exact LO|]. split; [exact BUD|].
      split; [exact SPT|]. split; [exact MI|]. split; [exact TPE|]. split; [exact ALN|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    intros rc' s' RNG1 ms' PO. cbv beta in PO. destruct PO as (FP1 & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MI1 ST1 AG1 G1' ndR2__; nd_post; revert ndR2__; intros ->).
    clear MI G1. cbn [fst snd].
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
    replace (ret_pc (Z_to_bv 64 0x844bc)) with (Z_to_bv 64 0x844bc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    destruct (gc_cell _ _ GCB _ _ _ _ _ _ _ G1') as (reg & ATXC). destruct ATXC as (_ & CBC & _).
    lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (munch_refl [(0x5e0c54, 0x5e0c55)]%Z m1) as MU; pose proof (wmono_refl asegs m1) as WM end.
    ienterG. zstep. zstep.
    lazymatch type of MU with munch _ ?ma ?mb => lazymatch type of G1' with GIOA1 _ _ _ _ ?fb _ _ =>
      assert (G2 : GIOA L RNG1 s' CL fb [] mb);
      [ eapply (gc_clr _ _ GCB); [exact G1' | exact MU | exact WM | exact CBC]
      | assert (AG2 : agrees_on (client_keeps [] CL (bv_unsigned spi)) ma mb);
        [ eapply (drv_keeps1 L RNG1 s' [] CL fb ma mb _ (bv_unsigned spi)); [exact G1' | exact MU | exact WM | | lia];
          constructor; [right; right; right; right; left; cbn [fst snd]; unfold DRV_INIT_FLAG; lia | constructor] | ] ]
    end end.
    clear MU WM G1' CBC reg.
    zstep. zstep.
    apply evtF_done. eapply implMG_bind.
    { eapply (emit_printf_spec _ spi) with (v := 0%Z); [| reflexivity | lia].
      split; [exact G2|]. split; [eassumption|]. split; [exact LO|]. split; [unfold STDIO_STACK; lia|].
      split; [exact SPT|]. split; [eassumption|]. split; [exact TPE|]. split; [exact ALN|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    intros [] s'' RNG2 ms'' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP2 a0v m2 E OF2 MI2 ST2 AG3 G3; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms''.
    cbn [fst snd].
    repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    replace (ret_pc (Z_to_bv 64 0x844cc)) with (Z_to_bv 64 0x844cc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite bad_rc_step0.
    ienterG. zstep. zstep. if_true. zstep.
    replace (bv_swrap 32 (Z.of_nat (S n) + -1)) with (Z.of_nat n) by (rewrite bv_swrap_small; [lia| change (bv_half_modulus 32) with 2147483648%Z; lia]).
    assert (AGall : agrees_on (client_keeps [] CL (bv_unsigned spi)) m m2).
    { eapply keeps_trans; [exact AG0 | eapply keeps_trans; [exact AG1 | eapply keeps_trans; [exact AG2 | exact AG3 | lia | intros a Ha; exact Ha | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha | intros a Ha; exact Ha]. }
    destruct (Nat.eq_dec n 0) as [->|Hn0].
    - change (Z.of_nat 0) with 0%Z. zstep. if_false. apply evtF_done. apply implMG_ret. apply evtF_done.
      unfold loop_post. split; [eapply fp_le_trans; [exact FP1| exact FP2]|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact AGall|exact G3].
    - zstep. if_true_by (nez_cond (Z.of_nat n) ltac:(lia)).
      apply evtF_done. eapply implMG_mono.
      + eapply IH with (D := D) (data := data) (bad := bad); [lia | | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HK | exact HD].
        * split; [exact G3|]. split; [exact ST2|]. split; [exact LO|]. split; [exact BUD|].
          split; [exact SPT|]. split; [exact MI2|]. split; [exact TPE|]. split; [exact ALN|].
          split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
        * exact TRF.
        * eapply agrees_bytes_at; [exact AG3 | eapply agrees_bytes_at; [exact AG2 | eapply agrees_bytes_at; [exact AG1 | exact SRC |] |] |]; intros a Ha; right; left; eapply data_loc_keeps; eassumption.
      + cbv beta. intros b2 s2' RNG3 ms2 PO. unfold loop_post in *. destruct PO as (FP3 & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MI4 ST4 AG4 G4; nd_post).
        split; [eapply fp_le_trans; [exact FP1| eapply fp_le_trans; [exact FP2| exact FP3]]|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [|exact G4].
        eapply keeps_trans; [exact AGall | exact AG4 | lia | intros a Ha; exact Ha | intros a Ha; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Definition tr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL : list cblk) (lo SP : Z) (m : mem) : Z -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' FB',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps [] CL SP) m m'
      /\ GIOA L RNG' s' CL FB' [] m' /\ (0 <= r <= 2)%Z.

  #[using="fflagA USP SB GL GL1 GD GA GCB MALLOC FREE FREENULL FUZZ VPR drv_lit_mobjA drv_stack_writes drv_keeps drv_keeps1 data_loc_cobjA data_loc_cobjA1 block_mobjA"] Lemma rest_spec : forall (k : nat) (o : option hptr)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo D : Z) (data : list byte),
    (1 <= k <= 4)%nat ->
    GIOA L RNG s (match o with Some q => (q, D, Z.of_nat (length data)) :: CL | None => CL end) FB [] m ->
    stk asegs m lo (bv_unsigned sp + -80) -> (ATOP + 4096 <= lo)%Z -> (lo + TARGET_RUN_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp - 48 < al_top L /\ al_top L <= 2^47)%Z -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> (bv_unsigned sp mod 16 = 0)%Z ->
    rng RNG lo (al_top L - lo) -> rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    traces_drv L -> traces_fuzz_one TP L RA_FUZZ [] ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 DRV_INIT_FLAG ->
    s2 = match o with Some _ => Z_to_bv 64 D | None => Z_to_bv 64 0 end ->
    bytes_at asegs m D data ->
    match o with Some q => True | None => data = [] /\ (0x10040 <= D /\ D <= 0x602fc0)%Z end ->
    (Z.of_nat (length data) < 2^26)%Z ->
    rw_cells asegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implMG RNG (bad <- call_loop (@emit_d PS hptr ps_libc set_libc) (harness_call HO FO sites) k (map bv_unsigned data) false ;;
                match o with Some q => pfree HO q | None => mret tt end ;;;
                mret (if bad then 78 else 0)%Z) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc L RNG CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x844a0) fc None m (seg_rom asegs)).
  Proof.
    intros until data. intros Hk G ST LO BUD SPT MI TPE ALN RSTK RSTK2 RIMG RISH RTLS TRD TRF Es0 Es1 Es5 Es4 Es2 SRC HO0 HD FR.
    pose proof BUD as BUD'. unfold TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in BUD'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
    subst s0 s1 s5 s4.
    (* [comment removed for export] *)
    ienterG. zstep. zstep.
    name_sp sp (-80)%Z.
    apply evtF_done.
    eapply implMG_bind.
    { eapply (loop_spec k) with (D := D) (data := data) (bad := false); [exact Hk | | exact TRF | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact SRC | | exact HD].
      - spo_tac G ST MI Hsp.
      - destruct o as [q|]; [right; exists (q, D, Z.of_nat (length data)); split; [left; reflexivity| cbn [cb_addr cb_size fst snd]; lia] | left; exact HO0]. }
    intros bad' s' RNG1 ms' PO. unfold loop_post in PO. destruct PO as (FP1 & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MI1 ST1 AG1 G1; nd_post). clear MI.
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
    rewrite Hsp in *.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
    unname_sp.
    ienterG. zstep. zstep.
    destruct o as [q|]; subst s2.
    - (* [comment removed for export] *)
      name_sp sp (-80)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply FREE with (C1 := @nil cblk) (q := q) (A := D) (n := Z.of_nat (length data)); [| reflexivity |].
        - spo_tac G1 ST1 MI1 Hsp.
        - eapply unw_of_ucaller with (trC := @nil Z);
            [ eapply (ucaller_data 0%nat _ _ _ _ _ 0x844e8%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia
            | rewrite unsigned_lit by lia; apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | assumption ]. }
      intros [] s'' RNG2 ms'' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP2 a0v m2 E OF2 MI2 ST2 AG2 G2; nd_post). clear MI1.
      unfold hpost_regs in E. destruct_exs E. subst ms''.
      cbn [app] in AG2, G2.
      repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
      replace (ret_pc (Z_to_bv 64 0x844e8)) with (Z_to_bv 64 0x844e8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hsp in *.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
      unname_sp.
      ienterG. do 3 zstep.
      do 11 zstep.
      apply evtF_done. apply implMG_ret. apply evtF_done.
      release_frame FR ST2 (bv_unsigned sp).
      unfold tr_post. split; [eapply fp_le_trans; [exact FP1| exact FP2]|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [|split; [exact G2| lia]].
      eapply keeps_trans; [ | exact AG2 | lia | intros a Ha; exact Ha | intros a Ha; exact Ha].
      eapply client_keeps_weaken; [exact AG1 | lia | intros a Ha; apply in_block_cons; exact Ha | intros a Ha; exact Ha].
    - (* [comment removed for export] *)
      name_sp sp (-80)%Z.
      eapply evtF_cut.
      { eapply FREENULL; [| reflexivity |].
        - spo_tac G1 ST1 MI1 Hsp.
        - eapply unw_of_ucaller with (trC := @nil Z);
            [ eapply (ucaller_data 0%nat _ _ _ _ _ 0x844e8%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia
            | rewrite unsigned_lit by lia; apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | assumption ]. }
      intros ms' PO. cbv beta in PO. (nd_pre PO 7%nat; intros a0v m2 E MI2 ST2 AG2 G2; nd_post). clear MI1.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      replace (ret_pc (Z_to_bv 64 0x844e8)) with (Z_to_bv 64 0x844e8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hsp in *.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
      unname_sp.
      do 3 zstep.
      do 11 zstep.
      apply evtF_done. apply implMG_ret_bind. apply implMG_ret. apply evtF_done.
      release_frame FR ST2 (bv_unsigned sp).
      unfold tr_post. split; [exact FP1|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [|split; [exact G2| lia]].
      eapply keeps_trans; [exact AG1 | exact AG2 | lia | intros a Ha; exact Ha | intros a Ha; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Definition tr_rest (k : nat) (pl : list Z) : Monad.M PS Z :=
    owned <- (if (length pl =? 0)%nat then mret (Some None)
              else q <- pmalloc HO (zlength pl) ;;
                   mret (match q with None => None | Some q' => Some (Some q') end)) ;;
    match owned with
    | None => mret 2%Z
    | Some o =>
        bad <- call_loop (@emit_d PS hptr ps_libc set_libc) (harness_call HO FO sites) k pl false ;;
        (match o with Some q => pfree HO q | None => mret tt end) ;;;
        mret (if bad then 78 else 0)%Z
    end.

  (* [comment removed for export] *)
  #[using="fflagA USP SB GL GL1 GD GA GCB MALLOC FREE FREENULL FUZZ VPR drv_lit_mobjA drv_stack_writes drv_keeps drv_keeps1 data_loc_cobjA data_loc_cobjA1 block_mobjA"] Lemma path_empty : forall (k : nat)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo : Z),
    (1 <= k <= 4)%nat ->
    GIOA L RNG s CL FB [] m ->
    stk asegs m lo (bv_unsigned sp + -80) -> (ATOP + 4096 <= lo)%Z -> (lo + TARGET_RUN_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp - 48 < al_top L /\ al_top L <= 2^47)%Z -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> (bv_unsigned sp mod 16 = 0)%Z ->
    rng RNG lo (al_top L - lo) -> rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    traces_drv L -> traces_fuzz_one TP L RA_FUZZ [] ->
    s0 = Z_to_bv 64 0 -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 DRV_INIT_FLAG ->
    rw_cells asegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implMG RNG (tr_rest k []) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc L RNG CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x84498) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros Hk G ST LO BUD SPT MI TPE ALN RSTK RSTK2 RIMG RISH RTLS TRD TRF Es0 Es5 Es4 FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof BUD as BUD'. unfold TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in BUD'.
    subst s0 s5 s4.
    unfold tr_rest. cbn [length Nat.eqb]. apply implMG_ret_bind. cbv beta iota.
    ienterG. zstep. zstep.
    apply evtF_done. eapply rest_spec with (o := None) (data := @nil byte) (D := (DRV_INIT_FLAG + 16)%Z) (FB := FB);
      [exact Hk | exact G | exact ST | exact LO | exact BUD | exact SPT | exact MI | exact TPE | exact ALN | exact RSTK | exact RSTK2 | exact RIMG | exact RISH | exact RTLS
      | exact TRD | exact TRF | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | apply bytes_at_nil; unfold DRV_INIT_FLAG; lia | split; [reflexivity| unfold DRV_INIT_FLAG; lia] | cbn; lia | exact FR].
  Qed.

  (* [comment removed for export] *)
  #[using="fflagA USP SB GL GL1 GD GA GCB MALLOC FREE FREENULL FUZZ VPR drv_lit_mobjA drv_stack_writes drv_keeps drv_keeps1 data_loc_cobjA data_loc_cobjA1 block_mobjA"] Lemma path_alloc : forall (k : nat)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo P : Z) (src : list byte),
    (1 <= k <= 4)%nat ->
    GIOA L RNG s CL FB [] m ->
    stk asegs m lo (bv_unsigned sp + -80) -> (ATOP + 4096 <= lo)%Z -> (lo + TARGET_RUN_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp - 48 < al_top L /\ al_top L <= 2^47)%Z -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> (bv_unsigned sp mod 16 = 0)%Z ->
    rng RNG lo (al_top L - lo) -> rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    traces_drv L -> traces_fuzz_one TP L RA_FUZZ [] ->
    s0 = Z_to_bv 64 (Z.of_nat (length src)) -> s1 = Z_to_bv 64 P -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 DRV_INIT_FLAG ->
    (0 < length src)%nat -> (Z.of_nat (length src) < 2^26)%Z ->
    bytes_at asegs m P src ->
    (exists b, In b CL /\ (cb_addr b <= P /\ P + Z.of_nat (length src) <= cb_addr b + cb_size b)%Z) ->
    rw_cells asegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implMG RNG (tr_rest k (map bv_unsigned src)) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc L RNG CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8444c) fc None m (seg_rom asegs)).
  Proof.
    intros until src. intros Hk G ST LO BUD SPT MI TPE ALN RSTK RSTK2 RIMG RISH RTLS TRD TRF Es0 Es1 Es5 Es4 HP0 HP32 SRC HINP FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof BUD as BUD'. unfold TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in BUD'.
    (nd_pre (block_mobjA L RNG s CL FB m P (Z.of_nat (length src)) G HINP ltac:(lia)) 3%nat; intros PO PT PI; nd_post). unfold AIMG_HI in PI.
    (nd_pre HINP 4%nat; intros pb Hpb PB1 PB2; nd_post).
    subst s0 s1 s5 s4.
    set (n := Z.of_nat (length src)) in *.
    unfold tr_rest. rewrite length_map. replace (length src =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    unfold zlength. rewrite length_map. fold n.
    apply implMG_bind_assoc.
    ienterG. zstep. zstep.
    name_sp sp (-80)%Z.
    apply evtF_done. eapply implMG_bind.
    { eapply MALLOC with (n := n); [| reflexivity | lia |].
      - spo_tac G ST MI Hsp.
      - eapply unw_of_ucaller with (trC := @nil Z);
          [ eapply (ucaller_data 0%nat _ _ _ _ _ 0x84454%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | lia]
          | unfold AMALLOC_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia
          | rewrite unsigned_lit by lia; apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | assumption ]. }
    intros r s' RNG1 ms' PO1. cbv beta in PO1. (nd_pre PO1 9%nat; intros FP1 a0v m1 E OF1 MI1 ST1 AG1 CASES; nd_post). clear MI.
    unfold hpost_regs in E. destruct_exs E. subst ms'.
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
    replace (ret_pc (Z_to_bv 64 0x84454)) with (Z_to_bv 64 0x84454) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite Hsp in *.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
    apply (keeps_bytes_at_block _ _ _ _ _ _ _ AG1) in SRC; [|intros a Ha; apply in_block_In; exists pb; split; [exact Hpb| lia]].
    unname_sp.
    destruct r as [q|]; [| destruct CASES].
    (nd_pre CASES 3%nat; intros A' junk' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros G1 BLK; nd_post).
    (nd_pre (block_mobjA L RNG1 s' ((q, A', n) :: CL) FB m1 A' n G1 ltac:(exists (q, A', n); split; [left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]) ltac:(lia)) 3%nat; intros DO DT DI; nd_post).
    (nd_pre (block_mobjA L RNG1 s' ((q, A', n) :: CL) FB m1 P n G1 ltac:(exists pb; split; [right; exact Hpb| lia]) ltac:(lia)) 3%nat; intros PO1 _ _; nd_post).
    unfold AIMG_HI in DI.
    assert (SEP : (P + n <= A' \/ A' + n <= P)%Z).
    { pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G1) as AP. apply blocks_apart_app_inv in AP as (AP & _ & _). cbn [blocks_apart] in AP. destruct AP as [AP _].
      pose proof (proj1 (Forall_forall _ _) AP _ Hpb) as X. unfold apart in X. cbn [cb_addr cb_size fst snd] in X. lia. }
    apply implMG_ret_bind. cbv beta iota.
    ienterG. zstep. if_false_by (eqz_cond_false A' ltac:(lia)).
    zstep. zstep. zstep. zstep.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(bv_unsigned sp + -80 - 2240, bv_unsigned sp + -80); (A', A' + n)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2 end.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G1) as (RT1 & _).
    call_sp (memcpy_i_specZ RNG1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo A' P n src junk');
      [ first [reflexivity | assumption | lia | (subst n; lia) | (eapply rng_sub'; [eassumption| lia])] .. | ].
    rename PC into ST2. rename PC0 into DST. rename POST into SRC2.
    lazymatch type of MU2 with munch _ ?ma ?mb =>
      assert (G2 : GIOA L RNG1 s' ((q, A', n) :: CL) FB [] mb);
      [ eapply (gl_client_frame _ _ _ GL); [exact G1 | exact MU2 | exact WM2 |];
        constructor; [left; cbn [fst snd]; lia | constructor; [| constructor]];
        right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia
      | assert (AG2 : agrees_on (client_keeps [] CL (bv_unsigned sp + -80)) ma mb);
        [ eapply (drv_keeps L RNG1 s' [(q, A', n)] CL FB ma mb _ (bv_unsigned sp + -80)); [exact G1 | exact MU2 | exact WM2 | | lia];
          constructor; [left; cbn [fst snd]; lia | constructor; [| constructor]];
          right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia | ] ];
      assert (DATA : bytes_at asegs mb A' src);
      [ destruct DST as [[Hwf HB] Hwr]; cbn [cells_bytes cbytes] in HB; rewrite app_nil_r in HB; exact HB | ]
    end.
    clear MU2 WM2.
    zstep. zstep.
    apply evtF_done. eapply implMG_mono.
    + eapply rest_spec with (o := Some q) (data := src) (D := A') (lo := lo) (FB := FB);
        [exact Hk | exact G2 | exact ST2 | exact LO | exact BUD | exact SPT | exact MI | exact TPE | exact ALN | assumption | assumption | assumption | assumption | assumption
        | exact TRD | exact TRF | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | exact DATA | exact I | subst n; lia | exact FR].
    + cbv beta. intros r2 s2' RNG2 ms2 PO2. unfold tr_post in *. destruct PO2 as (FP2 & PO2). destruct_exs PO2. (destruct PO2 as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MI3 ST3 AG3 G3 Hr; nd_post).
      split; [eapply fp_le_trans; [exact FP1| exact FP2]|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [|split; [exact G3| exact Hr]].
      eapply keeps_trans; [exact AG1 | eapply keeps_trans; [exact AG2 | exact AG3 | lia | intros a Ha; exact Ha | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha | intros a Ha; exact Ha].
  Qed.

  #[using="fflagA USP SB GL GL1 GD GA GCB MALLOC FREE FREENULL FUZZ VPR drv_lit_mobjA drv_stack_writes drv_keeps drv_keeps1 data_loc_cobjA data_loc_cobjA1 block_mobjA"] Theorem target_run_proof : target_run_stmt_o HO FO sites GIOA TP.
  Proof.
    unfold target_run_stmt_o.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB lo A Lc content.
    intros (G & ST & LO & BUD & (SP47 & AT47) & MI & TPE & ALN & RSTK & RSTK2 & RIMG & RISH & RTLS) SPT0 TRD TRF SRC HL0 HL6 HLEN HINB Ea0 Ea1 Ea2 Ea3.
    assert (SPT : (bv_unsigned sp - 48 < al_top L /\ al_top L <= 2^47)%Z) by (split; assumption).
    pose proof BUD as BUD'. unfold TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in BUD'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SBD.
    (nd_pre (block_mobjA L RNG s CL FB m A (Z.of_nat (length content)) G HINB ltac:(lia)) 3%nat; intros (_ & _ & _ & CRNG & _) SRCT SRCI; nd_post). unfold AIMG_HI in SRCI.
    (nd_pre HINB 4%nat; intros cb Hcb CB1 CB2; nd_post).
    (* [comment removed for export] *)
    assert (exists b0 b1 b2 rest, content = b0 :: b1 :: b2 :: rest) as (b0 & b1 & b2 & rest & EC).
    { destruct content as [|x0 [|x1 [|x2 r]]]; [cbn in HL6; lia..|]. repeat eexists. }
    unfold TARGET_RUN_ENTRY. unfold run, target_run.
    set (pl := skipn (Z.to_nat (6 + Lc)) (map bv_unsigned content)).
    set (cfg := firstn (Z.to_nat Lc) (skipn 2 (map bv_unsigned content))).
    set (k := Z.to_nat (1 + Z.land (match cfg with [] => 0 | b :: _ => b end) 3)).
    set (plen := (Z.of_nat (length content) - 6 - Lc)%Z) in *.
    set (src := skipn (Z.to_nat (6 + Lc)) content).
    assert (Epl : pl = map bv_unsigned src). { subst pl src. rewrite skipn_map. reflexivity. }
    assert (Hsrc : length src = Z.to_nat plen). { subst src plen. rewrite length_skipn. lia. }
    assert (SRCp : bytes_at asegs m (A + 6 + Lc) src).
    { subst src. pose proof SRC as SRC2. rewrite <- (firstn_skipn (Z.to_nat (6 + Lc)) content) in SRC2. apply bytes_at_app in SRC2 as [_ S2].
      rewrite length_firstn in S2. replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + Lc)) (length content)))%Z with (A + 6 + Lc)%Z in S2 by lia. exact S2. }
    assert (HINP : exists b, In b CL /\ (cb_addr b <= A + 6 + Lc /\ A + 6 + Lc + Z.of_nat (length src) <= cb_addr b + cb_size b)%Z).
    { exists cb. split; [exact Hcb| lia]. }
    assert (Hk : (1 <= k <= 4)%nat). { subst k. pose proof (land3_range (match cfg with [] => 0 | b :: _ => b end)). lia. }
    change (Z.to_nat (1 + Z.land (match cfg with [] => 0 | b :: _ => b end) 3)) with k.
    rewrite Epl.
    subst a0 a1 a2 a3.
    (* [comment removed for export] *)
    destruct (ga_get _ GA _ _ _ _ _ _ _ G) as (reg & ATXC).
    destruct ATXC as (IFL & CBC & FIN & ALK & SLOT & HEAD & NEXT & F0 & F1 & A0 & A1 & (cdt & thr & sec & tm1 & LIBC)).
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros _ _ GLI; nd_post).
    unfold GOT_FUZZ_INIT in GLI.
    pose proof (munch_refl [(0x5e0c50, 0x5e0c58); (0x601608, 0x601828); (bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    ienterG.
    carve_frame 80%nat ST.
    do 17 zstep.
    call_sp (reg_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo reg);
      [ first [ exact ST | exact GLI | exact MI | exact RIMG | reflexivity | lia | (eapply rng_sub'; [exact RSTK2| lia])
              | (unfold atx_cells; repeat (split; [first [assumption | hyp_by_addr]|]); exists cdt, thr, sec, tm1; first [assumption | hyp_by_addr]) ] .. |].
    lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI' end.
    lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
    lazymatch goal with H : atx_cells true 0 _ |- _ => rename H into ATX1 end.
    (* [comment removed for export] *)
    lazymatch type of MU with munch _ _ ?mb =>
      assert (G1 : GIOA L RNG s CL FB [] mb);
      [ eapply (ga_frame _ GA) with (W := [(bv_unsigned sp - 128, bv_unsigned sp)]%Z) (reg' := true); [exact G | | exact WM | | exact ATX1];
        [ eapply munch_weaken; [| exact MU]; intros xq Hx; unfold ATX_KEEP, DRV_INIT_FLAG, ATX in Hx; cbn [app outside] in Hx |- *; lia
        | constructor; [left; left; cbn [fst snd]; lia | constructor] ]
      | assert (AG0 : agrees_on (client_keeps [] CL (bv_unsigned sp)) m mb);
        [ eapply (drv_keeps L RNG s [] CL FB m mb _ (bv_unsigned sp)); [exact G | exact MU | exact WM | | lia];
          constructor; [right; right; right; right; left; cbn [fst snd]; unfold DRV_INIT_FLAG; lia
                       | constructor; [right; right; right; right; right; cbn [fst snd]; unfold ATX; lia
                                      | constructor; [left; cbn [fst snd]; lia | constructor]]] | ] ]
    end.
    clear MU WM.
    (* [comment removed for export] *)
    assert (TAIL : forall r s' RNG' ms' m1, agrees_on (client_keeps [] CL (bv_unsigned sp)) m m1 ->
              tr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo (bv_unsigned sp + -80) m1 r s' RNG' ms' ->
              target_run_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m r s' RNG' ms').
    { intros r s' RNG' ms' m1 AGa PO. unfold tr_post in PO. destruct PO as (FPf & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MIf STf AGf Gf Hr; nd_post).
      unfold target_run_post. split; [exact FPf|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MIf|]. split; [exact STf|]. split; [| split; [exact Gf| exact Hr]].
      eapply keeps_trans; [exact AGa | exact AGf | lia | intros a Ha; exact Ha | intros a Ha; exact Ha]. }
    zstep.
    destruct (Z.eq_dec Lc 0) as [EL|NL].
    - (* [comment removed for export] *)
      assert (Ek : k = 1%nat). { subst k cfg. rewrite EL. reflexivity. }
      replace (Z_to_bv 64 Lc) with z64 by (rewrite EL; reflexivity). if_true. zstep. zstep.
      destruct (Z.eq_dec plen 0) as [EP|NP].
      + replace (Z_to_bv 64 plen) with z64 by (rewrite EP; reflexivity). if_false.
        assert (Esrc : src = []). { destruct src; [reflexivity| rewrite EP in Hsrc; cbn in Hsrc; lia]. }
        rewrite Esrc. apply evtF_done. eapply implMG_mono.
        * eapply path_empty with (lo := lo) (FB := FB);
            [exact Hk | exact G1 | exact ST' | exact LO | exact BUD | exact SPT | exact MI' | exact TPE | exact ALN | exact RSTK | exact RSTK2 | exact RIMG | exact RISH | exact RTLS
            | exact TRD | exact TRF | reflexivity | rewrite Ek; reflexivity | reflexivity | exact FR].
        * intros r s' RNG' ms'. apply TAIL. exact AG0.
      + if_true_by (nez_cond plen ltac:(lia)).
        apply evtF_done. eapply implMG_mono.
        * eapply path_alloc with (lo := lo) (P := (A + 6 + Lc)%Z) (src := src) (FB := FB);
            [exact Hk | exact G1 | exact ST' | exact LO | exact BUD | exact SPT | exact MI' | exact TPE | exact ALN | exact RSTK | exact RSTK2 | exact RIMG | exact RISH | exact RTLS
            | exact TRD | exact TRF | f_equal; lia | reflexivity | rewrite Ek; reflexivity | reflexivity | lia | lia
            | exact SRCp
            | exact HINP | exact FR].
        * intros r s' RNG' ms'. apply TAIL. exact AG0.
    - (* [comment removed for export] *)
      assert (Ek : (Z.of_nat k = Z.land (bv_unsigned b2) 3 + 1)%Z).
      { subst k cfg. rewrite EC. replace (Z.to_nat Lc) with (S (Z.to_nat (Lc - 1))) by lia. cbn [map skipn firstn].
        pose proof (land3_range (bv_unsigned b2)). lia. }
      if_false_by (eqz_cond_false Lc ltac:(lia)).
      pose proof SRC as SRC3.
      rewrite EC in SRC3.
      pose proof (bytes_at_read asegs _ A _ 2 1 SRC3 ltac:(lia) ltac:(cbn; lia)) as HR. clear SRC3.
      change (Z.to_nat 2) with 2%nat in HR. cbn [firstn skipn] in HR.
      assert (RB2 : rng RNG (A + 2) 1) by (eapply rng_sub'; [exact CRNG| lia]).
      zstep. zstep. zstep. zstep.
      destruct (Z.eq_dec plen 0) as [EP|NP].
      + replace (Z_to_bv 64 plen) with z64 by (rewrite EP; reflexivity). if_true.
        assert (Esrc : src = []). { destruct src; [reflexivity| rewrite EP in Hsrc; cbn in Hsrc; lia]. }
        rewrite Esrc. apply evtF_done. eapply implMG_mono.
        * eapply path_empty with (lo := lo) (FB := FB);
            [exact Hk | exact G1 | exact ST' | exact LO | exact BUD | exact SPT | exact MI' | exact TPE | exact ALN | exact RSTK | exact RSTK2 | exact RIMG | exact RISH | exact RTLS
            | exact TRD | exact TRF | reflexivity | f_equal; lia | reflexivity | exact FR].
        * intros r s' RNG' ms'. apply TAIL. exact AG0.
      + if_false_by (eqz_cond_false plen ltac:(lia)).
        apply evtF_done. eapply implMG_mono.
        * eapply path_alloc with (lo := lo) (P := (A + 6 + Lc)%Z) (src := src) (FB := FB);
            [exact Hk | exact G1 | exact ST' | exact LO | exact BUD | exact SPT | exact MI' | exact TPE | exact ALN | exact RSTK | exact RSTK2 | exact RIMG | exact RISH | exact RTLS
            | exact TRD | exact TRF | f_equal; lia | reflexivity | f_equal; lia | reflexivity | lia | lia
            | exact SRCp
            | exact HINP | exact FR].
        * intros r s' RNG' ms'. apply TAIL. exact AG0.
  Qed.
End TargetRun.
End CANSEC1.

(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvFactsA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_atexitA.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac alia_t1 := zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac solve_acc_with_t1 H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); alia_t1
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); alia_t1
      end
  end.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve_acc_with_t1 H end end.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ _ _ => apply implMG_from_evtF end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

(* [comment removed for export] *)
#[using="Type"] Lemma reg_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (reg : bool),
  stk asegs m lo (bv_unsigned sp) ->
  atx_cells reg 0 m ->
  rw_cells asegs m 0xa64f8 [C8 (Z_to_bv 64 0)] ->       (* [comment removed for export] *)
  mem_inv asegs m -> (lo <= bv_unsigned sp - 48)%Z -> (ATOP + 4096 <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  a1 = Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (Z.b2z reg))) -> s4 = Z_to_bv 64 0x5e1050 ->
  evtF asegs RNG (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x844a0) fc None m' (seg_rom asegs)
      /\ munch [(0x5e1050, 0x5e1058); (0x601a08, 0x601c28); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ atx_cells true 0 m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8449c) fc None m (seg_rom asegs)).
Proof.
  intros until reg. intros ST ATXC GLI MI LO KH RSTK RIMG -> ->.
  destruct ATXC as (IFL & CBC & FIN & ALK & SLOT & HEAD & NEXT & F0 & F1 & A0 & A1 & (cdt & thr & sec & tm1 & LIBC)).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  pose proof (munch_refl [(0x5e1050, 0x5e1058); (0x601a08, 0x601c28); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  destruct reg; cbn [Z.b2z] in *.
  - (* [comment removed for export] *)
    zstep. if_false.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    unfold atx_cells. cbn [Z.b2z]. repeat (split; [assumption|]). exists cdt, thr, sec, tm1. exact LIBC.
  - (* [comment removed for export] *)
    change (1 + 0)%Z with 1%Z in SLOT.
    zstep. if_true. zstep. zstep. zstep. zstep. zstep.
    call atexitA_spec; [ first [exact ST | exact FIN | exact ALK | exact SLOT | exact HEAD | exact F1 | exact A1 | exact LIBC | exact MI | exact KH | exact RSTK | exact RIMG | lia] .. |].
    zstep. if_true. zstep. zstep. zstep. if_true.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    unfold atx_cells. cbn [Z.b2z]. change (1 + 1)%Z with 2%Z.
    repeat (split; [first [eassumption | hyp_by_addr]|]). exists cdt, thr, sec, tm1. first [eassumption | hyp_by_addr].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma target_alloc_init_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TARGET_ALLOC_INIT_ENTRY) fc None m (seg_rom asegs)).
Proof. intros. unfold TARGET_ALLOC_INIT_ENTRY. zstep. apply evtF_done. reflexivity. Qed.

#[using="Type"] Lemma target_alloc_count_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TARGET_ALLOC_COUNT_ENTRY) fc None m (seg_rom asegs)).
Proof. intros. unfold TARGET_ALLOC_COUNT_ENTRY. zstep. zstep. apply evtF_done. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ranges_apart : forall S D n, (0 < n)%Z ->
  (forall a, S <= a < S + n -> ~ (D <= a < D + n))%Z -> (S + n <= D \/ D + n <= S)%Z.
Proof.
  intros S D n Hn H.
  destruct (Z_lt_le_dec S (D + n)); [|right; lia]. destruct (Z_lt_le_dec D (S + n)); [|left; lia].
  exfalso. destruct (Z_le_gt_dec D S).
  - apply (H S); lia.
  - apply (H D); lia.
Qed.

#[using="Type"] Lemma land3_range : forall c, (0 <= Z.land c 3 <= 3)%Z.
Proof. intros c. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia. pose proof (Z.mod_pos_bound c (2^2) ltac:(lia)). lia. Qed.

#[using="Type"] Lemma eqz_cond_false : forall z, (0 < z < 2^64)%Z -> bv_eqb (Z_to_bv 64 z) z64 = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.
#[using="Type"] Lemma nez_cond : forall z, (0 < z < 2^64)%Z -> negb (bv_eqb (Z_to_bv 64 z) z64) = true.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. Qed.

Section TargetRun.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Variables (USP : Z) (SB : list byte).
  (* [comment removed for export] *)
  Variable GIOA1 : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GL1 : gia_laws FO GIOA1 fflagA.
  Hypothesis GD : gia_drv_laws GIOA USP SB.
  Hypothesis GA : gia_atx_laws GIOA.
  Hypothesis GCB : gia_cb_laws GIOA GIOA1.
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis FUZZ : fuzz_one_stmt HO FO sites GIOA1 TP.
  Hypothesis VPR : vprintf_d_stmt_o GIOA.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).

  (* [comment removed for export] *)
  Let drv_lit_mobjA := drv_lit_mobjA FO GIOA fflagA USP SB GL GD.
  Let drv_stack_writes := drv_stack_writes FO GIOA fflagA GL.
  Let drv_keeps := drv_keeps FO GIOA fflagA GL.
  Let data_loc_cobjA := data_loc_cobjA FO GIOA fflagA GL.
  Let block_mobjA := block_mobjA FO GIOA fflagA GL.
  Let drv_keeps1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvFactsA.TwB.drv_keeps FO GIOA1 fflagA GL1.
  Let data_loc_cobjA1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvFactsA.TwB.data_loc_cobjA FO GIOA1 fflagA GL1.

  (* [comment removed for export] *)
  Ltac aln_fin := first [ assumption | lia | Z.div_mod_to_equations; lia ].
  Ltac aln :=
    first [ assumption
          | (match goal with H : bv_unsigned ?x = _ |- (bv_unsigned ?x mod 16 = 0)%Z => rewrite H end; aln_fin)
          | (rewrite unsigned_lit by lia; aln_fin)
          | aln_fin ].

  (* [comment removed for export] *)
  Definition emit_printf_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo v : Z),
    std_pre_o GIOA L RNG sp tp s CL FB [] lo (80 + STDIO_STACK) m ->
    a1 = Z_to_bv 64 v -> (- 2^31 <= v < 2^31)%Z ->
    implMG RNG (@emit_d PS hptr ps_libc set_libc v) s
      (out_post_o GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB [] lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EMIT_PRINTF_ENTRY) fc None m (seg_rom asegs)).
  Section Zd1.   (* [comment removed for export] *)
  Variable ra : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 0).
  Variable sp : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 1).
  Variable gp : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 2).
  Variable tp : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 3).
  Variable t0 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 4).
  Variable t1 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 5).
  Variable t2 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 6).
  Variable s0 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 7).
  Variable s1 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 8).
  Variable a0 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 9).
  Variable a1 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 10).
  Variable a2 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 11).
  Variable a3 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 12).
  Variable a4 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 13).
  Variable a5 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 14).
  Variable a6 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 15).
  Variable a7 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 16).
  Variable s2 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 17).
  Variable s3 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 18).
  Variable s4 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 19).
  Variable s5 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 20).
  Variable s6 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 21).
  Variable s7 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 22).
  Variable s8 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 23).
  Variable s9 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 24).
  Variable s10 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 25).
  Variable s11 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 26).
  Variable t3 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 27).
  Variable t4 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 28).
  Variable t5 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 29).
  Variable t6 : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 30).
  Variable F : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 31).
  Variable fc : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 32).
  Variable m : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 33).
  Variable L : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 34).
  Variable RNG : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 35).
  Variable s : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 36).
  Variable CL : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 37).
  Variable FB : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 38).
  Variable lo : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 39).
  Variable v : ltac2:(SecDietF.SzSecF.ty 'emit_printf_spec__stmt 40).
  #[using="FO fflagA USP SB GL GD VPR drv_lit_mobjA drv_stack_writes"] Lemma emit_printf_spec__body : ltac:(let T := type of (fun (h : emit_printf_spec__stmt) => h ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB lo v) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
  Proof.
    pose proof (fun (_ : True) => (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (RNG, (s, (CL, (FB, (lo, v))))))))))))))))))))))))))))))))))))))))) as _.
 intros (G & ST & LO & BUD & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS) Ea1 Hv.
    unfold STDIO_STACK in BUD. unfold EMIT_PRINTF_ENTRY.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    subst a1.
    ienterG.
    carve_frame 80%nat ST.
    zsteps_to 0x44504%Z.
    (* [comment removed for export] *)
    destruct (drv_stack_writes L RNG s CL FB m m0 _ (bv_unsigned sp) G MU WM) as [G1 AG0];
      [constructor; [cbn [fst snd]; lia| constructor] | lia |].
    clear MU WM.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs m0 _ [_; _; _] _)) in FR as [FR1 FR2]. cbn [cells_size csize Nat.add] in FR2.
    apply (rw_cells_merge asegs m0 _ [C8 (Z_to_bv 64 v)] [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] []) in FR2.
    cbn [cells_size csize cells_bytes cbytes Nat.add app] in FR2.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in FR2 by lia.
    name_sp sp (-80)%Z.
    apply evtF_done. unfold emit_d. eapply implMG_post_evtF.
    { eapply VPR with (AP := (bv_unsigned sp + -56)%Z) (v := v).
      { split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI|]. split; [exact TPE|]. split; [rewrite Hsp; aln|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
      - reflexivity.
      - reflexivity.
      - exact Hv.
      - eapply drv_lit_mobjA; [exact G1 | exact RIMG | exact RISH | unfold FMT_D; lia | unfold FMT_D, DRV_RODATA_HI; lia | lia].
      - exact FR2.
      - rewrite Hsp. lia.
      - lia. }
    intros [] s' RNG' ms' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP a0v m' E OF MI' ST' AG G'; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. clear MI. rename MI' into MI.
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP) in HR end.
    replace (ret_pc (Z_to_bv 64 542236)) with (Z_to_bv 64 542236) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite Hsp in *.
    apply (keeps_rw_cells_stack [] CL _ _ _ _ _ AG) in FR1; [|lia].
    apply (keeps_rw_cells_stack [] CL _ _ _ _ _ AG) in FR2; [|lia].
    unname_sp.
    zstep. zstep. zstep.
    release_frame FR1 ST' (bv_unsigned sp + -56)%Z. release_frame FR2 ST' (bv_unsigned sp).
    apply evtF_done. unfold out_post_o. split; [exact FP|].
    eexists _, _. split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); cbv delta [mkR]; reflexivity|].
    split; [exact OF|]. split; [exact MI|]. split; [exact ST'|]. split; [| exact G'].
    eapply keeps_trans; [exact AG0 | exact AG | lia | intros a Ha; exact Ha | intros a Ha; exact Ha].
  Qed.
  End Zd1.
  #[using="FO fflagA USP SB GL GD VPR drv_lit_mobjA drv_stack_writes"] Lemma emit_printf_spec : ltac:(let t := eval cbv delta [emit_printf_spec__stmt] in emit_printf_spec__stmt in exact t).
  Proof. exact emit_printf_spec__body. Qed.

  (* [comment removed for export] *)
  Ltac tr_hide H := lazymatch type of H with ?T => let X := fresh "AUX" in pose (X := T); change T with X in H end.
  Ltac tr_unhide H := lazymatch type of H with ?X => subst X end.
  (* [comment removed for export] *)
  Ltac spo_tac G ST MI Hsp :=
    split; [exact G|]; split; [rewrite Hsp; exact ST|]; split; [lia|];
    split; [unfold FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK, MALLOC_STACK, FREE_STACK in *; rewrite Hsp; lia|];
    split; [rewrite Hsp; lia|]; split; [exact MI|]; split; [assumption|]; split; [rewrite Hsp; aln|];
    split; [assumption|]; split; [assumption|]; split; assumption.

  (* [comment removed for export] *)
  Definition loop_post (spi gp tp s0 s1 s2 s4 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL : list cblk) (lo : Z) (bad : bool) (m : mem) : bool -> PS -> footprint -> machine_state -> Prop :=
    fun bad' s' RNG' ms' => fp_le RNG RNG' /\ exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3' m' FB',
      ms' = MS (mkR ra' spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3' s4 (Z_to_bv 64 0) (Z_to_bv 64 (Z.b2z bad)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x84548) fc None m' (seg_rom asegs)
      /\ bad' = bad /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned spi)
      /\ agrees_on (client_keeps [] CL (bv_unsigned spi)) m m' /\ GIOA L RNG' s' CL FB' [] m'.

  #[using="fflagA USP SB GL GL1 GD GA GCB FUZZ VPR drv_lit_mobjA drv_stack_writes drv_keeps drv_keeps1 data_loc_cobjA1"] Lemma loop_spec : forall (n : nat) (ra spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo D : Z) (data : list byte) (bad : bool),
    (1 <= n <= 4)%nat ->
    std_pre_o GIOA L RNG spi tp s CL FB [] lo FUZZ_STACK m -> traces_fuzz_one TP L RA_FUZZ [] ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s5 = Z_to_bv 64 (Z.of_nat n) -> s4 = Z_to_bv 64 DRV_INIT_FLAG ->
    s6 = Z_to_bv 64 (Z.b2z bad) -> s7 = Z_to_bv 64 (-2) ->
    bytes_at asegs m D data -> data_loc CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (call_loop (@emit_d PS hptr ps_libc set_libc) (harness_call HO FO sites) n (map bv_unsigned data) bad) s
      (loop_post spi gp tp s0 s1 s2 s4 s7 s8 s9 s10 s11 F fc L RNG CL lo bad m)
      (MS (mkR ra spi gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x84510) fc None m (seg_rom asegs)).
  Proof.
    induction n as [|n IH]; [intros; lia|].
    intros until bad. intros Hn (G & ST & LO & BUD & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS) TRF Es0 Es1 Es5 Es4 Es6 Es7 SRC HK HD.
    pose proof BUD as BUD'. unfold FUZZ_STACK, PCAP_L4_STACK in BUD'.
    pose proof (bv_unsigned_in_range 64 spi) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
    subst s0 s1 s5 s4 s6 s7. unfold DRV_INIT_FLAG.
    cbn [call_loop].
    (* [comment removed for export] *)
    destruct (ga_get _ GA _ _ _ _ _ _ _ G) as (reg & ATXC). destruct ATXC as (_ & CBC & _).
    pose proof (munch_refl [(0x5e1054, 0x5e1055)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    tr_hide SRC.
    ienterG. zstep. zstep.
    tr_unhide SRC.
    lazymatch type of MU with munch _ _ ?mb =>
      assert (G1 : GIOA1 L RNG s CL FB [] mb);
      [ eapply (gc_set _ _ GCB); [exact G | exact MU | exact WM | exact CBC]
      | assert (AG0 : agrees_on (client_keeps [] CL (bv_unsigned spi)) m mb);
        [ eapply (drv_keeps L RNG s [] CL FB m mb _ (bv_unsigned spi)); [exact G | exact MU | exact WM | | lia];
          constructor; [right; right; right; right; left; cbn [fst snd]; unfold DRV_INIT_FLAG; lia | constructor] | ] ]
    end.
    apply (agrees_bytes_at _ _ _ _ _ AG0) in SRC; [| intros a Ha; right; left; eapply data_loc_keeps; eassumption].
    clear MU WM G CBC reg.
    zstep. zstep. zstep.
    apply evtF_done. eapply implMG_bind.
    { eapply FUZZ with (trC := @nil Z) (D := D) (data := data);
        [ | eapply (ucaller_data depth_fuzz_one _ _ _ _ _ RA_FUZZ); [rewrite unsigned_lit by lia; lia | reflexivity | unfold RA_FUZZ, ACLIENT_LO, ACLIENT_HI; lia | unfold depth_fuzz_one; lia]
          | rewrite unsigned_lit by (unfold RA_FUZZ; lia); exact TRF | reflexivity | reflexivity | exact SRC | eapply data_loc_cobjA1; eassumption | exact HD].
      split; [exact G1|]. split; [exact ST|]. split; [exact LO|]. split; [exact BUD|].
      split; [exact SPT|]. split; [exact MI|]. split; [exact TPE|]. split; [exact ALN|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    intros rc' s' RNG1 ms' PO. cbv beta in PO. destruct PO as (FP1 & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MI1 ST1 AG1 G1' ndR2__; nd_post; revert ndR2__; intros ->).
    clear MI G1. cbn [fst snd].
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
    replace (ret_pc (Z_to_bv 64 0x84524)) with (Z_to_bv 64 0x84524) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    destruct (gc_cell _ _ GCB _ _ _ _ _ _ _ G1') as (reg & ATXC). destruct ATXC as (_ & CBC & _).
    lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (munch_refl [(0x5e1054, 0x5e1055)]%Z m1) as MU; pose proof (wmono_refl asegs m1) as WM end.
    ienterG. zstep. zstep.
    lazymatch type of MU with munch _ ?ma ?mb => lazymatch type of G1' with GIOA1 _ _ _ _ ?fb _ _ =>
      assert (G2 : GIOA L RNG1 s' CL fb [] mb);
      [ eapply (gc_clr _ _ GCB); [exact G1' | exact MU | exact WM | exact CBC]
      | assert (AG2 : agrees_on (client_keeps [] CL (bv_unsigned spi)) ma mb);
        [ eapply (drv_keeps1 L RNG1 s' [] CL fb ma mb _ (bv_unsigned spi)); [exact G1' | exact MU | exact WM | | lia];
          constructor; [right; right; right; right; left; cbn [fst snd]; unfold DRV_INIT_FLAG; lia | constructor] | ] ]
    end end.
    clear MU WM G1' CBC reg.
    zstep. zstep.
    apply evtF_done. eapply implMG_bind.
    { eapply (emit_printf_spec _ spi) with (v := 0%Z); [| reflexivity | lia].
      split; [exact G2|]. split; [eassumption|]. split; [exact LO|]. split; [unfold STDIO_STACK; lia|].
      split; [exact SPT|]. split; [eassumption|]. split; [exact TPE|]. split; [exact ALN|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    intros [] s'' RNG2 ms'' PO. unfold out_post_o in PO. (nd_pre PO 9%nat; intros FP2 a0v m2 E OF2 MI2 ST2 AG3 G3; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms''.
    cbn [fst snd].
    repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    replace (ret_pc (Z_to_bv 64 0x84534)) with (Z_to_bv 64 0x84534) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite bad_rc_step0.
    ienterG. zstep. zstep. if_true. zstep.
    replace (bv_swrap 32 (Z.of_nat (S n) + -1)) with (Z.of_nat n) by (rewrite bv_swrap_small; [lia| change (bv_half_modulus 32) with 2147483648%Z; lia]).
    assert (AGall : agrees_on (client_keeps [] CL (bv_unsigned spi)) m m2).
    { eapply keeps_trans; [exact AG0 | eapply keeps_trans; [exact AG1 | eapply keeps_trans; [exact AG2 | exact AG3 | lia | intros a Ha; exact Ha | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha | intros a Ha; exact Ha]. }
    destruct (Nat.eq_dec n 0) as [->|Hn0].
    - change (Z.of_nat 0) with 0%Z. zstep. if_false. apply evtF_done. apply implMG_ret. apply evtF_done.
      unfold loop_post. split; [eapply fp_le_trans; [exact FP1| exact FP2]|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact AGall|exact G3].
    - zstep. if_true_by (nez_cond (Z.of_nat n) ltac:(lia)).
      apply evtF_done. eapply implMG_mono.
      + eapply IH with (D := D) (data := data) (bad := bad); [lia | | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | exact HK | exact HD].
        * split; [exact G3|]. split; [exact ST2|]. split; [exact LO|]. split; [exact BUD|].
          split; [exact SPT|]. split; [exact MI2|]. split; [exact TPE|]. split; [exact ALN|].
          split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
        * exact TRF.
        * eapply agrees_bytes_at; [exact AG3 | eapply agrees_bytes_at; [exact AG2 | eapply agrees_bytes_at; [exact AG1 | exact SRC |] |] |]; intros a Ha; right; left; eapply data_loc_keeps; eassumption.
      + cbv beta. intros b2 s2' RNG3 ms2 PO. unfold loop_post in *. destruct PO as (FP3 & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MI4 ST4 AG4 G4; nd_post).
        split; [eapply fp_le_trans; [exact FP1| eapply fp_le_trans; [exact FP2| exact FP3]]|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [|exact G4].
        eapply keeps_trans; [exact AGall | exact AG4 | lia | intros a Ha; exact Ha | intros a Ha; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Definition tr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL : list cblk) (lo SP : Z) (m : mem) : Z -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' FB',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps [] CL SP) m m'
      /\ GIOA L RNG' s' CL FB' [] m' /\ (0 <= r <= 2)%Z.

  #[using="fflagA USP SB GL GL1 GD GA GCB MALLOC FREE FREENULL FUZZ VPR drv_lit_mobjA drv_stack_writes drv_keeps drv_keeps1 data_loc_cobjA data_loc_cobjA1 block_mobjA"] Lemma rest_spec : forall (k : nat) (o : option hptr)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo D : Z) (data : list byte),
    (1 <= k <= 4)%nat ->
    GIOA L RNG s (match o with Some q => (q, D, Z.of_nat (length data)) :: CL | None => CL end) FB [] m ->
    stk asegs m lo (bv_unsigned sp + -80) -> (ATOP + 4096 <= lo)%Z -> (lo + TARGET_RUN_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp - 48 < al_top L /\ al_top L <= 2^47)%Z -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> (bv_unsigned sp mod 16 = 0)%Z ->
    rng RNG lo (al_top L - lo) -> rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    traces_drv L -> traces_fuzz_one TP L RA_FUZZ [] ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 DRV_INIT_FLAG ->
    s2 = match o with Some _ => Z_to_bv 64 D | None => Z_to_bv 64 0 end ->
    bytes_at asegs m D data ->
    match o with Some q => True | None => data = [] /\ (0x10040 <= D /\ D <= 0x603fc0)%Z end ->
    (Z.of_nat (length data) < 2^26)%Z ->
    rw_cells asegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implMG RNG (bad <- call_loop (@emit_d PS hptr ps_libc set_libc) (harness_call HO FO sites) k (map bv_unsigned data) false ;;
                match o with Some q => pfree HO q | None => mret tt end ;;;
                mret (if bad then 78 else 0)%Z) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc L RNG CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x84508) fc None m (seg_rom asegs)).
  Proof.
    intros until data. intros Hk G ST LO BUD SPT MI TPE ALN RSTK RSTK2 RIMG RISH RTLS TRD TRF Es0 Es1 Es5 Es4 Es2 SRC HO0 HD FR.
    pose proof BUD as BUD'. unfold TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in BUD'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
    subst s0 s1 s5 s4.
    (* [comment removed for export] *)
    ienterG. zstep. zstep.
    name_sp sp (-80)%Z.
    apply evtF_done.
    eapply implMG_bind.
    { eapply (loop_spec k) with (D := D) (data := data) (bad := false); [exact Hk | | exact TRF | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact SRC | | exact HD].
      - spo_tac G ST MI Hsp.
      - destruct o as [q|]; [right; exists (q, D, Z.of_nat (length data)); split; [left; reflexivity| cbn [cb_addr cb_size fst snd]; lia] | left; exact HO0]. }
    intros bad' s' RNG1 ms' PO. unfold loop_post in PO. destruct PO as (FP1 & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MI1 ST1 AG1 G1; nd_post). clear MI.
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
    rewrite Hsp in *.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
    unname_sp.
    ienterG. zstep. zstep.
    destruct o as [q|]; subst s2.
    - (* [comment removed for export] *)
      name_sp sp (-80)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply FREE with (C1 := @nil cblk) (q := q) (A := D) (n := Z.of_nat (length data)); [| reflexivity |].
        - spo_tac G1 ST1 MI1 Hsp.
        - eapply unw_of_ucaller with (trC := @nil Z);
            [ eapply (ucaller_data 0%nat _ _ _ _ _ 0x84550%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia
            | rewrite unsigned_lit by lia; apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | assumption ]. }
      intros [] s'' RNG2 ms'' PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP2 a0v m2 E OF2 MI2 ST2 AG2 G2; nd_post). clear MI1.
      unfold hpost_regs in E. destruct_exs E. subst ms''.
      cbn [app] in AG2, G2.
      repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
      replace (ret_pc (Z_to_bv 64 0x84550)) with (Z_to_bv 64 0x84550) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hsp in *.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
      unname_sp.
      ienterG. do 3 zstep.
      do 11 zstep.
      apply evtF_done. apply implMG_ret. apply evtF_done.
      release_frame FR ST2 (bv_unsigned sp).
      unfold tr_post. split; [eapply fp_le_trans; [exact FP1| exact FP2]|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [|split; [exact G2| lia]].
      eapply keeps_trans; [ | exact AG2 | lia | intros a Ha; exact Ha | intros a Ha; exact Ha].
      eapply client_keeps_weaken; [exact AG1 | lia | intros a Ha; apply in_block_cons; exact Ha | intros a Ha; exact Ha].
    - (* [comment removed for export] *)
      name_sp sp (-80)%Z.
      eapply evtF_cut.
      { eapply FREENULL; [| reflexivity |].
        - spo_tac G1 ST1 MI1 Hsp.
        - eapply unw_of_ucaller with (trC := @nil Z);
            [ eapply (ucaller_data 0%nat _ _ _ _ _ 0x84550%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | lia]
            | unfold AFREE_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia
            | rewrite unsigned_lit by lia; apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | assumption ]. }
      intros ms' PO. cbv beta in PO. (nd_pre PO 7%nat; intros a0v m2 E MI2 ST2 AG2 G2; nd_post). clear MI1.
      unfold hpost_regs in E. destruct_exs E. subst ms'.
      replace (ret_pc (Z_to_bv 64 0x84550)) with (Z_to_bv 64 0x84550) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite Hsp in *.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG2) in FR; [|lia].
      unname_sp.
      do 3 zstep.
      do 11 zstep.
      apply evtF_done. apply implMG_ret_bind. apply implMG_ret. apply evtF_done.
      release_frame FR ST2 (bv_unsigned sp).
      unfold tr_post. split; [exact FP1|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [|split; [exact G2| lia]].
      eapply keeps_trans; [exact AG1 | exact AG2 | lia | intros a Ha; exact Ha | intros a Ha; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Definition tr_rest (k : nat) (pl : list Z) : Monad.M PS Z :=
    owned <- (if (length pl =? 0)%nat then mret (Some None)
              else q <- pmalloc HO (zlength pl) ;;
                   mret (match q with None => None | Some q' => Some (Some q') end)) ;;
    match owned with
    | None => mret 2%Z
    | Some o =>
        bad <- call_loop (@emit_d PS hptr ps_libc set_libc) (harness_call HO FO sites) k pl false ;;
        (match o with Some q => pfree HO q | None => mret tt end) ;;;
        mret (if bad then 78 else 0)%Z
    end.

  (* [comment removed for export] *)
  #[using="fflagA USP SB GL GL1 GD GA GCB MALLOC FREE FREENULL FUZZ VPR drv_lit_mobjA drv_stack_writes drv_keeps drv_keeps1 data_loc_cobjA data_loc_cobjA1 block_mobjA"] Lemma path_empty : forall (k : nat)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo : Z),
    (1 <= k <= 4)%nat ->
    GIOA L RNG s CL FB [] m ->
    stk asegs m lo (bv_unsigned sp + -80) -> (ATOP + 4096 <= lo)%Z -> (lo + TARGET_RUN_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp - 48 < al_top L /\ al_top L <= 2^47)%Z -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> (bv_unsigned sp mod 16 = 0)%Z ->
    rng RNG lo (al_top L - lo) -> rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    traces_drv L -> traces_fuzz_one TP L RA_FUZZ [] ->
    s0 = Z_to_bv 64 0 -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 DRV_INIT_FLAG ->
    rw_cells asegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implMG RNG (tr_rest k []) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc L RNG CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x84500) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros Hk G ST LO BUD SPT MI TPE ALN RSTK RSTK2 RIMG RISH RTLS TRD TRF Es0 Es5 Es4 FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof BUD as BUD'. unfold TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in BUD'.
    subst s0 s5 s4.
    unfold tr_rest. cbn [length Nat.eqb]. apply implMG_ret_bind. cbv beta iota.
    ienterG. zstep. zstep.
    apply evtF_done. eapply rest_spec with (o := None) (data := @nil byte) (D := (DRV_INIT_FLAG + 16)%Z) (FB := FB);
      [exact Hk | exact G | exact ST | exact LO | exact BUD | exact SPT | exact MI | exact TPE | exact ALN | exact RSTK | exact RSTK2 | exact RIMG | exact RISH | exact RTLS
      | exact TRD | exact TRF | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | apply bytes_at_nil; unfold DRV_INIT_FLAG; lia | split; [reflexivity| unfold DRV_INIT_FLAG; lia] | cbn; lia | exact FR].
  Qed.

  (* [comment removed for export] *)
  #[using="fflagA USP SB GL GL1 GD GA GCB MALLOC FREE FREENULL FUZZ VPR drv_lit_mobjA drv_stack_writes drv_keeps drv_keeps1 data_loc_cobjA data_loc_cobjA1 block_mobjA"] Lemma path_alloc : forall (k : nat)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 : word) (junk : list byte)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (lo P : Z) (src : list byte),
    (1 <= k <= 4)%nat ->
    GIOA L RNG s CL FB [] m ->
    stk asegs m lo (bv_unsigned sp + -80) -> (ATOP + 4096 <= lo)%Z -> (lo + TARGET_RUN_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp - 48 < al_top L /\ al_top L <= 2^47)%Z -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> (bv_unsigned sp mod 16 = 0)%Z ->
    rng RNG lo (al_top L - lo) -> rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
    traces_drv L -> traces_fuzz_one TP L RA_FUZZ [] ->
    s0 = Z_to_bv 64 (Z.of_nat (length src)) -> s1 = Z_to_bv 64 P -> s5 = Z_to_bv 64 (Z.of_nat k) -> s4 = Z_to_bv 64 DRV_INIT_FLAG ->
    (0 < length src)%nat -> (Z.of_nat (length src) < 2^26)%Z ->
    bytes_at asegs m P src ->
    (exists b, In b CL /\ (cb_addr b <= P /\ P + Z.of_nat (length src) <= cb_addr b + cb_size b)%Z) ->
    rw_cells asegs m (bv_unsigned sp + -80) [CB 8 junk; C8 cs7; C8 cs6; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implMG RNG (tr_rest k (map bv_unsigned src)) s
      (tr_post cra sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 s8 s9 s10 s11 F fc L RNG CL lo (bv_unsigned sp + -80) m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x844b4) fc None m (seg_rom asegs)).
  Proof.
    intros until src. intros Hk G ST LO BUD SPT MI TPE ALN RSTK RSTK2 RIMG RISH RTLS TRD TRF Es0 Es1 Es5 Es4 HP0 HP32 SRC HINP FR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof BUD as BUD'. unfold TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in BUD'.
    (nd_pre (block_mobjA L RNG s CL FB m P (Z.of_nat (length src)) G HINP ltac:(lia)) 3%nat; intros PO PT PI; nd_post). unfold AIMG_HI in PI.
    (nd_pre HINP 4%nat; intros pb Hpb PB1 PB2; nd_post).
    subst s0 s1 s5 s4.
    set (n := Z.of_nat (length src)) in *.
    unfold tr_rest. rewrite length_map. replace (length src =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    unfold zlength. rewrite length_map. fold n.
    apply implMG_bind_assoc.
    ienterG. zstep. zstep.
    name_sp sp (-80)%Z.
    apply evtF_done. eapply implMG_bind.
    { eapply MALLOC with (n := n); [| reflexivity | lia |].
      - spo_tac G ST MI Hsp.
      - eapply unw_of_ucaller with (trC := @nil Z);
          [ eapply (ucaller_data 0%nat _ _ _ _ _ 0x844bc%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | lia]
          | unfold AMALLOC_PC, ACLIENT_LO, ACLIENT_HI; lia | rewrite Hsp; lia
          | rewrite unsigned_lit by lia; apply TRD; unfold drv_traces; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ] | assumption ]. }
    intros r s' RNG1 ms' PO1. cbv beta in PO1. (nd_pre PO1 9%nat; intros FP1 a0v m1 E OF1 MI1 ST1 AG1 CASES; nd_post). clear MI.
    unfold hpost_regs in E. destruct_exs E. subst ms'.
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
    replace (ret_pc (Z_to_bv 64 0x844bc)) with (Z_to_bv 64 0x844bc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite Hsp in *.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
    apply (keeps_bytes_at_block _ _ _ _ _ _ _ AG1) in SRC; [|intros a Ha; apply in_block_In; exists pb; split; [exact Hpb| lia]].
    unname_sp.
    destruct r as [q|]; [| destruct CASES].
    (nd_pre CASES 3%nat; intros A' junk' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros G1 BLK; nd_post).
    (nd_pre (block_mobjA L RNG1 s' ((q, A', n) :: CL) FB m1 A' n G1 ltac:(exists (q, A', n); split; [left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]) ltac:(lia)) 3%nat; intros DO DT DI; nd_post).
    (nd_pre (block_mobjA L RNG1 s' ((q, A', n) :: CL) FB m1 P n G1 ltac:(exists pb; split; [right; exact Hpb| lia]) ltac:(lia)) 3%nat; intros PO1 _ _; nd_post).
    unfold AIMG_HI in DI.
    assert (SEP : (P + n <= A' \/ A' + n <= P)%Z).
    { pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G1) as AP. apply blocks_apart_app_inv in AP as (AP & _ & _). cbn [blocks_apart] in AP. destruct AP as [AP _].
      pose proof (proj1 (Forall_forall _ _) AP _ Hpb) as X. unfold apart in X. cbn [cb_addr cb_size fst snd] in X. lia. }
    apply implMG_ret_bind. cbv beta iota.
    ienterG. zstep. if_false_by (eqz_cond_false A' ltac:(lia)).
    zstep. zstep. zstep. zstep.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(bv_unsigned sp + -80 - 2240, bv_unsigned sp + -80); (A', A' + n)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2 end.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G1) as (RT1 & _).
    call_sp (memcpy_i_specZ RNG1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo A' P n src junk');
      [ first [reflexivity | assumption | lia | (subst n; lia) | (eapply rng_sub'; [eassumption| lia])] .. | ].
    rename PC into ST2. rename PC0 into DST. rename POST into SRC2.
    lazymatch type of MU2 with munch _ ?ma ?mb =>
      assert (G2 : GIOA L RNG1 s' ((q, A', n) :: CL) FB [] mb);
      [ eapply (gl_client_frame _ _ _ GL); [exact G1 | exact MU2 | exact WM2 |];
        constructor; [left; cbn [fst snd]; lia | constructor; [| constructor]];
        right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia
      | assert (AG2 : agrees_on (client_keeps [] CL (bv_unsigned sp + -80)) ma mb);
        [ eapply (drv_keeps L RNG1 s' [(q, A', n)] CL FB ma mb _ (bv_unsigned sp + -80)); [exact G1 | exact MU2 | exact WM2 | | lia];
          constructor; [left; cbn [fst snd]; lia | constructor; [| constructor]];
          right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia | ] ];
      assert (DATA : bytes_at asegs mb A' src);
      [ destruct DST as [[Hwf HB] Hwr]; cbn [cells_bytes cbytes] in HB; rewrite app_nil_r in HB; exact HB | ]
    end.
    clear MU2 WM2.
    zstep. zstep.
    apply evtF_done. eapply implMG_mono.
    + eapply rest_spec with (o := Some q) (data := src) (D := A') (lo := lo) (FB := FB);
        [exact Hk | exact G2 | exact ST2 | exact LO | exact BUD | exact SPT | exact MI | exact TPE | exact ALN | assumption | assumption | assumption | assumption | assumption
        | exact TRD | exact TRF | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | exact DATA | exact I | subst n; lia | exact FR].
    + cbv beta. intros r2 s2' RNG2 ms2 PO2. unfold tr_post in *. destruct PO2 as (FP2 & PO2). destruct_exs PO2. (destruct PO2 as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MI3 ST3 AG3 G3 Hr; nd_post).
      split; [eapply fp_le_trans; [exact FP1| exact FP2]|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [|split; [exact G3| exact Hr]].
      eapply keeps_trans; [exact AG1 | eapply keeps_trans; [exact AG2 | exact AG3 | lia | intros a Ha; exact Ha | intros a Ha; exact Ha] | lia | intros a Ha; exact Ha | intros a Ha; exact Ha].
  Qed.

  #[using="fflagA USP SB GL GL1 GD GA GCB MALLOC FREE FREENULL FUZZ VPR drv_lit_mobjA drv_stack_writes drv_keeps drv_keeps1 data_loc_cobjA data_loc_cobjA1 block_mobjA"] Theorem target_run_proof : target_run_stmt_o HO FO sites GIOA TP.
  Proof.
    unfold target_run_stmt_o.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB lo A Lc content.
    intros (G & ST & LO & BUD & (SP47 & AT47) & MI & TPE & ALN & RSTK & RSTK2 & RIMG & RISH & RTLS) SPT0 TRD TRF SRC HL0 HL6 HLEN HINB Ea0 Ea1 Ea2 Ea3.
    assert (SPT : (bv_unsigned sp - 48 < al_top L /\ al_top L <= 2^47)%Z) by (split; assumption).
    pose proof BUD as BUD'. unfold TARGET_RUN_STACK, FUZZ_STACK, PCAP_L4_STACK, STDIO_STACK in BUD'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SBD.
    (nd_pre (block_mobjA L RNG s CL FB m A (Z.of_nat (length content)) G HINB ltac:(lia)) 3%nat; intros (_ & _ & _ & CRNG & _) SRCT SRCI; nd_post). unfold AIMG_HI in SRCI.
    (nd_pre HINB 4%nat; intros cb Hcb CB1 CB2; nd_post).
    (* [comment removed for export] *)
    assert (exists b0 b1 b2 rest, content = b0 :: b1 :: b2 :: rest) as (b0 & b1 & b2 & rest & EC).
    { destruct content as [|x0 [|x1 [|x2 r]]]; [cbn in HL6; lia..|]. repeat eexists. }
    unfold TARGET_RUN_ENTRY. unfold run, target_run.
    set (pl := skipn (Z.to_nat (6 + Lc)) (map bv_unsigned content)).
    set (cfg := firstn (Z.to_nat Lc) (skipn 2 (map bv_unsigned content))).
    set (k := Z.to_nat (1 + Z.land (match cfg with [] => 0 | b :: _ => b end) 3)).
    set (plen := (Z.of_nat (length content) - 6 - Lc)%Z) in *.
    set (src := skipn (Z.to_nat (6 + Lc)) content).
    assert (Epl : pl = map bv_unsigned src). { subst pl src. rewrite skipn_map. reflexivity. }
    assert (Hsrc : length src = Z.to_nat plen). { subst src plen. rewrite length_skipn. lia. }
    assert (SRCp : bytes_at asegs m (A + 6 + Lc) src).
    { subst src. pose proof SRC as SRC2. rewrite <- (firstn_skipn (Z.to_nat (6 + Lc)) content) in SRC2. apply bytes_at_app in SRC2 as [_ S2].
      rewrite length_firstn in S2. replace (A + Z.of_nat (Nat.min (Z.to_nat (6 + Lc)) (length content)))%Z with (A + 6 + Lc)%Z in S2 by lia. exact S2. }
    assert (HINP : exists b, In b CL /\ (cb_addr b <= A + 6 + Lc /\ A + 6 + Lc + Z.of_nat (length src) <= cb_addr b + cb_size b)%Z).
    { exists cb. split; [exact Hcb| lia]. }
    assert (Hk : (1 <= k <= 4)%nat). { subst k. pose proof (land3_range (match cfg with [] => 0 | b :: _ => b end)). lia. }
    change (Z.to_nat (1 + Z.land (match cfg with [] => 0 | b :: _ => b end) 3)) with k.
    rewrite Epl.
    subst a0 a1 a2 a3.
    (* [comment removed for export] *)
    destruct (ga_get _ GA _ _ _ _ _ _ _ G) as (reg & ATXC).
    destruct ATXC as (IFL & CBC & FIN & ALK & SLOT & HEAD & NEXT & F0 & F1 & A0 & A1 & (cdt & thr & sec & tm1 & LIBC)).
    (nd_pre (gd_misc _ _ _ GD _ _ _ _ _ _ _ G) 3%nat; intros _ _ GLI; nd_post).
    unfold GOT_FUZZ_INIT in GLI.
    pose proof (munch_refl [(0x5e1050, 0x5e1058); (0x601a08, 0x601c28); (bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    ienterG.
    carve_frame 80%nat ST.
    do 17 zstep.
    call_sp (reg_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo reg);
      [ first [ exact ST | exact GLI | exact MI | exact RIMG | reflexivity | lia | (eapply rng_sub'; [exact RSTK2| lia])
              | (unfold atx_cells; repeat (split; [first [assumption | hyp_by_addr]|]); exists cdt, thr, sec, tm1; first [assumption | hyp_by_addr]) ] .. |].
    lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI' end.
    lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
    lazymatch goal with H : atx_cells true 0 _ |- _ => rename H into ATX1 end.
    (* [comment removed for export] *)
    lazymatch type of MU with munch _ _ ?mb =>
      assert (G1 : GIOA L RNG s CL FB [] mb);
      [ eapply (ga_frame _ GA) with (W := [(bv_unsigned sp - 128, bv_unsigned sp)]%Z) (reg' := true); [exact G | | exact WM | | exact ATX1];
        [ eapply munch_weaken; [| exact MU]; intros xq Hx; unfold ATX_KEEP, DRV_INIT_FLAG, ATX in Hx; cbn [app outside] in Hx |- *; lia
        | constructor; [left; left; cbn [fst snd]; lia | constructor] ]
      | assert (AG0 : agrees_on (client_keeps [] CL (bv_unsigned sp)) m mb);
        [ eapply (drv_keeps L RNG s [] CL FB m mb _ (bv_unsigned sp)); [exact G | exact MU | exact WM | | lia];
          constructor; [right; right; right; right; left; cbn [fst snd]; unfold DRV_INIT_FLAG; lia
                       | constructor; [right; right; right; right; right; cbn [fst snd]; unfold ATX; lia
                                      | constructor; [left; cbn [fst snd]; lia | constructor]]] | ] ]
    end.
    clear MU WM.
    (* [comment removed for export] *)
    assert (TAIL : forall r s' RNG' ms' m1, agrees_on (client_keeps [] CL (bv_unsigned sp)) m m1 ->
              tr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo (bv_unsigned sp + -80) m1 r s' RNG' ms' ->
              target_run_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m r s' RNG' ms').
    { intros r s' RNG' ms' m1 AGa PO. unfold tr_post in PO. destruct PO as (FPf & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MIf STf AGf Gf Hr; nd_post).
      unfold target_run_post. split; [exact FPf|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MIf|]. split; [exact STf|]. split; [| split; [exact Gf| exact Hr]].
      eapply keeps_trans; [exact AGa | exact AGf | lia | intros a Ha; exact Ha | intros a Ha; exact Ha]. }
    zstep.
    destruct (Z.eq_dec Lc 0) as [EL|NL].
    - (* [comment removed for export] *)
      assert (Ek : k = 1%nat). { subst k cfg. rewrite EL. reflexivity. }
      replace (Z_to_bv 64 Lc) with z64 by (rewrite EL; reflexivity). if_true. zstep. zstep.
      destruct (Z.eq_dec plen 0) as [EP|NP].
      + replace (Z_to_bv 64 plen) with z64 by (rewrite EP; reflexivity). if_false.
        assert (Esrc : src = []). { destruct src; [reflexivity| rewrite EP in Hsrc; cbn in Hsrc; lia]. }
        rewrite Esrc. apply evtF_done. eapply implMG_mono.
        * eapply path_empty with (lo := lo) (FB := FB);
            [exact Hk | exact G1 | exact ST' | exact LO | exact BUD | exact SPT | exact MI' | exact TPE | exact ALN | exact RSTK | exact RSTK2 | exact RIMG | exact RISH | exact RTLS
            | exact TRD | exact TRF | reflexivity | rewrite Ek; reflexivity | reflexivity | exact FR].
        * intros r s' RNG' ms'. apply TAIL. exact AG0.
      + if_true_by (nez_cond plen ltac:(lia)).
        apply evtF_done. eapply implMG_mono.
        * eapply path_alloc with (lo := lo) (P := (A + 6 + Lc)%Z) (src := src) (FB := FB);
            [exact Hk | exact G1 | exact ST' | exact LO | exact BUD | exact SPT | exact MI' | exact TPE | exact ALN | exact RSTK | exact RSTK2 | exact RIMG | exact RISH | exact RTLS
            | exact TRD | exact TRF | f_equal; lia | reflexivity | rewrite Ek; reflexivity | reflexivity | lia | lia
            | exact SRCp
            | exact HINP | exact FR].
        * intros r s' RNG' ms'. apply TAIL. exact AG0.
    - (* [comment removed for export] *)
      assert (Ek : (Z.of_nat k = Z.land (bv_unsigned b2) 3 + 1)%Z).
      { subst k cfg. rewrite EC. replace (Z.to_nat Lc) with (S (Z.to_nat (Lc - 1))) by lia. cbn [map skipn firstn].
        pose proof (land3_range (bv_unsigned b2)). lia. }
      if_false_by (eqz_cond_false Lc ltac:(lia)).
      pose proof SRC as SRC3.
      rewrite EC in SRC3.
      pose proof (bytes_at_read asegs _ A _ 2 1 SRC3 ltac:(lia) ltac:(cbn; lia)) as HR. clear SRC3.
      change (Z.to_nat 2) with 2%nat in HR. cbn [firstn skipn] in HR.
      assert (RB2 : rng RNG (A + 2) 1) by (eapply rng_sub'; [exact CRNG| lia]).
      zstep. zstep. zstep. zstep.
      destruct (Z.eq_dec plen 0) as [EP|NP].
      + replace (Z_to_bv 64 plen) with z64 by (rewrite EP; reflexivity). if_true.
        assert (Esrc : src = []). { destruct src; [reflexivity| rewrite EP in Hsrc; cbn in Hsrc; lia]. }
        rewrite Esrc. apply evtF_done. eapply implMG_mono.
        * eapply path_empty with (lo := lo) (FB := FB);
            [exact Hk | exact G1 | exact ST' | exact LO | exact BUD | exact SPT | exact MI' | exact TPE | exact ALN | exact RSTK | exact RSTK2 | exact RIMG | exact RISH | exact RTLS
            | exact TRD | exact TRF | reflexivity | f_equal; lia | reflexivity | exact FR].
        * intros r s' RNG' ms'. apply TAIL. exact AG0.
      + if_false_by (eqz_cond_false plen ltac:(lia)).
        apply evtF_done. eapply implMG_mono.
        * eapply path_alloc with (lo := lo) (P := (A + 6 + Lc)%Z) (src := src) (FB := FB);
            [exact Hk | exact G1 | exact ST' | exact LO | exact BUD | exact SPT | exact MI' | exact TPE | exact ALN | exact RSTK | exact RSTK2 | exact RIMG | exact RISH | exact RTLS
            | exact TRD | exact TRF | f_equal; lia | reflexivity | f_equal; lia | reflexivity | lia | lia
            | exact SRCp
            | exact HINP | exact FR].
        * intros r s' RNG' ms'. apply TAIL. exact AG0.
  Qed.
End TargetRun.
End CANSEC1.

(* [comment removed for export] *)
End TwB.
