(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require EasAmong.
From Stdlib Require Uint63.
From Corelib Require PrimString.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StartupFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require EntryCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_main_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.CallKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.ImgAny.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_target_run.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import EasAmong.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.   (* [comment removed for export] *)
From Stdlib Require Uint63.
From Corelib Require PrimString.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implM_bind_u : forall segs {St A B} (m : @M St A) (f : A -> @M St B) s Q1 Q ms,
  implM segs m s Q1 ms -> (forall a s' ms', Q1 a s' ms' -> implM segs (f a) s' Q ms') ->
  impl segs (at_node segs) (npeek segs) (mbind m f s) (epost (fun p => Q (fst p) (snd p))) ms.
Proof. intros segs St A B m f s Q1 Q ms H1 H2. exact (implM_bind segs m f s Q1 Q ms H1 H2). Qed.

Section WithCeil.
Context {CEILV : CEIL}.
Definition img_lit (A : Z) (n : nat) : list byte := match image_bytes ssegs A n with Some bs => bs | None => [] end.
Definition MSG_OOM_bytes : list byte := img_lit 0x104f4 19.
Definition MSG_SHORT_HDR_bytes : list byte := img_lit 0x10e00 31.
Definition MSG_CFG_OVERRUN_bytes : list byte := img_lit 0x106e5 31.

Lemma MSG_OOM_ok : ro_bytes_b ssegs 0x104f4 MSG_OOM_bytes = true /\ map bv_unsigned MSG_OOM_bytes = List.concat pieces_oom /\ length MSG_OOM_bytes = 19%nat.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. vm_compute. repeat split; reflexivity. Qed.
Lemma MSG_SHORT_HDR_ok : ro_bytes_b ssegs 0x10e00 MSG_SHORT_HDR_bytes = true /\ map bv_unsigned MSG_SHORT_HDR_bytes = List.concat pieces_short_hdr /\ length MSG_SHORT_HDR_bytes = 31%nat.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. vm_compute. repeat split; reflexivity. Qed.
Lemma MSG_CFG_OVERRUN_ok : ro_bytes_b ssegs 0x106e5 MSG_CFG_OVERRUN_bytes = true /\ map bv_unsigned MSG_CFG_OVERRUN_bytes = List.concat pieces_cfg_overrun /\ length MSG_CFG_OVERRUN_bytes = 31%nat.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. vm_compute. repeat split; reflexivity. Qed.

Lemma lit_bytes_at : forall m A bs, mem_inv ssegs m -> ro_bytes_b ssegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z -> bytes_at ssegs m A bs.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros m A bs MI RB HA HB. apply ro_bytes_at; [exact MI | exact HA | exact HB |]. apply ro_bytes_b_sound. exact RB. Qed.

Lemma cap_double_ok : forall cap j, (cap = 65536 * 2 ^ j)%Z -> (0 <= j)%Z -> (cap < 67108864)%Z ->
  (cap * 2 = 65536 * 2 ^ (j + 1))%Z /\ (cap * 2 <= 67108864)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros cap j -> Hj Hc. split. { rewrite Z.pow_add_r by lia. change (2 ^ 1)%Z with 2%Z. lia. }
  assert (Hj10 : (2 ^ j < 2 ^ 10)%Z) by (change (2 ^ 10)%Z with 1024%Z; lia).
  apply Z.pow_lt_mono_r_iff in Hj10; [|lia|lia].
  assert (2 ^ (j + 1) <= 2 ^ 10)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 10)%Z with 1024%Z in H. rewrite Z.pow_add_r in H by lia. change (2 ^ 1)%Z with 2%Z in H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma read_specZ : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd B count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m B [CB (Z.to_nat count) junk] ->
  rw_cells ssegs m (bv_unsigned tp + -164) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 2^24)%Z -> (0 <= B)%Z -> (B + count <= 2^47)%Z ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned tp + -164 + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned tp + -164)%Z ->
  (B + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= B)%Z ->
  (B + count <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= B)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NRead fd B count) (dec_read B count))
       (epost (read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x214e8) fc None m (seg_rom ssegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros until lo. intros ST DST ERR MI -> EA1 -> FD CNT B0 UB LO SEP1 SEP2 SEP3 TP.
  assert (EB : bv_unsigned a1 = B). { subst a1. apply unsigned_lit. lia. }
  rewrite <- EB. rewrite <- EB in DST, SEP2, SEP3, UB.
  eapply read_spec; try eas_among ST DST ERR MI FD CNT UB LO SEP1 SEP2 SEP3 TP; try reflexivity; lia.
Qed.

Lemma ltu_cond_true : forall x y, (0 <= x < y)%Z -> (y < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_lt. lia. Qed.
Lemma ltu_cond_false : forall x y, (0 <= y <= x)%Z -> (x < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltz_cond_false : forall x, (0 <= x < 2^63)%Z -> bv_lts (Z_to_bv 64 x) z64 = false.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. rewrite bv_lts_zero_r, unsigned_lit by lia. apply Z.leb_gt. lia. Qed.
Lemma ltz_cond_m1 : bv_lts (Z_to_bv 64 (-1)) z64 = true.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. reflexivity. Qed.

Section Main.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites_of : Z -> stack_site -> Z) (sites : stack_site -> Z).
  (* [comment removed for export] *)
  Variable SEF : Z.
  Hypothesis SEF_range : (0 <= SEF <= 0x10000)%Z.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOC : malloc_stmt HO K.
  Hypothesis FREE : free_stmt HO K.
  Hypothesis FUZZ : fuzz_one_stmt HO K sites_of sites.
  Hypothesis VPR : vprintf_d_stmt K.
  Hypothesis EPR_USAGE : eprintf_s_stmt47 K FMT_USAGE pieces_usage.   (* [comment removed for export] *)
  Hypothesis EPR_OPEN : eprintf_s_stmt47 K FMT_CANNOT_OPEN pieces_cannot_open.
  Hypothesis EPR_READ : eprintf_s_stmt47 K FMT_READ_ERROR pieces_read_error.
  Hypothesis EPR_BIG : eprintf_i_stmt K FMT_TOO_BIG 0x4000000 pieces_too_big.
  Hypothesis EFW : efwrite_stmt K.
  (* [comment removed for export] *)
  Hypothesis SITE_RS : sites SiteReadStage = 0x23989%Z.

  (* [comment removed for export] *)
  Ltac name_spm R :=
    remember (Z_to_bv 64 (usp0 R + -128)) as spm eqn:Espm;
    assert (Hspm : bv_unsigned spm = (usp0 R + -128)%Z) by (rewrite Espm; apply unsigned_lit; lia).
  Ltac unname_spm := match goal with H : bv_unsigned ?s = (usp0 _ + -128)%Z |- _ => is_var s; rewrite H in *; subst s; clear H end.

  (* [comment removed for export] *)
  Ltac aln16 := match goal with H : (usp0 ?R mod 16 = 0)%Z |- _ => generalize H; clear; intros; Z.div_mod_to_equations; lia end.

  (* [comment removed for export] *)
  Ltac std_pre_tac G ST MI Hspm :=
    split; [exact G|]; split; [rewrite Hspm; exact ST|]; split; [unfold rc_lo; lia|];
    split; [unfold TARGET_RUN_STACK; unfold rc_lo, STDIO_STACK, MALLOC_STACK, FREE_STACK, FUZZ_STACK; lia|];
    split; [unfold rc_spmain; lia|]; split; [exact MI|]; split; [reflexivity| rewrite Hspm; aln16].

  (* [comment removed for export] *)
  Definition GI_at_exit__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo code : Z),
    GI K R s CL m -> rc_cb R = false ->  (* [comment removed for export] *)
    mem_inv ssegs m -> stk ssegs m lo (bv_unsigned sp) -> (rc_lo R <= lo)%Z -> (lo <= bv_unsigned sp - 80 - SEF)%Z ->
    (bv_unsigned sp <= usp0 R)%Z ->      (* [comment removed for export] *)
    tp = rc_tp R -> a0 = Z_to_bv 64 code ->
    at_exit (St:=PState H hptr) (SXGI K) SEF code s
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1845c) fc None m (seg_rom ssegs)).
  Section Sz11.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo code : ltac2:(SecDiet.SzSec.tyM 'GI_at_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma GI_at_exit__body : ltac2:(SecDiet.SzSec.bodyP 'GI_at_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt. ceil_facts.
    intros G Hcb MI ST LOLO LOSP SPUP -> ->.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof (GI_sp47 K _ _ _ _ G) as SP47. unfold rc_lo in LOLO.
    destruct G as (FB & HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & _).
    unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e & T1 & T2 & T3 & T4 & T5 & T6 & Ht); subst z x.
    destruct CLI as (L1 & L2 & L3 & L4 & L5).
    destruct CE as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    (* [comment removed for export] *)
    destruct E2 as (reg & pad & f0 & g0 & j1 & j2 & X1 & X2 & X3 & X4). rewrite Hcb in X1. cbn [bool8] in X1.
    apply (proj1 (rw_cells_app _ m _ [_; _] [_])) in X1 as [_ XF]. (sl_lit_sizes_in XF; cbn [cells_size csize Nat.add] in XF).
    match type of XF with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in XF end.
    unfold at_exit. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact ST|]. split; [exact T1|]. split; [exact E1|]. split; [exact L1|].
    split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact XF|].
    split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|]. split; [exact E7|].
    split.
    { unfold SXGI. exists R, CL, FB. split; [reflexivity|]. split; [exact HH|]. split; [exact HS|]. split; [exact HA|].
      split; [exists t, e; repeat (split; [eas_among T1 T2 T3 T4 T5 T6|]); exact Ht|]. split; [exact PT|].
      split; [split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact L5]|]. split; [exact CM|].
      split; [exact Etls|]. split; [exact TB| exact BOK]. }
    split; [exact MI|]. split; [reflexivity|]. split; [exact Ht|]. split; [lia|]. split; [lia|].
    split; [replace (bv_unsigned (rc_tp R) - 200)%Z with (utp R - 200)%Z by reflexivity; exact TB | lia].
  Qed.
  End Sz11.
  Lemma GI_at_exit : ltac:(let t := eval cbv delta [GI_at_exit__stmt] in GI_at_exit__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo code. ltac2:(SecDiet.SzSec.closeP 'GI_at_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  (* [comment removed for export] *)
  Definition main_entry (R : rctx) (s : PState H hptr) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem),
      ms = MS (mkR (Z_to_bv 64 0x17f08) (Z_to_bv 64 (usp0 R + -48)) (Z_to_bv 64 0x10800) (rc_tp R) t0 t1 t2
                   (Z_to_bv 64 (usp0 R + 8)) (Z_to_bv 64 (argc (rc_argv R)))
                   (Z_to_bv 64 (argc (rc_argv R))) (Z_to_bv 64 (usp0 R + 8)) (Z_to_bv 64 (envp_addr (rc_sp0 R) (rc_argv R))) a3 a4 a5 a6 a7
                   (Z_to_bv 64 0x13b10) (Z_to_bv 64 (envp_addr (rc_sp0 R) (rc_argv R))) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              bvmap_empty (Z_to_bv 64 0x13b10) (Z_to_bv 32 0) None m (seg_rom ssegs)
      /\ GI K R s [] m /\ mem_inv ssegs m /\ stk ssegs m (rc_lo R) (usp0 R + -48) /\ valid_argv (rc_argv R)
      /\ (usp0 R mod 16 = 0)%Z
      (* [comment removed for export] *)
      /\ (usp0 R + Z.of_nat (length (build_stack_bytes Plain.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R))) <= 2^47)%Z.

  Definition main_post : Z -> PState H hptr -> machine_state -> Prop :=
    fun code s' ms' => at_exit (St:=PState H hptr) (SXGI K) SEF code s' ms'.

  Lemma neq_cond : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y ->
    negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros x y Hx Hy Hn. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hn. Qed.
  Lemma eq_cond : forall x, negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 x)) = false.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma beq_cond : forall x, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 x) = true.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma bne_cond_false : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y ->
    bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros x y Hx Hy Hn. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact Hn. Qed.

  (* [comment removed for export] *)
  Definition main_usage__stmt : Prop := forall R s ms,
    rc_cb R = false ->
    main_entry R s ms -> Z.of_nat (length (rc_argv R)) <> 2%Z ->
    implM ssegs (main_prog HO fo_nop sites (argv_Z (rc_argv R))) s main_post ms.
  Section Sz16.
  Variables R s ms : ltac2:(SecDiet.SzSec.tyM 'main_usage__stmt "vvv" @R).
  Lemma main_usage__body : ltac2:(SecDiet.SzSec.bodyP 'main_usage__stmt "vvv").
  Proof using EPR_USAGE HFL SEF_range SFL. pin_using (fun (EPR_USAGE HFL SEF_range SFL : unit) => tt). ceil_facts.
    intros Hcb (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & -> & G & MI & ST & VA & AL16 & STKTOP) HC.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof VA as VA'. destruct VA' as (VA1 & VA2 & VA3 & VA4 & VA5).
    destruct (GI_core K _ _ _ _ G) as (_ & _ & _ & CM & _ & CS). destruct CM as (CM1 & CM2 & _). unfold CORE_STK in CS.
    destruct (rc_argv R) as [|argv0 argvr] eqn:EARGV; [cbn in VA1; lia|].
    pose proof (raw_len_nonneg Plain.M.phdrs (rc_sp0 R) (argv0 :: argvr) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R)) as RN.
    pose proof (build_stack_bytes_length Plain.M.phdrs (rc_sp0 R) (argv0 :: argvr) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R)) as BL.
    pose proof (bytes_at_bound _ _ _ _ CS) as CSB. fold (usp0 R) in BL, CSB.
    unfold main_prog, main_model. unfold argv_Z at 1. rewrite length_map.
    replace (Z.of_nat (length (argv0 :: argvr)) =? 2)%Z with false by (symmetry; apply Z.eqb_neq; exact HC). cbn [negb].
    pose proof (munch_refl [(usp0 R - 128, usp0 R - 48)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold rc_lo in ST. unfold implM. iprefix.
    carve_frame 80%nat ST.
    do 11 lstep.
    lstep. if_true_by (neq_cond (argc (argv0 :: argvr)) 2 ltac:(unfold argc; lia) ltac:(lia) ltac:(unfold argc; exact HC)).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      destruct (stack_argv_string_slack ssegs Plain.M.phdrs (rc_sp0 R) (argv0 :: argvr) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R) m1 CS
                  ltac:(fold (usp0 R); clear -AL16; Z.div_mod_to_equations; lia) 0 argv0 eq_refl)
        as (P0 & slack0 & HP0 & P0lo & P0hi & STR0 & SLK0 & END0);
      pose proof (stack_argv_ptr_read ssegs Plain.M.phdrs (rc_sp0 R) (argv0 :: argvr) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R) m1 CS 0 _ HP0) as RD0
    end.
    replace (bv_unsigned (rc_sp0 R) + 8 + 8 * Z.of_nat 0)%Z with (usp0 R + 8)%Z in RD0 by (unfold usp0; lia).
    unfold InitMem.str_base, InitMem.env_base, InitMem.str_base in P0lo, P0hi. fold (usp0 R) in P0lo, P0hi.
    do 7 lstep.
    (* [comment removed for export] *)
    assert (G1 : GI K R s [] ltac:(lazymatch type of MU with munch _ _ ?mb => exact mb end)).
    { eapply (GI_client_frame K HFL SFL); [exact G | exact MU | exact WM |].
      constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia | constructor]. }
    clear MU WM.
    name_spm R.
    apply evt_done. unfold diag, diag_usage. cbn [nth argv_Z map]. eapply (implM_bind_u ssegs).
    { eapply EPR_USAGE; [ | reflexivity | reflexivity | reflexivity | exact STR0 | | | exact SLK0 | | ].
      - std_pre_tac G1 ST MI Hspm.
      - apply Forall_cons_iff in VA4 as [X _]. exact X.
      - apply Forall_cons_iff in VA3 as [X _]. lia.
      - intros a Ha. left. lia.
      - unfold usp0 in *. lia. }
    intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
    replace (ret_pc (Z_to_bv 64 0x13cc4)) with (Z_to_bv 64 0x13cc4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
    unname_spm.
    unfold implM. iprefix. do 13 lstep.
    replace (ret_pc (Z_to_bv 64 0x17f08)) with (Z_to_bv 64 0x17f08) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lstep.
    apply evt_done. apply (implM_ret ssegs). apply evt_done. unfold main_post.
    release_frame FR ST2 (usp0 R + -48)%Z.
    eapply GI_at_exit; [exact G2 | exact Hcb | exact MI2 | rewrite unsigned_lit by lia; exact ST2 | unfold rc_lo; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity].
  Qed.
  End Sz16.
  Lemma main_usage : ltac:(let t := eval cbv delta [main_usage__stmt] in main_usage__stmt in exact t).
  Proof using EPR_USAGE HFL SEF_range SFL. intros R s ms. ltac2:(SecDiet.SzSec.closeP 'main_usage__body "vvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mframe (R : rctx) (m : mem) : Prop :=
    exists (j0 : list byte) (f1 f2 f3 f4 f5 f6 f7 f8 : word),
      rw_cells ssegs m (usp0 R + -128) [CB 8 j0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7; C8 f8; C8 (Z_to_bv 64 0x17f08)].

  (* [comment removed for export] *)
  Definition mbuf (R : rctx) (s : PState H hptr) (m : mem) (q : hptr) (A cap : Z) (CBs : list byte) : Prop :=
    GI K R s [(q, A, cap)] m /\ mem_inv ssegs m /\ stk ssegs m (rc_lo R) (usp0 R + -128) /\ mframe R m
    /\ (exists junk, rw_cells ssegs m A [CB (length CBs) CBs; CB (Z.to_nat (cap - Z.of_nat (length CBs))) junk])
    /\ (Z.of_nat (length CBs) <= cap)%Z /\ (65536 <= cap <= MAX_INPUT)%Z /\ (exists j, cap = 65536 * 2 ^ j)%Z
    /\ (usp0 R mod 16 = 0)%Z.

  (* [comment removed for export] *)
  Definition LH (R : rctx) (fd P1 : Z) (path slack : list byte) (st : rd_st (ptr:=hptr)) (s : PState H hptr) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (A : Z) (CBs : list byte) (pc : Z),
      ms = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 P1) (Z_to_bv 64 (rd_len st)) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st)) (Z_to_bv 64 0x23989) (Z_to_bv 64 A) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 pc) fc None m (seg_rom ssegs)
      (* [comment removed for export] *)
      /\ (pc = 0x13b98 \/ (pc = 0x13b78 /\ rd_len st = 0))%Z
      /\ mbuf R s m (rd_buf st) A (rd_cap st) CBs /\ rd_content st = of_bytes CBs /\ rd_len st = Z.of_nat (length CBs)
      /\ bytes_at ssegs m P1 (path ++ Z_to_bv 8 0 :: slack) /\ (usp0 R <= P1)%Z /\ (3 <= fd <= 4096)%Z.

  (* [comment removed for export] *)
  Definition at_exit2 (R : rctx) (s : PState H hptr) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (CL : list cblock),
      ms = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x13d98) fc None m (seg_rom ssegs)
      /\ GI K R s CL m /\ mem_inv ssegs m /\ stk ssegs m (rc_lo R) (usp0 R + -128).

  Lemma at_exit2_exit : forall R s ms (Q : rd_result (ptr:=hptr) -> PState H hptr -> machine_state -> Prop),
    rc_cb R = false ->
    at_exit2 R s ms ->
    (forall ms', main_post 2 s ms' -> Q RdExit s ms') ->
    evt ssegs (Q RdExit s) ms.
  Proof using SEF_range. pin_using (fun (SEF_range : unit) => tt). ceil_facts.
    intros R s ms Q Hcb (ra & gp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & CL & -> & G & MI & ST) HQ.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0. fold (usp0 R) in RSP0.
    lstep. lstep. apply evt_done. apply HQ. unfold main_post.
    eapply GI_at_exit; [exact G | exact Hcb | exact MI | rewrite unsigned_lit by lia; exact ST | lia | rewrite unsigned_lit by lia; unfold rc_lo; lia | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition LX (R : rctx) (fd P1 : Z) (path slack : list byte) (res : rd_result (ptr:=hptr)) (s : PState H hptr) (ms : machine_state) : Prop :=
    match res with
    | RdExit => at_exit2 R s ms
    | RdDone q content =>
        exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
               (m : mem) (A cap : Z) (CBs : list byte),
          ms = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 P1) (Z_to_bv 64 (Z.of_nat (length CBs))) (Z_to_bv 64 fd) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c04) fc None m (seg_rom ssegs)
          /\ mbuf R s m q A cap CBs /\ content = of_bytes CBs
    end.

  (* [comment removed for export] *)
  Lemma implM_get_bind : forall {B} (k : PState H hptr -> M (PState H hptr) B) s Q ms,
    implM ssegs (k s) s Q ms -> implM ssegs (mbind mget k) s Q ms.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. exact H0. Qed.

  (* [comment removed for export] *)
  Lemma GI_addr : forall R s CL m q A n, GI K R s CL m -> In (q, A, n) CL -> ho_addr HO (ps_heap s) q = A.
  Proof using HAL. pin_using (fun (HAL : unit) => tt). ceil_facts.
    intros R s CL m q A n (FB & HH & _) Hin.
    exact (HAL _ _ _ _ (q, A, n) HH ltac:(apply in_app_iff; left; exact Hin)).
  Qed.

  (* [comment removed for export] *)
  Definition want_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (cap len : Z),
    s5 = Z_to_bv 64 cap -> s3 = Z_to_bv 64 len -> (0 <= len < cap)%Z -> (cap <= 67108864)%Z ->
    evt ssegs (fun ms' => exists a0', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 (Z_to_bv 64 (Z.min (cap - len) 65536)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                          F (Z_to_bv 64 0x13bec) fc None m (seg_rom ssegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13bdc) fc None m (seg_rom ssegs)).
  Section Sz20.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cap len : ltac2:(SecDiet.SzSec.tyM 'want_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma want_spec__body : ltac2:(SecDiet.SzSec.bodyP 'want_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
 intros -> -> Hr Hc.
    lstep. lstep. lstep.
    destruct (Z_lt_le_dec (cap - len) 65536).
    - if_true_by (ltu_cond_true (cap - len)%Z 65536%Z ltac:(lia) ltac:(lia)).
      rewrite Z.min_l by lia. apply evt_done. eexists. reflexivity.
    - if_false_by (ltu_cond_false (cap - len)%Z 65536%Z ltac:(lia) ltac:(lia)). lstep.
      rewrite Z.min_r by lia. apply evt_done. eexists. reflexivity.
  Qed.
  End Sz20.
  Lemma want_spec : ltac:(let t := eval cbv delta [want_spec__stmt] in want_spec__stmt in exact t).
  Proof using CEILV. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cap len. ltac2:(SecDiet.SzSec.closeP 'want_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma cap_shift_zero : forall cap j, (cap = 65536 * 2 ^ j)%Z -> (0 <= j)%Z -> (cap < 67108864)%Z -> Z.shiftr cap 26 = 0%Z.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros cap j -> Hj Hc. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia.
  Qed.

  (* [comment removed for export] *)
  Definition grow_post (R : rctx) (fd P1 : Z) (path slack : list byte) (len0 : Z) : option (rd_st (ptr:=hptr)) -> PState H hptr -> machine_state -> Prop :=
    fun g s' ms' =>
      match g with
      | None => at_exit2 R s' ms'
      | Some st1 => rd_len st1 = len0 /\ exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
                           (m : mem) (A : Z) (CBs : list byte),
          ms' = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 P1) (Z_to_bv 64 (rd_len st1)) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 0x23989) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13bdc) fc None m (seg_rom ssegs)
          /\ mbuf R s' m (rd_buf st1) A (rd_cap st1) CBs /\ rd_content st1 = of_bytes CBs /\ rd_len st1 = Z.of_nat (length CBs)
          /\ (rd_len st1 < rd_cap st1)%Z
          /\ bytes_at ssegs m P1 (path ++ Z_to_bv 8 0 :: slack)
      end.

  (* [comment removed for export] *)
  Definition grow_spec__stmt : Prop := forall R fd P1 path slack (st : rd_st (ptr:=hptr)) s ms,
    LH R fd P1 path slack st s ms -> rd_len st = rd_cap st ->
    implM ssegs
      (if (MAX_INPUT <=? rd_cap st)%Z then diag DTooBig ;;; mret None
       else nb <- pmalloc HO (rd_cap st * 2) ;;
            match nb with
            | None => diag DOom ;;; mret None
            | Some nb' => pfree HO (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_len st) (rd_chunks st)))
            end) s
      (grow_post R fd P1 path slack (rd_len st)) ms.
  Section Sz22.
  Variables R fd P1 path slack st s ms : ltac2:(SecDiet.SzSec.tyM 'grow_spec__stmt "vvvvvvvv" @R).
  Lemma grow_spec__body : ltac2:(SecDiet.SzSec.bodyP 'grow_spec__stmt "vvvvvvvv").
  Proof using EFW EPR_BIG FREE HFL MALLOC SFL. pin_using (fun (EFW EPR_BIG FREE HFL MALLOC SFL : unit) => tt). ceil_facts.
    intros LHH Hfull.
    destruct LHH as (ra & gp & t0 & t1 & t2 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & A & CBs & pc
                     & -> & HPC & MB & HC & HL & PATH & HP1 & HFD).
    destruct MB as (G & MI & ST & (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) & (junk & BUF) & HLC & HCAP & (j & Hj) & AL16).
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. destruct (GI_core K _ _ _ _ G) as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
    assert (ELO : rc_lo R = (usp0 R - 8388608)%Z) by reflexivity.
    destruct st as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *. subst len.
    destruct (GI_blocks K _ _ _ _ G) as [BO _]. apply Forall_cons_iff in BO as [Bq _].
    unfold block_ok in Bq; cbn [cb_addr cb_size fst snd] in Bq. destruct Bq as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (bytes_at_bound _ _ _ _ PATH) as PB. rewrite length_app in PB; cbn [length] in PB.
    assert (Hj0 : (0 <= j)%Z). { destruct (Z_lt_le_dec j 0); [|lia]. rewrite Z.pow_neg_r in Hj by lia. lia. }
    rewrite Hfull in *.
    (* [comment removed for export] *)
    destruct HPC as [->|[_ H0]]; [|exfalso; unfold MAX_INPUT in *; lia].
    unfold implM. iprefix. lstep. if_true_by (beq_cond cap). lstep.
    destruct (Z_le_gt_dec MAX_INPUT cap) as [HBIG|HOK].
    - (* [comment removed for export] *)
      replace (MAX_INPUT <=? cap)%Z with true by (symmetry; apply Z.leb_le; exact HBIG).
      assert (Ecap : cap = 67108864%Z) by (unfold MAX_INPUT in *; lia).
      replace (Z.shiftr cap 26) with 1%Z by (rewrite Ecap; reflexivity).
      astep. do 7 lstep.
      name_spm R.
      apply evt_done. unfold diag, diag_too_big. eapply (implM_bind_u ssegs).
      { eapply EPR_BIG; [ | reflexivity | reflexivity | reflexivity ]. std_pre_tac G ST MI Hspm. }
      intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13d74)) with (Z_to_bv 64 0x13d74) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unname_spm.
      unfold implM. iprefix. lstep.
      apply evt_done. apply (implM_ret ssegs). apply evt_done.
      unfold grow_post, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2| exact ST2].
    - (* [comment removed for export] *)
      replace (MAX_INPUT <=? cap)%Z with false by (symmetry; apply Z.leb_gt; lia).
      rewrite (cap_shift_zero cap j Hj Hj0 ltac:(unfold MAX_INPUT in HOK; lia)).
      astep. lstep. lstep. lstep.
      rewrite (Z.shiftl_mul_pow2 cap 1) by lia. change (2 ^ 1)%Z with 2%Z.
      destruct (cap_double_ok cap j Hj Hj0 ltac:(unfold MAX_INPUT in HOK; lia)) as [Hj' HC2].
      name_spm R.
      apply evt_done. eapply (implM_bind_u ssegs).
      { eapply MALLOC; [ | reflexivity | unfold MAX_INPUT in HOK; lia]. std_pre_tac G ST MI Hspm. }
      intros r s' ms' PO. unfold malloc_post in PO. destruct_exs PO. destruct PO as (-> & MI1 & ST1 & AG1 & CASES). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13bb8)) with (Z_to_bv 64 0x13bb8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ AG1) in PATH; [|lia].
      apply (keeps_rw_cells_block _ _ _ _ _ _ AG1) in BUF.
      2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
      unname_spm.
      destruct r as [nb|].
      + (* [comment removed for export] *)
        destruct CASES as (A' & junk' & -> & G1 & BLK & BOK & HADDR).
        pose proof BOK as BOK'. unfold block_ok in BOK'. cbn [cb_addr cb_size fst snd] in BOK'. destruct BOK' as (C1 & C2 & C3 & C4 & C5 & C6).
        destruct (GI_blocks K _ _ _ _ G1) as [_ [AP _]]. apply Forall_cons_iff in AP as [AP _]. unfold apart in AP. cbn [cb_addr cb_size fst snd] in AP.
        cbv beta iota. unfold implM. iprefix.
        lstep. if_false_by (eqz_cond_false A' ltac:(lia)). lstep.
        lstep. if_false_by (eqz_cond_false cap ltac:(lia)). lstep. lstep. lstep. lstep.
        (* [comment removed for export] *)
        apply (rw_cells_split_CB ssegs _ _ [] _ _ [] [Z.to_nat cap; Z.to_nat cap]) in BLK; [|cbn; lia]. cbn [app mk_CB_cells] in BLK.
        apply (proj1 (rw_cells_app ssegs _ _ [_] [_])) in BLK as [BLK1 BLK2]. cbn [cells_size csize Nat.add] in BLK2.
        rewrite Nat.add_0_r, Z2Nat.id in BLK2 by lia.
        pose proof BUF as BUF'. apply (proj1 (rw_cells_app ssegs _ _ [_] [_])) in BUF' as [BUF1 _].
        assert (SRC : bytes_at ssegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A CBs).
        { destruct BUF1 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          pose proof (munch_refl [(A', A' + cap)]%Z m1) as MU2; pose proof (wmono_refl ssegs m1) as WM2 end.
        call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' A cap CBs (firstn (Z.to_nat cap) junk'));
          [reflexivity | reflexivity | reflexivity | exact SRC | lia | lia | exact BLK1 | lia | lia | lia | exact MI1 |].
        rename PC into DST. clear POST BUF1 SRC BUF.
        lazymatch type of MU2 with munch _ _ ?mb =>
          assert (G2 : GI K R s' ((nb, A', (cap * 2)%Z) :: [(q, A, cap)]) mb);
          [ eapply (GI_client_frame K HFL SFL); [exact G1 | exact MU2 | exact WM2 |];
            constructor; [| constructor]; right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia | ]
        end.
        clear MU2 WM2 G1.
        lstep. lstep.
        name_spm R.
        apply evt_done. eapply (implM_bind_u ssegs).
        { eapply FREE with (C1 := [(nb, A', (cap * 2)%Z)]) (C2 := []); [| reflexivity]. std_pre_tac G2 ST1 MI Hspm. }
        intros [] s'' ms'' PO. unfold free_post in PO. destruct_exs PO. destruct PO as (-> & MI3 & ST3 & AG3 & G3). clear MI.
        cbn [app] in AG3, G3.
        replace (ret_pc (Z_to_bv 64 0x13bdc)) with (Z_to_bv 64 0x13bdc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FR; [|lia].
        apply (keeps_bytes_at_stack _ _ _ _ _ _ AG3) in PATH; [|lia].
        apply (keeps_rw_cells_block _ _ _ _ _ _ AG3) in DST.
        2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
        apply (keeps_rw_cells_block _ _ _ _ _ _ AG3) in BLK2.
        2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
        unname_spm.
        (* [comment removed for export] *)
        apply (implM_ret ssegs). apply evt_done.
        unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks rd_content]. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split.
        { split; [exact G3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
          split.
          { exists (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk')).
            replace (length CBs) with (Z.to_nat cap) by lia.
            replace (Z.to_nat (cap * 2 - Z.of_nat (Z.to_nat cap))) with (Z.to_nat cap) by lia.
            apply rw_cells_join2; [exact DST|]. cbn [csize]. rewrite Z2Nat.id by lia. exact BLK2. }
          split; [lia|]. split; [unfold MAX_INPUT; lia|]. split; [exists (j + 1)%Z; exact Hj'| assumption]. }
        split; [exact HC|]. split; [symmetry; exact Hfull|]. split; [lia| exact PATH].
      + (* [comment removed for export] *)
        destruct CASES as [-> G1]. clear CM1 CM2. destruct (GI_core K _ _ _ _ G1) as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
        cbv beta iota. unfold implM. iprefix. astep. do 8 lstep.
        destruct MSG_OOM_ok as (RB & EM & LM).
        name_spm R.
        apply evt_done. unfold diag, diag_oom. rewrite <- EM. eapply (implM_bind_u ssegs).
        { eapply EFW; [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI1 | exact RB | lia | rewrite LM; lia] | rewrite LM; lia | rewrite LM; lia].
          std_pre_tac G1 ST1 MI1 Hspm. }
        intros [] s'' ms'' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI3 & ST3 & AG3 & G3). clear MI1.
        replace (ret_pc (Z_to_bv 64 0x13d98)) with (Z_to_bv 64 0x13d98) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        unname_spm.
        apply (implM_ret ssegs). apply evt_done.
        unfold grow_post, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G3|]. split; [exact MI3| exact ST3].
  Qed.
  End Sz22.
  Lemma grow_spec : ltac:(let t := eval cbv delta [grow_spec__stmt] in grow_spec__stmt in exact t).
  Proof using EFW EPR_BIG FREE HFL MALLOC SFL. intros R fd P1 path slack st s ms. ltac2:(SecDiet.SzSec.closeP 'grow_spec__body "vvvvvvvv"). Qed.

  Definition body_post (R : rctx) (fd P1 : Z) (path slack : list byte) : (rd_st (ptr:=hptr) + rd_result (ptr:=hptr)) -> PState H hptr -> machine_state -> Prop :=
    fun r s' ms' => match r with inl st' => LH R fd P1 path slack st' s' ms' | inr res => LX R fd P1 path slack res s' ms' end.

  (* [comment removed for export] *)
  Lemma RS_ok : rw_bytes_b ssegs 0x23989 (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) = true.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    (* [comment removed for export] *)
    apply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.RwZero.rw_bytes_b_zero ssegs Plain_segment_003 Plain_seg_bytes_003 eq_refl eq_refl eq_refl
             (Uint63.of_Z 4882) (Uint63.of_Z 131072)).
    - vm_cast_no_check (@eq_refl bool true).
    - change (Uint63.to_Z (Uint63.of_Z 131072) <= Uint63.to_Z PrimString.max_length)%Z with (131072 <= 16777211)%Z. lia.
    - intros a Ha.
      change ssegs with ([Plain_segment_000; Plain_segment_001; Plain_segment_002] ++ Plain_segment_003 :: []).
      apply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.RwZero.rz_find_segment _ _ _ 0x23989 (0x23989 + 65536)); [ repeat constructor | .. ];
        unfold Plain_segment_000, Plain_segment_001, Plain_segment_002, Plain_segment_003; cbn [seg_base seg_size]; lia.
    - unfold Plain_segment_003; cbn [seg_base]; lia.
    - lia.
    - lia.
    - unfold Plain_segment_003; cbn [seg_base]. change (Uint63.to_Z (Uint63.of_Z 4882)) with 4882%Z. lia.
    - unfold Plain_segment_003; cbn [seg_base]. change (Uint63.to_Z (Uint63.of_Z 4882)) with 4882%Z.
      change (Uint63.to_Z (Uint63.of_Z 131072)) with 131072%Z. lia.
  Qed.
  Lemma RS_chunk : forall m : mem, exists rsj, rw_cells ssegs m 0x23989 [CB (Z.to_nat 65536) rsj].
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros m. destruct (rw_cells_any ssegs m 0x23989%Z (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) RS_ok ltac:(lia) ltac:(rewrite repeat_length; lia)) as (rsj & RSL & RSC).
    rewrite repeat_length in RSC. exists rsj. exact RSC.
  Qed.

  (* [comment removed for export] *)
  Definition read_step__stmt : Prop := forall R fd P1 path slack (len0 : Z) (st1 : rd_st (ptr:=hptr)) s ms,
    grow_post R fd P1 path slack len0 (Some st1) s ms ->
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z -> (3 <= fd <= 4096)%Z -> (usp0 R <= P1)%Z ->
    (P1 + Z.of_nat (length path) + 1 <= 2^47)%Z ->
    implM ssegs
      (s0 <- mget ;;
       (let buf := sites SiteReadStage in
        let want := (rd_cap st1 - len0)%Z in
        let want' := (if READ_CHUNK <? want then READ_CHUNK else want)%Z in
        a <- msys (NRead fd buf want') (dec_read buf want') ;;
        match a with
        | RdErr _ => diag (DReadError (map bv_unsigned path)) ;;; mret (inr RdExit)
        | RdData bs => if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
                       else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (len0 + zlength bs)%Z (rd_chunks st1 ++ [of_bytes bs])))
        end)) s (body_post R fd P1 path slack) ms.
  Section Sz25.
  Variables R fd P1 path slack len0 st1 s ms : ltac2:(SecDiet.SzSec.tyM 'read_step__stmt "vvvvvvvvv" @R).
  Lemma read_step__body : ltac2:(SecDiet.SzSec.bodyP 'read_step__stmt "vvvvvvvvv").
  Proof using EPR_READ HFL SFL SITE_RS. pin_using (fun (EPR_READ HFL SFL SITE_RS : unit) => tt). ceil_facts.
    intros GP HNUL HPL HFD HP1 HP47.
    destruct GP as [<- GP].
    destruct GP as (ra & gp & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & A & CBs
                    & -> & MB & HC & HL & HLT & PATH).
    destruct MB as (G & MI & ST & (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) & (junk & BUF) & HLC & HCAP & (j & Hj) & AL16).
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. destruct (GI_core K _ _ _ _ G) as (CT & _ & _ & (CM1 & CM2 & _) & _ & _).
    unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e & T1 & T2 & T3 & T4 & T5 & T6 & Ht); subst z x.
    pose proof (GI_tls K _ _ _ _ G) as [_ TB]. pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (ELO : rc_lo R = (usp0 R - 8388608)%Z) by reflexivity.
    destruct st1 as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *. subst len.
    set (len := Z.of_nat (length CBs)) in *.
    destruct (GI_blocks K _ _ _ _ G) as [BO _]. apply Forall_cons_iff in BO as [Bq _].
    unfold block_ok in Bq; cbn [cb_addr cb_size fst snd] in Bq. destruct Bq as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (bytes_at_bound _ _ _ _ PATH) as PB. rewrite length_app in PB; cbn [length] in PB.
    pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0. fold (usp0 R) in RSP0.
    apply implM_get_bind. cbv beta zeta.
    rewrite SITE_RS.
    set (want := Z.min (cap - len) 65536).
    replace (if READ_CHUNK <? cap - len then READ_CHUNK else cap - len)%Z with want.
    2:{ subst want. unfold READ_CHUNK. destruct (Z.ltb_spec 65536 (cap - len)); lia. }
    assert (HW : (1 <= want <= 65536)%Z /\ (want <= cap - len)%Z) by (subst want; lia).
    destruct HW as [HW1 HW2].
    unfold implM. iprefix.
    eapply evt_cut; [eapply (want_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m cap len); [reflexivity | reflexivity | lia | unfold MAX_INPUT in HCAP; lia] |].
    cbv beta. intros ms' [a0' ->]. fold want.
    lstep. lstep. lstep.
    (* [comment removed for export] *)
    destruct (RS_chunk m) as (rsj & RSC).
    apply (rw_cells_split_CB ssegs _ _ [] _ _ [] [Z.to_nat want; Z.to_nat (65536 - want)]) in RSC; [|cbn; lia]. cbn [app mk_CB_cells] in RSC.
    apply (proj1 (rw_cells_app ssegs _ _ [_] [_])) in RSC as [RSw _].
    name_spm R.
    apply evt_done. eapply (implM_msys_of_enode ssegs); [reflexivity | |].
    { eapply (read_specZ _ spm _ (rc_tp R)) with (lo := rc_lo R);
        [ rewrite Hspm; exact ST | exact RSw | exact T2 | exact MI | reflexivity | reflexivity | reflexivity
        | lia | lia | lia | lia | rewrite Hspm, ELO; lia | rewrite Hspm; unfold utp in *; lia | rewrite Hspm; lia | unfold utp in *; lia | unfold utp in *; lia ]. }
    intros a ms' PO. unfold read_post in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI' & ST' & CASE). 
    replace (ret_pc (Z_to_bv 64 0x13bf8)) with (Z_to_bv 64 0x13bf8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    change (bv_unsigned (rc_tp R)) with (utp R) in *. rewrite Z2Nat.id in MU by lia.
    clear RSw.
    lazymatch type of MU with munch _ ?ma ?mb => transport_after_call ssegs ma mb MU WM end.
    clear MI. rename MI' into MI.
    apply (munch_weaken _ [(utp R - 164, utp R - 160); (bv_unsigned spm - 16, bv_unsigned spm); (0x23989, 0x23989 + want)]%Z) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
    (* [comment removed for export] *)
    assert (G' : forall ev, rw_cells ssegs ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end) (utp R + -164) [C4 ev] ->
                 GI K R s [(q, A, cap)] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
    { intros ev HEV. eapply (GI_client_frame_errno_rs K HFL SFL); [exact G | exact MU | exact WM | | exact HEV].
      constructor; [left; left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia|].
      constructor; [right; unfold rs_iv; cbn [fst snd]; lia| constructor]. }
    clear MU WM G.
    destruct a as [err|bs].
    - (* [comment removed for export] *)
      destruct CASE as (_ & ERR & Herr). specialize (G' _ ERR).
      clear CM1 CM2. destruct (GI_core K _ _ _ _ G') as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
      unfold read_ret. unname_spm.
      unfold implM. iprefix. lstep. if_true_by ltz_cond_m1. do 8 lstep.
      name_spm R.
      apply evt_done. unfold diag, diag_read_error. eapply (implM_bind_u ssegs).
      { eapply EPR_READ; [ | reflexivity | reflexivity | reflexivity | exact PATH | exact HNUL | exact (proj1 HPL) | exact (proj2 HPL) | intros a Ha; left; lia | exact HP47 ].
        std_pre_tac G' ST' MI Hspm. }
      intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13d74)) with (Z_to_bv 64 0x13d74) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unname_spm.
      unfold implM. iprefix. lstep.
      apply evt_done. apply (implM_ret ssegs). apply evt_done.
      unfold body_post, LX, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2| exact ST2].
    - (* [comment removed for export] *)
      destruct CASE as (RSr & ERR & Hbs). specialize (G' _ ERR).
      unfold read_ret. unname_spm.
      pose proof (Nat2Z.is_nonneg (length bs)) as LB0.
      unfold implM. iprefix. lstep. if_false_by (ltz_cond_false (Z.of_nat (length bs)) ltac:(lia)). lstep.
      destruct bs as [|b bs'].
      + (* [comment removed for export] *)
        lstep. if_false_by (eq_cond 0).
        apply evt_done. cbn [length Nat.eqb]. apply (implM_ret ssegs). apply evt_done.
        unfold body_post, LX. cbn [rd_content rd_chunks].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|]. split; [| exact HC].
        split; [exact G'|]. split; [exact MI|]. split; [exact ST'|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
        split; [exists junk; exact BUF|].
        split; [lia|]. split; [exact HCAP|]. split; [exists j; exact Hj| assumption].
      + (* [comment removed for export] *)
        set (n := Z.of_nat (length (b :: bs'))) in *.
        assert (Hn : (1 <= n <= want)%Z) by (subst n; cbn [length] in *; lia).
        lstep. if_true_by (nez_cond n ltac:(lia)).
        lstep. lstep. lstep. lstep.
        (* [comment removed for export] *)
        apply (proj1 (rw_cells_app ssegs _ _ [_] [_])) in RSr as [RSd _].
        assert (SRC : bytes_at ssegs ltac:(lazymatch type of RSd with rw_cells _ ?mm _ _ => exact mm end) 0x23989 (b :: bs')).
        { destruct RSd as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
        clear RSd.
        pose proof BUF as BUF0. apply (proj1 (rw_cells_app ssegs _ _ [_] [_])) in BUF as [BUF1 BUF2]. cbn [cells_size csize Nat.add] in BUF2.
        rewrite Nat.add_0_r in BUF2. fold len in BUF2.
        apply (rw_cells_split_CB ssegs _ _ [] _ _ [] [Z.to_nat n; Z.to_nat (cap - len - n)]) in BUF2; [|cbn; lia]. cbn [app mk_CB_cells] in BUF2.
        apply (proj1 (rw_cells_app ssegs _ _ [_] [_])) in BUF2 as [BUFw BUF3]. cbn [cells_size csize Nat.add] in BUF3.
        rewrite Nat.add_0_r, Z2Nat.id in BUF3 by lia.
        clear BUF0.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          pose proof (munch_refl [(A + len, A + len + n)]%Z m1) as MU2; pose proof (wmono_refl ssegs m1) as WM2 end.
        call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A + len)%Z 0x23989%Z n (b :: bs') (firstn (Z.to_nat n) junk));
          [reflexivity | reflexivity | reflexivity | exact SRC | subst n; lia | lia | exact BUFw | lia | lia | lia | exact MI |].
        rename PC into DST. clear POST. try clear SRC. try clear MI. rename MI0 into MI.
        lazymatch type of MU2 with munch _ _ ?mb =>
          assert (G2 : GI K R s [(q, A, cap)] mb);
          [ eapply (GI_client_frame K HFL SFL); [exact G' | exact MU2 | exact WM2 |];
            constructor; [| constructor]; right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia | ]
        end.
        clear MU2 WM2 G'.
        (* [comment removed for export] *)
        lstep. lstep.
        (* [comment removed for export] *)
        assert (BUF : exists junk', rw_cells ssegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A
                        [CB (length (CBs ++ b :: bs')) (CBs ++ b :: bs'); CB (Z.to_nat (cap - (len + n))) junk']).
        { eexists.
          assert (J : rw_cells ssegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A
                        ([CB (length CBs) CBs] ++ [CB (Z.to_nat n) (b :: bs')] ++ [CB (Z.to_nat (cap - len - n)) (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk))])).
          { apply (proj2 (rw_cells_app ssegs _ _ _ _)). split; [exact BUF1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. fold len.
            apply (proj2 (rw_cells_app ssegs _ _ [_] [_])). split; [exact DST|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact BUF3. }
          cbn [app] in J.
          apply (rw_cells_merge ssegs _ _ [] [CB (length CBs) CBs; CB (Z.to_nat n) (b :: bs')] [_]) in J. cbn [cells_size csize cells_bytes cbytes app] in J.
          replace (length CBs + (Z.to_nat n + 0))%nat with (length (CBs ++ b :: bs')) in J by (rewrite length_app; subst n; lia).
          rewrite ?app_nil_r in J.
          replace (Z.to_nat (cap - len - n)) with (Z.to_nat (cap - (len + n))) in J by lia. exact J. }
        clear BUF1 DST BUF3. destruct BUF as [junk' BUF].
        apply evt_done. replace (length (b :: bs') =? 0)%nat with false by reflexivity. apply (implM_ret ssegs). apply evt_done.
        unfold body_post, LH. cbn [rd_buf rd_cap rd_len rd_chunks rd_content].
        replace (n + len)%Z with (len + zlength (b :: bs'))%Z by (unfold zlength; subst n; lia).
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [left; reflexivity|].
        split.
        { split; [exact G2|]. split; [exact MI|]. split; [exact ST'|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
          split. { exists junk'. replace (cap - Z.of_nat (length (CBs ++ b :: bs')))%Z with (cap - (len + n))%Z by (rewrite length_app; subst n len; lia). exact BUF. }
          split; [rewrite length_app; subst n len; lia|]. split; [exact HCAP|]. split; [exists j; exact Hj| assumption]. }
        split. { unfold rd_content in *. cbn [rd_chunks] in HC |- *. rewrite concat_app. cbn [concat]. rewrite app_nil_r, HC. unfold of_bytes. rewrite map_app. reflexivity. }
        split; [unfold zlength; rewrite length_app; subst len; lia|].
        split; [exact PATH|]. split; [exact HP1| exact HFD].
  Qed.
  End Sz25.
  Lemma read_step : ltac:(let t := eval cbv delta [read_step__stmt] in read_step__stmt in exact t).
  Proof using EPR_READ HFL SFL SITE_RS. intros R fd P1 path slack len0 st1 s ms. ltac2:(SecDiet.SzSec.closeP 'read_step__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition body_spec__stmt : Prop := forall R fd P1 path slack (st : rd_st (ptr:=hptr)) s ms,
    LH R fd P1 path slack st s ms -> ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
    (P1 + Z.of_nat (length path) + 1 <= 2^47)%Z ->
    implM ssegs (read_loop_body diag (pmalloc HO) (pfree HO) (sites SiteReadStage) fd (map bv_unsigned path) st) s (body_post R fd P1 path slack) ms.
  Section Sz26.
  Variables R fd P1 path slack st s ms : ltac2:(SecDiet.SzSec.tyM 'body_spec__stmt "vvvvvvvv" @R).
  Lemma body_spec__body : ltac2:(SecDiet.SzSec.bodyP 'body_spec__stmt "vvvvvvvv").
  Proof using EFW EPR_BIG EPR_READ FREE HFL MALLOC SFL SITE_RS. pin_using (fun (EFW EPR_BIG EPR_READ FREE HFL MALLOC SFL SITE_RS : unit) => tt). ceil_facts.
    intros LHH HNUL HPL HP47.
    pose proof LHH as LHH'.
    destruct LHH' as (ra & gp & t0 & t1 & t2 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & A & CBs & pc
                       & Ems & HPC & MB & HC & HL & PATH & HP1 & HFD). subst ms.
    pose proof MB as MB'. destruct MB' as (G & MI & ST & FRm & BUF & HLC & HCAP & HJ & AL16).
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__.
    unfold read_loop_body. cbv zeta.
    eapply (implM_bind ssegs _ _ s (grow_post R fd P1 path slack (rd_len st))).
    - destruct (Z.eqb_spec (rd_len st) (rd_cap st)) as [E|NE].
      + apply grow_spec; [exact LHH | exact E].
      + apply (implM_ret ssegs).
        destruct st as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *.
        (* [comment removed for export] *)
        destruct HPC as [->|[-> H0]].
        * lstep. if_false_by (bne_cond_false len cap ltac:(unfold MAX_INPUT in *; lia) ltac:(unfold MAX_INPUT in *; lia) NE). lstep. lstep.
          apply evt_done. unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks]. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|]. split; [exact MB|]. split; [exact HC|]. split; [exact HL|]. split; [lia| exact PATH].
        * lstep. if_true_by (neq_cond 0 cap ltac:(lia) ltac:(unfold MAX_INPUT in *; lia) ltac:(unfold MAX_INPUT in *; lia)). lstep. lstep.
          apply evt_done. unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks]. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|]. split; [exact MB|]. split; [exact HC|]. split; [exact HL|]. split; [lia| exact PATH].
    - intros g s' ms' GP. destruct g as [st1|].
      + cbv beta iota. eapply read_step; [exact GP | exact HNUL | exact HPL | exact HFD | exact HP1 | exact HP47].
      + cbv beta iota. apply (implM_ret ssegs). apply evt_done. exact GP.
  Qed.
  End Sz26.
  Lemma body_spec : ltac:(let t := eval cbv delta [body_spec__stmt] in body_spec__stmt in exact t).
  Proof using EFW EPR_BIG EPR_READ FREE HFL MALLOC SFL SITE_RS. intros R fd P1 path slack st s ms. ltac2:(SecDiet.SzSec.closeP 'body_spec__body "vvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma loop_spec : forall fuel R fd P1 path slack (st : rd_st (ptr:=hptr)) s ms,
    LH R fd P1 path slack st s ms -> ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
    (P1 + Z.of_nat (length path) + 1 <= 2^47)%Z ->
    implM ssegs (mloop fuel (read_loop_body diag (pmalloc HO) (pfree HO) (sites SiteReadStage) fd (map bv_unsigned path)) st) s
      (LX R fd P1 path slack) ms.
  Proof using EFW EPR_BIG EPR_READ FREE HFL MALLOC SFL SITE_RS. pin_using (fun (EFW EPR_BIG EPR_READ FREE HFL MALLOC SFL SITE_RS : unit) => tt). ceil_facts.
    induction fuel as [|fuel IH]; intros R fd P1 path slack st s ms LHH HNUL HPL HP47.
    - cbn [mloop]. apply implM_unr.
    - apply implM_loop_S. eapply (implM_mono ssegs); [eapply body_spec; [exact LHH | exact HNUL | exact HPL | exact HP47]|].
      cbv beta. intros [st'|res] s' ms' BP; unfold body_post in BP.
      + apply IH; [exact BP | exact HNUL | exact HPL | exact HP47].
      + apply evt_done. exact BP.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma to_bytes_of_bytes : forall l : list byte, to_bytes (map bv_unsigned l) = l.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros l. unfold to_bytes. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
    apply definitions.Z_to_bv_bv_unsigned.
  Qed.

  Lemma rw_cells_nil_CB : forall m A cs, rw_cells ssegs m A cs -> rw_cells ssegs m A (CB 0 [] :: cs).
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros m A cs [[Hwf HB] HW]. split; [split|].
    - split; [reflexivity| exact Hwf].
    - cbn [cells_bytes cbytes app]. exact HB.
    - cbn [cells_size csize Nat.add]. exact HW.
  Qed.

  (* [comment removed for export] *)
  Definition P2 (R : rctx) (s : PState H hptr) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      ms = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 2) s1 a0 (Z_to_bv 64 (usp0 R + 8)) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x13b40) fc None m (seg_rom ssegs)
      /\ GI K R s [] m /\ mem_inv ssegs m /\ stk ssegs m (rc_lo R) (usp0 R + -128) /\ mframe R m /\ (usp0 R mod 16 = 0)%Z
      /\ (usp0 R + Z.of_nat (length (build_stack_bytes Plain.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R))) <= 2^47)%Z.

  (* [comment removed for export] *)
  Definition RAX (R : rctx) (res : rd_result (ptr:=hptr)) (s : PState H hptr) (ms : machine_state) : Prop :=
    match res with
    | RdExit => at_exit2 R s ms
    | RdDone q content =>
        exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
               (m : mem) (A cap : Z) (CBs : list byte),
          ms = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (Z.of_nat (length CBs))) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c0c) fc None m (seg_rom ssegs)
          /\ mbuf R s m q A cap CBs /\ content = of_bytes CBs
    end.

  Definition read_all_spec__stmt : Prop := forall R s ms argv1,
    P2 R s ms -> nth_error (rc_argv R) 1 = Some argv1 -> valid_argv (rc_argv R) ->
    implM ssegs (read_all diag (pmalloc HO) (pfree HO) (sites SiteReadStage) (map bv_unsigned argv1)) s (RAX R) ms.
  Section Sz30.
  Variables R s ms argv1 : ltac2:(SecDiet.SzSec.tyM 'read_all_spec__stmt "vvvv" @R).
  Lemma read_all_spec__body : ltac2:(SecDiet.SzSec.bodyP 'read_all_spec__stmt "vvvv").
  Proof using EFW EPR_BIG EPR_OPEN EPR_READ FREE HFL MALLOC SFL SITE_RS. pin_using (fun (EFW EPR_BIG EPR_OPEN EPR_READ FREE HFL MALLOC SFL SITE_RS : unit) => tt). ceil_facts.
    intros (ra & gp & t0 & t1 & t2 & s1 & a0 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m
                           & -> & G & MI & ST & (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) & AL16 & STKTOP) HA1 VA.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof VA as VA'. destruct VA' as (VA1 & VA2 & VA3 & VA4 & VA5).
    destruct (GI_core K _ _ _ _ G) as (CT & _ & CLI & (CM1 & CM2 & _) & _ & CS). unfold CORE_STK in CS.
    unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e & T1 & T2 & T3 & T4 & T5 & T6 & Ht); subst z x. destruct CLI as (L1 & L2 & L3 & L4 & L5).
    pose proof (GI_tls K _ _ _ _ G) as [_ TB]. pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (ELO : rc_lo R = (usp0 R - 8388608)%Z) by reflexivity.
    pose proof (raw_len_nonneg Plain.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R)) as RN.
    pose proof (build_stack_bytes_length Plain.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R)) as BL.
    pose proof (bytes_at_bound _ _ _ _ CS) as CSB. fold (usp0 R) in BL, CSB.
    destruct (stack_argv_string_slack ssegs Plain.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R) m CS
                ltac:(fold (usp0 R); clear -AL16; Z.div_mod_to_equations; lia) 1 argv1 HA1) as (P1 & slack1 & HP1 & P1lo & P1hi & STRS & SLK1 & END1).
    destruct (proj1 (bytes_at_app ssegs m P1 (argv1 ++ [Z_to_bv 8 0]) slack1) ltac:(rewrite <- app_assoc; exact STRS)) as [STR1 _].
    pose proof (stack_argv_ptr_read ssegs Plain.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R) m CS 1 _ HP1) as RD1.
    replace (bv_unsigned (rc_sp0 R) + 8 + 8 * Z.of_nat 1)%Z with (usp0 R + 16)%Z in RD1 by (unfold usp0; lia).
    unfold InitMem.str_base, InitMem.env_base, InitMem.str_base in P1lo, P1hi. fold (usp0 R) in P1lo, P1hi.
    assert (HNUL : ~ In (Z_to_bv 8 0) argv1). { apply (proj1 (Forall_forall _ _) VA4). eapply nth_error_In. exact HA1. }
    (* [comment removed for export] *)
    assert (HSLD : Namei.path_has_slash argv1 = false /\ Fs.path_eqb argv1 Namei.dotdot_path = false).
    { clear - HA1 VA5. destruct (rc_argv R) as [|x tlv]; [discriminate|]. cbn [tl] in VA5.
      change (nth_error tlv 0 = Some argv1) in HA1.
      exact (proj1 (Forall_forall _ _) VA5 _ (nth_error_In _ _ HA1)). }
    assert (HPL : (Z.of_nat (length argv1) < 2^24 /\ (- (P1 + Z.of_nat (length argv1) + 1)) mod 8 <= Z.of_nat (length slack1))%Z).
    { split; [|exact SLK1]. pose proof (proj1 (Forall_forall _ _) VA3 _ (nth_error_In _ _ HA1)). cbn beta in *. lia. }
    assert (HP47 : (P1 + Z.of_nat (length argv1) + 1 <= 2^47)%Z) by (unfold usp0 in *; lia).
    pose proof (bytes_at_bound _ _ _ _ STRS) as PBS. rewrite length_app in PBS; cbn [length] in PBS.
    pose proof (bytes_at_bound _ _ _ _ STR1) as PB. rewrite length_app in PB; cbn [length] in PB.
    unfold read_all. rewrite to_bytes_of_bytes.
    unfold implM. iprefix. lstep. lstep. lstep. lstep.
    name_spm R.
    apply evt_done. eapply (implM_msys_of_enode ssegs); [reflexivity | |].
    { eapply (open_spec _ spm _ (rc_tp R)) with (lo := rc_lo R);
        [ rewrite Hspm; exact ST | rewrite unsigned_lit by lia; exact STR1 | exact T2 | exact L2 | exact L3 | exact MI | reflexivity | exact HNUL
        | exact (proj1 HSLD) | exact (proj2 HSLD)
        | rewrite Hspm, ELO; lia | rewrite Hspm; unfold utp in *; lia | rewrite Hspm, unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; unfold utp in *; lia | rewrite Hspm; unfold ssp_guard; lia
        | unfold ssp_guard, utp in *; lia | unfold got_ssp, utp in *; lia | unfold utp in *; lia ]. }
    intros r ms' PO. unfold open_post in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI' & ST' & ERR & STR & GOT & GUARD & Hr).
    replace (ret_pc (Z_to_bv 64 0x13b50)) with (Z_to_bv 64 0x13b50) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    change (bv_unsigned (rc_tp R)) with (utp R) in *. rewrite unsigned_lit in STR by lia.
    lazymatch type of MU with munch _ ?ma ?mb => transport_after_call ssegs ma mb MU WM end.
    clear MI. rename MI' into MI.
    apply (munch_weaken _ [(utp R - 164, utp R - 160); (bv_unsigned spm - 112, bv_unsigned spm)]%Z) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
    assert (G' : GI K R s [] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
    { eapply (GI_client_frame_errno K HFL SFL); [exact G | exact MU | exact WM | | exact ERR].
      constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia| constructor]. }
    clear MU WM G CM1 CM2. destruct (GI_core K _ _ _ _ G') as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
    destruct r as [err|fd].
    - (* [comment removed for export] *)
      unfold open_ret. unname_spm.
      cbv beta iota. unfold implM. iprefix. lstep. if_true_by ltz_cond_m1. do 9 lstep.
      name_spm R.
      apply evt_done. unfold diag, diag_cannot_open. eapply (implM_bind_u ssegs).
      { eapply EPR_OPEN; [ | reflexivity | reflexivity | reflexivity | exact STRS | exact HNUL | exact (proj1 HPL) | exact (proj2 HPL) | intros a Ha; left; lia | exact HP47 ].
        std_pre_tac G' ST' MI Hspm. }
      intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13d74)) with (Z_to_bv 64 0x13d74) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unname_spm.
      unfold implM. iprefix. lstep.
      apply evt_done. apply (implM_ret ssegs). apply evt_done.
      unfold RAX, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2| exact ST2].
    - (* [comment removed for export] *)
      unfold open_ret. unname_spm.
      cbv beta iota. unfold implM. iprefix. lstep. if_false_by (ltz_cond_false fd ltac:(lia)). do 4 lstep.
      name_spm R.
      apply evt_done. eapply (implM_bind_u ssegs).
      { eapply MALLOC; [ | reflexivity | lia]. std_pre_tac G' ST' MI Hspm. }
      intros r s' ms' PO. unfold malloc_post in PO. destruct_exs PO. destruct PO as (-> & MI1 & ST1 & AG1 & CASES). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13b64)) with (Z_to_bv 64 0x13b64) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ AG1) in STR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ AG1) in STRS; [|lia].
      unname_spm.
      destruct r as [q|].
      + destruct CASES as (A & junk & -> & G1 & BLK & BOK & HADDR).
        pose proof BOK as BOK'. unfold block_ok in BOK'. cbn [cb_addr cb_size fst snd] in BOK'. destruct BOK' as (B1 & B2 & B3 & B4 & B5 & B6).
        (* [comment removed for export] *)
        cbv beta iota. unfold implM. iprefix. lstep. if_false_by (eqz_cond_false A ltac:(lia)). lstep. lstep. lstep. lstep.
        apply evt_done. eapply (implM_bind_u ssegs _ _ s' (LX R fd P1 argv1 slack1)).
        { eapply loop_spec; [| exact HNUL | exact HPL | exact HP47].
          unfold LH. cbn [rd_buf rd_cap rd_len rd_chunks rd_content concat].
          repeat (lazymatch goal with |- @ex (list byte) _ => exists (@nil byte) | |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|].
          split; [right; split; reflexivity|].
          split.
          { split; [exact G1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
            split; [exists junk; apply rw_cells_nil_CB; exact BLK|].
            cbn [length Z.of_nat]. split; [lia|]. split; [unfold MAX_INPUT; lia|]. split; [exists 0%Z; reflexivity| assumption]. }
          split; [reflexivity|]. split; [reflexivity|].
          split; [exact STRS|]. split; [lia| lia]. }
        intros res s'' ms'' LXH. destruct res as [|q' content].
        * cbv beta iota. apply (implM_ret ssegs). apply evt_done. exact LXH.
        * destruct LXH as (ra' & gp' & y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & y3 & y4 & y5 & y6 & F' & fc' & m'' & A' & cap' & CBs'
                            & -> & MB & HC).
          destruct MB as (G2 & MI2 & ST2 & (h0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & FR2) & (junk2 & BUF2) & HLC2 & HCAP2 & HJ2 & AL16b).
          clear CM1 CM2. destruct (GI_core K _ _ _ _ G2) as ((t' & e' & _ & ERR2 & _) & _ & _ & (CM1 & CM2 & _) & _ & _).
          destruct (GI_blocks K _ _ _ _ G2) as [BO2 _]. apply Forall_cons_iff in BO2 as [Bq2 _].
          unfold block_ok in Bq2; cbn [cb_addr cb_size fst snd] in Bq2. destruct Bq2 as (D1 & D2 & D3 & D4 & D5 & D6).
          cbv beta iota. unfold implM. iprefix. lstep. lstep.
          name_spm R.
          apply evt_done. eapply (implM_msys_of_enode ssegs); [reflexivity | |].
          { eapply (close_spec _ spm _ (rc_tp R)) with (lo := rc_lo R);
              [ rewrite Hspm; exact ST2 | exact ERR2 | exact MI2 | reflexivity | lia | rewrite Hspm, ELO; lia | rewrite Hspm; unfold utp in *; lia | unfold utp in *; lia ]. }
          intros r ms' PO. unfold close_post in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI3 & ST3 & ERR3).
          replace (ret_pc (Z_to_bv 64 0x13c0c)) with (Z_to_bv 64 0x13c0c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
          change (bv_unsigned (rc_tp R)) with (utp R) in *.
          lazymatch type of MU with munch _ ?ma ?mb => transport_after_call ssegs ma mb MU WM end.
          apply (munch_weaken _ [(utp R - 164, utp R - 160); (bv_unsigned spm - 32, bv_unsigned spm)]%Z) in MU.
          2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
          assert (G3 : GI K R s'' [(q', A', cap')] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
          { eapply (GI_client_frame_errno K HFL SFL); [exact G2 | exact MU | exact WM | | exact ERR3].
            constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia| constructor]. }
          unname_spm.
          apply (implM_ret ssegs). apply evt_done.
          unfold RAX. repeat (lazymatch goal with |- ex _ => eexists end).
          split; [reflexivity|]. split; [| exact HC].
          split; [exact G3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exists h0, g1, g2, g3, g4, g5, g6, g7, g8; exact FR2|].
          split; [exists junk2; exact BUF2|]. split; [exact HLC2|]. split; [exact HCAP2|]. split; [exact HJ2| exact AL16b].
      + (* [comment removed for export] *)
        destruct CASES as [-> G1]. clear CM1 CM2. destruct (GI_core K _ _ _ _ G1) as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
        cbv beta iota. unfold implM. iprefix. astep. do 9 lstep.
        destruct MSG_OOM_ok as (RB & EM & LM).
        name_spm R.
        apply evt_done. unfold diag, diag_oom. rewrite <- EM. eapply (implM_bind_u ssegs).
        { eapply EFW; [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI1 | exact RB | lia | rewrite LM; lia] | rewrite LM; lia | rewrite LM; lia].
          std_pre_tac G1 ST1 MI1 Hspm. }
        intros [] s'' ms'' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI3 & ST3 & AG3 & G3). clear MI1.
        replace (ret_pc (Z_to_bv 64 0x13d98)) with (Z_to_bv 64 0x13d98) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        unname_spm.
        apply (implM_ret ssegs). apply evt_done.
        unfold RAX, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G3|]. split; [exact MI3| exact ST3].
  Qed.
  End Sz30.
  Lemma read_all_spec : ltac:(let t := eval cbv delta [read_all_spec__stmt] in read_all_spec__stmt in exact t).
  Proof using EFW EPR_BIG EPR_OPEN EPR_READ FREE HFL MALLOC SFL SITE_RS. intros R s ms argv1. ltac2:(SecDiet.SzSec.closeP 'read_all_spec__body "vvvv"). Qed.
End Main.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.CallKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.ImgAny.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_target_run.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implM_bind_u : forall segs {St A B} (m : @M St A) (f : A -> @M St B) s Q1 Q ms,
  implM segs m s Q1 ms -> (forall a s' ms', Q1 a s' ms' -> implM segs (f a) s' Q ms') ->
  impl segs (at_node segs) (npeek segs) (mbind m f s) (epost (fun p => Q (fst p) (snd p))) ms.
Proof. intros segs St A B m f s Q1 Q ms H1 H2. exact (implM_bind segs m f s Q1 Q ms H1 H2). Qed.

Section WithCeil.
Context {CEILV : CEIL}.
Definition img_lit (A : Z) (n : nat) : list byte := match image_bytes usegs A n with Some bs => bs | None => [] end.
Definition MSG_OOM_bytes : list byte := img_lit 0x104f4 19.
Definition MSG_SHORT_HDR_bytes : list byte := img_lit 0x10e00 31.
Definition MSG_CFG_OVERRUN_bytes : list byte := img_lit 0x106e5 31.

Lemma MSG_OOM_ok : ro_bytes_b usegs 0x104f4 MSG_OOM_bytes = true /\ map bv_unsigned MSG_OOM_bytes = List.concat pieces_oom /\ length MSG_OOM_bytes = 19%nat.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. vm_compute. repeat split; reflexivity. Qed.
Lemma MSG_SHORT_HDR_ok : ro_bytes_b usegs 0x10e00 MSG_SHORT_HDR_bytes = true /\ map bv_unsigned MSG_SHORT_HDR_bytes = List.concat pieces_short_hdr /\ length MSG_SHORT_HDR_bytes = 31%nat.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. vm_compute. repeat split; reflexivity. Qed.
Lemma MSG_CFG_OVERRUN_ok : ro_bytes_b usegs 0x106e5 MSG_CFG_OVERRUN_bytes = true /\ map bv_unsigned MSG_CFG_OVERRUN_bytes = List.concat pieces_cfg_overrun /\ length MSG_CFG_OVERRUN_bytes = 31%nat.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. vm_compute. repeat split; reflexivity. Qed.

Lemma lit_bytes_at : forall m A bs, mem_inv usegs m -> ro_bytes_b usegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z -> bytes_at usegs m A bs.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros m A bs MI RB HA HB. apply ro_bytes_at; [exact MI | exact HA | exact HB |]. apply ro_bytes_b_sound. exact RB. Qed.

Lemma cap_double_ok : forall cap j, (cap = 65536 * 2 ^ j)%Z -> (0 <= j)%Z -> (cap < 67108864)%Z ->
  (cap * 2 = 65536 * 2 ^ (j + 1))%Z /\ (cap * 2 <= 67108864)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros cap j -> Hj Hc. split. { rewrite Z.pow_add_r by lia. change (2 ^ 1)%Z with 2%Z. lia. }
  assert (Hj10 : (2 ^ j < 2 ^ 10)%Z) by (change (2 ^ 10)%Z with 1024%Z; lia).
  apply Z.pow_lt_mono_r_iff in Hj10; [|lia|lia].
  assert (2 ^ (j + 1) <= 2 ^ 10)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 10)%Z with 1024%Z in H. rewrite Z.pow_add_r in H by lia. change (2 ^ 1)%Z with 2%Z in H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma read_specZ : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd B count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m B [CB (Z.to_nat count) junk] ->
  rw_cells usegs m (bv_unsigned tp + -164) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 2^24)%Z -> (0 <= B)%Z -> (B + count <= 2^47)%Z ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned tp + -164 + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned tp + -164)%Z ->
  (B + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= B)%Z ->
  (B + count <= bv_unsigned tp + -164 \/ bv_unsigned tp + -164 + 4 <= B)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (npeek usegs) (enode (NRead fd B count) (dec_read B count))
       (epost (read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x21ca8) fc None m (seg_rom usegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros until lo. intros ST DST ERR MI -> EA1 -> FD CNT B0 UB LO SEP1 SEP2 SEP3 TP.
  assert (EB : bv_unsigned a1 = B). { subst a1. apply unsigned_lit. lia. }
  rewrite <- EB. rewrite <- EB in DST, SEP2, SEP3, UB.
  eapply read_spec; try eas_among ST DST ERR MI FD CNT UB LO SEP1 SEP2 SEP3 TP; try reflexivity; lia.
Qed.

Lemma ltu_cond_true : forall x y, (0 <= x < y)%Z -> (y < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_lt. lia. Qed.
Lemma ltu_cond_false : forall x y, (0 <= y <= x)%Z -> (x < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltz_cond_false : forall x, (0 <= x < 2^63)%Z -> bv_lts (Z_to_bv 64 x) z64 = false.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. rewrite bv_lts_zero_r, unsigned_lit by lia. apply Z.leb_gt. lia. Qed.
Lemma ltz_cond_m1 : bv_lts (Z_to_bv 64 (-1)) z64 = true.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. reflexivity. Qed.

Section Main.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites_of : Z -> stack_site -> Z) (sites : stack_site -> Z).
  (* [comment removed for export] *)
  Variable SEF : Z.
  Hypothesis SEF_range : (0 <= SEF <= 0x10000)%Z.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOC : malloc_stmt HO K.
  Hypothesis FREE : free_stmt HO K.
  Hypothesis FUZZ : fuzz_one_stmt HO K sites_of sites.
  Hypothesis VPR : vprintf_d_stmt K.
  Hypothesis EPR_USAGE : eprintf_s_stmt47 K FMT_USAGE pieces_usage.   (* [comment removed for export] *)
  Hypothesis EPR_OPEN : eprintf_s_stmt47 K FMT_CANNOT_OPEN pieces_cannot_open.
  Hypothesis EPR_READ : eprintf_s_stmt47 K FMT_READ_ERROR pieces_read_error.
  Hypothesis EPR_BIG : eprintf_i_stmt K FMT_TOO_BIG 0x4000000 pieces_too_big.
  Hypothesis EFW : efwrite_stmt K.
  (* [comment removed for export] *)
  Hypothesis SITE_RS : sites SiteReadStage = 0x24149%Z.

  (* [comment removed for export] *)
  Ltac name_spm R :=
    remember (Z_to_bv 64 (usp0 R + -128)) as spm eqn:Espm;
    assert (Hspm : bv_unsigned spm = (usp0 R + -128)%Z) by (rewrite Espm; apply unsigned_lit; lia).
  Ltac unname_spm := match goal with H : bv_unsigned ?s = (usp0 _ + -128)%Z |- _ => is_var s; rewrite H in *; subst s; clear H end.

  (* [comment removed for export] *)
  Ltac aln16 := match goal with H : (usp0 ?R mod 16 = 0)%Z |- _ => generalize H; clear; intros; Z.div_mod_to_equations; lia end.

  (* [comment removed for export] *)
  Ltac std_pre_tac G ST MI Hspm :=
    split; [exact G|]; split; [rewrite Hspm; exact ST|]; split; [unfold rc_lo; lia|];
    split; [unfold TARGET_RUN_STACK; unfold rc_lo, STDIO_STACK, MALLOC_STACK, FREE_STACK, FUZZ_STACK; lia|];
    split; [unfold rc_spmain; lia|]; split; [exact MI|]; split; [reflexivity| rewrite Hspm; aln16].

  (* [comment removed for export] *)
  Definition GI_at_exit__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PState H hptr) (CL : list cblock) (lo code : Z),
    GI K R s CL m -> rc_cb R = false ->  (* [comment removed for export] *)
    mem_inv usegs m -> stk usegs m lo (bv_unsigned sp) -> (rc_lo R <= lo)%Z -> (lo <= bv_unsigned sp - 80 - SEF)%Z ->
    (bv_unsigned sp <= usp0 R)%Z ->      (* [comment removed for export] *)
    tp = rc_tp R -> a0 = Z_to_bv 64 code ->
    at_exit (St:=PState H hptr) (SXGI K) SEF code s
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x18c1c) fc None m (seg_rom usegs)).
  Section Sz11.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo code : ltac2:(SecDiet.SzSec.tyM 'GI_at_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma GI_at_exit__body : ltac2:(SecDiet.SzSec.bodyP 'GI_at_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt. ceil_facts.
    intros G Hcb MI ST LOLO LOSP SPUP -> ->.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof (GI_sp47 K _ _ _ _ G) as SP47. unfold rc_lo in LOLO.
    destruct G as (FB & HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & _).
    unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e & T1 & T2 & T3 & T4 & T5 & T6 & Ht); subst z x.
    destruct CLI as (L1 & L2 & L3 & L4 & L5).
    destruct CE as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    (* [comment removed for export] *)
    destruct E2 as (reg & pad & f0 & g0 & j1 & j2 & X1 & X2 & X3 & X4). rewrite Hcb in X1. cbn [bool8] in X1.
    apply (proj1 (rw_cells_app _ m _ [_; _] [_])) in X1 as [_ XF]. (sl_lit_sizes_in XF; cbn [cells_size csize Nat.add] in XF).
    match type of XF with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in XF end.
    unfold at_exit. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact ST|]. split; [exact T1|]. split; [exact E1|]. split; [exact L1|].
    split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact XF|].
    split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|]. split; [exact E7|].
    split.
    { unfold SXGI. exists R, CL, FB. split; [reflexivity|]. split; [exact HH|]. split; [exact HS|]. split; [exact HA|].
      split; [exists t, e; repeat (split; [eas_among T1 T2 T3 T4 T5 T6|]); exact Ht|]. split; [exact PT|].
      split; [split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact L5]|]. split; [exact CM|].
      split; [exact Etls|]. split; [exact TB| exact BOK]. }
    split; [exact MI|]. split; [reflexivity|]. split; [exact Ht|]. split; [lia|]. split; [lia|].
    split; [replace (bv_unsigned (rc_tp R) - 200)%Z with (utp R - 200)%Z by reflexivity; exact TB | lia].
  Qed.
  End Sz11.
  Lemma GI_at_exit : ltac:(let t := eval cbv delta [GI_at_exit__stmt] in GI_at_exit__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo code. ltac2:(SecDiet.SzSec.closeP 'GI_at_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


  (* [comment removed for export] *)
  Definition main_entry (R : rctx) (s : PState H hptr) (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem),
      ms = MS (mkR (Z_to_bv 64 0x186c8) (Z_to_bv 64 (usp0 R + -48)) (Z_to_bv 64 0x10800) (rc_tp R) t0 t1 t2
                   (Z_to_bv 64 (usp0 R + 8)) (Z_to_bv 64 (argc (rc_argv R)))
                   (Z_to_bv 64 (argc (rc_argv R))) (Z_to_bv 64 (usp0 R + 8)) (Z_to_bv 64 (envp_addr (rc_sp0 R) (rc_argv R))) a3 a4 a5 a6 a7
                   (Z_to_bv 64 0x13b84) (Z_to_bv 64 (envp_addr (rc_sp0 R) (rc_argv R))) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              bvmap_empty (Z_to_bv 64 0x13b84) (Z_to_bv 32 0) None m (seg_rom usegs)
      /\ GI K R s [] m /\ mem_inv usegs m /\ stk usegs m (rc_lo R) (usp0 R + -48) /\ valid_argv (rc_argv R)
      /\ (usp0 R mod 16 = 0)%Z
      (* [comment removed for export] *)
      /\ (usp0 R + Z.of_nat (length (build_stack_bytes Ubsan.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R))) <= 2^47)%Z.

  Definition main_post : Z -> PState H hptr -> machine_state -> Prop :=
    fun code s' ms' => at_exit (St:=PState H hptr) (SXGI K) SEF code s' ms'.

  Lemma neq_cond : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y ->
    negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros x y Hx Hy Hn. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hn. Qed.
  Lemma eq_cond : forall x, negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 x)) = false.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma beq_cond : forall x, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 x) = true.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma bne_cond_false : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y ->
    bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros x y Hx Hy Hn. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact Hn. Qed.

  (* [comment removed for export] *)
  Definition main_usage__stmt : Prop := forall R s ms,
    rc_cb R = false ->
    main_entry R s ms -> Z.of_nat (length (rc_argv R)) <> 2%Z ->
    implM usegs (main_prog HO fo_nop sites (argv_Z (rc_argv R))) s main_post ms.
  Section Sz16.
  Variables R s ms : ltac2:(SecDiet.SzSec.tyM 'main_usage__stmt "vvv" @R).
  Lemma main_usage__body : ltac2:(SecDiet.SzSec.bodyP 'main_usage__stmt "vvv").
  Proof using EPR_USAGE HFL SEF_range SFL. pin_using (fun (EPR_USAGE HFL SEF_range SFL : unit) => tt). ceil_facts.
    intros Hcb (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & -> & G & MI & ST & VA & AL16 & STKTOP) HC.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof VA as VA'. destruct VA' as (VA1 & VA2 & VA3 & VA4 & VA5).
    destruct (GI_core K _ _ _ _ G) as (_ & _ & _ & CM & _ & CS). destruct CM as (CM1 & CM2 & _). unfold CORE_STK in CS.
    destruct (rc_argv R) as [|argv0 argvr] eqn:EARGV; [cbn in VA1; lia|].
    pose proof (raw_len_nonneg Ubsan.M.phdrs (rc_sp0 R) (argv0 :: argvr) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R)) as RN.
    pose proof (build_stack_bytes_length Ubsan.M.phdrs (rc_sp0 R) (argv0 :: argvr) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R)) as BL.
    pose proof (bytes_at_bound _ _ _ _ CS) as CSB. fold (usp0 R) in BL, CSB.
    unfold main_prog, main_model. unfold argv_Z at 1. rewrite length_map.
    replace (Z.of_nat (length (argv0 :: argvr)) =? 2)%Z with false by (symmetry; apply Z.eqb_neq; exact HC). cbn [negb].
    pose proof (munch_refl [(usp0 R - 128, usp0 R - 48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rc_lo in ST. unfold implM. iprefix.
    carve_frame 80%nat ST.
    do 11 lstep.
    lstep. if_true_by (neq_cond (argc (argv0 :: argvr)) 2 ltac:(unfold argc; lia) ltac:(lia) ltac:(unfold argc; exact HC)).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      destruct (stack_argv_string_slack usegs Ubsan.M.phdrs (rc_sp0 R) (argv0 :: argvr) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R) m1 CS
                  ltac:(fold (usp0 R); clear -AL16; Z.div_mod_to_equations; lia) 0 argv0 eq_refl)
        as (P0 & slack0 & HP0 & P0lo & P0hi & STR0 & SLK0 & END0);
      pose proof (stack_argv_ptr_read usegs Ubsan.M.phdrs (rc_sp0 R) (argv0 :: argvr) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R) m1 CS 0 _ HP0) as RD0
    end.
    replace (bv_unsigned (rc_sp0 R) + 8 + 8 * Z.of_nat 0)%Z with (usp0 R + 8)%Z in RD0 by (unfold usp0; lia).
    unfold InitMem.str_base, InitMem.env_base, InitMem.str_base in P0lo, P0hi. fold (usp0 R) in P0lo, P0hi.
    do 7 lstep.
    (* [comment removed for export] *)
    assert (G1 : GI K R s [] ltac:(lazymatch type of MU with munch _ _ ?mb => exact mb end)).
    { eapply (GI_client_frame K HFL SFL); [exact G | exact MU | exact WM |].
      constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia | constructor]. }
    clear MU WM.
    name_spm R.
    apply evt_done. unfold diag, diag_usage. cbn [nth argv_Z map]. eapply (implM_bind_u usegs).
    { eapply EPR_USAGE; [ | reflexivity | reflexivity | reflexivity | exact STR0 | | | exact SLK0 | | ].
      - std_pre_tac G1 ST MI Hspm.
      - apply Forall_cons_iff in VA4 as [X _]. exact X.
      - apply Forall_cons_iff in VA3 as [X _]. lia.
      - intros a Ha. left. lia.
      - unfold usp0 in *. lia. }
    intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
    replace (ret_pc (Z_to_bv 64 0x13d38)) with (Z_to_bv 64 0x13d38) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
    unname_spm.
    unfold implM. iprefix. do 13 lstep.
    replace (ret_pc (Z_to_bv 64 0x186c8)) with (Z_to_bv 64 0x186c8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lstep.
    apply evt_done. apply (implM_ret usegs). apply evt_done. unfold main_post.
    release_frame FR ST2 (usp0 R + -48)%Z.
    eapply GI_at_exit; [exact G2 | exact Hcb | exact MI2 | rewrite unsigned_lit by lia; exact ST2 | unfold rc_lo; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity].
  Qed.
  End Sz16.
  Lemma main_usage : ltac:(let t := eval cbv delta [main_usage__stmt] in main_usage__stmt in exact t).
  Proof using EPR_USAGE HFL SEF_range SFL. intros R s ms. ltac2:(SecDiet.SzSec.closeP 'main_usage__body "vvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mframe (R : rctx) (m : mem) : Prop :=
    exists (j0 : list byte) (f1 f2 f3 f4 f5 f6 f7 f8 : word),
      rw_cells usegs m (usp0 R + -128) [CB 8 j0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7; C8 f8; C8 (Z_to_bv 64 0x186c8)].

  (* [comment removed for export] *)
  Definition mbuf (R : rctx) (s : PState H hptr) (m : mem) (q : hptr) (A cap : Z) (CBs : list byte) : Prop :=
    GI K R s [(q, A, cap)] m /\ mem_inv usegs m /\ stk usegs m (rc_lo R) (usp0 R + -128) /\ mframe R m
    /\ (exists junk, rw_cells usegs m A [CB (length CBs) CBs; CB (Z.to_nat (cap - Z.of_nat (length CBs))) junk])
    /\ (Z.of_nat (length CBs) <= cap)%Z /\ (65536 <= cap <= MAX_INPUT)%Z /\ (exists j, cap = 65536 * 2 ^ j)%Z
    /\ (usp0 R mod 16 = 0)%Z.

  (* [comment removed for export] *)
  Definition LH (R : rctx) (fd P1 : Z) (path slack : list byte) (st : rd_st (ptr:=hptr)) (s : PState H hptr) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (A : Z) (CBs : list byte) (pc : Z),
      ms = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 P1) (Z_to_bv 64 (rd_len st)) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st)) (Z_to_bv 64 0x24149) (Z_to_bv 64 A) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 pc) fc None m (seg_rom usegs)
      (* [comment removed for export] *)
      /\ (pc = 0x13c0c \/ (pc = 0x13bec /\ rd_len st = 0))%Z
      /\ mbuf R s m (rd_buf st) A (rd_cap st) CBs /\ rd_content st = of_bytes CBs /\ rd_len st = Z.of_nat (length CBs)
      /\ bytes_at usegs m P1 (path ++ Z_to_bv 8 0 :: slack) /\ (usp0 R <= P1)%Z /\ (3 <= fd <= 4096)%Z.

  (* [comment removed for export] *)
  Definition at_exit2 (R : rctx) (s : PState H hptr) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (m : mem) (CL : list cblock),
      ms = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x13e0c) fc None m (seg_rom usegs)
      /\ GI K R s CL m /\ mem_inv usegs m /\ stk usegs m (rc_lo R) (usp0 R + -128).

  Lemma at_exit2_exit : forall R s ms (Q : rd_result (ptr:=hptr) -> PState H hptr -> machine_state -> Prop),
    rc_cb R = false ->
    at_exit2 R s ms ->
    (forall ms', main_post 2 s ms' -> Q RdExit s ms') ->
    evt usegs (Q RdExit s) ms.
  Proof using SEF_range. pin_using (fun (SEF_range : unit) => tt). ceil_facts.
    intros R s ms Q Hcb (ra & gp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & CL & -> & G & MI & ST) HQ.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0. fold (usp0 R) in RSP0.
    lstep. lstep. apply evt_done. apply HQ. unfold main_post.
    eapply GI_at_exit; [exact G | exact Hcb | exact MI | rewrite unsigned_lit by lia; exact ST | lia | rewrite unsigned_lit by lia; unfold rc_lo; lia | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition LX (R : rctx) (fd P1 : Z) (path slack : list byte) (res : rd_result (ptr:=hptr)) (s : PState H hptr) (ms : machine_state) : Prop :=
    match res with
    | RdExit => at_exit2 R s ms
    | RdDone q content =>
        exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
               (m : mem) (A cap : Z) (CBs : list byte),
          ms = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 P1) (Z_to_bv 64 (Z.of_nat (length CBs))) (Z_to_bv 64 fd) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c78) fc None m (seg_rom usegs)
          /\ mbuf R s m q A cap CBs /\ content = of_bytes CBs
    end.

  (* [comment removed for export] *)
  Lemma implM_get_bind : forall {B} (k : PState H hptr -> M (PState H hptr) B) s Q ms,
    implM usegs (k s) s Q ms -> implM usegs (mbind mget k) s Q ms.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. exact H0. Qed.

  (* [comment removed for export] *)
  Lemma GI_addr : forall R s CL m q A n, GI K R s CL m -> In (q, A, n) CL -> ho_addr HO (ps_heap s) q = A.
  Proof using HAL. pin_using (fun (HAL : unit) => tt). ceil_facts.
    intros R s CL m q A n (FB & HH & _) Hin.
    exact (HAL _ _ _ _ (q, A, n) HH ltac:(apply in_app_iff; left; exact Hin)).
  Qed.

  (* [comment removed for export] *)
  Definition want_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (cap len : Z),
    s5 = Z_to_bv 64 cap -> s3 = Z_to_bv 64 len -> (0 <= len < cap)%Z -> (cap <= 67108864)%Z ->
    evt usegs (fun ms' => exists a0', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 (Z_to_bv 64 (Z.min (cap - len) 65536)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                          F (Z_to_bv 64 0x13c60) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13c50) fc None m (seg_rom usegs)).
  Section Sz20.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cap len : ltac2:(SecDiet.SzSec.tyM 'want_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma want_spec__body : ltac2:(SecDiet.SzSec.bodyP 'want_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
 intros -> -> Hr Hc.
    lstep. lstep. lstep.
    destruct (Z_lt_le_dec (cap - len) 65536).
    - if_true_by (ltu_cond_true (cap - len)%Z 65536%Z ltac:(lia) ltac:(lia)).
      rewrite Z.min_l by lia. apply evt_done. eexists. reflexivity.
    - if_false_by (ltu_cond_false (cap - len)%Z 65536%Z ltac:(lia) ltac:(lia)). lstep.
      rewrite Z.min_r by lia. apply evt_done. eexists. reflexivity.
  Qed.
  End Sz20.
  Lemma want_spec : ltac:(let t := eval cbv delta [want_spec__stmt] in want_spec__stmt in exact t).
  Proof using CEILV. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cap len. ltac2:(SecDiet.SzSec.closeP 'want_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma cap_shift_zero : forall cap j, (cap = 65536 * 2 ^ j)%Z -> (0 <= j)%Z -> (cap < 67108864)%Z -> Z.shiftr cap 26 = 0%Z.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros cap j -> Hj Hc. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia.
  Qed.

  (* [comment removed for export] *)
  Definition grow_post (R : rctx) (fd P1 : Z) (path slack : list byte) (len0 : Z) : option (rd_st (ptr:=hptr)) -> PState H hptr -> machine_state -> Prop :=
    fun g s' ms' =>
      match g with
      | None => at_exit2 R s' ms'
      | Some st1 => rd_len st1 = len0 /\ exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
                           (m : mem) (A : Z) (CBs : list byte),
          ms' = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 P1) (Z_to_bv 64 (rd_len st1)) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 0x24149) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c50) fc None m (seg_rom usegs)
          /\ mbuf R s' m (rd_buf st1) A (rd_cap st1) CBs /\ rd_content st1 = of_bytes CBs /\ rd_len st1 = Z.of_nat (length CBs)
          /\ (rd_len st1 < rd_cap st1)%Z
          /\ bytes_at usegs m P1 (path ++ Z_to_bv 8 0 :: slack)
      end.

  (* [comment removed for export] *)
  Definition grow_spec__stmt : Prop := forall R fd P1 path slack (st : rd_st (ptr:=hptr)) s ms,
    LH R fd P1 path slack st s ms -> rd_len st = rd_cap st ->
    implM usegs
      (if (MAX_INPUT <=? rd_cap st)%Z then diag DTooBig ;;; mret None
       else nb <- pmalloc HO (rd_cap st * 2) ;;
            match nb with
            | None => diag DOom ;;; mret None
            | Some nb' => pfree HO (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_len st) (rd_chunks st)))
            end) s
      (grow_post R fd P1 path slack (rd_len st)) ms.
  Section Sz22.
  Variables R fd P1 path slack st s ms : ltac2:(SecDiet.SzSec.tyM 'grow_spec__stmt "vvvvvvvv" @R).
  Lemma grow_spec__body : ltac2:(SecDiet.SzSec.bodyP 'grow_spec__stmt "vvvvvvvv").
  Proof using EFW EPR_BIG FREE HFL MALLOC SFL. pin_using (fun (EFW EPR_BIG FREE HFL MALLOC SFL : unit) => tt). ceil_facts.
    intros LHH Hfull.
    destruct LHH as (ra & gp & t0 & t1 & t2 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & A & CBs & pc
                     & -> & HPC & MB & HC & HL & PATH & HP1 & HFD).
    destruct MB as (G & MI & ST & (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) & (junk & BUF) & HLC & HCAP & (j & Hj) & AL16).
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. destruct (GI_core K _ _ _ _ G) as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
    assert (ELO : rc_lo R = (usp0 R - 8388608)%Z) by reflexivity.
    destruct st as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *. subst len.
    destruct (GI_blocks K _ _ _ _ G) as [BO _]. apply Forall_cons_iff in BO as [Bq _].
    unfold block_ok in Bq; cbn [cb_addr cb_size fst snd] in Bq. destruct Bq as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (bytes_at_bound _ _ _ _ PATH) as PB. rewrite length_app in PB; cbn [length] in PB.
    assert (Hj0 : (0 <= j)%Z). { destruct (Z_lt_le_dec j 0); [|lia]. rewrite Z.pow_neg_r in Hj by lia. lia. }
    rewrite Hfull in *.
    (* [comment removed for export] *)
    destruct HPC as [->|[_ H0]]; [|exfalso; unfold MAX_INPUT in *; lia].
    unfold implM. iprefix. lstep. if_true_by (beq_cond cap). lstep.
    destruct (Z_le_gt_dec MAX_INPUT cap) as [HBIG|HOK].
    - (* [comment removed for export] *)
      replace (MAX_INPUT <=? cap)%Z with true by (symmetry; apply Z.leb_le; exact HBIG).
      assert (Ecap : cap = 67108864%Z) by (unfold MAX_INPUT in *; lia).
      replace (Z.shiftr cap 26) with 1%Z by (rewrite Ecap; reflexivity).
      astep. do 7 lstep.
      name_spm R.
      apply evt_done. unfold diag, diag_too_big. eapply (implM_bind_u usegs).
      { eapply EPR_BIG; [ | reflexivity | reflexivity | reflexivity ]. std_pre_tac G ST MI Hspm. }
      intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13de8)) with (Z_to_bv 64 0x13de8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unname_spm.
      unfold implM. iprefix. lstep.
      apply evt_done. apply (implM_ret usegs). apply evt_done.
      unfold grow_post, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2| exact ST2].
    - (* [comment removed for export] *)
      replace (MAX_INPUT <=? cap)%Z with false by (symmetry; apply Z.leb_gt; lia).
      rewrite (cap_shift_zero cap j Hj Hj0 ltac:(unfold MAX_INPUT in HOK; lia)).
      astep. lstep. lstep. lstep.
      rewrite (Z.shiftl_mul_pow2 cap 1) by lia. change (2 ^ 1)%Z with 2%Z.
      destruct (cap_double_ok cap j Hj Hj0 ltac:(unfold MAX_INPUT in HOK; lia)) as [Hj' HC2].
      name_spm R.
      apply evt_done. eapply (implM_bind_u usegs).
      { eapply MALLOC; [ | reflexivity | unfold MAX_INPUT in HOK; lia]. std_pre_tac G ST MI Hspm. }
      intros r s' ms' PO. unfold malloc_post in PO. destruct_exs PO. destruct PO as (-> & MI1 & ST1 & AG1 & CASES). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13c2c)) with (Z_to_bv 64 0x13c2c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ AG1) in PATH; [|lia].
      apply (keeps_rw_cells_block _ _ _ _ _ _ AG1) in BUF.
      2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
      unname_spm.
      destruct r as [nb|].
      + (* [comment removed for export] *)
        destruct CASES as (A' & junk' & -> & G1 & BLK & BOK & HADDR).
        pose proof BOK as BOK'. unfold block_ok in BOK'. cbn [cb_addr cb_size fst snd] in BOK'. destruct BOK' as (C1 & C2 & C3 & C4 & C5 & C6).
        destruct (GI_blocks K _ _ _ _ G1) as [_ [AP _]]. apply Forall_cons_iff in AP as [AP _]. unfold apart in AP. cbn [cb_addr cb_size fst snd] in AP.
        cbv beta iota. unfold implM. iprefix.
        lstep. if_false_by (eqz_cond_false A' ltac:(lia)). lstep.
        lstep. if_false_by (eqz_cond_false cap ltac:(lia)). lstep. lstep. lstep. lstep.
        (* [comment removed for export] *)
        apply (rw_cells_split_CB usegs _ _ [] _ _ [] [Z.to_nat cap; Z.to_nat cap]) in BLK; [|cbn; lia]. cbn [app mk_CB_cells] in BLK.
        apply (proj1 (rw_cells_app usegs _ _ [_] [_])) in BLK as [BLK1 BLK2]. cbn [cells_size csize Nat.add] in BLK2.
        rewrite Nat.add_0_r, Z2Nat.id in BLK2 by lia.
        pose proof BUF as BUF'. apply (proj1 (rw_cells_app usegs _ _ [_] [_])) in BUF' as [BUF1 _].
        assert (SRC : bytes_at usegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A CBs).
        { destruct BUF1 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          pose proof (munch_refl [(A', A' + cap)]%Z m1) as MU2; pose proof (wmono_refl usegs m1) as WM2 end.
        call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' A cap CBs (firstn (Z.to_nat cap) junk'));
          [reflexivity | reflexivity | reflexivity | exact SRC | lia | lia | exact BLK1 | lia | lia | lia | exact MI1 |].
        rename PC into DST. clear POST BUF1 SRC BUF.
        lazymatch type of MU2 with munch _ _ ?mb =>
          assert (G2 : GI K R s' ((nb, A', (cap * 2)%Z) :: [(q, A, cap)]) mb);
          [ eapply (GI_client_frame K HFL SFL); [exact G1 | exact MU2 | exact WM2 |];
            constructor; [| constructor]; right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia | ]
        end.
        clear MU2 WM2 G1.
        lstep. lstep.
        name_spm R.
        apply evt_done. eapply (implM_bind_u usegs).
        { eapply FREE with (C1 := [(nb, A', (cap * 2)%Z)]) (C2 := []); [| reflexivity]. std_pre_tac G2 ST1 MI Hspm. }
        intros [] s'' ms'' PO. unfold free_post in PO. destruct_exs PO. destruct PO as (-> & MI3 & ST3 & AG3 & G3). clear MI.
        cbn [app] in AG3, G3.
        replace (ret_pc (Z_to_bv 64 0x13c50)) with (Z_to_bv 64 0x13c50) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FR; [|lia].
        apply (keeps_bytes_at_stack _ _ _ _ _ _ AG3) in PATH; [|lia].
        apply (keeps_rw_cells_block _ _ _ _ _ _ AG3) in DST.
        2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
        apply (keeps_rw_cells_block _ _ _ _ _ _ AG3) in BLK2.
        2:{ intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *. lia. }
        unname_spm.
        (* [comment removed for export] *)
        apply (implM_ret usegs). apply evt_done.
        unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks rd_content]. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split.
        { split; [exact G3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
          split.
          { exists (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk')).
            replace (length CBs) with (Z.to_nat cap) by lia.
            replace (Z.to_nat (cap * 2 - Z.of_nat (Z.to_nat cap))) with (Z.to_nat cap) by lia.
            apply rw_cells_join2; [exact DST|]. cbn [csize]. rewrite Z2Nat.id by lia. exact BLK2. }
          split; [lia|]. split; [unfold MAX_INPUT; lia|]. split; [exists (j + 1)%Z; exact Hj'| assumption]. }
        split; [exact HC|]. split; [symmetry; exact Hfull|]. split; [lia| exact PATH].
      + (* [comment removed for export] *)
        destruct CASES as [-> G1]. clear CM1 CM2. destruct (GI_core K _ _ _ _ G1) as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
        cbv beta iota. unfold implM. iprefix. astep. do 8 lstep.
        destruct MSG_OOM_ok as (RB & EM & LM).
        name_spm R.
        apply evt_done. unfold diag, diag_oom. rewrite <- EM. eapply (implM_bind_u usegs).
        { eapply EFW; [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI1 | exact RB | lia | rewrite LM; lia] | rewrite LM; lia | rewrite LM; lia].
          std_pre_tac G1 ST1 MI1 Hspm. }
        intros [] s'' ms'' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI3 & ST3 & AG3 & G3). clear MI1.
        replace (ret_pc (Z_to_bv 64 0x13e0c)) with (Z_to_bv 64 0x13e0c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        unname_spm.
        apply (implM_ret usegs). apply evt_done.
        unfold grow_post, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G3|]. split; [exact MI3| exact ST3].
  Qed.
  End Sz22.
  Lemma grow_spec : ltac:(let t := eval cbv delta [grow_spec__stmt] in grow_spec__stmt in exact t).
  Proof using EFW EPR_BIG FREE HFL MALLOC SFL. intros R fd P1 path slack st s ms. ltac2:(SecDiet.SzSec.closeP 'grow_spec__body "vvvvvvvv"). Qed.

  Definition body_post (R : rctx) (fd P1 : Z) (path slack : list byte) : (rd_st (ptr:=hptr) + rd_result (ptr:=hptr)) -> PState H hptr -> machine_state -> Prop :=
    fun r s' ms' => match r with inl st' => LH R fd P1 path slack st' s' ms' | inr res => LX R fd P1 path slack res s' ms' end.

  (* [comment removed for export] *)
  Lemma RS_ok : rw_bytes_b usegs 0x24149 (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) = true.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    (* [comment removed for export] *)
    apply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.RwZero.rw_bytes_b_zero usegs Ubsan_segment_003 Ubsan_seg_bytes_003 eq_refl eq_refl eq_refl
             (Uint63.of_Z 8850) (Uint63.of_Z 131072)).
    - vm_cast_no_check (@eq_refl bool true).
    - change (Uint63.to_Z (Uint63.of_Z 131072) <= Uint63.to_Z PrimString.max_length)%Z with (131072 <= 16777211)%Z. lia.
    - intros a Ha.
      change usegs with ([Ubsan_segment_000; Ubsan_segment_001; Ubsan_segment_002] ++ Ubsan_segment_003 :: []).
      apply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.RwZero.rz_find_segment _ _ _ 0x24149 (0x24149 + 65536)); [ repeat constructor | .. ];
        unfold Ubsan_segment_000, Ubsan_segment_001, Ubsan_segment_002, Ubsan_segment_003; cbn [seg_base seg_size]; lia.
    - unfold Ubsan_segment_003; cbn [seg_base]; lia.
    - lia.
    - lia.
    - unfold Ubsan_segment_003; cbn [seg_base]. change (Uint63.to_Z (Uint63.of_Z 8850)) with 8850%Z. lia.
    - unfold Ubsan_segment_003; cbn [seg_base]. change (Uint63.to_Z (Uint63.of_Z 8850)) with 8850%Z.
      change (Uint63.to_Z (Uint63.of_Z 131072)) with 131072%Z. lia.
  Qed.
  Lemma RS_chunk : forall m : mem, exists rsj, rw_cells usegs m 0x24149 [CB (Z.to_nat 65536) rsj].
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros m. destruct (rw_cells_any usegs m 0x24149%Z (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) RS_ok ltac:(lia) ltac:(rewrite repeat_length; lia)) as (rsj & RSL & RSC).
    rewrite repeat_length in RSC. exists rsj. exact RSC.
  Qed.

  (* [comment removed for export] *)
  Definition read_step__stmt : Prop := forall R fd P1 path slack (len0 : Z) (st1 : rd_st (ptr:=hptr)) s ms,
    grow_post R fd P1 path slack len0 (Some st1) s ms ->
    ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z -> (3 <= fd <= 4096)%Z -> (usp0 R <= P1)%Z ->
    (P1 + Z.of_nat (length path) + 1 <= 2^47)%Z ->
    implM usegs
      (s0 <- mget ;;
       (let buf := sites SiteReadStage in
        let want := (rd_cap st1 - len0)%Z in
        let want' := (if READ_CHUNK <? want then READ_CHUNK else want)%Z in
        a <- msys (NRead fd buf want') (dec_read buf want') ;;
        match a with
        | RdErr _ => diag (DReadError (map bv_unsigned path)) ;;; mret (inr RdExit)
        | RdData bs => if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
                       else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (len0 + zlength bs)%Z (rd_chunks st1 ++ [of_bytes bs])))
        end)) s (body_post R fd P1 path slack) ms.
  Section Sz25.
  Variables R fd P1 path slack len0 st1 s ms : ltac2:(SecDiet.SzSec.tyM 'read_step__stmt "vvvvvvvvv" @R).
  Lemma read_step__body : ltac2:(SecDiet.SzSec.bodyP 'read_step__stmt "vvvvvvvvv").
  Proof using EPR_READ HFL SFL SITE_RS. pin_using (fun (EPR_READ HFL SFL SITE_RS : unit) => tt). ceil_facts.
    intros GP HNUL HPL HFD HP1 HP47.
    destruct GP as [<- GP].
    destruct GP as (ra & gp & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & A & CBs
                    & -> & MB & HC & HL & HLT & PATH).
    destruct MB as (G & MI & ST & (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) & (junk & BUF) & HLC & HCAP & (j & Hj) & AL16).
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. destruct (GI_core K _ _ _ _ G) as (CT & _ & _ & (CM1 & CM2 & _) & _ & _).
    unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e & T1 & T2 & T3 & T4 & T5 & T6 & Ht); subst z x.
    pose proof (GI_tls K _ _ _ _ G) as [_ TB]. pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (ELO : rc_lo R = (usp0 R - 8388608)%Z) by reflexivity.
    destruct st1 as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *. subst len.
    set (len := Z.of_nat (length CBs)) in *.
    destruct (GI_blocks K _ _ _ _ G) as [BO _]. apply Forall_cons_iff in BO as [Bq _].
    unfold block_ok in Bq; cbn [cb_addr cb_size fst snd] in Bq. destruct Bq as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (bytes_at_bound _ _ _ _ PATH) as PB. rewrite length_app in PB; cbn [length] in PB.
    pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0. fold (usp0 R) in RSP0.
    apply implM_get_bind. cbv beta zeta.
    rewrite SITE_RS.
    set (want := Z.min (cap - len) 65536).
    replace (if READ_CHUNK <? cap - len then READ_CHUNK else cap - len)%Z with want.
    2:{ subst want. unfold READ_CHUNK. destruct (Z.ltb_spec 65536 (cap - len)); lia. }
    assert (HW : (1 <= want <= 65536)%Z /\ (want <= cap - len)%Z) by (subst want; lia).
    destruct HW as [HW1 HW2].
    unfold implM. iprefix.
    eapply evt_cut; [eapply (want_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m cap len); [reflexivity | reflexivity | lia | unfold MAX_INPUT in HCAP; lia] |].
    cbv beta. intros ms' [a0' ->]. fold want.
    lstep. lstep. lstep.
    (* [comment removed for export] *)
    destruct (RS_chunk m) as (rsj & RSC).
    apply (rw_cells_split_CB usegs _ _ [] _ _ [] [Z.to_nat want; Z.to_nat (65536 - want)]) in RSC; [|cbn; lia]. cbn [app mk_CB_cells] in RSC.
    apply (proj1 (rw_cells_app usegs _ _ [_] [_])) in RSC as [RSw _].
    name_spm R.
    apply evt_done. eapply (implM_msys_of_enode usegs); [reflexivity | |].
    { eapply (read_specZ _ spm _ (rc_tp R)) with (lo := rc_lo R);
        [ rewrite Hspm; exact ST | exact RSw | exact T2 | exact MI | reflexivity | reflexivity | reflexivity
        | lia | lia | lia | lia | rewrite Hspm, ELO; lia | rewrite Hspm; unfold utp in *; lia | rewrite Hspm; lia | unfold utp in *; lia | unfold utp in *; lia ]. }
    intros a ms' PO. unfold read_post in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI' & ST' & CASE). 
    replace (ret_pc (Z_to_bv 64 0x13c6c)) with (Z_to_bv 64 0x13c6c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    change (bv_unsigned (rc_tp R)) with (utp R) in *. rewrite Z2Nat.id in MU by lia.
    clear RSw.
    lazymatch type of MU with munch _ ?ma ?mb => transport_after_call usegs ma mb MU WM end.
    clear MI. rename MI' into MI.
    apply (munch_weaken _ [(utp R - 164, utp R - 160); (bv_unsigned spm - 16, bv_unsigned spm); (0x24149, 0x24149 + want)]%Z) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
    (* [comment removed for export] *)
    assert (G' : forall ev, rw_cells usegs ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end) (utp R + -164) [C4 ev] ->
                 GI K R s [(q, A, cap)] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
    { intros ev HEV. eapply (GI_client_frame_errno_rs K HFL SFL); [exact G | exact MU | exact WM | | exact HEV].
      constructor; [left; left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia|].
      constructor; [right; unfold rs_iv; cbn [fst snd]; lia| constructor]. }
    clear MU WM G.
    destruct a as [err|bs].
    - (* [comment removed for export] *)
      destruct CASE as (_ & ERR & Herr). specialize (G' _ ERR).
      clear CM1 CM2. destruct (GI_core K _ _ _ _ G') as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
      unfold read_ret. unname_spm.
      unfold implM. iprefix. lstep. if_true_by ltz_cond_m1. do 8 lstep.
      name_spm R.
      apply evt_done. unfold diag, diag_read_error. eapply (implM_bind_u usegs).
      { eapply EPR_READ; [ | reflexivity | reflexivity | reflexivity | exact PATH | exact HNUL | exact (proj1 HPL) | exact (proj2 HPL) | intros a Ha; left; lia | exact HP47 ].
        std_pre_tac G' ST' MI Hspm. }
      intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13de8)) with (Z_to_bv 64 0x13de8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unname_spm.
      unfold implM. iprefix. lstep.
      apply evt_done. apply (implM_ret usegs). apply evt_done.
      unfold body_post, LX, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2| exact ST2].
    - (* [comment removed for export] *)
      destruct CASE as (RSr & ERR & Hbs). specialize (G' _ ERR).
      unfold read_ret. unname_spm.
      pose proof (Nat2Z.is_nonneg (length bs)) as LB0.
      unfold implM. iprefix. lstep. if_false_by (ltz_cond_false (Z.of_nat (length bs)) ltac:(lia)). lstep.
      destruct bs as [|b bs'].
      + (* [comment removed for export] *)
        lstep. if_false_by (eq_cond 0).
        apply evt_done. cbn [length Nat.eqb]. apply (implM_ret usegs). apply evt_done.
        unfold body_post, LX. cbn [rd_content rd_chunks].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|]. split; [| exact HC].
        split; [exact G'|]. split; [exact MI|]. split; [exact ST'|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
        split; [exists junk; exact BUF|].
        split; [lia|]. split; [exact HCAP|]. split; [exists j; exact Hj| assumption].
      + (* [comment removed for export] *)
        set (n := Z.of_nat (length (b :: bs'))) in *.
        assert (Hn : (1 <= n <= want)%Z) by (subst n; cbn [length] in *; lia).
        lstep. if_true_by (nez_cond n ltac:(lia)).
        lstep. lstep. lstep. lstep.
        (* [comment removed for export] *)
        apply (proj1 (rw_cells_app usegs _ _ [_] [_])) in RSr as [RSd _].
        assert (SRC : bytes_at usegs ltac:(lazymatch type of RSd with rw_cells _ ?mm _ _ => exact mm end) 0x24149 (b :: bs')).
        { destruct RSd as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
        clear RSd.
        pose proof BUF as BUF0. apply (proj1 (rw_cells_app usegs _ _ [_] [_])) in BUF as [BUF1 BUF2]. cbn [cells_size csize Nat.add] in BUF2.
        rewrite Nat.add_0_r in BUF2. fold len in BUF2.
        apply (rw_cells_split_CB usegs _ _ [] _ _ [] [Z.to_nat n; Z.to_nat (cap - len - n)]) in BUF2; [|cbn; lia]. cbn [app mk_CB_cells] in BUF2.
        apply (proj1 (rw_cells_app usegs _ _ [_] [_])) in BUF2 as [BUFw BUF3]. cbn [cells_size csize Nat.add] in BUF3.
        rewrite Nat.add_0_r, Z2Nat.id in BUF3 by lia.
        clear BUF0.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          pose proof (munch_refl [(A + len, A + len + n)]%Z m1) as MU2; pose proof (wmono_refl usegs m1) as WM2 end.
        call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A + len)%Z 0x24149%Z n (b :: bs') (firstn (Z.to_nat n) junk));
          [reflexivity | reflexivity | reflexivity | exact SRC | subst n; lia | lia | exact BUFw | lia | lia | lia | exact MI |].
        rename PC into DST. clear POST. try clear SRC. try clear MI. rename MI0 into MI.
        lazymatch type of MU2 with munch _ _ ?mb =>
          assert (G2 : GI K R s [(q, A, cap)] mb);
          [ eapply (GI_client_frame K HFL SFL); [exact G' | exact MU2 | exact WM2 |];
            constructor; [| constructor]; right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia | ]
        end.
        clear MU2 WM2 G'.
        (* [comment removed for export] *)
        lstep. lstep.
        (* [comment removed for export] *)
        assert (BUF : exists junk', rw_cells usegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A
                        [CB (length (CBs ++ b :: bs')) (CBs ++ b :: bs'); CB (Z.to_nat (cap - (len + n))) junk']).
        { eexists.
          assert (J : rw_cells usegs ltac:(lazymatch type of BUF1 with rw_cells _ ?mm _ _ => exact mm end) A
                        ([CB (length CBs) CBs] ++ [CB (Z.to_nat n) (b :: bs')] ++ [CB (Z.to_nat (cap - len - n)) (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk))])).
          { apply (proj2 (rw_cells_app usegs _ _ _ _)). split; [exact BUF1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. fold len.
            apply (proj2 (rw_cells_app usegs _ _ [_] [_])). split; [exact DST|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact BUF3. }
          cbn [app] in J.
          apply (rw_cells_merge usegs _ _ [] [CB (length CBs) CBs; CB (Z.to_nat n) (b :: bs')] [_]) in J. cbn [cells_size csize cells_bytes cbytes app] in J.
          replace (length CBs + (Z.to_nat n + 0))%nat with (length (CBs ++ b :: bs')) in J by (rewrite length_app; subst n; lia).
          rewrite ?app_nil_r in J.
          replace (Z.to_nat (cap - len - n)) with (Z.to_nat (cap - (len + n))) in J by lia. exact J. }
        clear BUF1 DST BUF3. destruct BUF as [junk' BUF].
        apply evt_done. replace (length (b :: bs') =? 0)%nat with false by reflexivity. apply (implM_ret usegs). apply evt_done.
        unfold body_post, LH. cbn [rd_buf rd_cap rd_len rd_chunks rd_content].
        replace (n + len)%Z with (len + zlength (b :: bs'))%Z by (unfold zlength; subst n; lia).
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [left; reflexivity|].
        split.
        { split; [exact G2|]. split; [exact MI|]. split; [exact ST'|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
          split. { exists junk'. replace (cap - Z.of_nat (length (CBs ++ b :: bs')))%Z with (cap - (len + n))%Z by (rewrite length_app; subst n len; lia). exact BUF. }
          split; [rewrite length_app; subst n len; lia|]. split; [exact HCAP|]. split; [exists j; exact Hj| assumption]. }
        split. { unfold rd_content in *. cbn [rd_chunks] in HC |- *. rewrite concat_app. cbn [concat]. rewrite app_nil_r, HC. unfold of_bytes. rewrite map_app. reflexivity. }
        split; [unfold zlength; rewrite length_app; subst len; lia|].
        split; [exact PATH|]. split; [exact HP1| exact HFD].
  Qed.
  End Sz25.
  Lemma read_step : ltac:(let t := eval cbv delta [read_step__stmt] in read_step__stmt in exact t).
  Proof using EPR_READ HFL SFL SITE_RS. intros R fd P1 path slack len0 st1 s ms. ltac2:(SecDiet.SzSec.closeP 'read_step__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition body_spec__stmt : Prop := forall R fd P1 path slack (st : rd_st (ptr:=hptr)) s ms,
    LH R fd P1 path slack st s ms -> ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
    (P1 + Z.of_nat (length path) + 1 <= 2^47)%Z ->
    implM usegs (read_loop_body diag (pmalloc HO) (pfree HO) (sites SiteReadStage) fd (map bv_unsigned path) st) s (body_post R fd P1 path slack) ms.
  Section Sz26.
  Variables R fd P1 path slack st s ms : ltac2:(SecDiet.SzSec.tyM 'body_spec__stmt "vvvvvvvv" @R).
  Lemma body_spec__body : ltac2:(SecDiet.SzSec.bodyP 'body_spec__stmt "vvvvvvvv").
  Proof using EFW EPR_BIG EPR_READ FREE HFL MALLOC SFL SITE_RS. pin_using (fun (EFW EPR_BIG EPR_READ FREE HFL MALLOC SFL SITE_RS : unit) => tt). ceil_facts.
    intros LHH HNUL HPL HP47.
    pose proof LHH as LHH'.
    destruct LHH' as (ra & gp & t0 & t1 & t2 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & A & CBs & pc
                       & Ems & HPC & MB & HC & HL & PATH & HP1 & HFD). subst ms.
    pose proof MB as MB'. destruct MB' as (G & MI & ST & FRm & BUF & HLC & HCAP & HJ & AL16).
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__.
    unfold read_loop_body. cbv zeta.
    eapply (implM_bind usegs _ _ s (grow_post R fd P1 path slack (rd_len st))).
    - destruct (Z.eqb_spec (rd_len st) (rd_cap st)) as [E|NE].
      + apply grow_spec; [exact LHH | exact E].
      + apply (implM_ret usegs).
        destruct st as [q cap len chunks]; cbn [rd_buf rd_cap rd_len rd_chunks] in *.
        (* [comment removed for export] *)
        destruct HPC as [->|[-> H0]].
        * lstep. if_false_by (bne_cond_false len cap ltac:(unfold MAX_INPUT in *; lia) ltac:(unfold MAX_INPUT in *; lia) NE). lstep. lstep.
          apply evt_done. unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks]. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|]. split; [exact MB|]. split; [exact HC|]. split; [exact HL|]. split; [lia| exact PATH].
        * lstep. if_true_by (neq_cond 0 cap ltac:(lia) ltac:(unfold MAX_INPUT in *; lia) ltac:(unfold MAX_INPUT in *; lia)). lstep. lstep.
          apply evt_done. unfold grow_post. cbn [rd_buf rd_cap rd_len rd_chunks]. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|]. split; [exact MB|]. split; [exact HC|]. split; [exact HL|]. split; [lia| exact PATH].
    - intros g s' ms' GP. destruct g as [st1|].
      + cbv beta iota. eapply read_step; [exact GP | exact HNUL | exact HPL | exact HFD | exact HP1 | exact HP47].
      + cbv beta iota. apply (implM_ret usegs). apply evt_done. exact GP.
  Qed.
  End Sz26.
  Lemma body_spec : ltac:(let t := eval cbv delta [body_spec__stmt] in body_spec__stmt in exact t).
  Proof using EFW EPR_BIG EPR_READ FREE HFL MALLOC SFL SITE_RS. intros R fd P1 path slack st s ms. ltac2:(SecDiet.SzSec.closeP 'body_spec__body "vvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma loop_spec : forall fuel R fd P1 path slack (st : rd_st (ptr:=hptr)) s ms,
    LH R fd P1 path slack st s ms -> ~ In (Z_to_bv 8 0) path -> (Z.of_nat (length path) < 2^24 /\ (- (P1 + Z.of_nat (length path) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
    (P1 + Z.of_nat (length path) + 1 <= 2^47)%Z ->
    implM usegs (mloop fuel (read_loop_body diag (pmalloc HO) (pfree HO) (sites SiteReadStage) fd (map bv_unsigned path)) st) s
      (LX R fd P1 path slack) ms.
  Proof using EFW EPR_BIG EPR_READ FREE HFL MALLOC SFL SITE_RS. pin_using (fun (EFW EPR_BIG EPR_READ FREE HFL MALLOC SFL SITE_RS : unit) => tt). ceil_facts.
    induction fuel as [|fuel IH]; intros R fd P1 path slack st s ms LHH HNUL HPL HP47.
    - cbn [mloop]. apply implM_unr.
    - apply implM_loop_S. eapply (implM_mono usegs); [eapply body_spec; [exact LHH | exact HNUL | exact HPL | exact HP47]|].
      cbv beta. intros [st'|res] s' ms' BP; unfold body_post in BP.
      + apply IH; [exact BP | exact HNUL | exact HPL | exact HP47].
      + apply evt_done. exact BP.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma to_bytes_of_bytes : forall l : list byte, to_bytes (map bv_unsigned l) = l.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros l. unfold to_bytes. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
    apply definitions.Z_to_bv_bv_unsigned.
  Qed.

  Lemma rw_cells_nil_CB : forall m A cs, rw_cells usegs m A cs -> rw_cells usegs m A (CB 0 [] :: cs).
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros m A cs [[Hwf HB] HW]. split; [split|].
    - split; [reflexivity| exact Hwf].
    - cbn [cells_bytes cbytes app]. exact HB.
    - cbn [cells_size csize Nat.add]. exact HW.
  Qed.

  (* [comment removed for export] *)
  Definition P2 (R : rctx) (s : PState H hptr) (ms : machine_state) : Prop :=
    exists (ra gp t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      ms = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 2) s1 a0 (Z_to_bv 64 (usp0 R + 8)) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x13bb4) fc None m (seg_rom usegs)
      /\ GI K R s [] m /\ mem_inv usegs m /\ stk usegs m (rc_lo R) (usp0 R + -128) /\ mframe R m /\ (usp0 R mod 16 = 0)%Z
      /\ (usp0 R + Z.of_nat (length (build_stack_bytes Ubsan.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R))) <= 2^47)%Z.

  (* [comment removed for export] *)
  Definition RAX (R : rctx) (res : rd_result (ptr:=hptr)) (s : PState H hptr) (ms : machine_state) : Prop :=
    match res with
    | RdExit => at_exit2 R s ms
    | RdDone q content =>
        exists (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
               (m : mem) (A cap : Z) (CBs : list byte),
          ms = MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (Z.of_nat (length CBs))) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13c80) fc None m (seg_rom usegs)
          /\ mbuf R s m q A cap CBs /\ content = of_bytes CBs
    end.

  Definition read_all_spec__stmt : Prop := forall R s ms argv1,
    P2 R s ms -> nth_error (rc_argv R) 1 = Some argv1 -> valid_argv (rc_argv R) ->
    implM usegs (read_all diag (pmalloc HO) (pfree HO) (sites SiteReadStage) (map bv_unsigned argv1)) s (RAX R) ms.
  Section Sz30.
  Variables R s ms argv1 : ltac2:(SecDiet.SzSec.tyM 'read_all_spec__stmt "vvvv" @R).
  Lemma read_all_spec__body : ltac2:(SecDiet.SzSec.bodyP 'read_all_spec__stmt "vvvv").
  Proof using EFW EPR_BIG EPR_OPEN EPR_READ FREE HFL MALLOC SFL SITE_RS. pin_using (fun (EFW EPR_BIG EPR_OPEN EPR_READ FREE HFL MALLOC SFL SITE_RS : unit) => tt). ceil_facts.
    intros (ra & gp & t0 & t1 & t2 & s1 & a0 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m
                           & -> & G & MI & ST & (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) & AL16 & STKTOP) HA1 VA.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. pose proof VA as VA'. destruct VA' as (VA1 & VA2 & VA3 & VA4 & VA5).
    destruct (GI_core K _ _ _ _ G) as (CT & _ & CLI & (CM1 & CM2 & _) & _ & CS). unfold CORE_STK in CS.
    unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e & T1 & T2 & T3 & T4 & T5 & T6 & Ht); subst z x. destruct CLI as (L1 & L2 & L3 & L4 & L5).
    pose proof (GI_tls K _ _ _ _ G) as [_ TB]. pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (ELO : rc_lo R = (usp0 R - 8388608)%Z) by reflexivity.
    pose proof (raw_len_nonneg Ubsan.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R)) as RN.
    pose proof (build_stack_bytes_length Ubsan.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R)) as BL.
    pose proof (bytes_at_bound _ _ _ _ CS) as CSB. fold (usp0 R) in BL, CSB.
    destruct (stack_argv_string_slack usegs Ubsan.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R) m CS
                ltac:(fold (usp0 R); clear -AL16; Z.div_mod_to_equations; lia) 1 argv1 HA1) as (P1 & slack1 & HP1 & P1lo & P1hi & STRS & SLK1 & END1).
    destruct (proj1 (bytes_at_app usegs m P1 (argv1 ++ [Z_to_bv 8 0]) slack1) ltac:(rewrite <- app_assoc; exact STRS)) as [STR1 _].
    pose proof (stack_argv_ptr_read usegs Ubsan.M.phdrs (rc_sp0 R) (rc_argv R) (rc_envp R) (rc_uid R) (rc_hw R) (rc_rnd R) m CS 1 _ HP1) as RD1.
    replace (bv_unsigned (rc_sp0 R) + 8 + 8 * Z.of_nat 1)%Z with (usp0 R + 16)%Z in RD1 by (unfold usp0; lia).
    unfold InitMem.str_base, InitMem.env_base, InitMem.str_base in P1lo, P1hi. fold (usp0 R) in P1lo, P1hi.
    assert (HNUL : ~ In (Z_to_bv 8 0) argv1). { apply (proj1 (Forall_forall _ _) VA4). eapply nth_error_In. exact HA1. }
    (* [comment removed for export] *)
    assert (HSLD : Namei.path_has_slash argv1 = false /\ Fs.path_eqb argv1 Namei.dotdot_path = false).
    { clear - HA1 VA5. destruct (rc_argv R) as [|x tlv]; [discriminate|]. cbn [tl] in VA5.
      change (nth_error tlv 0 = Some argv1) in HA1.
      exact (proj1 (Forall_forall _ _) VA5 _ (nth_error_In _ _ HA1)). }
    assert (HPL : (Z.of_nat (length argv1) < 2^24 /\ (- (P1 + Z.of_nat (length argv1) + 1)) mod 8 <= Z.of_nat (length slack1))%Z).
    { split; [|exact SLK1]. pose proof (proj1 (Forall_forall _ _) VA3 _ (nth_error_In _ _ HA1)). cbn beta in *. lia. }
    assert (HP47 : (P1 + Z.of_nat (length argv1) + 1 <= 2^47)%Z) by (unfold usp0 in *; lia).
    pose proof (bytes_at_bound _ _ _ _ STRS) as PBS. rewrite length_app in PBS; cbn [length] in PBS.
    pose proof (bytes_at_bound _ _ _ _ STR1) as PB. rewrite length_app in PB; cbn [length] in PB.
    unfold read_all. rewrite to_bytes_of_bytes.
    unfold implM. iprefix. lstep. lstep. lstep. lstep.
    name_spm R.
    apply evt_done. eapply (implM_msys_of_enode usegs); [reflexivity | |].
    { eapply (open_spec _ spm _ (rc_tp R)) with (lo := rc_lo R);
        [ rewrite Hspm; exact ST | rewrite unsigned_lit by lia; exact STR1 | exact T2 | exact L2 | exact L3 | exact MI | reflexivity | exact HNUL
        | exact (proj1 HSLD) | exact (proj2 HSLD)
        | rewrite Hspm, ELO; lia | rewrite Hspm; unfold utp in *; lia | rewrite Hspm, unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; unfold utp in *; lia | rewrite Hspm; unfold ssp_guard; lia
        | unfold ssp_guard, utp in *; lia | unfold got_ssp, utp in *; lia | unfold utp in *; lia ]. }
    intros r ms' PO. unfold open_post in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI' & ST' & ERR & STR & GOT & GUARD & Hr).
    replace (ret_pc (Z_to_bv 64 0x13bc4)) with (Z_to_bv 64 0x13bc4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    change (bv_unsigned (rc_tp R)) with (utp R) in *. rewrite unsigned_lit in STR by lia.
    lazymatch type of MU with munch _ ?ma ?mb => transport_after_call usegs ma mb MU WM end.
    clear MI. rename MI' into MI.
    apply (munch_weaken _ [(utp R - 164, utp R - 160); (bv_unsigned spm - 112, bv_unsigned spm)]%Z) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
    assert (G' : GI K R s [] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
    { eapply (GI_client_frame_errno K HFL SFL); [exact G | exact MU | exact WM | | exact ERR].
      constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia| constructor]. }
    clear MU WM G CM1 CM2. destruct (GI_core K _ _ _ _ G') as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
    destruct r as [err|fd].
    - (* [comment removed for export] *)
      unfold open_ret. unname_spm.
      cbv beta iota. unfold implM. iprefix. lstep. if_true_by ltz_cond_m1. do 9 lstep.
      name_spm R.
      apply evt_done. unfold diag, diag_cannot_open. eapply (implM_bind_u usegs).
      { eapply EPR_OPEN; [ | reflexivity | reflexivity | reflexivity | exact STRS | exact HNUL | exact (proj1 HPL) | exact (proj2 HPL) | intros a Ha; left; lia | exact HP47 ].
        std_pre_tac G' ST' MI Hspm. }
      intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13de8)) with (Z_to_bv 64 0x13de8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unname_spm.
      unfold implM. iprefix. lstep.
      apply evt_done. apply (implM_ret usegs). apply evt_done.
      unfold RAX, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G2|]. split; [exact MI2| exact ST2].
    - (* [comment removed for export] *)
      unfold open_ret. unname_spm.
      cbv beta iota. unfold implM. iprefix. lstep. if_false_by (ltz_cond_false fd ltac:(lia)). do 4 lstep.
      name_spm R.
      apply evt_done. eapply (implM_bind_u usegs).
      { eapply MALLOC; [ | reflexivity | lia]. std_pre_tac G' ST' MI Hspm. }
      intros r s' ms' PO. unfold malloc_post in PO. destruct_exs PO. destruct PO as (-> & MI1 & ST1 & AG1 & CASES). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13bd8)) with (Z_to_bv 64 0x13bd8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ AG1) in STR; [|lia].
      apply (keeps_bytes_at_stack _ _ _ _ _ _ AG1) in STRS; [|lia].
      unname_spm.
      destruct r as [q|].
      + destruct CASES as (A & junk & -> & G1 & BLK & BOK & HADDR).
        pose proof BOK as BOK'. unfold block_ok in BOK'. cbn [cb_addr cb_size fst snd] in BOK'. destruct BOK' as (B1 & B2 & B3 & B4 & B5 & B6).
        (* [comment removed for export] *)
        cbv beta iota. unfold implM. iprefix. lstep. if_false_by (eqz_cond_false A ltac:(lia)). lstep. lstep. lstep. lstep.
        apply evt_done. eapply (implM_bind_u usegs _ _ s' (LX R fd P1 argv1 slack1)).
        { eapply loop_spec; [| exact HNUL | exact HPL | exact HP47].
          unfold LH. cbn [rd_buf rd_cap rd_len rd_chunks rd_content concat].
          repeat (lazymatch goal with |- @ex (list byte) _ => exists (@nil byte) | |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|].
          split; [right; split; reflexivity|].
          split.
          { split; [exact G1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR|].
            split; [exists junk; apply rw_cells_nil_CB; exact BLK|].
            cbn [length Z.of_nat]. split; [lia|]. split; [unfold MAX_INPUT; lia|]. split; [exists 0%Z; reflexivity| assumption]. }
          split; [reflexivity|]. split; [reflexivity|].
          split; [exact STRS|]. split; [lia| lia]. }
        intros res s'' ms'' LXH. destruct res as [|q' content].
        * cbv beta iota. apply (implM_ret usegs). apply evt_done. exact LXH.
        * destruct LXH as (ra' & gp' & y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & y3 & y4 & y5 & y6 & F' & fc' & m'' & A' & cap' & CBs'
                            & -> & MB & HC).
          destruct MB as (G2 & MI2 & ST2 & (h0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & FR2) & (junk2 & BUF2) & HLC2 & HCAP2 & HJ2 & AL16b).
          clear CM1 CM2. destruct (GI_core K _ _ _ _ G2) as ((t' & e' & _ & ERR2 & _) & _ & _ & (CM1 & CM2 & _) & _ & _).
          destruct (GI_blocks K _ _ _ _ G2) as [BO2 _]. apply Forall_cons_iff in BO2 as [Bq2 _].
          unfold block_ok in Bq2; cbn [cb_addr cb_size fst snd] in Bq2. destruct Bq2 as (D1 & D2 & D3 & D4 & D5 & D6).
          cbv beta iota. unfold implM. iprefix. lstep. lstep.
          name_spm R.
          apply evt_done. eapply (implM_msys_of_enode usegs); [reflexivity | |].
          { eapply (close_spec _ spm _ (rc_tp R)) with (lo := rc_lo R);
              [ rewrite Hspm; exact ST2 | exact ERR2 | exact MI2 | reflexivity | lia | rewrite Hspm, ELO; lia | rewrite Hspm; unfold utp in *; lia | unfold utp in *; lia ]. }
          intros r ms' PO. unfold close_post in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI3 & ST3 & ERR3).
          replace (ret_pc (Z_to_bv 64 0x13c80)) with (Z_to_bv 64 0x13c80) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
          change (bv_unsigned (rc_tp R)) with (utp R) in *.
          lazymatch type of MU with munch _ ?ma ?mb => transport_after_call usegs ma mb MU WM end.
          apply (munch_weaken _ [(utp R - 164, utp R - 160); (bv_unsigned spm - 32, bv_unsigned spm)]%Z) in MU.
          2:{ unfold sub_fp. cbn [outside]. intros xx Hxx. repeat split; try exact I; lia. }
          assert (G3 : GI K R s'' [(q', A', cap')] ltac:(lazymatch type of WM with wmono _ _ ?mb => exact mb end)).
          { eapply (GI_client_frame_errno K HFL SFL); [exact G2 | exact MU | exact WM | | exact ERR3].
            constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia| constructor]. }
          unname_spm.
          apply (implM_ret usegs). apply evt_done.
          unfold RAX. repeat (lazymatch goal with |- ex _ => eexists end).
          split; [reflexivity|]. split; [| exact HC].
          split; [exact G3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exists h0, g1, g2, g3, g4, g5, g6, g7, g8; exact FR2|].
          split; [exists junk2; exact BUF2|]. split; [exact HLC2|]. split; [exact HCAP2|]. split; [exact HJ2| exact AL16b].
      + (* [comment removed for export] *)
        destruct CASES as [-> G1]. clear CM1 CM2. destruct (GI_core K _ _ _ _ G1) as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
        cbv beta iota. unfold implM. iprefix. astep. do 9 lstep.
        destruct MSG_OOM_ok as (RB & EM & LM).
        name_spm R.
        apply evt_done. unfold diag, diag_oom. rewrite <- EM. eapply (implM_bind_u usegs).
        { eapply EFW; [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI1 | exact RB | lia | rewrite LM; lia] | rewrite LM; lia | rewrite LM; lia].
          std_pre_tac G1 ST1 MI1 Hspm. }
        intros [] s'' ms'' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI3 & ST3 & AG3 & G3). clear MI1.
        replace (ret_pc (Z_to_bv 64 0x13e0c)) with (Z_to_bv 64 0x13e0c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        unname_spm.
        apply (implM_ret usegs). apply evt_done.
        unfold RAX, at_exit2. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G3|]. split; [exact MI3| exact ST3].
  Qed.
  End Sz30.
  Lemma read_all_spec : ltac:(let t := eval cbv delta [read_all_spec__stmt] in read_all_spec__stmt in exact t).
  Proof using EFW EPR_BIG EPR_OPEN EPR_READ FREE HFL MALLOC SFL SITE_RS. intros R s ms argv1. ltac2:(SecDiet.SzSec.closeP 'read_all_spec__body "vvvv"). Qed.
End Main.

End WithCeil.
End TwB.
End F_main_A.

(* [comment removed for export] *)
Module F_main_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.CallKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_target_run OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_main_A.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma forall_range : forall (f : Z -> bool) (n : nat),
  forallb f (map Z.of_nat (seq 0 n)) = true -> forall z, (0 <= z < Z.of_nat n)%Z -> f z = true.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros f n Hf z Hz. rewrite forallb_forall in Hf. apply Hf. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

Lemma hdr_hi : forall c1 : byte,
  Z.shiftr ((Z.shiftl (bv_unsigned (sxb c1)) 57) mod 18446744073709551616) 49 = ((bv_unsigned c1) mod 128 * 256)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros c1. unfold sxb. rewrite unsigned_lit_wrap. unfold bv_signed.
  pose proof (bv_unsigned_in_range 8 c1) as R. unfold bv_modulus in R. cbn in R.
  generalize dependent R. generalize (bv_unsigned c1). intros u R.
  pose proof (forall_range (fun u => Z.eqb (Z.shiftr ((Z.shiftl ((bv_swrap 8 u) mod 2^64) 57) mod 18446744073709551616) 49) (u mod 128 * 256)) 256 ltac:(vm_compute; reflexivity) u ltac:(cbn; lia)) as E.
  apply Z.eqb_eq in E. exact E.
Qed.

Lemma lor_disjoint8 : forall m u0, (0 <= m < 128)%Z -> (0 <= u0 < 256)%Z -> Z.lor (m * 256) u0 = (m * 256 + u0)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros m u0 Hm Hu.
  pose proof (forall_range (fun m => forallb (fun u0 => Z.eqb (Z.lor (m * 256) u0) (m * 256 + u0)) (map Z.of_nat (seq 0 256))) 128 ltac:(vm_compute; reflexivity) m ltac:(cbn; lia)) as E.
  cbn beta in E. pose proof (forall_range _ 256 E u0 ltac:(cbn; lia)) as E2. apply Z.eqb_eq in E2. exact E2.
Qed.

Lemma land_7fff : forall u0 u1, (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> Z.land (u0 + u1 * 256) 32767 = (u1 mod 128 * 256 + u0)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros. change 32767%Z with (2^15 - 1)%Z. rewrite zb_land_mask by lia. change (2^15)%Z with 32768%Z.
  rewrite (Z.div_mod u1 128) at 1 by lia.
  replace (u0 + (128 * (u1 / 128) + u1 mod 128) * 256)%Z with ((u1 mod 128 * 256 + u0) + (u1 / 128) * 32768)%Z by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound u1 128). lia.
Qed.

Lemma testbit15 : forall u0 u1, (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> Z.testbit (u0 + u1 * 256) 15 = (128 <=? u1)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros. destruct (Z.leb_spec 128 u1).
  - apply Z.testbit_true; [lia|]. change (2^15)%Z with 32768%Z.
    replace ((u0 + u1 * 256) / 32768)%Z with 1%Z; [reflexivity|]. Z.div_mod_to_equations. lia.
  - apply Z.testbit_false; [lia|]. change (2^15)%Z with 32768%Z.
    replace ((u0 + u1 * 256) / 32768)%Z with 0%Z; [reflexivity|]. Z.div_mod_to_equations. lia.
Qed.

Definition sxb_ltz__stmt : Prop := forall c1 : byte, bv_lts (sxb c1) (Z_to_bv 64 0) = (128 <=? bv_unsigned c1)%Z.
Section Sz6.
Variables c1 : ltac2:(SecDiet.SzSec.tyM 'sxb_ltz__stmt "v" @c1).
Lemma sxb_ltz__body : ltac2:(SecDiet.SzSec.bodyP 'sxb_ltz__stmt "v").
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
 rewrite bv_lts_zero_r. unfold sxb. rewrite unsigned_lit_wrap. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  pose proof (bv_unsigned_in_range 8 c1) as R. unfold bv_modulus in R. cbn in R.
  change (Z.of_N 8) with 8%Z. change (2^8)%Z with 256%Z. cbn [Z.div Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  destruct (Z.leb_spec 128 (bv_unsigned c1)).
  - apply Z.leb_le. Z.div_mod_to_equations. lia.
  - apply Z.leb_gt. Z.div_mod_to_equations. lia.
Qed.
End Sz6.
Lemma sxb_ltz : ltac:(let t := eval cbv delta [sxb_ltz__stmt] in sxb_ltz__stmt in exact t).
Proof using CEILV. intros c1. ltac2:(SecDiet.SzSec.closeP 'sxb_ltz__body "v"). Qed.

Section MainB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites_of : Z -> stack_site -> Z) (sites : stack_site -> Z).
  Variable SEF : Z.
  Hypothesis SEF_range : (0 <= SEF <= 0x10000)%Z.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HCB : heap_cb_law K.
  Hypothesis SCB : stdio_cb_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOC : malloc_stmt HO K.
  Hypothesis FREE : free_stmt HO K.
  Hypothesis FUZZ : fuzz_one_stmt HO K sites_of sites.
  Hypothesis VPR : vprintf_d_stmt K.
  Hypothesis EPR_USAGE : eprintf_s_stmt47 K FMT_USAGE pieces_usage.
  Hypothesis EPR_OPEN : eprintf_s_stmt47 K FMT_CANNOT_OPEN pieces_cannot_open.
  Hypothesis EPR_READ : eprintf_s_stmt47 K FMT_READ_ERROR pieces_read_error.
  Hypothesis EPR_BIG : eprintf_i_stmt K FMT_TOO_BIG 0x4000000 pieces_too_big.
  Hypothesis EFW : efwrite_stmt K.
  Hypothesis SITE_RS : sites SiteReadStage = 0x23989%Z.   (* [comment removed for export] *)

  Ltac name_spm R :=
    remember (Z_to_bv 64 (usp0 R + -128)) as spm eqn:Espm;
    assert (Hspm : bv_unsigned spm = (usp0 R + -128)%Z) by (rewrite Espm; apply unsigned_lit; lia).
  Ltac unname_spm := match goal with H : bv_unsigned ?s = (usp0 _ + -128)%Z |- _ => is_var s; rewrite H in *; subst s; clear H end.
  Ltac aln16 := match goal with H : (usp0 ?R mod 16 = 0)%Z |- _ => generalize H; clear; intros; Z.div_mod_to_equations; lia end.
  Ltac std_pre_tac G ST MI Hspm :=
    split; [exact G|]; split; [rewrite Hspm; exact ST|]; split; [unfold rc_lo; lia|];
    split; [unfold TARGET_RUN_STACK; unfold rc_lo, STDIO_STACK, MALLOC_STACK, FREE_STACK, FUZZ_STACK; lia|];
    split; [unfold rc_spmain; lia|]; split; [exact MI|]; split; [reflexivity| rewrite Hspm; aln16].

  (* [comment removed for export] *)
  Definition free_ret_spec__stmt : Prop := forall R s (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (q : hptr) (A cap code : Z),
    rc_cb R = false ->
    GI K R s [(q, A, cap)] m -> mem_inv ssegs m -> stk ssegs m (rc_lo R) (usp0 R + -128) -> mframe R m -> (usp0 R mod 16 = 0)%Z ->
    implM ssegs (pfree HO q ;;; mret code) s (main_post K SEF)
      (MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13d04) fc None m (seg_rom ssegs)).
  Section Sz7.
  Variables R s ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q A cap code : ltac2:(SecDiet.SzSec.tyM 'free_ret_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @R).
  Lemma free_ret_spec__body : ltac2:(SecDiet.SzSec.bodyP 'free_ret_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FREE SEF_range. pin_using (fun (FREE SEF_range : unit) => tt). ceil_facts.
    intros Hcb G MI ST (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) AL16.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. assert (ELO : rc_lo R = (usp0 R - 8388608)%Z) by reflexivity.
    pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0. fold (usp0 R) in RSP0.
    destruct (GI_blocks K _ _ _ _ G) as [BO _]. apply Forall_cons_iff in BO as [Bq _].
    unfold block_ok in Bq; cbn [cb_addr cb_size fst snd] in Bq. destruct Bq as (B1 & B2 & B3 & B4 & B5 & B6).
    unfold implM. iprefix. lstep. lstep.
    name_spm R.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply FREE with (C1 := []) (C2 := []); [| reflexivity]. std_pre_tac G ST MI Hspm. }
    intros [] s' ms' PO. unfold free_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
    cbn [app] in AG2, G2.
    replace (ret_pc (Z_to_bv 64 0x13d0c)) with (Z_to_bv 64 0x13d0c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
    unname_spm.
    unfold implM. iprefix. do 12 lstep.
    replace (ret_pc (Z_to_bv 64 0x17f08)) with (Z_to_bv 64 0x17f08) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lstep.
    apply evt_done. apply (implM_ret ssegs). apply evt_done. unfold main_post.
    release_frame FR ST2 (usp0 R + -48)%Z.
    eapply GI_at_exit; [exact G2 | exact Hcb | exact MI2 | rewrite unsigned_lit by lia; exact ST2 | unfold rc_lo; lia | rewrite unsigned_lit by lia; unfold rc_lo; lia | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity].
  Qed.
  End Sz7.
  Lemma free_ret_spec : ltac:(let t := eval cbv delta [free_ret_spec__stmt] in free_ret_spec__stmt in exact t).
  Proof using FREE SEF_range. intros R s ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q A cap code. ltac2:(SecDiet.SzSec.closeP 'free_ret_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma geu_cond_true : forall x y, (0 <= y <= x)%Z -> (x < 2^64)%Z -> negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. rewrite ltu_cond_false by lia. reflexivity. Qed.
  Lemma geu_cond_false : forall x y, (0 <= x < y)%Z -> (y < 2^64)%Z -> negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = false.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. rewrite ltu_cond_true by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition tail_spec__stmt : Prop := forall R s ms q content,
    rc_cb R = false ->
    sites = sites_of (usp0 R - 208) ->
    RAX K R (RdDone q content) s ms ->
    implM ssegs (let len := zlength content in
                 if len <? HDR_MIN then diag DShortHdr ;;; pfree HO q ;;; mret 2
                 else let cfg_word := le16 content in
                      let count_allocs := Z.testbit cfg_word 15 in
                      let config_len := Z.land cfg_word 0x7fff in
                      if len <? HDR_MIN + config_len then diag DCfgOverrun ;;; pfree HO q ;;; mret 2
                      else let config := firstn (Z.to_nat config_len) (skipn 2 content) in
                           let payload := skipn (Z.to_nat (6 + config_len)) content in
                           status <- run HO fo_nop sites config payload ;;
                           (let status' := (if count_allocs then 0 else status)%Z in pfree HO q ;;; mret status'))%Z
      s (main_post K SEF) ms.
  Section Sz10.
  Variables R s ms q content : ltac2:(SecDiet.SzSec.tyM 'tail_spec__stmt "vvvvv" @R).
  Lemma tail_spec__body : ltac2:(SecDiet.SzSec.bodyP 'tail_spec__stmt "vvvvv").
  Proof using EFW FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL VPR. pin_using (fun (EFW FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL VPR : unit) => tt). ceil_facts.
    intros Hcb SITES RX.
    destruct RX as (ra & gp & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & A & cap & CBs
                    & -> & MB & ->).
    destruct MB as (G & MI & ST & FRm & (junk & BUF) & HLC & HCAP & HJ & AL16).
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. assert (ELO : rc_lo R = (usp0 R - 8388608)%Z) by reflexivity.
    pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0. fold (usp0 R) in RSP0.
    destruct (GI_core K _ _ _ _ G) as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
    destruct (GI_blocks K _ _ _ _ G) as [BO _]. apply Forall_cons_iff in BO as [Bq _].
    unfold block_ok in Bq; cbn [cb_addr cb_size fst snd] in Bq. destruct Bq as (B1 & B2 & B3 & B4 & B5 & B6).
    unfold zlength, of_bytes at 1. rewrite length_map. set (len := Z.of_nat (length CBs)) in *.
    cbv zeta. unfold HDR_MIN.
    unfold implM. iprefix. lstep. lstep.
    destruct (Z_lt_le_dec len 6) as [SHORT|LONG].
    - (* [comment removed for export] *)
      replace (len <? 6)%Z with true by (symmetry; apply Z.ltb_lt; exact SHORT).
      if_true_by (geu_cond_true 5 len ltac:(lia) ltac:(lia)).
      do 9 lstep.
      destruct MSG_SHORT_HDR_ok as (RB & EM & LM).
      name_spm R.
      apply evt_done. unfold diag, diag_short_hdr. rewrite <- EM. eapply (implM_bind ssegs).
      { eapply EFW; [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI | exact RB | lia | rewrite LM; lia] | rewrite LM; lia | rewrite LM; lia].
        std_pre_tac G ST MI Hspm. }
      intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13d04)) with (Z_to_bv 64 0x13d04) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      destruct FRm as (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR). apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
      unname_spm.
      eapply free_ret_spec; [exact Hcb | exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact AL16].
    - (* [comment removed for export] *)
      replace (len <? 6)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      if_false_by (geu_cond_false 5 len ltac:(lia) ltac:(lia)).
      destruct CBs as [|c0 [|c1 rest]]; [subst len; cbn in LONG; lia..|].
      pose proof BUF as BUF'. apply (proj1 (rw_cells_app ssegs _ _ [_] [_])) in BUF' as [BUF1 _].
      assert (BY : bytes_at ssegs m A (c0 :: c1 :: rest)).
      { destruct BUF1 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
      pose proof (bytes_at_read ssegs _ A _ 0 1 BY ltac:(lia) ltac:(cbn; lia)) as HR0. change (Z.to_nat 0) with 0%nat in HR0. cbn [firstn skipn] in HR0. rewrite Z.add_0_r in HR0.
      pose proof (bytes_at_read ssegs _ A _ 1 1 BY ltac:(lia) ltac:(cbn; lia)) as HR1. change (Z.to_nat 1) with 1%nat in HR1. cbn [firstn skipn] in HR1.
      pose proof (bv_unsigned_in_range 8 c0) as RC0. pose proof (bv_unsigned_in_range 8 c1) as RC1. unfold bv_modulus in RC0, RC1. cbn in RC0, RC1.
      lstep. lstep. lstep. lstep. lstep. lstep.
      rewrite hdr_hi. rewrite lor_disjoint8 by (pose proof (Z.mod_pos_bound (bv_unsigned c1) 128); lia).
      assert (EL16 : le16 (of_bytes (c0 :: c1 :: rest)) = (bv_unsigned c0 + bv_unsigned c1 * 256)%Z) by reflexivity.
      rewrite EL16. rewrite land_7fff by lia. rewrite testbit15 by lia.
      set (L := (bv_unsigned c1 mod 128 * 256 + bv_unsigned c0)%Z) in *.
      assert (HL : (0 <= L < 32768)%Z) by (pose proof (Z.mod_pos_bound (bv_unsigned c1) 128); lia).
      unfold of_bytes. rewrite length_map. fold len.
      lstep.
      destruct (Z_lt_le_dec len (6 + L)) as [OVR|OK].
      + (* [comment removed for export] *)
        replace (len <? 6 + L)%Z with true by (symmetry; apply Z.ltb_lt; exact OVR).
        if_true_by (ltu_cond_true len (L + 6)%Z ltac:(lia) ltac:(lia)).
        do 8 lstep.
        destruct MSG_CFG_OVERRUN_ok as (RB & EM & LM).
        name_spm R.
        apply evt_done. unfold diag, diag_cfg_overrun. rewrite <- EM. eapply (implM_bind ssegs).
        { eapply EFW; [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI | exact RB | lia | rewrite LM; lia] | rewrite LM; lia | rewrite LM; lia].
          std_pre_tac G ST MI Hspm. }
        intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
        replace (ret_pc (Z_to_bv 64 0x13d04)) with (Z_to_bv 64 0x13d04) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        destruct FRm as (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR). apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
        unname_spm.
        eapply free_ret_spec; [exact Hcb | exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact AL16].
      + (* [comment removed for export] *)
        replace (len <? 6 + L)%Z with false by (symmetry; apply Z.ltb_ge; lia).
        if_false_by (ltu_cond_false len (L + 6)%Z ltac:(lia) ltac:(lia)).
        assert (exists d0 d1 d2 d3 rest', skipn (Z.to_nat (2 + L)) (c0 :: c1 :: rest) = d0 :: d1 :: d2 :: d3 :: rest') as (d0 & d1 & d2 & d3 & rest' & ED).
        { pose proof (length_skipn (Z.to_nat (2 + L)) (c0 :: c1 :: rest)) as LS.
          destruct (skipn (Z.to_nat (2 + L)) (c0 :: c1 :: rest)) as [|d0 [|d1 [|d2 [|d3 rest']]]]; cbn [length] in LS, LONG, OK; try (subst len; cbn [length] in *; lia).
          repeat eexists. }
        assert (BYp : bytes_at ssegs m (A + (2 + L)) (d0 :: d1 :: d2 :: d3 :: rest')).
        { rewrite <- ED. pose proof BY as BY2. rewrite <- (firstn_skipn (Z.to_nat (2 + L)) (c0 :: c1 :: rest)) in BY2.
          apply bytes_at_app in BY2 as [_ X]. rewrite length_firstn in X.
          replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + L)) (length (c0 :: c1 :: rest))))%Z with (A + (2 + L))%Z in X by (subst len; lia). exact X. }
        pose proof (bytes_at_read ssegs _ _ _ 0 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB0. change (Z.to_nat 0) with 0%nat in HB0. cbn [firstn skipn] in HB0.
        pose proof (bytes_at_read ssegs _ _ _ 1 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB1. change (Z.to_nat 1) with 1%nat in HB1. cbn [firstn skipn] in HB1.
        pose proof (bytes_at_read ssegs _ _ _ 2 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB2. change (Z.to_nat 2) with 2%nat in HB2. cbn [firstn skipn] in HB2.
        pose proof (bytes_at_read ssegs _ _ _ 3 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB3. change (Z.to_nat 3) with 3%nat in HB3. cbn [firstn skipn] in HB3.
        do 6 lstep. do 16 lstep.
        (* [comment removed for export] *)
        destruct FRm as (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR).
        assert (Elen : len = Z.of_nat (length (c0 :: c1 :: rest))) by reflexivity. clearbody len.
        assert (HINB : forall a, (A <= a < A + Z.of_nat (length (c0 :: c1 :: rest)))%Z -> in_block [(q, A, cap)] a).
        { intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        name_spm R.
        apply evt_done. eapply (implM_bind ssegs).
        { eapply (target_run_proof HO K sites_of sites HFL SFL HCB SCB MALLOC FREE FUZZ VPR) with (L := L) (A := A);
            [ | exact Hcb | rewrite Hspm, SITES; f_equal; lia | exact BY | lia | lia | unfold MAX_INPUT in *; lia | exact HINB | reflexivity | reflexivity | f_equal; lia | f_equal; lia ].
          std_pre_tac G ST MI Hspm. }
        intros r s' ms' PO. unfold target_run_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2 & Hr). clear MI.
        replace (ret_pc (Z_to_bv 64 0x13c84)) with (Z_to_bv 64 0x13c84) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
        unname_spm.
        cbv zeta. unfold implM. iprefix. lstep.
        destruct (Z.leb_spec 128 (bv_unsigned c1)) as [CA|NCA].
        * (* [comment removed for export] *)
          replace (128 <=? bv_unsigned c1)%Z with true by (symmetry; apply Z.leb_le; exact CA).
          if_true_by (eq_trans (sxb_ltz c1) (proj2 (Z.leb_le _ _) CA)).
          do 5 lstep. astep.
          apply evt_done. eapply free_ret_spec; [exact Hcb | exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact AL16].
        * replace (128 <=? bv_unsigned c1)%Z with false by (symmetry; apply Z.leb_gt; exact NCA).
          if_false_by (eq_trans (sxb_ltz c1) (proj2 (Z.leb_gt _ _) NCA)).
          lstep. lstep.
          apply evt_done. eapply free_ret_spec; [exact Hcb | exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact AL16].
  Qed.
  End Sz10.
  Lemma tail_spec : ltac:(let t := eval cbv delta [tail_spec__stmt] in tail_spec__stmt in exact t).
  Proof using EFW FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL VPR. intros R s ms q content. ltac2:(SecDiet.SzSec.closeP 'tail_spec__body "vvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition main_spec__stmt : Prop := forall R s ms,
    rc_cb R = false ->
    sites = sites_of (usp0 R - 208) ->
    main_entry K R s ms ->
    implM ssegs (main_prog HO fo_nop sites (argv_Z (rc_argv R))) s (main_post K SEF) ms.
  Section Sz11.
  Variables R s ms : ltac2:(SecDiet.SzSec.tyM 'main_spec__stmt "vvv" @R).
  Lemma main_spec__body : ltac2:(SecDiet.SzSec.bodyP 'main_spec__stmt "vvv").
  Proof using EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL SITE_RS VPR. pin_using (fun (EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL SITE_RS VPR : unit) => tt). ceil_facts.
    intros Hcb SITES ME.
    destruct (Z.eq_dec (Z.of_nat (length (rc_argv R))) 2) as [E2|NE2].
    2:{ exact (main_usage HO K sites SEF SEF_range HFL SFL EPR_USAGE R s ms Hcb ME NE2). }
    destruct ME as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & -> & G & MI & ST & VA & AL16 & STKTOP).
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__.
    pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0. fold (usp0 R) in RSP0.
    destruct (rc_argv R) as [|av0 [|av1 [|av2 avr]]] eqn:EARGV; try (cbn in E2; lia).
    unfold main_prog, main_model. unfold argv_Z at 1. rewrite length_map.
    replace (Z.of_nat (length [av0; av1]) =? 2)%Z with true by reflexivity. cbn [negb nth argv_Z map].
    pose proof (munch_refl [(usp0 R - 128, usp0 R - 48)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold rc_lo in ST. unfold implM. iprefix.
    carve_frame 80%nat ST.
    do 11 lstep.
    lstep. if_false_by (eq_cond 2).
    assert (G1 : GI K R s [] ltac:(lazymatch type of MU with munch _ _ ?mb => exact mb end)).
    { eapply (GI_client_frame K HFL SFL); [exact G | exact MU | exact WM |].
      constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia | constructor]. }
    clear MU WM.
    apply evt_done. eapply (implM_bind ssegs _ _ s (RAX K R)).
    - eapply (read_all_spec HO K sites HFL SFL MALLOC FREE EPR_OPEN EPR_READ EPR_BIG EFW SITE_RS); [| rewrite EARGV; reflexivity | rewrite EARGV; exact VA].
      unfold P2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G1|]. split; [exact MI|]. split; [exact ST|].
      split; [eexists _, _, _, _, _, _, _, _, _; exact FR|]. split; [exact AL16| first [exact STKTOP | rewrite EARGV; exact STKTOP]].
    - intros res s' ms' RX. destruct res as [|q content].
      + cbv beta iota. apply (implM_ret ssegs).
        eapply (at_exit2_exit K SEF SEF_range R s' ms' (fun _ s0 ms0 => main_post K SEF 2 s0 ms0)); [exact Hcb | exact RX | intros ms0 HP; exact HP].
      + cbv beta iota. apply (tail_spec R); [exact Hcb | exact SITES| exact RX].
  Qed.
  End Sz11.
  Theorem main_spec : ltac:(let t := eval cbv delta [main_spec__stmt] in main_spec__stmt in exact t).
  Proof using EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL SITE_RS VPR. intros R s ms. ltac2:(SecDiet.SzSec.closeP 'main_spec__body "vvv"). Qed.
End MainB.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.CallKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_target_run.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_main_A.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma forall_range : forall (f : Z -> bool) (n : nat),
  forallb f (map Z.of_nat (seq 0 n)) = true -> forall z, (0 <= z < Z.of_nat n)%Z -> f z = true.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros f n Hf z Hz. rewrite forallb_forall in Hf. apply Hf. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

Lemma hdr_hi : forall c1 : byte,
  Z.shiftr ((Z.shiftl (bv_unsigned (sxb c1)) 57) mod 18446744073709551616) 49 = ((bv_unsigned c1) mod 128 * 256)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros c1. unfold sxb. rewrite unsigned_lit_wrap. unfold bv_signed.
  pose proof (bv_unsigned_in_range 8 c1) as R. unfold bv_modulus in R. cbn in R.
  generalize dependent R. generalize (bv_unsigned c1). intros u R.
  pose proof (forall_range (fun u => Z.eqb (Z.shiftr ((Z.shiftl ((bv_swrap 8 u) mod 2^64) 57) mod 18446744073709551616) 49) (u mod 128 * 256)) 256 ltac:(vm_compute; reflexivity) u ltac:(cbn; lia)) as E.
  apply Z.eqb_eq in E. exact E.
Qed.

Lemma lor_disjoint8 : forall m u0, (0 <= m < 128)%Z -> (0 <= u0 < 256)%Z -> Z.lor (m * 256) u0 = (m * 256 + u0)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros m u0 Hm Hu.
  pose proof (forall_range (fun m => forallb (fun u0 => Z.eqb (Z.lor (m * 256) u0) (m * 256 + u0)) (map Z.of_nat (seq 0 256))) 128 ltac:(vm_compute; reflexivity) m ltac:(cbn; lia)) as E.
  cbn beta in E. pose proof (forall_range _ 256 E u0 ltac:(cbn; lia)) as E2. apply Z.eqb_eq in E2. exact E2.
Qed.

Lemma land_7fff : forall u0 u1, (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> Z.land (u0 + u1 * 256) 32767 = (u1 mod 128 * 256 + u0)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros. change 32767%Z with (2^15 - 1)%Z. rewrite zb_land_mask by lia. change (2^15)%Z with 32768%Z.
  rewrite (Z.div_mod u1 128) at 1 by lia.
  replace (u0 + (128 * (u1 / 128) + u1 mod 128) * 256)%Z with ((u1 mod 128 * 256 + u0) + (u1 / 128) * 32768)%Z by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound u1 128). lia.
Qed.

Lemma testbit15 : forall u0 u1, (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> Z.testbit (u0 + u1 * 256) 15 = (128 <=? u1)%Z.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros. destruct (Z.leb_spec 128 u1).
  - apply Z.testbit_true; [lia|]. change (2^15)%Z with 32768%Z.
    replace ((u0 + u1 * 256) / 32768)%Z with 1%Z; [reflexivity|]. Z.div_mod_to_equations. lia.
  - apply Z.testbit_false; [lia|]. change (2^15)%Z with 32768%Z.
    replace ((u0 + u1 * 256) / 32768)%Z with 0%Z; [reflexivity|]. Z.div_mod_to_equations. lia.
Qed.

Definition sxb_ltz__stmt : Prop := forall c1 : byte, bv_lts (sxb c1) (Z_to_bv 64 0) = (128 <=? bv_unsigned c1)%Z.
Section Sz6.
Variables c1 : ltac2:(SecDiet.SzSec.tyM 'sxb_ltz__stmt "v" @c1).
Lemma sxb_ltz__body : ltac2:(SecDiet.SzSec.bodyP 'sxb_ltz__stmt "v").
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
 rewrite bv_lts_zero_r. unfold sxb. rewrite unsigned_lit_wrap. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  pose proof (bv_unsigned_in_range 8 c1) as R. unfold bv_modulus in R. cbn in R.
  change (Z.of_N 8) with 8%Z. change (2^8)%Z with 256%Z. cbn [Z.div Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  destruct (Z.leb_spec 128 (bv_unsigned c1)).
  - apply Z.leb_le. Z.div_mod_to_equations. lia.
  - apply Z.leb_gt. Z.div_mod_to_equations. lia.
Qed.
End Sz6.
Lemma sxb_ltz : ltac:(let t := eval cbv delta [sxb_ltz__stmt] in sxb_ltz__stmt in exact t).
Proof using CEILV. intros c1. ltac2:(SecDiet.SzSec.closeP 'sxb_ltz__body "v"). Qed.

Section MainB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites_of : Z -> stack_site -> Z) (sites : stack_site -> Z).
  Variable SEF : Z.
  Hypothesis SEF_range : (0 <= SEF <= 0x10000)%Z.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HCB : heap_cb_law K.
  Hypothesis SCB : stdio_cb_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis MALLOC : malloc_stmt HO K.
  Hypothesis FREE : free_stmt HO K.
  Hypothesis FUZZ : fuzz_one_stmt HO K sites_of sites.
  Hypothesis VPR : vprintf_d_stmt K.
  Hypothesis EPR_USAGE : eprintf_s_stmt47 K FMT_USAGE pieces_usage.
  Hypothesis EPR_OPEN : eprintf_s_stmt47 K FMT_CANNOT_OPEN pieces_cannot_open.
  Hypothesis EPR_READ : eprintf_s_stmt47 K FMT_READ_ERROR pieces_read_error.
  Hypothesis EPR_BIG : eprintf_i_stmt K FMT_TOO_BIG 0x4000000 pieces_too_big.
  Hypothesis EFW : efwrite_stmt K.
  Hypothesis SITE_RS : sites SiteReadStage = 0x24149%Z.   (* [comment removed for export] *)

  Ltac name_spm R :=
    remember (Z_to_bv 64 (usp0 R + -128)) as spm eqn:Espm;
    assert (Hspm : bv_unsigned spm = (usp0 R + -128)%Z) by (rewrite Espm; apply unsigned_lit; lia).
  Ltac unname_spm := match goal with H : bv_unsigned ?s = (usp0 _ + -128)%Z |- _ => is_var s; rewrite H in *; subst s; clear H end.
  Ltac aln16 := match goal with H : (usp0 ?R mod 16 = 0)%Z |- _ => generalize H; clear; intros; Z.div_mod_to_equations; lia end.
  Ltac std_pre_tac G ST MI Hspm :=
    split; [exact G|]; split; [rewrite Hspm; exact ST|]; split; [unfold rc_lo; lia|];
    split; [unfold TARGET_RUN_STACK; unfold rc_lo, STDIO_STACK, MALLOC_STACK, FREE_STACK, FUZZ_STACK; lia|];
    split; [unfold rc_spmain; lia|]; split; [exact MI|]; split; [reflexivity| rewrite Hspm; aln16].

  (* [comment removed for export] *)
  Definition free_ret_spec__stmt : Prop := forall R s (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (q : hptr) (A cap code : Z),
    rc_cb R = false ->
    GI K R s [(q, A, cap)] m -> mem_inv usegs m -> stk usegs m (rc_lo R) (usp0 R + -128) -> mframe R m -> (usp0 R mod 16 = 0)%Z ->
    implM usegs (pfree HO q ;;; mret code) s (main_post K SEF)
      (MS (mkR ra (Z_to_bv 64 (usp0 R + -128)) gp (rc_tp R) t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13d78) fc None m (seg_rom usegs)).
  Section Sz7.
  Variables R s ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q A cap code : ltac2:(SecDiet.SzSec.tyM 'free_ret_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @R).
  Lemma free_ret_spec__body : ltac2:(SecDiet.SzSec.bodyP 'free_ret_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FREE SEF_range. pin_using (fun (FREE SEF_range : unit) => tt). ceil_facts.
    intros Hcb G MI ST (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR) AL16.
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. assert (ELO : rc_lo R = (usp0 R - 8388608)%Z) by reflexivity.
    pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0. fold (usp0 R) in RSP0.
    destruct (GI_blocks K _ _ _ _ G) as [BO _]. apply Forall_cons_iff in BO as [Bq _].
    unfold block_ok in Bq; cbn [cb_addr cb_size fst snd] in Bq. destruct Bq as (B1 & B2 & B3 & B4 & B5 & B6).
    unfold implM. iprefix. lstep. lstep.
    name_spm R.
    apply evt_done. eapply (implM_bind usegs).
    { eapply FREE with (C1 := []) (C2 := []); [| reflexivity]. std_pre_tac G ST MI Hspm. }
    intros [] s' ms' PO. unfold free_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
    cbn [app] in AG2, G2.
    replace (ret_pc (Z_to_bv 64 0x13d80)) with (Z_to_bv 64 0x13d80) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
    unname_spm.
    unfold implM. iprefix. do 12 lstep.
    replace (ret_pc (Z_to_bv 64 0x186c8)) with (Z_to_bv 64 0x186c8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lstep.
    apply evt_done. apply (implM_ret usegs). apply evt_done. unfold main_post.
    release_frame FR ST2 (usp0 R + -48)%Z.
    eapply GI_at_exit; [exact G2 | exact Hcb | exact MI2 | rewrite unsigned_lit by lia; exact ST2 | unfold rc_lo; lia | rewrite unsigned_lit by lia; unfold rc_lo; lia | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity].
  Qed.
  End Sz7.
  Lemma free_ret_spec : ltac:(let t := eval cbv delta [free_ret_spec__stmt] in free_ret_spec__stmt in exact t).
  Proof using FREE SEF_range. intros R s ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q A cap code. ltac2:(SecDiet.SzSec.closeP 'free_ret_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma geu_cond_true : forall x y, (0 <= y <= x)%Z -> (x < 2^64)%Z -> negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. rewrite ltu_cond_false by lia. reflexivity. Qed.
  Lemma geu_cond_false : forall x y, (0 <= x < y)%Z -> (y < 2^64)%Z -> negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = false.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. rewrite ltu_cond_true by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition tail_spec__stmt : Prop := forall R s ms q content,
    rc_cb R = false ->
    sites = sites_of (usp0 R - 208) ->
    RAX K R (RdDone q content) s ms ->
    implM usegs (let len := zlength content in
                 if len <? HDR_MIN then diag DShortHdr ;;; pfree HO q ;;; mret 2
                 else let cfg_word := le16 content in
                      let count_allocs := Z.testbit cfg_word 15 in
                      let config_len := Z.land cfg_word 0x7fff in
                      if len <? HDR_MIN + config_len then diag DCfgOverrun ;;; pfree HO q ;;; mret 2
                      else let config := firstn (Z.to_nat config_len) (skipn 2 content) in
                           let payload := skipn (Z.to_nat (6 + config_len)) content in
                           status <- run HO fo_nop sites config payload ;;
                           (let status' := (if count_allocs then 0 else status)%Z in pfree HO q ;;; mret status'))%Z
      s (main_post K SEF) ms.
  Section Sz10.
  Variables R s ms q content : ltac2:(SecDiet.SzSec.tyM 'tail_spec__stmt "vvvvv" @R).
  Lemma tail_spec__body : ltac2:(SecDiet.SzSec.bodyP 'tail_spec__stmt "vvvvv").
  Proof using EFW FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL VPR. pin_using (fun (EFW FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL VPR : unit) => tt). ceil_facts.
    intros Hcb SITES RX.
    destruct RX as (ra & gp & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & A & cap & CBs
                    & -> & MB & ->).
    destruct MB as (G & MI & ST & FRm & (junk & BUF) & HLC & HCAP & HJ & AL16).
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__. assert (ELO : rc_lo R = (usp0 R - 8388608)%Z) by reflexivity.
    pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0. fold (usp0 R) in RSP0.
    destruct (GI_core K _ _ _ _ G) as (_ & _ & _ & (CM1 & CM2 & _) & _ & _).
    destruct (GI_blocks K _ _ _ _ G) as [BO _]. apply Forall_cons_iff in BO as [Bq _].
    unfold block_ok in Bq; cbn [cb_addr cb_size fst snd] in Bq. destruct Bq as (B1 & B2 & B3 & B4 & B5 & B6).
    unfold zlength, of_bytes at 1. rewrite length_map. set (len := Z.of_nat (length CBs)) in *.
    cbv zeta. unfold HDR_MIN.
    unfold implM. iprefix. lstep. lstep.
    destruct (Z_lt_le_dec len 6) as [SHORT|LONG].
    - (* [comment removed for export] *)
      replace (len <? 6)%Z with true by (symmetry; apply Z.ltb_lt; exact SHORT).
      if_true_by (geu_cond_true 5 len ltac:(lia) ltac:(lia)).
      do 9 lstep.
      destruct MSG_SHORT_HDR_ok as (RB & EM & LM).
      name_spm R.
      apply evt_done. unfold diag, diag_short_hdr. rewrite <- EM. eapply (implM_bind usegs).
      { eapply EFW; [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI | exact RB | lia | rewrite LM; lia] | rewrite LM; lia | rewrite LM; lia].
        std_pre_tac G ST MI Hspm. }
      intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
      replace (ret_pc (Z_to_bv 64 0x13d78)) with (Z_to_bv 64 0x13d78) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      destruct FRm as (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR). apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
      unname_spm.
      eapply free_ret_spec; [exact Hcb | exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact AL16].
    - (* [comment removed for export] *)
      replace (len <? 6)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      if_false_by (geu_cond_false 5 len ltac:(lia) ltac:(lia)).
      destruct CBs as [|c0 [|c1 rest]]; [subst len; cbn in LONG; lia..|].
      pose proof BUF as BUF'. apply (proj1 (rw_cells_app usegs _ _ [_] [_])) in BUF' as [BUF1 _].
      assert (BY : bytes_at usegs m A (c0 :: c1 :: rest)).
      { destruct BUF1 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
      pose proof (bytes_at_read usegs _ A _ 0 1 BY ltac:(lia) ltac:(cbn; lia)) as HR0. change (Z.to_nat 0) with 0%nat in HR0. cbn [firstn skipn] in HR0. rewrite Z.add_0_r in HR0.
      pose proof (bytes_at_read usegs _ A _ 1 1 BY ltac:(lia) ltac:(cbn; lia)) as HR1. change (Z.to_nat 1) with 1%nat in HR1. cbn [firstn skipn] in HR1.
      pose proof (bv_unsigned_in_range 8 c0) as RC0. pose proof (bv_unsigned_in_range 8 c1) as RC1. unfold bv_modulus in RC0, RC1. cbn in RC0, RC1.
      lstep. lstep. lstep. lstep. lstep. lstep.
      rewrite hdr_hi. rewrite lor_disjoint8 by (pose proof (Z.mod_pos_bound (bv_unsigned c1) 128); lia).
      assert (EL16 : le16 (of_bytes (c0 :: c1 :: rest)) = (bv_unsigned c0 + bv_unsigned c1 * 256)%Z) by reflexivity.
      rewrite EL16. rewrite land_7fff by lia. rewrite testbit15 by lia.
      set (L := (bv_unsigned c1 mod 128 * 256 + bv_unsigned c0)%Z) in *.
      assert (HL : (0 <= L < 32768)%Z) by (pose proof (Z.mod_pos_bound (bv_unsigned c1) 128); lia).
      unfold of_bytes. rewrite length_map. fold len.
      lstep.
      destruct (Z_lt_le_dec len (6 + L)) as [OVR|OK].
      + (* [comment removed for export] *)
        replace (len <? 6 + L)%Z with true by (symmetry; apply Z.ltb_lt; exact OVR).
        if_true_by (ltu_cond_true len (L + 6)%Z ltac:(lia) ltac:(lia)).
        do 8 lstep.
        destruct MSG_CFG_OVERRUN_ok as (RB & EM & LM).
        name_spm R.
        apply evt_done. unfold diag, diag_cfg_overrun. rewrite <- EM. eapply (implM_bind usegs).
        { eapply EFW; [ | reflexivity | rewrite LM; reflexivity | reflexivity | reflexivity | apply lit_bytes_at; [exact MI | exact RB | lia | rewrite LM; lia] | rewrite LM; lia | rewrite LM; lia].
          std_pre_tac G ST MI Hspm. }
        intros [] s' ms' PO. unfold out_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2). clear MI.
        replace (ret_pc (Z_to_bv 64 0x13d78)) with (Z_to_bv 64 0x13d78) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        destruct FRm as (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR). apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
        unname_spm.
        eapply free_ret_spec; [exact Hcb | exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact AL16].
      + (* [comment removed for export] *)
        replace (len <? 6 + L)%Z with false by (symmetry; apply Z.ltb_ge; lia).
        if_false_by (ltu_cond_false len (L + 6)%Z ltac:(lia) ltac:(lia)).
        assert (exists d0 d1 d2 d3 rest', skipn (Z.to_nat (2 + L)) (c0 :: c1 :: rest) = d0 :: d1 :: d2 :: d3 :: rest') as (d0 & d1 & d2 & d3 & rest' & ED).
        { pose proof (length_skipn (Z.to_nat (2 + L)) (c0 :: c1 :: rest)) as LS.
          destruct (skipn (Z.to_nat (2 + L)) (c0 :: c1 :: rest)) as [|d0 [|d1 [|d2 [|d3 rest']]]]; cbn [length] in LS, LONG, OK; try (subst len; cbn [length] in *; lia).
          repeat eexists. }
        assert (BYp : bytes_at usegs m (A + (2 + L)) (d0 :: d1 :: d2 :: d3 :: rest')).
        { rewrite <- ED. pose proof BY as BY2. rewrite <- (firstn_skipn (Z.to_nat (2 + L)) (c0 :: c1 :: rest)) in BY2.
          apply bytes_at_app in BY2 as [_ X]. rewrite length_firstn in X.
          replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + L)) (length (c0 :: c1 :: rest))))%Z with (A + (2 + L))%Z in X by (subst len; lia). exact X. }
        pose proof (bytes_at_read usegs _ _ _ 0 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB0. change (Z.to_nat 0) with 0%nat in HB0. cbn [firstn skipn] in HB0.
        pose proof (bytes_at_read usegs _ _ _ 1 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB1. change (Z.to_nat 1) with 1%nat in HB1. cbn [firstn skipn] in HB1.
        pose proof (bytes_at_read usegs _ _ _ 2 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB2. change (Z.to_nat 2) with 2%nat in HB2. cbn [firstn skipn] in HB2.
        pose proof (bytes_at_read usegs _ _ _ 3 1 BYp ltac:(lia) ltac:(cbn; lia)) as HB3. change (Z.to_nat 3) with 3%nat in HB3. cbn [firstn skipn] in HB3.
        do 6 lstep. do 16 lstep.
        (* [comment removed for export] *)
        destruct FRm as (j0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & FR).
        assert (Elen : len = Z.of_nat (length (c0 :: c1 :: rest))) by reflexivity. clearbody len.
        assert (HINB : forall a, (A <= a < A + Z.of_nat (length (c0 :: c1 :: rest)))%Z -> in_block [(q, A, cap)] a).
        { intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        name_spm R.
        apply evt_done. eapply (implM_bind usegs).
        { eapply (target_run_proof HO K sites_of sites HFL SFL HCB SCB MALLOC FREE FUZZ VPR) with (L := L) (A := A);
            [ | exact Hcb | rewrite Hspm, SITES; f_equal; lia | exact BY | lia | lia | unfold MAX_INPUT in *; lia | exact HINB | reflexivity | reflexivity | f_equal; lia | f_equal; lia ].
          std_pre_tac G ST MI Hspm. }
        intros r s' ms' PO. unfold target_run_post in PO. destruct_exs PO. destruct PO as (-> & MI2 & ST2 & AG2 & G2 & Hr). clear MI.
        replace (ret_pc (Z_to_bv 64 0x13cf8)) with (Z_to_bv 64 0x13cf8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
        unname_spm.
        cbv zeta. unfold implM. iprefix. lstep.
        destruct (Z.leb_spec 128 (bv_unsigned c1)) as [CA|NCA].
        * (* [comment removed for export] *)
          replace (128 <=? bv_unsigned c1)%Z with true by (symmetry; apply Z.leb_le; exact CA).
          if_true_by (eq_trans (sxb_ltz c1) (proj2 (Z.leb_le _ _) CA)).
          do 5 lstep. astep.
          apply evt_done. eapply free_ret_spec; [exact Hcb | exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact AL16].
        * replace (128 <=? bv_unsigned c1)%Z with false by (symmetry; apply Z.leb_gt; exact NCA).
          if_false_by (eq_trans (sxb_ltz c1) (proj2 (Z.leb_gt _ _) NCA)).
          lstep. lstep.
          apply evt_done. eapply free_ret_spec; [exact Hcb | exact G2 | exact MI2 | exact ST2 | exists j0, f1, f2, f3, f4, f5, f6, f7, f8; exact FR | exact AL16].
  Qed.
  End Sz10.
  Lemma tail_spec : ltac:(let t := eval cbv delta [tail_spec__stmt] in tail_spec__stmt in exact t).
  Proof using EFW FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL VPR. intros R s ms q content. ltac2:(SecDiet.SzSec.closeP 'tail_spec__body "vvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition main_spec__stmt : Prop := forall R s ms,
    rc_cb R = false ->
    sites = sites_of (usp0 R - 208) ->
    main_entry K R s ms ->
    implM usegs (main_prog HO fo_nop sites (argv_Z (rc_argv R))) s (main_post K SEF) ms.
  Section Sz11.
  Variables R s ms : ltac2:(SecDiet.SzSec.tyM 'main_spec__stmt "vvv" @R).
  Lemma main_spec__body : ltac2:(SecDiet.SzSec.bodyP 'main_spec__stmt "vvv").
  Proof using EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL SITE_RS VPR. pin_using (fun (EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL SITE_RS VPR : unit) => tt). ceil_facts.
    intros Hcb SITES ME.
    destruct (Z.eq_dec (Z.of_nat (length (rc_argv R))) 2) as [E2|NE2].
    2:{ exact (main_usage HO K sites SEF SEF_range HFL SFL EPR_USAGE R s ms Hcb ME NE2). }
    destruct ME as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & -> & G & MI & ST & VA & AL16 & STKTOP).
    pose proof (GI_spw K _ _ _ _ G) as SPW. pose proof (GI_ceil_lo K _ _ _ _ G) as CLO__. unfold rc_lo in CLO__.
    pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0. fold (usp0 R) in RSP0.
    destruct (rc_argv R) as [|av0 [|av1 [|av2 avr]]] eqn:EARGV; try (cbn in E2; lia).
    unfold main_prog, main_model. unfold argv_Z at 1. rewrite length_map.
    replace (Z.of_nat (length [av0; av1]) =? 2)%Z with true by reflexivity. cbn [negb nth argv_Z map].
    pose proof (munch_refl [(usp0 R - 128, usp0 R - 48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold rc_lo in ST. unfold implM. iprefix.
    carve_frame 80%nat ST.
    do 11 lstep.
    lstep. if_false_by (eq_cond 2).
    assert (G1 : GI K R s [] ltac:(lazymatch type of MU with munch _ _ ?mb => exact mb end)).
    { eapply (GI_client_frame K HFL SFL); [exact G | exact MU | exact WM |].
      constructor; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia | constructor]. }
    clear MU WM.
    apply evt_done. eapply (implM_bind usegs _ _ s (RAX K R)).
    - eapply (read_all_spec HO K sites HFL SFL MALLOC FREE EPR_OPEN EPR_READ EPR_BIG EFW SITE_RS); [| rewrite EARGV; reflexivity | rewrite EARGV; exact VA].
      unfold P2. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact G1|]. split; [exact MI|]. split; [exact ST|].
      split; [eexists _, _, _, _, _, _, _, _, _; exact FR|]. split; [exact AL16| first [exact STKTOP | rewrite EARGV; exact STKTOP]].
    - intros res s' ms' RX. destruct res as [|q content].
      + cbv beta iota. apply (implM_ret usegs).
        eapply (at_exit2_exit K SEF SEF_range R s' ms' (fun _ s0 ms0 => main_post K SEF 2 s0 ms0)); [exact Hcb | exact RX | intros ms0 HP; exact HP].
      + cbv beta iota. apply (tail_spec R); [exact Hcb | exact SITES| exact RX].
  Qed.
  End Sz11.
  Theorem main_spec : ltac:(let t := eval cbv delta [main_spec__stmt] in main_spec__stmt in exact t).
  Proof using EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE FREE FUZZ HCB HFL MALLOC SCB SEF_range SFL SITE_RS VPR. intros R s ms. ltac2:(SecDiet.SzSec.closeP 'main_spec__body "vvv"). Qed.
End MainB.

End WithCeil.
End TwB.
End F_main_B.

(* [comment removed for export] *)
Module GIInit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_main_A.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac cl_lit_hyps :=
  repeat match goal with
  | H : context [cells_size ?cs] |- _ =>
      tryif (match goal with H' := _ |- _ => constr_eq H' H end) then fail else
      (sl_spine_closed cs;
       let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
       change (cells_size cs) with n in H)
  end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac rimg_chunk segs NONE m A cs H ::=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nz := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells segs m A cs);
  [ apply (rw_cells_recast segs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 segs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nz in Ha; cbn [length outside] in Ha |- *; lia
      | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nz; lia ]
    | vm_compute; repeat split; exact I | vm_compute; reflexivity | vm_compute; reflexivity ]
  | ].
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition wimg (A : Z) (n : nat) : list byte := match image_bytes ssegs A n with Some bs => bs | None => [] end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition heap_init_mem (canary : word) (m : mem) : Prop :=
  rw_cells ssegs m 0x53d98 [C4 (Z_to_bv 64 0)]
  /\ bytes_at ssegs m 0x53da0 (repeat (Z_to_bv 8 0) 928) /\ wr_at ssegs m 0x53da0 928
  /\ rw_cells ssegs m 0x53d2b [C1 (Z_to_bv 8 0)]
  /\ rw_cells ssegs m 0x53d58 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells ssegs m 0x22620 [C8 (Z_to_bv 64 0x53d08)]
  /\ rw_cells ssegs m 0x53d08 [C8 canary]
  /\ rw_cells ssegs m 0x54140 [C4 (Z_to_bv 64 0)].     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition stdio_init_mem (m : mem) : Prop :=
  rw_cells ssegs m 0x23660 [CB 720 (wimg 0x23660 720)]
  /\ rw_cells ssegs m 0x54148 [CB 2088 (wimg 0x54148 2088)].

Section Init.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (h0 : H).
  (* [comment removed for export] *)
  Variable rnd0 : EntryDraw.

  (* [comment removed for export] *)
  Definition heap_init_law : Prop :=
    forall R m, rc_rnd R = rnd0 -> heap_init_mem (rc_canary R) m -> tls_block_ok (utp R - 200) -> 0x7fff80000000 <= usp0 R ->
      CEILZ <= rc_lo R ->
      mk_heap K (ho_pin HO (utp R - 200) h0) R [] m.
  Definition stdio_init_law : Prop :=
    forall R m, stdio_init_mem m -> mk_stdio K libc_init R [] m.

  Hypothesis HINIT : heap_init_law.
  Hypothesis SINIT : stdio_init_law.

  Lemma GI_init : forall sp0 argv envp uid hw tp ms,
    valid_sp sp0 -> valid_argv argv -> entry_stack_fits sp0 argv envp ->     (* [comment removed for export] *)
    at_main sp0 argv envp uid hw rnd0 tp ms ->
    main_entry K (mkRC sp0 argv envp uid hw rnd0 tp false) (set_tls_pin HO (bv_unsigned tp - 200) (ps_init h0)) ms.
  Proof using HINIT SINIT. pin_using (fun (HINIT SINIT : unit) => tt). ceil_facts.
    intros sp0 argv envp uid hw tp ms VSP VA FITS AM.
    pose proof (entry_bounds Plain.M.phdrs sp0 argv envp uid hw rnd0 VSP FITS) as [_ EB].
    pose proof (bsb_le_esi Plain.M.phdrs sp0 argv envp uid hw rnd0) as BLE. unfold sp_window_hi in EB.
    (* [comment removed for export] *)
    unfold at_main in AM. let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in AM.
    let x := fresh "sbl" in pose (x := 3616%nat); change 3616%nat with x in AM.
    let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 256); change (repeat (Z_to_bv 8 0) 256) with z in AM.
    destruct AM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & t & P0 & pg & m & -> & AM).
    destruct AM as (MI & ST & TB & TD & ERR & TD2 & CAN & DTV & TLS & DTVB & LC & TLL & SI & PG & HW & ENV & DS & GU & G0 & G1 & G2 & G3 & G4 & GG & GF & IA & FA & DSO & INI & FIN & EXL & ATX & STKB & STKW & HP0 & NONE & Ht & CLO).
    destruct VSP as (VL & VH & V16). unfold sp_window_lo, sp_window_hi in VL, VH.
    assert (SPW : (0x7fff80000000 <= bv_unsigned sp0)%Z) by exact VL.
    assert (SPH : (bv_unsigned sp0 <= 2^47)%Z) by exact VH.
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    (* [comment removed for export] *)
    Ltac none_range NONE m lo hi N :=
      assert (N : forall a : word, (lo <= bv_unsigned a < hi)%Z -> m a = None)
        by (intros a Ha; apply NONE; [lia| unfold crt_written; cbn [outside]; lia]).
    none_range NONE m 0x53d98 0x54148 N1.
    none_range NONE m 0x23660 0x23930 N2.
    none_range NONE m 0x54148 0x54970 N3.
    none_range NONE m 0x225b8 0x225f0 N4.
    none_range NONE m 0x22560 0x22570 N5.
    none_range NONE m 0x225f0 0x225f8 N6.
    none_range NONE m 0x33990 0x339c8 N7.
    none_range NONE m 0x53af8 0x53d00 N8.
    rimg_chunk ssegs N1 m 0x53d98%Z [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); CB 928 (repeat (Z_to_bv 8 0) 928)] HP1.
    rimg_chunk ssegs N1 m 0x54140%Z [C4 (Z_to_bv 64 0)] HREPL.
    rimg_chunk ssegs N2 m 0x23660%Z [CB 720 (wimg 0x23660 720)] SF1.
    rimg_chunk ssegs N3 m 0x54148%Z [CB 2088 (wimg 0x54148 2088)] SF2.
    rimg_chunk ssegs N4 m 0x225b8%Z [C8 (Z_to_bv 64 0x22560); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x22570); C8 (Z_to_bv 64 0x1496c); C8 (Z_to_bv 64 0x14694); C8 (Z_to_bv 64 0x148a8); C8 (Z_to_bv 64 0x14190)] M1.
    rimg_chunk ssegs N5 m 0x22560%Z [C8 (Z_to_bv 64 0x23660); C8 (Z_to_bv 64 0x23750)] M2.
    rimg_chunk ssegs N6 m 0x225f0%Z [C8 (Z_to_bv 64 0x22568)] M3.
    rimg_chunk ssegs N7 m 0x33990%Z [C1 (Z_to_bv 8 0); CB 15 (repeat (Z_to_bv 8 0) 15); CB 32 (repeat (Z_to_bv 8 0) 32); C8 (Z_to_bv 64 0)] HA.
    (* [comment removed for export] *)
    rimg_chunk ssegs N7 m 0x33990%Z [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 0)] FLG.
    rimg_chunk ssegs N8 m 0x53af8%Z [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 248 (repeat (Z_to_bv 8 0) 248); C8 (Z_to_bv 64 0); CB 248 (repeat (Z_to_bv 8 0) 248)] BLTN.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app ssegs m _ [_; _] [_])) in HP1 as [HPL HPC]. (sl_lit_sizes_in HPC; cbn [cells_size csize Nat.add] in HPC).
    apply rw_cells_split2 in HPL as [HPL _].
    destruct HPC as [[_ HPCB] HPCW]. (sl_lit_sizes_in HPCB; sl_lit_sizes_in HPCW; cbn [cells_bytes cbytes cells_size csize Nat.add] in HPCB, HPCW). rewrite app_nil_r in HPCB.
    apply (proj1 (rw_cells_app ssegs m _ [_; _] [_; _; _; _; _])) in M1 as [M1 M1c]. (sl_lit_sizes_in M1c; cbn [cells_size csize Nat.add] in M1c).
    apply (proj1 (rw_cells_app ssegs m _ [_] [_; _; _; _])) in M1c as [_ M1c]. (sl_lit_sizes_in M1c; cbn [cells_size csize Nat.add] in M1c).
    match type of M1c with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in M1c end.
    apply rw_cells_split2 in M1 as [M1a M1b]. cbn [csize] in M1b.
    apply rw_cells_split2 in M2 as [M2a M2b]. cbn [csize] in M2b.
    apply (proj1 (rw_cells_app ssegs m _ [_; _] [_; _])) in HA as [HA1 HA2]. (sl_lit_sizes_in HA2; cbn [cells_size csize Nat.add] in HA2).
    apply rw_cells_split2 in HA1 as [HA1 _]. apply rw_cells_split2 in HA2 as [HA2 HA3]. cbn [csize] in HA3.
    (* [comment removed for export] *)
    pose proof LC as LC'. unfold libc_cells in LC'.
    apply (proj1 (rw_cells_app ssegs m _ [_; _; _] _)) in LC' as [_ LC']. (sl_lit_sizes_in LC'; cbn [cells_size csize Nat.add] in LC').
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in LC' as [NL LC']. (sl_lit_sizes_in LC'; cbn [cells_size csize Nat.add] in LC').
    apply (proj1 (rw_cells_app ssegs m _ [_; _; _; _; _; _] _)) in LC' as [_ LC']. (sl_lit_sizes_in LC'; cbn [cells_size csize Nat.add] in LC').
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in LC' as [PS _].
    match type of NL with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in NL end.
    match type of PS with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in PS end.
    unfold main_entry. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    cbn [rc_sp0 rc_argv rc_envp rc_uid rc_hw rc_rnd rc_tp rc_cb usp0 rc_lo].
    split.
    { (* [comment removed for export] *)
      exists []. cbn [app ps_heap ps_libc ps_outfile ps_tls set_tls_pin set_tls set_heap ps_init utp rc_tp usp0 rc_sp0 rc_argv rc_envp rc_uid rc_hw rc_rnd rc_cb].
      split. { pose proof HINIT as HI. unfold heap_init_law in HI. apply (HI (mkRC sp0 argv envp uid hw rnd0 tp false) m); [reflexivity | | exact TB | exact SPW | unfold rc_lo, usp0; cbn [rc_sp0]; exact CLO]. unfold heap_init_mem, rc_canary; cbn [rc_rnd].
               split; [exact HPL|]. split; [exact HPCB|]. split; [exact HPCW|]. split; [exact NL|]. split; [exact PS|]. split; [exact GG|]. split; [exact GU| exact HREPL]. }
      split. { pose proof SINIT as SI'. unfold stdio_init_law in SI'. apply (SI' (mkRC sp0 argv envp uid hw rnd0 tp false) m). split; [exact SF1| exact SF2]. }
      split. { unfold HARNR. split; [eexists; exact HA1|]. split; [eexists; exact HA2| exact HA3]. }
      split. { unfold CORE_TLS, rc_canary. cbn [utp rc_tp rc_rnd]. exists t, (Z_to_bv 64 0).
               split; [exact TD|]. split; [exact ERR|]. split; [exact TD2|]. split; [exact CAN|]. split; [exact DTV|]. split; [exact DTVB| exact Ht]. }
      split. { unfold PCAP_TLS. cbn [utp rc_tp]. eexists. exact TLS. }
      split. { unfold CORE_LIBC, rc_canary. cbn [rc_sp0 rc_argv rc_envp rc_rnd]. split; [exact LC|]. split; [exact GG|]. split; [exact GU|]. split; [exact SI|].
               exists pg, P0. split; [exact PG| exact HP0]. }
      split. { unfold CORE_MISC. split; [exact M1a|]. split; [exact M2a|]. split; [exact M3|]. split; [exact M2b|]. split; [exact M1b| exact M1c]. }
      split. { unfold CORE_EXIT. split; [exact EXL|].
               split. { exists false, (repeat (Z_to_bv 8 0) 3), (Z_to_bv 64 0), (Z_to_bv 64 0), (repeat (Z_to_bv 8 0) 248), (repeat (Z_to_bv 8 0) 248).
                        split; [exact FLG|]. split; [exact ATX|]. split; [exact BLTN| intros X; discriminate X]. }
               split; [exact GF|]. split; [exact FA|]. split; [exact FIN|]. split; [exact G2| exact DSO]. }
      split. { unfold CORE_STK. cbn [usp0 rc_sp0 rc_argv rc_envp rc_uid rc_hw rc_rnd]. exact STKB. }
      split; [reflexivity|]. split; [exact TB|]. split; [split; [constructor| exact I]|]. split; [split; [exact SPW| exact SPH]| unfold rc_lo, usp0; cbn [rc_sp0]; exact CLO]. }
    split; [exact MI|]. split; [exact ST|]. split; [exact VA|]. split; [cbn [usp0 rc_sp0]; exact V16|].
    unfold usp0. cbn [rc_sp0 rc_argv rc_envp rc_uid rc_hw rc_rnd]. change (2^47)%Z with 140737488355328%Z. lia.
  Qed.
End Init.

(* [comment removed for export] *)
Section ExitFrame.
  Context {H hptr : Type} (K : modkit H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  Lemma SXGI_frame : forall (s : PState H hptr) tp m m',
    SXGI K s tp m -> munch exit_footprint m m' -> wmono ssegs m m' -> SXGI K s tp m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt). ceil_facts.
    intros s tp m m' (R & CL & FB & Etp & HH & HS & HA & CT & PT & CLI & CM & Etls & TB & BOK) MU WM.
    pose proof BOK as [BO BA]. pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (AG : agrees_on (fun a => outside exit_footprint a) m m').
    { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact Hp. }
    assert (OUTB : forall a, in_block (CL ++ FB) a -> outside exit_footprint a).
    { intros a Hin. destruct (in_block_facts _ _ _ BO Hin) as (F1 & F2 & F3 & F4). unfold exit_footprint. cbn [outside]. lia. }
    exists R, CL, FB. split; [exact Etp|].
    split. { eapply HFL; [exact HH| exact MU| exact WM|]. unfold exit_footprint, heap_client_iv.
             repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    split. { eapply SFL; [exact HS|]. eapply agrees_on_weaken; [exact AG|]. intros a [Hst|Hfb].
             - unfold stdio_static, exit_footprint in *. cbn [outside]. lia.
             - apply OUTB. apply in_block_app. right. exact Hfb. }
    split. { eapply HARNR_agree; [exact AG| |exact HA]. intros a Hp. unfold harn_fp, harn_static, exit_footprint in *. cbn [outside]. lia. }
    split. { eapply CORE_TLS_agree; [exact AG| |exact CT]. intros a Hp. unfold core_tls_fp, exit_footprint in *. cbn [outside]. lia. }
    split. { eapply PCAP_TLS_agree; [exact AG| |exact PT]. intros a Hp. unfold pcap_tls_fp, exit_footprint in *. cbn [outside]. lia. }
    split. { eapply CORE_LIBC_agree; [exact AG| |exact CLI]. intros a Hp. unfold core_libc_fp, exit_footprint in *. cbn [outside]. lia. }
    split. { eapply CORE_MISC_agree; [exact AG| |exact CM]. intros a Hp. unfold core_misc_fp, exit_footprint in *. cbn [outside]. lia. }
    split; [exact Etls|]. split; [exact TB| exact BOK].
  Qed.
End ExitFrame.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.EntryRnd.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_main_A.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac cl_lit_hyps :=
  repeat match goal with
  | H : context [cells_size ?cs] |- _ =>
      tryif (match goal with H' := _ |- _ => constr_eq H' H end) then fail else
      (sl_spine_closed cs;
       let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
       change (cells_size cs) with n in H)
  end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac rimg_chunk segs NONE m A cs H ::=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nz := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells segs m A cs);
  [ apply (rw_cells_recast segs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 segs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nz in Ha; cbn [length outside] in Ha |- *; lia
      | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nz; lia ]
    | vm_compute; repeat split; exact I | vm_compute; reflexivity | vm_compute; reflexivity ]
  | ].
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition wimg (A : Z) (n : nat) : list byte := match image_bytes usegs A n with Some bs => bs | None => [] end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition heap_init_mem (canary : word) (m : mem) : Prop :=
  rw_cells usegs m 0x54558 [C4 (Z_to_bv 64 0)]
  /\ bytes_at usegs m 0x54560 (repeat (Z_to_bv 8 0) 928) /\ wr_at usegs m 0x54560 928
  /\ rw_cells usegs m 0x544eb [C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m 0x54518 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells usegs m 0x22de0 [C8 (Z_to_bv 64 0x544c8)]
  /\ rw_cells usegs m 0x544c8 [C8 canary]
  /\ rw_cells usegs m 0x54900 [C4 (Z_to_bv 64 0)].     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition stdio_init_mem (m : mem) : Prop :=
  rw_cells usegs m 0x23e20 [CB 720 (wimg 0x23e20 720)]
  /\ rw_cells usegs m 0x54908 [CB 2088 (wimg 0x54908 2088)].

Section Init.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (h0 : H).
  (* [comment removed for export] *)
  Variable rnd0 : EntryDraw.

  (* [comment removed for export] *)
  Definition heap_init_law : Prop :=
    forall R m, rc_rnd R = rnd0 -> heap_init_mem (rc_canary R) m -> tls_block_ok_u (utp R - 200) -> 0x7fff80000000 <= usp0 R ->
      CEILZ <= rc_lo R ->
      mk_heap K (ho_pin HO (utp R - 200) h0) R [] m.
  Definition stdio_init_law : Prop :=
    forall R m, stdio_init_mem m -> mk_stdio K libc_init R [] m.

  Hypothesis HINIT : heap_init_law.
  Hypothesis SINIT : stdio_init_law.

  Lemma GI_init : forall sp0 argv envp uid hw tp ms,
    valid_sp sp0 -> valid_argv argv -> entry_stack_fits sp0 argv envp ->     (* [comment removed for export] *)
    at_main sp0 argv envp uid hw rnd0 tp ms ->
    main_entry K (mkRC sp0 argv envp uid hw rnd0 tp false) (set_tls_pin HO (bv_unsigned tp - 200) (ps_init h0)) ms.
  Proof using HINIT SINIT. pin_using (fun (HINIT SINIT : unit) => tt). ceil_facts.
    intros sp0 argv envp uid hw tp ms VSP VA FITS AM.
    pose proof (entry_bounds Ubsan.M.phdrs sp0 argv envp uid hw rnd0 VSP FITS) as [_ EB].
    pose proof (bsb_le_esi Ubsan.M.phdrs sp0 argv envp uid hw rnd0) as BLE. unfold sp_window_hi in EB.
    (* [comment removed for export] *)
    unfold at_main in AM. let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in AM.
    let x := fresh "sbl" in pose (x := 3616%nat); change 3616%nat with x in AM.
    let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 256); change (repeat (Z_to_bv 8 0) 256) with z in AM.
    destruct AM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & t & P0 & pg & m & -> & AM).
    destruct AM as (MI & ST & TB & TD & ERR & TD2 & CAN & DTV & TLS & DTVB & LC & TLL & SI & PG & HW & ENV & DS & GU & G0 & G1 & G2 & G3 & G4 & GG & GF & IA & FA & DSO & INI & FIN & EXL & ATX & STKB & STKW & HP0 & NONE & Ht & CLO).
    destruct VSP as (VL & VH & V16). unfold sp_window_lo, sp_window_hi in VL, VH.
    assert (SPW : (0x7fff80000000 <= bv_unsigned sp0)%Z) by exact VL.
    assert (SPH : (bv_unsigned sp0 <= 2^47)%Z) by exact VH.
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    (* [comment removed for export] *)
    Ltac none_range NONE m lo hi N :=
      assert (N : forall a : word, (lo <= bv_unsigned a < hi)%Z -> m a = None)
        by (intros a Ha; apply NONE; [lia| unfold crt_written; cbn [outside]; lia]).
    none_range NONE m 0x54558 0x54908 N1.
    none_range NONE m 0x23e20 0x240f0 N2.
    none_range NONE m 0x54908 0x55130 N3.
    none_range NONE m 0x22d78 0x22db0 N4.
    none_range NONE m 0x22d20 0x22d30 N5.
    none_range NONE m 0x22db0 0x22db8 N6.
    none_range NONE m 0x34150 0x34188 N7.
    none_range NONE m 0x542b8 0x544c0 N8.
    rimg_chunk usegs N1 m 0x54558%Z [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); CB 928 (repeat (Z_to_bv 8 0) 928)] HP1.
    rimg_chunk usegs N1 m 0x54900%Z [C4 (Z_to_bv 64 0)] HREPL.
    rimg_chunk usegs N2 m 0x23e20%Z [CB 720 (wimg 0x23e20 720)] SF1.
    rimg_chunk usegs N3 m 0x54908%Z [CB 2088 (wimg 0x54908 2088)] SF2.
    rimg_chunk usegs N4 m 0x22d78%Z [C8 (Z_to_bv 64 0x22d20); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x22d30); C8 (Z_to_bv 64 0x14b64); C8 (Z_to_bv 64 0x147dc); C8 (Z_to_bv 64 0x14a64); C8 (Z_to_bv 64 0x1422c)] M1.
    rimg_chunk usegs N5 m 0x22d20%Z [C8 (Z_to_bv 64 0x23e20); C8 (Z_to_bv 64 0x23f10)] M2.
    rimg_chunk usegs N6 m 0x22db0%Z [C8 (Z_to_bv 64 0x22d28)] M3.
    rimg_chunk usegs N7 m 0x34150%Z [C1 (Z_to_bv 8 0); CB 15 (repeat (Z_to_bv 8 0) 15); CB 32 (repeat (Z_to_bv 8 0) 32); C8 (Z_to_bv 64 0)] HA.
    (* [comment removed for export] *)
    rimg_chunk usegs N7 m 0x34150%Z [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 0)] FLG.
    rimg_chunk usegs N8 m 0x542b8%Z [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 248 (repeat (Z_to_bv 8 0) 248); C8 (Z_to_bv 64 0); CB 248 (repeat (Z_to_bv 8 0) 248)] BLTN.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app usegs m _ [_; _] [_])) in HP1 as [HPL HPC]. (sl_lit_sizes_in HPC; cbn [cells_size csize Nat.add] in HPC).
    apply rw_cells_split2 in HPL as [HPL _].
    destruct HPC as [[_ HPCB] HPCW]. (sl_lit_sizes_in HPCB; sl_lit_sizes_in HPCW; cbn [cells_bytes cbytes cells_size csize Nat.add] in HPCB, HPCW). rewrite app_nil_r in HPCB.
    apply (proj1 (rw_cells_app usegs m _ [_; _] [_; _; _; _; _])) in M1 as [M1 M1c]. (sl_lit_sizes_in M1c; cbn [cells_size csize Nat.add] in M1c).
    apply (proj1 (rw_cells_app usegs m _ [_] [_; _; _; _])) in M1c as [_ M1c]. (sl_lit_sizes_in M1c; cbn [cells_size csize Nat.add] in M1c).
    match type of M1c with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in M1c end.
    apply rw_cells_split2 in M1 as [M1a M1b]. cbn [csize] in M1b.
    apply rw_cells_split2 in M2 as [M2a M2b]. cbn [csize] in M2b.
    apply (proj1 (rw_cells_app usegs m _ [_; _] [_; _])) in HA as [HA1 HA2]. (sl_lit_sizes_in HA2; cbn [cells_size csize Nat.add] in HA2).
    apply rw_cells_split2 in HA1 as [HA1 _]. apply rw_cells_split2 in HA2 as [HA2 HA3]. cbn [csize] in HA3.
    (* [comment removed for export] *)
    pose proof LC as LC'. unfold libc_cells in LC'.
    apply (proj1 (rw_cells_app usegs m _ [_; _; _] _)) in LC' as [_ LC']. (sl_lit_sizes_in LC'; cbn [cells_size csize Nat.add] in LC').
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in LC' as [NL LC']. (sl_lit_sizes_in LC'; cbn [cells_size csize Nat.add] in LC').
    apply (proj1 (rw_cells_app usegs m _ [_; _; _; _; _; _] _)) in LC' as [_ LC']. (sl_lit_sizes_in LC'; cbn [cells_size csize Nat.add] in LC').
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in LC' as [PS _].
    match type of NL with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in NL end.
    match type of PS with rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in PS end.
    unfold main_entry. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    cbn [rc_sp0 rc_argv rc_envp rc_uid rc_hw rc_rnd rc_tp rc_cb usp0 rc_lo].
    split.
    { (* [comment removed for export] *)
      exists []. cbn [app ps_heap ps_libc ps_outfile ps_tls set_tls_pin set_tls set_heap ps_init utp rc_tp usp0 rc_sp0 rc_argv rc_envp rc_uid rc_hw rc_rnd rc_cb].
      split. { pose proof HINIT as HI. unfold heap_init_law in HI. apply (HI (mkRC sp0 argv envp uid hw rnd0 tp false) m); [reflexivity | | exact TB | exact SPW | unfold rc_lo, usp0; cbn [rc_sp0]; exact CLO]. unfold heap_init_mem, rc_canary; cbn [rc_rnd].
               split; [exact HPL|]. split; [exact HPCB|]. split; [exact HPCW|]. split; [exact NL|]. split; [exact PS|]. split; [exact GG|]. split; [exact GU| exact HREPL]. }
      split. { pose proof SINIT as SI'. unfold stdio_init_law in SI'. apply (SI' (mkRC sp0 argv envp uid hw rnd0 tp false) m). split; [exact SF1| exact SF2]. }
      split. { unfold HARNR. split; [eexists; exact HA1|]. split; [eexists; exact HA2| exact HA3]. }
      split. { unfold CORE_TLS, rc_canary. cbn [utp rc_tp rc_rnd]. exists t, (Z_to_bv 64 0).
               split; [exact TD|]. split; [exact ERR|]. split; [exact TD2|]. split; [exact CAN|]. split; [exact DTV|]. split; [exact DTVB| exact Ht]. }
      split. { unfold PCAP_TLS. cbn [utp rc_tp]. eexists. exact TLS. }
      split. { unfold CORE_LIBC, rc_canary. cbn [rc_sp0 rc_argv rc_envp rc_rnd]. split; [exact LC|]. split; [exact GG|]. split; [exact GU|]. split; [exact SI|].
               exists pg, P0. split; [exact PG| exact HP0]. }
      split. { unfold CORE_MISC. split; [exact M1a|]. split; [exact M2a|]. split; [exact M3|]. split; [exact M2b|]. split; [exact M1b| exact M1c]. }
      split. { unfold CORE_EXIT. split; [exact EXL|].
               split. { exists false, (repeat (Z_to_bv 8 0) 3), (Z_to_bv 64 0), (Z_to_bv 64 0), (repeat (Z_to_bv 8 0) 248), (repeat (Z_to_bv 8 0) 248).
                        split; [exact FLG|]. split; [exact ATX|]. split; [exact BLTN| intros X; discriminate X]. }
               split; [exact GF|]. split; [exact FA|]. split; [exact FIN|]. split; [exact G2| exact DSO]. }
      split. { unfold CORE_STK. cbn [usp0 rc_sp0 rc_argv rc_envp rc_uid rc_hw rc_rnd]. exact STKB. }
      split; [reflexivity|]. split; [exact TB|]. split; [split; [constructor| exact I]|]. split; [split; [exact SPW| exact SPH]| unfold rc_lo, usp0; cbn [rc_sp0]; exact CLO]. }
    split; [exact MI|]. split; [exact ST|]. split; [exact VA|]. split; [cbn [usp0 rc_sp0]; exact V16|].
    unfold usp0. cbn [rc_sp0 rc_argv rc_envp rc_uid rc_hw rc_rnd]. change (2^47)%Z with 140737488355328%Z. lia.
  Qed.
End Init.

(* [comment removed for export] *)
Section ExitFrame.
  Context {H hptr : Type} (K : modkit H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  Lemma SXGI_frame : forall (s : PState H hptr) tp m m',
    SXGI K s tp m -> munch exit_footprint m m' -> wmono usegs m m' -> SXGI K s tp m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt). ceil_facts.
    intros s tp m m' (R & CL & FB & Etp & HH & HS & HA & CT & PT & CLI & CM & Etls & TB & BOK) MU WM.
    pose proof BOK as [BO BA]. pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (AG : agrees_on (fun a => outside exit_footprint a) m m').
    { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact Hp. }
    assert (OUTB : forall a, in_block (CL ++ FB) a -> outside exit_footprint a).
    { intros a Hin. destruct (in_block_facts _ _ _ BO Hin) as (F1 & F2 & F3 & F4). unfold exit_footprint. cbn [outside]. lia. }
    exists R, CL, FB. split; [exact Etp|].
    split. { eapply HFL; [exact HH| exact MU| exact WM|]. unfold exit_footprint, heap_client_iv.
             repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    split. { eapply SFL; [exact HS|]. eapply agrees_on_weaken; [exact AG|]. intros a [Hst|Hfb].
             - unfold stdio_static, exit_footprint in *. cbn [outside]. lia.
             - apply OUTB. apply in_block_app. right. exact Hfb. }
    split. { eapply HARNR_agree; [exact AG| |exact HA]. intros a Hp. unfold harn_fp, harn_static, exit_footprint in *. cbn [outside]. lia. }
    split. { eapply CORE_TLS_agree; [exact AG| |exact CT]. intros a Hp. unfold core_tls_fp, exit_footprint in *. cbn [outside]. lia. }
    split. { eapply PCAP_TLS_agree; [exact AG| |exact PT]. intros a Hp. unfold pcap_tls_fp, exit_footprint in *. cbn [outside]. lia. }
    split. { eapply CORE_LIBC_agree; [exact AG| |exact CLI]. intros a Hp. unfold core_libc_fp, exit_footprint in *. cbn [outside]. lia. }
    split. { eapply CORE_MISC_agree; [exact AG| |exact CM]. intros a Hp. unfold core_misc_fp, exit_footprint in *. cbn [outside]. lia. }
    split; [exact Etls|]. split; [exact TB| exact BOK].
  Qed.
End ExitFrame.

End WithCeil.
End TwB.
End GIInit.

(* [comment removed for export] *)
Module F_fuzz_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep RegsEquiv MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac cl_lit_hyps :=
  repeat match goal with
  | H : context [cells_size ?cs] |- _ =>
      tryif (match goal with H' := _ |- _ => constr_eq H' H end) then fail else
      (sl_spine_closed cs;
       let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
       change (cells_size cs) with n in H)
  end.
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.release_frame FR ST hi ::=
  eapply stk_release in FR; [ | exact ST | lia ];
  clear ST; rename FR into ST;
  sl_lit_sizes_in ST;
  cbn [cells_size csize Nat.add] in ST;
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi' => replace hi' with hi in ST by lia
  end.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope Z_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition FZ : Z := 4432.

(* [comment removed for export] *)
Definition pro_post (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 : list byte) (ej : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x13fec) (Z_to_bv 64 (bv_unsigned sp + - 4432)) gp tp t0 t1 t2 a1 a0 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x13fec) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 4432, bv_unsigned sp)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp + - 4432)
    /\ rw_cells ssegs m' (bv_unsigned sp + - 4432) [CB 40 j0]
    /\ rw_cells ssegs m' (bv_unsigned sp + - 4392) [CB 30 j1]
    /\ rw_cells ssegs m' (bv_unsigned sp + - 4362) [CB 4066 (repeat (Z_to_bv 8 0) 4066)]
    /\ rw_cells ssegs m' (bv_unsigned sp + - 296) [CB 256 ej]
    /\ rw_cells ssegs m' (bv_unsigned sp + - 40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition prologue_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) -> (lo + FZ <= bv_unsigned sp)%Z -> mem_inv ssegs m ->
  evt ssegs (pro_post ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fb0) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo : ltac2:(SecDiet.SzSec.tyM 'prologue_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma prologue_spec__body : ltac2:(SecDiet.SzSec.bodyP 'prologue_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
  intros ST BUD MI.
 unfold FZ in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
  pose proof (munch_refl [(bv_unsigned sp - 4432, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  carve_frame 40%nat ST. rename FR into FRH.
  carve_frame 256%nat ST. rename FR into FRE.
  carve_frame 4066%nat ST. rename FR into FRZ.
  carve_frame 30%nat ST. rename FR into FRT.
  carve_frame 40%nat ST. rename FR into FRL.
  do 8 lstep. do 7 lstep.
  name_sp sp (-4432)%Z.
  call (memset_specZ (bv_unsigned sp + -4362) 4066 0); [ fastfirst (first [ noevar_assumption |exact FRZ | exact MI | reflexivity | lia]) .. | ].
  unname_sp.
  finish. all: eassumption.
Qed.
End Sz1.
Lemma prologue_spec : ltac:(let t := eval cbv delta [prologue_spec__stmt] in prologue_spec__stmt in exact t).
Proof using CEILV. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo. ltac2:(SecDiet.SzSec.closeP 'prologue_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Lemma name_bytes : forall m A n (buf pre : list byte) k,
  rw_cells ssegs m A [CB n buf] -> firstn k buf = pre -> bytes_at ssegs m A pre.
Proof using Type. pin_using tt.
  intros m A n buf pre k RC E. apply rw_cells_bytes_at in RC. cbn [cells_bytes cbytes] in RC. rewrite app_nil_r in RC.
  rewrite <- (firstn_skipn k buf), E in RC. apply bytes_at_app in RC as [RC _]. exact RC.
Qed.

Definition tmpname : list byte := map b8 TMPNAME.
Lemma tmpname_Z : map bv_unsigned tmpname = TMPNAME.
Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
Lemma tmpname_len : length tmpname = 24%nat.
Proof using Type. pin_using tt. reflexivity. Qed.
Lemma tmpname_nonul : ~ In (Z_to_bv 8 0) tmpname.
Proof using Type. pin_using tt. unfold tmpname, TMPNAME. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
Lemma tmpname_first : nth_error tmpname 0 <> Some (Z_to_bv 8 45).
Proof using Type. pin_using tt. cbn. discriminate. Qed.
Lemma tmpname_ok : unlink_name_ok tmpname.
Proof using Type. pin_using tt.
  unfold unlink_name_ok. split; [vm_compute; reflexivity|]. split; [discriminate|]. split; [discriminate|].
  rewrite tmpname_len. unfold Uapi.NAME_MAX. lia.
Qed.
(* [comment removed for export] *)
Lemma tmpname_open_w : open_name_ok true tmpname.
Proof using Type. pin_using tt. left. vm_compute. reflexivity. Qed.
Lemma tmpname_open_r : open_name_ok false tmpname.
Proof using Type. pin_using tt. split; vm_compute; reflexivity. Qed.

Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  Definition hinv (R : rctx) (lo : Z) (spB : word) (m : mem) : Prop :=
    stk ssegs m lo (bv_unsigned spB) /\ rc_lo R <= lo /\ lo + FUZZ_STACK <= bv_unsigned spB + FZ
    /\ bv_unsigned spB + FZ <= rc_spmain R /\ mem_inv ssegs m /\ bv_unsigned spB mod 16 = 0.

  Lemma hinv_spo : forall R lo spB m s CL FB tp budget,
    hinv R lo spB m -> GIo K R s CL FB m -> tp = rc_tp R -> budget <= FUZZ_STACK - FZ ->
    std_pre_o K spB tp R s CL FB lo budget m.
  Proof using Type. pin_using tt.
    intros R lo spB m s CL FB tp budget (ST & LO & BU & SPM & MI & ALN) G TP HB. unfold FZ in *.
    split; [exact G|]. split; [exact ST|]. split; [exact LO|]. split; [lia|]. split; [unfold rc_spmain in *; lia|]. split; [exact MI|]. split; [exact TP| exact ALN].
  Qed.

  Lemma hinv_mem : forall R lo spB m m', hinv R lo spB m -> stk ssegs m' lo (bv_unsigned spB) -> mem_inv ssegs m' -> hinv R lo spB m'.
  Proof using Type. pin_using tt.
    intros R lo spB m m' (ST & LO & BU & SPM & MI & ALN) ST' MI'.
    split; [exact ST'|]. split; [exact LO|]. split; [exact BU|]. split; [exact SPM|]. split; [exact MI'| exact ALN].
  Qed.

  (* [comment removed for export] *)
  Definition KEEP (CL : list cblk) (spB : word) : Z -> Prop := client_keeps CL (bv_unsigned spB + FZ).

  Lemma keep_of_callee : forall (CL : list cblk) spB (X : Z -> Prop) m m',
    agrees_on (fun a => client_keeps CL (bv_unsigned spB) a /\ X a) m m' ->
    (forall a, bv_unsigned spB + FZ <= a -> X a) -> (forall a, in_block CL a -> X a) ->
    agrees_on (KEEP CL spB) m m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros CL spB X m m' AG H1 H2. eapply agrees_on_weaken; [exact AG|]. unfold KEEP, client_keeps, FZ in *.
    intros a [Ha|Ha]; [split; [left; lia| apply H1; lia] | split; [right; exact Ha| apply H2; exact Ha]].
  Qed.

  Lemma keep_of_callee0 : forall (CL : list cblk) spB m m',
    agrees_on (client_keeps CL (bv_unsigned spB)) m m' -> agrees_on (KEEP CL spB) m m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros CL spB m m' AG. eapply agrees_on_weaken; [exact AG|]. unfold KEEP, client_keeps, FZ. intros a [Ha|Ha]; [left; lia| right; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Definition at18 (spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (cs3 cs2 cs1 cs0 cra : word) (m0 : mem) : unit -> PSt -> machine_state -> Prop :=
    fun _ s' ms' => exists ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 m' FB' (j : list byte),
      ms' = MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14148) fc None m' (seg_rom ssegs)
      /\ GIo K R s' CL FB' m' /\ hinv R lo spB m'
      /\ agrees_on (KEEP CL spB) m0 m'
      /\ rw_cells ssegs m' (bv_unsigned spB) [CB 4392 j]
      /\ rw_cells ssegs m' (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra].

  (* [comment removed for export] *)
  Definition epilogue_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (cs3 cs2 cs1 cs0 cra : word) (j : list byte),
    stk ssegs m lo (bv_unsigned spB) -> mem_inv ssegs m -> bv_unsigned spB + FZ < 2^64 -> lo <= bv_unsigned spB ->
    rw_cells ssegs m (bv_unsigned spB) [CB 4392 j] ->
    rw_cells ssegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    evt ssegs (fun ms' =>
        ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned spB + FZ)) gp tp t0 t1 t2 cs0 cs1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 cs2 cs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc cra) fc None m (seg_rom ssegs)
        /\ stk ssegs m lo (bv_unsigned spB + FZ))
      (MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14148) fc None m (seg_rom ssegs)).
  Section Sz14.
  Variables ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo cs3 cs2 cs1 cs0 cra j : ltac2:(SecDiet.SzSec.tyM 'epilogue_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma epilogue_spec__body : ltac2:(SecDiet.SzSec.bodyP 'epilogue_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros ST MI HB LOB FRL FRH.
 unfold FZ in *.
    pose proof (bv_unsigned_in_range 64 spB) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    do 10 lstep.
    release_frame FRL ST (bv_unsigned spB + 4392). release_frame FRH ST (bv_unsigned spB + 4432).
    apply evt_done. split; [|exact ST]. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz14.
  Lemma epilogue_spec : ltac:(let t := eval cbv delta [epilogue_spec__stmt] in epilogue_spec__stmt in exact t).
  Proof using Type. intros ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo cs3 cs2 cs1 cs0 cra j. ltac2:(SecDiet.SzSec.closeP 'epilogue_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma frame_forget3 : forall m A (a b c : list byte),
    rw_cells ssegs m A [CB 40 a] -> rw_cells ssegs m (A + 40) [CB 4096 b] -> rw_cells ssegs m (A + 4136) [CB 256 c] ->
    exists j, rw_cells ssegs m A [CB 4392 j].
  Proof using Type. pin_using tt.
    intros m A a b c H1 H2 H3.
    assert (X : rw_cells ssegs m A ([CB 40 a] ++ [CB 4096 b] ++ [CB 256 c])).
    { apply rw_cells_app. split; [exact H1|]. (sl_lit_sizes; cbn [cells_size csize Nat.add]). replace (A + Z.of_nat 40) with (A + 40) by lia.
      apply rw_cells_app. split; [exact H2|]. (sl_lit_sizes; cbn [cells_size csize Nat.add]). replace (A + 40 + Z.of_nat 4096) with (A + 4136) by lia. exact H3. }
    apply rw_cells_forget in X. exact X.
  Qed.

  Lemma at18_back : forall spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 m1 u s ms,
    agrees_on (KEEP CL spB) m0 m1 ->
    at18 spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m1 u s ms ->
    at18 spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 u s ms.
  Proof using Type. pin_using tt.
    intros until ms. intros AG PO. unfold at18 in *. let sblx := fresh "sbl" in pose (sblx := 4392%nat); change 4392%nat with sblx in PO |- *. destruct_exs PO. destruct PO as (E & G & HI & AG2 & FRL & FRH).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [exact E|]. split; [exact G|]. split; [exact HI|]. split; [eapply agrees_on_trans; [exact AG| exact AG2]|]. split; [exact FRL| exact FRH].
  Qed.

  Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
    try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

  (* [comment removed for export] *)
  Definition unlink18_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo : Z)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R ->
    rw_cells ssegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells ssegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells ssegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells ssegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM ssegs (s_unlink (H:=H) (hptr:=hptr) TMPNAME ;;; mret tt) s
      (at18 spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14140) fc None m (seg_rom ssegs)).
  Section Sz17.
  Variables ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo cs3 cs2 cs1 cs0 cra j0 nbuf ej : ltac2:(SecDiet.SzSec.tyM 'unlink18_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma unlink18_spec__body : ltac2:(SecDiet.SzSec.bodyP 'unlink18_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using UNLINK. pin_using (fun (UNLINK : unit) => tt).
    intros G HI TP FR1 FR2 NB FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN). unfold FZ, FUZZ_STACK in BU, SPM. unfold rc_spmain in SPM.
    pose proof (bv_unsigned_in_range 64 spB) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (name_bytes _ _ _ _ _ _ FR2 NB) as NBY.
    unfold implM. iprefix. lstep. lstep.
    apply evt_done. eapply (implM_bind ssegs).
    { rewrite <- tmpname_Z.
      eapply (UNLINK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (bv_unsigned spB + 40) tmpname);
        [ eapply hinv_spo; [exact HI | exact G | exact TP | unfold STDIO_STACK, FUZZ_STACK, FZ; lia]
        | f_equal; lia | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia
        | right; rewrite tmpname_len; unfold rc_spmain; lia | exact tmpname_ok ]. }
    intros r s' ms' PO. cbv beta in PO. destruct PO as (a0v & m' & E & EO' & MI' & ST' & AG & G' & -> & Hr).
    post_regs E.
    apply (implM_ret ssegs). apply evt_done.
    assert (K1 : forall a, bv_unsigned spB <= a -> client_keeps CL (bv_unsigned spB) a) by (intros a Ha; left; exact Ha).
    apply (agrees_rw_cells _ _ _ _ _ AG) in FR1; [| intros a Ha; apply K1; sl_lit_sizes_in Ha; cbn in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in FR2; [| intros a Ha; apply K1; sl_lit_sizes_in Ha; cbn in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in FR3; [| intros a Ha; apply K1; sl_lit_sizes_in Ha; cbn in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in FR4; [| intros a Ha; apply K1; sl_lit_sizes_in Ha; cbn in Ha; lia].
    destruct (frame_forget3 _ _ _ _ _ FR1 FR2 FR3) as [j FRL].
    unfold at18. let sblx := fresh "sbl" in pose (sblx := 4392%nat); change 4392%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact G'|]. split; [eapply hinv_mem; [exact HI| exact ST'| exact MI']|].
    split; [apply keep_of_callee0; exact AG|]. split; [exact FRL| exact FR4].
  Qed.
  End Sz17.
  Lemma unlink18_spec : ltac:(let t := eval cbv delta [unlink18_spec__stmt] in unlink18_spec__stmt in exact t).
  Proof using UNLINK. intros ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo cs3 cs2 cs1 cs0 cra j0 nbuf ej. ltac2:(SecDiet.SzSec.closeP 'unlink18_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fuzz.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit.TwB.
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
Open Scope Z_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition FZ : Z := 4432.

(* [comment removed for export] *)
Definition pro_post (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 : list byte) (ej : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x14060) (Z_to_bv 64 (bv_unsigned sp + - 4432)) gp tp t0 t1 t2 a1 a0 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x14060) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 4432, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + - 4432)
    /\ rw_cells usegs m' (bv_unsigned sp + - 4432) [CB 40 j0]
    /\ rw_cells usegs m' (bv_unsigned sp + - 4392) [CB 30 j1]
    /\ rw_cells usegs m' (bv_unsigned sp + - 4362) [CB 4066 (repeat (Z_to_bv 8 0) 4066)]
    /\ rw_cells usegs m' (bv_unsigned sp + - 296) [CB 256 ej]
    /\ rw_cells usegs m' (bv_unsigned sp + - 40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition prologue_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk usegs m lo (bv_unsigned sp) -> (lo + FZ <= bv_unsigned sp)%Z -> mem_inv usegs m ->
  evt usegs (pro_post ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14024) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo : ltac2:(SecDiet.SzSec.tyM 'prologue_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma prologue_spec__body : ltac2:(SecDiet.SzSec.bodyP 'prologue_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
 intros ST BUD MI. unfold FZ in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
  pose proof (munch_refl [(bv_unsigned sp - 4432, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  carve_frame 40%nat ST. rename FR into FRH.
  carve_frame 256%nat ST. rename FR into FRE.
  carve_frame 4066%nat ST. rename FR into FRZ.
  carve_frame 30%nat ST. rename FR into FRT.
  carve_frame 40%nat ST. rename FR into FRL.
  do 8 lstep. do 7 lstep.
  name_sp sp (-4432)%Z.
  call (memset_specZ (bv_unsigned sp + -4362) 4066 0); [ fastfirst (first [ noevar_assumption |exact FRZ | exact MI | reflexivity | lia]) .. | ].
  unname_sp.
  finish. all: eassumption.
Qed.
End Sz1.
Lemma prologue_spec : ltac:(let t := eval cbv delta [prologue_spec__stmt] in prologue_spec__stmt in exact t).
Proof using CEILV. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo. ltac2:(SecDiet.SzSec.closeP 'prologue_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Lemma name_bytes : forall m A n (buf pre : list byte) k,
  rw_cells usegs m A [CB n buf] -> firstn k buf = pre -> bytes_at usegs m A pre.
Proof using Type. pin_using tt.
  intros m A n buf pre k RC E. apply rw_cells_bytes_at in RC. cbn [cells_bytes cbytes] in RC. rewrite app_nil_r in RC.
  rewrite <- (firstn_skipn k buf), E in RC. apply bytes_at_app in RC as [RC _]. exact RC.
Qed.

Definition tmpname : list byte := map b8 TMPNAME.
Lemma tmpname_Z : map bv_unsigned tmpname = TMPNAME.
Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
Lemma tmpname_len : length tmpname = 24%nat.
Proof using Type. pin_using tt. reflexivity. Qed.
Lemma tmpname_nonul : ~ In (Z_to_bv 8 0) tmpname.
Proof using Type. pin_using tt. unfold tmpname, TMPNAME. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
Lemma tmpname_first : nth_error tmpname 0 <> Some (Z_to_bv 8 45).
Proof using Type. pin_using tt. cbn. discriminate. Qed.
Lemma tmpname_ok : unlink_name_ok tmpname.
Proof using Type. pin_using tt.
  unfold unlink_name_ok. split; [vm_compute; reflexivity|]. split; [discriminate|]. split; [discriminate|].
  rewrite tmpname_len. unfold Uapi.NAME_MAX. lia.
Qed.
(* [comment removed for export] *)
Lemma tmpname_open_w : open_name_ok true tmpname.
Proof using Type. pin_using tt. left. vm_compute. reflexivity. Qed.
Lemma tmpname_open_r : open_name_ok false tmpname.
Proof using Type. pin_using tt. split; vm_compute; reflexivity. Qed.

Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  Definition hinv (R : rctx) (lo : Z) (spB : word) (m : mem) : Prop :=
    stk usegs m lo (bv_unsigned spB) /\ rc_lo R <= lo /\ lo + FUZZ_STACK <= bv_unsigned spB + FZ
    /\ bv_unsigned spB + FZ <= rc_spmain R /\ mem_inv usegs m /\ bv_unsigned spB mod 16 = 0.

  Lemma hinv_spo : forall R lo spB m s CL FB tp budget,
    hinv R lo spB m -> GIo K R s CL FB m -> tp = rc_tp R -> budget <= FUZZ_STACK - FZ ->
    std_pre_o K spB tp R s CL FB lo budget m.
  Proof using Type. pin_using tt.
    intros R lo spB m s CL FB tp budget (ST & LO & BU & SPM & MI & ALN) G TP HB. unfold FZ in *.
    split; [exact G|]. split; [exact ST|]. split; [exact LO|]. split; [lia|]. split; [unfold rc_spmain in *; lia|]. split; [exact MI|]. split; [exact TP| exact ALN].
  Qed.

  Lemma hinv_mem : forall R lo spB m m', hinv R lo spB m -> stk usegs m' lo (bv_unsigned spB) -> mem_inv usegs m' -> hinv R lo spB m'.
  Proof using Type. pin_using tt.
    intros R lo spB m m' (ST & LO & BU & SPM & MI & ALN) ST' MI'.
    split; [exact ST'|]. split; [exact LO|]. split; [exact BU|]. split; [exact SPM|]. split; [exact MI'| exact ALN].
  Qed.

  (* [comment removed for export] *)
  Definition KEEP (CL : list cblk) (spB : word) : Z -> Prop := client_keeps CL (bv_unsigned spB + FZ).

  Lemma keep_of_callee : forall (CL : list cblk) spB (X : Z -> Prop) m m',
    agrees_on (fun a => client_keeps CL (bv_unsigned spB) a /\ X a) m m' ->
    (forall a, bv_unsigned spB + FZ <= a -> X a) -> (forall a, in_block CL a -> X a) ->
    agrees_on (KEEP CL spB) m m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros CL spB X m m' AG H1 H2. eapply agrees_on_weaken; [exact AG|]. unfold KEEP, client_keeps, FZ in *.
    intros a [Ha|Ha]; [split; [left; lia| apply H1; lia] | split; [right; exact Ha| apply H2; exact Ha]].
  Qed.

  Lemma keep_of_callee0 : forall (CL : list cblk) spB m m',
    agrees_on (client_keeps CL (bv_unsigned spB)) m m' -> agrees_on (KEEP CL spB) m m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros CL spB m m' AG. eapply agrees_on_weaken; [exact AG|]. unfold KEEP, client_keeps, FZ. intros a [Ha|Ha]; [left; lia| right; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Definition at18 (spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (cs3 cs2 cs1 cs0 cra : word) (m0 : mem) : unit -> PSt -> machine_state -> Prop :=
    fun _ s' ms' => exists ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 m' FB' (j : list byte),
      ms' = MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x141e0) fc None m' (seg_rom usegs)
      /\ GIo K R s' CL FB' m' /\ hinv R lo spB m'
      /\ agrees_on (KEEP CL spB) m0 m'
      /\ rw_cells usegs m' (bv_unsigned spB) [CB 4392 j]
      /\ rw_cells usegs m' (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra].

  (* [comment removed for export] *)
  Definition epilogue_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (cs3 cs2 cs1 cs0 cra : word) (j : list byte),
    stk usegs m lo (bv_unsigned spB) -> mem_inv usegs m -> bv_unsigned spB + FZ < 2^64 -> lo <= bv_unsigned spB ->
    rw_cells usegs m (bv_unsigned spB) [CB 4392 j] ->
    rw_cells usegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    evt usegs (fun ms' =>
        ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned spB + FZ)) gp tp t0 t1 t2 cs0 cs1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 cs2 cs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc cra) fc None m (seg_rom usegs)
        /\ stk usegs m lo (bv_unsigned spB + FZ))
      (MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x141e0) fc None m (seg_rom usegs)).
  Section Sz14.
  Variables ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo cs3 cs2 cs1 cs0 cra j : ltac2:(SecDiet.SzSec.tyM 'epilogue_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma epilogue_spec__body : ltac2:(SecDiet.SzSec.bodyP 'epilogue_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros ST MI HB LOB FRL FRH. unfold FZ in *.
    pose proof (bv_unsigned_in_range 64 spB) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    do 10 lstep.
    release_frame FRL ST (bv_unsigned spB + 4392). release_frame FRH ST (bv_unsigned spB + 4432).
    apply evt_done. split; [|exact ST]. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz14.
  Lemma epilogue_spec : ltac:(let t := eval cbv delta [epilogue_spec__stmt] in epilogue_spec__stmt in exact t).
  Proof using Type. intros ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo cs3 cs2 cs1 cs0 cra j. ltac2:(SecDiet.SzSec.closeP 'epilogue_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma frame_forget3 : forall m A (a b c : list byte),
    rw_cells usegs m A [CB 40 a] -> rw_cells usegs m (A + 40) [CB 4096 b] -> rw_cells usegs m (A + 4136) [CB 256 c] ->
    exists j, rw_cells usegs m A [CB 4392 j].
  Proof using Type. pin_using tt.
    intros m A a b c H1 H2 H3.
    assert (X : rw_cells usegs m A ([CB 40 a] ++ [CB 4096 b] ++ [CB 256 c])).
    { apply rw_cells_app. split; [exact H1|]. (sl_lit_sizes; cbn [cells_size csize Nat.add]). replace (A + Z.of_nat 40) with (A + 40) by lia.
      apply rw_cells_app. split; [exact H2|]. (sl_lit_sizes; cbn [cells_size csize Nat.add]). replace (A + 40 + Z.of_nat 4096) with (A + 4136) by lia. exact H3. }
    apply rw_cells_forget in X. exact X.
  Qed.

  Lemma at18_back : forall spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 m1 u s ms,
    agrees_on (KEEP CL spB) m0 m1 ->
    at18 spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m1 u s ms ->
    at18 spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 u s ms.
  Proof using Type. pin_using tt.
    intros until ms. intros AG PO. unfold at18 in *. let sblx := fresh "sbl" in pose (sblx := 4392%nat); change 4392%nat with sblx in PO |- *. destruct_exs PO. destruct PO as (E & G & HI & AG2 & FRL & FRH).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [exact E|]. split; [exact G|]. split; [exact HI|]. split; [eapply agrees_on_trans; [exact AG| exact AG2]|]. split; [exact FRL| exact FRH].
  Qed.

  Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
    try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

  (* [comment removed for export] *)
  Definition unlink18_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo : Z)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R ->
    rw_cells usegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells usegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells usegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells usegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM usegs (s_unlink (H:=H) (hptr:=hptr) TMPNAME ;;; mret tt) s
      (at18 spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x141d8) fc None m (seg_rom usegs)).
  Section Sz17.
  Variables ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo cs3 cs2 cs1 cs0 cra j0 nbuf ej : ltac2:(SecDiet.SzSec.tyM 'unlink18_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma unlink18_spec__body : ltac2:(SecDiet.SzSec.bodyP 'unlink18_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using UNLINK. pin_using (fun (UNLINK : unit) => tt).
 intros G HI TP FR1 FR2 NB FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN). unfold FZ, FUZZ_STACK in BU, SPM. unfold rc_spmain in SPM.
    pose proof (bv_unsigned_in_range 64 spB) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (name_bytes _ _ _ _ _ _ FR2 NB) as NBY.
    unfold implM. iprefix. lstep. lstep.
    apply evt_done. eapply (implM_bind usegs).
    { rewrite <- tmpname_Z.
      eapply (UNLINK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (bv_unsigned spB + 40) tmpname);
        [ eapply hinv_spo; [exact HI | exact G | exact TP | unfold STDIO_STACK, FUZZ_STACK, FZ; lia]
        | f_equal; lia | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia
        | right; rewrite tmpname_len; unfold rc_spmain; lia | exact tmpname_ok ]. }
    intros r s' ms' PO. cbv beta in PO. destruct PO as (a0v & m' & E & EO' & MI' & ST' & AG & G' & -> & Hr).
    post_regs E.
    apply (implM_ret usegs). apply evt_done.
    assert (K1 : forall a, bv_unsigned spB <= a -> client_keeps CL (bv_unsigned spB) a) by (intros a Ha; left; exact Ha).
    apply (agrees_rw_cells _ _ _ _ _ AG) in FR1; [| intros a Ha; apply K1; sl_lit_sizes_in Ha; cbn in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in FR2; [| intros a Ha; apply K1; sl_lit_sizes_in Ha; cbn in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in FR3; [| intros a Ha; apply K1; sl_lit_sizes_in Ha; cbn in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in FR4; [| intros a Ha; apply K1; sl_lit_sizes_in Ha; cbn in Ha; lia].
    destruct (frame_forget3 _ _ _ _ _ FR1 FR2 FR3) as [j FRL].
    unfold at18. let sblx := fresh "sbl" in pose (sblx := 4392%nat); change 4392%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact G'|]. split; [eapply hinv_mem; [exact HI| exact ST'| exact MI']|].
    split; [apply keep_of_callee0; exact AG|]. split; [exact FRL| exact FR4].
  Qed.
  End Sz17.
  Lemma unlink18_spec : ltac:(let t := eval cbv delta [unlink18_spec__stmt] in unlink18_spec__stmt in exact t).
  Proof using UNLINK. intros ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo cs3 cs2 cs1 cs0 cra j0 nbuf ej. ltac2:(SecDiet.SzSec.closeP 'unlink18_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fuzz.

End WithCeil.
End TwB.
End F_fuzz_A.

(* [comment removed for export] *)
Module F_fuzz_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep RegsEquiv MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_A.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac natfold_term t :=
  match t with
  | context C[4096%nat] => let t1 := context C[Z.to_nat 4096] in natfold_term t1
  | _ => t
  end.
Local Ltac natfold_hyp H := let T := type of H in let U := natfold_term T in change U in H.
Local Ltac natfold_concl := lazymatch goal with |- ?G => let U := natfold_term G in change U end.
Local Ltac natfold_lits :=
  repeat match goal with
  | nfH : context [4096%nat] |- _ => natfold_hyp nfH
  end;
  lazymatch goal with
  | |- context [4096%nat] => natfold_concl
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma rodata_wb : forall m, mem_inv ssegs m -> bytes_at ssegs m STR_WB ([Z_to_bv 8 119; Z_to_bv 8 98] ++ [Z_to_bv 8 0]).
Proof using Type. all: natfold_lits. pin_using tt.
  intros m MI. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m STR_WB [Z_to_bv 8 119; Z_to_bv 8 98; Z_to_bv 8 0] MI ltac:(vm_compute; reflexivity) ltac:(unfold STR_WB; lia) ltac:(unfold STR_WB; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia))).
Qed.
Lemma rodata_w : forall m, mem_inv ssegs m -> bytes_at ssegs m STR_W ([Z_to_bv 8 119] ++ [Z_to_bv 8 0]).
Proof using Type. all: natfold_lits. pin_using tt.
  intros m MI. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m STR_W [Z_to_bv 8 119; Z_to_bv 8 0] MI ltac:(vm_compute; reflexivity) ltac:(unfold STR_W; lia) ltac:(unfold STR_W; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia))).
Qed.
Definition devnull : list byte := map b8 DEVNULL.
Lemma rodata_devnull : forall m, mem_inv ssegs m -> bytes_at ssegs m STR_DEVNULL (devnull ++ [Z_to_bv 8 0]).
Proof using Type. all: natfold_lits. pin_using tt.
  intros m MI. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m STR_DEVNULL (devnull ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold STR_DEVNULL; lia) ltac:(unfold STR_DEVNULL, devnull, DEVNULL; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ map app str String.list_ascii_of_string]; lia))).
Qed.
Definition template : list byte := map b8 TEMPLATE ++ [Z_to_bv 8 0].
Lemma rodata_template : forall m, mem_inv ssegs m -> bytes_at ssegs m STR_TEMPLATE template.
Proof using Type. all: natfold_lits. pin_using tt.
  intros m MI. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m STR_TEMPLATE template MI ltac:(vm_compute; reflexivity) ltac:(unfold STR_TEMPLATE; lia) ltac:(unfold STR_TEMPLATE, template, TEMPLATE; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ map app str String.list_ascii_of_string]; lia))).
Qed.
End WithCeil.


Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

(* [comment removed for export] *)
Ltac kf_lit_in Ha :=
  repeat match type of Ha with
  | context [Z.of_nat (cells_size ?cs)] =>
      d_spine_closed cs;
      let z := d_zsize constr:(Z.of_nat (cells_size cs)) in
      d_is_Zlit z;
      change (Z.of_nat (cells_size cs)) with z in Ha
  end.
Ltac keep_frame AG :=
  lazymatch type of AG with agrees_on _ ?m _ =>
    repeat match goal with
    | FR : rw_cells ssegs m _ _ |- _ =>
        apply (agrees_rw_cells _ _ _ _ _ AG) in FR; [| intros a Ha; kf_lit_in Ha; cbn in Ha; fastfirst (first [left; lia | split; [left; lia| lia]])]
    end
  end.

(* [comment removed for export] *)
Ltac spo :=
  eapply hinv_spo;
  [ first [eassumption | eapply hinv_mem; [eassumption| eassumption| eassumption]]
  | eassumption
  | first [eassumption | reflexivity]
  | unfold STDIO_STACK, PCAP_L4_STACK, PCAP_L1_STACK, FUZZ_STACK, FZ; lia ].

Section WithCeil.
Context {CEILV : CEIL}.
Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).

  Lemma implM_errno_l : forall {B} (k : Z -> M PSt B) (s : PSt) Q ms,
    implM ssegs (k (lc_errno (ps_libc s))) s Q ms -> implM ssegs (mbind (s_get_errno (H:=H) (hptr:=hptr)) k) s Q ms.
  Proof using Type. all: natfold_lits. pin_using tt. intros. exact H0. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition btf_post (spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (cs3 cs2 cs1 cs0 cra : word) (m0 : mem) : Z -> PSt -> machine_state -> Prop :=
    fun r s' ms' => exists ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m' FB' (j0 nbuf ej : list byte),
      ms' = MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x33fec) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (if r <? 0 then 0x14140 else 0x14090)) fc None m' (seg_rom ssegs)
      /\ GIo K R s' CL FB' m' /\ hinv R lo spB m' /\ agrees_on (KEEP CL spB) m0 m'
      /\ rw_cells ssegs m' (bv_unsigned spB) [CB 40 j0]
      /\ rw_cells ssegs m' (bv_unsigned spB + 40) [CB 4096 nbuf] /\ firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0]
      /\ rw_cells ssegs m' (bv_unsigned spB + 4136) [CB 256 ej]
      /\ rw_cells ssegs m' (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra]
      /\ (r < 0 \/ r = 0).

  (* [comment removed for export] *)
  Definition fopen_part_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo D : Z) (data : list byte)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s3 = Z_to_bv 64 0x33fec ->
    bytes_at ssegs m D data -> (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a) -> Z.of_nat (length data) < 2^26 ->
    rw_cells ssegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells ssegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells ssegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells ssegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM ssegs (fo <- s_fopen HO TMPNAME true ;;
                 match fo with
                 | None => e <- s_get_errno ;; s_printf (pieces_failed_open e) ;;; mret (-2)
                 | Some fd => n <- s_fwrite HO fd (map bv_unsigned data) ;; s_fclose HO fd ;;;
                              (if negb (n =? zlength (map bv_unsigned data)) then mret (-3) else mret 0)
                 end) s
      (btf_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14054) fc None m (seg_rom ssegs)).
  Section Sz6.
  Variables ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 nbuf ej : ltac2:(SecDiet.SzSec.tyM 'fopen_part_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fopen_part_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_part_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB FCLOSE FOPEN FWRITE HAL PRINTF_O. all: natfold_lits. pin_using (fun (EQB FCLOSE FOPEN FWRITE HAL PRINTF_O : unit) => tt).
    intros G HI TP Es0 Es1 Es3 DAT DIN DLEN FR1 FR2 NB FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN). unfold FZ, FUZZ_STACK in BU, SPM. unfold rc_spmain in SPM. unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW.
    pose proof (name_bytes _ _ _ _ _ _ FR2 NB) as NBY.
    pose proof (bytes_at_bound _ _ _ _ DAT) as DB.
    subst s0 s1 s3.
    unfold implM. iprefix. lstep. lstep. lstep. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rodata_wb mm MI) as RB end.
    rewrite <- tmpname_Z.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply implM_leaf.
      eapply (FOPEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (bv_unsigned spB + 40) STR_WB tmpname [Z_to_bv 8 119; Z_to_bv 8 98] true);
        [ spo | f_equal; lia | reflexivity | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia | exact tmpname_open_w (* [comment removed for export] *)
        | left; right; rewrite tmpname_len; unfold rc_spmain; lia | exact RB | right; split; reflexivity ]. }
    intros fo s' ms' [PO L]. cbv beta in PO. destruct fo as [f|].
    - (* [comment removed for export] *)
      destruct PO as (a0v & m2 & E & EO2 & MI2 & ST2 & AG2 & (Af & -> & G2)). post_regs E.
      apply (fopen_leaf HO EQB) in L as [fd LK].
      pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; left; reflexivity)) as (A1 & _ & _ & A4 & A5 & _).
      cbn [cb_addr cb_size fst snd] in A1, A4, A5. unfold FILE_BLOCK in A4, A5.
      keep_frame AG2.
      assert (DAT2 : bytes_at ssegs m2 D data) by (eapply agrees_bytes_at; [exact AG2 | exact DAT | intros a Ha; right; apply DIN; exact Ha]).
      clear MI. unfold implM. iprefix. lstep. if_false_by (eqz_false Af ltac:(lia)). do 6 lstep.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply (FWRITE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL ((f, Af, FILE_BLOCK) :: FB) f Af D lo data);
          [ spo
          | left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact DAT2
          | left; exact DIN
          | intros fs Hfs; rewrite LK in Hfs; injection Hfs as <-; cbn [f_wbuf fdopen_file]; unfold zlength; cbn [length Z.of_nat]; lia ]. }
      intros n s3' ms3 PO. cbv beta in PO. destruct PO as (a0v & m3 & E & EO3 & MI3 & ST3 & AG3 & G3 & -> & Hn). post_regs E.
      keep_frame AG3. clear MI2.
      unfold implM. iprefix. lstep. lstep. lstep.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply (FCLOSE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s3' CL [] FB f Af lo); [| reflexivity |].
        - cbn [app]. spo.
        - (* [comment removed for export] *)
          eapply (GIo_new_file_not_out HO K HAL); [exact G | exact G3 | congruence]. }
      intros [] s4' ms4 PO. cbv beta in PO. destruct PO as (a0v & m4 & E & EO4 & MI4 & ST4 & AG4 & G4). post_regs E. cbn [app] in G4.
      keep_frame AG4. clear MI3.
      replace (zlength (map bv_unsigned data)) with (Z.of_nat (length data)) by (unfold zlength; rewrite length_map; reflexivity).
      assert (AG : agrees_on (KEEP CL spB) m m4).
      { eapply agrees_on_trans; [apply keep_of_callee0; exact AG2|]. eapply agrees_on_trans; [apply keep_of_callee0; exact AG3| apply keep_of_callee0; exact AG4]. }
      pose proof (hinv_mem _ _ _ _ _ HI ST4 MI4) as HI4.
      unfold implM. iprefix. lstep.
      destruct (Z.eqb_spec n (Z.of_nat (length data))) as [En|Nn].
      + subst n. unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb].
        apply evt_done. apply (implM_ret ssegs). apply evt_done.
        unfold btf_post. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G4|]. split; [exact HI4|]. split; [exact AG|].
        split; [eexact FR1|]. split; [eexact FR2|]. split; [exact NB|]. split; [eexact FR3|]. split; [eexact FR4| right; reflexivity].
      + rewrite (eqb_lits_false n (Z.of_nat (length data))) by lia. cbn [negb].
        apply evt_done. apply (implM_ret ssegs). apply evt_done.
        unfold btf_post. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G4|]. split; [exact HI4|]. split; [exact AG|].
        split; [eexact FR1|]. split; [eexact FR2|]. split; [exact NB|]. split; [eexact FR3|]. split; [eexact FR4| left; reflexivity].
    - (* [comment removed for export] *)
      destruct PO as (a0v & m2 & E & EO2 & MI2 & ST2 & AG2 & -> & G2 & EN & ER). post_regs E.
      keep_frame AG2. clear MI L.
      pose proof (GIo_tls K _ _ _ _ _ G2) as [_ TB]. unfold tls_block_ok in TB. unfold utp in EN, TB. rewrite <- TP in EN, TB.
      set (e := lc_errno (ps_libc s')) in *.
      unfold implM. iprefix. lstep. if_true. do 4 step. lstep. rewrite (sx32_small e) by lia. do 3 lstep.
      apply evt_done. apply implM_errno_l. fold e. eapply (implM_bind ssegs).
      { eapply (PRINTF_O _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo e);
          [ spo | reflexivity | reflexivity | exact ER ]. }
      intros [] s3' ms3 PO. cbv beta in PO. destruct PO as (a0v & m3 & E & EO3 & MI3 & ST3 & AG3 & G3). post_regs E.
      keep_frame AG3. clear MI2.
      apply (implM_ret ssegs). apply evt_done.
      unfold btf_post. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact G3|]. split; [exact (hinv_mem _ _ _ _ _ HI ST3 MI3)|].
      split; [eapply agrees_on_trans; [apply keep_of_callee0; exact AG2| apply keep_of_callee0; exact AG3]|].
      split; [eexact FR1|]. split; [eexact FR2|]. split; [exact NB|]. split; [eexact FR3|]. split; [eexact FR4| left; reflexivity].
  Qed.
  End Sz6.
  Lemma fopen_part_spec : ltac:(let t := eval cbv delta [fopen_part_spec__stmt] in fopen_part_spec__stmt in exact t).
  Proof using EQB FCLOSE FOPEN FWRITE HAL PRINTF_O. all: natfold_lits. intros ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 nbuf ej. ltac2:(SecDiet.SzSec.closeP 'fopen_part_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma implM_errno_ll : forall {B C} (f : Z -> M PSt B) (g : B -> M PSt C) (s : PSt) Q ms,
    implM ssegs (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implM ssegs (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof using Type. all: natfold_lits. pin_using tt. intros. exact H0. Qed.

  Lemma implM_bind_assoc : forall {A B C} (m : M PSt A) (f : A -> M PSt B) (g : B -> M PSt C) s Q ms,
    implM ssegs (mbind m (fun x => mbind (f x) g)) s Q ms -> implM ssegs (mbind (mbind m f) g) s Q ms.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros A B C m f g s Q ms HH. unfold implM, mbind, ebind in *. apply impl_bind_assoc.
    eapply impl_bind_cong; [|exact HH]. intros [|[a s1]] ms' H1; cbn [bind] in *; exact H1.
  Qed.

  Lemma btf_post_back : forall spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 m1 r s ms,
    agrees_on (KEEP CL spB) m0 m1 ->
    btf_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m1 r s ms ->
    btf_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 r s ms.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros until ms. intros AG PO. unfold btf_post in *. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx in PO |- *. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx in PO |- *. destruct_exs PO. destruct PO as (E & G & HI & AG2 & REST).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [exact E|]. split; [exact G|]. split; [exact HI|]. split; [eapply agrees_on_trans; [exact AG| exact AG2]| exact REST].
  Qed.

  Lemma eqz_false_neg1 : bv_eqb (Z_to_bv 64 (-1)) z64 = false.
  Proof using Type. all: natfold_lits. pin_using tt. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition btf_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo D : Z) (data : list byte)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s3 = Z_to_bv 64 0x33fec ->
    bytes_at ssegs m D data -> (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a) -> Z.of_nat (length data) < 2^26 ->
    rw_cells ssegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells ssegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells ssegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells ssegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM ssegs (bufferToFile MOps (prims HO fo_nop sites) TMPNAME (map bv_unsigned data)) s
      (btf_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14038) fc None m (seg_rom ssegs)).
  Section Sz11.
  Variables ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 nbuf ej : ltac2:(SecDiet.SzSec.tyM 'btf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma btf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'btf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB FCLOSE FOPEN FWRITE HAL PRINTF_O PRINTF_R REMOVE. all: natfold_lits. pin_using (fun (EQB FCLOSE FOPEN FWRITE HAL PRINTF_O PRINTF_R REMOVE : unit) => tt).
    intros G HI TP Es0 Es1 Es3 DAT DIN DLEN FR1 FR2 NB FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN). unfold FZ, FUZZ_STACK in BU, SPM. unfold rc_spmain in SPM. unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW.
    pose proof (name_bytes _ _ _ _ _ _ FR2 NB) as NBY.
    pose proof (bytes_at_bound _ _ _ _ DAT) as DB.
    subst s0 s1 s3.
    unfold bufferToFile. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_remove e_last_errno e_printf e_fopen_w e_fwrite e_fclose prims].
    unfold implM. iprefix. lstep. lstep.
    rewrite <- tmpname_Z.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply (REMOVE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (bv_unsigned spB + 40) tmpname);
        [ spo | f_equal; lia | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia
        | right; rewrite tmpname_len; unfold rc_spmain; lia | exact tmpname_ok ]. }
    intros r s' ms' PO. cbv beta in PO. destruct PO as (a0v & m2 & E & EO2 & MI2 & ST2 & AG2 & G2 & -> & Hr). post_regs E.
    rewrite tmpname_Z. keep_frame AG2.
    assert (DAT2 : bytes_at ssegs m2 D data) by (eapply agrees_bytes_at; [exact AG2 | exact DAT | intros a Ha; right; apply DIN; exact Ha]).
    pose proof (hinv_mem _ _ _ _ _ HI ST2 MI2) as HI2. clear MI.
    destruct Hr as [-> | (-> & EN & ER)].
    - (* [comment removed for export] *)
      unfold implM. iprefix. lstep. if_true. apply evt_done.
      cbn [Z.eqb negb]. apply implM_ret_l. cbn [negb].
      eapply (implM_mono ssegs); [| intros r1 s1' ms1 PO; eapply btf_post_back; [apply keep_of_callee0; exact AG2| exact PO]].
      eapply fopen_part_spec; first [exact G2 | exact HI2 | reflexivity | exact DAT2 | exact DIN | exact DLEN | exact NB | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
    - (* [comment removed for export] *)
      pose proof (GIo_tls K _ _ _ _ _ G2) as [_ TB]. unfold tls_block_ok in TB. unfold utp in EN, TB. rewrite <- TP in EN, TB.
      set (e := lc_errno (ps_libc s')) in *.
      unfold implM. iprefix. lstep. if_false_by (eqz_false_neg1). do 4 step. lstep. rewrite (sx32_small e) by lia. lstep. lstep.
      apply evt_done. cbn [Z.eqb negb]. apply implM_errno_ll. cbv beta. fold e.
      destruct (Z.eqb_spec e 2) as [E2|NE2].
      + (* [comment removed for export] *)
        rewrite E2. unfold ENOENT. cbn [Z.eqb negb]. apply implM_ret_l. cbn [negb].
        unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb].
        eapply (implM_mono ssegs); [| intros r1 s1' ms1 PO; eapply btf_post_back; [apply keep_of_callee0; exact AG2| exact PO]].
        eapply fopen_part_spec; first [exact G2 | exact HI2 | reflexivity | exact DAT2 | exact DIN | exact DLEN | exact NB | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
      + (* [comment removed for export] *)
        replace (negb (e =? ENOENT)) with true by (unfold ENOENT; destruct (Z.eqb_spec e 2); [lia| reflexivity]).
        rewrite (eqb_lits_false e 2) by lia. cbn [negb].
        apply implM_bind_assoc. cbv beta.
        unfold implM. iprefix. do 4 lstep.
        apply evt_done. eapply (implM_bind ssegs).
        { eapply (PRINTF_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo e);
            [ spo | reflexivity | reflexivity | exact ER ]. }
        intros [] s3' ms3 PO. cbv beta in PO. destruct PO as (a0v & m3 & E & EO3 & MI3 & ST3 & AG3 & G3). post_regs E.
        keep_frame AG3. clear MI2.
        apply implM_ret_l. cbn [negb]. apply (implM_ret ssegs). apply evt_done.
        unfold btf_post. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G3|]. split; [exact (hinv_mem _ _ _ _ _ HI ST3 MI3)|].
        split; [eapply agrees_on_trans; [apply keep_of_callee0; exact AG2| apply keep_of_callee0; exact AG3]|].
        split; [eexact FR1|]. split; [eexact FR2|]. split; [exact NB|]. split; [eexact FR3|]. split; [eexact FR4| left; reflexivity].
  Qed.
  End Sz11.
  Lemma btf_spec : ltac:(let t := eval cbv delta [btf_spec__stmt] in btf_spec__stmt in exact t).
  Proof using EQB FCLOSE FOPEN FWRITE HAL PRINTF_O PRINTF_R REMOVE. all: natfold_lits. intros ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 nbuf ej. ltac2:(SecDiet.SzSec.closeP 'btf_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fuzz_body (data : list Z) : M PSt unit :=
    '(filename, fd) <- s_mkstemp TEMPLATE ;;
    if fd <? 0 then mret tt else
    s_close fd ;;;
    r <- bufferToFile MOps (prims HO fo_nop sites) filename data ;;
    if r <? 0 then s_unlink filename ;;; mret tt else
    po <- Pcap.pcap_open_offline MOps (prims HO fo_nop sites) (S (length data)) filename ;;
    match po with
    | inl errbuf =>
        with_outfile MOps (prims HO fo_nop sites) (fun out => s_fprintf HO out (pieces_couldnt_open (cstr errbuf))) ;;;
        s_unlink filename ;;; mret tt
    | inr p =>
        p <- packet_loop MOps (prims HO fo_nop sites) (S (length data)) (S (length data)) p ;;
        '(sr, p) <- Pcap.pcap_stats MOps p ;;
        (if sr =? 0 then with_outfile MOps (prims HO fo_nop sites) (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
        Pcap.pcap_close MOps (prims HO fo_nop sites) p ;;;
        s_unlink filename ;;; mret tt
    end.

  Lemma fuzz_unfold : forall data,
    LLVMFuzzerTestOneInput MOps (prims HO fo_nop sites) data =
    (o0 <- (s <- mget ;; mret (ps_outfile s)) ;;
     o <- match o0 with
          | Some f => mret (Some f)
          | None => fo <- s_fopen HO DEVNULL true ;; mupd (set_outfile fo) ;;; mret fo
          end ;;
     match o with None => mret tt | Some _ => fuzz_body data end).
  Proof using Type. all: natfold_lits. pin_using tt. intros data. reflexivity. Qed.
End Fuzz.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_A.TwB.
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
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma rodata_wb : forall m, mem_inv usegs m -> bytes_at usegs m STR_WB ([Z_to_bv 8 119; Z_to_bv 8 98] ++ [Z_to_bv 8 0]).
Proof using Type. all: natfold_lits. pin_using tt.
  intros m MI. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m STR_WB [Z_to_bv 8 119; Z_to_bv 8 98; Z_to_bv 8 0] MI ltac:(vm_compute; reflexivity) ltac:(unfold STR_WB; lia) ltac:(unfold STR_WB; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia))).
Qed.
Lemma rodata_w : forall m, mem_inv usegs m -> bytes_at usegs m STR_W ([Z_to_bv 8 119] ++ [Z_to_bv 8 0]).
Proof using Type. all: natfold_lits. pin_using tt.
  intros m MI. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m STR_W [Z_to_bv 8 119; Z_to_bv 8 0] MI ltac:(vm_compute; reflexivity) ltac:(unfold STR_W; lia) ltac:(unfold STR_W; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia))).
Qed.
Definition devnull : list byte := map b8 DEVNULL.
Lemma rodata_devnull : forall m, mem_inv usegs m -> bytes_at usegs m STR_DEVNULL (devnull ++ [Z_to_bv 8 0]).
Proof using Type. all: natfold_lits. pin_using tt.
  intros m MI. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m STR_DEVNULL (devnull ++ [Z_to_bv 8 0]) MI ltac:(vm_compute; reflexivity) ltac:(unfold STR_DEVNULL; lia) ltac:(unfold STR_DEVNULL, devnull, DEVNULL; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ map app str String.list_ascii_of_string]; lia))).
Qed.
Definition template : list byte := map b8 TEMPLATE ++ [Z_to_bv 8 0].
Lemma rodata_template : forall m, mem_inv usegs m -> bytes_at usegs m STR_TEMPLATE template.
Proof using Type. all: natfold_lits. pin_using tt.
  intros m MI. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m STR_TEMPLATE template MI ltac:(vm_compute; reflexivity) ltac:(unfold STR_TEMPLATE; lia) ltac:(unfold STR_TEMPLATE, template, TEMPLATE; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ map app str String.list_ascii_of_string]; lia))).
Qed.
End WithCeil.


Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

(* [comment removed for export] *)
Ltac kf_lit_in Ha :=
  repeat match type of Ha with
  | context [Z.of_nat (cells_size ?cs)] =>
      d_spine_closed cs;
      let z := d_zsize constr:(Z.of_nat (cells_size cs)) in
      d_is_Zlit z;
      change (Z.of_nat (cells_size cs)) with z in Ha
  end.
Ltac keep_frame AG :=
  lazymatch type of AG with agrees_on _ ?m _ =>
    repeat match goal with
    | FR : rw_cells usegs m _ _ |- _ =>
        apply (agrees_rw_cells _ _ _ _ _ AG) in FR; [| intros a Ha; kf_lit_in Ha; cbn in Ha; fastfirst (first [left; lia | split; [left; lia| lia]])]
    end
  end.

(* [comment removed for export] *)
Ltac spo :=
  eapply hinv_spo;
  [ first [eassumption | eapply hinv_mem; [eassumption| eassumption| eassumption]]
  | eassumption
  | first [eassumption | reflexivity]
  | unfold STDIO_STACK, PCAP_L4_STACK, PCAP_L1_STACK, FUZZ_STACK, FZ; lia ].

Section WithCeil.
Context {CEILV : CEIL}.
Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).

  Lemma implM_errno_l : forall {B} (k : Z -> M PSt B) (s : PSt) Q ms,
    implM usegs (k (lc_errno (ps_libc s))) s Q ms -> implM usegs (mbind (s_get_errno (H:=H) (hptr:=hptr)) k) s Q ms.
  Proof using Type. all: natfold_lits. pin_using tt. intros. exact H0. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition btf_post (spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (cs3 cs2 cs1 cs0 cra : word) (m0 : mem) : Z -> PSt -> machine_state -> Prop :=
    fun r s' ms' => exists ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m' FB' (j0 nbuf ej : list byte),
      ms' = MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x34060) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (if r <? 0 then 0x141d8 else 0x14110)) fc None m' (seg_rom usegs)
      /\ GIo K R s' CL FB' m' /\ hinv R lo spB m' /\ agrees_on (KEEP CL spB) m0 m'
      /\ rw_cells usegs m' (bv_unsigned spB) [CB 40 j0]
      /\ rw_cells usegs m' (bv_unsigned spB + 40) [CB 4096 nbuf] /\ firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0]
      /\ rw_cells usegs m' (bv_unsigned spB + 4136) [CB 256 ej]
      /\ rw_cells usegs m' (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra]
      /\ (r < 0 \/ r = 0).

  (* [comment removed for export] *)
  Definition fopen_part_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo D : Z) (data : list byte)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s3 = Z_to_bv 64 0x34060 ->
    bytes_at usegs m D data -> (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a) -> Z.of_nat (length data) < 2^26 ->
    rw_cells usegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells usegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells usegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells usegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM usegs (fo <- s_fopen HO TMPNAME true ;;
                 match fo with
                 | None => e <- s_get_errno ;; s_printf (pieces_failed_open e) ;;; mret (-2)
                 | Some fd => n <- s_fwrite HO fd (map bv_unsigned data) ;; s_fclose HO fd ;;;
                              (if negb (n =? zlength (map bv_unsigned data)) then mret (-3) else mret 0)
                 end) s
      (btf_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140d4) fc None m (seg_rom usegs)).
  Section Sz6.
  Variables ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 nbuf ej : ltac2:(SecDiet.SzSec.tyM 'fopen_part_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fopen_part_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_part_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB FCLOSE FOPEN FWRITE HAL PRINTF_O. all: natfold_lits. pin_using (fun (EQB FCLOSE FOPEN FWRITE HAL PRINTF_O : unit) => tt).
 intros G HI TP Es0 Es1 Es3 DAT DIN DLEN FR1 FR2 NB FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN). unfold FZ, FUZZ_STACK in BU, SPM. unfold rc_spmain in SPM. unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW.
    pose proof (name_bytes _ _ _ _ _ _ FR2 NB) as NBY.
    pose proof (bytes_at_bound _ _ _ _ DAT) as DB.
    subst s0 s1 s3.
    unfold implM. iprefix. lstep. lstep. lstep. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rodata_wb mm MI) as RB end.
    rewrite <- tmpname_Z.
    apply evt_done. eapply (implM_bind usegs).
    { eapply implM_leaf.
      eapply (FOPEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (bv_unsigned spB + 40) STR_WB tmpname [Z_to_bv 8 119; Z_to_bv 8 98] true);
        [ spo | f_equal; lia | reflexivity | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia | exact tmpname_open_w (* [comment removed for export] *)
        | left; right; rewrite tmpname_len; unfold rc_spmain; lia | exact RB | right; split; reflexivity ]. }
    intros fo s' ms' [PO L]. cbv beta in PO. destruct fo as [f|].
    - (* [comment removed for export] *)
      destruct PO as (a0v & m2 & E & EO2 & MI2 & ST2 & AG2 & (Af & -> & G2)). post_regs E.
      apply (fopen_leaf HO EQB) in L as [fd LK].
      pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; left; reflexivity)) as (A1 & _ & _ & A4 & A5 & _).
      cbn [cb_addr cb_size fst snd] in A1, A4, A5. unfold FILE_BLOCK in A4, A5.
      keep_frame AG2.
      assert (DAT2 : bytes_at usegs m2 D data) by (eapply agrees_bytes_at; [exact AG2 | exact DAT | intros a Ha; right; apply DIN; exact Ha]).
      clear MI. unfold implM. iprefix. lstep. if_false_by (eqz_false Af ltac:(lia)). do 6 lstep.
      apply evt_done. eapply (implM_bind usegs).
      { eapply (FWRITE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL ((f, Af, FILE_BLOCK) :: FB) f Af D lo data);
          [ spo
          | left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact DAT2
          | left; exact DIN
          | intros fs Hfs; rewrite LK in Hfs; injection Hfs as <-; cbn [f_wbuf fdopen_file]; unfold zlength; cbn [length Z.of_nat]; lia ]. }
      intros n s3' ms3 PO. cbv beta in PO. destruct PO as (a0v & m3 & E & EO3 & MI3 & ST3 & AG3 & G3 & -> & Hn). post_regs E.
      keep_frame AG3. clear MI2.
      unfold implM. iprefix. lstep. lstep. lstep.
      apply evt_done. eapply (implM_bind usegs).
      { eapply (FCLOSE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s3' CL [] FB f Af lo); [| reflexivity |].
        - cbn [app]. spo.
        - (* [comment removed for export] *)
          eapply (GIo_new_file_not_out HO K HAL); [exact G | exact G3 | congruence]. }
      intros [] s4' ms4 PO. cbv beta in PO. destruct PO as (a0v & m4 & E & EO4 & MI4 & ST4 & AG4 & G4). post_regs E. cbn [app] in G4.
      keep_frame AG4. clear MI3.
      replace (zlength (map bv_unsigned data)) with (Z.of_nat (length data)) by (unfold zlength; rewrite length_map; reflexivity).
      assert (AG : agrees_on (KEEP CL spB) m m4).
      { eapply agrees_on_trans; [apply keep_of_callee0; exact AG2|]. eapply agrees_on_trans; [apply keep_of_callee0; exact AG3| apply keep_of_callee0; exact AG4]. }
      pose proof (hinv_mem _ _ _ _ _ HI ST4 MI4) as HI4.
      unfold implM. iprefix. lstep.
      destruct (Z.eqb_spec n (Z.of_nat (length data))) as [En|Nn].
      + subst n. unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb].
        apply evt_done. apply (implM_ret usegs). apply evt_done.
        unfold btf_post. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G4|]. split; [exact HI4|]. split; [exact AG|].
        split; [eexact FR1|]. split; [eexact FR2|]. split; [exact NB|]. split; [eexact FR3|]. split; [eexact FR4| right; reflexivity].
      + rewrite (eqb_lits_false n (Z.of_nat (length data))) by lia. cbn [negb].
        apply evt_done. apply (implM_ret usegs). apply evt_done.
        unfold btf_post. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G4|]. split; [exact HI4|]. split; [exact AG|].
        split; [eexact FR1|]. split; [eexact FR2|]. split; [exact NB|]. split; [eexact FR3|]. split; [eexact FR4| left; reflexivity].
    - (* [comment removed for export] *)
      destruct PO as (a0v & m2 & E & EO2 & MI2 & ST2 & AG2 & -> & G2 & EN & ER). post_regs E.
      keep_frame AG2. clear MI L.
      pose proof (GIo_tls K _ _ _ _ _ G2) as [_ TB]. unfold tls_block_ok_u in TB. unfold utp in EN, TB. rewrite <- TP in EN, TB.
      assert (E4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
      { destruct TB as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q4 Hq4]. apply Z.mod_divide; [lia|]. exists (q4 * 4 + 9)%Z. lia. }
      set (e := lc_errno (ps_libc s')) in *.
      unfold implM. iprefix. lstep. if_true. do 4 step.
      (* [comment removed for export] *)
      step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(lia)). step. rewrite (and3_aligned (bv_unsigned tp + -164)) by lia. step. if_false.
      lstep. rewrite (sx32_small e) by lia. do 3 lstep.
      apply evt_done. apply implM_errno_l. fold e. eapply (implM_bind usegs).
      { eapply (PRINTF_O _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo e);
          [ spo | reflexivity | reflexivity | exact ER ]. }
      intros [] s3' ms3 PO. cbv beta in PO. destruct PO as (a0v & m3 & E & EO3 & MI3 & ST3 & AG3 & G3). post_regs E.
      keep_frame AG3. clear MI2.
      apply (implM_ret usegs). apply evt_done.
      unfold btf_post. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact G3|]. split; [exact (hinv_mem _ _ _ _ _ HI ST3 MI3)|].
      split; [eapply agrees_on_trans; [apply keep_of_callee0; exact AG2| apply keep_of_callee0; exact AG3]|].
      split; [eexact FR1|]. split; [eexact FR2|]. split; [exact NB|]. split; [eexact FR3|]. split; [eexact FR4| left; reflexivity].
  Qed.
  End Sz6.
  Lemma fopen_part_spec : ltac:(let t := eval cbv delta [fopen_part_spec__stmt] in fopen_part_spec__stmt in exact t).
  Proof using EQB FCLOSE FOPEN FWRITE HAL PRINTF_O. all: natfold_lits. intros ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 nbuf ej. ltac2:(SecDiet.SzSec.closeP 'fopen_part_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Lemma implM_errno_ll : forall {B C} (f : Z -> M PSt B) (g : B -> M PSt C) (s : PSt) Q ms,
    implM usegs (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implM usegs (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof using Type. all: natfold_lits. pin_using tt. intros. exact H0. Qed.

  Lemma implM_bind_assoc : forall {A B C} (m : M PSt A) (f : A -> M PSt B) (g : B -> M PSt C) s Q ms,
    implM usegs (mbind m (fun x => mbind (f x) g)) s Q ms -> implM usegs (mbind (mbind m f) g) s Q ms.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros A B C m f g s Q ms HH. unfold implM, mbind, ebind in *. apply impl_bind_assoc.
    eapply impl_bind_cong; [|exact HH]. intros [|[a s1]] ms' H1; cbn [bind] in *; exact H1.
  Qed.

  Lemma btf_post_back : forall spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 m1 r s ms,
    agrees_on (KEEP CL spB) m0 m1 ->
    btf_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m1 r s ms ->
    btf_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 r s ms.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros until ms. intros AG PO. unfold btf_post in *. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx in PO |- *. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx in PO |- *. destruct_exs PO. destruct PO as (E & G & HI & AG2 & REST).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [exact E|]. split; [exact G|]. split; [exact HI|]. split; [eapply agrees_on_trans; [exact AG| exact AG2]| exact REST].
  Qed.

  Lemma eqz_false_neg1 : bv_eqb (Z_to_bv 64 (-1)) z64 = false.
  Proof using Type. all: natfold_lits. pin_using tt. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition btf_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo D : Z) (data : list byte)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R ->
    s0 = Z_to_bv 64 (Z.of_nat (length data)) -> s1 = Z_to_bv 64 D -> s3 = Z_to_bv 64 0x34060 ->
    bytes_at usegs m D data -> (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a) -> Z.of_nat (length data) < 2^26 ->
    rw_cells usegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells usegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells usegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells usegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM usegs (bufferToFile MOps (prims HO fo_nop sites) TMPNAME (map bv_unsigned data)) s
      (btf_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140ac) fc None m (seg_rom usegs)).
  Section Sz11.
  Variables ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 nbuf ej : ltac2:(SecDiet.SzSec.tyM 'btf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma btf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'btf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB FCLOSE FOPEN FWRITE HAL PRINTF_O PRINTF_R REMOVE. all: natfold_lits. pin_using (fun (EQB FCLOSE FOPEN FWRITE HAL PRINTF_O PRINTF_R REMOVE : unit) => tt).
 intros G HI TP Es0 Es1 Es3 DAT DIN DLEN FR1 FR2 NB FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN). unfold FZ, FUZZ_STACK in BU, SPM. unfold rc_spmain in SPM. unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW.
    pose proof (name_bytes _ _ _ _ _ _ FR2 NB) as NBY.
    pose proof (bytes_at_bound _ _ _ _ DAT) as DB.
    subst s0 s1 s3.
    unfold bufferToFile. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_remove e_last_errno e_printf e_fopen_w e_fwrite e_fclose prims].
    unfold implM. iprefix. lstep. lstep.
    rewrite <- tmpname_Z.
    apply evt_done. eapply (implM_bind usegs).
    { eapply (REMOVE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (bv_unsigned spB + 40) tmpname);
        [ spo | f_equal; lia | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia
        | right; rewrite tmpname_len; unfold rc_spmain; lia | exact tmpname_ok ]. }
    intros r s' ms' PO. cbv beta in PO. destruct PO as (a0v & m2 & E & EO2 & MI2 & ST2 & AG2 & G2 & -> & Hr). post_regs E.
    rewrite tmpname_Z. keep_frame AG2.
    assert (DAT2 : bytes_at usegs m2 D data) by (eapply agrees_bytes_at; [exact AG2 | exact DAT | intros a Ha; right; apply DIN; exact Ha]).
    pose proof (hinv_mem _ _ _ _ _ HI ST2 MI2) as HI2. clear MI.
    destruct Hr as [-> | (-> & EN & ER)].
    - (* [comment removed for export] *)
      unfold implM. iprefix. lstep. if_true. apply evt_done.
      cbn [Z.eqb negb]. apply implM_ret_l. cbn [negb].
      eapply (implM_mono usegs); [| intros r1 s1' ms1 PO; eapply btf_post_back; [apply keep_of_callee0; exact AG2| exact PO]].
      eapply fopen_part_spec; first [exact G2 | exact HI2 | reflexivity | exact DAT2 | exact DIN | exact DLEN | exact NB | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
    - (* [comment removed for export] *)
      pose proof (GIo_tls K _ _ _ _ _ G2) as [_ TB]. unfold tls_block_ok_u in TB. unfold utp in EN, TB. rewrite <- TP in EN, TB.
      assert (E4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
      { destruct TB as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q4 Hq4]. apply Z.mod_divide; [lia|]. exists (q4 * 4 + 9)%Z. lia. }
      set (e := lc_errno (ps_libc s')) in *.
      unfold implM. iprefix. lstep. if_false_by (eqz_false_neg1). do 4 step.
      (* [comment removed for export] *)
      step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(lia)). step. rewrite (and3_aligned (bv_unsigned tp + -164)) by lia. step. if_false.
      lstep. rewrite (sx32_small e) by lia. lstep. lstep.
      apply evt_done. cbn [Z.eqb negb]. apply implM_errno_ll. cbv beta. fold e.
      destruct (Z.eqb_spec e 2) as [E2|NE2].
      + (* [comment removed for export] *)
        rewrite E2. unfold ENOENT. cbn [Z.eqb negb]. apply implM_ret_l. cbn [negb].
        unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb].
        eapply (implM_mono usegs); [| intros r1 s1' ms1 PO; eapply btf_post_back; [apply keep_of_callee0; exact AG2| exact PO]].
        eapply fopen_part_spec; first [exact G2 | exact HI2 | reflexivity | exact DAT2 | exact DIN | exact DLEN | exact NB | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
      + (* [comment removed for export] *)
        replace (negb (e =? ENOENT)) with true by (unfold ENOENT; destruct (Z.eqb_spec e 2); [lia| reflexivity]).
        rewrite (eqb_lits_false e 2) by lia. cbn [negb].
        apply implM_bind_assoc. cbv beta.
        unfold implM. iprefix. do 4 lstep.
        apply evt_done. eapply (implM_bind usegs).
        { eapply (PRINTF_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo e);
            [ spo | reflexivity | reflexivity | exact ER ]. }
        intros [] s3' ms3 PO. cbv beta in PO. destruct PO as (a0v & m3 & E & EO3 & MI3 & ST3 & AG3 & G3). post_regs E.
        keep_frame AG3. clear MI2.
        apply implM_ret_l. cbn [negb]. apply (implM_ret usegs). apply evt_done.
        unfold btf_post. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G3|]. split; [exact (hinv_mem _ _ _ _ _ HI ST3 MI3)|].
        split; [eapply agrees_on_trans; [apply keep_of_callee0; exact AG2| apply keep_of_callee0; exact AG3]|].
        split; [eexact FR1|]. split; [eexact FR2|]. split; [exact NB|]. split; [eexact FR3|]. split; [eexact FR4| left; reflexivity].
  Qed.
  End Sz11.
  Lemma btf_spec : ltac:(let t := eval cbv delta [btf_spec__stmt] in btf_spec__stmt in exact t).
  Proof using EQB FCLOSE FOPEN FWRITE HAL PRINTF_O PRINTF_R REMOVE. all: natfold_lits. intros ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 nbuf ej. ltac2:(SecDiet.SzSec.closeP 'btf_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fuzz_body (data : list Z) : M PSt unit :=
    '(filename, fd) <- s_mkstemp TEMPLATE ;;
    if fd <? 0 then mret tt else
    s_close fd ;;;
    r <- bufferToFile MOps (prims HO fo_nop sites) filename data ;;
    if r <? 0 then s_unlink filename ;;; mret tt else
    po <- Pcap.pcap_open_offline MOps (prims HO fo_nop sites) (S (length data)) filename ;;
    match po with
    | inl errbuf =>
        with_outfile MOps (prims HO fo_nop sites) (fun out => s_fprintf HO out (pieces_couldnt_open (cstr errbuf))) ;;;
        s_unlink filename ;;; mret tt
    | inr p =>
        p <- packet_loop MOps (prims HO fo_nop sites) (S (length data)) (S (length data)) p ;;
        '(sr, p) <- Pcap.pcap_stats MOps p ;;
        (if sr =? 0 then with_outfile MOps (prims HO fo_nop sites) (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
        Pcap.pcap_close MOps (prims HO fo_nop sites) p ;;;
        s_unlink filename ;;; mret tt
    end.

  Lemma fuzz_unfold : forall data,
    LLVMFuzzerTestOneInput MOps (prims HO fo_nop sites) data =
    (o0 <- (s <- mget ;; mret (ps_outfile s)) ;;
     o <- match o0 with
          | Some f => mret (Some f)
          | None => fo <- s_fopen HO DEVNULL true ;; mupd (set_outfile fo) ;;; mret fo
          end ;;
     match o with None => mret tt | Some _ => fuzz_body data end).
  Proof using Type. all: natfold_lits. pin_using tt. intros data. reflexivity. Qed.
End Fuzz.

End WithCeil.
End TwB.
End F_fuzz_B.

(* [comment removed for export] *)
Module F_fuzz_C.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep RegsEquiv MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_B.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac natfold_term t :=
  match t with
  | context C[4096%nat] => let t1 := context C[Z.to_nat 4096] in natfold_term t1
  | _ => t
  end.
Local Ltac natfold_hyp H := let T := type of H in let U := natfold_term T in change U in H.
Local Ltac natfold_concl := lazymatch goal with |- ?G => let U := natfold_term G in change U end.
Local Ltac natfold_lits :=
  repeat match goal with
  | nfH : context [4096%nat] |- _ => natfold_hyp nfH
  end;
  lazymatch goal with
  | |- context [4096%nat] => natfold_concl
  | |- _ => idtac
  end.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import EasAmong.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).


  Lemma packet_loop_S : forall f ng (p : pcapT),
    packet_loop MOps (prims HO fo_nop sites) (S f) ng p =
    mo_bind MOps (Pcap.pcap_next_ex MOps (prims HO fo_nop sites) ng p) (fun x => let '(r, p) := x in
      if 0 <? r then
        mo_bind MOps (with_outfile MOps (prims HO fo_nop sites) (fun out => e_fprintf (prims HO fo_nop sites) out (pieces_packet_length (h_caplen (pc_header p)) (h_len (pc_header p)))))
                (fun _ => packet_loop MOps (prims HO fo_nop sites) f ng p)
      else mo_ret MOps p).
  Proof using Type. all: natfold_lits. pin_using tt. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma with_outfile_l : forall {A B} (k : hptr -> M PSt A) (g : A -> M PSt B) (s : PSt) Q ms,
    (forall out, ps_outfile s = Some out -> implM ssegs (mbind (k out) g) s Q ms) ->
    implM ssegs (mo_bind MOps (with_outfile MOps (prims HO fo_nop sites) k) g) s Q ms.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros A B k g s Q ms HK. unfold implM in *. cbn. destruct (ps_outfile s) as [out|].
    - exact (HK out eq_refl).
    - cbn. apply evt_done. exact I.
  Qed.

  Lemma GIo_outfile_some : forall R (s : PSt) CL FB m q, GIo K R s CL FB m -> ps_outfile s = Some q ->
    exists A, In (q, A, 1264) FB /\ rw_cells ssegs m 0x339c0 [C8 (Z_to_bv 64 A)].
  Proof using Type. all: natfold_lits. pin_using tt. intros R s CL FB m q G EO. destruct G as (_ & _ & (_ & _ & HA) & _). rewrite EO in HA. exact HA. Qed.
  Lemma GIo_outfile_none : forall R (s : PSt) CL FB m, GIo K R s CL FB m -> ps_outfile s = None ->
    rw_cells ssegs m 0x339c0 [C8 (Z_to_bv 64 0)].
  Proof using Type. all: natfold_lits. pin_using tt. intros R s CL FB m G EO. destruct G as (_ & _ & (_ & _ & HA) & _). rewrite EO in HA. exact HA. Qed.

  Lemma PCAPR_hdr : forall P (p : pcapT) PB FB m, PCAPR P p PB FB m ->
    rw_cells ssegs m (P + 520) (hdr_cells (pc_header p)) /\ 0 <= h_caplen (pc_header p) < 2^32 /\ 0 <= h_len (pc_header p) < 2^32.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros P p PB FB m (Af & Hin & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (pcap_cells_split4 _ _ _ _ (C8 (Z_to_bv 64 Af)) _ _ _ eq_refl CELLS) as (_ & _ & H3 & _).
    pose proof WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc & Hl & _). split; [exact H3|]. split; [exact Hc| exact Hl].
  Qed.

  (* [comment removed for export] *)
  Definition lx_post (spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (cs3 cs2 cs1 cs0 cra : word) (m0 : mem) (P : Z) : pcapT -> PSt -> machine_state -> Prop :=
    fun p' s' ms' => exists ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m' PB' FB' (j0 : list byte) (pkc : cell) (nbuf ej : list byte),
      ms' = MS (mkR ra spB gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x33fec) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x140f0) fc None m' (seg_rom ssegs)
      /\ GIo K R s' (CL ++ PB') FB' m' /\ PCAPR_closable P p' PB' FB' m' /\ hinv R lo spB m' /\ agrees_on (KEEP CL spB) m0 m'
      /\ ps_outfile s' <> Some (pc_rfile p')
      /\ rw_cells ssegs m' (bv_unsigned spB) [CB 24 j0]
      /\ rw_cells ssegs m' (bv_unsigned spB + 24) [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))]
      /\ rw_cells ssegs m' (bv_unsigned spB + 32) [pkc] /\ csize pkc = 8%nat
      /\ rw_cells ssegs m' (bv_unsigned spB + 40) [CB 4096 nbuf] /\ firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0]
      /\ rw_cells ssegs m' (bv_unsigned spB + 4136) [CB 256 ej]
      /\ rw_cells ssegs m' (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra].

  Lemma lx_post_back : forall spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 m1 P r s ms,
    agrees_on (KEEP CL spB) m0 m1 ->
    lx_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m1 P r s ms ->
    lx_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 P r s ms.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros until ms. intros AG PO. unfold lx_post in *. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx in PO |- *. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx in PO |- *. destruct_exs PO. destruct PO as (E & G & PC & HI & AG2 & REST).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [exact E|]. split; [exact G|]. split; [exact PC|]. split; [exact HI|]. split; [eapply agrees_on_trans; [exact AG| exact AG2]| exact REST].
  Qed.

  (* [comment removed for export] *)
  Lemma iter_spec : forall (f : nat) (ng : nat) (ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL PB FB : list cblk) (lo P : Z) (p : pcapT)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte) (pkc : cell),
    GIo K R s (CL ++ PB) FB m -> PCAPR P p PB FB m -> hinv R lo spB m -> tp = rc_tp R -> sites = sites_at (bv_unsigned spB) ->
    ps_outfile s <> Some (pc_rfile p) ->
    rw_cells ssegs m (bv_unsigned spB) [CB 24 j0] ->
    rw_cells ssegs m (bv_unsigned spB + 24) [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))] ->
    rw_cells ssegs m (bv_unsigned spB + 32) [pkc] -> csize pkc = 8%nat ->
    rw_cells ssegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells ssegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells ssegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM ssegs (mo_bind MOps (with_outfile MOps (prims HO fo_nop sites) (fun out => e_fprintf (prims HO fo_nop sites) out (pieces_packet_length (h_caplen (pc_header p)) (h_len (pc_header p)))))
                         (fun _ => packet_loop MOps (prims HO fo_nop sites) f ng p)) s
      (lx_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m P)
      (MS (mkR ra spB gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 FMT_PACKET_LENGTH) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x33fec) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140c4) fc None m (seg_rom ssegs)).
  Proof using FPRINTF_DD PNEXT. all: natfold_lits. pin_using (fun (FPRINTF_DD PNEXT : unit) => tt).
    induction f as [|f IH]; intros until pkc; intros G PC HI TP SITES NOF FR1 FRH FRP PKC FR2 NB FR3 FR4.
    all: pose proof HI as (ST & LO & BU & SPM & MI & ALN); unfold FZ, FUZZ_STACK in BU, SPM; unfold rc_spmain in SPM; unfold rc_lo in LO.
    all: pose proof (bv_unsigned_in_range 64 spB) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    all: pose proof (GIo_spw K _ _ _ _ _ G) as SPW.
    all: pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G (PCAPR_self_in _ _ _ _ _ PC)) as (P1 & _ & _ & P4 & _); pose proof (psize_pos p) as PS.
    all: pose proof (PCAPR_hdr _ _ _ _ _ PC) as (HDR & HC & HL).
    all: apply with_outfile_l; intros out EO; destruct (GIo_outfile_some _ _ _ _ _ _ G EO) as (A & AIN & OC).
    all: pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact AIN)) as (A1 & _ & _ & A4 & _); cbn [cb_addr cb_size fst snd] in A1, A4.
    all: unfold PCAP_HDR_OFF in *; unfold hdr_cells in HDR.
    all: unfold implM; iprefix; do 6 lstep.
    all: apply evt_done; eapply (implM_bind ssegs);
      [ eapply (FPRINTF_DD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s (CL ++ PB) FB out A lo (h_caplen (pc_header p)) (h_len (pc_header p)));
        [ spo | exact AIN | reflexivity | reflexivity | reflexivity | reflexivity | exact HC | exact HL ]
      | ].
    all: intros [] s2' ms2 PO; cbv beta in PO; destruct PO as (a0v & m2 & E & EO2 & MI2 & ST2 & AG2 & G2); post_regs E.
    all: assert (PC2 : PCAPR P p PB FB m2) by (eapply (PCAPR_agree _ _ _ _ _ _ _ AG2); [| exact PC]; intros a Ha; right; apply in_block_app; right; exact Ha).
    all: assert (NOF2 : ps_outfile s2' <> Some (pc_rfile p)) by (rewrite EO2; exact NOF).
    all: keep_frame AG2; clear MI OC HDR.
    all: pose proof (hinv_mem _ _ _ _ _ HI ST2 MI2) as HI2.
    - (* [comment removed for export] *)
      apply (implM_unr ssegs s2').
    - rewrite packet_loop_S.
      unfold implM. iprefix. do 4 lstep.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply implM_leaf.
        eapply (PNEXT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s2' CL PB FB lo P (bv_unsigned spB + 24) (bv_unsigned spB + 32) p ng (C8 (Z_to_bv 64 (P + 520))) pkc);
          [ spo | exact PC2 | rewrite SITES; unfold D_NEXT_EX; f_equal; lia | reflexivity | f_equal; lia | f_equal; lia
          | exact FRH | reflexivity | exact FRP | exact PKC
          | lia | unfold rc_spmain; lia | lia | unfold rc_spmain; lia | left; lia
          | apply aligned16_8; [exact ALN| reflexivity] | apply aligned16_8; [exact ALN| reflexivity] ]. }
      intros [st p'] s3' ms3 [PO L]. cbv beta in PO. destruct PO as (a0v3 & m3 & PB3 & pk3 & E & EO3 & MI3 & ST3 & AG3 & G3 & PC3 & PCC3 & -> & Hst & FRH3 & FRP3 & PKC3). post_regs E.
      apply (pcap_next_ex_rfile HO sites) in L.
      assert (NOF3 : ps_outfile s3' <> Some (pc_rfile p')) by (rewrite EO3, L; exact NOF2).
      clear FRH FRP. keep_frame AG3. clear MI2.
      assert (AGK : agrees_on (KEEP CL spB) m m3).
      { eapply agrees_on_trans.
        - eapply agrees_on_weaken; [exact AG2|]. unfold KEEP, client_keeps, FZ. intros a [Ha|Ha]; [left; lia| right; apply in_block_app; left; exact Ha].
        - eapply agrees_on_weaken; [exact AG3|]. unfold KEEP, client_keeps, FZ. cbv beta. intros a [Ha|Ha]; [split; [left; lia| lia]|].
          pose proof (GIo_CLc_facts K _ _ _ _ _ _ _ G3 Ha) as [Hc _]. split; [right; exact Ha| lia]. }
      unfold PCAP_HDR_OFF in FRH3.
      unfold implM. iprefix. lstep.
      destruct Hst as [-> | Hst].
      + (* [comment removed for export] *)
        change (bv_lts z64 (Z_to_bv 64 1)) with true. cbn [Z.ltb].
        apply evt_done. eapply (implM_mono ssegs); [| intros r1 s1' ms1 PO; eapply lx_post_back; [exact AGK| exact PO]].
        eapply IH; [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact G3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (PC3 ltac:((keep_hyps CEILV spB pkc pk3; lia)))]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (hinv_mem _ _ _ _ _ HI ST3 MI3)]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact TP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SITES]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact NOF3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FRH3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FRP3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact PKC3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact NB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FR4]) ].
      + (* [comment removed for export] *)
        assert (PCC : PCAPR_closable P p' PB3 FB m3) by (destruct Hst as [-> | ->]; [apply PCAPR_closable_of; apply PC3; lia | apply PCC3; reflexivity]).
        replace (bv_lts z64 (Z_to_bv 64 st)) with false by (destruct Hst as [-> | ->]; reflexivity).
        replace (0 <? st) with false by (destruct Hst as [-> | ->]; reflexivity).
        apply evt_done. apply (implM_ret ssegs). apply evt_done.
        unfold lx_post. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G3|]. split; [exact PCC|]. split; [exact (hinv_mem _ _ _ _ _ HI ST3 MI3)|]. split; [exact AGK|].
        split; [exact NOF3|].
        split; [eexact FR1|]. split; [exact FRH3|]. split; [exact FRP3|]. split; [exact PKC3|].
        split; [eexact FR2|]. split; [exact NB|]. split; [eexact FR3| eexact FR4].
  Qed.

  Lemma nez_true_neg1 : negb (bv_eqb (Z_to_bv 64 (-1)) z64) = true.
  Proof using Type. all: natfold_lits. pin_using tt. reflexivity. Qed.

  Lemma frame_join40 : forall m A (a : list byte) (h : cell) (k : cell),
    rw_cells ssegs m A [CB 24 a] -> rw_cells ssegs m (A + 24) [h] -> csize h = 8%nat -> rw_cells ssegs m (A + 32) [k] -> csize k = 8%nat ->
    exists j, rw_cells ssegs m A [CB 40 j].
  Proof using Type. all: natfold_lits. pin_using tt.
    intros m A a h k H1 H2 Hh H3 Hk.
    assert (X : rw_cells ssegs m A ([CB 24 a] ++ [h] ++ [k])).
    { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. replace (A + Z.of_nat 24) with (A + 24) by lia.
      apply rw_cells_app. split; [exact H2|]. cbn [cells_size]. rewrite Hh. replace (A + 24 + Z.of_nat (8 + 0)) with (A + 32) by lia. exact H3. }
    apply rw_cells_forget in X. cbn [cells_size app] in X. rewrite Hh, Hk in X. exact X.
  Qed.

  Lemma PCAPRC_self_in : forall P (p : pcapT) PB FB m, PCAPR_closable P p PB FB m -> In (pc_self p, P, psize p) PB.
  Proof using Type. all: natfold_lits. pin_using tt. intros P p PB FB m (Af & _ & (B & I & j & pad & bs & -> & _)). left. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma name_bytes_slack : forall m A n (buf pre : list byte) k,
    rw_cells ssegs m A [CB n buf] -> firstn k buf = pre ++ [Z_to_bv 8 0] -> bytes_at ssegs m A (pre ++ Z_to_bv 8 0 :: skipn k buf).
  Proof using Type. all: natfold_lits. pin_using tt.
    intros m A n buf pre k RC E. apply rw_cells_bytes_at in RC. cbn [cells_bytes cbytes] in RC. rewrite app_nil_r in RC.
    rewrite <- (firstn_skipn k buf), E, <- app_assoc in RC. exact RC.
  Qed.
  (* [comment removed for export] *)
  Lemma neg_mod8_slack : forall E T, E mod 8 = 0 -> T <= E -> (- T) mod 8 <= E - T.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros E T HE HT. replace (- T) with ((E - T) + (- (E / 8)) * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z_mod_plus_full. apply Z.mod_le; lia.
  Qed.

  Lemma skipn_length_le : forall {A} k (l : list A) n, (n + k <= length l)%nat -> (n <= length (skipn k l))%nat.
  Proof using Type. all: natfold_lits. pin_using tt. intros A k l n Hl. rewrite length_skipn. lia. Qed.

  (* [comment removed for export] *)
  Definition tail_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL PB FB : list cblk) (lo P : Z) (p : pcapT)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte) (hc pkc : cell),
    GIo K R s (CL ++ PB) FB m -> PCAPR_closable P p PB FB m -> hinv R lo spB m -> tp = rc_tp R ->
    ps_outfile s <> Some (pc_rfile p) ->
    rw_cells ssegs m (bv_unsigned spB) [CB 24 j0] ->
    rw_cells ssegs m (bv_unsigned spB + 24) [hc] -> csize hc = 8%nat ->
    rw_cells ssegs m (bv_unsigned spB + 32) [pkc] -> csize pkc = 8%nat ->
    rw_cells ssegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells ssegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells ssegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM ssegs ('(sr, p) <- Pcap.pcap_stats MOps p ;;
                 (if sr =? 0 then with_outfile MOps (prims HO fo_nop sites) (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
                 Pcap.pcap_close MOps (prims HO fo_nop sites) p ;;;
                 s_unlink TMPNAME ;;; mret tt) s
      (at18 K spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x33fec) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140f0) fc None m (seg_rom ssegs)).
  Section Sz14.
  Variables ra spB gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL PB FB lo P p cs3 cs2 cs1 cs0 cra j0 nbuf ej hc pkc : ltac2:(SecDiet.SzSec.tyM 'tail_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma tail_spec__body : ltac2:(SecDiet.SzSec.bodyP 'tail_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using PCLOSE PSTATS UNLINK. all: natfold_lits. pin_using (fun (PCLOSE PSTATS UNLINK : unit) => tt).
    idtac; intros G PC HI TP NOF FR1 FRH HC8 FRP PK8 FR2 NB FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN); unfold FZ, FUZZ_STACK in BU, SPM; unfold rc_spmain in SPM; unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G (PCAPRC_self_in _ _ _ _ _ PC)) as (P1 & _ & _ & P4 & _); pose proof (psize_pos p) as PS.
    unfold implM. iprefix. do 3 lstep.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply implM_leaf.
      eapply (PSTATS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL PB FB lo P p); [spo | exact PC | reflexivity]. }
    intros [sr p'] s2' ms2 [PO L]. unfold pcap_post in PO. all: natfold_lits. destruct PO as (a0v & m2 & PB2 & FB2 & E & MI2 & ST2 & AG2 & G2 & (-> & -> & -> & -> & Esr & PC2)). post_regs E.
    apply (pcap_stats_rfile (H:=H)) in L.
    cbn [fst snd] in Esr, PC2. subst sr.
    keep_frame AG2. clear MI.
    unfold implM. iprefix. lstep. if_true_by (nez_true_neg1). cbv beta iota. cbn [Z.eqb].
    apply evt_done. apply implM_ret_l.
    unfold implM. iprefix. lstep. lstep.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply (PCLOSE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL PB FB lo P p'); [spo | exact PC2 | reflexivity | rewrite L; exact NOF]. }
    intros [] s3' ms3 PO. unfold pcap_post in PO. all: natfold_lits. destruct PO as (a0v & m3 & PB3 & FB3 & E & MI3 & ST3 & AG3 & G3 & (EO3 & -> & _)). post_regs E.
    rewrite app_nil_r in G3. keep_frame AG3. clear MI2.
    unfold implM. iprefix. lstep. apply evt_done.
    destruct (frame_join40 _ _ _ _ _ FR1 FRH HC8 FRP PK8) as [j FR1'].
    eapply (implM_mono ssegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO];
                                  eapply agrees_on_trans; [apply keep_of_callee0; exact AG2| apply keep_of_callee0; exact AG3]].
    eapply unlink18_spec; [> exact UNLINK | exact G3 | exact (hinv_mem _ _ _ _ _ HI ST3 MI3) | exact TP | eexact FR1' | eexact FR2 | exact NB | eexact FR3 | exact FR4 ].
  Qed.
  End Sz14.
  Lemma tail_spec : ltac:(let t := eval cbv delta [tail_spec__stmt] in tail_spec__stmt in exact t).
  Proof using PCLOSE PSTATS UNLINK. all: natfold_lits. intros ra spB gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL PB FB lo P p cs3 cs2 cs1 cs0 cra j0 nbuf ej hc pkc. ltac2:(SecDiet.SzSec.closeP 'tail_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma msg_cstr : forall msg, Forall (fun z => 0 < z < 256) msg -> cstr msg = msg.
  Proof using Type. all: natfold_lits. pin_using tt. induction msg as [|c msg IH]; intros HF; [reflexivity|]. inversion HF; subst. cbn. destruct (Z.eqb_spec c 0); [lia|]. f_equal. apply IH. assumption. Qed.
  Lemma msg_unsigned : forall msg, Forall (fun z => 0 < z < 256) msg -> map bv_unsigned (map b8 msg) = msg.
  Proof using Type. all: natfold_lits. pin_using tt. induction msg as [|c msg IH]; intros HF; [reflexivity|]. inversion HF; subst. cbn [map]. f_equal; [unfold b8; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia | apply IH; assumption]. Qed.
  Lemma msg_nonul : forall msg, Forall (fun z => 0 < z < 256) msg -> ~ In (Z_to_bv 8 0) (map b8 msg).
  Proof using Type. all: natfold_lits. pin_using tt.
    intros msg HF Hin. apply in_map_iff in Hin as (z & E & Hz). apply (proj1 (Forall_forall _ _) HF) in Hz.
    unfold b8 in E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap_small in E by (unfold bv_modulus; cbn; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Definition pcap_part_spec__stmt : Prop := forall (fu : nat) (ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo : Z)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R -> sites = sites_at (bv_unsigned spB) ->
    rw_cells ssegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells ssegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells ssegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells ssegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM ssegs (po <- Pcap.pcap_open_offline MOps (prims HO fo_nop sites) fu TMPNAME ;;
                 match po with
                 | inl errbuf =>
                     with_outfile MOps (prims HO fo_nop sites) (fun out => s_fprintf HO out (pieces_couldnt_open (cstr errbuf))) ;;;
                     s_unlink TMPNAME ;;; mret tt
                 | inr p =>
                     p <- packet_loop MOps (prims HO fo_nop sites) fu fu p ;;
                     '(sr, p) <- Pcap.pcap_stats MOps p ;;
                     (if sr =? 0 then with_outfile MOps (prims HO fo_nop sites) (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
                     Pcap.pcap_close MOps (prims HO fo_nop sites) p ;;;
                     s_unlink TMPNAME ;;; mret tt
                 end) s
      (at18 K spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x33fec) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14090) fc None m (seg_rom ssegs)).
  Section Sz18.
  Variables fu ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo cs3 cs2 cs1 cs0 cra j0 nbuf ej : ltac2:(SecDiet.SzSec.tyM 'pcap_part_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fu).
  Lemma pcap_part_spec__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_part_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FPRINTF_DD FPRINTF_S HAL PCLOSE PNEXT POPEN PSTATS UNLINK. all: natfold_lits. pin_using (fun (FPRINTF_DD FPRINTF_S HAL PCLOSE PNEXT POPEN PSTATS UNLINK : unit) => tt).
    idtac; intros G HI TP SITES FR1 FR2 NB FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN); unfold FZ, FUZZ_STACK in BU, SPM; unfold rc_spmain in SPM; unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW.
    pose proof (name_bytes_slack _ _ _ _ _ _ FR2 NB) as NBY.
    pose proof (rw_cells_bound _ _ _ _ FR2) as NBB. pose proof FR2 as FR2c. destruct FR2c as [[NWF _] _]. cbn in NWF. destruct NWF as [NLEN _].
    pose proof (skipn_length_le 25 nbuf 4071 ltac:(lia)) as SLK.
    unfold implM. iprefix. do 5 lstep.
    rewrite <- tmpname_Z.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply (POPEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (bv_unsigned spB + 40) (bv_unsigned spB + 4136) tmpname (skipn 25 nbuf) ej fu);
        [ spo | rewrite SITES; unfold D_OPEN_OFFLINE; f_equal; (keep_hyps CEILV spB nbuf; lia) | f_equal; lia | cbv beta; f_equal; lia
        | intros E; unfold PCAP_OPEN_OFFLINE_ENTRY, PCAP_OPEN_OFFLINE_WTP_ENTRY in E; (keep_hyps CEILV spB nbuf E; lia)
        | exact NBY | exact tmpname_nonul | rewrite tmpname_len; (keep_hyps CEILV spB nbuf; lia) | exact tmpname_first | exact tmpname_open_r (* [comment removed for export] *)
        | rewrite tmpname_len, length_skipn, NLEN; etransitivity; [apply (neg_mod8_slack (bv_unsigned spB + 40 + 4096)); [Z.div_mod_to_equations; (keep_hyps CEILV spB nbuf r0 q r q0 ALN H0 H1 H5; lia) | (keep_hyps CEILV spB nbuf; lia)] | (keep_hyps CEILV spB nbuf; lia)]
        | (keep_hyps CEILV spB nbuf; lia) | rewrite tmpname_len, length_skipn; unfold rc_spmain; (keep_hyps CEILV spB R nbuf SPM NLEN; lia) | exact FR3 | (keep_hyps CEILV spB nbuf; lia) | unfold rc_spmain; (keep_hyps CEILV spB R nbuf SPM; lia)
        | apply aligned16_8; [exact ALN| reflexivity]
        | left; rewrite tmpname_len, length_skipn; (keep_hyps CEILV spB nbuf NLEN; lia) ]. }
    intros po s2' ms2 PO. unfold open_result_post in PO. all: natfold_lits.
    destruct PO as (a0v & m2 & FB2 & E & EO2 & MI2 & ST2 & AG2 & PO). post_regs E.
    clear FR3. keep_frame AG2. clear MI.
    pose proof (hinv_mem _ _ _ _ _ HI ST2 MI2) as HI2.
    assert (AGK : agrees_on (KEEP CL spB) m m2).
    { eapply agrees_on_weaken; [exact AG2|]. unfold KEEP, client_keeps, FZ. cbv beta. intros a [Ha|Ha]; [split; [left; lia| lia]|].
      pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. split; [right; exact Ha| lia]. }
    destruct po as [msg|p].
    - (* [comment removed for export] *)
      destruct PO as (junk' & -> & -> & G2 & HEB & LENM & RNG).
      unfold implM. iprefix. lstep. if_true.
      apply evt_done. rewrite tmpname_Z. apply with_outfile_l. intros out EO.
      destruct (GIo_outfile_some _ _ _ _ _ _ G2 EO) as (A & AIN & OC).
      pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; exact AIN)) as (A1 & _ & _ & A4 & _); cbn [cb_addr cb_size fst snd] in A1, A4.
      rewrite (msg_cstr _ RNG). rewrite <- (msg_unsigned _ RNG).
      assert (HEBB : bytes_at ssegs m2 (bv_unsigned spB + 4136) (map b8 msg ++ Z_to_bv 8 0 :: junk')).
      { pose proof (rw_cells_bytes_at _ _ _ _ HEB) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r, <- app_assoc in X. exact X. }
      assert (JL : length junk' = (255 - length msg)%nat) by (destruct HEB as [[W _] _]; cbn in W; lia).
      unfold implM. iprefix. do 7 lstep.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply (FPRINTF_S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s2' CL FB out A lo (bv_unsigned spB + 4136) (map b8 msg) junk');
          [ spo | exact AIN | reflexivity | reflexivity | f_equal; lia | exact HEBB | apply msg_nonul; exact RNG
          | rewrite length_map; (keep_hyps CEILV spB nbuf msg junk' LENM; lia)
          | rewrite length_map, JL; etransitivity; [apply (neg_mod8_slack (bv_unsigned spB + 4136 + 256)); [Z.div_mod_to_equations; (keep_hyps CEILV spB nbuf r0 msg junk' q r q0 ALN H0 H1 H5; lia) | (keep_hyps CEILV spB nbuf msg junk' LENM; lia)] | (keep_hyps CEILV spB nbuf msg junk'; lia)]
          | right; rewrite length_map; unfold rc_spmain; (keep_hyps CEILV spB R nbuf msg junk' SPM LENM; lia) ]. }
      intros [] s3' ms3 PO. cbv beta in PO. destruct PO as (a0v & m3 & E & EO3 & MI3 & ST3 & AG3 & G3). post_regs E.
      clear HEBB OC. keep_frame AG3. clear MI2.
      apply rw_cells_forget in HEB as [ej3 FR3]. cbn [cells_size csize] in FR3.
      replace (length msg + 1 + (255 - length msg + 0))%nat with 256%nat in FR3 by lia.
      unfold implM. iprefix. lstep. apply evt_done.
      eapply (implM_mono ssegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO];
                                    eapply agrees_on_trans; [exact AGK| apply keep_of_callee0; exact AG3]].
      eapply unlink18_spec; [> exact UNLINK | exact G3 | exact (hinv_mem _ _ _ _ _ HI ST3 MI3) | exact TP | eexact FR1 | eexact FR2 | exact NB | eexact FR3 | exact FR4 ].
    - (* [comment removed for export] *)
      destruct PO as (P & PB & -> & [FA ->] & G2 & PC2 & [ej2 HEB]).
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G2 (PCAPR_self_in _ _ _ _ _ PC2)) as (P1 & _ & _ & P4 & _); pose proof (psize_pos p) as PS.
      (* [comment removed for export] *)
      assert (NOF0 : ps_outfile s2' <> Some (pc_rfile p)) by (eapply (GIo_new_file_not_out HO K HAL); [exact G | exact G2 | exact EO2]).
      unfold implM. iprefix. lstep. if_false_by (eqz_false P ltac:(lia)). do 4 lstep.
      rewrite tmpname_Z.
      apply (rw_cells_split_CB ssegs _ _ [] _ _ [] [24; 8; 8]%nat) in FR1; [|reflexivity]. cbn [mk_CB_cells app] in FR1.
      apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in FR1 as [FR1 FRH]. cbn [cells_size csize Nat.add] in FRH.
      apply (proj1 (rw_cells_app ssegs _ _ [_] _)) in FRH as [FRH FRP]. cbn [cells_size csize Nat.add] in FRP.
      replace (bv_unsigned spB + Z.of_nat 24 + Z.of_nat 8) with (bv_unsigned spB + 32) in FRP by lia.
      replace (bv_unsigned spB + Z.of_nat 24) with (bv_unsigned spB + 24) in FRH by lia.
      apply evt_done. destruct fu as [|fu'].
      + (* [comment removed for export] *) apply (implM_unr ssegs s2').
      + rewrite packet_loop_S. apply implM_bind_assoc.
        eapply (implM_bind ssegs).
        { eapply implM_leaf.
          eapply (PNEXT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s2' CL PB ((pc_rfile p, FA, FILE_BLOCK) :: FB) lo P (bv_unsigned spB + 24) (bv_unsigned spB + 32) p (S fu') (CB 8 _) (CB 8 _));
            [ spo | exact PC2 | rewrite SITES; unfold D_NEXT_EX; f_equal; (keep_hyps CEILV spB nbuf; lia) | reflexivity | f_equal; lia | f_equal; lia
            | exact FRH | reflexivity | exact FRP | reflexivity
            | (keep_hyps CEILV spB nbuf; lia) | unfold rc_spmain; (keep_hyps CEILV spB R nbuf SPM; lia) | (keep_hyps CEILV spB nbuf; lia) | unfold rc_spmain; (keep_hyps CEILV spB R nbuf SPM; lia) | left; (keep_hyps CEILV spB nbuf; lia)
            | apply aligned16_8; [exact ALN| reflexivity] | apply aligned16_8; [exact ALN| reflexivity] ]. }
        intros [st p'] s3' ms3 [PO L]. cbv beta in PO. destruct PO as (a0v3 & m3 & PB3 & pk3 & E & EO3 & MI3 & ST3 & AG3 & G3 & PC3 & PCC3 & -> & Hst & FRH3 & FRP3 & PKC3). post_regs E.
        apply (pcap_next_ex_rfile HO sites) in L.
        assert (NOF3 : ps_outfile s3' <> Some (pc_rfile p')) by (rewrite EO3, L; exact NOF0).
        clear FRH FRP. keep_frame AG3. clear MI2.
        assert (AGK3 : agrees_on (KEEP CL spB) m m3).
        { eapply agrees_on_trans; [exact AGK|].
          eapply agrees_on_weaken; [exact AG3|]. unfold KEEP, client_keeps, FZ. cbv beta. intros a [Ha|Ha]; [split; [left; lia| lia]|].
          pose proof (GIo_CLc_facts K _ _ _ _ _ _ _ G3 Ha) as [Hc _]. split; [right; exact Ha| lia]. }
        pose proof (hinv_mem _ _ _ _ _ HI ST3 MI3) as HI3.
        unfold PCAP_HDR_OFF in FRH3.
        unfold implM. iprefix. lstep.
        destruct Hst as [-> | Hst].
        * (* [comment removed for export] *)
          change (bv_lts z64 (Z_to_bv 64 1)) with true. cbn [negb Z.ltb]. lstep. lstep.
          apply evt_done. eapply (implM_bind ssegs).
          { eapply iter_spec; [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact G3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (PC3 ltac:((keep_hyps CEILV spB nbuf pk3; lia)))]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact HI3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact TP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SITES]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact NOF3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FRH3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FRP3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact PKC3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact NB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact HEB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR4]) ]. }
          intros p2 s4' ms4 PO. unfold lx_post in PO. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx in PO. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx in PO. destruct_exs PO.
          destruct PO as (-> & G4 & PC4 & HI4 & AG4 & NOF4 & FR1' & FRH4 & FRP4 & PKC4 & FR2' & NB' & FR3' & FR4').
          eapply (implM_mono ssegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO]; eapply agrees_on_trans; [exact AGK3| exact AG4]].
          eapply tail_spec; [> exact G4 | exact PC4 | exact HI4 | exact TP | exact NOF4 | eexact FR1' | eexact FRH4 | reflexivity | eexact FRP4 | exact PKC4 | eexact FR2' | exact NB' | eexact FR3' | exact FR4' ].
        * (* [comment removed for export] *)
          assert (PCC : PCAPR_closable P p' PB3 ((pc_rfile p, FA, FILE_BLOCK) :: FB) m3)
            by (destruct Hst as [-> | ->]; [apply PCAPR_closable_of; apply PC3; lia | apply PCC3; reflexivity]).
          replace (bv_lts z64 (Z_to_bv 64 st)) with false by (destruct Hst as [-> | ->]; reflexivity).
          replace (0 <? st) with false by (destruct Hst as [-> | ->]; reflexivity). cbn [negb].
          apply evt_done. apply implM_ret_l.
          eapply (implM_mono ssegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO]; exact AGK3].
          eapply tail_spec; [> exact G3 | exact PCC | exact HI3 | exact TP | exact NOF3 | eexact FR1 | eexact FRH3 | reflexivity | eexact FRP3 | exact PKC3 | eexact FR2 | exact NB | eexact HEB | exact FR4 ].
  Qed.
  End Sz18.
  Lemma pcap_part_spec : ltac:(let t := eval cbv delta [pcap_part_spec__stmt] in pcap_part_spec__stmt in exact t).
  Proof using FPRINTF_DD FPRINTF_S HAL PCLOSE PNEXT POPEN PSTATS UNLINK. all: natfold_lits. intros fu ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo cs3 cs2 cs1 cs0 cra j0 nbuf ej. ltac2:(SecDiet.SzSec.closeP 'pcap_part_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fuzz.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_B.TwB.
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
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).


  Lemma packet_loop_S : forall f ng (p : pcapT),
    packet_loop MOps (prims HO fo_nop sites) (S f) ng p =
    mo_bind MOps (Pcap.pcap_next_ex MOps (prims HO fo_nop sites) ng p) (fun x => let '(r, p) := x in
      if 0 <? r then
        mo_bind MOps (with_outfile MOps (prims HO fo_nop sites) (fun out => e_fprintf (prims HO fo_nop sites) out (pieces_packet_length (h_caplen (pc_header p)) (h_len (pc_header p)))))
                (fun _ => packet_loop MOps (prims HO fo_nop sites) f ng p)
      else mo_ret MOps p).
  Proof using Type. all: natfold_lits. pin_using tt. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma with_outfile_l : forall {A B} (k : hptr -> M PSt A) (g : A -> M PSt B) (s : PSt) Q ms,
    (forall out, ps_outfile s = Some out -> implM usegs (mbind (k out) g) s Q ms) ->
    implM usegs (mo_bind MOps (with_outfile MOps (prims HO fo_nop sites) k) g) s Q ms.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros A B k g s Q ms HK. unfold implM in *. cbn. destruct (ps_outfile s) as [out|].
    - exact (HK out eq_refl).
    - cbn. apply evt_done. exact I.
  Qed.

  Lemma GIo_outfile_some : forall R (s : PSt) CL FB m q, GIo K R s CL FB m -> ps_outfile s = Some q ->
    exists A, In (q, A, 1264) FB /\ rw_cells usegs m 0x34180 [C8 (Z_to_bv 64 A)].
  Proof using Type. all: natfold_lits. pin_using tt. intros R s CL FB m q G EO. destruct G as (_ & _ & (_ & _ & HA) & _). rewrite EO in HA. exact HA. Qed.
  Lemma GIo_outfile_none : forall R (s : PSt) CL FB m, GIo K R s CL FB m -> ps_outfile s = None ->
    rw_cells usegs m 0x34180 [C8 (Z_to_bv 64 0)].
  Proof using Type. all: natfold_lits. pin_using tt. intros R s CL FB m G EO. destruct G as (_ & _ & (_ & _ & HA) & _). rewrite EO in HA. exact HA. Qed.

  Lemma PCAPR_hdr : forall P (p : pcapT) PB FB m, PCAPR P p PB FB m ->
    rw_cells usegs m (P + 520) (hdr_cells (pc_header p)) /\ 0 <= h_caplen (pc_header p) < 2^32 /\ 0 <= h_len (pc_header p) < 2^32.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros P p PB FB m (Af & Hin & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (pcap_cells_split4 _ _ _ _ (C8 (Z_to_bv 64 Af)) _ _ _ eq_refl CELLS) as (_ & _ & H3 & _).
    pose proof WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc & Hl & _). split; [exact H3|]. split; [exact Hc| exact Hl].
  Qed.

  (* [comment removed for export] *)
  Definition lx_post (spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (cs3 cs2 cs1 cs0 cra : word) (m0 : mem) (P : Z) : pcapT -> PSt -> machine_state -> Prop :=
    fun p' s' ms' => exists ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m' PB' FB' (j0 : list byte) (pkc : cell) (nbuf ej : list byte),
      ms' = MS (mkR ra spB gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x34060) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1417c) fc None m' (seg_rom usegs)
      /\ GIo K R s' (CL ++ PB') FB' m' /\ PCAPR_closable P p' PB' FB' m' /\ hinv R lo spB m' /\ agrees_on (KEEP CL spB) m0 m'
      /\ ps_outfile s' <> Some (pc_rfile p')
      /\ rw_cells usegs m' (bv_unsigned spB) [CB 24 j0]
      /\ rw_cells usegs m' (bv_unsigned spB + 24) [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))]
      /\ rw_cells usegs m' (bv_unsigned spB + 32) [pkc] /\ csize pkc = 8%nat
      /\ rw_cells usegs m' (bv_unsigned spB + 40) [CB 4096 nbuf] /\ firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0]
      /\ rw_cells usegs m' (bv_unsigned spB + 4136) [CB 256 ej]
      /\ rw_cells usegs m' (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra].

  Lemma lx_post_back : forall spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 m1 P r s ms,
    agrees_on (KEEP CL spB) m0 m1 ->
    lx_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m1 P r s ms ->
    lx_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m0 P r s ms.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros until ms. intros AG PO. unfold lx_post in *. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx in PO |- *. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx in PO |- *. destruct_exs PO. destruct PO as (E & G & PC & HI & AG2 & REST).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [exact E|]. split; [exact G|]. split; [exact PC|]. split; [exact HI|]. split; [eapply agrees_on_trans; [exact AG| exact AG2]| exact REST].
  Qed.

  (* [comment removed for export] *)
  Lemma iter_spec : forall (f : nat) (ng : nat) (ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL PB FB : list cblk) (lo P : Z) (p : pcapT)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte) (pkc : cell),
    GIo K R s (CL ++ PB) FB m -> PCAPR P p PB FB m -> hinv R lo spB m -> tp = rc_tp R -> sites = sites_at (bv_unsigned spB) ->
    ps_outfile s <> Some (pc_rfile p) ->
    rw_cells usegs m (bv_unsigned spB) [CB 24 j0] ->
    rw_cells usegs m (bv_unsigned spB + 24) [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))] ->
    rw_cells usegs m (bv_unsigned spB + 32) [pkc] -> csize pkc = 8%nat ->
    rw_cells usegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells usegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells usegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM usegs (mo_bind MOps (with_outfile MOps (prims HO fo_nop sites) (fun out => e_fprintf (prims HO fo_nop sites) out (pieces_packet_length (h_caplen (pc_header p)) (h_len (pc_header p)))))
                         (fun _ => packet_loop MOps (prims HO fo_nop sites) f ng p)) s
      (lx_post spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m P)
      (MS (mkR ra spB gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 FMT_PACKET_LENGTH) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x34060) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14144) fc None m (seg_rom usegs)).
  Proof using FPRINTF_DD PNEXT. all: natfold_lits. pin_using (fun (FPRINTF_DD PNEXT : unit) => tt).
    induction f as [|f IH]; intros until pkc; intros G PC HI TP SITES NOF FR1 FRH FRP PKC FR2 NB FR3 FR4.
    all: pose proof HI as (ST & LO & BU & SPM & MI & ALN); unfold FZ, FUZZ_STACK in BU, SPM; unfold rc_spmain in SPM; unfold rc_lo in LO.
    all: pose proof (bv_unsigned_in_range 64 spB) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    all: pose proof (GIo_spw K _ _ _ _ _ G) as SPW.
    all: pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G (PCAPR_self_in _ _ _ _ _ PC)) as (P1 & P16 & _ & P4 & _); pose proof (psize_pos p) as PS.
    all: pose proof (PCAPR_hdr _ _ _ _ _ PC) as (HDR & HC & HL).
    all: apply with_outfile_l; intros out EO; destruct (GIo_outfile_some _ _ _ _ _ _ G EO) as (A & AIN & OC).
    all: pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact AIN)) as (A1 & _ & _ & A4 & _); cbn [cb_addr cb_size fst snd] in A1, A4.
    all: unfold PCAP_HDR_OFF in *; unfold hdr_cells in HDR.
    all: unfold implM; iprefix; lstep.
    (* [comment removed for export] *)
    all: step; [if_false_by (eqz_false (P + 520) ltac:((keep_hyps CEILV hptr spB P p pkc P1 P4 PS; lia)))]; step; rewrite (and7_aligned (P + 520)) by (fastfirst (first [ noevar_assumption |(keep_hyps CEILV hptr spB P p pkc P1 P4 PS P16; lia) | apply aligned16_8; [exact P16| reflexivity]])); step; [if_false]; do 5 lstep.
    all: apply evt_done; eapply (implM_bind usegs);
      [ eapply (FPRINTF_DD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s (CL ++ PB) FB out A lo (h_caplen (pc_header p)) (h_len (pc_header p)));
        [ spo | exact AIN | reflexivity | reflexivity | reflexivity | reflexivity | exact HC | exact HL ]
      | ].
    all: intros [] s2' ms2 PO; cbv beta in PO; destruct PO as (a0v & m2 & E & EO2 & MI2 & ST2 & AG2 & G2); post_regs E.
    all: assert (PC2 : PCAPR P p PB FB m2) by (eapply (PCAPR_agree _ _ _ _ _ _ _ AG2); [| exact PC]; intros a Ha; right; apply in_block_app; right; exact Ha).
    all: assert (NOF2 : ps_outfile s2' <> Some (pc_rfile p)) by (rewrite EO2; exact NOF).
    all: keep_frame AG2; clear MI OC HDR.
    all: pose proof (hinv_mem _ _ _ _ _ HI ST2 MI2) as HI2.
    - (* [comment removed for export] *)
      apply (implM_unr usegs s2').
    - rewrite packet_loop_S.
      unfold implM. iprefix. do 4 lstep.
      apply evt_done. eapply (implM_bind usegs).
      { eapply implM_leaf.
        eapply (PNEXT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s2' CL PB FB lo P (bv_unsigned spB + 24) (bv_unsigned spB + 32) p ng (C8 (Z_to_bv 64 (P + 520))) pkc);
          [ spo | exact PC2 | rewrite SITES; unfold D_NEXT_EX; f_equal; lia | reflexivity | f_equal; lia | f_equal; lia
          | exact FRH | reflexivity | exact FRP | exact PKC
          | lia | unfold rc_spmain; lia | lia | unfold rc_spmain; lia | left; lia
          | apply aligned16_8; [exact ALN| reflexivity] | apply aligned16_8; [exact ALN| reflexivity] ]. }
      intros [st p'] s3' ms3 [PO L]. cbv beta in PO. destruct PO as (a0v3 & m3 & PB3 & pk3 & E & EO3 & MI3 & ST3 & AG3 & G3 & PC3 & PCC3 & -> & Hst & FRH3 & FRP3 & PKC3). post_regs E.
      apply (pcap_next_ex_rfile HO sites) in L.
      assert (NOF3 : ps_outfile s3' <> Some (pc_rfile p')) by (rewrite EO3, L; exact NOF2).
      clear FRH FRP. keep_frame AG3. clear MI2.
      assert (AGK : agrees_on (KEEP CL spB) m m3).
      { eapply agrees_on_trans.
        - eapply agrees_on_weaken; [exact AG2|]. unfold KEEP, client_keeps, FZ. intros a [Ha|Ha]; [left; lia| right; apply in_block_app; left; exact Ha].
        - eapply agrees_on_weaken; [exact AG3|]. unfold KEEP, client_keeps, FZ. cbv beta. intros a [Ha|Ha]; [split; [left; lia| lia]|].
          pose proof (GIo_CLc_facts K _ _ _ _ _ _ _ G3 Ha) as [Hc _]. split; [right; exact Ha| lia]. }
      unfold PCAP_HDR_OFF in FRH3.
      unfold implM. iprefix. lstep.
      destruct Hst as [-> | Hst].
      + (* [comment removed for export] *)
        change (bv_lts z64 (Z_to_bv 64 1)) with true. cbn [Z.ltb].
        apply evt_done. eapply (implM_mono usegs); [| intros r1 s1' ms1 PO; eapply lx_post_back; [exact AGK| exact PO]].
        eapply IH; [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact G3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (PC3 ltac:((keep_hyps CEILV spB P pkc pk3; lia)))]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (hinv_mem _ _ _ _ _ HI ST3 MI3)]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact TP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SITES]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact NOF3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FRH3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FRP3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact PKC3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact NB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FR4]) ].
      + (* [comment removed for export] *)
        assert (PCC : PCAPR_closable P p' PB3 FB m3) by (destruct Hst as [-> | ->]; [apply PCAPR_closable_of; apply PC3; lia | apply PCC3; reflexivity]).
        replace (bv_lts z64 (Z_to_bv 64 st)) with false by (destruct Hst as [-> | ->]; reflexivity).
        replace (0 <? st) with false by (destruct Hst as [-> | ->]; reflexivity).
        apply evt_done. apply (implM_ret usegs). apply evt_done.
        unfold lx_post. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G3|]. split; [exact PCC|]. split; [exact (hinv_mem _ _ _ _ _ HI ST3 MI3)|]. split; [exact AGK|].
        split; [exact NOF3|].
        split; [eexact FR1|]. split; [exact FRH3|]. split; [exact FRP3|]. split; [exact PKC3|].
        split; [eexact FR2|]. split; [exact NB|]. split; [eexact FR3| eexact FR4].
  Qed.

  Lemma nez_true_neg1 : negb (bv_eqb (Z_to_bv 64 (-1)) z64) = true.
  Proof using Type. all: natfold_lits. pin_using tt. reflexivity. Qed.

  Lemma frame_join40 : forall m A (a : list byte) (h : cell) (k : cell),
    rw_cells usegs m A [CB 24 a] -> rw_cells usegs m (A + 24) [h] -> csize h = 8%nat -> rw_cells usegs m (A + 32) [k] -> csize k = 8%nat ->
    exists j, rw_cells usegs m A [CB 40 j].
  Proof using Type. all: natfold_lits. pin_using tt.
    intros m A a h k H1 H2 Hh H3 Hk.
    assert (X : rw_cells usegs m A ([CB 24 a] ++ [h] ++ [k])).
    { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. replace (A + Z.of_nat 24) with (A + 24) by lia.
      apply rw_cells_app. split; [exact H2|]. cbn [cells_size]. rewrite Hh. replace (A + 24 + Z.of_nat (8 + 0)) with (A + 32) by lia. exact H3. }
    apply rw_cells_forget in X. cbn [cells_size app] in X. rewrite Hh, Hk in X. exact X.
  Qed.

  Lemma PCAPRC_self_in : forall P (p : pcapT) PB FB m, PCAPR_closable P p PB FB m -> In (pc_self p, P, psize p) PB.
  Proof using Type. all: natfold_lits. pin_using tt. intros P p PB FB m (Af & _ & (B & I & j & pad & bs & -> & _)). left. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma name_bytes_slack : forall m A n (buf pre : list byte) k,
    rw_cells usegs m A [CB n buf] -> firstn k buf = pre ++ [Z_to_bv 8 0] -> bytes_at usegs m A (pre ++ Z_to_bv 8 0 :: skipn k buf).
  Proof using Type. all: natfold_lits. pin_using tt.
    intros m A n buf pre k RC E. apply rw_cells_bytes_at in RC. cbn [cells_bytes cbytes] in RC. rewrite app_nil_r in RC.
    rewrite <- (firstn_skipn k buf), E, <- app_assoc in RC. exact RC.
  Qed.
  (* [comment removed for export] *)
  Lemma neg_mod8_slack : forall E T, E mod 8 = 0 -> T <= E -> (- T) mod 8 <= E - T.
  Proof using Type. all: natfold_lits. pin_using tt.
    intros E T HE HT. replace (- T) with ((E - T) + (- (E / 8)) * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z_mod_plus_full. apply Z.mod_le; lia.
  Qed.

  Lemma skipn_length_le : forall {A} k (l : list A) n, (n + k <= length l)%nat -> (n <= length (skipn k l))%nat.
  Proof using Type. all: natfold_lits. pin_using tt. intros A k l n Hl. rewrite length_skipn. lia. Qed.

  (* [comment removed for export] *)
  Definition tail_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL PB FB : list cblk) (lo P : Z) (p : pcapT)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte) (hc pkc : cell),
    GIo K R s (CL ++ PB) FB m -> PCAPR_closable P p PB FB m -> hinv R lo spB m -> tp = rc_tp R ->
    ps_outfile s <> Some (pc_rfile p) ->
    rw_cells usegs m (bv_unsigned spB) [CB 24 j0] ->
    rw_cells usegs m (bv_unsigned spB + 24) [hc] -> csize hc = 8%nat ->
    rw_cells usegs m (bv_unsigned spB + 32) [pkc] -> csize pkc = 8%nat ->
    rw_cells usegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells usegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells usegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM usegs ('(sr, p) <- Pcap.pcap_stats MOps p ;;
                 (if sr =? 0 then with_outfile MOps (prims HO fo_nop sites) (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
                 Pcap.pcap_close MOps (prims HO fo_nop sites) p ;;;
                 s_unlink TMPNAME ;;; mret tt) s
      (at18 K spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x34060) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1417c) fc None m (seg_rom usegs)).
  Section Sz14.
  Variables ra spB gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL PB FB lo P p cs3 cs2 cs1 cs0 cra j0 nbuf ej hc pkc : ltac2:(SecDiet.SzSec.tyM 'tail_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma tail_spec__body : ltac2:(SecDiet.SzSec.bodyP 'tail_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using PCLOSE PSTATS UNLINK. all: natfold_lits. pin_using (fun (PCLOSE PSTATS UNLINK : unit) => tt).
    idtac; intros G PC HI TP NOF FR1 FRH HC8 FRP PK8 FR2 NB FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN); unfold FZ, FUZZ_STACK in BU, SPM; unfold rc_spmain in SPM; unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G (PCAPRC_self_in _ _ _ _ _ PC)) as (P1 & _ & _ & P4 & _); pose proof (psize_pos p) as PS.
    unfold implM. iprefix. do 3 lstep.
    apply evt_done. eapply (implM_bind usegs).
    { eapply implM_leaf.
      eapply (PSTATS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL PB FB lo P p); [spo | exact PC | reflexivity]. }
    intros [sr p'] s2' ms2 [PO L]. unfold pcap_post in PO. all: natfold_lits. destruct PO as (a0v & m2 & PB2 & FB2 & E & MI2 & ST2 & AG2 & G2 & (-> & -> & -> & -> & Esr & PC2)). post_regs E.
    apply (pcap_stats_rfile (H:=H)) in L.
    cbn [fst snd] in Esr, PC2. subst sr.
    keep_frame AG2. clear MI.
    unfold implM. iprefix. lstep. if_true_by (nez_true_neg1). cbv beta iota. cbn [Z.eqb].
    apply evt_done. apply implM_ret_l.
    unfold implM. iprefix. lstep. lstep.
    apply evt_done. eapply (implM_bind usegs).
    { eapply (PCLOSE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL PB FB lo P p'); [spo | exact PC2 | reflexivity | rewrite L; exact NOF]. }
    intros [] s3' ms3 PO. unfold pcap_post in PO. all: natfold_lits. destruct PO as (a0v & m3 & PB3 & FB3 & E & MI3 & ST3 & AG3 & G3 & (EO3 & -> & _)). post_regs E.
    rewrite app_nil_r in G3. keep_frame AG3. clear MI2.
    unfold implM. iprefix. lstep. apply evt_done.
    destruct (frame_join40 _ _ _ _ _ FR1 FRH HC8 FRP PK8) as [j FR1'].
    eapply (implM_mono usegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO];
                                  eapply agrees_on_trans; [apply keep_of_callee0; exact AG2| apply keep_of_callee0; exact AG3]].
    eapply unlink18_spec; [> exact UNLINK | exact G3 | exact (hinv_mem _ _ _ _ _ HI ST3 MI3) | exact TP | eexact FR1' | eexact FR2 | exact NB | eexact FR3 | exact FR4 ].
  Qed.
  End Sz14.
  Lemma tail_spec : ltac:(let t := eval cbv delta [tail_spec__stmt] in tail_spec__stmt in exact t).
  Proof using PCLOSE PSTATS UNLINK. all: natfold_lits. intros ra spB gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL PB FB lo P p cs3 cs2 cs1 cs0 cra j0 nbuf ej hc pkc. ltac2:(SecDiet.SzSec.closeP 'tail_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma msg_cstr : forall msg, Forall (fun z => 0 < z < 256) msg -> cstr msg = msg.
  Proof using Type. all: natfold_lits. pin_using tt. induction msg as [|c msg IH]; intros HF; [reflexivity|]. inversion HF; subst. cbn. destruct (Z.eqb_spec c 0); [lia|]. f_equal. apply IH. assumption. Qed.
  Lemma msg_unsigned : forall msg, Forall (fun z => 0 < z < 256) msg -> map bv_unsigned (map b8 msg) = msg.
  Proof using Type. all: natfold_lits. pin_using tt. induction msg as [|c msg IH]; intros HF; [reflexivity|]. inversion HF; subst. cbn [map]. f_equal; [unfold b8; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia | apply IH; assumption]. Qed.
  Lemma msg_nonul : forall msg, Forall (fun z => 0 < z < 256) msg -> ~ In (Z_to_bv 8 0) (map b8 msg).
  Proof using Type. all: natfold_lits. pin_using tt.
    intros msg HF Hin. apply in_map_iff in Hin as (z & E & Hz). apply (proj1 (Forall_forall _ _) HF) in Hz.
    unfold b8 in E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap_small in E by (unfold bv_modulus; cbn; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Definition pcap_part_spec__stmt : Prop := forall (fu : nat) (ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo : Z)
      (cs3 cs2 cs1 cs0 cra : word) (j0 nbuf ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R -> sites = sites_at (bv_unsigned spB) ->
    rw_cells usegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells usegs m (bv_unsigned spB + 40) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells usegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells usegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM usegs (po <- Pcap.pcap_open_offline MOps (prims HO fo_nop sites) fu TMPNAME ;;
                 match po with
                 | inl errbuf =>
                     with_outfile MOps (prims HO fo_nop sites) (fun out => s_fprintf HO out (pieces_couldnt_open (cstr errbuf))) ;;;
                     s_unlink TMPNAME ;;; mret tt
                 | inr p =>
                     p <- packet_loop MOps (prims HO fo_nop sites) fu fu p ;;
                     '(sr, p) <- Pcap.pcap_stats MOps p ;;
                     (if sr =? 0 then with_outfile MOps (prims HO fo_nop sites) (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
                     Pcap.pcap_close MOps (prims HO fo_nop sites) p ;;;
                     s_unlink TMPNAME ;;; mret tt
                 end) s
      (at18 K spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x34060) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14110) fc None m (seg_rom usegs)).
  Section Sz18.
  Variables fu ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo cs3 cs2 cs1 cs0 cra j0 nbuf ej : ltac2:(SecDiet.SzSec.tyM 'pcap_part_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fu).
  Lemma pcap_part_spec__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_part_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FPRINTF_DD FPRINTF_S HAL PCLOSE PNEXT POPEN PSTATS UNLINK. all: natfold_lits. pin_using (fun (FPRINTF_DD FPRINTF_S HAL PCLOSE PNEXT POPEN PSTATS UNLINK : unit) => tt).
    idtac; intros G HI TP SITES FR1 FR2 NB FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN); unfold FZ, FUZZ_STACK in BU, SPM; unfold rc_spmain in SPM; unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW.
    pose proof (name_bytes_slack _ _ _ _ _ _ FR2 NB) as NBY.
    pose proof (rw_cells_bound _ _ _ _ FR2) as NBB. pose proof FR2 as FR2c. destruct FR2c as [[NWF _] _]. cbn in NWF. destruct NWF as [NLEN _].
    pose proof (skipn_length_le 25 nbuf 4071 ltac:(lia)) as SLK.
    unfold implM. iprefix. do 5 lstep.
    rewrite <- tmpname_Z.
    apply evt_done. eapply (implM_bind usegs).
    { eapply (POPEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (bv_unsigned spB + 40) (bv_unsigned spB + 4136) tmpname (skipn 25 nbuf) ej fu);
        [ spo | rewrite SITES; unfold D_OPEN_OFFLINE; f_equal; (keep_hyps CEILV spB nbuf; lia) | f_equal; lia | cbv beta; f_equal; lia
        | intros E; unfold PCAP_OPEN_OFFLINE_ENTRY, PCAP_OPEN_OFFLINE_WTP_ENTRY in E; (keep_hyps CEILV spB nbuf E; lia)
        | exact NBY | exact tmpname_nonul | rewrite tmpname_len; (keep_hyps CEILV spB nbuf; lia) | exact tmpname_first | exact tmpname_open_r (* [comment removed for export] *)
        | rewrite tmpname_len, length_skipn, NLEN; etransitivity; [apply (neg_mod8_slack (bv_unsigned spB + 40 + 4096)); [Z.div_mod_to_equations; (keep_hyps CEILV spB nbuf r0 q r q0 ALN H0 H1 H5; lia) | (keep_hyps CEILV spB nbuf; lia)] | (keep_hyps CEILV spB nbuf; lia)]
        | (keep_hyps CEILV spB nbuf; lia) | rewrite tmpname_len, length_skipn; unfold rc_spmain; (keep_hyps CEILV spB R nbuf SPM NLEN; lia) | exact FR3 | (keep_hyps CEILV spB nbuf; lia) | unfold rc_spmain; (keep_hyps CEILV spB R nbuf SPM; lia)
        | apply aligned16_8; [exact ALN| reflexivity]
        | left; rewrite tmpname_len, length_skipn; (keep_hyps CEILV spB nbuf NLEN; lia) ]. }
    intros po s2' ms2 PO. unfold open_result_post in PO. all: natfold_lits.
    destruct PO as (a0v & m2 & FB2 & E & EO2 & MI2 & ST2 & AG2 & PO). post_regs E.
    clear FR3. keep_frame AG2. clear MI.
    pose proof (hinv_mem _ _ _ _ _ HI ST2 MI2) as HI2.
    assert (AGK : agrees_on (KEEP CL spB) m m2).
    { eapply agrees_on_weaken; [exact AG2|]. unfold KEEP, client_keeps, FZ. cbv beta. intros a [Ha|Ha]; [split; [left; lia| lia]|].
      pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. split; [right; exact Ha| lia]. }
    destruct po as [msg|p].
    - (* [comment removed for export] *)
      destruct PO as (junk' & -> & -> & G2 & HEB & LENM & RNG).
      unfold implM. iprefix. lstep. if_true.
      apply evt_done. rewrite tmpname_Z. apply with_outfile_l. intros out EO.
      destruct (GIo_outfile_some _ _ _ _ _ _ G2 EO) as (A & AIN & OC).
      pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; exact AIN)) as (A1 & _ & _ & A4 & _); cbn [cb_addr cb_size fst snd] in A1, A4.
      rewrite (msg_cstr _ RNG). rewrite <- (msg_unsigned _ RNG).
      assert (HEBB : bytes_at usegs m2 (bv_unsigned spB + 4136) (map b8 msg ++ Z_to_bv 8 0 :: junk')).
      { pose proof (rw_cells_bytes_at _ _ _ _ HEB) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r, <- app_assoc in X. exact X. }
      assert (JL : length junk' = (255 - length msg)%nat) by (destruct HEB as [[W _] _]; cbn in W; lia).
      unfold implM. iprefix. do 7 lstep.
      apply evt_done. eapply (implM_bind usegs).
      { eapply (FPRINTF_S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s2' CL FB out A lo (bv_unsigned spB + 4136) (map b8 msg) junk');
          [ spo | exact AIN | reflexivity | reflexivity | f_equal; lia | exact HEBB | apply msg_nonul; exact RNG
          | rewrite length_map; (keep_hyps CEILV spB nbuf msg junk' LENM; lia)
          | rewrite length_map, JL; etransitivity; [apply (neg_mod8_slack (bv_unsigned spB + 4136 + 256)); [Z.div_mod_to_equations; (keep_hyps CEILV spB nbuf r0 msg junk' q r q0 ALN H0 H1 H5; lia) | (keep_hyps CEILV spB nbuf msg junk' LENM; lia)] | (keep_hyps CEILV spB nbuf msg junk'; lia)]
          | right; rewrite length_map; unfold rc_spmain; (keep_hyps CEILV spB R nbuf msg junk' SPM LENM; lia) ]. }
      intros [] s3' ms3 PO. cbv beta in PO. destruct PO as (a0v & m3 & E & EO3 & MI3 & ST3 & AG3 & G3). post_regs E.
      clear HEBB OC. keep_frame AG3. clear MI2.
      apply rw_cells_forget in HEB as [ej3 FR3]. cbn [cells_size csize] in FR3.
      replace (length msg + 1 + (255 - length msg + 0))%nat with 256%nat in FR3 by lia.
      unfold implM. iprefix. lstep. apply evt_done.
      eapply (implM_mono usegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO];
                                    eapply agrees_on_trans; [exact AGK| apply keep_of_callee0; exact AG3]].
      eapply unlink18_spec; [> exact UNLINK | exact G3 | exact (hinv_mem _ _ _ _ _ HI ST3 MI3) | exact TP | eexact FR1 | eexact FR2 | exact NB | eexact FR3 | exact FR4 ].
    - (* [comment removed for export] *)
      destruct PO as (P & PB & -> & [FA ->] & G2 & PC2 & [ej2 HEB]).
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G2 (PCAPR_self_in _ _ _ _ _ PC2)) as (P1 & _ & _ & P4 & _); pose proof (psize_pos p) as PS.
      (* [comment removed for export] *)
      assert (NOF0 : ps_outfile s2' <> Some (pc_rfile p)) by (eapply (GIo_new_file_not_out HO K HAL); [exact G | exact G2 | exact EO2]).
      unfold implM. iprefix. lstep. if_false_by (eqz_false P ltac:(lia)). do 4 lstep.
      rewrite tmpname_Z.
      apply (rw_cells_split_CB usegs _ _ [] _ _ [] [24; 8; 8]%nat) in FR1; [|reflexivity]. cbn [mk_CB_cells app] in FR1.
      apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR1 as [FR1 FRH]. cbn [cells_size csize Nat.add] in FRH.
      apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FRH as [FRH FRP]. cbn [cells_size csize Nat.add] in FRP.
      replace (bv_unsigned spB + Z.of_nat 24 + Z.of_nat 8) with (bv_unsigned spB + 32) in FRP by lia.
      replace (bv_unsigned spB + Z.of_nat 24) with (bv_unsigned spB + 24) in FRH by lia.
      apply evt_done. destruct fu as [|fu'].
      + (* [comment removed for export] *) apply (implM_unr usegs s2').
      + rewrite packet_loop_S. apply implM_bind_assoc.
        eapply (implM_bind usegs).
        { eapply implM_leaf.
          eapply (PNEXT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s2' CL PB ((pc_rfile p, FA, FILE_BLOCK) :: FB) lo P (bv_unsigned spB + 24) (bv_unsigned spB + 32) p (S fu') (CB 8 _) (CB 8 _));
            [ spo | exact PC2 | rewrite SITES; unfold D_NEXT_EX; f_equal; (keep_hyps CEILV spB nbuf; lia) | reflexivity | f_equal; lia | f_equal; lia
            | exact FRH | reflexivity | exact FRP | reflexivity
            | (keep_hyps CEILV spB nbuf; lia) | unfold rc_spmain; (keep_hyps CEILV spB R nbuf SPM; lia) | (keep_hyps CEILV spB nbuf; lia) | unfold rc_spmain; (keep_hyps CEILV spB R nbuf SPM; lia) | left; (keep_hyps CEILV spB nbuf; lia)
            | apply aligned16_8; [exact ALN| reflexivity] | apply aligned16_8; [exact ALN| reflexivity] ]. }
        intros [st p'] s3' ms3 [PO L]. cbv beta in PO. destruct PO as (a0v3 & m3 & PB3 & pk3 & E & EO3 & MI3 & ST3 & AG3 & G3 & PC3 & PCC3 & -> & Hst & FRH3 & FRP3 & PKC3). post_regs E.
        apply (pcap_next_ex_rfile HO sites) in L.
        assert (NOF3 : ps_outfile s3' <> Some (pc_rfile p')) by (rewrite EO3, L; exact NOF0).
        clear FRH FRP. keep_frame AG3. clear MI2.
        assert (AGK3 : agrees_on (KEEP CL spB) m m3).
        { eapply agrees_on_trans; [exact AGK|].
          eapply agrees_on_weaken; [exact AG3|]. unfold KEEP, client_keeps, FZ. cbv beta. intros a [Ha|Ha]; [split; [left; lia| lia]|].
          pose proof (GIo_CLc_facts K _ _ _ _ _ _ _ G3 Ha) as [Hc _]. split; [right; exact Ha| lia]. }
        pose proof (hinv_mem _ _ _ _ _ HI ST3 MI3) as HI3.
        unfold PCAP_HDR_OFF in FRH3.
        unfold implM. iprefix. lstep.
        destruct Hst as [-> | Hst].
        * (* [comment removed for export] *)
          change (bv_lts z64 (Z_to_bv 64 1)) with true. cbn [negb Z.ltb]. lstep. lstep.
          apply evt_done. eapply (implM_bind usegs).
          { eapply iter_spec; [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact G3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact (PC3 ltac:((keep_hyps CEILV spB nbuf pk3; lia)))]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact HI3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact TP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SITES]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact NOF3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FRH3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FRP3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact PKC3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact NB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact HEB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eexact FR4]) ]. }
          intros p2 s4' ms4 PO. unfold lx_post in PO. all: natfold_lits. let sblx := fresh "sbl" in pose (sblx := (Z.to_nat 4096)); change (Z.to_nat 4096) with sblx in PO. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx in PO. destruct_exs PO.
          destruct PO as (-> & G4 & PC4 & HI4 & AG4 & NOF4 & FR1' & FRH4 & FRP4 & PKC4 & FR2' & NB' & FR3' & FR4').
          eapply (implM_mono usegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO]; eapply agrees_on_trans; [exact AGK3| exact AG4]].
          eapply tail_spec; [> exact G4 | exact PC4 | exact HI4 | exact TP | exact NOF4 | eexact FR1' | eexact FRH4 | reflexivity | eexact FRP4 | exact PKC4 | eexact FR2' | exact NB' | eexact FR3' | exact FR4' ].
        * (* [comment removed for export] *)
          assert (PCC : PCAPR_closable P p' PB3 ((pc_rfile p, FA, FILE_BLOCK) :: FB) m3)
            by (destruct Hst as [-> | ->]; [apply PCAPR_closable_of; apply PC3; lia | apply PCC3; reflexivity]).
          replace (bv_lts z64 (Z_to_bv 64 st)) with false by (destruct Hst as [-> | ->]; reflexivity).
          replace (0 <? st) with false by (destruct Hst as [-> | ->]; reflexivity). cbn [negb].
          apply evt_done. apply implM_ret_l.
          eapply (implM_mono usegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO]; exact AGK3].
          eapply tail_spec; [> exact G3 | exact PCC | exact HI3 | exact TP | exact NOF3 | eexact FR1 | eexact FRH3 | reflexivity | eexact FRP3 | exact PKC3 | eexact FR2 | exact NB | eexact HEB | exact FR4 ].
  Qed.
  End Sz18.
  Lemma pcap_part_spec : ltac:(let t := eval cbv delta [pcap_part_spec__stmt] in pcap_part_spec__stmt in exact t).
  Proof using FPRINTF_DD FPRINTF_S HAL PCLOSE PNEXT POPEN PSTATS UNLINK. all: natfold_lits. intros fu ra spB gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo cs3 cs2 cs1 cs0 cra j0 nbuf ej. ltac2:(SecDiet.SzSec.closeP 'pcap_part_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fuzz.

End WithCeil.
End TwB.
End F_fuzz_C.

(* [comment removed for export] *)
Module F_fuzz_D.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep RegsEquiv MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_C.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma usp0_range : forall R, 0 <= usp0 R < 2^64.
Proof using Type. pin_using tt. intros R. unfold usp0. pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as X. unfold bv_modulus in X. cbn in X. cbn. lia. Qed.

Definition tmplb : list byte := map b8 TEMPLATE.
Lemma tmplb_Z : map bv_unsigned tmplb = TEMPLATE.
Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
Lemma tmplb_nonul : ~ In (Z_to_bv 8 0) tmplb.
Proof using Type. pin_using tt. unfold tmplb, TEMPLATE. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
Lemma template_eq : template = tmplb ++ [Z_to_bv 8 0].
Proof using Type. pin_using tt. reflexivity. Qed.
Lemma template_len : length template = 30%nat.
Proof using Type. pin_using tt. reflexivity. Qed.

Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

  (* [comment removed for export] *)
  Definition body_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo D : Z) (data : list byte)
      (cs3 cs2 cs1 cs0 cra : word) (j0 j1 ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R -> sites = sites_at (bv_unsigned spB) ->
    bytes_at ssegs m D data -> (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a) -> Z.of_nat (length data) < 2^26 ->
    rw_cells ssegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells ssegs m (bv_unsigned spB + 40) [CB 30 j1] ->
    rw_cells ssegs m (bv_unsigned spB + 70) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
    rw_cells ssegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells ssegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM ssegs (fuzz_body HO sites (map bv_unsigned data)) s
      (at18 K spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x33fec) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14014) fc None m (seg_rom ssegs)).
  Section Sz6.
  Variables ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 j1 ej : ltac2:(SecDiet.SzSec.tyM 'body_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma body_spec__body : ltac2:(SecDiet.SzSec.bodyP 'body_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. pin_using (fun (CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK : unit) => tt).
    idtac; intros G HI TP SITES DAT DIN DLEN FR1 FRT FRZ FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN); unfold FZ, FUZZ_STACK in BU, SPM; unfold rc_spmain in SPM; unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (usp0_range R) as RSP0.
    pose proof (bytes_at_bound _ _ _ _ DAT) as DB.
    pose proof (rodata_template m MI) as TMP.
    pose proof (munch_refl [(bv_unsigned spB + 40, bv_unsigned spB + 70)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold fuzz_body.
    unfold implM. iprefix. do 5 lstep.
    hide DAT.
    call (memcpy_specZ (bv_unsigned spB + 40) STR_TEMPLATE 30);
      [ fastfirst (first [ noevar_assumption |exact TMP | exact template_len | exact FRT | exact MI | reflexivity | unfold STR_TEMPLATE; lia | lia]) .. | ].
    unhide DAT.
    lazymatch type of MU with munch _ _ ?m1 => assert (DAT1 : bytes_at ssegs m1 D data) end.
    { eapply agrees_bytes_at; [eapply (agrees_on_of_munch (fun a => in_block CL a)); [exact MU | exact WM |] | exact DAT | exact DIN].
      intros a _ Ha. pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. cbn. lia. }
    clear DAT. rename PC into FRT. change (Z.to_nat 30) with 30%nat in FRT. clear POST.
    pose proof (hinv_mem _ _ _ _ _ HI ST MI0) as HI1.
    lazymatch type of MU with munch _ _ ?m1 =>
      assert (NBUF : rw_cells ssegs m1 (bv_unsigned spB + 40) [CB 4096 (template ++ repeat (Z_to_bv 8 0) 4066)]);
      [ pose proof (rw_cells_merge ssegs m1 (bv_unsigned spB + 40) [] [CB 30 template; CB 4066 (repeat (Z_to_bv 8 0) 4066)] []) as X |] end.
    { (sl_lit_sizes_in X; cbn [app cells_size csize cells_bytes cbytes Nat.add] in X). rewrite app_nil_r in X. apply X.
      apply (proj2 (rw_cells_app ssegs _ _ [_] _)). split; [exact FRT|]. (sl_lit_sizes; cbn [cells_size csize Nat.add]).
      replace (bv_unsigned spB + 40 + Z.of_nat 30) with (bv_unsigned spB + 70) by lia. exact FRZ. }
    clear FRT FRZ.
    lazymatch type of MU with munch _ _ ?m1 => assert (AGK1 : agrees_on (KEEP CL spB) m m1) end.
    { eapply agrees_on_of_munch; [exact MU | exact WM |]. unfold KEEP, client_keeps, FZ. intros a _ [Ha|Ha]; cbn; [lia|].
      pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. lia. }
    lazymatch type of MU with munch _ _ ?m1 => assert (G1 : GIo K R s CL FB m1) end.
    { eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain. lia. }
    clear MU WM.
    lstep. lstep.
    rewrite <- tmplb_Z.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply implM_leaf.
      eapply (MKSTEMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (bv_unsigned spB + 40) 4096%nat tmplb (template ++ repeat (Z_to_bv 8 0) 4066));
        [ spo | f_equal; lia | exact NBUF | vm_compute; reflexivity | exact tmplb_nonul | reflexivity | cbn; lia | lia | right; unfold rc_spmain; lia ]. }
    intros [fn fd] sx2 ms2 [PO L]. cbv beta in PO. cbn [fst snd] in PO.
    let sx := fresh "sbl" in let sy := fresh "sbl" in pose (sx := 4096%nat); change 4096%nat with sx in PO; pose (sy := 4066%nat); change 4066%nat with sy in PO;
      destruct PO as (a0v & m2 & buf' & E & EO2 & MI2 & ST2 & AG2 & G2 & -> & Hfd & NBUF2 & NB2 & RNGf & LENf & SHAPE); subst sx sy. post_regs E.
    rewrite tmplb_Z in L. apply mkstemp_leaf in L. subst fn.
    replace (length TMPNAME + 1)%nat with 25%nat in NB2 by reflexivity. change (map b8 TMPNAME) with tmpname in NB2.
    clear NBUF. keep_frame AG2. clear MI0.
    pose proof (hinv_mem _ _ _ _ _ HI ST2 MI2) as HI2.
    assert (AGK2 : agrees_on (KEEP CL spB) m m2).
    { eapply agrees_on_trans; [exact AGK1|].
      eapply agrees_on_weaken; [exact AG2|]. unfold KEEP, client_keeps, FZ. cbv beta. intros a [Ha|Ha]; [split; [left; lia| lia]|].
      pose proof (GIo_CLc_facts K R sx2 CL [] FB m2 a ltac:(rewrite app_nil_r; exact G2) Ha) as [Hc _]. split; [right; exact Ha| lia]. }
    cbv beta iota.
    assert (DAT2 : bytes_at ssegs m2 D data).
    { eapply agrees_bytes_at; [exact AG2 | exact DAT1 |]. intros a Ha. cbv beta.
      pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) (DIN a Ha)) as [Hc _]. split; [right; apply DIN; exact Ha| lia]. }
    clear DAT1.
    unfold implM. iprefix. lstep.
    destruct Hfd as [Efd|Hpos].
    - (* [comment removed for export] *)
      rewrite Efd. change (bv_lts (Z_to_bv 64 (-1)) z64) with true. cbn [Z.ltb].
      apply evt_done. apply (implM_ret ssegs). apply evt_done.
      destruct (frame_forget3 _ _ _ _ _ FR1 NBUF2 FR3) as [j FRL].
      unfold at18. let sblx := fresh "sbl" in pose (sblx := 4392%nat); change 4392%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact G2|]. split; [exact HI2|]. split; [exact AGK2|]. split; [exact FRL| exact FR4].
    - (* [comment removed for export] *)
      rewrite bv_lts_zero_r, unsigned_lit by lia. replace (2 ^ 63 <=? fd) with false by (symmetry; apply Z.leb_gt; lia).
      replace (fd <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      lstep. apply evt_done. eapply (implM_bind ssegs).
      { eapply (CLOSE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R sx2 CL FB lo fd); [spo | reflexivity | lia]. }
      intros rclose sx3 ms3 PO. cbv beta in PO. destruct PO as (a0v & m3 & E & EO3 & MI3 & ST3 & AG3 & G3). post_regs E.
      keep_frame AG3. clear MI2.
      assert (DAT3 : bytes_at ssegs m3 D data) by (eapply agrees_bytes_at; [exact AG3 | exact DAT2 | intros a Ha; right; apply DIN; exact Ha]).
      pose proof (hinv_mem _ _ _ _ _ HI ST3 MI3) as HI3.
      assert (AGK3 : agrees_on (KEEP CL spB) m m3) by (eapply agrees_on_trans; [exact AGK2| apply keep_of_callee0; exact AG3]).
      eapply (implM_bind ssegs).
      { eapply btf_spec; first [exact G3 | exact HI3 | exact TP | reflexivity | exact DAT3 | exact DIN | exact DLEN | exact NB2 | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption]. }
      intros r sx4 ms4 PO. unfold btf_post in PO. let sblx := fresh "sbl" in pose (sblx := 4096%nat); change 4096%nat with sblx in PO. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx in PO. destruct_exs PO.
      destruct PO as (-> & G4 & HI4 & AG4 & FR1' & FR2' & NB' & FR3' & FR4' & Hr).
      destruct Hr as [Hr | ->].
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.ltb_lt r 0) Hr).
        eapply (implM_mono ssegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO]; eapply agrees_on_trans; [exact AGK3| exact AG4]].
        eapply unlink18_spec; first [exact UNLINK | exact G4 | exact HI4 | exact TP | exact NB' | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
      + cbn [Z.ltb].
        eapply (implM_mono ssegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO]; eapply agrees_on_trans; [exact AGK3| exact AG4]].
        eapply pcap_part_spec; first [exact G4 | exact HI4 | exact TP | exact SITES | exact NB' | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
  Qed.
  End Sz6.
  Lemma body_spec : ltac:(let t := eval cbv delta [body_spec__stmt] in body_spec__stmt in exact t).
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. intros ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 j1 ej. ltac2:(SecDiet.SzSec.closeP 'body_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End Fuzz.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_C.TwB.
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
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma usp0_range : forall R, 0 <= usp0 R < 2^64.
Proof using Type. pin_using tt. intros R. unfold usp0. pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as X. unfold bv_modulus in X. cbn in X. cbn. lia. Qed.

Definition tmplb : list byte := map b8 TEMPLATE.
Lemma tmplb_Z : map bv_unsigned tmplb = TEMPLATE.
Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
Lemma tmplb_nonul : ~ In (Z_to_bv 8 0) tmplb.
Proof using Type. pin_using tt. unfold tmplb, TEMPLATE. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
Lemma template_eq : template = tmplb ++ [Z_to_bv 8 0].
Proof using Type. pin_using tt. reflexivity. Qed.
Lemma template_len : length template = 30%nat.
Proof using Type. pin_using tt. reflexivity. Qed.

Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

  (* [comment removed for export] *)
  Definition body_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo D : Z) (data : list byte)
      (cs3 cs2 cs1 cs0 cra : word) (j0 j1 ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R -> sites = sites_at (bv_unsigned spB) ->
    bytes_at usegs m D data -> (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a) -> Z.of_nat (length data) < 2^26 ->
    rw_cells usegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells usegs m (bv_unsigned spB + 40) [CB 30 j1] ->
    rw_cells usegs m (bv_unsigned spB + 70) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
    rw_cells usegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells usegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM usegs (fuzz_body HO sites (map bv_unsigned data)) s
      (at18 K spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x34060) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14088) fc None m (seg_rom usegs)).
  Section Sz6.
  Variables ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 j1 ej : ltac2:(SecDiet.SzSec.tyM 'body_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma body_spec__body : ltac2:(SecDiet.SzSec.bodyP 'body_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. pin_using (fun (CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK : unit) => tt).
    idtac; intros G HI TP SITES DAT DIN DLEN FR1 FRT FRZ FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN); unfold FZ, FUZZ_STACK in BU, SPM; unfold rc_spmain in SPM; unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (usp0_range R) as RSP0.
    pose proof (bytes_at_bound _ _ _ _ DAT) as DB.
    pose proof (rodata_template m MI) as TMP.
    pose proof (munch_refl [(bv_unsigned spB + 40, bv_unsigned spB + 70)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold fuzz_body.
    unfold implM. iprefix. do 5 lstep.
    hide DAT.
    call (memcpy_specZ (bv_unsigned spB + 40) STR_TEMPLATE 30);
      [ fastfirst (first [ noevar_assumption |exact TMP | exact template_len | exact FRT | exact MI | reflexivity | unfold STR_TEMPLATE; lia | lia]) .. | ].
    unhide DAT.
    lazymatch type of MU with munch _ _ ?m1 => assert (DAT1 : bytes_at usegs m1 D data) end.
    { eapply agrees_bytes_at; [eapply (agrees_on_of_munch (fun a => in_block CL a)); [exact MU | exact WM |] | exact DAT | exact DIN].
      intros a _ Ha. pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. cbn. lia. }
    clear DAT. rename PC into FRT. change (Z.to_nat 30) with 30%nat in FRT. clear POST.
    pose proof (hinv_mem _ _ _ _ _ HI ST MI0) as HI1.
    lazymatch type of MU with munch _ _ ?m1 =>
      assert (NBUF : rw_cells usegs m1 (bv_unsigned spB + 40) [CB 4096 (template ++ repeat (Z_to_bv 8 0) 4066)]);
      [ pose proof (rw_cells_merge usegs m1 (bv_unsigned spB + 40) [] [CB 30 template; CB 4066 (repeat (Z_to_bv 8 0) 4066)] []) as X |] end.
    { (sl_lit_sizes_in X; cbn [app cells_size csize cells_bytes cbytes Nat.add] in X). rewrite app_nil_r in X. apply X.
      apply (proj2 (rw_cells_app usegs _ _ [_] _)). split; [exact FRT|]. (sl_lit_sizes; cbn [cells_size csize Nat.add]).
      replace (bv_unsigned spB + 40 + Z.of_nat 30) with (bv_unsigned spB + 70) by lia. exact FRZ. }
    clear FRT FRZ.
    lazymatch type of MU with munch _ _ ?m1 => assert (AGK1 : agrees_on (KEEP CL spB) m m1) end.
    { eapply agrees_on_of_munch; [exact MU | exact WM |]. unfold KEEP, client_keeps, FZ. intros a _ [Ha|Ha]; cbn; [lia|].
      pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. lia. }
    lazymatch type of MU with munch _ _ ?m1 => assert (G1 : GIo K R s CL FB m1) end.
    { eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain. lia. }
    clear MU WM.
    lstep. lstep.
    rewrite <- tmplb_Z.
    apply evt_done. eapply (implM_bind usegs).
    { eapply implM_leaf.
      eapply (MKSTEMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (bv_unsigned spB + 40) 4096%nat tmplb (template ++ repeat (Z_to_bv 8 0) 4066));
        [ spo | f_equal; lia | exact NBUF | vm_compute; reflexivity | exact tmplb_nonul | reflexivity | cbn; lia | lia | right; unfold rc_spmain; lia ]. }
    intros [fn fd] sx2 ms2 [PO L]. cbv beta in PO. cbn [fst snd] in PO.
    let sx := fresh "sbl" in let sy := fresh "sbl" in pose (sx := 4096%nat); change 4096%nat with sx in PO; pose (sy := 4066%nat); change 4066%nat with sy in PO;
      destruct PO as (a0v & m2 & buf' & E & EO2 & MI2 & ST2 & AG2 & G2 & -> & Hfd & NBUF2 & NB2 & RNGf & LENf & SHAPE); subst sx sy. post_regs E.
    rewrite tmplb_Z in L. apply mkstemp_leaf in L. subst fn.
    replace (length TMPNAME + 1)%nat with 25%nat in NB2 by reflexivity. change (map b8 TMPNAME) with tmpname in NB2.
    clear NBUF. keep_frame AG2. clear MI0.
    pose proof (hinv_mem _ _ _ _ _ HI ST2 MI2) as HI2.
    assert (AGK2 : agrees_on (KEEP CL spB) m m2).
    { eapply agrees_on_trans; [exact AGK1|].
      eapply agrees_on_weaken; [exact AG2|]. unfold KEEP, client_keeps, FZ. cbv beta. intros a [Ha|Ha]; [split; [left; lia| lia]|].
      pose proof (GIo_CLc_facts K R sx2 CL [] FB m2 a ltac:(rewrite app_nil_r; exact G2) Ha) as [Hc _]. split; [right; exact Ha| lia]. }
    cbv beta iota.
    assert (DAT2 : bytes_at usegs m2 D data).
    { eapply agrees_bytes_at; [exact AG2 | exact DAT1 |]. intros a Ha. cbv beta.
      pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) (DIN a Ha)) as [Hc _]. split; [right; apply DIN; exact Ha| lia]. }
    clear DAT1.
    unfold implM. iprefix. lstep.
    destruct Hfd as [Efd|Hpos].
    - (* [comment removed for export] *)
      rewrite Efd. change (bv_lts (Z_to_bv 64 (-1)) z64) with true. cbn [Z.ltb].
      apply evt_done. apply (implM_ret usegs). apply evt_done.
      destruct (frame_forget3 _ _ _ _ _ FR1 NBUF2 FR3) as [j FRL].
      unfold at18. let sblx := fresh "sbl" in pose (sblx := 4392%nat); change 4392%nat with sblx. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact G2|]. split; [exact HI2|]. split; [exact AGK2|]. split; [exact FRL| exact FR4].
    - (* [comment removed for export] *)
      rewrite bv_lts_zero_r, unsigned_lit by lia. replace (2 ^ 63 <=? fd) with false by (symmetry; apply Z.leb_gt; lia).
      replace (fd <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      lstep. apply evt_done. eapply (implM_bind usegs).
      { eapply (CLOSE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R sx2 CL FB lo fd); [spo | reflexivity | lia]. }
      intros rclose sx3 ms3 PO. cbv beta in PO. destruct PO as (a0v & m3 & E & EO3 & MI3 & ST3 & AG3 & G3). post_regs E.
      keep_frame AG3. clear MI2.
      assert (DAT3 : bytes_at usegs m3 D data) by (eapply agrees_bytes_at; [exact AG3 | exact DAT2 | intros a Ha; right; apply DIN; exact Ha]).
      pose proof (hinv_mem _ _ _ _ _ HI ST3 MI3) as HI3.
      assert (AGK3 : agrees_on (KEEP CL spB) m m3) by (eapply agrees_on_trans; [exact AGK2| apply keep_of_callee0; exact AG3]).
      eapply (implM_bind usegs).
      { eapply btf_spec; first [exact G3 | exact HI3 | exact TP | reflexivity | exact DAT3 | exact DIN | exact DLEN | exact NB2 | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption]. }
      intros r sx4 ms4 PO. unfold btf_post in PO. let sblx := fresh "sbl" in pose (sblx := 4096%nat); change 4096%nat with sblx in PO. let sblx := fresh "sbl" in pose (sblx := 256%nat); change 256%nat with sblx in PO. destruct_exs PO.
      destruct PO as (-> & G4 & HI4 & AG4 & FR1' & FR2' & NB' & FR3' & FR4' & Hr).
      destruct Hr as [Hr | ->].
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.ltb_lt r 0) Hr).
        eapply (implM_mono usegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO]; eapply agrees_on_trans; [exact AGK3| exact AG4]].
        eapply unlink18_spec; first [exact UNLINK | exact G4 | exact HI4 | exact TP | exact NB' | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
      + cbn [Z.ltb].
        eapply (implM_mono usegs); [| intros r1 s1' ms1 PO; eapply at18_back; [| exact PO]; eapply agrees_on_trans; [exact AGK3| exact AG4]].
        eapply pcap_part_spec; first [exact G4 | exact HI4 | exact TP | exact SITES | exact NB' | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
  Qed.
  End Sz6.
  Lemma body_spec : ltac:(let t := eval cbv delta [body_spec__stmt] in body_spec__stmt in exact t).
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. intros ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 j1 ej. ltac2:(SecDiet.SzSec.closeP 'body_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End Fuzz.

End WithCeil.
End TwB.
End F_fuzz_D.

(* [comment removed for export] *)
Module F_fuzz_E.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep RegsEquiv MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_D.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Section WithCeil.
Context {CEILV : CEIL}.
Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

  Lemma devnull_Z : map bv_unsigned devnull = DEVNULL.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma devnull_nonul : ~ In (Z_to_bv 8 0) devnull.
  Proof using Type. pin_using tt. unfold devnull, DEVNULL. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
  Lemma devnull_len : length devnull = 9%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma devnull_open_w : open_name_ok true devnull.
  Proof using Type. pin_using tt. right. reflexivity. Qed.

  Lemma GIo_outfile_cell : forall R (s : PSt) CL FB m, GIo K R s CL FB m -> exists v, rw_cells ssegs m 0x339c0 [C8 v].
  Proof using Type. pin_using tt.
    intros R s CL FB m G. destruct (ps_outfile s) as [q|] eqn:EO.
    - destruct (GIo_outfile_some _ _ _ _ _ _ _ G EO) as (A & _ & OC). eexists. exact OC.
    - eexists. exact (GIo_outfile_none _ _ _ _ _ _ G EO).
  Qed.

  Lemma implM_updret_l : forall {A B} g (x : A) (k : A -> M PSt B) (s : PSt) Q ms,
    implM ssegs (k x) (g s) Q ms -> implM ssegs (mbind (mbind (mupd g) (fun _ => mret x)) k) s Q ms.
  Proof using Type. pin_using tt. intros. exact H0. Qed.

  (* [comment removed for export] *)
  Definition outfile_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo D : Z) (data : list byte)
      (cs3 cs2 cs1 cs0 cra : word) (j0 j1 ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R -> sites = sites_at (bv_unsigned spB) ->
    bytes_at ssegs m D data -> (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a) -> Z.of_nat (length data) < 2^26 ->
    rw_cells ssegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells ssegs m (bv_unsigned spB + 40) [CB 30 j1] ->
    rw_cells ssegs m (bv_unsigned spB + 70) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
    rw_cells ssegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells ssegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM ssegs (o <- match ps_outfile s with
                      | Some f => mret (Some f)
                      | None => fo <- s_fopen HO DEVNULL true ;; mupd (set_outfile fo) ;;; mret fo
                      end ;;
                 match o with None => mret tt | Some _ => fuzz_body HO sites (map bv_unsigned data) end) s
      (at18 K spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13fec) fc None m (seg_rom ssegs)).
  Section Sz7.
  Variables ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 j1 ej : ltac2:(SecDiet.SzSec.tyM 'outfile_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma outfile_spec__body : ltac2:(SecDiet.SzSec.bodyP 'outfile_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. pin_using (fun (CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK : unit) => tt).
    idtac; intros G HI TP SITES DAT DIN DLEN FR1 FRT FRZ FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN); unfold FZ, FUZZ_STACK in BU, SPM; unfold rc_spmain in SPM; unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (usp0_range R) as RSP0.
    pose proof (bytes_at_bound _ _ _ _ DAT) as DB.
    destruct (ps_outfile s) as [q|] eqn:EO.
    - (* [comment removed for export] *)
      destruct (GIo_outfile_some _ _ _ _ _ _ _ G EO) as (A & AIN & OC).
      pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact AIN)) as (A1 & _ & _ & A4 & _); cbn [cb_addr cb_size fst snd] in A1, A4.
      apply implM_ret_l.
      unfold implM. iprefix. lstep. lstep. lstep. if_true_by (nez_true A ltac:(lia)). apply evt_done.
      eapply body_spec; first [exact G | exact HI | exact TP | exact SITES | exact DAT | exact DIN | exact DLEN | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
    - (* [comment removed for export] *)
      pose proof (GIo_outfile_none _ _ _ _ _ _ G EO) as OC.
      apply implM_bind_assoc.
      unfold implM. iprefix. lstep. lstep. lstep. if_false. do 5 lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rodata_devnull mm MI) as RB1; pose proof (rodata_w mm MI) as RB2 end.
      rewrite <- devnull_Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply (FOPEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo STR_DEVNULL STR_W devnull [Z_to_bv 8 119] true);
          [ spo | reflexivity | reflexivity | exact RB1 | exact devnull_nonul | rewrite devnull_len; lia | exact devnull_open_w (* [comment removed for export] *)
          | right; rewrite devnull_len; unfold STR_DEVNULL; lia | exact RB2 | left; split; reflexivity ]. }
      intros fo sx2 ms2 PO. cbv beta in PO. destruct PO as (a0v & m2 & E & EO2 & MI2 & ST2 & AG2 & PO). post_regs E.
      clear OC. keep_frame AG2. clear MI.
      assert (DAT2 : bytes_at ssegs m2 D data) by (eapply agrees_bytes_at; [exact AG2 | exact DAT | intros a Ha; right; apply DIN; exact Ha]).
      assert (G2 : exists FB2, GIo K R sx2 CL FB2 m2 /\ match fo with None => a0v = Z_to_bv 64 0 | Some f => exists Af, a0v = Z_to_bv 64 Af /\ In (f, Af, 1264) FB2 end).
      { destruct fo as [f|].
        - destruct PO as (Af & -> & G2). exists ((f, Af, FILE_BLOCK) :: FB). split; [exact G2|]. exists Af. split; [reflexivity| left; reflexivity].
        - destruct PO as (-> & G2 & _). exists FB. split; [exact G2| reflexivity]. }
      clear PO. destruct G2 as (FB2 & G2 & Hfo).
      destruct (GIo_outfile_cell _ _ _ _ _ G2) as [v OC2].
      pose proof (munch_refl [(0x339c0, 0x339c8)]%Z m2) as MU. pose proof (wmono_refl ssegs m2) as WM.
      apply implM_updret_l.
      hide DAT2.
      unfold implM. iprefix. lstep.
      unhide DAT2.
      lazymatch type of MU with munch _ _ ?m3 =>
        assert (DAT3 : bytes_at ssegs m3 D data)
          by (eapply agrees_bytes_at; [eapply (agrees_on_of_munch (fun a => in_block CL a)); [exact MU | exact WM |] | exact DAT2 | exact DIN];
              intros a _ Ha; apply in_block_In in Ha as ([[q' A'] n'] & Hb & Hr); cbn [cb_addr cb_size fst snd] in Hr;
              pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & _ & K5 & _);
              cbn [cb_addr cb_size fst snd] in K5; cbn; lia);
        assert (G3 : GIo K R (set_outfile fo sx2) CL FB2 m3)
          by (eapply (GIo_set_outfile K HFL SFL); [exact G2 | exact MU | exact WM | apply Forall_nil |];
              destruct fo as [f|]; [destruct Hfo as (Af & -> & AIN); exists Af; split; [exact AIN| exact OC2] | rewrite Hfo in OC2; exact OC2]);
        assert (AGK : agrees_on (KEEP CL spB) m m3)
          by (eapply agrees_on_trans; [apply keep_of_callee0; exact AG2|];
              eapply agrees_on_of_munch; [exact MU | exact WM |]; unfold KEEP, client_keeps, FZ; intros a _ [Ha|Ha]; cbn; [lia|];
              apply in_block_In in Ha as ([[q' A'] n'] & Hb & Hr); cbn [cb_addr cb_size fst snd] in Hr;
              pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & _ & K5 & _);
              cbn [cb_addr cb_size fst snd] in K5; lia)
      end.
      clear DAT2 MU WM OC2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) => pose proof (hinv_mem _ _ _ _ m3 HI ltac:(eassumption) ltac:(eassumption)) as HI3 end.
      destruct fo as [f|].
      + destruct Hfo as (Af & -> & AIN).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; exact AIN)) as (A1 & _ & _ & A4 & _); cbn [cb_addr cb_size fst snd] in A1, A4.
        lstep. if_false_by (eqz_false Af ltac:(lia)). apply evt_done.
        eapply (implM_mono ssegs); [| intros r1 s1' ms1 PO; eapply at18_back; [exact AGK| exact PO]].
        eapply body_spec; first [exact G3 | exact HI3 | exact TP | exact SITES | exact DAT3 | exact DIN | exact DLEN | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
      + rewrite Hfo. lstep. if_true. apply evt_done. apply (implM_ret ssegs). apply evt_done.
        lazymatch goal with |- context [MS _ _ _ _ _ ?m3 _] =>
          assert (NBUF : rw_cells ssegs m3 (bv_unsigned spB + 40) [CB 4096 (j1 ++ repeat (Z_to_bv 8 0) 4066)]);
          [ pose proof (rw_cells_merge ssegs m3 (bv_unsigned spB + 40) [] [CB 30 j1; CB 4066 (repeat (Z_to_bv 8 0) 4066)] []) as X |] end.
        { (sl_lit_sizes_in X; cbn [app cells_size csize cells_bytes cbytes Nat.add] in X). rewrite app_nil_r in X. apply X.
          apply (proj2 (rw_cells_app ssegs _ _ [_] _)). split; [eassumption|]. (sl_lit_sizes; cbn [cells_size csize Nat.add]).
          replace (bv_unsigned spB + 40 + Z.of_nat 30) with (bv_unsigned spB + 70) by lia. eassumption. }
        destruct (frame_forget3 _ _ _ _ _ FR1 NBUF FR3) as [j FRL].
        unfold at18. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G3|]. split; [exact HI3|]. split; [exact AGK|]. split; [exact FRL| exact FR4].
  Qed.
  End Sz7.
  Lemma outfile_spec : ltac:(let t := eval cbv delta [outfile_spec__stmt] in outfile_spec__stmt in exact t).
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. intros ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 j1 ej. ltac2:(SecDiet.SzSec.closeP 'outfile_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End Fuzz.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_C.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_D.TwB.
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
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Section WithCeil.
Context {CEILV : CEIL}.
Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

  Lemma devnull_Z : map bv_unsigned devnull = DEVNULL.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma devnull_nonul : ~ In (Z_to_bv 8 0) devnull.
  Proof using Type. pin_using tt. unfold devnull, DEVNULL. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
  Lemma devnull_len : length devnull = 9%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma devnull_open_w : open_name_ok true devnull.
  Proof using Type. pin_using tt. right. reflexivity. Qed.

  Lemma GIo_outfile_cell : forall R (s : PSt) CL FB m, GIo K R s CL FB m -> exists v, rw_cells usegs m 0x34180 [C8 v].
  Proof using Type. pin_using tt.
    intros R s CL FB m G. destruct (ps_outfile s) as [q|] eqn:EO.
    - destruct (GIo_outfile_some _ _ _ _ _ _ _ G EO) as (A & _ & OC). eexists. exact OC.
    - eexists. exact (GIo_outfile_none _ _ _ _ _ _ G EO).
  Qed.

  Lemma implM_updret_l : forall {A B} g (x : A) (k : A -> M PSt B) (s : PSt) Q ms,
    implM usegs (k x) (g s) Q ms -> implM usegs (mbind (mbind (mupd g) (fun _ => mret x)) k) s Q ms.
  Proof using Type. pin_using tt. intros. exact H0. Qed.

  (* [comment removed for export] *)
  Definition outfile_spec__stmt : Prop := forall (ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PSt) (CL FB : list cblk) (lo D : Z) (data : list byte)
      (cs3 cs2 cs1 cs0 cra : word) (j0 j1 ej : list byte),
    GIo K R s CL FB m -> hinv R lo spB m -> tp = rc_tp R -> sites = sites_at (bv_unsigned spB) ->
    bytes_at usegs m D data -> (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a) -> Z.of_nat (length data) < 2^26 ->
    rw_cells usegs m (bv_unsigned spB) [CB 40 j0] ->
    rw_cells usegs m (bv_unsigned spB + 40) [CB 30 j1] ->
    rw_cells usegs m (bv_unsigned spB + 70) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
    rw_cells usegs m (bv_unsigned spB + 4136) [CB 256 ej] ->
    rw_cells usegs m (bv_unsigned spB + 4392) [C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
    implM usegs (o <- match ps_outfile s with
                      | Some f => mret (Some f)
                      | None => fo <- s_fopen HO DEVNULL true ;; mupd (set_outfile fo) ;;; mret fo
                      end ;;
                 match o with None => mret tt | Some _ => fuzz_body HO sites (map bv_unsigned data) end) s
      (at18 K spB gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo cs3 cs2 cs1 cs0 cra m)
      (MS (mkR ra spB gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14060) fc None m (seg_rom usegs)).
  Section Sz7.
  Variables ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 j1 ej : ltac2:(SecDiet.SzSec.tyM 'outfile_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma outfile_spec__body : ltac2:(SecDiet.SzSec.bodyP 'outfile_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. pin_using (fun (CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK : unit) => tt).
    idtac; intros G HI TP SITES DAT DIN DLEN FR1 FRT FRZ FR3 FR4.
    pose proof HI as (ST & LO & BU & SPM & MI & ALN); unfold FZ, FUZZ_STACK in BU, SPM; unfold rc_spmain in SPM; unfold rc_lo in LO.
    pose proof (bv_unsigned_in_range 64 spB) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (usp0_range R) as RSP0.
    pose proof (bytes_at_bound _ _ _ _ DAT) as DB.
    destruct (ps_outfile s) as [q|] eqn:EO.
    - (* [comment removed for export] *)
      destruct (GIo_outfile_some _ _ _ _ _ _ _ G EO) as (A & AIN & OC).
      pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact AIN)) as (A1 & _ & _ & A4 & _); cbn [cb_addr cb_size fst snd] in A1, A4.
      apply implM_ret_l.
      unfold implM. iprefix. lstep. lstep. lstep. if_true_by (nez_true A ltac:(lia)). apply evt_done.
      eapply body_spec; first [exact G | exact HI | exact TP | exact SITES | exact DAT | exact DIN | exact DLEN | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
    - (* [comment removed for export] *)
      pose proof (GIo_outfile_none _ _ _ _ _ _ G EO) as OC.
      apply implM_bind_assoc.
      unfold implM. iprefix. lstep. lstep. lstep. if_false. do 5 lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rodata_devnull mm MI) as RB1; pose proof (rodata_w mm MI) as RB2 end.
      rewrite <- devnull_Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply (FOPEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo STR_DEVNULL STR_W devnull [Z_to_bv 8 119] true);
          [ spo | reflexivity | reflexivity | exact RB1 | exact devnull_nonul | rewrite devnull_len; lia | exact devnull_open_w (* [comment removed for export] *)
          | right; rewrite devnull_len; unfold STR_DEVNULL; lia | exact RB2 | left; split; reflexivity ]. }
      intros fo sx2 ms2 PO. cbv beta in PO. destruct PO as (a0v & m2 & E & EO2 & MI2 & ST2 & AG2 & PO). post_regs E.
      clear OC. keep_frame AG2. clear MI.
      assert (DAT2 : bytes_at usegs m2 D data) by (eapply agrees_bytes_at; [exact AG2 | exact DAT | intros a Ha; right; apply DIN; exact Ha]).
      assert (G2 : exists FB2, GIo K R sx2 CL FB2 m2 /\ match fo with None => a0v = Z_to_bv 64 0 | Some f => exists Af, a0v = Z_to_bv 64 Af /\ In (f, Af, 1264) FB2 end).
      { destruct fo as [f|].
        - destruct PO as (Af & -> & G2). exists ((f, Af, FILE_BLOCK) :: FB). split; [exact G2|]. exists Af. split; [reflexivity| left; reflexivity].
        - destruct PO as (-> & G2 & _). exists FB. split; [exact G2| reflexivity]. }
      clear PO. destruct G2 as (FB2 & G2 & Hfo).
      destruct (GIo_outfile_cell _ _ _ _ _ G2) as [v OC2].
      pose proof (munch_refl [(0x34180, 0x34188)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      apply implM_updret_l.
      hide DAT2.
      unfold implM. iprefix. lstep.
      unhide DAT2.
      lazymatch type of MU with munch _ _ ?m3 =>
        assert (DAT3 : bytes_at usegs m3 D data)
          by (eapply agrees_bytes_at; [eapply (agrees_on_of_munch (fun a => in_block CL a)); [exact MU | exact WM |] | exact DAT2 | exact DIN];
              intros a _ Ha; apply in_block_In in Ha as ([[q' A'] n'] & Hb & Hr); cbn [cb_addr cb_size fst snd] in Hr;
              pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & _ & K5 & _);
              cbn [cb_addr cb_size fst snd] in K5; cbn; lia);
        assert (G3 : GIo K R (set_outfile fo sx2) CL FB2 m3)
          by (eapply (GIo_set_outfile K HFL SFL); [exact G2 | exact MU | exact WM | apply Forall_nil |];
              destruct fo as [f|]; [destruct Hfo as (Af & -> & AIN); exists Af; split; [exact AIN| exact OC2] | rewrite Hfo in OC2; exact OC2]);
        assert (AGK : agrees_on (KEEP CL spB) m m3)
          by (eapply agrees_on_trans; [apply keep_of_callee0; exact AG2|];
              eapply agrees_on_of_munch; [exact MU | exact WM |]; unfold KEEP, client_keeps, FZ; intros a _ [Ha|Ha]; cbn; [lia|];
              apply in_block_In in Ha as ([[q' A'] n'] & Hb & Hr); cbn [cb_addr cb_size fst snd] in Hr;
              pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & _ & K5 & _);
              cbn [cb_addr cb_size fst snd] in K5; lia)
      end.
      clear DAT2 MU WM OC2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) => pose proof (hinv_mem _ _ _ _ m3 HI ltac:(eassumption) ltac:(eassumption)) as HI3 end.
      destruct fo as [f|].
      + destruct Hfo as (Af & -> & AIN).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; exact AIN)) as (A1 & _ & _ & A4 & _); cbn [cb_addr cb_size fst snd] in A1, A4.
        lstep. if_false_by (eqz_false Af ltac:(lia)). apply evt_done.
        eapply (implM_mono usegs); [| intros r1 s1' ms1 PO; eapply at18_back; [exact AGK| exact PO]].
        eapply body_spec; first [exact G3 | exact HI3 | exact TP | exact SITES | exact DAT3 | exact DIN | exact DLEN | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption].
      + rewrite Hfo. lstep. if_true. apply evt_done. apply (implM_ret usegs). apply evt_done.
        lazymatch goal with |- context [MS _ _ _ _ _ ?m3 _] =>
          assert (NBUF : rw_cells usegs m3 (bv_unsigned spB + 40) [CB 4096 (j1 ++ repeat (Z_to_bv 8 0) 4066)]);
          [ pose proof (rw_cells_merge usegs m3 (bv_unsigned spB + 40) [] [CB 30 j1; CB 4066 (repeat (Z_to_bv 8 0) 4066)] []) as X |] end.
        { (sl_lit_sizes_in X; cbn [app cells_size csize cells_bytes cbytes Nat.add] in X). rewrite app_nil_r in X. apply X.
          apply (proj2 (rw_cells_app usegs _ _ [_] _)). split; [eassumption|]. (sl_lit_sizes; cbn [cells_size csize Nat.add]).
          replace (bv_unsigned spB + 40 + Z.of_nat 30) with (bv_unsigned spB + 70) by lia. eassumption. }
        destruct (frame_forget3 _ _ _ _ _ FR1 NBUF FR3) as [j FRL].
        unfold at18. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact G3|]. split; [exact HI3|]. split; [exact AGK|]. split; [exact FRL| exact FR4].
  Qed.
  End Sz7.
  Lemma outfile_spec : ltac:(let t := eval cbv delta [outfile_spec__stmt] in outfile_spec__stmt in exact t).
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. intros ra spB gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo D data cs3 cs2 cs1 cs0 cra j0 j1 ej. ltac2:(SecDiet.SzSec.closeP 'outfile_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End Fuzz.

End WithCeil.
End TwB.
End F_fuzz_E.

(* [comment removed for export] *)
Module F_fuzz_main.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep RegsEquiv MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_D OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_E.
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
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Section WithCeil.
Context {CEILV : CEIL}.
Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

  (* [comment removed for export] *)
  Definition fuzz_one_proof__stmt : Prop := fuzz_one_stmt HO K (fun v => sites_at (v - FUZZ_FRAME)) sites.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo D data : ltac2:(SecDiet.SzSec.tyM 'fuzz_one_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fuzz_one_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fuzz_one_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. pin_using (fun (CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK : unit) => tt).
    intros PRE SITES Ea0 Ea1 DAT DIN DLEN.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    apply (GI_open K) in G. destruct G as [FB G].
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (usp0_range R) as RSP0.
    unfold rc_lo in LO. unfold rc_spmain in SPM. unfold FUZZ_STACK in BU. unfold FUZZ_FRAME in SITES.
    pose proof (bytes_at_bound _ _ _ _ DAT) as DB.
    subst a0 a1.
    unfold harness_call. rewrite fuzz_unfold.
    pose proof (munch_refl [(bv_unsigned sp - 4432, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold implM. iprefix.
    hide DAT.
    call prologue_spec; [exact ST | unfold FZ; lia | exact MI |].
    unhide DAT.
    lazymatch goal with MU : munch _ m ?m1 |- _ =>
      assert (DAT1 : bytes_at ssegs m1 D data)
        by (eapply agrees_bytes_at; [eapply (agrees_on_of_munch (fun a => in_block CL a)); [exact MU | eassumption |] | exact DAT | exact DIN];
            intros a _ Ha; pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; cbn; lia);
      assert (G1 : GIo K R s CL FB m1)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | eassumption |]; apply Forall_cons; [| apply Forall_nil]; left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia);
      assert (AGK0 : agrees_on (client_keeps CL (bv_unsigned sp)) m m1)
        by (eapply agrees_on_of_munch; [exact MU | eassumption |]; unfold client_keeps; intros a _ [Ha|Ha]; cbn; [lia|];
            pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; lia)
    end.
    clear DAT.
    name_sp sp (-4432)%Z.
    lazymatch goal with ST1 : stk ssegs _ lo (bv_unsigned sp + -4432) |- _ => rewrite <- Hsp in ST1 | _ => idtac end.
    repeat match goal with
    | FR : rw_cells ssegs _ (bv_unsigned sp + ?k) _ |- _ =>
        let k' := eval vm_compute in (k + 4432)%Z in
        lazymatch k' with
        | 0%Z => replace (bv_unsigned sp + k)%Z with (bv_unsigned sp0) in FR by lia
        | _ => replace (bv_unsigned sp + k)%Z with (bv_unsigned sp0 + k')%Z in FR by lia
        end
    end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (HI1 : hinv R lo sp0 m1)
        by (split; [assumption|]; split; [unfold rc_lo; lia|]; split; [unfold FUZZ_STACK, FZ; lia|]; split; [unfold rc_spmain, FZ; lia|];
            split; [assumption|]; rewrite Hsp; replace (bv_unsigned sp + -4432) with (bv_unsigned sp - 16 * 277) by lia;
            rewrite <- Zminus_mod_idemp_l, ALN; reflexivity) end.
    assert (SITES' : sites = sites_at (bv_unsigned sp0)) by (rewrite Hsp, SITES; f_equal; lia).
    apply evt_done. eapply (implM_bind ssegs).
    { apply implM_getret_l.
      eapply outfile_spec; first [exact G1 | exact HI1 | exact TP | exact SITES' | exact DAT1 | exact DIN | exact DLEN | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption]. }
    intros [] s' ms' PO. unfold at18 in PO. destruct_exs PO. destruct PO as (-> & G' & HI' & AG' & FRL & FRH).
    pose proof HI' as (ST' & _ & _ & _ & MI' & _).
    apply (implM_ret ssegs).
    eapply evt_cut; [eapply epilogue_spec; [exact ST' | exact MI' | unfold FZ; lia | lia | exact FRL | exact FRH] |].
    cbv beta. intros ms2 [-> ST2]. apply evt_done.
    unfold fuzz_post. repeat (lazymatch goal with |- ex _ => eexists end).
    replace (Z_to_bv 64 (bv_unsigned sp0 + FZ)) with sp by (unfold FZ; rewrite Hsp; replace (bv_unsigned sp + -4432 + 4432) with (bv_unsigned sp) by lia; symmetry; apply Z_to_bv_bv_unsigned).
    split; [reflexivity|]. split; [exact MI'|]. split; [unfold FZ in ST2; rewrite Hsp in ST2; replace (bv_unsigned sp + -4432 + 4432) with (bv_unsigned sp) in ST2 by lia; exact ST2|].
    split. { eapply agrees_on_trans; [exact AGK0|]. unfold KEEP, FZ in AG'. rewrite Hsp in AG'. replace (bv_unsigned sp + -4432 + 4432) with (bv_unsigned sp) in AG' by lia. exact AG'. }
    split; [eapply (GIo_close K); exact G'| reflexivity].
  Qed.
  End Sz1.
  Theorem fuzz_one_proof : ltac:(let t := eval cbv delta [fuzz_one_proof__stmt] in fuzz_one_proof__stmt in exact t).
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo D data. ltac2:(SecDiet.SzSec.closeP 'fuzz_one_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fuzz.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.FuzzKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_C.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_D.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_E.TwB.
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
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Section WithCeil.
Context {CEILV : CEIL}.
Section Fuzz.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO K sites.
  Hypothesis PNEXT : pcap_next_ex_stmt HO K sites.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : pcap_close_stmt HO K sites.

  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

  (* [comment removed for export] *)
  Definition fuzz_one_proof__stmt : Prop := fuzz_one_stmt HO K (fun v => sites_at (v - FUZZ_FRAME)) sites.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo D data : ltac2:(SecDiet.SzSec.tyM 'fuzz_one_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fuzz_one_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fuzz_one_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. pin_using (fun (CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK : unit) => tt).
 intros PRE SITES Ea0 Ea1 DAT DIN DLEN.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    apply (GI_open K) in G. destruct G as [FB G].
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (usp0_range R) as RSP0.
    unfold rc_lo in LO. unfold rc_spmain in SPM. unfold FUZZ_STACK in BU. unfold FUZZ_FRAME in SITES.
    pose proof (bytes_at_bound _ _ _ _ DAT) as DB.
    subst a0 a1.
    unfold harness_call. rewrite fuzz_unfold.
    pose proof (munch_refl [(bv_unsigned sp - 4432, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.
    hide DAT.
    call prologue_spec; [exact ST | unfold FZ; lia | exact MI |].
    unhide DAT.
    lazymatch goal with MU : munch _ m ?m1 |- _ =>
      assert (DAT1 : bytes_at usegs m1 D data)
        by (eapply agrees_bytes_at; [eapply (agrees_on_of_munch (fun a => in_block CL a)); [exact MU | eassumption |] | exact DAT | exact DIN];
            intros a _ Ha; pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; cbn; lia);
      assert (G1 : GIo K R s CL FB m1)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | eassumption |]; apply Forall_cons; [| apply Forall_nil]; left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia);
      assert (AGK0 : agrees_on (client_keeps CL (bv_unsigned sp)) m m1)
        by (eapply agrees_on_of_munch; [exact MU | eassumption |]; unfold client_keeps; intros a _ [Ha|Ha]; cbn; [lia|];
            pose proof (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; lia)
    end.
    clear DAT.
    name_sp sp (-4432)%Z.
    lazymatch goal with ST1 : stk usegs _ lo (bv_unsigned sp + -4432) |- _ => rewrite <- Hsp in ST1 | _ => idtac end.
    repeat match goal with
    | FR : rw_cells usegs _ (bv_unsigned sp + ?k) _ |- _ =>
        let k' := eval vm_compute in (k + 4432)%Z in
        lazymatch k' with
        | 0%Z => replace (bv_unsigned sp + k)%Z with (bv_unsigned sp0) in FR by lia
        | _ => replace (bv_unsigned sp + k)%Z with (bv_unsigned sp0 + k')%Z in FR by lia
        end
    end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (HI1 : hinv R lo sp0 m1)
        by (split; [assumption|]; split; [unfold rc_lo; lia|]; split; [unfold FUZZ_STACK, FZ; lia|]; split; [unfold rc_spmain, FZ; lia|];
            split; [assumption|]; rewrite Hsp; replace (bv_unsigned sp + -4432) with (bv_unsigned sp - 16 * 277) by lia;
            rewrite <- Zminus_mod_idemp_l, ALN; reflexivity) end.
    assert (SITES' : sites = sites_at (bv_unsigned sp0)) by (rewrite Hsp, SITES; f_equal; lia).
    apply evt_done. eapply (implM_bind usegs).
    { apply implM_getret_l.
      eapply outfile_spec; first [exact G1 | exact HI1 | exact TP | exact SITES' | exact DAT1 | exact DIN | exact DLEN | (match goal with HSYN__ : ?TSYN__ |- ?GSYN__ => constr_eq TSYN__ GSYN__; exact HSYN__ end) | eassumption]. }
    intros [] s' ms' PO. unfold at18 in PO. destruct_exs PO. destruct PO as (-> & G' & HI' & AG' & FRL & FRH).
    pose proof HI' as (ST' & _ & _ & _ & MI' & _).
    apply (implM_ret usegs).
    eapply evt_cut; [eapply epilogue_spec; [exact ST' | exact MI' | unfold FZ; lia | lia | exact FRL | exact FRH] |].
    cbv beta. intros ms2 [-> ST2]. apply evt_done.
    unfold fuzz_post. repeat (lazymatch goal with |- ex _ => eexists end).
    replace (Z_to_bv 64 (bv_unsigned sp0 + FZ)) with sp by (unfold FZ; rewrite Hsp; replace (bv_unsigned sp + -4432 + 4432) with (bv_unsigned sp) by lia; symmetry; apply Z_to_bv_bv_unsigned).
    split; [reflexivity|]. split; [exact MI'|]. split; [unfold FZ in ST2; rewrite Hsp in ST2; replace (bv_unsigned sp + -4432 + 4432) with (bv_unsigned sp) in ST2 by lia; exact ST2|].
    split. { eapply agrees_on_trans; [exact AGK0|]. unfold KEEP, FZ in AG'. rewrite Hsp in AG'. replace (bv_unsigned sp + -4432 + 4432) with (bv_unsigned sp) in AG' by lia. exact AG'. }
    split; [eapply (GIo_close K); exact G'| reflexivity].
  Qed.
  End Sz1.
  Theorem fuzz_one_proof : ltac:(let t := eval cbv delta [fuzz_one_proof__stmt] in fuzz_one_proof__stmt in exact t).
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL lo D data. ltac2:(SecDiet.SzSec.closeP 'fuzz_one_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fuzz.

End WithCeil.
End TwB.
End F_fuzz_main.

(* [comment removed for export] *)
Module ProgImpl.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv ImgSrc3.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StartupFacts. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StartupFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.Startup_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_target_run OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_main_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_main_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.GIInit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_main.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import EntryCeil.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL}.
Section ProgImpl.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  (* [comment removed for export] *)
  Variables (h0 : H) (SEF : Z) (rnd0 : EntryDraw).
  (* [comment removed for export] *)
  Definition sites_of (v : Z) : stack_site -> Z := sites_at (v - FUZZ_FRAME).
  Definition sites (en : ExecEntry) : stack_site -> Z := sites_of (bv_unsigned (en_sp en) - 208).
  Hypothesis SEF_range : 0 <= SEF <= 0x10000.
  (* [comment removed for export] *)
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HCB : heap_cb_law K.       (* [comment removed for export] *)
  Hypothesis SCB : stdio_cb_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis HINIT : heap_init_law HO K h0 rnd0.
  Hypothesis SINIT : stdio_init_law K.
  (* [comment removed for export] *)
  Hypothesis MALLOC : malloc_stmt HO K.
  Hypothesis FREE : free_stmt HO K.
  Hypothesis VPR : vprintf_d_stmt K.
  Hypothesis EPR_USAGE : eprintf_s_stmt47 K FMT_USAGE pieces_usage.   (* [comment removed for export] *)
  Hypothesis EPR_OPEN : eprintf_s_stmt47 K FMT_CANNOT_OPEN pieces_cannot_open.
  Hypothesis EPR_READ : eprintf_s_stmt47 K FMT_READ_ERROR pieces_read_error.
  Hypothesis EPR_BIG : eprintf_i_stmt K FMT_TOO_BIG 0x4000000 pieces_too_big.
  Hypothesis EFW : efwrite_stmt K.
  Hypothesis STDIO_EXIT : stdio_exit_stmt s_stdio_exit (SXGI K) SEF.
  (* [comment removed for export] *)
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : forall stk, pcap_open_offline_stmt HO K stk.
  Hypothesis PNEXT : forall stk, pcap_next_ex_stmt HO K stk.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : forall stk, pcap_close_stmt HO K stk.

  Lemma FUZZ : forall stk, fuzz_one_stmt HO K sites_of stk.
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. pin_using (fun (CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK : unit) => tt). ceil_facts.
    intros stk. exact (fuzz_one_proof HO K stk HFL SFL HAL EQB FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O
                         FPRINTF_DD FPRINTF_S (POPEN stk) (PNEXT stk) PSTATS (PCLOSE stk)).
  Qed.

  Definition main_of (en : ExecEntry) (inp : ProcInput) : M (PState H hptr) Z :=
    main_prog HO fo_nop (sites en) (argv_Z (in_argv inp)).

  (* [comment removed for export] *)
  Lemma SITE_RS : forall en, sites en SiteReadStage = 0x23989.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros en. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition EN_OK (en : ExecEntry) : Prop :=
    alloc_ceiling <= bv_unsigned (en_sp en) - 8388608 /\ en_draw en = rnd0.

  (* [comment removed for export] *)
  Theorem main_stmt_proof :
    main_stmt (set_tls_pin HO) main_of (SXGI K) SEF (fun s => s = ps_init h0) EN_OK.
  Proof using CLOSE EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FREE FWRITE HAL HCB HFL HINIT MALLOC MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SCB SEF_range SFL SINIT UNLINK VPR. pin_using (fun (CLOSE EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FREE FWRITE HAL HCB HFL HINIT MALLOC MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SCB SEF_range SFL SINIT UNLINK VPR : unit) => tt). ceil_facts.
    intros en inp tp s ms -> [_ EDRAW] VE VI AM.
    pose proof (valid_entry_sp _ _ _ VI VE) as VSP.
    apply (valid_entry_sv48 _ _ _ (valid_input_sv48 inp VI)) in VE.
    destruct en as [sp0 brk mb rnd]. destruct VE as (_ & _ & _ & FITS). destruct inp as [argv envp fs sin uid gid groups net nofile sigmask hw abterm vasz].
    cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap] in *. subst rnd.
    destruct VI as (VARGV & _).
    unfold main_of. cbn [in_argv].
    change (argv_Z argv) with (argv_Z (rc_argv (mkRC sp0 argv envp uid hw rnd0 tp false))).
    eapply (implM_mono ssegs).
    - apply (main_spec HO K sites_of (sites (mkEntry sp0 brk mb rnd0)) SEF SEF_range HFL SFL HCB SCB MALLOC FREE (FUZZ _) VPR EPR_USAGE EPR_OPEN EPR_READ EPR_BIG EFW (SITE_RS _)); [reflexivity|reflexivity|].
      apply (GI_init HO K h0 rnd0 HINIT SINIT); [exact VSP | exact VARGV | exact FITS | exact AM].
    - intros code s' ms' HP. exact HP.
  Qed.

  (* [comment removed for export] *)
  Theorem prog_impl : forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage ssegs Plain.M.init_pc Plain.M.phdrs) en inp ->
    valid_input inp ->
    EN_OK en ->
    impl ssegs (at_node ssegs) (npeek ssegs)
         (prog_itree HO 0x339d0 h0 fo_nop (sites en) (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 ssegs Plain.M.init_pc Plain.M.phdrs en inp).
  Proof using CLOSE EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FREE FWRITE HAL HCB HFL HINIT MALLOC MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SCB SEF_range SFL SINIT STDIO_EXIT UNLINK VPR. pin_using (fun (CLOSE EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FREE FWRITE HAL HCB HFL HINIT MALLOC MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SCB SEF_range SFL SINIT STDIO_EXIT UNLINK VPR : unit) => tt). ceil_facts.
    intros en inp VE VI ENOK.
    exact (prog_impl_from_main (set_tls_pin HO) main_of s_stdio_exit
             (SXGI K) SEF (proj1 SEF_range) (SXGI_frame K HFL SFL) STDIO_EXIT (fun s => s = ps_init h0)
             EN_OK (fun en H => proj1 H)
             main_stmt_proof (ps_init h0) en inp eq_refl VE VI ENOK).
  Qed.
End ProgImpl.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StartupFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.Startup_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Compose.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Ifaces47.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_target_run.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_main_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_main_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.GIInit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.F_fuzz_main.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.TopLevel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top.EntryCeil.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL}.
Section ProgImpl.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  (* [comment removed for export] *)
  Variables (h0 : H) (SEF : Z) (rnd0 : EntryDraw).
  (* [comment removed for export] *)
  Definition sites_of (v : Z) : stack_site -> Z := sites_at (v - FUZZ_FRAME).
  Definition sites (en : ExecEntry) : stack_site -> Z := sites_of (bv_unsigned (en_sp en) - 208).
  Hypothesis SEF_range : 0 <= SEF <= 0x10000.
  (* [comment removed for export] *)
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HCB : heap_cb_law K.       (* [comment removed for export] *)
  Hypothesis SCB : stdio_cb_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis HINIT : heap_init_law HO K h0 rnd0.
  Hypothesis SINIT : stdio_init_law K.
  (* [comment removed for export] *)
  Hypothesis MALLOC : malloc_stmt HO K.
  Hypothesis FREE : free_stmt HO K.
  Hypothesis VPR : vprintf_d_stmt K.
  Hypothesis EPR_USAGE : eprintf_s_stmt47 K FMT_USAGE pieces_usage.   (* [comment removed for export] *)
  Hypothesis EPR_OPEN : eprintf_s_stmt47 K FMT_CANNOT_OPEN pieces_cannot_open.
  Hypothesis EPR_READ : eprintf_s_stmt47 K FMT_READ_ERROR pieces_read_error.
  Hypothesis EPR_BIG : eprintf_i_stmt K FMT_TOO_BIG 0x4000000 pieces_too_big.
  Hypothesis EFW : efwrite_stmt K.
  Hypothesis STDIO_EXIT : stdio_exit_stmt s_stdio_exit (SXGI K) SEF.
  (* [comment removed for export] *)
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FWRITE : fwrite_stmt_o HO K.
  Hypothesis REMOVE : remove_stmt_o K.
  Hypothesis UNLINK : unlink_stmt_o K.
  Hypothesis CLOSE : close_stmt_o K.
  Hypothesis MKSTEMP : mkstemp_stmt_o K.
  Hypothesis PRINTF_R : printf_d_stmt_o K FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o K FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO K FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO K FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : forall stk, pcap_open_offline_stmt HO K stk.
  Hypothesis PNEXT : forall stk, pcap_next_ex_stmt HO K stk.
  Hypothesis PSTATS : pcap_stats_stmt K.
  Hypothesis PCLOSE : forall stk, pcap_close_stmt HO K stk.

  Lemma FUZZ : forall stk, fuzz_one_stmt HO K sites_of stk.
  Proof using CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK. pin_using (fun (CLOSE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FWRITE HAL HFL MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SFL UNLINK : unit) => tt). ceil_facts.
    intros stk. exact (fuzz_one_proof HO K stk HFL SFL HAL EQB FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O
                         FPRINTF_DD FPRINTF_S (POPEN stk) (PNEXT stk) PSTATS (PCLOSE stk)).
  Qed.

  Definition main_of (en : ExecEntry) (inp : ProcInput) : M (PState H hptr) Z :=
    main_prog HO fo_nop (sites en) (argv_Z (in_argv inp)).

  (* [comment removed for export] *)
  Lemma SITE_RS : forall en, sites en SiteReadStage = 0x24149.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros en. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition EN_OK (en : ExecEntry) : Prop :=
    alloc_ceiling <= bv_unsigned (en_sp en) - 8388608 /\ en_draw en = rnd0.

  (* [comment removed for export] *)
  Theorem main_stmt_proof :
    main_stmt (set_tls_pin HO) main_of (SXGI K) SEF (fun s => s = ps_init h0) EN_OK.
  Proof using CLOSE EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FREE FWRITE HAL HCB HFL HINIT MALLOC MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SCB SEF_range SFL SINIT UNLINK VPR. pin_using (fun (CLOSE EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FREE FWRITE HAL HCB HFL HINIT MALLOC MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SCB SEF_range SFL SINIT UNLINK VPR : unit) => tt). ceil_facts.
    intros en inp tp s ms -> [_ EDRAW] VE VI AM.
    pose proof (valid_entry_sp _ _ _ VI VE) as VSP.
    apply (valid_entry_sv48 _ _ _ (valid_input_sv48 inp VI)) in VE.
    destruct en as [sp0 brk mb rnd]. destruct VE as (_ & _ & _ & FITS). destruct inp as [argv envp fs sin uid gid groups net nofile sigmask hw abterm vasz].
    cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap] in *. subst rnd.
    destruct VI as (VARGV & _).
    unfold main_of. cbn [in_argv].
    change (argv_Z argv) with (argv_Z (rc_argv (mkRC sp0 argv envp uid hw rnd0 tp false))).
    eapply (implM_mono usegs).
    - apply (main_spec HO K sites_of (sites (mkEntry sp0 brk mb rnd0)) SEF SEF_range HFL SFL HCB SCB MALLOC FREE (FUZZ _) VPR EPR_USAGE EPR_OPEN EPR_READ EPR_BIG EFW (SITE_RS _)); [reflexivity|reflexivity|].
      apply (GI_init HO K h0 rnd0 HINIT SINIT); [exact VSP | exact VARGV | exact FITS | exact AM].
    - intros code s' ms' HP. exact HP.
  Qed.

  (* [comment removed for export] *)
  Theorem prog_impl : forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
    valid_input inp ->
    EN_OK en ->
    impl usegs (at_node usegs) (npeek usegs)
         (prog_itree HO 0x34190 h0 fo_nop (sites en) (in_argv inp))
         (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 usegs Ubsan.M.init_pc Ubsan.M.phdrs en inp).
  Proof using CLOSE EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FREE FWRITE HAL HCB HFL HINIT MALLOC MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SCB SEF_range SFL SINIT STDIO_EXIT UNLINK VPR. pin_using (fun (CLOSE EFW EPR_BIG EPR_OPEN EPR_READ EPR_USAGE EQB FCLOSE FOPEN FPRINTF_DD FPRINTF_S FREE FWRITE HAL HCB HFL HINIT MALLOC MKSTEMP PCLOSE PNEXT POPEN PRINTF_O PRINTF_R PSTATS REMOVE SCB SEF_range SFL SINIT STDIO_EXIT UNLINK VPR : unit) => tt). ceil_facts.
    intros en inp VE VI ENOK.
    exact (prog_impl_from_main (set_tls_pin HO) main_of s_stdio_exit
             (SXGI K) SEF (proj1 SEF_range) (SXGI_frame K HFL SFL) STDIO_EXIT (fun s => s = ps_init h0)
             EN_OK (fun en H => proj1 H)
             main_stmt_proof (ps_init h0) en inp eq_refl VE VI ENOK).
  Qed.
End ProgImpl.

End WithCeil.
End TwB.
End ProgImpl.
