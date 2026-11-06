(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StrerrorTable StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require StrerrorData.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From Stdlib Require Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_pcap_err.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StrerrorTable StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require StrerrorData. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.StrerrorData.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_strerror OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.
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
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition strerror_chk (k : nat) : bool :=
  if list_eq_dec Z.eq_dec (nth k strerror_msgZ [])
       (str (match table_lookup strerror_table (Z.of_nat k) with Some s => s | None => strerror_default end))
  then true else false.

Lemma strerror_chk_all : forallb strerror_chk (seq 0 132) = true.
Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.

Definition strerror_tables_agree__stmt : Prop := forall e, (-2^31 <= e < 2^31)%Z -> strerror_msgb e = map b8 (Fmt.strerror e).
Section Sz2.
Variables e : ltac2:(SecDiet.SzSec.tyM 'strerror_tables_agree__stmt "v" @e).
Lemma strerror_tables_agree__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_tables_agree__stmt "v").
Proof using Type. pin_using tt.
  intros He.
 unfold strerror_msgb, sr_msgb, strerror_e, Fmt.strerror, StrerrorTable.STRERROR_N, b8.
  set (k := if ((0 <=? e) && (e <? 132))%Z then e else 0%Z).
  assert (Hk : (0 <= k < 132)%Z) by (subst k; destruct (Z.leb_spec 0 e), (Z.ltb_spec e 132); cbn; lia).
  f_equal.
  pose proof (proj1 (forallb_forall _ _) strerror_chk_all (Z.to_nat k) ltac:(apply in_seq; lia)) as C.
  unfold strerror_chk in C. rewrite Z2Nat.id in C by lia.
  destruct (list_eq_dec Z.eq_dec _ _) as [E|NE]; [exact E| discriminate C].
Qed.
End Sz2.
Lemma strerror_tables_agree : ltac:(let t := eval cbv delta [strerror_tables_agree__stmt] in strerror_tables_agree__stmt in exact t).
Proof using Type. intros e. ltac2:(SecDiet.SzSec.closeP 'strerror_tables_agree__body "v"). Qed.

Lemma s32_id : forall e, (-2^31 <= e < 2^31)%Z -> s32 e = e.
Proof using Type. pin_using tt. intros e He. unfold s32. rewrite Z.mod_small by lia. lia. Qed.

Section Err.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  Definition pcap_strerror_proof__stmt : Prop := pcap_strerror_stmt K.
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo e : ltac2:(SecDiet.SzSec.tyM 'pcap_strerror_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_strerror_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_strerror_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros PRE -> He.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L0_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (GIo_tls K _ _ _ _ _ G) as [_ TB]. unfold tls_block_ok in TB.
    pose proof (GIo_core_tls K _ _ _ _ _ G) as (tt & ew & T1 & T2 & T3 & T4 & T5 & T6 & Ht).
    pose proof (GIo_core_libc K _ _ _ _ _ G) as (LC & _).
    pose proof (GIo_pcap_tls K _ _ _ _ _ G) as [old TLS].
    unfold utp in *. rewrite <- TP in *.
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 4 T3) as [_ T3b]. cbn [firstn skipn cells_size csize Nat.add] in T3b.
    destruct (rw_cells_cut _ _ _ 1 T3b) as [LOCP _]. cbn [firstn skipn cells_size csize Nat.add] in LOCP.
    replace (bv_unsigned tp + -160 + Z.of_nat 112)%Z with (bv_unsigned tp + -48)%Z in LOCP by lia.
    destruct (rw_cells_cut _ _ _ 11 LC) as [_ LCl]. cbn [firstn skipn cells_size csize Nat.add libc_cells] in LCl.
    apply (rw_cells_split_CB ssegs _ _ [] 48 _ [] [40; 8]%nat) in LCl; [|reflexivity]. cbn [mk_CB_cells app] in LCl.
    destruct (rw_cells_cut _ _ _ 1 LCl) as [_ CAT]. cbn [firstn skipn cells_size csize Nat.add] in CAT.
    assert (CAT8 : rw_cells ssegs m (0x53d60 + 40) [C8 (Z_to_bv 64 0)]).
    { eapply rw_cells_recell; [exact CAT | cbn; repeat split; exact Logic.I | vm_compute; reflexivity]. }
    clear CAT LCl T3b.
    rewrite (s32_id e He).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned tp, bv_unsigned tp + 256)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold PCAP_STRERROR_ENTRY. carve_frame 32%nat ST. do 10 step.
    name_sp sp (-32)%Z.
    call (strerror_r_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e 256 0x53d60 z64 old lo);
      [ rewrite Hsp; exact ST | exact TLS | exact LOCP | exact CAT8 | assumption | reflexivity | exact He | reflexivity | lia | lia | lia
      | rewrite Hsp; lia | rewrite Hsp; lia | lia | lia | rewrite Hsp; lia | rewrite Hsp; lia | lia | ].
    rewrite Hsp in *. unname_sp. rename PC into ST. rename PC0 into RES. clear PC1 POST.
    step. if_true. do 6 step.
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    pose proof (strerror_msgb_length e) as ML. rewrite (strerror_tables_agree e He) in *. rewrite length_map in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with HB : rw_cells _ mm (bv_unsigned tp) ?cs |- _ =>
        pose proof (rw_cells_merge ssegs mm (bv_unsigned tp) [] cs [] ltac:(rewrite app_nil_r; exact HB)) as TLS';
        cbn [cells_size csize cells_bytes cbytes Nat.add app] in TLS';
        replace (length (Fmt.strerror e) + 1 + (Z.to_nat 256 - (length (Fmt.strerror e) + 1) + 0))%nat with 256%nat in TLS' by lia
      end;
      assert (G' : GIo K R s CL FB mm)
        by (eapply (GIo_client_frame_tls K HFL SFL) with (W := [(bv_unsigned sp - 64, bv_unsigned sp)]%Z); [exact G | | exact WM | | unfold utp; rewrite <- TP; exact TLS'];
            [ eapply munch_weaken; [| exact MU]; intros a Ho; unfold utp in Ho; rewrite <- TP in Ho; cbn [outside] in *; tauto
            | apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil] ])
    end.
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    split. { eapply agrees_on_of_munch; [exact MU | exact WM |]. intros a _ [Ha|Ha]; cbn [outside]; [lia|].
             destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _].
             apply in_block_In in Ha as (b & HbIn & Hb).
             destruct (GIo_block_ok K _ _ _ _ _ b G ltac:(apply in_or_app; left; exact HbIn)) as (K1 & K2 & K3 & K4 & K5 & K6).
             unfold utp in K6. rewrite <- TP in K6. lia. }
    split; [exact G'|].
    replace (Z.to_nat 256 - (length (Fmt.strerror e) + 1))%nat with (255 - length (Fmt.strerror e))%nat in RES by lia.
    exact RES.
  Qed.
  End Sz4.
  Theorem pcap_strerror_proof : ltac:(let t := eval cbv delta [pcap_strerror_proof__stmt] in pcap_strerror_proof__stmt in exact t).
  Proof using HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo e. ltac2:(SecDiet.SzSec.closeP 'pcap_strerror_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Err.


End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StrerrorTable OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.StrerrorData.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_strerror.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.
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
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition strerror_chk (k : nat) : bool :=
  if list_eq_dec Z.eq_dec (nth k strerror_msgZ [])
       (str (match table_lookup strerror_table (Z.of_nat k) with Some s => s | None => strerror_default end))
  then true else false.

Lemma strerror_chk_all : forallb strerror_chk (seq 0 132) = true.
Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.

Definition strerror_tables_agree__stmt : Prop := forall e, (-2^31 <= e < 2^31)%Z -> strerror_msgb e = map b8 (Fmt.strerror e).
Section Sz2.
Variables e : ltac2:(SecDiet.SzSec.tyM 'strerror_tables_agree__stmt "v" @e).
Lemma strerror_tables_agree__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_tables_agree__stmt "v").
Proof using Type. pin_using tt.
  intros He.
 unfold strerror_msgb, sr_msgb, strerror_e, Fmt.strerror, StrerrorTable.STRERROR_N, b8.
  set (k := if ((0 <=? e) && (e <? 132))%Z then e else 0%Z).
  assert (Hk : (0 <= k < 132)%Z) by (subst k; destruct (Z.leb_spec 0 e), (Z.ltb_spec e 132); cbn; lia).
  f_equal.
  pose proof (proj1 (forallb_forall _ _) strerror_chk_all (Z.to_nat k) ltac:(apply in_seq; lia)) as C.
  unfold strerror_chk in C. rewrite Z2Nat.id in C by lia.
  destruct (list_eq_dec Z.eq_dec _ _) as [E|NE]; [exact E| discriminate C].
Qed.
End Sz2.
Lemma strerror_tables_agree : ltac:(let t := eval cbv delta [strerror_tables_agree__stmt] in strerror_tables_agree__stmt in exact t).
Proof using Type. intros e. ltac2:(SecDiet.SzSec.closeP 'strerror_tables_agree__body "v"). Qed.

Lemma s32_id : forall e, (-2^31 <= e < 2^31)%Z -> s32 e = e.
Proof using Type. pin_using tt. intros e He. unfold s32. rewrite Z.mod_small by lia. lia. Qed.

Section Err.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  Definition pcap_strerror_proof__stmt : Prop := pcap_strerror_stmt K.
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo e : ltac2:(SecDiet.SzSec.tyM 'pcap_strerror_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_strerror_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_strerror_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
 intros PRE -> He.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L0_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (GIo_tls K _ _ _ _ _ G) as [_ TB]. unfold tls_block_ok_u in TB.
    pose proof (GIo_core_tls K _ _ _ _ _ G) as (tt & ew & T1 & T2 & T3 & T4 & T5 & T6 & Ht).
    pose proof (GIo_core_libc K _ _ _ _ _ G) as (LC & _).
    pose proof (GIo_pcap_tls K _ _ _ _ _ G) as [old TLS].
    unfold utp in *. rewrite <- TP in *.
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 4 T3) as [_ T3b]. cbn [firstn skipn cells_size csize Nat.add] in T3b.
    destruct (rw_cells_cut _ _ _ 1 T3b) as [LOCP _]. cbn [firstn skipn cells_size csize Nat.add] in LOCP.
    replace (bv_unsigned tp + -160 + Z.of_nat 112)%Z with (bv_unsigned tp + -48)%Z in LOCP by lia.
    destruct (rw_cells_cut _ _ _ 11 LC) as [_ LCl]. cbn [firstn skipn cells_size csize Nat.add libc_cells] in LCl.
    apply (rw_cells_split_CB usegs _ _ [] 48 _ [] [40; 8]%nat) in LCl; [|reflexivity]. cbn [mk_CB_cells app] in LCl.
    destruct (rw_cells_cut _ _ _ 1 LCl) as [_ CAT]. cbn [firstn skipn cells_size csize Nat.add] in CAT.
    assert (CAT8 : rw_cells usegs m (0x54520 + 40) [C8 (Z_to_bv 64 0)]).
    { eapply rw_cells_recell; [exact CAT | cbn; repeat split; exact Logic.I | vm_compute; reflexivity]. }
    clear CAT LCl T3b.
    rewrite (s32_id e He).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned tp, bv_unsigned tp + 256)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold PCAP_STRERROR_ENTRY. carve_frame 32%nat ST. do 10 step.
    name_sp sp (-32)%Z.
    call (strerror_r_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e 256 0x54520 z64 old lo);
      [ rewrite Hsp; exact ST | exact TLS | exact LOCP | exact CAT8 | assumption | reflexivity | exact He | reflexivity | lia | lia | lia
      | rewrite Hsp; lia | rewrite Hsp; lia | lia | lia | rewrite Hsp; lia | rewrite Hsp; lia | lia | ].
    rewrite Hsp in *. unname_sp. rename PC into ST. rename PC0 into RES. clear PC1 POST.
    step. if_true. do 6 step.
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    pose proof (strerror_msgb_length e) as ML. rewrite (strerror_tables_agree e He) in *. rewrite length_map in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with HB : rw_cells _ mm (bv_unsigned tp) ?cs |- _ =>
        pose proof (rw_cells_merge usegs mm (bv_unsigned tp) [] cs [] ltac:(rewrite app_nil_r; exact HB)) as TLS';
        cbn [cells_size csize cells_bytes cbytes Nat.add app] in TLS';
        replace (length (Fmt.strerror e) + 1 + (Z.to_nat 256 - (length (Fmt.strerror e) + 1) + 0))%nat with 256%nat in TLS' by lia
      end;
      assert (G' : GIo K R s CL FB mm)
        by (eapply (GIo_client_frame_tls K HFL SFL) with (W := [(bv_unsigned sp - 64, bv_unsigned sp)]%Z); [exact G | | exact WM | | unfold utp; rewrite <- TP; exact TLS'];
            [ eapply munch_weaken; [| exact MU]; intros a Ho; unfold utp in Ho; rewrite <- TP in Ho; cbn [outside] in *; tauto
            | apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil] ])
    end.
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [assumption|]. split; [assumption|].
    split. { eapply agrees_on_of_munch; [exact MU | exact WM |]. intros a _ [Ha|Ha]; cbn [outside]; [lia|].
             destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _].
             apply in_block_In in Ha as (b & HbIn & Hb).
             destruct (GIo_block_ok K _ _ _ _ _ b G ltac:(apply in_or_app; left; exact HbIn)) as (K1 & K2 & K3 & K4 & K5 & K6).
             unfold utp in K6. rewrite <- TP in K6. lia. }
    split; [exact G'|].
    replace (Z.to_nat 256 - (length (Fmt.strerror e) + 1))%nat with (255 - length (Fmt.strerror e))%nat in RES by lia.
    exact RES.
  Qed.
  End Sz4.
  Theorem pcap_strerror_proof : ltac:(let t := eval cbv delta [pcap_strerror_proof__stmt] in pcap_strerror_proof__stmt in exact t).
  Proof using HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo e. ltac2:(SecDiet.SzSec.closeP 'pcap_strerror_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Err.


End WithCeil.
End TwB.
End F_pcap_err.

(* [comment removed for export] *)
Module F_pcap_close.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.
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
Section Close.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  (* [comment removed for export] *)
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FREE : free_stmt_o HO K.

  Definition sf_cleanup_proof__stmt : Prop := sf_cleanup_stmt HO K sites.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc FB1 FB2 lo P B Af p j : ltac2:(SecDiet.SzSec.tyM 'sf_cleanup_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma sf_cleanup_proof__body : ltac2:(SecDiet.SzSec.bodyP 'sf_cleanup_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FCLOSE FREE HFL SFL. pin_using (fun (FCLOSE FREE HFL SFL : unit) => tt).
    intros PRE CELLS -> NOF.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(right; left; reflexivity)) as (R1 & R2 & R3 & R4 & R5 & R6).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as (A1 & _ & _ & A4 & A5 & _).
    cbn [cb_addr cb_size fst snd] in A1, A4, A5. unfold FILE_BLOCK in A4, A5.
    pose proof (GIo_core_misc K _ _ _ _ _ G) as (_ & _ & GOT1 & GOT2 & _).
    pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold pcap_cells in CELLS. apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    unfold pc_pre, PCAP_PRIV_OFF in CA. unfold hdr_cells in CH. unfold pc_ops in CO.
    unfold Pcap.pcapint_sf_cleanup. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fclose e_free prims]. unfold PK; cbn [pk_cleanup_sf].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    ienter.
    carve_frame 16%nat ST.
    do 9 step. if_false_by (eqb_lits_false Af 0x23750 ltac:(lia) ltac:(lia) ltac:(lia)). step.
    (* [comment removed for export] *)
    assert (KP : forall (CL : list cblock) SP mA mB A cs, In (pc_self p, P, psize p) CL -> agrees_on (client_keeps CL SP) mA mB ->
              rw_cells ssegs mA A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + psize p)%Z -> rw_cells ssegs mB A cs).
    { intros CL SP mA mB A cs Hin AG HC HA HB. eapply keeps_rw_cells_block; [exact AG | exact HC |].
      intros a Ha. apply in_block_In. exists (pc_self p, P, psize p). split; [exact Hin| cbn [cb_addr cb_size fst snd]; lia]. }
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)])) by (apply in_or_app; right; left; reflexivity).
    assert (HinP' : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p)])) by (apply in_or_app; right; left; reflexivity).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv R [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) [(bv_unsigned sp + -16, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (G0 : GIo K R s (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) (FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2) mm)
        by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps CLc (bv_unsigned sp)) m mm)
        by (eapply (keeps_of_pcap_writes K); [exact G | exact MU | exact WM | | unfold rc_lo; lia];
            apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil])
    end.
    clear MU WM.
    name_sp sp (-16)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply FCLOSE; [|reflexivity| exact NOF].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
    intros [] s' ms' PO. cbv beta in PO. destruct PO as (av1 & m2 & E & OF1 & MI1 & ST1 & AG1 & G1).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 82360)) with (Z_to_bv 64 82360) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CA; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CE; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CH; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CO; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear MI.
    (* [comment removed for export] *)
    ienter. step. step. if_false_by (eqz_false B ltac:(lia)). step.
    replace (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) with ((CLc ++ [(pc_self p, P, psize p)]) ++ [(pc_buffer p, B, pc_bufalloc p)]) in G1
      by (rewrite <- app_assoc; reflexivity).
    name_sp sp (-16)%Z.
    apply evt_done. eapply (implM_post_evt ssegs).
    { eapply FREE; [|reflexivity].
      split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
    intros [] s'' ms'' PO. cbv beta in PO. destruct PO as (av2 & m3 & E & OF2 & MI2 & ST2 & AG2 & G2).
    unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 82372)) with (Z_to_bv 64 82372) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite app_nil_r in AG2, G2.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CA; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CE; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CH; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CO; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear MI1.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P + 200, P + 204)]%Z m3) as MU3. pose proof (wmono_refl ssegs m3) as WM3.
    do 5 step.
    release_frame FR ST2 (bv_unsigned sp).
    unfold PCAP_FREECODE_ENTRY.
    call (pcap_freecode_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo P B p (C8 (Z_to_bv 64 Af)) j);
      [exact ST2 | lia | unfold rc_lo in LO; lia | assumption | reflexivity | reflexivity | lia | lia | exact P2 | exact CA |].
    (* [comment removed for export] *)
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps (CLc ++ CL) (bv_unsigned sp + -16)) mA mB ->
                 agrees_on (client_keeps CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha]. }
    apply WK in AG1. apply WK in AG2. clear WK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AG3 : agrees_on (client_keeps CLc (bv_unsigned sp)) m3 mm)
        by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 |]; intros a _ [Ha|Ha]; cbn [outside]; [unfold rc_lo in LO; lia|];
            destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G Ha) as [Hc Hnb]; split; [lia|]; split; [|exact I];
            intros Hin; apply Hnb; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia);
      assert (FW3 : Forall (pcap_iv R [(pc_self p, P, psize p)]) [(bv_unsigned sp - 16, bv_unsigned sp); (P + 200, P + 204)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|];
            apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| apply Forall_nil]);
      lazymatch goal with HCA : rw_cells _ mm P (pc_pre _ _ _ _ ?jj) |- _ =>
        pose proof (pcap_cells_join4 mm P p B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jj _ (pc_header p)
                      eq_refl HCA CE eq_refl CH CO) as J;
        replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity)
      end;
      apply evt_done; subst POSTQ0 POSTQ; unfold cleanup_post
    end.
    lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ ?av _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _] =>
      lazymatch type of J with rw_cells _ _ _ (pcap_cells_gen _ _ _ _ _ _ ?jj) => exists av, mm, jj end end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [rewrite OF2; exact OF1|]. split; [assumption|]. split; [assumption|].
    split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans; [exact AG1|]. eapply agrees_on_trans; [exact AG2| exact AG3]. }
    split. { eapply (GIo_pcap_frame K HFL SFL); [exact G2 | exact MU3 | exact WM3 | exact FW3]. }
    exact J.
  Qed.
  End Sz1.
  Theorem sf_cleanup_proof : ltac:(let t := eval cbv delta [sf_cleanup_proof__stmt] in sf_cleanup_proof__stmt in exact t).
  Proof using FCLOSE FREE HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc FB1 FB2 lo P B Af p j. ltac2:(SecDiet.SzSec.closeP 'sf_cleanup_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition ng_cleanup_proof__stmt : Prop := ng_cleanup_stmt HO K sites.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p : ltac2:(SecDiet.SzSec.tyM 'ng_cleanup_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ng_cleanup_proof__body : ltac2:(SecDiet.SzSec.bodyP 'ng_cleanup_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FCLOSE FREE HFL SFL. pin_using (fun (FCLOSE FREE HFL SFL : unit) => tt).
    intros PRE PC NG -> NOF.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (in_split _ _ HinF) as (FB1 & FB2 & EFB).
    (* [comment removed for export] *)
    unfold is_ng in NG. unfold priv_cells in PRIV. unfold ifaces_closable in IFS. unfold pcap_blocks in EPB.
    destruct (pc_priv p) as [sf|sg oq] eqn:EP; [discriminate NG|]. clear NG. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    (* [comment removed for export] *)
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
    clear BUF PFX.
    unfold Pcap.pcap_ng_cleanup, ng_ifaces_ptr_of. rewrite EP. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims]. unfold PK; cbn [pk_cleanup_ng].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    assert (KP : forall (CL : list cblock) SP mA mB A cs, In (pc_self p, P, psize p) CL -> agrees_on (client_keeps CL SP) mA mB ->
              rw_cells ssegs mA A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + psize p)%Z -> rw_cells ssegs mB A cs).
    { intros CL SP mA mB A cs Hin AG HC HA HB. eapply keeps_rw_cells_block; [exact AG | exact HC |].
      intros a Ha. apply in_block_In. exists (pc_self p, P, psize p). split; [exact Hin| cbn [cb_addr cb_size fst snd]; lia]. }
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)])) by (apply in_or_app; right; left; reflexivity).
    ienter.
    carve_frame 16%nat ST.
    do 7 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv R PB) [(bv_unsigned sp + -16, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (G0 : GIo K R s (CLc ++ PB) FB mm) by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps CLc (bv_unsigned sp)) m mm)
        by (eapply (keeps_of_pcap_writes K); [exact G | exact MU | exact WM | | unfold rc_lo; lia];
            apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil])
    end.
    clear MU WM.
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps (CLc ++ CL) (bv_unsigned sp + -16)) mA mB ->
                 agrees_on (client_keeps CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha]. }
    (* [comment removed for export] *)
    assert (CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) (ps2 : PState H hptr),
      mem_inv ssegs m2 -> stk ssegs m2 lo (bv_unsigned sp + -16) -> agrees_on (client_keeps CLc (bv_unsigned sp)) m m2 ->
      GIo K R ps2 (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) FB m2 ->
      rw_cells ssegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> rw_cells ssegs m2 P (pcap_cells p P B Af j) -> ps_outfile ps2 = ps_outfile s ->
      implM ssegs (pcapint_sf_cleanup MOps (prims HO fo_nop sites) p) ps2 POSTQ
        (MS (mkR (Z_to_bv 64 0x17b04) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0' t1' t2' (Z_to_bv 64 P) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x17b04) fc None m2 (seg_rom ssegs))).
    { intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 MI2 ST2 AG2 G2 FR2 CELLS2 OF2.
      clear CELLS PRIV FR G0 AGa MI G IFS.
      unfold implM. iprefix. do 5 step.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. eapply (implM_mono ssegs).
      { eapply sf_cleanup_proof; [| exact CELLS2 | reflexivity | rewrite OF2; exact NOF].
        split; [rewrite EFB in G2; exact G2|]. split; [exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L3_STACK; lia|].
        split; [lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
      cbv beta. intros [] ps3 ms3 PO. subst POSTQ. exists B, Af, FB1, FB2. split; [exact EFB|].
      unfold cleanup_post in *. destruct PO as (a0v & m' & j' & E & OF' & MI' & ST' & AG' & G' & HC').
      exists a0v, m', j'. split; [exact E|]. split; [rewrite OF'; exact OF2|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply agrees_on_trans; [exact AG2| exact AG']|]. split; [exact G'| exact HC']. }
    (* [comment removed for export] *)
    destruct oq as [q|].
    - pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
      rewrite EPB in G0.
      replace (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p); (q, I, 40 * ng_ifaces_size sg)%Z])
        with ((CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) ++ [(q, I, 40 * ng_ifaces_size sg)%Z]) in G0
        by (rewrite <- app_assoc; reflexivity).
      name_sp sp (-16)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply FREE; [|reflexivity].
        split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
      intros [] s' ms' PO. cbv beta in PO. destruct PO as (av1 & m2 & E & OF1 & MI1 & ST1 & AG1 & G1).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x17b04)) with (Z_to_bv 64 0x17b04) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite app_nil_r in AG1, G1.
      apply CONT; [exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK _ _ _ AG1)] | exact G1
            | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | eapply KP; [exact HinP | exact AG1 | exact CELLS | lia | rewrite pcap_cells_size; lia] | exact OF1 ].
    - rewrite IFS in *. rewrite EPB in G0.
      unfold FREE_ENTRY. step. step. if_true. step.
      apply evt_done. apply CONT; [assumption | exact ST | exact AGa | exact G0 | exact FR | exact CELLS | reflexivity].
  Qed.
  End Sz2.
  Theorem ng_cleanup_proof : ltac:(let t := eval cbv delta [ng_cleanup_proof__stmt] in ng_cleanup_proof__stmt in exact t).
  Proof using FCLOSE FREE HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p. ltac2:(SecDiet.SzSec.closeP 'ng_cleanup_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition pcap_close_proof__stmt : Prop := pcap_close_stmt HO K sites.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p : ltac2:(SecDiet.SzSec.tyM 'pcap_close_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_close_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_close_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FCLOSE FREE HFL SFL. pin_using (fun (FCLOSE FREE HFL SFL : unit) => tt).
    intros PRE PC -> NOF.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L4_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (in_split _ _ HinF) as (FB1 & FB2 & EFB).
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
    clear PRIV BUF PFX IFS.
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p)])) by (apply in_or_app; right; left; reflexivity).
    unfold Pcap.pcap_close. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims]. unfold PCAP_CLOSE_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    ienter.
    (* [comment removed for export] *)
    assert (CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) (ps2 : PState H hptr) FB1' FB2' Af' B' j',
      FB = FB1' ++ (pc_rfile p, Af', FILE_BLOCK) :: FB2' ->
      mem_inv ssegs m2 -> stk ssegs m2 lo (bv_unsigned sp + -16) -> agrees_on (client_keeps CLc (bv_unsigned sp)) m m2 ->
      GIo K R ps2 (CLc ++ [(pc_self p, P, psize p)]) (FB1' ++ FB2') m2 ->
      rw_cells ssegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> rw_cells ssegs m2 P (pcap_cells p P B' Af' j') -> ps_outfile ps2 = ps_outfile s ->
      implM ssegs (pfree HO (pc_self p)) ps2 POSTQ
        (MS (mkR (Z_to_bv 64 0x1473c) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0' t1' t2' (Z_to_bv 64 P) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1473c) fc None m2 (seg_rom ssegs))).
    { intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 FB1' FB2' Af' B' j' EFB' MI2 ST2 AG2 G2 FR2 CELLS2 OF2.
      clear CELLS MU WM MI G ST.
      unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS2. cbn [app] in CELLS2.
      unfold implM. iprefix. step. step. if_true. do 5 step.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. eapply (implM_mono ssegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CLc []); [|reflexivity].
        split; [exact G2|]. split; [exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; lia|].
        split; [lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
      cbv beta. intros [] ps3 ms3 PO. subst POSTQ. unfold pcap_post.
      destruct PO as (a0v & m' & E & OF' & MI' & ST' & AG' & G'). rewrite app_nil_r in AG'.
      exists a0v, m', [], (FB1' ++ FB2'). split; [exact E|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply agrees_on_trans; [exact AG2| exact AG']|]. split; [exact G'|]. split; [rewrite OF'; exact OF2|]. split; [reflexivity|].
      exists FB1', FB2', Af'. split; [exact EFB'| reflexivity]. }
    carve_frame 16%nat ST.
    do 6 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv R PB) [(bv_unsigned sp + -16, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (G0 : GIo K R s (CLc ++ PB) FB mm) by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM | exact FW]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp + -16, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (PC0 : PCAPR_closable P p PB FB mm)
        by (eapply PCAPR_closable_agree; [exact AG0 | intros a Ha; pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha); cbn [outside]; unfold rc_lo in *; lia | exact PC]);
      assert (AGa : agrees_on (client_keeps CLc (bv_unsigned sp)) m mm)
        by (eapply (keeps_of_pcap_writes K); [exact G | exact MU | exact WM | | unfold rc_lo; lia];
            apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil])
    end.
    clear MU WM AG0.
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps (CLc ++ CL) (bv_unsigned sp + -16)) mA mB ->
                 agrees_on (client_keeps CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha]. }
    (* [comment removed for export] *)
    unfold pcap_blocks in EPB. unfold cleanup_entry, is_ng, PK. cbn [pk_cleanup_ng pk_cleanup_sf].
    destruct (pc_priv p) as [sf|sg oq] eqn:EP.
    - (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 82320)) with (Z_to_bv 64 (pk_cleanup_sf PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
      rewrite EPB, EFB in G0.
      name_sp sp (-16)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply sf_cleanup_proof; [| exact CELLS | reflexivity | exact NOF].
        split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
      intros [] s' ms' PO. unfold cleanup_post in PO. destruct PO as (av1 & m2 & j' & E & OF1 & MI1 & ST1 & AG1 & G1 & HC1).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x1473c)) with (Z_to_bv 64 0x1473c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      eapply CONT; [exact EFB | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK []); rewrite app_nil_r; exact AG1] | exact G1
             | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | exact HC1 | exact OF1].
    - (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 97000)) with (Z_to_bv 64 (pk_cleanup_ng PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
      name_sp sp (-16)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply ng_cleanup_proof; [| exact PC0 | unfold is_ng; rewrite EP; reflexivity | reflexivity | exact NOF].
        split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
      intros [] s' ms' PO. cbv beta in PO. destruct PO as (B' & Af' & FB1' & FB2' & EFB' & PO). unfold cleanup_post in PO.
      destruct PO as (av1 & m2 & j' & E & OF1 & MI1 & ST1 & AG1 & G1 & HC1).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x1473c)) with (Z_to_bv 64 0x1473c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      eapply CONT; [exact EFB' | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK []); rewrite app_nil_r; exact AG1] | exact G1
             | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | exact HC1 | exact OF1].
  Qed.
  End Sz3.
  Theorem pcap_close_proof : ltac:(let t := eval cbv delta [pcap_close_proof__stmt] in pcap_close_proof__stmt in exact t).
  Proof using FCLOSE FREE HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p. ltac2:(SecDiet.SzSec.closeP 'pcap_close_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Close.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB.
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
Section Close.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  (* [comment removed for export] *)
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FREE : free_stmt_o HO K.

  Definition sf_cleanup_proof__stmt : Prop := sf_cleanup_stmt HO K sites.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc FB1 FB2 lo P B Af p j : ltac2:(SecDiet.SzSec.tyM 'sf_cleanup_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma sf_cleanup_proof__body : ltac2:(SecDiet.SzSec.bodyP 'sf_cleanup_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FCLOSE FREE HFL SFL. pin_using (fun (FCLOSE FREE HFL SFL : unit) => tt).
 intros PRE CELLS -> NOF.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(right; left; reflexivity)) as (R1 & R2 & R3 & R4 & R5 & R6).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as (A1 & _ & _ & A4 & A5 & _).
    cbn [cb_addr cb_size fst snd] in A1, A4, A5. unfold FILE_BLOCK in A4, A5.
    pose proof (GIo_core_misc K _ _ _ _ _ G) as (_ & _ & GOT1 & GOT2 & _).
    pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold pcap_cells in CELLS. apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    unfold pc_pre, PCAP_PRIV_OFF in CA. unfold hdr_cells in CH. unfold pc_ops in CO.
    unfold Pcap.pcapint_sf_cleanup. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fclose e_free prims]. unfold PK; cbn [pk_cleanup_sf].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    ienter.
    carve_frame 16%nat ST.
    assert (P8 : (P mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r P); apply aligned16_8; [exact P2| reflexivity]).
    do 4 step. if_false_by (eqz_false P ltac:(lia)). do 2 step. rewrite (and7_aligned P) by lia. step. if_false.
    do 5 step. if_false_by (eqb_lits_false Af 0x23f10 ltac:(lia) ltac:(lia) ltac:(lia)). step.
    (* [comment removed for export] *)
    assert (KP : forall (CL : list cblock) SP mA mB A cs, In (pc_self p, P, psize p) CL -> agrees_on (client_keeps CL SP) mA mB ->
              rw_cells usegs mA A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + psize p)%Z -> rw_cells usegs mB A cs).
    { intros CL SP mA mB A cs Hin AG HC HA HB. eapply keeps_rw_cells_block; [exact AG | exact HC |].
      intros a Ha. apply in_block_In. exists (pc_self p, P, psize p). split; [exact Hin| cbn [cb_addr cb_size fst snd]; lia]. }
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)])) by (apply in_or_app; right; left; reflexivity).
    assert (HinP' : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p)])) by (apply in_or_app; right; left; reflexivity).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv R [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) [(bv_unsigned sp + -16, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (G0 : GIo K R s (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) (FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2) mm)
        by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps CLc (bv_unsigned sp)) m mm)
        by (eapply (keeps_of_pcap_writes K); [exact G | exact MU | exact WM | | unfold rc_lo; lia];
            apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil])
    end.
    clear MU WM.
    name_sp sp (-16)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { eapply FCLOSE; [|reflexivity| exact NOF].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
    intros [] s' ms' PO. cbv beta in PO. destruct PO as (av1 & m2 & E & OF1 & MI1 & ST1 & AG1 & G1).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 82528)) with (Z_to_bv 64 82528) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CA; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CE; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CH; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP AG1) in CO; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear MI.
    (* [comment removed for export] *)
    ienter. step. step. if_false_by (eqz_false B ltac:(lia)). step.
    replace (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) with ((CLc ++ [(pc_self p, P, psize p)]) ++ [(pc_buffer p, B, pc_bufalloc p)]) in G1
      by (rewrite <- app_assoc; reflexivity).
    name_sp sp (-16)%Z.
    apply evt_done. eapply (implM_post_evt usegs).
    { eapply FREE; [|reflexivity].
      split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
    intros [] s'' ms'' PO. cbv beta in PO. destruct PO as (av2 & m3 & E & OF2 & MI2 & ST2 & AG2 & G2).
    unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 82540)) with (Z_to_bv 64 82540) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite app_nil_r in AG2, G2.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG2) in FR; [|lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CA; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CE; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CH; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (KP _ _ _ _ _ _ HinP' AG2) in CO; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear MI1.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P + 200, P + 204)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
    do 5 step.
    release_frame FR ST2 (bv_unsigned sp).
    unfold PCAP_FREECODE_ENTRY.
    call (pcap_freecode_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo P B p (C8 (Z_to_bv 64 Af)) j);
      [exact ST2 | lia | unfold rc_lo in LO; lia | assumption | reflexivity | reflexivity | lia | lia | exact P2 | exact CA |].
    (* [comment removed for export] *)
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps (CLc ++ CL) (bv_unsigned sp + -16)) mA mB ->
                 agrees_on (client_keeps CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha]. }
    apply WK in AG1. apply WK in AG2. clear WK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AG3 : agrees_on (client_keeps CLc (bv_unsigned sp)) m3 mm)
        by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 |]; intros a _ [Ha|Ha]; cbn [outside]; [unfold rc_lo in LO; lia|];
            destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G Ha) as [Hc Hnb]; split; [lia|]; split; [|exact I];
            intros Hin; apply Hnb; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia);
      assert (FW3 : Forall (pcap_iv R [(pc_self p, P, psize p)]) [(bv_unsigned sp - 16, bv_unsigned sp); (P + 200, P + 204)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|];
            apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| apply Forall_nil]);
      lazymatch goal with HCA : rw_cells _ mm P (pc_pre _ _ _ _ ?jj) |- _ =>
        pose proof (pcap_cells_join4 mm P p B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jj _ (pc_header p)
                      eq_refl HCA CE eq_refl CH CO) as J;
        replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity)
      end;
      apply evt_done; subst POSTQ0 POSTQ; unfold cleanup_post
    end.
    lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ ?av _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _] =>
      lazymatch type of J with rw_cells _ _ _ (pcap_cells_gen _ _ _ _ _ _ ?jj) => exists av, mm, jj end end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [rewrite OF2; exact OF1|]. split; [assumption|]. split; [assumption|].
    split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans; [exact AG1|]. eapply agrees_on_trans; [exact AG2| exact AG3]. }
    split. { eapply (GIo_pcap_frame K HFL SFL); [exact G2 | exact MU3 | exact WM3 | exact FW3]. }
    exact J.
  Qed.
  End Sz1.
  Theorem sf_cleanup_proof : ltac:(let t := eval cbv delta [sf_cleanup_proof__stmt] in sf_cleanup_proof__stmt in exact t).
  Proof using FCLOSE FREE HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc FB1 FB2 lo P B Af p j. ltac2:(SecDiet.SzSec.closeP 'sf_cleanup_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition ng_cleanup_proof__stmt : Prop := ng_cleanup_stmt HO K sites.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p : ltac2:(SecDiet.SzSec.tyM 'ng_cleanup_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ng_cleanup_proof__body : ltac2:(SecDiet.SzSec.bodyP 'ng_cleanup_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FCLOSE FREE HFL SFL. pin_using (fun (FCLOSE FREE HFL SFL : unit) => tt).
 intros PRE PC NG -> NOF.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (in_split _ _ HinF) as (FB1 & FB2 & EFB).
    (* [comment removed for export] *)
    unfold is_ng in NG. unfold priv_cells in PRIV. unfold ifaces_closable in IFS. unfold pcap_blocks in EPB.
    destruct (pc_priv p) as [sf|sg oq] eqn:EP; [discriminate NG|]. clear NG. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    (* [comment removed for export] *)
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
    clear BUF PFX.
    unfold Pcap.pcap_ng_cleanup, ng_ifaces_ptr_of. rewrite EP. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims]. unfold PK; cbn [pk_cleanup_ng].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (KP : forall (CL : list cblock) SP mA mB A cs, In (pc_self p, P, psize p) CL -> agrees_on (client_keeps CL SP) mA mB ->
              rw_cells usegs mA A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + psize p)%Z -> rw_cells usegs mB A cs).
    { intros CL SP mA mB A cs Hin AG HC HA HB. eapply keeps_rw_cells_block; [exact AG | exact HC |].
      intros a Ha. apply in_block_In. exists (pc_self p, P, psize p). split; [exact Hin| cbn [cb_addr cb_size fst snd]; lia]. }
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)])) by (apply in_or_app; right; left; reflexivity).
    ienter.
    carve_frame 16%nat ST.
    assert (P8 : (P mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r P); apply aligned16_8; [exact P2| reflexivity]).
    assert (P648 : ((P + 648) mod 8 = 0)%Z) by (apply aligned16_8; [exact P2| reflexivity]).
    do 4 step. if_false_by (eqz_false P ltac:(lia)). do 2 step. rewrite (and7_aligned P) by lia. step. if_false.
    do 2 step. if_false_by (eqz_false (P + 648) ltac:(lia)). step. rewrite (and7_aligned (P + 648)) by lia. step. if_false.
    do 2 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv R PB) [(bv_unsigned sp + -16, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (G0 : GIo K R s (CLc ++ PB) FB mm) by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps CLc (bv_unsigned sp)) m mm)
        by (eapply (keeps_of_pcap_writes K); [exact G | exact MU | exact WM | | unfold rc_lo; lia];
            apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil])
    end.
    clear MU WM.
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps (CLc ++ CL) (bv_unsigned sp + -16)) mA mB ->
                 agrees_on (client_keeps CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha]. }
    (* [comment removed for export] *)
    assert (CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) (ps2 : PState H hptr),
      mem_inv usegs m2 -> stk usegs m2 lo (bv_unsigned sp + -16) -> agrees_on (client_keeps CLc (bv_unsigned sp)) m m2 ->
      GIo K R ps2 (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) FB m2 ->
      rw_cells usegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> rw_cells usegs m2 P (pcap_cells p P B Af j) -> ps_outfile ps2 = ps_outfile s ->
      implM usegs (pcapint_sf_cleanup MOps (prims HO fo_nop sites) p) ps2 POSTQ
        (MS (mkR (Z_to_bv 64 0x182c0) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0' t1' t2' (Z_to_bv 64 P) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x182c0) fc None m2 (seg_rom usegs))).
    { intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 MI2 ST2 AG2 G2 FR2 CELLS2 OF2.
      clear CELLS PRIV FR G0 AGa MI G IFS.
      unfold implM. iprefix. do 5 step.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. eapply (implM_mono usegs).
      { eapply sf_cleanup_proof; [| exact CELLS2 | reflexivity | rewrite OF2; exact NOF].
        split; [rewrite EFB in G2; exact G2|]. split; [exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L3_STACK; lia|].
        split; [lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
      cbv beta. intros [] ps3 ms3 PO. subst POSTQ. exists B, Af, FB1, FB2. split; [exact EFB|].
      unfold cleanup_post in *. destruct PO as (a0v & m' & j' & E & OF' & MI' & ST' & AG' & G' & HC').
      exists a0v, m', j'. split; [exact E|]. split; [rewrite OF'; exact OF2|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply agrees_on_trans; [exact AG2| exact AG']|]. split; [exact G'| exact HC']. }
    (* [comment removed for export] *)
    destruct oq as [q|].
    - pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
      rewrite EPB in G0.
      replace (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p); (q, I, 40 * ng_ifaces_size sg)%Z])
        with ((CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) ++ [(q, I, 40 * ng_ifaces_size sg)%Z]) in G0
        by (rewrite <- app_assoc; reflexivity).
      name_sp sp (-16)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply FREE; [|reflexivity].
        split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
      intros [] s' ms' PO. cbv beta in PO. destruct PO as (av1 & m2 & E & OF1 & MI1 & ST1 & AG1 & G1).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x182c0)) with (Z_to_bv 64 0x182c0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      rewrite app_nil_r in AG1, G1.
      apply CONT; [exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK _ _ _ AG1)] | exact G1
            | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | eapply KP; [exact HinP | exact AG1 | exact CELLS | lia | rewrite pcap_cells_size; lia] | exact OF1 ].
    - rewrite IFS in *. rewrite EPB in G0.
      unfold FREE_ENTRY. step. step. if_true. step.
      apply evt_done. apply CONT; [assumption | exact ST | exact AGa | exact G0 | exact FR | exact CELLS | reflexivity].
  Qed.
  End Sz2.
  Theorem ng_cleanup_proof : ltac:(let t := eval cbv delta [ng_cleanup_proof__stmt] in ng_cleanup_proof__stmt in exact t).
  Proof using FCLOSE FREE HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p. ltac2:(SecDiet.SzSec.closeP 'ng_cleanup_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition pcap_close_proof__stmt : Prop := pcap_close_stmt HO K sites.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p : ltac2:(SecDiet.SzSec.tyM 'pcap_close_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_close_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_close_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FCLOSE FREE HFL SFL. pin_using (fun (FCLOSE FREE HFL SFL : unit) => tt).
 intros PRE PC -> NOF.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    pose proof (psize_pos p) as PS. pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L4_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (in_split _ _ HinF) as (FB1 & FB2 & EFB).
    unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
    clear PRIV BUF PFX IFS.
    assert (HinP : In (pc_self p, P, psize p) (CLc ++ [(pc_self p, P, psize p)])) by (apply in_or_app; right; left; reflexivity).
    unfold Pcap.pcap_close. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims]. unfold PCAP_CLOSE_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    ienter.
    (* [comment removed for export] *)
    assert (CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) (ps2 : PState H hptr) FB1' FB2' Af' B' j',
      FB = FB1' ++ (pc_rfile p, Af', FILE_BLOCK) :: FB2' ->
      mem_inv usegs m2 -> stk usegs m2 lo (bv_unsigned sp + -16) -> agrees_on (client_keeps CLc (bv_unsigned sp)) m m2 ->
      GIo K R ps2 (CLc ++ [(pc_self p, P, psize p)]) (FB1' ++ FB2') m2 ->
      rw_cells usegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> rw_cells usegs m2 P (pcap_cells p P B' Af' j') -> ps_outfile ps2 = ps_outfile s ->
      implM usegs (pfree HO (pc_self p)) ps2 POSTQ
        (MS (mkR (Z_to_bv 64 0x148cc) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0' t1' t2' (Z_to_bv 64 P) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x148cc) fc None m2 (seg_rom usegs))).
    { intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 FB1' FB2' Af' B' j' EFB' MI2 ST2 AG2 G2 FR2 CELLS2 OF2.
      clear CELLS MU WM MI G ST.
      unfold pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS2. cbn [app] in CELLS2.
      unfold implM. iprefix. step. step. if_true. do 5 step.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. eapply (implM_mono usegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CLc []); [|reflexivity].
        split; [exact G2|]. split; [exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; lia|].
        split; [lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
      cbv beta. intros [] ps3 ms3 PO. subst POSTQ. unfold pcap_post.
      destruct PO as (a0v & m' & E & OF' & MI' & ST' & AG' & G'). rewrite app_nil_r in AG'.
      exists a0v, m', [], (FB1' ++ FB2'). split; [exact E|]. split; [exact MI'|]. split; [exact ST'|].
      split; [eapply agrees_on_trans; [exact AG2| exact AG']|]. split; [exact G'|]. split; [rewrite OF'; exact OF2|]. split; [reflexivity|].
      exists FB1', FB2', Af'. split; [exact EFB'| reflexivity]. }
    carve_frame 16%nat ST.
    assert (P8 : (P mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r P); apply aligned16_8; [exact P2| reflexivity]).
    do 4 step. if_false_by (eqz_false P ltac:(lia)). do 2 step. rewrite (and7_aligned P) by lia. step. if_false.
    do 3 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv R PB) [(bv_unsigned sp + -16, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (G0 : GIo K R s (CLc ++ PB) FB mm) by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM | exact FW]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp + -16, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (PC0 : PCAPR_closable P p PB FB mm)
        by (eapply PCAPR_closable_agree; [exact AG0 | intros a Ha; pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha); cbn [outside]; unfold rc_lo in *; lia | exact PC]);
      assert (AGa : agrees_on (client_keeps CLc (bv_unsigned sp)) m mm)
        by (eapply (keeps_of_pcap_writes K); [exact G | exact MU | exact WM | | unfold rc_lo; lia];
            apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil])
    end.
    clear MU WM AG0.
    assert (WK : forall (CL : list cblock) mA mB, agrees_on (client_keeps (CLc ++ CL) (bv_unsigned sp + -16)) mA mB ->
                 agrees_on (client_keeps CLc (bv_unsigned sp)) mA mB).
    { intros CL mA mB AG. eapply client_keeps_weaken; [exact AG | lia | intros a Ha; apply in_block_app; left; exact Ha]. }
    (* [comment removed for export] *)
    unfold pcap_blocks in EPB. unfold cleanup_entry, is_ng, PK. cbn [pk_cleanup_ng pk_cleanup_sf].
    destruct (pc_priv p) as [sf|sg oq] eqn:EP.
    - (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 82476)) with (Z_to_bv 64 (pk_cleanup_sf PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
      rewrite EPB, EFB in G0.
      name_sp sp (-16)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply sf_cleanup_proof; [| exact CELLS | reflexivity | exact NOF].
        split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
      intros [] s' ms' PO. unfold cleanup_post in PO. destruct PO as (av1 & m2 & j' & E & OF1 & MI1 & ST1 & AG1 & G1 & HC1).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x148cc)) with (Z_to_bv 64 0x148cc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      eapply CONT; [exact EFB | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK []); rewrite app_nil_r; exact AG1] | exact G1
             | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | exact HC1 | exact OF1].
    - (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 98956)) with (Z_to_bv 64 (pk_cleanup_ng PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
      name_sp sp (-16)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply ng_cleanup_proof; [| exact PC0 | unfold is_ng; rewrite EP; reflexivity | reflexivity | exact NOF].
        split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]; split; [exact TP| first [exact ALN | rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]]. }
      intros [] s' ms' PO. cbv beta in PO. destruct PO as (B' & Af' & FB1' & FB2' & EFB' & PO). unfold cleanup_post in PO.
      destruct PO as (av1 & m2 & j' & E & OF1 & MI1 & ST1 & AG1 & G1 & HC1).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x148cc)) with (Z_to_bv 64 0x148cc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      eapply CONT; [exact EFB' | exact MI1 | exact ST1 | eapply agrees_on_trans; [exact AGa| apply (WK []); rewrite app_nil_r; exact AG1] | exact G1
             | eapply keeps_rw_cells_stack; [exact AG1 | exact FR | lia] | exact HC1 | exact OF1].
  Qed.
  End Sz3.
  Theorem pcap_close_proof : ltac:(let t := eval cbv delta [pcap_close_proof__stmt] in pcap_close_proof__stmt in exact t).
  Proof using FCLOSE FREE HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P p. ltac2:(SecDiet.SzSec.closeP 'pcap_close_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Close.

End WithCeil.
End TwB.
End F_pcap_close.

(* [comment removed for export] *)
Module F_pcap_open.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.
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

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma implM_pure : forall {St A} (c : @M St A) s Q ms r s1,
  c s = Ret (Ok (r, s1)) -> evt ssegs (Q r s1) ms -> implM ssegs c s Q ms.
Proof using Type. pin_using tt. intros St A c s Q ms r s1 E H. unfold implM. rewrite E. cbn. exact H. Qed.

Definition fmt_errmsg_length__stmt : Prop := forall f args e, (length (fmt_errmsg f args e) <= 255)%nat.
Section Sz2.
Variables f args e : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_length__stmt "vvv" @f).
Lemma fmt_errmsg_length__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_length__stmt "vvv").
Proof using Type. pin_using tt.
 unfold fmt_errmsg, snprintf, snprintf_out, PCAP_ERRBUF_SIZE, zlength.
  set (mm := firstn (Z.to_nat (256 - 1)) (fmt_output (fmt f) args)).
  assert (Hm : (length mm <= 255)%nat) by (subst mm; rewrite length_firstn; apply Nat.le_min_l).
  destruct (256 <? Z.of_nat (length mm) + 3)%Z eqn:E; [exact Hm|].
  apply Z.ltb_ge in E. rewrite !length_app, length_firstn. cbn [length str String.list_ascii_of_string map]. 
  unfold str. cbn [String.list_ascii_of_string map length]. lia.
Qed.
End Sz2.
Lemma fmt_errmsg_length : ltac:(let t := eval cbv delta [fmt_errmsg_length__stmt] in fmt_errmsg_length__stmt in exact t).
Proof using Type. intros f args e. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_length__body "vvv"). Qed.

Section Open.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis CALLOC : calloc_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.

  Definition open_offline_common_proof__stmt : Prop := open_offline_common_stmt HO K sites.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo EB total ej : ltac2:(SecDiet.SzSec.tyM 'open_offline_common_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma open_offline_common_proof__body : ltac2:(SecDiet.SzSec.bodyP 'open_offline_common_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CALLOC FMT HFL SFL. pin_using (fun (CALLOC FMT HFL SFL : unit) => tt).
    intros PRE -> -> -> Htot HEB CR E8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L1B_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    assert (TOT : 0 <= total < 2^32) by (unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in Htot; lia).
    assert (EBX : EB + 256 <= CEILZ \/ bv_unsigned sp <= EB).
    { destruct CR as [Hb|Hs]; [|right; lia]. left.
      destruct (GIo_CLc_facts K R s CL [] FB m (EB + 255) ltac:(rewrite app_nil_r; exact G) ltac:(apply Hb; lia)) as [Hc _]. lia. }
    unfold Pcap.pcapint_open_offline_common, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_calloc e_last_errno prims]. unfold PCAP_OPEN_OFFLINE_COMMON_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    hide HEB.
    ienter. carve_frame 32%nat ST. do 10 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R s CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AGa : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|Ha] Hn]; cbn [outside]; [lia|];
            destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; lia);
      unhide HEB; assert (HEB1 : rw_cells ssegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia])
    end.
    clear MU WM HEB.
    name_sp sp (-32)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply CALLOC; [| reflexivity | reflexivity | lia | lia | unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in Htot; lia].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    intros [q|] s' ms' PO; cbv beta iota in PO.
    - (* [comment removed for export] *)
      destruct PO as (av & m2 & E & OF1 & MI1 & ST1 & AG1 & (A & -> & G1 & NEW)).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      rewrite Z.mul_1_r in G1, NEW.
      pose proof (GIo_block_ok K _ _ _ _ _ _ G1 ltac:(left; reflexivity)) as (A1 & A2 & A3 & A4 & A5 & A6). cbn [cb_addr cb_size fst snd] in A1, A2, A3, A4, A5, A6.
      replace (ret_pc (Z_to_bv 64 83848)) with (Z_to_bv 64 83848) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (HEB2 : rw_cells ssegs m2 EB [CB 256 ej]).
      { eapply agrees_rw_cells; [exact AG1 | exact HEB1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
        destruct CR as [Hb|Hs]; [right; apply Hb; lia | left; lia]. }
      clear HEB1.
      assert (NB : forall a, in_block CL a -> ~ (A <= a < A + total)).
      { intros a Ha Hin. destruct (GIo_CLc_facts K R s' [(q, A, total)] CL FB m2 a G1 ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Hin)) as [_ Hn].
        exact (Hn Ha). }
      pose proof (munch_refl [(A, A + 200)]%Z m2) as MU2. pose proof (wmono_refl ssegs m2) as WM2.   (* [comment removed for export] *)
      unfold PCAP_PRIV_OFF. apply (implM_ret ssegs). hide HEB2.
      destruct Htot as [-> | ->]; unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in *.
      all: lazymatch type of NEW with context [Z.to_nat ?z] => let n := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with n in NEW end.
      (* [comment removed for export] *)
      all: let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 664); change (repeat (Z_to_bv 8 0) 664) with z in NEW.
      all: let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 680); change (repeat (Z_to_bv 8 0) 680) with z in NEW.
      all: step; if_false_by (eqz_false A ltac:(lia)); do 12 step.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      all: lazymatch type of NEW with rw_cells _ ?mm ?AA [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10] =>
             pose proof (rw_cells_merge ssegs mm AA [c0; c1; c2; c3] [c4; c5; c6] [c7; c8; c9; c10] NEW) as NEW2;
             cbn [cells_size csize cells_bytes cbytes app Nat.add] in NEW2 end.
      all: lazymatch type of NEW2 with rw_cells _ ?mm ?AA [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
             pose proof (rw_cells_merge ssegs mm AA [c0; c1; c2; c3; c4; c5] [c6; c7; c8] [] NEW2) as NEW3;
             cbn [cells_size csize cells_bytes cbytes app Nat.add] in NEW3 end.
      all: clear NEW NEW2.
      all: release_frame FR ST1 (bv_unsigned sp).
      all: apply evt_done; subst POSTQ; unfold open_common_post.
      all: lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 A), mm end.
      all: split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      all: split; [solve [assumption | congruence] |].
      all: split; [assumption|]; split; [assumption|].
      all: split; [eapply agrees_on_trans; [exact AGa|]; eapply agrees_on_trans;
                    [eapply agrees_on_weaken; [exact AG1|]; intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha]
                    |eapply agrees_on_of_munch; [exact MU2 | exact WM2|]; intros a _ [[Ha|Ha] Hn]; cbn [outside]; [unfold rc_lo in LO; lia|];
                     split; [|exact I]; intros Hin; apply (NB a Ha); lia]|].
      all: exists A; split; [reflexivity|].
      all: split; [eapply (GIo_client_frame K HFL SFL); [exact G1 | exact MU2 | exact WM2|];
                   apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| apply Forall_nil]|].
      all: unhide HEB2.
      all: split; [| eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU2| exact WM2| intros a _ Ho; exact Ho] | exact HEB2 |];
                    intros a Ha; cbn [outside cells_size csize Nat.add] in *; split; [|exact I];
                    destruct CR as [Hb|Hs]; [intros Hin; apply (NB a ltac:(apply Hb; lia)); lia | lia]].
      all: assumption.
    - (* [comment removed for export] *)
      destruct PO as (av & m2 & E & OF1 & MI1 & ST1 & AG1 & -> & G1 & EN1 & EN2).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 83848)) with (Z_to_bv 64 83848) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (HEB2 : rw_cells ssegs m2 EB [CB 256 ej]).
      { eapply agrees_rw_cells; [exact AG1 | exact HEB1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
        destruct CR as [Hb|Hs]; [right; apply Hb; lia | left; lia]. }
      clear HEB1.
      pose proof (GIo_tls K _ _ _ _ _ G1) as [_ TB]. unfold tls_block_ok in TB.
      unfold utp in EN2. rewrite <- TP in EN2.
      eapply implM_pure; [reflexivity|]. cbn [fst snd]. rewrite EN1.
      step. if_true. do 11 step.
      replace (sx32 (Z_to_bv 64 12)) with (Z_to_bv 64 (s32 12)) by (unfold sx32; rewrite unsigned_lit by lia; reflexivity).
      assert (MSG : fmt_at m2 0x108ae "malloc"%string).
      { split; [|cbn; lia]. pose proof (ro_cells_image ssegs m2 0x108ae (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "malloc"%string) ++ [Z_to_bv 8 0])
                                 MI1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
        exact (ro_cells_bytes_at _ _ _ _ RO). }
      name_sp sp (-32)%Z.
      eapply evt_cut.
      { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 0x108ae%Z 12%Z "malloc"%string [] ej);
          [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB2
           | destruct CR as [Hb|Hs]; [left; exact Hb | right; rewrite Hsp; lia] | exact E8 ].
        split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m3 & junk' & -> & MI3 & ST3 & AG3 & G3 & HEB3).
      rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 83932)) with (Z_to_bv 64 83932) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      assert (FR3 : rw_cells ssegs m3 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 s1; C8 s0; C8 ra]).
      { eapply agrees_rw_cells; [exact AG3 | exact FR |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| lia]. }
      clear FR MI1.
      do 6 step.
      release_frame FR3 ST3 (bv_unsigned sp).
      apply evt_done; subst POSTQ; unfold open_common_post.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [solve [assumption | congruence] |].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans.
               - eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha].
               - eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] Hn]; (split; [|exact Hn]); [left; lia| right; exact Ha]. }
      exists junk'. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB3|].
      split; [pose proof (fmt_errmsg_length "malloc"%string [] 12); lia|].
      apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor].
  Qed.
  End Sz3.
  Theorem open_offline_common_proof : ltac:(let t := eval cbv delta [open_offline_common_proof__stmt] in open_offline_common_proof__stmt in exact t).
  Proof using CALLOC FMT HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo EB total ej. ltac2:(SecDiet.SzSec.closeP 'open_offline_common_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FOPEN_OFFLINE : fopen_offline_stmt HO K sites.

  Lemma cstr_no_nul : forall (bs : list byte), ~ In (Z_to_bv 8 0) bs -> cstr (map bv_unsigned bs) = map bv_unsigned bs.
  Proof using Type. pin_using tt.
    induction bs as [|b bs IH]; intros Hn; [reflexivity|]. cbn [map cstr].
    destruct (bv_unsigned b =? 0) eqn:E.
    - exfalso. apply Hn. left. apply Z.eqb_eq in E. apply bv_eq. rewrite E. reflexivity.
    - f_equal. apply IH. intros Hin. apply Hn. right. exact Hin.
  Qed.

  (* [comment removed for export] *)
  Definition open_offline_wtp_proof__stmt : Prop := pcap_open_offline_wtp_stmt HO K sites.
  Section Sz5.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME EB name slack ej fuel : ltac2:(SecDiet.SzSec.tyM 'open_offline_wtp_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma open_offline_wtp_proof__body : ltac2:(SecDiet.SzSec.bodyP 'open_offline_wtp_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FCLOSE FMT FOPEN FOPEN_OFFLINE HAL HFL SFL. pin_using (fun (FCLOSE FMT FOPEN FOPEN_OFFLINE HAL HFL SFL : unit) => tt).
    intros PRE SITES -> Ha2 Ha1 HNAME NNUL LEN FIRST NOK SLK N1 N2 HEB E1 E2 E8 D1.
    (* [comment removed for export] *)
    assert (LENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - LEN; lia). hide LEN.
    specialize (Ha1 eq_refl). cbv beta in Ha2. subst a1 a2.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L4_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (bytes_at_bound _ _ _ _ HNAME) as BN. rewrite length_app in BN. cbn [length] in BN.
    pose proof (GIo_core_misc K _ _ _ _ _ G) as (_ & _ & GOT1 & GOT2 & _).
    (* [comment removed for export] *)
    destruct name as [|c0 name']; [cbn in LENZ; lia|].
    assert (HNAME0 : bytes_at ssegs m NAME ((c0 :: name') ++ [Z_to_bv 8 0])).
    { pose proof HNAME as X. change ((c0 :: name') ++ Z_to_bv 8 0 :: slack) with ((c0 :: name') ++ ([Z_to_bv 8 0] ++ slack)) in X.
      rewrite app_assoc in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X. exact (proj1 X). }
    unfold Pcap.pcap_open_offline, pcap_open_offline_with_tstamp_precision, errmsg_for_errno.
    cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fopen_r e_last_errno e_fclose prims]. unfold PCAP_OPEN_OFFLINE_WTP_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    hide HEB.
    ienter. carve_frame 48%nat ST. do 8 step. if_false_by (eqz_false NAME ltac:(lia)).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HR0 : ov_read_bytes ssegs mm (wa (NAME + 0)) 1 = Some [c0])
        by (rewrite (bytes_at_read ssegs mm NAME _ 0 1 HNAME ltac:(lia) ltac:(cbn; lia)); reflexivity) end.
    assert (NE45 : negb (bv_eqb (zxb c0) (Z_to_bv 64 45)) = true).
    { unfold zxb, bv_eqb. pose proof (bv_unsigned_in_range 8 c0) as Hc. unfold bv_modulus in Hc. cbn in Hc.
      rewrite !unsigned_lit by lia. apply Bool.negb_true_iff, Z.eqb_neq. intros E. apply FIRST. cbn. f_equal. apply bv_eq. rewrite E. reflexivity. }
    do 3 step. rewrite NE45; cbv iota. do 5 step.
    (* [comment removed for export] *)
    assert (EBX : CEILZ <= bv_unsigned sp) by (unfold rc_lo in *; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R s CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AGa : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|Ha] Hn]; cbn [outside]; [lia|];
            destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; lia);
      unhide HEB; assert (HEB1 : rw_cells ssegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
      assert (RB : bytes_at ssegs mm 0x108ab ([Z_to_bv 8 114; Z_to_bv 8 98] ++ [Z_to_bv 8 0]))
        by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs mm 0x108ab [Z_to_bv 8 114; Z_to_bv 8 98; Z_to_bv 8 0] ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))))
    end.
    clear MU WM HEB HR0.
    name_sp sp (-48)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply (FOPEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo NAME 0x108ab%Z (c0 :: name') [Z_to_bv 8 114; Z_to_bv 8 98] false);
        [| reflexivity | reflexivity | exact HNAME0 | exact NNUL | exact LEN | exact NOK (* [comment removed for export] *) | left; right; rewrite Hsp; cbn [length] in *; lia | exact RB | split; reflexivity ].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    intros [f|] s' ms' PO; cbv beta iota in PO.
    - (* [comment removed for export] *)
      destruct PO as (av & m2 & E & OF1 & MI1 & ST1 & AG1 & (Af & -> & G1)).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 82464)) with (Z_to_bv 64 82464) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      pose proof (GIo_block_ok K _ _ _ _ _ _ G1 ltac:(apply in_or_app; right; left; reflexivity)) as (A1 & _ & _ & A4 & A5 & _).
      cbn [cb_addr cb_size fst snd] in A1, A4, A5. unfold FILE_BLOCK in A4, A5.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (HEB2 : rw_cells ssegs m2 EB [CB 256 ej]) by (eapply agrees_rw_cells; [exact AG1 | exact HEB1 | intros a Ha; left; lia]). clear HEB1.
      pose proof (GIo_core_misc K _ _ _ _ _ G1) as (_ & _ & GOT1' & GOT2' & _).
      hide HEB2.
      ienter. step. if_false_by (eqz_false Af ltac:(lia)). do 8 step.
      unhide HEB2. clear GOT1' GOT2'.
      name_sp sp (-48)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply FOPEN_OFFLINE;
          [ split; [exact G1|]; split; [rewrite Hsp; exact ST1|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
          | left; reflexivity | rewrite SITES, Hsp; unfold D_OPEN_OFFLINE, D_FOPEN_OFFLINE; f_equal; lia
          | reflexivity | reflexivity | reflexivity | exact HEB2 | rewrite Hsp; lia | lia | exact E8 ]. }
      intros [msg|p] s'' ms'' PO; unfold open_result_post in PO.
      + (* [comment removed for export] *)
        destruct PO as (av2 & m3 & FB' & E & OF2 & MI2 & ST2 & AG2 & (junk' & -> & -> & G2 & HEB3 & LENM & RNGM)).
        unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 82500)) with (Z_to_bv 64 82500) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (FR2 : rw_cells ssegs m3 (bv_unsigned sp + -48) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply agrees_rw_cells; [exact AG2 | exact FR |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| lia]. }
        clear FR MI1. hide HEB3.
        ienter. step. if_false. step. if_false_by (eqb_lits_false Af 0x23750 ltac:(lia) ltac:(lia) ltac:(lia)). do 2 step.
        name_sp sp (-48)%Z.
        apply evt_done. eapply (implM_bind ssegs).
        { eapply (FCLOSE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s'' CL [] FB); [|reflexivity| eapply (GIo_new_file_not_out HO K HAL); [exact G | exact G2 | congruence]].
          split; [exact G2|]. split; [rewrite Hsp; exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
        intros [] s3' ms3 PO. cbv beta in PO. destruct PO as (av3 & m4 & E & OF3 & MI3 & ST3 & AG3 & G3).
        unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 82516)) with (Z_to_bv 64 82516) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FR2; [|lia].
        unhide HEB3. assert (HEB4 : rw_cells ssegs m4 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'])
          by (eapply agrees_rw_cells; [exact AG3 | exact HEB3 | intros a Ha; left; lia]). clear HEB3 MI2.
        apply (implM_ret ssegs). do 9 step.
        release_frame FR2 ST3 (bv_unsigned sp).
        apply evt_done; subst POSTQ; unfold open_result_post.
        lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
        split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
        split; [solve [assumption | congruence] |].
        split; [assumption|]. split; [assumption|].
        split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans; [|eapply agrees_on_trans].
                 - eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha].
                 - eapply agrees_on_weaken; [exact AG2|]. intros a [[Ha|Ha] Hn]; (split; [|exact Hn]); [left; lia| right; exact Ha].
                 - eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha]. }
        exists junk'. split; [reflexivity|]. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB4|]. split; [exact LENM| exact RNGM].
      + (* [comment removed for export] *)
        destruct PO as (av2 & m3 & FB' & E & OF2 & MI2 & ST2 & AG2 & (P & PB & -> & [-> ERF] & G2 & PC2 & HEB3)).
        unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 82500)) with (Z_to_bv 64 82500) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (FR2 : rw_cells ssegs m3 (bv_unsigned sp + -48) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply agrees_rw_cells; [exact AG2 | exact FR |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| lia]. }
        clear FR MI1.
        pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G2 (PCAPR_self_in _ _ _ _ _ PC2)) as (Q1 & _ & _ & Q4 & _).
        destruct HEB3 as [e3 HEB3]. hide HEB3. hide PC2.
        apply (implM_ret ssegs). step. if_true_by (nez_true P ltac:(pose proof (psize_pos p); lia)). do 7 step.
        release_frame FR2 ST2 (bv_unsigned sp).
        unhide HEB3. unhide PC2.
        apply evt_done; subst POSTQ; unfold open_result_post.
        lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 P), mm, ((f, Af, FILE_BLOCK) :: FB) end.
        split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
        split; [solve [assumption | congruence] |].
        split; [assumption|]. split; [assumption|].
        split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans.
                 - eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha].
                 - eapply agrees_on_weaken; [exact AG2|]. intros a [[Ha|Ha] Hn]; (split; [|exact Hn]); [left; lia| right; exact Ha]. }
        exists P, PB. split; [reflexivity|]. split; [exists Af; rewrite ERF; reflexivity|]. split; [exact G2|]. split; [exact PC2| exists e3; exact HEB3].
    - (* [comment removed for export] *)
      destruct PO as (av & m2 & E & OF1 & MI1 & ST1 & AG1 & -> & G1 & EN2 & ER).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 82464)) with (Z_to_bv 64 82464) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (HEB2 : rw_cells ssegs m2 EB [CB 256 ej]) by (eapply agrees_rw_cells; [exact AG1 | exact HEB1 | intros a Ha; left; lia]). clear HEB1.
      assert (HNAME2 : bytes_at ssegs m2 NAME ((c0 :: name') ++ Z_to_bv 8 0 :: slack)) by (eapply agrees_bytes_at; [exact AG1 | exact HNAME | intros a Ha; rewrite length_app in Ha; cbn [length] in Ha; left; lia]).
      pose proof (GIo_tls K _ _ _ _ _ G1) as [_ TB]. unfold tls_block_ok in TB.
      unfold utp in EN2. rewrite <- TP in EN2.
      eapply implM_pure; [reflexivity|]. cbn [fst snd]. rewrite (cstr_no_nul _ NNUL).
      set (e := lc_errno (ps_libc s')) in *.
      hide HEB2. hide HNAME2.
      step. if_true. do 11 step.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      unhide HEB2. unhide HNAME2.
      assert (MSG : fmt_at m2 0x107e7 "%s"%string).
      { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m2 0x107e7 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "%s"%string) ++ [Z_to_bv 8 0])
                                 MI1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
      name_sp sp (-48)%Z.
      eapply evt_cut.
      { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 0x107e7%Z e "%s"%string [AStr (map bv_unsigned (c0 :: name'))] ej);
          [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | | exact HEB2
           | right; rewrite Hsp; lia | exact E8 ].
        { split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
        cbn [length firstn]. constructor; [|constructor]. cbn [farg_word]. exists NAME, (c0 :: name'), slack.
        split; [reflexivity|]. split; [exact HNAME2|]. split; [exact NNUL|]. split; [reflexivity|]. split; [cbn [length] in *; lia|].
        split; [first [exact SLK | cbn [length] in *; exact SLK]|]. split; [clear - D1; cbn [length] in *; lia|].
        left. right. rewrite Hsp. cbn [length] in *. lia. }
      cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m3 & junk' & -> & MI3 & ST3 & AG3 & G3 & HEB3).
      rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 82576)) with (Z_to_bv 64 82576) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      assert (FR3 : rw_cells ssegs m3 (bv_unsigned sp + -48) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply agrees_rw_cells; [exact AG3 | exact FR |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| lia]. }
      clear FR MI1. hide HEB3.
      do 8 step.
      release_frame FR3 ST3 (bv_unsigned sp). unhide HEB3.
      apply evt_done; subst POSTQ; unfold open_result_post.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [solve [assumption | congruence] |].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans.
               - eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha].
               - eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] Hn]; (split; [|exact Hn]); [left; lia| right; exact Ha]. }
      exists junk'. split; [reflexivity|]. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB3|].
      split; [pose proof (fmt_errmsg_length "%s"%string [AStr (map bv_unsigned (c0 :: name'))] e); lia|].
      apply fmt_errmsg_ok; [vm_compute; reflexivity| apply args_ok_str1; exact NNUL].
  Qed.
  End Sz5.
  Theorem open_offline_wtp_proof : ltac:(let t := eval cbv delta [open_offline_wtp_proof__stmt] in open_offline_wtp_proof__stmt in exact t).
  Proof using FCLOSE FMT FOPEN FOPEN_OFFLINE HAL HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME EB name slack ej fuel. ltac2:(SecDiet.SzSec.closeP 'open_offline_wtp_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Theorem open_offline_proof : pcap_open_offline_stmt HO K sites.
  Proof using FCLOSE FMT FOPEN FOPEN_OFFLINE HAL HFL SFL. pin_using (fun (FCLOSE FMT FOPEN FOPEN_OFFLINE HAL HFL SFL : unit) => tt).
    red. intros until fuel. intros PRE SITES -> Ha1 _ HNAME NNUL LEN FIRST NOK SLK N1 N2 HEB E1 E2 E8 D1. cbv beta in Ha1. subst a1.
    pose proof PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    unfold PCAP_OPEN_OFFLINE_ENTRY. unfold implM. iprefix. do 3 step. apply evt_done.
    eapply open_offline_wtp_proof; [exact PRE | exact SITES | reflexivity | reflexivity | reflexivity | exact HNAME | exact NNUL | exact LEN | exact FIRST
                                   | exact NOK | exact SLK | exact N1 | exact N2 | exact HEB | exact E1 | exact E2 | exact E8 | exact D1].
  Qed.
End Open.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB.
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

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).
Ltac pstep := step; fix_lit_store.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall a, (0 <= a < 2^64)%Z -> Z.lxor a 18446744073709551615 = (18446744073709551615 - a)%Z.
Proof.
  intros a Ha. change 18446744073709551615%Z with (Z.ones 64).
  destruct (Z.eq_dec a 0) as [->|Hnz]; [reflexivity|].
  rewrite <- Z.ldiff_ones_l_low; [| lia | apply Z.log2_lt_pow2; lia].
  symmetry. apply Z.sub_nocarry_ldiff. rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_eq_0; [reflexivity| lia |].
  apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma implM_pure : forall {St A} (c : @M St A) s Q ms r s1,
  c s = Ret (Ok (r, s1)) -> evt usegs (Q r s1) ms -> implM usegs c s Q ms.
Proof using Type. pin_using tt. intros St A c s Q ms r s1 E H. unfold implM. rewrite E. cbn. exact H. Qed.

Definition fmt_errmsg_length__stmt : Prop := forall f args e, (length (fmt_errmsg f args e) <= 255)%nat.
Section Sz3.
Variables f args e : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_length__stmt "vvv" @f).
Lemma fmt_errmsg_length__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_length__stmt "vvv").
Proof using Type. pin_using tt.
 unfold fmt_errmsg, snprintf, snprintf_out, PCAP_ERRBUF_SIZE, zlength.
  set (mm := firstn (Z.to_nat (256 - 1)) (fmt_output (fmt f) args)).
  assert (Hm : (length mm <= 255)%nat) by (subst mm; rewrite length_firstn; apply Nat.le_min_l).
  destruct (256 <? Z.of_nat (length mm) + 3)%Z eqn:E; [exact Hm|].
  apply Z.ltb_ge in E. rewrite !length_app, length_firstn. cbn [length str String.list_ascii_of_string map]. 
  unfold str. cbn [String.list_ascii_of_string map length]. lia.
Qed.
End Sz3.
Lemma fmt_errmsg_length : ltac:(let t := eval cbv delta [fmt_errmsg_length__stmt] in fmt_errmsg_length__stmt in exact t).
Proof using Type. intros f args e. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_length__body "vvv"). Qed.

Section Open.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis CALLOC : calloc_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.

  Definition open_offline_common_proof__stmt : Prop := open_offline_common_stmt HO K sites.
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo EB total ej : ltac2:(SecDiet.SzSec.tyM 'open_offline_common_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma open_offline_common_proof__body : ltac2:(SecDiet.SzSec.bodyP 'open_offline_common_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CALLOC FMT HFL SFL. pin_using (fun (CALLOC FMT HFL SFL : unit) => tt).
 intros PRE -> -> -> Htot HEB CR E8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L1B_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    assert (TOT : 0 <= total < 2^32) by (unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in Htot; lia).
    assert (EBX : EB + 256 <= CEILZ \/ bv_unsigned sp <= EB).
    { destruct CR as [Hb|Hs]; [|right; lia]. left.
      destruct (GIo_CLc_facts K R s CL [] FB m (EB + 255) ltac:(rewrite app_nil_r; exact G) ltac:(apply Hb; lia)) as [Hc _]. lia. }
    unfold Pcap.pcapint_open_offline_common, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_calloc e_last_errno prims]. unfold PCAP_OPEN_OFFLINE_COMMON_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide HEB.
    ienter. carve_frame 32%nat ST. do 11 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R s CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AGa : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|Ha] Hn]; cbn [outside]; [lia|];
            destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; lia);
      unhide HEB; assert (HEB1 : rw_cells usegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia])
    end.
    clear MU WM HEB.
    name_sp sp (-32)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { eapply CALLOC; [| reflexivity | reflexivity | lia | lia | unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in Htot; lia].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    intros [q|] s' ms' PO; cbv beta iota in PO.
    - (* [comment removed for export] *)
      destruct PO as (av & m2 & E & OF1 & MI1 & ST1 & AG1 & (A & -> & G1 & NEW)).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      rewrite Z.mul_1_r in G1, NEW.
      pose proof (GIo_block_ok K _ _ _ _ _ _ G1 ltac:(left; reflexivity)) as (A1 & A2 & A3 & A4 & A5 & A6). cbn [cb_addr cb_size fst snd] in A1, A2, A3, A4, A5, A6.
      replace (ret_pc (Z_to_bv 64 84256)) with (Z_to_bv 64 84256) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (HEB2 : rw_cells usegs m2 EB [CB 256 ej]).
      { eapply agrees_rw_cells; [exact AG1 | exact HEB1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
        destruct CR as [Hb|Hs]; [right; apply Hb; lia | left; lia]. }
      clear HEB1.
      assert (NB : forall a, in_block CL a -> ~ (A <= a < A + total)).
      { intros a Ha Hin. destruct (GIo_CLc_facts K R s' [(q, A, total)] CL FB m2 a G1 ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Hin)) as [_ Hn].
        exact (Hn Ha). }
      pose proof (munch_refl [(A, A + 200)]%Z m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.   (* [comment removed for export] *)
      unfold PCAP_PRIV_OFF. apply (implM_ret usegs). hide HEB2.
      destruct Htot as [-> | ->]; unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in *.
      all: lazymatch type of NEW with context [Z.to_nat ?z] => let n := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with n in NEW end.
      (* [comment removed for export] *)
      all: let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 664); change (repeat (Z_to_bv 8 0) 664) with z in NEW.
      all: let z := fresh "sblz" in pose (z := repeat (Z_to_bv 8 0) 680); change (repeat (Z_to_bv 8 0) 680) with z in NEW.
      all: step; step; if_false_by (eqz_false A ltac:(lia)); step; rewrite (and7_aligned A) by (unfold rc_lo in LO; lia); step; if_false; do 5 step.   (* [comment removed for export] *)
      all: rewrite (unsigned_lit A) by lia; rewrite (lxor_ones64 A) by lia; step.
      all: replace (bv_ltu (Z_to_bv 64 (18446744073709551615 - A)) (Z_to_bv 64 648)) with false
             by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia); cbv iota.
      all: do 11 pstep.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      all: lazymatch type of NEW with rw_cells _ ?mm ?AA [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10] =>
             pose proof (rw_cells_merge usegs mm AA [c0; c1; c2; c3] [c4; c5; c6] [c7; c8; c9; c10] NEW) as NEW2;
             cbn [cells_size csize cells_bytes cbytes app Nat.add] in NEW2 end.
      all: lazymatch type of NEW2 with rw_cells _ ?mm ?AA [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
             pose proof (rw_cells_merge usegs mm AA [c0; c1; c2; c3; c4; c5] [c6; c7; c8] [] NEW2) as NEW3;
             cbn [cells_size csize cells_bytes cbytes app Nat.add] in NEW3 end.
      all: clear NEW NEW2.
      all: release_frame FR ST1 (bv_unsigned sp).
      all: apply evt_done; subst POSTQ; unfold open_common_post.
      all: lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 A), mm end.
      all: split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      all: split; [solve [assumption | congruence] |].
      all: split; [assumption|]; split; [assumption|].
      all: split; [eapply agrees_on_trans; [exact AGa|]; eapply agrees_on_trans;
                    [eapply agrees_on_weaken; [exact AG1|]; intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha]
                    |eapply agrees_on_of_munch; [exact MU2 | exact WM2|]; intros a _ [[Ha|Ha] Hn]; cbn [outside]; [unfold rc_lo in LO; lia|];
                     split; [|exact I]; intros Hin; apply (NB a Ha); lia]|].
      all: exists A; split; [reflexivity|].
      all: split; [eapply (GIo_client_frame K HFL SFL); [exact G1 | exact MU2 | exact WM2|];
                   apply Forall_cons; [right; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| apply Forall_nil]|].
      all: unhide HEB2.
      all: split; [| eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU2| exact WM2| intros a _ Ho; exact Ho] | exact HEB2 |];
                    intros a Ha; cbn [outside cells_size csize Nat.add] in *; split; [|exact I];
                    destruct CR as [Hb|Hs]; [intros Hin; apply (NB a ltac:(apply Hb; lia)); lia | lia]].
      all: assumption.
    - (* [comment removed for export] *)
      destruct PO as (av & m2 & E & OF1 & MI1 & ST1 & AG1 & -> & G1 & EN1 & EN2).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 84256)) with (Z_to_bv 64 84256) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (HEB2 : rw_cells usegs m2 EB [CB 256 ej]).
      { eapply agrees_rw_cells; [exact AG1 | exact HEB1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
        destruct CR as [Hb|Hs]; [right; apply Hb; lia | left; lia]. }
      clear HEB1.
      pose proof (GIo_tls K _ _ _ _ _ G1) as [_ TB]. unfold tls_block_ok_u in TB.
      unfold utp in EN2. rewrite <- TP in EN2.
      eapply implM_pure; [reflexivity|]. cbn [fst snd]. rewrite EN1.
      pose proof TB as TB'. unfold utp in TB'. rewrite <- TP in TB'.
      assert (E4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
      { destruct TB' as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * 4 + 9)%Z. lia. }
      step. step. if_true. do 5 step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(lia)).
      step. rewrite (and3_aligned (bv_unsigned tp + -164)) by lia. step. if_false. do 6 step.
      replace (sx32 (Z_to_bv 64 12)) with (Z_to_bv 64 (s32 12)) by (unfold sx32; rewrite unsigned_lit by lia; reflexivity).
      assert (MSG : fmt_at m2 0x108ae "malloc"%string).
      { split; [|cbn; lia]. pose proof (ro_cells_image usegs m2 0x108ae (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "malloc"%string) ++ [Z_to_bv 8 0])
                                 MI1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
        exact (ro_cells_bytes_at _ _ _ _ RO). }
      name_sp sp (-32)%Z.
      eapply evt_cut.
      { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 0x108ae%Z 12%Z "malloc"%string [] ej);
          [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB2
           | destruct CR as [Hb|Hs]; [left; exact Hb | right; rewrite Hsp; lia] | exact E8 ].
        split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m3 & junk' & -> & MI3 & ST3 & AG3 & G3 & HEB3).
      rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 84352)) with (Z_to_bv 64 84352) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply agrees_rw_cells; [exact AG3 | exact FR |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| lia]. }
      clear FR MI1.
      do 7 step.
      release_frame FR3 ST3 (bv_unsigned sp).
      apply evt_done; subst POSTQ; unfold open_common_post.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [solve [assumption | congruence] |].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans.
               - eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha].
               - eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] Hn]; (split; [|exact Hn]); [left; lia| right; exact Ha]. }
      exists junk'. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB3|].
      split; [pose proof (fmt_errmsg_length "malloc"%string [] 12); lia|].
      apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor].
  Qed.
  End Sz4.
  Theorem open_offline_common_proof : ltac:(let t := eval cbv delta [open_offline_common_proof__stmt] in open_offline_common_proof__stmt in exact t).
  Proof using CALLOC FMT HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo EB total ej. ltac2:(SecDiet.SzSec.closeP 'open_offline_common_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FOPEN : fopen_stmt_o HO K.
  Hypothesis FCLOSE : fclose_stmt_o HO K.
  Hypothesis FOPEN_OFFLINE : fopen_offline_stmt HO K sites.

  Lemma cstr_no_nul : forall (bs : list byte), ~ In (Z_to_bv 8 0) bs -> cstr (map bv_unsigned bs) = map bv_unsigned bs.
  Proof using Type. pin_using tt.
    induction bs as [|b bs IH]; intros Hn; [reflexivity|]. cbn [map cstr].
    destruct (bv_unsigned b =? 0) eqn:E.
    - exfalso. apply Hn. left. apply Z.eqb_eq in E. apply bv_eq. rewrite E. reflexivity.
    - f_equal. apply IH. intros Hin. apply Hn. right. exact Hin.
  Qed.

  (* [comment removed for export] *)
  Definition open_offline_wtp_proof__stmt : Prop := pcap_open_offline_wtp_stmt HO K sites.
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME EB name slack ej fuel : ltac2:(SecDiet.SzSec.tyM 'open_offline_wtp_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma open_offline_wtp_proof__body : ltac2:(SecDiet.SzSec.bodyP 'open_offline_wtp_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FCLOSE FMT FOPEN FOPEN_OFFLINE HAL HFL SFL. pin_using (fun (FCLOSE FMT FOPEN FOPEN_OFFLINE HAL HFL SFL : unit) => tt).
 intros PRE SITES -> Ha2 Ha1 HNAME NNUL LEN FIRST NOK SLK N1 N2 HEB E1 E2 E8 D1.
    (* [comment removed for export] *)
    assert (LENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - LEN; lia). hide LEN.
    specialize (Ha1 eq_refl). cbv beta in Ha2. subst a1 a2.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L4_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (bytes_at_bound _ _ _ _ HNAME) as BN. rewrite length_app in BN. cbn [length] in BN.
    pose proof (GIo_core_misc K _ _ _ _ _ G) as (_ & _ & GOT1 & GOT2 & _).
    (* [comment removed for export] *)
    destruct name as [|c0 name']; [cbn in LENZ; lia|].
    assert (HNAME0 : bytes_at usegs m NAME ((c0 :: name') ++ [Z_to_bv 8 0])).
    { pose proof HNAME as X. change ((c0 :: name') ++ Z_to_bv 8 0 :: slack) with ((c0 :: name') ++ ([Z_to_bv 8 0] ++ slack)) in X.
      rewrite app_assoc in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X. exact (proj1 X). }
    unfold Pcap.pcap_open_offline, pcap_open_offline_with_tstamp_precision, errmsg_for_errno.
    cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fopen_r e_last_errno e_fclose prims]. unfold PCAP_OPEN_OFFLINE_WTP_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide HEB.
    ienter. carve_frame 48%nat ST. do 8 step. if_false_by (eqz_false NAME ltac:(lia)).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HR0 : ov_read_bytes usegs mm (wa (NAME + 0)) 1 = Some [c0])
        by (rewrite (bytes_at_read usegs mm NAME _ 0 1 HNAME ltac:(lia) ltac:(cbn; lia)); reflexivity) end.
    assert (NE45 : negb (bv_eqb (zxb c0) (Z_to_bv 64 45)) = true).
    { unfold zxb, bv_eqb. pose proof (bv_unsigned_in_range 8 c0) as Hc. unfold bv_modulus in Hc. cbn in Hc.
      rewrite !unsigned_lit by lia. apply Bool.negb_true_iff, Z.eqb_neq. intros E. apply FIRST. cbn. f_equal. apply bv_eq. rewrite E. reflexivity. }
    do 3 step. rewrite NE45; cbv iota. do 5 step.
    (* [comment removed for export] *)
    assert (EBX : CEILZ <= bv_unsigned sp) by (unfold rc_lo in *; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R s CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AGa : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|Ha] Hn]; cbn [outside]; [lia|];
            destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; lia);
      unhide HEB; assert (HEB1 : rw_cells usegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
      assert (RB : bytes_at usegs mm 0x108ab ([Z_to_bv 8 114; Z_to_bv 8 98] ++ [Z_to_bv 8 0]))
        by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs mm 0x108ab [Z_to_bv 8 114; Z_to_bv 8 98; Z_to_bv 8 0] ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))))
    end.
    clear MU WM HEB HR0.
    name_sp sp (-48)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { eapply (FOPEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo NAME 0x108ab%Z (c0 :: name') [Z_to_bv 8 114; Z_to_bv 8 98] false);
        [| reflexivity | reflexivity | exact HNAME0 | exact NNUL | exact LEN | exact NOK (* [comment removed for export] *) | left; right; rewrite Hsp; cbn [length] in *; lia | exact RB | split; reflexivity ].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    intros [f|] s' ms' PO; cbv beta iota in PO.
    - (* [comment removed for export] *)
      destruct PO as (av & m2 & E & OF1 & MI1 & ST1 & AG1 & (Af & -> & G1)).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 82644)) with (Z_to_bv 64 82644) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      pose proof (GIo_block_ok K _ _ _ _ _ _ G1 ltac:(apply in_or_app; right; left; reflexivity)) as (A1 & _ & _ & A4 & A5 & _).
      cbn [cb_addr cb_size fst snd] in A1, A4, A5. unfold FILE_BLOCK in A4, A5.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (HEB2 : rw_cells usegs m2 EB [CB 256 ej]) by (eapply agrees_rw_cells; [exact AG1 | exact HEB1 | intros a Ha; left; lia]). clear HEB1.
      pose proof (GIo_core_misc K _ _ _ _ _ G1) as (_ & _ & GOT1' & GOT2' & _).
      hide HEB2.
      ienter. step. if_false_by (eqz_false Af ltac:(lia)). do 8 step.
      unhide HEB2. clear GOT1' GOT2'.
      name_sp sp (-48)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply FOPEN_OFFLINE;
          [ split; [exact G1|]; split; [rewrite Hsp; exact ST1|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
          | left; reflexivity | rewrite SITES, Hsp; unfold D_OPEN_OFFLINE, D_FOPEN_OFFLINE; f_equal; lia
          | reflexivity | reflexivity | reflexivity | exact HEB2 | rewrite Hsp; lia | lia | exact E8 ]. }
      intros [msg|p] s'' ms'' PO; unfold open_result_post in PO.
      + (* [comment removed for export] *)
        destruct PO as (av2 & m3 & FB' & E & OF2 & MI2 & ST2 & AG2 & (junk' & -> & -> & G2 & HEB3 & LENM & RNGM)).
        unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 82680)) with (Z_to_bv 64 82680) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (FR2 : rw_cells usegs m3 (bv_unsigned sp + -48) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply agrees_rw_cells; [exact AG2 | exact FR |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| lia]. }
        clear FR MI1. hide HEB3.
        ienter. step. if_false. step. if_false_by (eqb_lits_false Af 0x23f10 ltac:(lia) ltac:(lia) ltac:(lia)). do 2 step.
        name_sp sp (-48)%Z.
        apply evt_done. eapply (implM_bind usegs).
        { eapply (FCLOSE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s'' CL [] FB); [|reflexivity| eapply (GIo_new_file_not_out HO K HAL); [exact G | exact G2 | congruence]].
          split; [exact G2|]. split; [rewrite Hsp; exact ST2|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
        intros [] s3' ms3 PO. cbv beta in PO. destruct PO as (av3 & m4 & E & OF3 & MI3 & ST3 & AG3 & G3).
        unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 82696)) with (Z_to_bv 64 82696) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FR2; [|lia].
        unhide HEB3. assert (HEB4 : rw_cells usegs m4 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'])
          by (eapply agrees_rw_cells; [exact AG3 | exact HEB3 | intros a Ha; left; lia]). clear HEB3 MI2.
        apply (implM_ret usegs). do 9 step.
        release_frame FR2 ST3 (bv_unsigned sp).
        apply evt_done; subst POSTQ; unfold open_result_post.
        lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
        split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
        split; [solve [assumption | congruence] |].
        split; [assumption|]. split; [assumption|].
        split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans; [|eapply agrees_on_trans].
                 - eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha].
                 - eapply agrees_on_weaken; [exact AG2|]. intros a [[Ha|Ha] Hn]; (split; [|exact Hn]); [left; lia| right; exact Ha].
                 - eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha]. }
        exists junk'. split; [reflexivity|]. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB4|]. split; [exact LENM| exact RNGM].
      + (* [comment removed for export] *)
        destruct PO as (av2 & m3 & FB' & E & OF2 & MI2 & ST2 & AG2 & (P & PB & -> & [-> ERF] & G2 & PC2 & HEB3)).
        unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 82680)) with (Z_to_bv 64 82680) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (FR2 : rw_cells usegs m3 (bv_unsigned sp + -48) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply agrees_rw_cells; [exact AG2 | exact FR |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| lia]. }
        clear FR MI1.
        pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G2 (PCAPR_self_in _ _ _ _ _ PC2)) as (Q1 & _ & _ & Q4 & _).
        destruct HEB3 as [e3 HEB3]. hide HEB3. hide PC2.
        apply (implM_ret usegs). step. if_true_by (nez_true P ltac:(pose proof (psize_pos p); lia)). do 7 step.
        release_frame FR2 ST2 (bv_unsigned sp).
        unhide HEB3. unhide PC2.
        apply evt_done; subst POSTQ; unfold open_result_post.
        lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 P), mm, ((f, Af, FILE_BLOCK) :: FB) end.
        split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
        split; [solve [assumption | congruence] |].
        split; [assumption|]. split; [assumption|].
        split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans.
                 - eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha].
                 - eapply agrees_on_weaken; [exact AG2|]. intros a [[Ha|Ha] Hn]; (split; [|exact Hn]); [left; lia| right; exact Ha]. }
        exists P, PB. split; [reflexivity|]. split; [exists Af; rewrite ERF; reflexivity|]. split; [exact G2|]. split; [exact PC2| exists e3; exact HEB3].
    - (* [comment removed for export] *)
      destruct PO as (av & m2 & E & OF1 & MI1 & ST1 & AG1 & -> & G1 & EN2 & ER).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 82644)) with (Z_to_bv 64 82644) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (HEB2 : rw_cells usegs m2 EB [CB 256 ej]) by (eapply agrees_rw_cells; [exact AG1 | exact HEB1 | intros a Ha; left; lia]). clear HEB1.
      assert (HNAME2 : bytes_at usegs m2 NAME ((c0 :: name') ++ Z_to_bv 8 0 :: slack)) by (eapply agrees_bytes_at; [exact AG1 | exact HNAME | intros a Ha; rewrite length_app in Ha; cbn [length] in Ha; left; lia]).
      pose proof (GIo_tls K _ _ _ _ _ G1) as [_ TB]. unfold tls_block_ok_u in TB.
      unfold utp in EN2. rewrite <- TP in EN2.
      eapply implM_pure; [reflexivity|]. cbn [fst snd]. rewrite (cstr_no_nul _ NNUL).
      set (e := lc_errno (ps_libc s')) in *.
      pose proof TB as TB'. unfold utp in TB'. rewrite <- TP in TB'.
      assert (E4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
      { destruct TB' as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * 4 + 9)%Z. lia. }
      hide HEB2. hide HNAME2.
      step. if_true. do 5 step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(lia)).
      step. rewrite (and3_aligned (bv_unsigned tp + -164)) by lia. step. if_false. do 7 step.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      unhide HEB2. unhide HNAME2.
      assert (MSG : fmt_at m2 0x107e7 "%s"%string).
      { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m2 0x107e7 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "%s"%string) ++ [Z_to_bv 8 0])
                                 MI1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
      name_sp sp (-48)%Z.
      eapply evt_cut.
      { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 0x107e7%Z e "%s"%string [AStr (map bv_unsigned (c0 :: name'))] ej);
          [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | | exact HEB2
           | right; rewrite Hsp; lia | exact E8 ].
        { split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
        cbn [length firstn]. constructor; [|constructor]. cbn [farg_word]. exists NAME, (c0 :: name'), slack.
        split; [reflexivity|]. split; [exact HNAME2|]. split; [exact NNUL|]. split; [reflexivity|]. split; [cbn [length] in *; lia|].
        split; [first [exact SLK | cbn [length] in *; exact SLK]|]. split; [clear - D1; cbn [length] in *; lia|].
        left. right. rewrite Hsp. cbn [length] in *. lia. }
      cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m3 & junk' & -> & MI3 & ST3 & AG3 & G3 & HEB3).
      rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 82768)) with (Z_to_bv 64 82768) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -48) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply agrees_rw_cells; [exact AG3 | exact FR |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. split; [left; lia| lia]. }
      clear FR MI1. hide HEB3.
      do 8 step.
      release_frame FR3 ST3 (bv_unsigned sp). unhide HEB3.
      apply evt_done; subst POSTQ; unfold open_result_post.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [solve [assumption | congruence] |].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_trans.
               - eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] Hn]; [left; lia| right; exact Ha].
               - eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] Hn]; (split; [|exact Hn]); [left; lia| right; exact Ha]. }
      exists junk'. split; [reflexivity|]. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB3|].
      split; [pose proof (fmt_errmsg_length "%s"%string [AStr (map bv_unsigned (c0 :: name'))] e); lia|].
      apply fmt_errmsg_ok; [vm_compute; reflexivity| apply args_ok_str1; exact NNUL].
  Qed.
  End Sz6.
  Theorem open_offline_wtp_proof : ltac:(let t := eval cbv delta [open_offline_wtp_proof__stmt] in open_offline_wtp_proof__stmt in exact t).
  Proof using FCLOSE FMT FOPEN FOPEN_OFFLINE HAL HFL SFL. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo NAME EB name slack ej fuel. ltac2:(SecDiet.SzSec.closeP 'open_offline_wtp_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Theorem open_offline_proof : pcap_open_offline_stmt HO K sites.
  Proof using FCLOSE FMT FOPEN FOPEN_OFFLINE HAL HFL SFL. pin_using (fun (FCLOSE FMT FOPEN FOPEN_OFFLINE HAL HFL SFL : unit) => tt).
    red. intros until fuel. intros PRE SITES -> Ha1 _ HNAME NNUL LEN FIRST NOK SLK N1 N2 HEB E1 E2 E8 D1. cbv beta in Ha1. subst a1.
    pose proof PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    unfold PCAP_OPEN_OFFLINE_ENTRY. unfold implM. iprefix. do 3 step. apply evt_done.
    eapply open_offline_wtp_proof; [exact PRE | exact SITES | reflexivity | reflexivity | reflexivity | exact HNAME | exact NNUL | exact LEN | exact FIRST
                                   | exact NOK | exact SLK | exact N1 | exact N2 | exact HEB | exact E1 | exact E2 | exact E8 | exact D1].
  Qed.
End Open.

End WithCeil.
End TwB.
End F_pcap_open.

(* [comment removed for export] *)
Module F_pcap_fopen.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.
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
Section WithCeil.
Context {CEILV : CEIL}.
Lemma implM_mget : forall {St A} (k : St -> @M St A) s Q ms, implM ssegs (k s) s Q ms -> implM ssegs (mbind mget k) s Q ms.
Proof using Type. pin_using tt. intros St A k s Q ms H. exact H. Qed.

Lemma map_unsigned_b8 : forall l, Forall (fun z => 0 <= z < 256)%Z l -> map bv_unsigned (map b8 l) = l.
Proof using Type. pin_using tt.
  induction l as [|x l IH]; intros HF; [reflexivity|]. apply Forall_cons_iff in HF as [Hx HF]. cbn [map]. f_equal; [|apply IH; exact HF].
  unfold b8. apply Z_to_bv_small. unfold bv_modulus. cbn. lia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac merge_cells H k n :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let pre := eval cbv beta iota delta [firstn skipn] in (firstn k cs) in
      let mid := eval cbv beta iota delta [firstn skipn] in (firstn n (skipn k cs)) in
      let post := eval cbv beta iota delta [firstn skipn Nat.add] in (skipn (k + n) cs) in
      change cs with (pre ++ mid ++ post) in H;
      apply (rw_cells_merge segs m A pre mid post) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac pstep := step; fix_lit_store.

(* [comment removed for export] *)
Ltac norm_addr H P :=
  lazymatch type of H with
  | rw_cells _ _ (?b + Z.of_nat ?n)%Z _ =>
      lazymatch b with
      | (P + ?k0)%Z => let k := eval vm_compute in (k0 + Z.of_nat n)%Z in replace (b + Z.of_nat n)%Z with (P + k)%Z in H by lia
      | P => let k := eval vm_compute in (Z.of_nat n) in replace (P + Z.of_nat n)%Z with (P + k)%Z in H by lia
      end
  end.
(* [comment removed for export] *)
Ltac cut_cells H k H1 P :=
  let H2 := fresh "TMP" in
  destruct (rw_cells_cut _ _ _ k H) as [H1 H2]; clear H; cbn [firstn skipn cells_size csize Nat.add] in H1, H2;
  norm_addr H2 P; rename H2 into H.
(* [comment removed for export] *)
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
(* [comment removed for export] *)
Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells ?s ?m ?A1 ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    let J := fresh "J" in
    pose proof (rw_cells_uncut m A1 cs1 cs2 A2 H1 H2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J;
    clear H1 H2; cbn [app] in J; rename J into H1
  end end.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma snprintf_length : forall n f a, (length (Fmt.snprintf n f a) <= Z.to_nat (n - 1))%nat.
Proof using Type. pin_using tt. intros. unfold Fmt.snprintf, snprintf_out. apply firstn_le_length. Qed.


(* [comment removed for export] *)
Lemma aligned16_4 : forall x k, (x mod 16 = 0)%Z -> (k mod 4 = 0)%Z -> ((x + k) mod 4 = 0)%Z.
Proof using Type. pin_using tt.
  intros x k Hx Hk. rewrite Z.add_mod, Hk, Z.add_0_r by lia. rewrite Z.mod_mod by lia.
  apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->]. replace (q * 16)%Z with ((q * 4) * 4)%Z by lia. apply Z.mod_mul.
  all: lia.
Qed.

Section FopenOffline.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FILENO : fileno_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis CHK_PCAP : pcap_check_header_stmt HO K sites.
  Hypothesis CHK_NG : pcap_ng_check_header_stmt HO K sites.
  Lemma chk_any : forall ng, check_header_stmt_for HO K sites ng.
  Proof using CHK_NG CHK_PCAP. pin_using (fun (CHK_NG CHK_PCAP : unit) => tt). intros [|]; [exact CHK_NG | exact CHK_PCAP]. Qed.

  Definition fopen_offline_proof__stmt : Prop := fopen_offline_stmt HO K sites.
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo FA EB f ej fuel : ltac2:(SecDiet.SzSec.tyM 'fopen_offline_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fopen_offline_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_offline_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CHK_NG CHK_PCAP FERROR FILENO FMT FREAD HFL SFL SNPRINTF. pin_using (fun (CHK_NG CHK_PCAP FERROR FILENO FMT FREAD HFL SFL SNPRINTF : unit) => tt).
    intros PRE HinF SITES -> -> -> HEB E1 E2 E8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & A5 & _).
    cbn [cb_addr cb_size fst snd] in A1, A4, A5. unfold FILE_BLOCK in A4, A5.
    assert (EBX : CEILZ <= bv_unsigned sp) by (unfold rc_lo in *; lia).
    unfold pcap_fopen_offline_with_tstamp_precision, read_fail_msg, errmsg_for_errno.
    cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_fileno e_last_errno prims]. unfold PCAP_FOPEN_OFFLINE_WTP_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    hide HEB.
    ienter. carve_frame 48%nat ST. do 8 step. if_false_by (eqz_false FA ltac:(lia)). do 8 step.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB ssegs _ _ [] 8 _ _ [4; 4]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (rw_cells_cut _ _ _ 1 FR) as [ERRc FR']. clear FR. cbn [firstn skipn cells_size csize Nat.add] in ERRc, FR'.
    destruct (rw_cells_cut _ _ _ 1 FR') as [MGc FRS]. clear FR'. cbn [firstn skipn cells_size csize Nat.add] in MGc, FRS.
    replace (bv_unsigned sp + -48 + Z.of_nat 4 + Z.of_nat 4)%Z with (bv_unsigned sp + -40)%Z in FRS by lia.
    replace (bv_unsigned sp + -48 + Z.of_nat 4)%Z with (bv_unsigned sp + -44)%Z in MGc by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R s CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AGa : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|Ha] Hn]; cbn [outside]; [lia|];
            destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; lia);
      unhide HEB; assert (HEB1 : rw_cells ssegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia])
    end.
    clear MU WM HEB.
    (* [comment removed for export] *)
    name_sp sp (-48)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop]. rewrite SITES. unfold sites_at, D_FOPEN_OFFLINE.
      replace (bv_unsigned sp + 48 - 92 + 0)%Z with (bv_unsigned sp + -44)%Z by lia.
      eapply FREAD; [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact MGc | right; rewrite Hsp; lia]. }
    intros got s' ms' PO. cbv beta in PO.
    destruct PO as (av & m2 & junk' & E & OF1 & MI1 & ST1 & AG1 & G1 & -> & GL & GR & MG2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 82708)) with (Z_to_bv 64 82708) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (KEEP : forall A cs, rw_cells ssegs m0 A cs -> (bv_unsigned sp + -48 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -44 \/ bv_unsigned sp + -40 <= A)%Z -> rw_cells ssegs m2 A cs).
    { intros A cs HC HA HD. eapply agrees_rw_cells; [exact AG1 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KEEP in HEB1; [|lia|cbn [cells_size csize Nat.add]; lia]. clear KEEP MI MGc.
    unfold zlength in *.
    assert (WK : forall (PB : list cblock) mA mB, agrees_on (client_keeps (CL ++ PB) (bv_unsigned sp + -48)) mA mB ->
                 agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z mA mB).
    { intros PB mA mB AG. eapply agrees_on_weaken; [exact AG|]. intros a [[Ha|Ha] Hn]; [left; lia| right; apply in_block_app; left; exact Ha]. }
    assert (CLB : forall a, in_block CL a -> a < CEILZ).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. lia. }
    (* [comment removed for export] *)
    assert (WKG : forall (Pr : Z -> Prop) mA mB, agrees_on Pr mA mB ->
                 (forall a, (bv_unsigned sp <= a \/ (in_block CL a /\ a < CEILZ)) -> ~ (EB <= a < EB + 256) -> Pr a)%Z ->
                 agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z mA mB).
    { intros Pr mA mB AG HP. eapply agrees_on_weaken; [exact AG|]. intros a [[Ha|Ha] Hn]; apply HP; [left; exact Ha| exact Hn | | exact Hn].
      right. split; [exact Ha| apply CLB; exact Ha]. }
    (* [comment removed for export] *)
    assert (FOUND : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' : word) (m3 : mem) (ps3 : PState H hptr)
                           (P : Z) (PB : list cblock) (p : pcap hptr hptr) (e3 : list byte) (errw : word),
      pc_rfile p = f -> mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -48) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      GIo K R ps3 (CL ++ PB) FB m3 -> pre_PCAPR (hptr:=hptr) P p PB m3 ->
      rw_cells ssegs m3 (bv_unsigned sp + -48) [C4 errw] -> rw_cells ssegs m3 (bv_unsigned sp + -44) [CB 4 (map b8 got)] ->
      rw_cells ssegs m3 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> rw_cells ssegs m3 EB [CB 256 e3] -> ps_outfile ps3 = ps_outfile s ->
      implM ssegs (mbind (s_fileno HO f) (fun _ => mret (inr p))) ps3 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 FA) (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x14334) fc None m3 (seg_rom ssegs))).
    { intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m3 ps3 P PB p e3 errw RF MI3 ST3 AG3 G3 PPC ERR3 MG3 FRS3 HEB3 OFX.
      clear FRS ERRc HEB1 MG2 MI1 ST1 AG1 G1 G0 AGa.
      destruct PPC as (rf & st & os & Lrf & Lst & Los & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G3 ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
      pose proof (psize_pos p) as PS.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
      hide PRIV. hide BUF. hide IFS. hide HEB3.
      assert (NB : forall a, in_block CL a -> ~ (P <= a < P + 648)%Z).
      { intros a Ha Hin. destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G3 Ha) as [_ Hnb]. apply Hnb. rewrite EPB. unfold pcap_blocks, in_block.
        apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (FWP : Forall (pcap_iv R PB) [(P, P + 648)]%Z).
      { apply Forall_cons; [| apply Forall_nil]. right. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      pose proof (munch_refl [(P, P + 648)]%Z m3) as MU3. pose proof (wmono_refl ssegs m3) as WM3.
      ienter. do 5 step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (G3' : GIo K R ps3 (CL ++ PB) FB mm) by (eapply (GIo_pcap_frame K HFL SFL); [exact G3 | exact MU3 | exact WM3 | exact FWP]);
        assert (AG34 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m3 mm)
          by (eapply agrees_on_of_munch; [exact MU3 | exact WM3|]; intros a _ [[Ha|Ha] Hn]; cbn [outside]; [unfold rc_lo in LO; lia| split; [apply NB; exact Ha| exact Logic.I]]);
        assert (AGP34 : agrees_on (fun a => outside [(P, P + 648)]%Z a) m3 mm) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3| intros a _ Ho; exact Ho])
      end.
      clear MU3 WM3.
      name_sp sp (-48)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply FILENO; [| exact HinF | reflexivity].
        split; [exact G3'|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros fd ps5 ms5 PO. cbv beta in PO. destruct PO as (av & m5 & E & MI5 & ST5 & AG5 & G5 & -> & -> & Hfd).
      unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 82760)) with (Z_to_bv 64 82760) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG5) in FRS3; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ AG5) in ERR3; [|lia].
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG5) in MG3; [|lia].
      assert (HinP : forall a, (P <= a < P + 648)%Z -> in_block (CL ++ PB) a).
      { intros a Ha. apply in_block_app. right. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      apply (keeps_rw_cells_block _ _ _ _ _ _ AG5) in CELLS; [|intros a Ha; apply HinP; cbn [cells_size csize Nat.add] in Ha; lia].
      pose proof (GIo_got_pcap K _ _ _ _ _ G5) as GOT. unfold PK, GOT_PCAP_ADDR, GOT_INSTALL_BPF, GOT_BREAKLOOP in GOT; cbn [pk_oneshot pk_cleanup_sf] in GOT.
      pose proof (munch_refl [(P, P + 648)]%Z m5) as MU5. pose proof (wmono_refl ssegs m5) as WM5.
      apply (implM_ret ssegs).
      (* [comment removed for export] *)
      cut_cells CELLS 1%nat X0 P. cut_cells CELLS 9%nat X1 P. cut_cells CELLS 1%nat X2 P. cut_cells CELLS 2%nat X3 P.
      cut_cells CELLS 5%nat X4 P. cut_cells CELLS 1%nat X5 P. cut_cells CELLS 3%nat X6 P. cut_cells CELLS 1%nat X7 P.
      cut_cells CELLS 6%nat X8 P. cut_cells CELLS 1%nat X9 P. cut_cells CELLS 1%nat X10 P. cut_cells CELLS 1%nat X11 P.
      cut_cells CELLS 1%nat X12 P. rename CELLS into X13.
      (* [comment removed for export] *)
      do 46 pstep.
      all: release_frame ERR3 ST5 (bv_unsigned sp + -44)%Z; release_frame MG3 ST5 (bv_unsigned sp + -40)%Z; release_frame FRS3 ST5 (bv_unsigned sp).
      (* [comment removed for export] *)
      all: merge_all X3; merge_all X5; merge_all X7; merge_all X9.
      all: join_cells X0 X1; join_cells X0 X2; join_cells X0 X3; join_cells X0 X4; join_cells X0 X5; join_cells X0 X6; join_cells X0 X7;
           join_cells X0 X8; join_cells X0 X9; join_cells X0 X10; join_cells X0 X11; join_cells X0 X12; join_cells X0 X13.
      all: rename X0 into CELLS.
      unhide PRIV. unhide BUF. unhide IFS. unhide HEB3.
      pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G3 EPB) as [APB API].
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G3 ltac:(rewrite EPB; right; left; reflexivity)) as (R1 & R2 & R3 & R4 & R5 & R6).
      pose proof WF as (_ & _ & W3 & _).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGP56 : agrees_on (fun a => outside [(P, P + 648)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU5 | exact WM5| intros a _ Ho; exact Ho]);
        assert (AGX : agrees_on (fun a => (in_block (CL ++ PB) a \/ bv_unsigned sp <= a) /\ ~ (P <= a < P + 648))%Z m3 mm)
          by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGP34|]; intros a [_ Hn]; cbn [outside]; split; [exact Hn| exact Logic.I]|];
              eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a [[Ha|Ha] Hn]; [right; exact Ha| left; (keep_hyps CEILV sp EB got P rf st os B a Ha; lia)]|];
              eapply agrees_on_weaken; [exact AGP56|]; intros a [_ Hn]; cbn [outside]; split; [exact Hn| exact Logic.I]);
        destruct (pcap_aux_agree p P B I pad bs m3 mm _ AGX) as (BUF' & PRIV' & IFS');
          [ intros a Ha; split; [left; apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; (keep_hyps CEILV hptr sp EB got P p rf st os B a Ha; lia)| (keep_hyps CEILV hptr sp R lo EB got P p rf st os B a PS APB Ha; lia)]
          | intros a Ha; unfold PCAP_PRIV_OFF in Ha; split; [left; apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; (keep_hyps CEILV hptr sp EB got P p rf st os B a Ha; lia)| unfold PCAP_PRIV_OFF in *; (keep_hyps CEILV hptr sp EB got P p rf st os B a Ha; lia)]
          | intros sg q Hq a Ha; destruct (API sg q Hq) as [X1 X2];
            split; [left; apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; rewrite Hq; do 2 apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; (keep_hyps CEILV sp EB got P rf st os B I sg a Ha; lia)| (keep_hyps CEILV hptr sp R lo EB got P p rf st os B I sg a PS Ha X1; lia)]
          | (keep_hyps CEILV hptr sp EB got P p rf st os B R3; lia) | exact BUF | exact PRIV | exact IFS |];
        assert (HEB6 : rw_cells ssegs mm EB [CB 256 e3])
          by (eapply agrees_rw_cells; [exact AGX | exact HEB3 | intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; (keep_hyps CEILV sp R lo EB got P rf st os B a E1 Ha; lia)| unfold rc_lo in LO; (keep_hyps CEILV hptr sp R lo EB got P p rf st os B a LO BU E1 SPW P4 PS Ha; lia)]]);
        apply evt_done; subst POSTQ; unfold open_result_post; exists (Z_to_bv 64 P), mm, FB
      end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [solve [assumption | congruence] |].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_trans; [exact AG34|]. eapply agrees_on_trans; [apply (WK PB); exact AG5|].
               eapply agrees_on_weaken; [exact AGP56|]. intros a [[Ha|Ha] Hn]; cbn [outside]; [unfold rc_lo in LO; lia| split; [apply NB; exact Ha| exact Logic.I]]. }
      exists P, PB. split; [reflexivity|]. split; [split; [reflexivity| exact RF]|].
      split; [eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU5 | exact WM5 | exact FWP]|].
      split; [| exists e3; exact HEB6].
      exists FA. split; [rewrite RF; exact HinF|].
      exists B, I. eexists (mkPJ _ _ _ _ _ _ _ _ _ _ _). exists pad, bs.
      split; [exact EPB|].
      split; [unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF, PK; cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_stats pk_oneshot]; exact CELLS|].
      split; [exact PRIV'|]. split; [exact BUF'|]. split; [exact PFX|]. split; [exact IFS'| exact WF]. }
    (* [comment removed for export] *)
    assert (FAIL : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' t3' t4' t5' t6' : word) (m3 : mem) (ps3 : PState H hptr)
                          (msg : list Z) (junk3 : list byte) (ec : cell) (mc : list cell),
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -48) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      GIo K R ps3 CL FB m3 ->
      rw_cells ssegs m3 (bv_unsigned sp + -48) [ec] -> csize ec = 4%nat -> rw_cells ssegs m3 (bv_unsigned sp + -44) mc -> cells_size mc = 4%nat ->
      rw_cells ssegs m3 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] -> Z.of_nat (length msg) < 256 ->
      Forall (fun z => 0 < z < 256)%Z msg -> ps_outfile ps3 = ps_outfile s ->
      evt ssegs (POSTQ (inl msg) ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x14484) fc None m3 (seg_rom ssegs))).
    { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' t3' t4' t5' t6' m3 ps3 msg junk3 ec mc MI3 ST3 AG3 G3 ERR3 Hec MG3 Hmc FRS3 HEB3 LEN3 RNG3 OFX.
      clear FRS ERRc HEB1 MG2 MI1 ST1 AG1 G1 G0 AGa.
      destruct (rw_cells_forget _ _ _ _ ERR3) as [ej3 ERR3']. clear ERR3. cbn [cells_size] in ERR3'. rewrite Hec in ERR3'. change (4 + 0)%nat with 4%nat in ERR3'.
      destruct (rw_cells_forget _ _ _ _ MG3) as [mj3 MG3']. clear MG3. rewrite Hmc in MG3'.
      hide HEB3.
      do 8 pstep.
      release_frame ERR3' ST3 (bv_unsigned sp + -44)%Z. release_frame MG3' ST3 (bv_unsigned sp + -40)%Z. release_frame FRS3 ST3 (bv_unsigned sp).
      unhide HEB3.
      apply evt_done; subst POSTQ; unfold open_result_post.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [solve [assumption | congruence] |].
      split; [assumption|]. split; [assumption|]. split; [exact AG3|].
      exists junk3. split; [reflexivity|]. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB3|]. split; [exact LEN3| exact RNG3]. }
    destruct (Z.eq_dec (Z.of_nat (length got)) 4) as [L4|L4].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) L4). cbn [negb].
      destruct (rw_cells_cut _ _ _ 1 MG2) as [MG _]. clear MG2. cbn [firstn] in MG.
      replace (length got) with 4%nat in MG by lia.
      ienter. step. rewrite L4. if_false. do 6 step.
      name_sp sp (-48)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply (chk_any false) with (fuel := O);
          [ split; [exact G1|]; split; [rewrite Hsp; exact ST1|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L2_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
          | exact HinF | rewrite SITES, Hsp; unfold D_FOPEN_OFFLINE, D_CHECK_HEADER; f_equal; lia
          | reflexivity | reflexivity | reflexivity | reflexivity | exact Esp
          | exact MG | exact GR | lia | exact HEB1 | exact ERRc | reflexivity
          | rewrite Hsp; lia | lia | lia | rewrite Hsp; lia | lia | lia | apply aligned16_4; [exact ALN| reflexivity] | exact E8 ]. }
      intros [|msg|p] ps3 ms3 PO; unfold check_header_post in PO;
        destruct PO as (av & m3 & errw & E & OF3 & MI3 & ST3 & AG3 & MG3 & ERR3 & REST);
        unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hsp in *; unname_sp;
        replace (ret_pc (Z_to_bv 64 82736)) with (Z_to_bv 64 82736) by (symmetry; apply ret_pc_even; [(keep_hyps CEILV sp EB got; lia)|reflexivity]);
        (assert (FRS3 : rw_cells ssegs m3 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
           by (eapply agrees_rw_cells; [exact AG3 | exact FRS | intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; (keep_hyps CEILV sp EB got a Ha; lia)| (keep_hyps CEILV sp R lo EB got a E1 Ha; lia)]]));
        pose proof (agrees_on_trans _ _ _ _ AGa (agrees_on_trans _ _ _ _
                      (WKG _ _ _ AG1 ltac:(intros a [Ha|[Ha Hc]] Hn; cbv beta; (split; [|(keep_hyps CEILV sp EB got a Ha R lo LO BU SPW Hc; lia)]); [left; (keep_hyps CEILV sp EB got a Ha; lia)| right; exact Ha]))
                      (WKG _ _ _ AG3 ltac:(intros a [Ha|[Ha Hc]] Hn; cbv beta; (split; [|(keep_hyps CEILV sp EB got a Ha Hn R lo LO BU E1 SPW Hc; lia)]); [left; (keep_hyps CEILV sp EB got a Ha; lia)| right; exact Ha])))) as AG03.
      + (* [comment removed for export] *)
        destruct REST as (-> & -> & G3 & [e3 HEB3]).
        ienter. step. if_true. step. step. if_false. do 6 step.
        name_sp sp (-48)%Z.
        apply evt_done. eapply (implM_bind ssegs).
        { eapply (chk_any true);
            [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L2_STACK; rewrite Hsp; lia|];
              split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
            | exact HinF | rewrite SITES, Hsp; unfold D_FOPEN_OFFLINE, D_CHECK_HEADER; f_equal; lia
            | reflexivity | reflexivity | reflexivity | reflexivity | exact Esp
            | exact MG3 | exact GR | lia | exact HEB3 | exact ERR3 | reflexivity
            | rewrite Hsp; lia | lia | lia | rewrite Hsp; lia | lia | lia | apply aligned16_4; [exact ALN| reflexivity] | exact E8 ]. }
        intros [|msg|p] ps4 ms4 PO; unfold check_header_post in PO;
          destruct PO as (av4 & m4 & errw4 & E & OF4 & MI4 & ST4 & AG4 & MG4 & ERR4 & REST);
          unfold hpost_regs in E; destruct_exs E; subst ms4; rewrite Hsp in *; unname_sp;
          replace (ret_pc (Z_to_bv 64 83020)) with (Z_to_bv 64 83020) by (symmetry; apply ret_pc_even; [(keep_hyps CEILV sp EB got; lia)|reflexivity]);
          (assert (FRS4 : rw_cells ssegs m4 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
             by (eapply agrees_rw_cells; [exact AG4 | exact FRS3 | intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; (keep_hyps CEILV sp EB got a Ha; lia)| (keep_hyps CEILV sp R lo EB got a E1 Ha; lia)]]));
          pose proof (agrees_on_trans _ _ _ _ AG03 (WKG _ _ _ AG4 ltac:(intros a [Ha|[Ha Hc]] Hn; cbv beta; (split; [|(keep_hyps CEILV sp EB got a Ha Hn R lo LO BU E1 SPW Hc; lia)]); [left; (keep_hyps CEILV sp EB got a Ha; lia)| right; exact Ha]))) as AG04.
        * (* [comment removed for export] *)
          destruct REST as (-> & -> & G4 & [e4 HEB4]).
          assert (U64 : usp0 R < 2^64) by (unfold usp0; pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as X; unfold bv_modulus in X; cbn in X; lia).
          unfold rc_spmain in E2.
          pose proof (rw_cells_bound _ _ _ _ HEB4) as BE4. cbn [cells_size csize Nat.add] in BE4.
          apply (rw_cells_split_CB ssegs _ _ [] 256 _ [] [20; 236]%nat) in HEB4; [|reflexivity]. cbn [mk_CB_cells app] in HEB4.
          destruct (rw_cells_cut _ _ _ 1 HEB4) as [EB1 EB2]. clear HEB4. cbn [firstn skipn cells_size csize Nat.add] in EB1, EB2.
          replace (EB + Z.of_nat 20)%Z with (EB + 20)%Z in EB2 by lia.
          set (UFF := [Z_to_bv 8 117; Z_to_bv 8 110; Z_to_bv 8 107; Z_to_bv 8 110; Z_to_bv 8 111; Z_to_bv 8 119; Z_to_bv 8 110; Z_to_bv 8 32; Z_to_bv 8 102; Z_to_bv 8 105;
                       Z_to_bv 8 108; Z_to_bv 8 101; Z_to_bv 8 32; Z_to_bv 8 102; Z_to_bv 8 111; Z_to_bv 8 114; Z_to_bv 8 109; Z_to_bv 8 97; Z_to_bv 8 116; Z_to_bv 8 0]).
          assert (MSGB : bytes_at ssegs m4 0x10457 UFF).
          { exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m4 0x10457 UFF MI4 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
          assert (EUFF : map b8 Msg.unknown_file_format ++ [Z_to_bv 8 0] = UFF) by (vm_compute; reflexivity).
          hide EB2.
          pose proof (munch_refl [(EB, EB + 20)]%Z m4) as MU4. pose proof (wmono_refl ssegs m4) as WM4.
          apply (implM_ret ssegs). step. if_false. step. step. if_false. do 6 step.
          call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB 0x10457%Z 20%Z UFF (firstn 20 e4));
            [reflexivity | reflexivity | reflexivity | exact MSGB | reflexivity | (keep_hyps CEILV sp EB got; lia) | exact EB1 | (keep_hyps CEILV sp R lo EB got LO BU E1 SPW; lia) | (keep_hyps CEILV sp EB got BE4; lia) | (keep_hyps CEILV sp EB got; lia) | assumption |].
          step. unhide EB2.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            assert (G5 : GIo K R ps4 CL FB mm)
              by (eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MU4 | exact WM4 |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia| apply Forall_nil]);
            assert (AG45 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m4 mm)
              by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 |]; intros a _ [_ Hn]; cbn [outside]; lia);
            assert (EB2' : rw_cells ssegs mm (EB + 20) [CB 236 (firstn 236 (skipn 20 e4))])
              by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho] | exact EB2 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
            lazymatch goal with E1' : rw_cells _ mm EB _ |- _ =>
              change (Z.to_nat 20) with 20%nat in E1';
              pose proof (rw_cells_uncut _ _ _ _ _ E1' EB2' ltac:(reflexivity)) as HEB5 end
          end.
          rewrite <- EUFF in HEB5. cbn [app] in HEB5.
          eapply FAIL; [assumption | assumption | exact (agrees_on_trans _ _ _ _ AG04 AG45) | exact G5 | eassumption | reflexivity | eassumption | reflexivity | assumption
                       | exact HEB5 | vm_compute; reflexivity | apply snprintf_ok; [vm_compute; reflexivity| constructor] | congruence].
        * (* [comment removed for export] *)
          destruct REST as (junk4 & -> & -> & G4 & HEB4 & LEN4 & RNG4).
          apply (implM_ret ssegs). step. if_false. step. step. if_true.
          eapply FAIL; [assumption | assumption | exact AG04 | exact G4 | exact ERR4 | reflexivity | exact MG4 | reflexivity | exact FRS4 | exact HEB4 | exact LEN4 | exact RNG4 | congruence].
        * (* [comment removed for export] *)
          destruct REST as (P & PB & -> & G4 & PPC & RF & [e4 HEB4]).
          pose proof PPC as (rf0 & st0 & os0 & _ & _ & _ & PG0). destruct (PCAPRg_blocks _ _ _ _ _ _ _ PG0) as (B0 & I0 & EPB0).
          pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G4 ltac:(rewrite EPB0; left; reflexivity)) as (Q1 & _ & _ & Q4 & _). pose proof (psize_pos p) as PS0.
          unfold implM. iprefix. step. if_true_by (nez_true P ltac:(lia)).
          apply evt_done. eapply FOUND; [exact RF | assumption | assumption | exact AG04 | exact G4 | exact PPC | exact ERR4 | exact MG4 | exact FRS4 | exact HEB4 | congruence].
      + (* [comment removed for export] *)
        destruct REST as (junk3 & -> & -> & G3 & HEB3 & LEN3 & RNG3).
        apply (implM_ret ssegs). step. if_true. step. step. if_true.
        eapply FAIL; [assumption | assumption | exact AG03 | exact G3 | exact ERR3 | reflexivity | exact MG3 | reflexivity | exact FRS3 | exact HEB3 | exact LEN3 | exact RNG3 | congruence].
      + (* [comment removed for export] *)
        destruct REST as (P & PB & -> & G3 & PPC & RF & [e3 HEB3]).
        pose proof PPC as (rf0 & st0 & os0 & _ & _ & _ & PG0). destruct (PCAPRg_blocks _ _ _ _ _ _ _ PG0) as (B0 & I0 & EPB0).
        pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G3 ltac:(rewrite EPB0; left; reflexivity)) as (Q1 & _ & _ & Q4 & _). pose proof (psize_pos p) as PS0.
        unfold implM. iprefix. step. if_false_by (eqz_false P ltac:(lia)).
        apply evt_done. eapply FOUND; [exact RF | assumption | assumption | exact AG03 | exact G3 | exact PPC | exact ERR3 | exact MG3 | exact FRS3 | exact HEB3 | congruence].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) L4). cbn [negb].
      apply (implM_bind_assoc ssegs).
      ienter. step. rewrite (eqb_lits_false (Z.of_nat (length got)) 4) by lia. cbn [negb]. cbv iota. do 3 step.
      name_sp sp (-48)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [|] ps3 ms3 PO; cbv beta in PO; destruct PO as (av & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO);
        unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hsp in *; unname_sp;
        replace (ret_pc (Z_to_bv 64 82952)) with (Z_to_bv 64 82952) by (symmetry; apply ret_pc_even; [(keep_hyps CEILV sp EB got; lia)|reflexivity]);
        (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FRS; [|(keep_hyps CEILV sp EB got; lia)]); (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in ERRc; [|(keep_hyps CEILV sp EB got; lia)]);
        (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in MG2; [|(keep_hyps CEILV sp EB got; lia)]);
        (assert (HEB3 : rw_cells ssegs m3 EB [CB 256 ej]) by (eapply agrees_rw_cells; [exact AG3 | exact HEB1 | intros a Ha; left; (keep_hyps CEILV sp R lo EB ej got a E1 Ha; lia)]));
        pose proof (agrees_on_trans _ _ _ _ AGa (agrees_on_trans _ _ _ _
                      (WKG _ _ _ AG1 ltac:(intros a [Ha|[Ha Hc]] Hn; cbv beta; (split; [|(keep_hyps CEILV sp EB got a Ha R lo LO BU SPW Hc; lia)]); [left; (keep_hyps CEILV sp EB got a Ha; lia)| right; exact Ha]))
                      (WKG _ _ _ AG3 ltac:(intros a [Ha|[Ha Hc]] Hn; cbv beta; [left; (keep_hyps CEILV sp EB got a Ha; lia)| right; exact Ha])))) as AG03;
        clear MI1 HEB1.
      + (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
        pose proof (GIo_tls K _ _ _ _ _ G3) as [_ TB]. unfold tls_block_ok in TB.
        unfold utp in EN2. rewrite <- TP in EN2.
        eapply implM_pure; [reflexivity|]. cbn [fst snd].
        set (e := lc_errno (ps_libc s')) in *.
        hide HEB3.
        cbn [Z.b2z]. step. if_false. do 10 step.
        replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
        unhide HEB3.
        assert (MSG : fmt_at m3 0x108d6 "error reading dump file"%string).
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m3 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        name_sp sp (-48)%Z.
        eapply evt_cut.
        { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 0x108d6%Z e "error reading dump file"%string [] ej);
            [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB3
             | right; rewrite Hsp; lia | exact E8 ].
          split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
        cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & junk4 & -> & MI4 & ST4 & AG4 & G4 & HEB4).
        rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 82984)) with (Z_to_bv 64 82984) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (KEEP4 : forall A cs, rw_cells ssegs m3 A cs -> (bv_unsigned sp + -48 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells ssegs m4 A cs).
        { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG4 | exact HC | intros a Ha; split; [left; lia| lia]]. }
        apply KEEP4 in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP4 in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia].
        apply KEEP4 in MG2; [|lia|cbn [cells_size csize Nat.add]; lia]. clear KEEP4.
        hide HEB4. step. unhide HEB4.
        eapply FAIL; [assumption | assumption | | exact G4 | exact ERRc | reflexivity | exact MG2 | cbn [cells_size csize Nat.add]; lia | exact FRS | exact HEB4
                     | pose proof (fmt_errmsg_length "error reading dump file"%string [] e); lia
                     | apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor] | congruence].
        eapply agrees_on_trans; [exact AG03|]. eapply agrees_on_weaken; [exact AG4|]. intros a [[Ha|Ha] Hn]; (split; [|exact Hn]); [left; lia| right; exact Ha].
      + (* [comment removed for export] *)
        eapply implM_pure; [reflexivity|]. cbn [fst snd].
        hide HEB3.
        cbn [Z.b2z]. step. if_true. do 7 step.
        unhide HEB3.
        assert (MSG : fmt_at m3 0x1050c "truncated dump file; tried to read %zu file header bytes, only got %zu"%string).
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m3 0x1050c (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %zu file header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                   MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        name_sp sp (-48)%Z.
        eapply evt_cut.
        { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 256%Z 0x1050c%Z
                    "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 4; AInt (Z.of_nat (length got))] ej);
            [| reflexivity | reflexivity | reflexivity | lia | exact MSG | vm_compute; reflexivity | cbn; lia | | exact HEB3 | right; rewrite Hsp; lia].
          { split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
            split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
          cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
        cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
        unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 83076)) with (Z_to_bv 64 83076) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -48 - STDIO_STACK, bv_unsigned sp + -48); (EB, EB + 256)]%Z a) m3 m4)
          by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
        unfold STDIO_STACK in AGS.
        assert (KEEP4 : forall A cs, rw_cells ssegs m3 A cs -> (bv_unsigned sp + -48 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells ssegs m4 A cs).
        { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AGS | exact HC | intros a Ha; cbn [outside]; lia]. }
        apply KEEP4 in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP4 in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia].
        apply KEEP4 in MG2; [|lia|cbn [cells_size csize Nat.add]; lia]. clear KEEP4.
        assert (G4 : GIo K R s' CL FB m4).
        { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |].
          apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, STDIO_STACK; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
        change (Z.to_nat 256) with 256%nat in HEB4.
        replace (256 - length (Fmt.snprintf 256 "truncated dump file; tried to read %zu file header bytes, only got %zu" [AInt 4; AInt (Z.of_nat (length got))]) - 1)%nat
          with (255 - length (Fmt.snprintf 256 "truncated dump file; tried to read %zu file header bytes, only got %zu" [AInt 4; AInt (Z.of_nat (length got))]))%nat in HEB4 by lia.
        eapply FAIL; [assumption | assumption | | exact G4 | exact ERRc | reflexivity | exact MG2 | cbn [cells_size csize Nat.add]; lia | exact FRS | exact HEB4
                     | pose proof (snprintf_length 256 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 4; AInt (Z.of_nat (length got))]) as LS;
                       change (Z.to_nat (256 - 1)) with 255%nat in LS; unfold Msg.trunc_file_header, PCAP_ERRBUF_SIZE; lia
                     | unfold Msg.trunc_file_header; apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] | congruence].
        eapply agrees_on_trans; [exact AG03|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] Hn]; cbn [outside]; [lia|]. pose proof (CLB a Ha). unfold rc_lo in LO. split; [lia|]. split; [exact Hn| exact Logic.I].
  Qed.
  End Sz6.
  Theorem fopen_offline_proof : ltac:(let t := eval cbv delta [fopen_offline_proof__stmt] in fopen_offline_proof__stmt in exact t).
  Proof using CHK_NG CHK_PCAP FERROR FILENO FMT FREAD HFL SFL SNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo FA EB f ej fuel. ltac2:(SecDiet.SzSec.closeP 'fopen_offline_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FopenOffline.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB.
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

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma implM_mget : forall {St A} (k : St -> @M St A) s Q ms, implM usegs (k s) s Q ms -> implM usegs (mbind mget k) s Q ms.
Proof using Type. pin_using tt. intros St A k s Q ms H. exact H. Qed.

Lemma map_unsigned_b8 : forall l, Forall (fun z => 0 <= z < 256)%Z l -> map bv_unsigned (map b8 l) = l.
Proof using Type. pin_using tt.
  induction l as [|x l IH]; intros HF; [reflexivity|]. apply Forall_cons_iff in HF as [Hx HF]. cbn [map]. f_equal; [|apply IH; exact HF].
  unfold b8. apply Z_to_bv_small. unfold bv_modulus. cbn. lia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac merge_cells H k n :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let pre := eval cbv beta iota delta [firstn skipn] in (firstn k cs) in
      let mid := eval cbv beta iota delta [firstn skipn] in (firstn n (skipn k cs)) in
      let post := eval cbv beta iota delta [firstn skipn Nat.add] in (skipn (k + n) cs) in
      change cs with (pre ++ mid ++ post) in H;
      apply (rw_cells_merge segs m A pre mid post) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac pstep := step; fix_lit_store.

(* [comment removed for export] *)
Ltac norm_addr H P :=
  lazymatch type of H with
  | rw_cells _ _ (?b + Z.of_nat ?n)%Z _ =>
      lazymatch b with
      | (P + ?k0)%Z => let k := eval vm_compute in (k0 + Z.of_nat n)%Z in replace (b + Z.of_nat n)%Z with (P + k)%Z in H by lia
      | P => let k := eval vm_compute in (Z.of_nat n) in replace (P + Z.of_nat n)%Z with (P + k)%Z in H by lia
      end
  end.
(* [comment removed for export] *)
Ltac cut_cells H k H1 P :=
  let H2 := fresh "TMP" in
  destruct (rw_cells_cut _ _ _ k H) as [H1 H2]; clear H; cbn [firstn skipn cells_size csize Nat.add] in H1, H2;
  norm_addr H2 P; rename H2 into H.
(* [comment removed for export] *)
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
(* [comment removed for export] *)
Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells ?s ?m ?A1 ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    let J := fresh "J" in
    pose proof (rw_cells_uncut m A1 cs1 cs2 A2 H1 H2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J;
    clear H1 H2; cbn [app] in J; rename J into H1
  end end.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma snprintf_length : forall n f a, (length (Fmt.snprintf n f a) <= Z.to_nat (n - 1))%nat.
Proof using Type. pin_using tt. intros. unfold Fmt.snprintf, snprintf_out. apply firstn_le_length. Qed.


(* [comment removed for export] *)
Lemma aligned16_4 : forall x k, (x mod 16 = 0)%Z -> (k mod 4 = 0)%Z -> ((x + k) mod 4 = 0)%Z.
Proof using Type. pin_using tt.
  intros x k Hx Hk. rewrite Z.add_mod, Hk, Z.add_0_r by lia. rewrite Z.mod_mod by lia.
  apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->]. replace (q * 16)%Z with ((q * 4) * 4)%Z by lia. apply Z.mod_mul.
  all: lia.
Qed.

Section FopenOffline.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FILENO : fileno_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis CHK_PCAP : pcap_check_header_stmt HO K sites.
  Hypothesis CHK_NG : pcap_ng_check_header_stmt HO K sites.
  Lemma chk_any : forall ng, check_header_stmt_for HO K sites ng.
  Proof using CHK_NG CHK_PCAP. pin_using (fun (CHK_NG CHK_PCAP : unit) => tt). intros [|]; [exact CHK_NG | exact CHK_PCAP]. Qed.

  Definition fopen_offline_proof__stmt : Prop := fopen_offline_stmt HO K sites.
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo FA EB f ej fuel : ltac2:(SecDiet.SzSec.tyM 'fopen_offline_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fopen_offline_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_offline_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CHK_NG CHK_PCAP FERROR FILENO FMT FREAD HFL SFL SNPRINTF. pin_using (fun (CHK_NG CHK_PCAP FERROR FILENO FMT FREAD HFL SFL SNPRINTF : unit) => tt).
 intros PRE HinF SITES -> -> -> HEB E1 E2 E8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & A5 & _).
    cbn [cb_addr cb_size fst snd] in A1, A4, A5. unfold FILE_BLOCK in A4, A5.
    assert (EBX : CEILZ <= bv_unsigned sp) by (unfold rc_lo in *; lia).
    unfold pcap_fopen_offline_with_tstamp_precision, read_fail_msg, errmsg_for_errno.
    cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_fileno e_last_errno prims]. unfold PCAP_FOPEN_OFFLINE_WTP_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide HEB.
    ienter. carve_frame 48%nat ST. do 8 step. if_false_by (eqz_false FA ltac:(lia)). do 8 step.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs _ _ [] 8 _ _ [4; 4]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (rw_cells_cut _ _ _ 1 FR) as [ERRc FR']. clear FR. cbn [firstn skipn cells_size csize Nat.add] in ERRc, FR'.
    destruct (rw_cells_cut _ _ _ 1 FR') as [MGc FRS]. clear FR'. cbn [firstn skipn cells_size csize Nat.add] in MGc, FRS.
    replace (bv_unsigned sp + -48 + Z.of_nat 4 + Z.of_nat 4)%Z with (bv_unsigned sp + -40)%Z in FRS by lia.
    replace (bv_unsigned sp + -48 + Z.of_nat 4)%Z with (bv_unsigned sp + -44)%Z in MGc by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R s CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AGa : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|Ha] Hn]; cbn [outside]; [lia|];
            destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]; lia);
      unhide HEB; assert (HEB1 : rw_cells usegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia])
    end.
    clear MU WM HEB.
    (* [comment removed for export] *)
    name_sp sp (-48)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop]. rewrite SITES. unfold sites_at, D_FOPEN_OFFLINE.
      replace (bv_unsigned sp + 48 - 92 + 0)%Z with (bv_unsigned sp + -44)%Z by lia.
      eapply FREAD; [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact MGc | right; rewrite Hsp; lia]. }
    intros got s' ms' PO. cbv beta in PO.
    destruct PO as (av & m2 & junk' & E & OF1 & MI1 & ST1 & AG1 & G1 & -> & GL & GR & MG2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 82904)) with (Z_to_bv 64 82904) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (KEEP : forall A cs, rw_cells usegs m0 A cs -> (bv_unsigned sp + -48 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -44 \/ bv_unsigned sp + -40 <= A)%Z -> rw_cells usegs m2 A cs).
    { intros A cs HC HA HD. eapply agrees_rw_cells; [exact AG1 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KEEP in HEB1; [|lia|cbn [cells_size csize Nat.add]; lia]. clear KEEP MI MGc.
    unfold zlength in *.
    assert (WK : forall (PB : list cblock) mA mB, agrees_on (client_keeps (CL ++ PB) (bv_unsigned sp + -48)) mA mB ->
                 agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z mA mB).
    { intros PB mA mB AG. eapply agrees_on_weaken; [exact AG|]. intros a [[Ha|Ha] Hn]; [left; lia| right; apply in_block_app; left; exact Ha]. }
    assert (CLB : forall a, in_block CL a -> a < CEILZ).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. lia. }
    (* [comment removed for export] *)
    assert (WKG : forall (Pr : Z -> Prop) mA mB, agrees_on Pr mA mB ->
                 (forall a, (bv_unsigned sp <= a \/ (in_block CL a /\ a < CEILZ)) -> ~ (EB <= a < EB + 256) -> Pr a)%Z ->
                 agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z mA mB).
    { intros Pr mA mB AG HP. eapply agrees_on_weaken; [exact AG|]. intros a [[Ha|Ha] Hn]; apply HP; [left; exact Ha| exact Hn | | exact Hn].
      right. split; [exact Ha| apply CLB; exact Ha]. }
    (* [comment removed for export] *)
    assert (FOUND : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' : word) (m3 : mem) (ps3 : PState H hptr)
                           (P : Z) (PB : list cblock) (p : pcap hptr hptr) (e3 : list byte) (errw : word),
      pc_rfile p = f -> mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -48) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      GIo K R ps3 (CL ++ PB) FB m3 -> pre_PCAPR (hptr:=hptr) P p PB m3 ->
      rw_cells usegs m3 (bv_unsigned sp + -48) [C4 errw] -> rw_cells usegs m3 (bv_unsigned sp + -44) [CB 4 (map b8 got)] ->
      rw_cells usegs m3 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> rw_cells usegs m3 EB [CB 256 e3] -> ps_outfile ps3 = ps_outfile s ->
      implM usegs (mbind (s_fileno HO f) (fun _ => mret (inr p))) ps3 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 FA) (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x143f8) fc None m3 (seg_rom usegs))).
    { intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m3 ps3 P PB p e3 errw RF MI3 ST3 AG3 G3 PPC ERR3 MG3 FRS3 HEB3 OFX.
      clear FRS ERRc HEB1 MG2 MI1 ST1 AG1 G1 G0 AGa.
      destruct PPC as (rf & st & os & Lrf & Lst & Los & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G3 ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
      pose proof (psize_pos p) as PS.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
      hide PRIV. hide BUF. hide IFS. hide HEB3.
      assert (NB : forall a, in_block CL a -> ~ (P <= a < P + 648)%Z).
      { intros a Ha Hin. destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G3 Ha) as [_ Hnb]. apply Hnb. rewrite EPB. unfold pcap_blocks, in_block.
        apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (FWP : Forall (pcap_iv R PB) [(P, P + 648)]%Z).
      { apply Forall_cons; [| apply Forall_nil]. right. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      pose proof (munch_refl [(P, P + 648)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
      assert (P8 : (P mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r P); apply aligned16_8; [exact P2| reflexivity]).
      ienter. step. rewrite (and7_aligned P) by lia. step. if_false. do 5 step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (G3' : GIo K R ps3 (CL ++ PB) FB mm) by (eapply (GIo_pcap_frame K HFL SFL); [exact G3 | exact MU3 | exact WM3 | exact FWP]);
        assert (AG34 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m3 mm)
          by (eapply agrees_on_of_munch; [exact MU3 | exact WM3|]; intros a _ [[Ha|Ha] Hn]; cbn [outside]; [unfold rc_lo in LO; lia| split; [apply NB; exact Ha| exact Logic.I]]);
        assert (AGP34 : agrees_on (fun a => outside [(P, P + 648)]%Z a) m3 mm) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3| intros a _ Ho; exact Ho])
      end.
      clear MU3 WM3.
      name_sp sp (-48)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply FILENO; [| exact HinF | reflexivity].
        split; [exact G3'|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros fd ps5 ms5 PO. cbv beta in PO. destruct PO as (av & m5 & E & MI5 & ST5 & AG5 & G5 & -> & -> & Hfd).
      unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 82964)) with (Z_to_bv 64 82964) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG5) in FRS3; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ AG5) in ERR3; [|lia].
      apply (keeps_rw_cells_stack _ _ _ _ _ _ AG5) in MG3; [|lia].
      assert (HinP : forall a, (P <= a < P + 648)%Z -> in_block (CL ++ PB) a).
      { intros a Ha. apply in_block_app. right. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      apply (keeps_rw_cells_block _ _ _ _ _ _ AG5) in CELLS; [|intros a Ha; apply HinP; cbn [cells_size csize Nat.add] in Ha; lia].
      pose proof (GIo_got_pcap K _ _ _ _ _ G5) as GOT. unfold PK, GOT_PCAP_ADDR, GOT_INSTALL_BPF, GOT_BREAKLOOP in GOT; cbn [pk_oneshot pk_cleanup_sf] in GOT.
      pose proof (munch_refl [(P, P + 648)]%Z m5) as MU5. pose proof (wmono_refl usegs m5) as WM5.
      apply (implM_ret usegs).
      (* [comment removed for export] *)
      cut_cells CELLS 1%nat X0 P. cut_cells CELLS 9%nat X1 P. cut_cells CELLS 1%nat X2 P. cut_cells CELLS 2%nat X3 P.
      cut_cells CELLS 5%nat X4 P. cut_cells CELLS 1%nat X5 P. cut_cells CELLS 3%nat X6 P. cut_cells CELLS 1%nat X7 P.
      cut_cells CELLS 6%nat X8 P. cut_cells CELLS 1%nat X9 P. cut_cells CELLS 1%nat X10 P. cut_cells CELLS 1%nat X11 P.
      cut_cells CELLS 1%nat X12 P. rename CELLS into X13.
      (* [comment removed for export] *)
      do 46 pstep.
      all: release_frame ERR3 ST5 (bv_unsigned sp + -44)%Z; release_frame MG3 ST5 (bv_unsigned sp + -40)%Z; release_frame FRS3 ST5 (bv_unsigned sp).
      (* [comment removed for export] *)
      all: merge_all X3; merge_all X5; merge_all X7; merge_all X9.
      all: join_cells X0 X1; join_cells X0 X2; join_cells X0 X3; join_cells X0 X4; join_cells X0 X5; join_cells X0 X6; join_cells X0 X7;
           join_cells X0 X8; join_cells X0 X9; join_cells X0 X10; join_cells X0 X11; join_cells X0 X12; join_cells X0 X13.
      all: rename X0 into CELLS.
      unhide PRIV. unhide BUF. unhide IFS. unhide HEB3.
      pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G3 EPB) as [APB API].
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G3 ltac:(rewrite EPB; right; left; reflexivity)) as (R1 & R2 & R3 & R4 & R5 & R6).
      pose proof WF as (_ & _ & W3 & _).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGP56 : agrees_on (fun a => outside [(P, P + 648)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU5 | exact WM5| intros a _ Ho; exact Ho]);
        assert (AGX : agrees_on (fun a => (in_block (CL ++ PB) a \/ bv_unsigned sp <= a) /\ ~ (P <= a < P + 648))%Z m3 mm)
          by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGP34|]; intros a [_ Hn]; cbn [outside]; split; [exact Hn| exact Logic.I]|];
              eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a [[Ha|Ha] Hn]; [right; exact Ha| left; (keep_hyps CEILV sp EB got P rf st os B a Ha; lia)]|];
              eapply agrees_on_weaken; [exact AGP56|]; intros a [_ Hn]; cbn [outside]; split; [exact Hn| exact Logic.I]);
        destruct (pcap_aux_agree p P B I pad bs m3 mm _ AGX) as (BUF' & PRIV' & IFS');
          [ intros a Ha; split; [left; apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; (keep_hyps CEILV hptr sp EB got P p rf st os B a Ha; lia)| (keep_hyps CEILV hptr sp R lo EB got P p rf st os B a PS APB Ha; lia)]
          | intros a Ha; unfold PCAP_PRIV_OFF in Ha; split; [left; apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; (keep_hyps CEILV hptr sp EB got P p rf st os B a Ha; lia)| unfold PCAP_PRIV_OFF in *; (keep_hyps CEILV hptr sp EB got P p rf st os B a Ha; lia)]
          | intros sg q Hq a Ha; destruct (API sg q Hq) as [X1 X2];
            split; [left; apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; rewrite Hq; do 2 apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; (keep_hyps CEILV sp EB got P rf st os B I sg a Ha; lia)| (keep_hyps CEILV hptr sp R lo EB got P p rf st os B I sg a PS Ha X1; lia)]
          | (keep_hyps CEILV hptr sp EB got P p rf st os B R3; lia) | exact BUF | exact PRIV | exact IFS |];
        assert (HEB6 : rw_cells usegs mm EB [CB 256 e3])
          by (eapply agrees_rw_cells; [exact AGX | exact HEB3 | intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; (keep_hyps CEILV sp R lo EB got P rf st os B a E1 Ha; lia)| unfold rc_lo in LO; (keep_hyps CEILV hptr sp R lo EB got P p rf st os B a LO BU E1 SPW P4 PS Ha; lia)]]);
        apply evt_done; subst POSTQ; unfold open_result_post; exists (Z_to_bv 64 P), mm, FB
      end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [solve [assumption | congruence] |].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_trans; [exact AG34|]. eapply agrees_on_trans; [apply (WK PB); exact AG5|].
               eapply agrees_on_weaken; [exact AGP56|]. intros a [[Ha|Ha] Hn]; cbn [outside]; [unfold rc_lo in LO; lia| split; [apply NB; exact Ha| exact Logic.I]]. }
      exists P, PB. split; [reflexivity|]. split; [split; [reflexivity| exact RF]|].
      split; [eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU5 | exact WM5 | exact FWP]|].
      split; [| exists e3; exact HEB6].
      exists FA. split; [rewrite RF; exact HinF|].
      exists B, I. eexists (mkPJ _ _ _ _ _ _ _ _ _ _ _). exists pad, bs.
      split; [exact EPB|].
      split; [unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF, PK; cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_stats pk_oneshot]; exact CELLS|].
      split; [exact PRIV'|]. split; [exact BUF'|]. split; [exact PFX|]. split; [exact IFS'| exact WF]. }
    (* [comment removed for export] *)
    assert (FAIL : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' t3' t4' t5' t6' : word) (m3 : mem) (ps3 : PState H hptr)
                          (msg : list Z) (junk3 : list byte) (ec : cell) (mc : list cell),
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -48) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      GIo K R ps3 CL FB m3 ->
      rw_cells usegs m3 (bv_unsigned sp + -48) [ec] -> csize ec = 4%nat -> rw_cells usegs m3 (bv_unsigned sp + -44) mc -> cells_size mc = 4%nat ->
      rw_cells usegs m3 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] -> Z.of_nat (length msg) < 256 ->
      Forall (fun z => 0 < z < 256)%Z msg -> ps_outfile ps3 = ps_outfile s ->
      evt usegs (POSTQ (inl msg) ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1455c) fc None m3 (seg_rom usegs))).
    { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' t3' t4' t5' t6' m3 ps3 msg junk3 ec mc MI3 ST3 AG3 G3 ERR3 Hec MG3 Hmc FRS3 HEB3 LEN3 RNG3 OFX.
      clear FRS ERRc HEB1 MG2 MI1 ST1 AG1 G1 G0 AGa.
      destruct (rw_cells_forget _ _ _ _ ERR3) as [ej3 ERR3']. clear ERR3. cbn [cells_size] in ERR3'. rewrite Hec in ERR3'. change (4 + 0)%nat with 4%nat in ERR3'.
      destruct (rw_cells_forget _ _ _ _ MG3) as [mj3 MG3']. clear MG3. rewrite Hmc in MG3'.
      hide HEB3.
      do 8 pstep.
      release_frame ERR3' ST3 (bv_unsigned sp + -44)%Z. release_frame MG3' ST3 (bv_unsigned sp + -40)%Z. release_frame FRS3 ST3 (bv_unsigned sp).
      unhide HEB3.
      apply evt_done; subst POSTQ; unfold open_result_post.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [solve [assumption | congruence] |].
      split; [assumption|]. split; [assumption|]. split; [exact AG3|].
      exists junk3. split; [reflexivity|]. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB3|]. split; [exact LEN3| exact RNG3]. }
    destruct (Z.eq_dec (Z.of_nat (length got)) 4) as [L4|L4].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) L4). cbn [negb].
      destruct (rw_cells_cut _ _ _ 1 MG2) as [MG _]. clear MG2. cbn [firstn] in MG.
      replace (length got) with 4%nat in MG by lia.
      ienter. step. rewrite L4. if_false. do 6 step.
      name_sp sp (-48)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply (chk_any false) with (fuel := O);
          [ split; [exact G1|]; split; [rewrite Hsp; exact ST1|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L2_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
          | exact HinF | rewrite SITES, Hsp; unfold D_FOPEN_OFFLINE, D_CHECK_HEADER; f_equal; lia
          | reflexivity | reflexivity | reflexivity | reflexivity | exact Esp
          | exact MG | exact GR | lia | exact HEB1 | exact ERRc | reflexivity
          | rewrite Hsp; lia | lia | lia | rewrite Hsp; lia | lia | lia | apply aligned16_4; [exact ALN| reflexivity] | exact E8 ]. }
      intros [|msg|p] ps3 ms3 PO; unfold check_header_post in PO;
        destruct PO as (av & m3 & errw & E & OF3 & MI3 & ST3 & AG3 & MG3 & ERR3 & REST);
        unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hsp in *; unname_sp;
        replace (ret_pc (Z_to_bv 64 82932)) with (Z_to_bv 64 82932) by (symmetry; apply ret_pc_even; [(keep_hyps CEILV sp EB got; lia)|reflexivity]);
        (assert (FRS3 : rw_cells usegs m3 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
           by (eapply agrees_rw_cells; [exact AG3 | exact FRS | intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; (keep_hyps CEILV sp EB got a Ha; lia)| (keep_hyps CEILV sp R lo EB got a E1 Ha; lia)]]));
        pose proof (agrees_on_trans _ _ _ _ AGa (agrees_on_trans _ _ _ _
                      (WKG _ _ _ AG1 ltac:(intros a [Ha|[Ha Hc]] Hn; cbv beta; (split; [|(keep_hyps CEILV sp EB got a Ha R lo LO BU SPW Hc; lia)]); [left; (keep_hyps CEILV sp EB got a Ha; lia)| right; exact Ha]))
                      (WKG _ _ _ AG3 ltac:(intros a [Ha|[Ha Hc]] Hn; cbv beta; (split; [|(keep_hyps CEILV sp EB got a Ha Hn R lo LO BU E1 SPW Hc; lia)]); [left; (keep_hyps CEILV sp EB got a Ha; lia)| right; exact Ha])))) as AG03.
      + (* [comment removed for export] *)
        destruct REST as (-> & -> & G3 & [e3 HEB3]).
        ienter. step. if_true. step. step. if_false. do 6 step.
        name_sp sp (-48)%Z.
        apply evt_done. eapply (implM_bind usegs).
        { eapply (chk_any true);
            [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L2_STACK; rewrite Hsp; lia|];
              split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
            | exact HinF | rewrite SITES, Hsp; unfold D_FOPEN_OFFLINE, D_CHECK_HEADER; f_equal; lia
            | reflexivity | reflexivity | reflexivity | reflexivity | exact Esp
            | exact MG3 | exact GR | lia | exact HEB3 | exact ERR3 | reflexivity
            | rewrite Hsp; lia | lia | lia | rewrite Hsp; lia | lia | lia | apply aligned16_4; [exact ALN| reflexivity] | exact E8 ]. }
        intros [|msg|p] ps4 ms4 PO; unfold check_header_post in PO;
          destruct PO as (av4 & m4 & errw4 & E & OF4 & MI4 & ST4 & AG4 & MG4 & ERR4 & REST);
          unfold hpost_regs in E; destruct_exs E; subst ms4; rewrite Hsp in *; unname_sp;
          replace (ret_pc (Z_to_bv 64 83236)) with (Z_to_bv 64 83236) by (symmetry; apply ret_pc_even; [(keep_hyps CEILV sp EB got; lia)|reflexivity]);
          (assert (FRS4 : rw_cells usegs m4 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
             by (eapply agrees_rw_cells; [exact AG4 | exact FRS3 | intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; (keep_hyps CEILV sp EB got a Ha; lia)| (keep_hyps CEILV sp R lo EB got a E1 Ha; lia)]]));
          pose proof (agrees_on_trans _ _ _ _ AG03 (WKG _ _ _ AG4 ltac:(intros a [Ha|[Ha Hc]] Hn; cbv beta; (split; [|(keep_hyps CEILV sp EB got a Ha Hn R lo LO BU E1 SPW Hc; lia)]); [left; (keep_hyps CEILV sp EB got a Ha; lia)| right; exact Ha]))) as AG04.
        * (* [comment removed for export] *)
          destruct REST as (-> & -> & G4 & [e4 HEB4]).
          assert (U64 : usp0 R < 2^64) by (unfold usp0; pose proof (bv_unsigned_in_range 64 (rc_sp0 R)) as X; unfold bv_modulus in X; cbn in X; lia).
          unfold rc_spmain in E2.
          pose proof (rw_cells_bound _ _ _ _ HEB4) as BE4. cbn [cells_size csize Nat.add] in BE4.
          apply (rw_cells_split_CB usegs _ _ [] 256 _ [] [20; 236]%nat) in HEB4; [|reflexivity]. cbn [mk_CB_cells app] in HEB4.
          destruct (rw_cells_cut _ _ _ 1 HEB4) as [EB1 EB2]. clear HEB4. cbn [firstn skipn cells_size csize Nat.add] in EB1, EB2.
          replace (EB + Z.of_nat 20)%Z with (EB + 20)%Z in EB2 by lia.
          set (UFF := [Z_to_bv 8 117; Z_to_bv 8 110; Z_to_bv 8 107; Z_to_bv 8 110; Z_to_bv 8 111; Z_to_bv 8 119; Z_to_bv 8 110; Z_to_bv 8 32; Z_to_bv 8 102; Z_to_bv 8 105;
                       Z_to_bv 8 108; Z_to_bv 8 101; Z_to_bv 8 32; Z_to_bv 8 102; Z_to_bv 8 111; Z_to_bv 8 114; Z_to_bv 8 109; Z_to_bv 8 97; Z_to_bv 8 116; Z_to_bv 8 0]).
          assert (MSGB : bytes_at usegs m4 0x10457 UFF).
          { exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m4 0x10457 UFF MI4 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
          assert (EUFF : map b8 Msg.unknown_file_format ++ [Z_to_bv 8 0] = UFF) by (vm_compute; reflexivity).
          hide EB2.
          pose proof (munch_refl [(EB, EB + 20)]%Z m4) as MU4. pose proof (wmono_refl usegs m4) as WM4.
          apply (implM_ret usegs). step. if_false. step. step. if_false. do 6 step.
          call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB 0x10457%Z 20%Z UFF (firstn 20 e4));
            [reflexivity | reflexivity | reflexivity | exact MSGB | reflexivity | (keep_hyps CEILV sp EB got; lia) | exact EB1 | (keep_hyps CEILV sp R lo EB got LO BU E1 SPW; lia) | (keep_hyps CEILV sp EB got BE4; lia) | (keep_hyps CEILV sp EB got; lia) | assumption |].
          step. unhide EB2.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            assert (G5 : GIo K R ps4 CL FB mm)
              by (eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MU4 | exact WM4 |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain; lia| apply Forall_nil]);
            assert (AG45 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m4 mm)
              by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 |]; intros a _ [_ Hn]; cbn [outside]; lia);
            assert (EB2' : rw_cells usegs mm (EB + 20) [CB 236 (firstn 236 (skipn 20 e4))])
              by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho] | exact EB2 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
            lazymatch goal with E1' : rw_cells _ mm EB _ |- _ =>
              change (Z.to_nat 20) with 20%nat in E1';
              pose proof (rw_cells_uncut _ _ _ _ _ E1' EB2' ltac:(reflexivity)) as HEB5 end
          end.
          rewrite <- EUFF in HEB5. cbn [app] in HEB5.
          eapply FAIL; [assumption | assumption | exact (agrees_on_trans _ _ _ _ AG04 AG45) | exact G5 | eassumption | reflexivity | eassumption | reflexivity | assumption
                       | exact HEB5 | vm_compute; reflexivity | apply snprintf_ok; [vm_compute; reflexivity| constructor] | congruence].
        * (* [comment removed for export] *)
          destruct REST as (junk4 & -> & -> & G4 & HEB4 & LEN4 & RNG4).
          apply (implM_ret usegs). step. if_false. step. step. if_true.
          eapply FAIL; [assumption | assumption | exact AG04 | exact G4 | exact ERR4 | reflexivity | exact MG4 | reflexivity | exact FRS4 | exact HEB4 | exact LEN4 | exact RNG4 | congruence].
        * (* [comment removed for export] *)
          destruct REST as (P & PB & -> & G4 & PPC & RF & [e4 HEB4]).
          pose proof PPC as (rf0 & st0 & os0 & _ & _ & _ & PG0). destruct (PCAPRg_blocks _ _ _ _ _ _ _ PG0) as (B0 & I0 & EPB0).
          pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G4 ltac:(rewrite EPB0; left; reflexivity)) as (Q1 & _ & _ & Q4 & _). pose proof (psize_pos p) as PS0.
          unfold implM. iprefix. step. if_true_by (nez_true P ltac:(lia)).
          apply evt_done. eapply FOUND; [exact RF | assumption | assumption | exact AG04 | exact G4 | exact PPC | exact ERR4 | exact MG4 | exact FRS4 | exact HEB4 | congruence].
      + (* [comment removed for export] *)
        destruct REST as (junk3 & -> & -> & G3 & HEB3 & LEN3 & RNG3).
        apply (implM_ret usegs). step. if_true. step. step. if_true.
        eapply FAIL; [assumption | assumption | exact AG03 | exact G3 | exact ERR3 | reflexivity | exact MG3 | reflexivity | exact FRS3 | exact HEB3 | exact LEN3 | exact RNG3 | congruence].
      + (* [comment removed for export] *)
        destruct REST as (P & PB & -> & G3 & PPC & RF & [e3 HEB3]).
        pose proof PPC as (rf0 & st0 & os0 & _ & _ & _ & PG0). destruct (PCAPRg_blocks _ _ _ _ _ _ _ PG0) as (B0 & I0 & EPB0).
        pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G3 ltac:(rewrite EPB0; left; reflexivity)) as (Q1 & _ & _ & Q4 & _). pose proof (psize_pos p) as PS0.
        unfold implM. iprefix. step. if_false_by (eqz_false P ltac:(lia)).
        apply evt_done. eapply FOUND; [exact RF | assumption | assumption | exact AG03 | exact G3 | exact PPC | exact ERR3 | exact MG3 | exact FRS3 | exact HEB3 | congruence].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) L4). cbn [negb].
      apply (implM_bind_assoc usegs).
      ienter. step. rewrite (eqb_lits_false (Z.of_nat (length got)) 4) by lia. cbn [negb]. cbv iota. do 3 step.
      name_sp sp (-48)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [|] ps3 ms3 PO; cbv beta in PO; destruct PO as (av & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO);
        unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hsp in *; unname_sp;
        replace (ret_pc (Z_to_bv 64 83156)) with (Z_to_bv 64 83156) by (symmetry; apply ret_pc_even; [(keep_hyps CEILV sp EB got; lia)|reflexivity]);
        (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FRS; [|(keep_hyps CEILV sp EB got; lia)]); (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in ERRc; [|(keep_hyps CEILV sp EB got; lia)]);
        (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in MG2; [|(keep_hyps CEILV sp EB got; lia)]);
        (assert (HEB3 : rw_cells usegs m3 EB [CB 256 ej]) by (eapply agrees_rw_cells; [exact AG3 | exact HEB1 | intros a Ha; left; (keep_hyps CEILV sp R lo EB ej got a E1 Ha; lia)]));
        pose proof (agrees_on_trans _ _ _ _ AGa (agrees_on_trans _ _ _ _
                      (WKG _ _ _ AG1 ltac:(intros a [Ha|[Ha Hc]] Hn; cbv beta; (split; [|(keep_hyps CEILV sp EB got a Ha R lo LO BU SPW Hc; lia)]); [left; (keep_hyps CEILV sp EB got a Ha; lia)| right; exact Ha]))
                      (WKG _ _ _ AG3 ltac:(intros a [Ha|[Ha Hc]] Hn; cbv beta; [left; (keep_hyps CEILV sp EB got a Ha; lia)| right; exact Ha])))) as AG03;
        clear MI1 HEB1.
      + (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
        pose proof (GIo_tls K _ _ _ _ _ G3) as [_ TB]. unfold tls_block_ok_u in TB.
        unfold utp in EN2. rewrite <- TP in EN2.
        eapply implM_pure; [reflexivity|]. cbn [fst snd].
        set (e := lc_errno (ps_libc s')) in *.
        hide HEB3.
        pose proof TB as TB'. unfold utp in TB'. rewrite <- TP in TB'.
        assert (E4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
        { destruct TB' as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * 4 + 9)%Z. lia. }
        cbn [Z.b2z]. step. if_false. do 5 step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(lia)).
        step. rewrite (and3_aligned (bv_unsigned tp + -164)) by lia. step. if_false. do 6 step.
        replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
        unhide HEB3.
        assert (MSG : fmt_at m3 0x108d6 "error reading dump file"%string).
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m3 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        name_sp sp (-48)%Z.
        eapply evt_cut.
        { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 0x108d6%Z e "error reading dump file"%string [] ej);
            [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB3
             | right; rewrite Hsp; lia | exact E8 ].
          split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
        cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & junk4 & -> & MI4 & ST4 & AG4 & G4 & HEB4).
        rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 83200)) with (Z_to_bv 64 83200) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (KEEP4 : forall A cs, rw_cells usegs m3 A cs -> (bv_unsigned sp + -48 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells usegs m4 A cs).
        { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG4 | exact HC | intros a Ha; split; [left; lia| lia]]. }
        apply KEEP4 in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP4 in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia].
        apply KEEP4 in MG2; [|lia|cbn [cells_size csize Nat.add]; lia]. clear KEEP4.
        hide HEB4. step. unhide HEB4.
        eapply FAIL; [assumption | assumption | | exact G4 | exact ERRc | reflexivity | exact MG2 | cbn [cells_size csize Nat.add]; lia | exact FRS | exact HEB4
                     | pose proof (fmt_errmsg_length "error reading dump file"%string [] e); lia
                     | apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor] | congruence].
        eapply agrees_on_trans; [exact AG03|]. eapply agrees_on_weaken; [exact AG4|]. intros a [[Ha|Ha] Hn]; (split; [|exact Hn]); [left; lia| right; exact Ha].
      + (* [comment removed for export] *)
        eapply implM_pure; [reflexivity|]. cbn [fst snd].
        hide HEB3.
        cbn [Z.b2z]. step. if_true. do 7 step.
        unhide HEB3.
        assert (MSG : fmt_at m3 0x1050c "truncated dump file; tried to read %zu file header bytes, only got %zu"%string).
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m3 0x1050c (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %zu file header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                   MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        name_sp sp (-48)%Z.
        eapply evt_cut.
        { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB 256%Z 0x1050c%Z
                    "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 4; AInt (Z.of_nat (length got))] ej);
            [| reflexivity | reflexivity | reflexivity | lia | exact MSG | vm_compute; reflexivity | cbn; lia | | exact HEB3 | right; rewrite Hsp; lia].
          { split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
            split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
          cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
        cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
        unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 83292)) with (Z_to_bv 64 83292) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -48 - STDIO_STACK, bv_unsigned sp + -48); (EB, EB + 256)]%Z a) m3 m4)
          by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
        unfold STDIO_STACK in AGS.
        assert (KEEP4 : forall A cs, rw_cells usegs m3 A cs -> (bv_unsigned sp + -48 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells usegs m4 A cs).
        { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AGS | exact HC | intros a Ha; cbn [outside]; lia]. }
        apply KEEP4 in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP4 in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia].
        apply KEEP4 in MG2; [|lia|cbn [cells_size csize Nat.add]; lia]. clear KEEP4.
        assert (G4 : GIo K R s' CL FB m4).
        { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |].
          apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, STDIO_STACK; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
        change (Z.to_nat 256) with 256%nat in HEB4.
        replace (256 - length (Fmt.snprintf 256 "truncated dump file; tried to read %zu file header bytes, only got %zu" [AInt 4; AInt (Z.of_nat (length got))]) - 1)%nat
          with (255 - length (Fmt.snprintf 256 "truncated dump file; tried to read %zu file header bytes, only got %zu" [AInt 4; AInt (Z.of_nat (length got))]))%nat in HEB4 by lia.
        eapply FAIL; [assumption | assumption | | exact G4 | exact ERRc | reflexivity | exact MG2 | cbn [cells_size csize Nat.add]; lia | exact FRS | exact HEB4
                     | pose proof (snprintf_length 256 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 4; AInt (Z.of_nat (length got))]) as LS;
                       change (Z.to_nat (256 - 1)) with 255%nat in LS; unfold Msg.trunc_file_header, PCAP_ERRBUF_SIZE; lia
                     | unfold Msg.trunc_file_header; apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] | congruence].
        eapply agrees_on_trans; [exact AG03|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] Hn]; cbn [outside]; [lia|]. pose proof (CLB a Ha). unfold rc_lo in LO. split; [lia|]. split; [exact Hn| exact Logic.I].
  Qed.
  End Sz6.
  Theorem fopen_offline_proof : ltac:(let t := eval cbv delta [fopen_offline_proof__stmt] in fopen_offline_proof__stmt in exact t).
  Proof using CHK_NG CHK_PCAP FERROR FILENO FMT FREAD HFL SFL SNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo FA EB f ej fuel. ltac2:(SecDiet.SzSec.closeP 'fopen_offline_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FopenOffline.

End WithCeil.
End TwB.
End F_pcap_fopen.

(* [comment removed for export] *)
Module F_sfpcap_swap.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
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

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition swap_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 : Z) (mid : list byte),
    mem_inv ssegs m -> (112 <= bv_unsigned sp)%Z ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    (0 <= e0 < 256)%Z -> (0 <= e1 < 256)%Z -> (0 <= e2 < 256)%Z -> (0 <= e3 < 256)%Z ->
    (0 <= h0 < 256)%Z -> (0 <= h1 < 256)%Z -> (0 <= h2 < 256)%Z -> (0 <= h3 < 256)%Z ->
    rw_cells ssegs m (bv_unsigned sp + -100)
      [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3)); CB 8 mid; C4 (Z_to_bv 64 (le4val e0 e1 e2 e3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3))] ->
    evt ssegs (fun ms' => exists a0' a1' a2' a3' a4' a5' a6' a7' m',
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x15124) fc None m' (seg_rom ssegs)
        /\ munch [(bv_unsigned sp + -100, bv_unsigned sp + -80)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rw_cells ssegs m' (bv_unsigned sp + -100)
             [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2)); CB 8 mid; C4 (Z_to_bv 64 (le4val e3 e2 e1 e0)); C4 (Z_to_bv 64 (le4val h3 h2 h1 h0))])
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1509c) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 mid : ltac2:(SecDiet.SzSec.tyM 'swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma swap_block__body : ltac2:(SecDiet.SzSec.bodyP 'swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
  intros MI SPL B0 B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  pose proof (munch_refl [(bv_unsigned sp + -100, bv_unsigned sp + -80)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  do 34 step.
  apply evt_done. do 9 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  assert (LM : length mid = 8%nat) by (destruct FR as [[WF _] _]; cbn in WF; tauto).
  eapply rw_cells_recell; [exact FR | cbn; repeat split; try exact Logic.I; exact LM |].
  { cbn [cells_bytes cbytes app].
      rewrite (le2_lit g1 g0), (le2_lit g3 g2), (le4_lit e3 e2 e1 e0), (le4_lit h3 h2 h1 h0) by lia.
      rewrite (le2_of_val _ g1 g0 g1); [| lia | lia | lia | apply (swap16_val _ g0 g1); [lia|lia| apply unsigned_zx16; lia]].
      rewrite (le2_of_val _ g3 g2 g3); [| lia | lia | lia | apply (swap16_val _ g2 g3); [lia|lia| apply unsigned_zx16; lia]].
      rewrite (le4_of_val _ e3 e2 e1 e0 (e1 + 256 * e2 + 65536 * e3 + 16777216 * (((e3 / 128) * 4294967295) mod 256)));
        [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
         | apply (swap32_val _ e0 e1 e2 e3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
      rewrite (le4_of_val _ h3 h2 h1 h0 (h1 + 256 * h2 + 65536 * h3 + 16777216 * (((h3 / 128) * 4294967295) mod 256)));
        [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
         | apply (swap32_val _ h0 h1 h2 h3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
      reflexivity. }
Qed.
End Sz1.
Lemma swap_block : ltac:(let t := eval cbv delta [swap_block__stmt] in swap_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 mid. ltac2:(SecDiet.SzSec.closeP 'swap_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB.
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

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition swap_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 : Z) (mid : list byte),
    mem_inv usegs m -> (96 <= bv_unsigned sp)%Z ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    (0 <= e0 < 256)%Z -> (0 <= e1 < 256)%Z -> (0 <= e2 < 256)%Z -> (0 <= e3 < 256)%Z ->
    (0 <= h0 < 256)%Z -> (0 <= h1 < 256)%Z -> (0 <= h2 < 256)%Z -> (0 <= h3 < 256)%Z ->
    rw_cells usegs m (bv_unsigned sp + -92)
      [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3)); CB 8 mid; C4 (Z_to_bv 64 (le4val e0 e1 e2 e3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3))] ->
    evt usegs (fun ms' => exists a0' a1' a2' a3' a4' a5' a6' a7' m',
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x15654) fc None m' (seg_rom usegs)
        /\ munch [(bv_unsigned sp + -92, bv_unsigned sp + -72)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' (bv_unsigned sp + -92)
             [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2)); CB 8 mid; C4 (Z_to_bv 64 (le4val e3 e2 e1 e0)); C4 (Z_to_bv 64 (le4val h3 h2 h1 h0))])
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x155cc) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 mid : ltac2:(SecDiet.SzSec.tyM 'swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma swap_block__body : ltac2:(SecDiet.SzSec.bodyP 'swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros MI SPL B0 B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  pose proof (munch_refl [(bv_unsigned sp + -92, bv_unsigned sp + -72)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 34 step.
  apply evt_done. do 9 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  assert (LM : length mid = 8%nat) by (destruct FR as [[WF _] _]; cbn in WF; tauto).
  eapply rw_cells_recell; [exact FR | cbn; repeat split; try exact Logic.I; exact LM |].
  { cbn [cells_bytes cbytes app].
      rewrite (le2_lit g1 g0), (le2_lit g3 g2), (le4_lit e3 e2 e1 e0), (le4_lit h3 h2 h1 h0) by lia.
      rewrite (le2_of_val _ g1 g0 g1); [| lia | lia | lia | apply (swap16_val _ g0 g1); [lia|lia| apply unsigned_zx16; lia]].
      rewrite (le2_of_val _ g3 g2 g3); [| lia | lia | lia | apply (swap16_val _ g2 g3); [lia|lia| apply unsigned_zx16; lia]].
      rewrite (le4_of_val _ e3 e2 e1 e0 (e1 + 256 * e2 + 65536 * e3 + 16777216 * (((e3 / 128) * 4294967295) mod 256)));
        [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
         | apply (swap32_val _ e0 e1 e2 e3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
      rewrite (le4_of_val _ h3 h2 h1 h0 (h1 + 256 * h2 + 65536 * h3 + 16777216 * (((h3 / 128) * 4294967295) mod 256)));
        [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
         | apply (swap32_val _ h0 h1 h2 h3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
      reflexivity. }
Qed.
End Sz1.
Lemma swap_block : ltac:(let t := eval cbv delta [swap_block__stmt] in swap_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g0 g1 g2 g3 e0 e1 e2 e3 h0 h1 h2 h3 mid. ltac2:(SecDiet.SzSec.closeP 'swap_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End WithCeil.
End TwB.
End F_sfpcap_swap.

(* [comment removed for export] *)
Module F_sfpcapng_chkA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.
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

Section WithCeil.
Context {CEILV : CEIL}.
Section ChkNgA.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis FREE : free_stmt_o HO K.

  (* [comment removed for export] *)
  Definition ngc_ctx (sp tp : word) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem) : Prop :=
    GIo K R s CL FB m /\ usp0 R - 8388608 <= lo /\ lo + 81920 <= bv_unsigned sp /\ bv_unsigned sp <= rc_spmain R
    /\ tp = rc_tp R /\ bv_unsigned sp mod 16 = 0
    /\ In (f, FA, FILE_BLOCK) FB /\ sites = sites_at (bv_unsigned sp + D_CHECK_HEADER)
    /\ length magic = 4%nat /\ Forall (fun z => 0 <= z < 256) magic
    /\ bv_unsigned sp <= ERR /\ ERR + 4 <= MG /\ MG + 4 <= rc_spmain R
    /\ bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= ERR \/ MG + 4 <= EB) /\ EB mod 8 = 0.

  #[local] Notation FRAME_NG ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 :=
    [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] (only parsing).

  Open Scope bv_scope.

  (* [comment removed for export] *)
  Definition ngc_err_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' : word) (pcx : Z) (m3 : mem) (ps3 : PS)
           (msg : list Z) (junk3 : list byte) (ew : word) (hc : list cell),
      ngc_ctx sp tp R s CL FB lo MG FA EB ERR f magic m ->
      ((pcx = 0x16a48)%Z /\ s7' = Z_to_bv 64 1) \/ (pcx = 0x16710)%Z \/ ((pcx = 0x16714)%Z /\ a0' = Z_to_bv 64 0) ->
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3 ->
      GIo K R ps3 CL FB m3 ->
      rw_cells ssegs m3 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat ->
      rw_cells ssegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m3 ERR [C4 ew] -> rw_cells ssegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) ->
      rw_cells ssegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] -> (Z.of_nat (length msg) < 256)%Z ->
      Forall (fun z => 0 < z < 256)%Z msg -> ps_outfile ps3 = ps_outfile s ->
      evt ssegs (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s) (CH_Err msg) ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 pcx) fc None m3 (seg_rom ssegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' pcx m3 ps3 msg junk3 ew hc : ltac2:(SecDiet.SzSec.tyM 'ngc_err_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_err_exit__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_err_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros CTX HPC MIx ST3 AG3 G3 FA3 Hhc FRS3 ERR3 MG3 HEB3 LEN3 RNG3 OFX.
    destruct CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (rw_cells_forget _ _ _ _ FA3) as [fj FA3']. clear FA3. rewrite Hhc in FA3'.
    hide HEB3. hide MG3.
    pose proof (munch_refl [(ERR, ERR + 4)]%Z m3) as MU3. pose proof (wmono_refl ssegs m3) as WM3.
    destruct HPC as [[-> ->]|[->|[-> ->]]]; [do 3 pstep | do 4 pstep | do 3 pstep].
    all: do 13 step.
    all: release_frame FA3' ST3 (bv_unsigned sp + -88)%Z; release_frame FRS3 ST3 (bv_unsigned sp).
    all: unhide HEB3; unhide MG3.
    all: destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL; cbn [map] in MG3.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGW : agrees_on (fun a => outside [(ERR, ERR + 4)]%Z a) m3 mm) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]);
      assert (HEB' : rw_cells ssegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3])
        by (eapply agrees_rw_cells; [exact AGW | exact HEB3 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
      assert (MG' : rw_cells ssegs mm MG [CB 4 (map b8 [k0; k1; k2; k3])])
        by (eapply rw_cells_recell; [eapply agrees_rw_cells; [exact AGW | exact MG3 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia] | cbn; repeat split; exact Logic.I | reflexivity]);
      assert (G' : GIo K R ps3 CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU3 | exact WM3 |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil])
    end.
    all: apply evt_done; unfold check_header_post.
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, (Z_to_bv 64 1) end.
    all: split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    all: split; [solve [assumption | congruence] |].
    all: split; [assumption|]; split; [assumption|].
    all: split; [eapply agrees_on_trans; [exact AG3|]; eapply agrees_on_weaken; [exact AGW|]; intros a [_ [_ Hn]]; cbn [outside]; lia |].
    all: split; [exact MG'|]; split; [assumption|].
    all: exists junk3; split; [reflexivity|]; split; [reflexivity|]; split; [exact G'|]; split; [exact HEB'|]; split; [exact LEN3| exact RNG3].
  Qed.
  End Sz1.
  Lemma ngc_err_exit : ltac:(let t := eval cbv delta [ngc_err_exit__stmt] in ngc_err_exit__stmt in exact t).
  Proof using HFL SFL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' pcx m3 ps3 msg junk3 ew hc. ltac2:(SecDiet.SzSec.closeP 'ngc_err_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_fail3__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s8' s9' t3' t4' t5' t6' : word) (m3 : mem) (ps3 : PS)
           (msg : list Z) (junk3 : list byte) (ew : word) (hc : list cell)
           (qs qb : hptr) (i : option hptr) (P B I nb ni : Z),
      ngc_ctx sp tp R s CL FB lo MG FA EB ERR f magic m ->
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3 ->
      GIo K R ps3 (match i with Some qi => [(qi, I, ni)] | None => [] end ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m3 ->
      match i with Some _ => True | None => I = 0%Z end ->
      rw_cells ssegs m3 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat ->
      rw_cells ssegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m3 ERR [C4 ew] -> rw_cells ssegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) ->
      rw_cells ssegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] -> (Z.of_nat (length msg) < 256)%Z ->
      Forall (fun z => 0 < z < 256)%Z msg -> ps_outfile ps3 = ps_outfile s ->
      rw_cells ssegs m3 (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells ssegs m3 (P + 672) [C8 (Z_to_bv 64 I)] -> (0 <= I < 2^64)%Z -> (0 < B < 2^64)%Z -> (0 < P /\ P + 680 < 2^64)%Z ->
      implM ssegs (Monad.mbind (match i with Some qi => pfree HO qi | None => mret tt end)
                     (fun _ => Monad.mbind (pfree HO qb) (fun _ => Monad.mbind (pfree HO qs) (fun _ => mret (CH_Err msg)))))
        ps3 (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 P) s3' s4' s5' (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) s8' s9' s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16a30) fc None m3 (seg_rom ssegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s8' s9' t3' t4' t5' t6' m3 ps3 msg junk3 ew hc qs qb i P B I nb ni : ltac2:(SecDiet.SzSec.tyM 'ngc_fail3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_fail3__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fail3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FREE HFL SFL. pin_using (fun (FREE HFL SFL : unit) => tt).
    intros CTX MI3 ST3 AG3 G3 HI HC Hhc FRS3 ERR3 MG3 HEB3 LEN3 RNG3 OFX HPB HPI IR BR PR.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    (* [comment removed for export] *)
    assert (KEEP : forall (mA mB : mem) (CLx : list cblk) A cs,
      agrees_on (client_keeps CLx (bv_unsigned sp + -128)) mA mB -> rw_cells ssegs mA A cs -> (bv_unsigned sp + -128 <= A)%Z -> rw_cells ssegs mB A cs).
    { intros mA mB CLx A cs AGx HA LA. eapply agrees_rw_cells; [exact AGx | exact HA | intros a Ha; left; lia]. }
    hide HC. hide FRS3. hide ERR3. hide MG3. hide HEB3. hide HPB.
    unfold implM. iprefix.
    step.
    (* [comment removed for export] *)
    assert (STEP1 : forall ms1,
      (exists ps4 m4 (a0v : word) t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x,
         ms1 = MS (mkR (Z_to_bv 64 0x16a38) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0x t1x t2x (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0v a1x a2x a3x a4x a5x a6x a7x
                       (Z_to_bv 64 P) s3' s4' s5' (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) s8' s9' s10 s11 t3x t4x t5x t6x) F (Z_to_bv 64 0x16a38) fc None m4 (seg_rom ssegs)
         /\ ps_outfile ps4 = ps_outfile s /\ mem_inv ssegs m4 /\ stk ssegs m4 lo (bv_unsigned sp + -128)
         /\ agrees_on (client_keeps ((qs, P, 680%Z) :: (qb, B, nb) :: CL) (bv_unsigned sp + -128)) m3 m4
         /\ GIo K R ps4 ((qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m4
         /\ impl ssegs (at_node ssegs) (npeek ssegs)
              ((Monad.mbind (pfree HO qb) (fun _ => Monad.mbind (pfree HO qs) (fun _ => mret (CH_Err msg)))) ps4)
              (epost (fun p0 => check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s) (fst p0) (snd p0))) ms1
         -> True) -> True) by (intros; exact Logic.I).
    clear STEP1.
    (* [comment removed for export] *)
    assert (REST2 : forall (rax a0x t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (m4 : mem) (ps4 : PS),
      mem_inv ssegs m4 -> stk ssegs m4 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m4 ->
      GIo K R ps4 ((qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m4 -> ps_outfile ps4 = ps_outfile s ->
      rw_cells ssegs m4 (bv_unsigned sp + -128) hc ->
      rw_cells ssegs m4 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m4 ERR [C4 ew] -> rw_cells ssegs m4 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) ->
      rw_cells ssegs m4 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] ->
      rw_cells ssegs m4 (P + 24) [C8 (Z_to_bv 64 B)] ->
      evt ssegs (fun ms' => impl ssegs (at_node ssegs) (npeek ssegs)
              ((Monad.mbind (pfree HO qb) (fun _ => Monad.mbind (pfree HO qs) (fun _ => mret (CH_Err msg)))) ps4)
              (epost (fun p0 => check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s) (fst p0) (snd p0))) ms')
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0x t1x t2x (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0x a1x a2x a3x a4x a5x a6x a7x
                 (Z_to_bv 64 P) s3' s4' s5' (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) s8' s9' s10 s11 t3x t4x t5x t6x) F (Z_to_bv 64 0x16a38) fc None m4 (seg_rom ssegs))).
    { intros until ps4. intros MI4 ST4 AG4 G4 OF4 HC4 FRS4 ERR4 MG4 HEB4 HPB4.
      hide HC4. hide FRS4. hide ERR4. hide MG4. hide HEB4.
      step. step.
      apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind ssegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 R ps4 [(qs, P, 680%Z)] CL FB qb B nb lo); [| reflexivity].
        split; [exact G4|]. split; [rewrite Hsp; exact ST4|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI4|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [] ps5 ms5 PO. cbv beta in PO. destruct PO as (av5 & m5 & E & OF5 & MI5 & ST5 & AG5 & G5).
      unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x16a40)) with (Z_to_bv 64 0x16a40) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in G5, AG5.
      unhide HC4. unhide FRS4. unhide ERR4. unhide MG4. unhide HEB4.
      apply (KEEP _ _ _ _ _ AG5) in HC4; [|lia]. apply (KEEP _ _ _ _ _ AG5) in FRS4; [|lia]. apply (KEEP _ _ _ _ _ AG5) in ERR4; [|lia].
      apply (KEEP _ _ _ _ _ AG5) in MG4; [|lia]. apply (KEEP _ _ _ _ _ AG5) in HEB4; [|lia].
      assert (AG5' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m5).
      { eapply agrees_on_trans; [exact AG4|]. eapply agrees_on_weaken; [exact AG5|]. intros a ([Ha|Ha] & _); [left; lia| right]. unfold in_block in Ha |- *. apply Exists_cons_tl. exact Ha. }
      clear AG5 MI4 ST4 G4.
      hide HC4. hide FRS4. hide ERR4. hide MG4. hide HEB4.
      (* [comment removed for export] *)
      unfold implM. iprefix. step. step.
      apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind ssegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 R ps5 [] CL FB qs P 680%Z lo); [| reflexivity].
        split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [] ps6 ms6 PO. cbv beta in PO. destruct PO as (av6 & m6 & E & OF6 & MI6 & ST6 & AG6 & G6).
      unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x16a48)) with (Z_to_bv 64 0x16a48) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in G6, AG6.
      unhide HC4. unhide FRS4. unhide ERR4. unhide MG4. unhide HEB4.
      apply (KEEP _ _ _ _ _ AG6) in HC4; [|lia]. apply (KEEP _ _ _ _ _ AG6) in FRS4; [|lia]. apply (KEEP _ _ _ _ _ AG6) in ERR4; [|lia].
      apply (KEEP _ _ _ _ _ AG6) in MG4; [|lia]. apply (KEEP _ _ _ _ _ AG6) in HEB4; [|lia].
      assert (AG6' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
      { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a ([Ha|Ha] & _); [left; lia| right; exact Ha]. }
      apply (implM_ret ssegs).
      eapply (ngc_err_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m); try eassumption.
      - left. split; reflexivity.
      - rewrite OF6, OF5. exact OF4. }
    step.
    destruct i as [qi|].
    - (* [comment removed for export] *)
      apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind ssegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 R ps3 [] ((qs, P, 680%Z) :: (qb, B, nb) :: CL) FB qi I ni lo); [| reflexivity].
        split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI3|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [] ps4 ms4 PO. cbv beta in PO. destruct PO as (av4 & m4 & E & OF4 & MI4 & ST4 & AG4 & G4).
      unfold hpost_regs in E. destruct_exs E. subst ms4. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x16a38)) with (Z_to_bv 64 0x16a38) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in G4, AG4.
      unhide HC. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB3. unhide HPB.
      apply (KEEP _ _ _ _ _ AG4) in HC; [|lia]. apply (KEEP _ _ _ _ _ AG4) in FRS3; [|lia]. apply (KEEP _ _ _ _ _ AG4) in ERR3; [|lia].
      apply (KEEP _ _ _ _ _ AG4) in MG3; [|lia]. apply (KEEP _ _ _ _ _ AG4) in HEB3; [|lia].
      assert (HPB4 : rw_cells ssegs m4 (P + 24) [C8 (Z_to_bv 64 B)]).
      { eapply agrees_rw_cells; [exact AG4 | exact HPB | intros a Ha; right; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *; lia]. }
      assert (AG4' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m4).
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AG4|]. intros a ([Ha|Ha] & _); [left; lia| right]. unfold in_block in Ha |- *. do 2 apply Exists_cons_tl. exact Ha. }
      unfold implM. iprefix.
      eapply REST2; [exact MI4 | exact ST4 | exact AG4' | exact G4 | rewrite OF4; exact OFX | exact HC | exact FRS3 | exact ERR3 | exact MG3 | exact HEB3 | exact HPB4].
    - (* [comment removed for export] *)
      subst I. cbn [app] in G3.
      eapply evt_cut; [apply free_null_spec; reflexivity|]. cbv beta. intros ms' ->.
      replace (ret_pc (Z_to_bv 64 0x16a38)) with (Z_to_bv 64 0x16a38) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply evt_done. apply (implM_retb ssegs). unfold implM. iprefix.
      unhide HC. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB3. unhide HPB.
      eapply REST2; [exact MI3 | exact ST3 | exact AG3 | exact G3 | exact OFX | exact HC | exact FRS3 | exact ERR3 | exact MG3 | exact HEB3 | exact HPB].
  Qed.
  End Sz2.
  Lemma ngc_fail3 : ltac:(let t := eval cbv delta [ngc_fail3__stmt] in ngc_fail3__stmt in exact t).
  Proof using FREE HFL SFL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s8' s9' t3' t4' t5' t6' m3 ps3 msg junk3 ew hc qs qb i P B I nb ni. ltac2:(SecDiet.SzSec.closeP 'ngc_fail3__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkNgA.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB.
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

Section WithCeil.
Context {CEILV : CEIL}.
Section ChkNgA.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis FREE : free_stmt_o HO K.

  (* [comment removed for export] *)
  Definition ngc_ctx (sp tp : word) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem) : Prop :=
    GIo K R s CL FB m /\ usp0 R - 8388608 <= lo /\ lo + 81920 <= bv_unsigned sp /\ bv_unsigned sp <= rc_spmain R
    /\ tp = rc_tp R /\ bv_unsigned sp mod 16 = 0
    /\ In (f, FA, FILE_BLOCK) FB /\ sites = sites_at (bv_unsigned sp + D_CHECK_HEADER)
    /\ length magic = 4%nat /\ Forall (fun z => 0 <= z < 256) magic
    /\ bv_unsigned sp <= ERR /\ ERR + 4 <= MG /\ MG + 4 <= rc_spmain R
    /\ bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= ERR \/ MG + 4 <= EB) /\ ERR mod 4 = 0 /\ EB mod 8 = 0.

  #[local] Notation FRAME_NG ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 :=
    [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] (only parsing).

  Open Scope bv_scope.

  (* [comment removed for export] *)
  Definition ngc_err_exit__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' : word) (pcx : Z) (m3 : mem) (ps3 : PS)
           (msg : list Z) (junk3 : list byte) (ew : word) (hc : list cell),
      ngc_ctx sp tp R s CL FB lo MG FA EB ERR f magic m ->
      ((pcx = 0x1702c)%Z /\ s8' = Z_to_bv 64 1) \/ (pcx = 0x16be0)%Z \/ ((pcx = 0x16be4)%Z /\ a0' = Z_to_bv 64 0) ->
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3 ->
      GIo K R ps3 CL FB m3 ->
      rw_cells usegs m3 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat ->
      rw_cells usegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m3 ERR [C4 ew] -> rw_cells usegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) ->
      rw_cells usegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] -> (Z.of_nat (length msg) < 256)%Z ->
      Forall (fun z => 0 < z < 256)%Z msg -> ps_outfile ps3 = ps_outfile s ->
      evt usegs (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s) (CH_Err msg) ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 pcx) fc None m3 (seg_rom usegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' pcx m3 ps3 msg junk3 ew hc : ltac2:(SecDiet.SzSec.tyM 'ngc_err_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_err_exit__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_err_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
 intros CTX HPC MIx ST3 AG3 G3 FA3 Hhc FRS3 ERR3 MG3 HEB3 LEN3 RNG3 OFX.
    destruct CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (rw_cells_forget _ _ _ _ FA3) as [fj FA3']. clear FA3. rewrite Hhc in FA3'.
    hide HEB3. hide MG3.
    pose proof (munch_refl [(ERR, ERR + 4)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
    destruct HPC as [[-> ->]|[->|[-> ->]]]; [do 3 pstep | do 4 pstep | do 3 pstep].
    all: do 13 step.
    all: release_frame FA3' ST3 (bv_unsigned sp + -88)%Z; release_frame FRS3 ST3 (bv_unsigned sp).
    all: unhide HEB3; unhide MG3.
    all: destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL; cbn [map] in MG3.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGW : agrees_on (fun a => outside [(ERR, ERR + 4)]%Z a) m3 mm) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]);
      assert (HEB' : rw_cells usegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3])
        by (eapply agrees_rw_cells; [exact AGW | exact HEB3 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
      assert (MG' : rw_cells usegs mm MG [CB 4 (map b8 [k0; k1; k2; k3])])
        by (eapply rw_cells_recell; [eapply agrees_rw_cells; [exact AGW | exact MG3 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia] | cbn; repeat split; exact Logic.I | reflexivity]);
      assert (G' : GIo K R ps3 CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU3 | exact WM3 |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil])
    end.
    all: apply evt_done; unfold check_header_post.
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, (Z_to_bv 64 1) end.
    all: split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    all: split; [solve [assumption | congruence] |].
    all: split; [assumption|]; split; [assumption|].
    all: split; [eapply agrees_on_trans; [exact AG3|]; eapply agrees_on_weaken; [exact AGW|]; intros a [_ [_ Hn]]; cbn [outside]; lia |].
    all: split; [exact MG'|]; split; [assumption|].
    all: exists junk3; split; [reflexivity|]; split; [reflexivity|]; split; [exact G'|]; split; [exact HEB'|]; split; [exact LEN3| exact RNG3].
  Qed.
  End Sz1.
  Lemma ngc_err_exit : ltac:(let t := eval cbv delta [ngc_err_exit__stmt] in ngc_err_exit__stmt in exact t).
  Proof using HFL SFL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' pcx m3 ps3 msg junk3 ew hc. ltac2:(SecDiet.SzSec.closeP 'ngc_err_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_fail3__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s7' s9' t3' t4' t5' t6' : word) (m3 : mem) (ps3 : PS)
           (msg : list Z) (junk3 : list byte) (ew : word) (hc : list cell)
           (qs qb : hptr) (i : option hptr) (P B I nb ni : Z),
      ngc_ctx sp tp R s CL FB lo MG FA EB ERR f magic m ->
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3 ->
      GIo K R ps3 (match i with Some qi => [(qi, I, ni)] | None => [] end ++ (qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m3 ->
      match i with Some _ => True | None => I = 0%Z end ->
      rw_cells usegs m3 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat ->
      rw_cells usegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m3 ERR [C4 ew] -> rw_cells usegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) ->
      rw_cells usegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] -> (Z.of_nat (length msg) < 256)%Z ->
      Forall (fun z => 0 < z < 256)%Z msg -> ps_outfile ps3 = ps_outfile s ->
      rw_cells usegs m3 (P + 24) [C8 (Z_to_bv 64 B)] -> rw_cells usegs m3 (P + 672) [C8 (Z_to_bv 64 I)] -> (0 <= I < 2^64)%Z -> (0 < B < 2^64)%Z -> (0 < P /\ P + 680 < 2^64)%Z ->
      implM usegs (Monad.mbind (match i with Some qi => pfree HO qi | None => mret tt end)
                     (fun _ => Monad.mbind (pfree HO qb) (fun _ => Monad.mbind (pfree HO qs) (fun _ => mret (CH_Err msg)))))
        ps3 (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' (Z_to_bv 64 P) s4' s5' (Z_to_bv 64 (P + 648)) s7' (Z_to_bv 64 1) s9' s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x17014) fc None m3 (seg_rom usegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s7' s9' t3' t4' t5' t6' m3 ps3 msg junk3 ew hc qs qb i P B I nb ni : ltac2:(SecDiet.SzSec.tyM 'ngc_fail3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_fail3__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fail3__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FREE HFL SFL. pin_using (fun (FREE HFL SFL : unit) => tt).
 intros CTX MI3 ST3 AG3 G3 HI HC Hhc FRS3 ERR3 MG3 HEB3 LEN3 RNG3 OFX HPB HPI IR BR PR.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    (* [comment removed for export] *)
    assert (KEEP : forall (mA mB : mem) (CLx : list cblk) A cs,
      agrees_on (client_keeps CLx (bv_unsigned sp + -128)) mA mB -> rw_cells usegs mA A cs -> (bv_unsigned sp + -128 <= A)%Z -> rw_cells usegs mB A cs).
    { intros mA mB CLx A cs AGx HA LA. eapply agrees_rw_cells; [exact AGx | exact HA | intros a Ha; left; lia]. }
    hide HC. hide FRS3. hide ERR3. hide MG3. hide HEB3. hide HPB.
    unfold implM. iprefix.
    step.
    (* [comment removed for export] *)
    assert (STEP1 : forall ms1,
      (exists ps4 m4 (a0v : word) t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x,
         ms1 = MS (mkR (Z_to_bv 64 0x1701c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0x t1x t2x (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0v a1x a2x a3x a4x a5x a6x a7x
                       s2' (Z_to_bv 64 P) s4' s5' (Z_to_bv 64 (P + 648)) s7' (Z_to_bv 64 1) s9' s10 s11 t3x t4x t5x t6x) F (Z_to_bv 64 0x1701c) fc None m4 (seg_rom usegs)
         /\ ps_outfile ps4 = ps_outfile s /\ mem_inv usegs m4 /\ stk usegs m4 lo (bv_unsigned sp + -128)
         /\ agrees_on (client_keeps ((qs, P, 680%Z) :: (qb, B, nb) :: CL) (bv_unsigned sp + -128)) m3 m4
         /\ GIo K R ps4 ((qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m4
         /\ impl usegs (at_node usegs) (npeek usegs)
              ((Monad.mbind (pfree HO qb) (fun _ => Monad.mbind (pfree HO qs) (fun _ => mret (CH_Err msg)))) ps4)
              (epost (fun p0 => check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s) (fst p0) (snd p0))) ms1
         -> True) -> True) by (intros; exact Logic.I).
    clear STEP1.
    (* [comment removed for export] *)
    assert (REST2 : forall (rax a0x t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (m4 : mem) (ps4 : PS),
      mem_inv usegs m4 -> stk usegs m4 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m4 ->
      GIo K R ps4 ((qs, P, 680%Z) :: (qb, B, nb) :: CL) FB m4 -> ps_outfile ps4 = ps_outfile s ->
      rw_cells usegs m4 (bv_unsigned sp + -128) hc ->
      rw_cells usegs m4 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m4 ERR [C4 ew] -> rw_cells usegs m4 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) ->
      rw_cells usegs m4 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] ->
      rw_cells usegs m4 (P + 24) [C8 (Z_to_bv 64 B)] ->
      evt usegs (fun ms' => impl usegs (at_node usegs) (npeek usegs)
              ((Monad.mbind (pfree HO qb) (fun _ => Monad.mbind (pfree HO qs) (fun _ => mret (CH_Err msg)))) ps4)
              (epost (fun p0 => check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s) (fst p0) (snd p0))) ms')
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0x t1x t2x (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0x a1x a2x a3x a4x a5x a6x a7x
                 s2' (Z_to_bv 64 P) s4' s5' (Z_to_bv 64 (P + 648)) s7' (Z_to_bv 64 1) s9' s10 s11 t3x t4x t5x t6x) F (Z_to_bv 64 0x1701c) fc None m4 (seg_rom usegs))).
    { intros until ps4. intros MI4 ST4 AG4 G4 OF4 HC4 FRS4 ERR4 MG4 HEB4 HPB4.
      hide HC4. hide FRS4. hide ERR4. hide MG4. hide HEB4.
      step. step.
      apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind usegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 R ps4 [(qs, P, 680%Z)] CL FB qb B nb lo); [| reflexivity].
        split; [exact G4|]. split; [rewrite Hsp; exact ST4|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI4|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [] ps5 ms5 PO. cbv beta in PO. destruct PO as (av5 & m5 & E & OF5 & MI5 & ST5 & AG5 & G5).
      unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x17024)) with (Z_to_bv 64 0x17024) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in G5, AG5.
      unhide HC4. unhide FRS4. unhide ERR4. unhide MG4. unhide HEB4.
      apply (KEEP _ _ _ _ _ AG5) in HC4; [|lia]. apply (KEEP _ _ _ _ _ AG5) in FRS4; [|lia]. apply (KEEP _ _ _ _ _ AG5) in ERR4; [|lia].
      apply (KEEP _ _ _ _ _ AG5) in MG4; [|lia]. apply (KEEP _ _ _ _ _ AG5) in HEB4; [|lia].
      assert (AG5' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m5).
      { eapply agrees_on_trans; [exact AG4|]. eapply agrees_on_weaken; [exact AG5|]. intros a ([Ha|Ha] & _); [left; lia| right]. unfold in_block in Ha |- *. apply Exists_cons_tl. exact Ha. }
      clear AG5 MI4 ST4 G4.
      hide HC4. hide FRS4. hide ERR4. hide MG4. hide HEB4.
      (* [comment removed for export] *)
      unfold implM. iprefix. step. step.
      apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind usegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 R ps5 [] CL FB qs P 680%Z lo); [| reflexivity].
        split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [] ps6 ms6 PO. cbv beta in PO. destruct PO as (av6 & m6 & E & OF6 & MI6 & ST6 & AG6 & G6).
      unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x1702c)) with (Z_to_bv 64 0x1702c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in G6, AG6.
      unhide HC4. unhide FRS4. unhide ERR4. unhide MG4. unhide HEB4.
      apply (KEEP _ _ _ _ _ AG6) in HC4; [|lia]. apply (KEEP _ _ _ _ _ AG6) in FRS4; [|lia]. apply (KEEP _ _ _ _ _ AG6) in ERR4; [|lia].
      apply (KEEP _ _ _ _ _ AG6) in MG4; [|lia]. apply (KEEP _ _ _ _ _ AG6) in HEB4; [|lia].
      assert (AG6' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m6).
      { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a ([Ha|Ha] & _); [left; lia| right; exact Ha]. }
      apply (implM_ret usegs).
      eapply (ngc_err_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m); try eassumption.
      - left. split; reflexivity.
      - rewrite OF6, OF5. exact OF4. }
    step.
    destruct i as [qi|].
    - (* [comment removed for export] *)
      apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind usegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 R ps3 [] ((qs, P, 680%Z) :: (qb, B, nb) :: CL) FB qi I ni lo); [| reflexivity].
        split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI3|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [] ps4 ms4 PO. cbv beta in PO. destruct PO as (av4 & m4 & E & OF4 & MI4 & ST4 & AG4 & G4).
      unfold hpost_regs in E. destruct_exs E. subst ms4. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x1701c)) with (Z_to_bv 64 0x1701c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in G4, AG4.
      unhide HC. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB3. unhide HPB.
      apply (KEEP _ _ _ _ _ AG4) in HC; [|lia]. apply (KEEP _ _ _ _ _ AG4) in FRS3; [|lia]. apply (KEEP _ _ _ _ _ AG4) in ERR3; [|lia].
      apply (KEEP _ _ _ _ _ AG4) in MG3; [|lia]. apply (KEEP _ _ _ _ _ AG4) in HEB3; [|lia].
      assert (HPB4 : rw_cells usegs m4 (P + 24) [C8 (Z_to_bv 64 B)]).
      { eapply agrees_rw_cells; [exact AG4 | exact HPB | intros a Ha; right; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd cells_size csize Nat.add] in *; lia]. }
      assert (AG4' : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m4).
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AG4|]. intros a ([Ha|Ha] & _); [left; lia| right]. unfold in_block in Ha |- *. do 2 apply Exists_cons_tl. exact Ha. }
      unfold implM. iprefix.
      eapply REST2; [exact MI4 | exact ST4 | exact AG4' | exact G4 | rewrite OF4; exact OFX | exact HC | exact FRS3 | exact ERR3 | exact MG3 | exact HEB3 | exact HPB4].
    - (* [comment removed for export] *)
      subst I. cbn [app] in G3.
      eapply evt_cut; [apply free_null_spec; reflexivity|]. cbv beta. intros ms' ->.
      replace (ret_pc (Z_to_bv 64 0x1701c)) with (Z_to_bv 64 0x1701c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply evt_done. apply (implM_retb usegs). unfold implM. iprefix.
      unhide HC. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB3. unhide HPB.
      eapply REST2; [exact MI3 | exact ST3 | exact AG3 | exact G3 | exact OFX | exact HC | exact FRS3 | exact ERR3 | exact MG3 | exact HEB3 | exact HPB].
  Qed.
  End Sz2.
  Lemma ngc_fail3 : ltac:(let t := eval cbv delta [ngc_fail3__stmt] in ngc_fail3__stmt in exact t).
  Proof using FREE HFL SFL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s7' s9' t3' t4' t5' t6' m3 ps3 msg junk3 ew hc qs qb i P B I nb ni. ltac2:(SecDiet.SzSec.closeP 'ngc_fail3__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkNgA.

End WithCeil.
End TwB.
End F_sfpcapng_chkA.

(* [comment removed for export] *)
Module F_sfpcapng_rb.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.
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

Section WithCeil.
Context {CEILV : CEIL}.
Definition FMT_ERR_READING : Z := 0x108d6.   (* [comment removed for export] *)
Definition FMT_TRUNC_PCAPNG : Z := 0x103e5. (* [comment removed for export] *)

Section RB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.

  Open Scope bv_scope.

  Definition read_bytes_proof__stmt : Prop := read_bytes_stmt HO K sites.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af D n EB lo foe dest junk ej : ltac2:(SecDiet.SzSec.tyM 'read_bytes_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma read_bytes_proof__body : ltac2:(SecDiet.SzSec.bodyP 'read_bytes_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FERROR FMT FREAD HFL SFL SNPRINTF. pin_using (fun (FERROR FMT FREAD HFL SFL SNPRINTF : unit) => tt).
    intros PRE HinF HD -> -> -> -> -> Hn HDST CRD HEB EBR DISJ EB8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    assert (CRE : client_range R CL (bv_unsigned sp) EB 256).
    { destruct EBR as [Hs|Hb]; [right; exact Hs| left]. intros a Ha. unfold iv_in_block in Hb. unfold in_block.
      apply Exists_exists in Hb as (b & Hin & Hb). apply Exists_exists. exists b. split; [exact Hin|]. cbn [fst snd] in Hb. lia. }
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold READ_BYTES_STACK, PCAP_L1_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & A5 & _).
    cbn [cb_addr cb_size fst snd] in A1, A4, A5. unfold FILE_BLOCK in A4, A5.
    pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    pose proof (rw_cells_bound _ _ _ _ HDST) as BD. cbn [cells_size csize Nat.add] in BD.
    assert (CLB : forall a, in_block CL a -> a < CEILZ).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. lia. }
    assert (EBX : EB + 256 <= CEILZ \/ bv_unsigned sp <= EB).
    { destruct CRE as [Hb|Hs]; [left; pose proof (CLB (EB + 255)%Z ltac:(apply Hb; lia)); lia| right; lia]. }
    assert (DX : (D + n <= CEILZ \/ bv_unsigned sp <= D \/ n = 0)%Z).
    { destruct (Z.eq_dec n 0%Z) as [->|NZ]; [right; right; reflexivity|].
      destruct CRD as [Hb|Hs]; [left; pose proof (CLB (D + n - 1)%Z ltac:(apply Hb; lia)); lia| right; left; lia]. }
    unfold read_bytes, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims]. unfold READ_BYTES_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    hide HEB. hide HDST.
    ienter. carve_frame 64%nat ST. do 19 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R s CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AGa : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256)) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|Ha] _]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]);
      unhide HEB; assert (HEB1 : rw_cells ssegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
      unhide HDST; assert (HD1 : rw_cells ssegs mm D [CB (Z.to_nat n) junk])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HDST | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia])
    end.
    clear MU WM HEB HDST.
    (* [comment removed for export] *)
    name_sp sp (-64)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { apply implM_mget. rewrite HD.
      eapply FREAD; [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact HD1
                    | destruct CRD as [Hb|Hs]; [left; exact Hb| right; rewrite Hsp; lia] ]. }
    intros got s' ms' PO. cbv beta in PO.
    destruct PO as (av & m2 & junk' & E & OF1 & MI1 & ST1 & AG1 & G1 & -> & GL & GR & HD2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 93076)) with (Z_to_bv 64 93076) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (KEEP : forall A cs, rw_cells ssegs m0 A cs -> (bv_unsigned sp + -64 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells ssegs m2 A cs).
    { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG1 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in FR; [|lia|cbn [cells_size csize Nat.add]; lia].
    assert (HEB2 : rw_cells ssegs m2 EB [CB 256 ej]).
    { eapply agrees_rw_cells; [exact AG1 | exact HEB1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      split; [destruct CRE as [Hb|Hs]; [right; apply Hb; lia | left; lia]| lia]. }
    clear KEEP HEB1 HD1 MI.
    assert (AG02 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] [Hd _]]; (split; [|exact Hd]); [left; lia| right; exact Ha]. }
    clear AGa AG1 G0.
    unfold zlength in *. pose proof GL as GL'.
    (* [comment removed for export] *)
    assert (EXIT : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (x2' x3' : word) (m3 : mem) (ps3 : PS) (st : rb_status) (sv : Z),
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -64) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      GIo K R ps3 CL FB m3 -> ps_outfile ps3 = ps_outfile s ->
      rw_cells ssegs m3 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk0))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
      match st with
      | RBS_Ok => sv = 1%Z /\ Z.of_nat (length got) = n /\ rw_cells ssegs m3 EB [CB 256 ej]
      | RBS_Eof => sv = 0%Z /\ Z.of_nat (length got) = 0%Z /\ foe = false /\ rw_cells ssegs m3 EB [CB 256 ej]
      | RBS_Err msg => exists junk'', sv = (-1)%Z /\ rw_cells ssegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''] /\ (Z.of_nat (length msg) < 256)%Z
                       /\ Forall (fun z => 0 < z < 256)%Z msg
      end ->
      evt ssegs (POSTQ (st, got) ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                 x2' x3' (Z_to_bv 64 sv) (Z_to_bv 64 Af) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16bf8) fc None m3 (seg_rom ssegs))).
    { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2' x3' m3 ps3 st sv MI3 ST3 AG3 G3 OF3 FR3 HD3 HST.
      hide HD3. hide HST.
      do 10 step.
      release_frame FR3 ST3 (bv_unsigned sp).
      unhide HD3. unhide HST.
      apply evt_done. subst POSTQ. unfold read_bytes_post.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 sv), mm, junk' end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [exact OF3|].
      split; [assumption|]. split; [assumption|]. split; [exact AG3|]. split; [exact G3|]. split; [exact HD3|].
      split; [exact GR|]. split; [unfold zlength; lia|].
      destruct st as [| |msg]; [destruct HST as (-> & E1 & X); auto| destruct HST as (-> & E1 & Ef & X); unfold zlength; auto| ].
      destruct HST as (j'' & -> & X & L & OK). exists j''. auto. }
    (* [comment removed for export] *)
    assert (KSNP : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (x2' : word) (m3 : mem) (ps3 : PS),
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -64) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      GIo K R ps3 CL FB m3 -> ps_outfile ps3 = ps_outfile s ->
      rw_cells ssegs m3 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk0))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
      rw_cells ssegs m3 EB [CB 256 ej] ->
      implM ssegs (mret (RBS_Err (Msg.trunc_pcapng n (Z.of_nat (length got))), got)) ps3 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                 x2' (Z_to_bv 64 (Z.of_nat (length got))) (Z_to_bv 64 1) (Z_to_bv 64 Af) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16bd8) fc None m3 (seg_rom ssegs))).
    { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2' m3 ps3 MI3 ST3 AG3 G3 OF3 FR3 HD3 HEB3.
      apply (implM_ret ssegs). hide HD3. hide HEB3.
      do 7 step.
      assert (MSG : fmt_at m3 FMT_TRUNC_PCAPNG "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
        by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_TRUNC_PCAPNG; lia| unfold FMT_TRUNC_PCAPNG; cbn; lia]).
      unhide HEB3.
      name_sp sp (-64)%Z.
      eapply evt_cut.
      { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps3 CL FB lo EB 256%Z FMT_TRUNC_PCAPNG
                  "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string [AInt n; AInt (Z.of_nat (length got))] ej);
          [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
          | reflexivity | reflexivity | reflexivity | lia | exact MSG | reflexivity | cbn; lia | | exact HEB3
          | destruct CRE as [Hb|Hs]; [left; exact Hb | right; rewrite Hsp; lia] ].
        cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
      cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 93172)) with (Z_to_bv 64 93172) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -64 - STDIO_STACK, bv_unsigned sp + -64); (EB, EB + 256)]%Z a) m3 m4)
        by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
      unfold STDIO_STACK in AGS.
      assert (FR4 : rw_cells ssegs m4 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk0))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply agrees_rw_cells; [exact AGS | exact FR3 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]).
      unhide HD3.
      assert (HD4 : rw_cells ssegs m4 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']).
      { eapply agrees_rw_cells; [exact AGS | exact HD3 |]. intros a Ha; cbn [outside cells_size csize Nat.add] in *.
        assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia. lia. }
      assert (G4 : GIo K R ps3 CL FB m4).
      { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |].
        apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, STDIO_STACK; lia|]. apply Forall_cons; [| apply Forall_nil].
        destruct EBR as [Hs|Hb]; [left; cbn [fst snd]; unfold rc_lo; lia | right; exact Hb]. }
      assert (AG4 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m4).
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
      change (Z.to_nat 256) with 256%nat in HEB4.
      hide HD4. hide HEB4. step. unhide HD4. unhide HEB4.
      eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RBS_Err _) (-1)%Z); [exact MI4 | exact ST4 | exact AG4 | exact G4 | exact OF3 | exact FR4 | exact HD4 |].
      eexists. split; [reflexivity|]. unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE.
      pose proof (snprintf_length 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string [AInt n; AInt (Z.of_nat (length got))]) as LS.
      change (Z.to_nat (256 - 1)) with 255%nat in LS.
      replace (256 - length (Fmt.snprintf 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu" [AInt n; AInt (Z.of_nat (length got))]) - 1)%nat
        with (255 - length (Fmt.snprintf 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu" [AInt n; AInt (Z.of_nat (length got))]))%nat in HEB4 by lia.
      split; [exact HEB4|]. split; [lia|]. apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2]. }
    (* [comment removed for export] *)
    destruct (Z.eq_dec (Z.of_nat (length got)) n) as [LEQ|LNE].
    { rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb]. apply (implM_ret ssegs).
      hide HD2. hide HEB2. step. rewrite (eqb_lits_eq _ _ LEQ). cbv iota. unhide HD2. unhide HEB2.
      eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RBS_Ok 1%Z); [exact MI1 | exact ST1 | exact AG02 | exact G1 | exact OF1 | exact FR | exact HD2 |].
      cbn. split; [reflexivity|]. split; [exact LEQ| exact HEB2]. }
    rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
    hide HD2. hide HEB2. ienter. step. rewrite (eqb_lits_false (Z.of_nat (length got)) n ltac:(lia) ltac:(lia) LNE). cbv iota. do 3 step. unhide HD2. unhide HEB2.
    name_sp sp (-64)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { eapply FERROR; [| exact HinF | reflexivity].
      split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    intros e ps3 ms3 PO. cbv beta in PO. destruct PO as (av3 & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 93092)) with (Z_to_bv 64 93092) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FR; [|lia].
    assert (HD3 : rw_cells ssegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']).
    { eapply agrees_rw_cells; [exact AG3 | exact HD2 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia.
      destruct CRD as [Hb|Hs]; [right; apply Hb; lia | left; lia]. }
    assert (HEB3 : rw_cells ssegs m3 EB [CB 256 ej]).
    { eapply agrees_rw_cells; [exact AG3 | exact HEB2 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      destruct CRE as [Hb|Hs]; [right; apply Hb; lia | left; lia]. }
    assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3).
    { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]. }
    clear HD2 HEB2 AG3 MI1 ST1 G1.
    destruct e.
    - (* [comment removed for export] *)
      cbv iota. destruct (ERRNO eq_refl) as [EN2 EB2]. clear ERRNO.
      unfold utp in EN2. rewrite <- TP in EN2.
      eapply implM_pure; [reflexivity|]. cbn [fst snd].
      set (err := lc_errno (ps_libc s')) in *.
      hide HD3. hide HEB3.
      cbn [Z.b2z]. step. if_false. do 4 step.
      replace (ret_pc (Z_to_bv 64 93100)) with (Z_to_bv 64 93100) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      do 5 step.
      replace (sx32 (Z_to_bv 64 err)) with (Z_to_bv 64 (s32 err)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      step.
      assert (MSG : fmt_at m3 FMT_ERR_READING "error reading dump file"%string)
        by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_ERR_READING; lia| unfold FMT_ERR_READING; cbn; lia]).
      unhide HEB3.
      name_sp sp (-64)%Z.
      eapply evt_cut.
      { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB FMT_ERR_READING err "error reading dump file"%string [] ej);
          [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB3
           | destruct CRE as [Hb|Hs]; [left; exact Hb | right; rewrite Hsp; lia] | exact EB8 ].
        split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & junk4 & -> & MI4 & ST4 & AG4 & G4 & HEB4).
      rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 93124)) with (Z_to_bv 64 93124) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      lazymatch type of FR with rw_cells _ _ ?A ?cs =>
        assert (FR4 : rw_cells ssegs m4 A cs) by (eapply agrees_rw_cells; [exact AG4 | exact FR | intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]]) end.
      clear FR. rename FR4 into FR.
      unhide HD3.
      assert (HD4 : rw_cells ssegs m4 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']).
      { eapply agrees_rw_cells; [exact AG4 | exact HD3 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
        assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia.
        split; [destruct CRD as [Hb|Hs]; [right; apply Hb; lia | left; lia]| lia]. }
      assert (AG04 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m4).
      { eapply agrees_on_trans; [exact AG03|]. eapply agrees_on_weaken; [exact AG4|]. intros a [[Ha|Ha] [_ Hn2]]; (split; [|exact Hn2]); [left; lia| right; exact Ha]. }
      hide HD4. hide HEB4. do 2 step. unhide HD4. unhide HEB4.
      eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RBS_Err _) (-1)%Z); [exact MI4 | exact ST4 | exact AG04 | exact G4 | exact OF1 | exact FR | exact HD4 |].
      exists junk4. split; [reflexivity|]. split; [exact HEB4|]. split; [pose proof (fmt_errmsg_length "error reading dump file"%string [] err); lia|].
      apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor].
    - (* [comment removed for export] *)
      cbv iota. clear ERRNO.
      destruct foe.
      + (* [comment removed for export] *) cbn [negb andb]. rewrite Bool.andb_false_r.
        hide HD3. hide HEB3. cbn [Z.b2z]. ienter. step. if_true. step. if_true. unhide HD3. unhide HEB3.
        apply evt_done. apply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' MI3 ST3 AG03 G3 OF1 FR HD3 HEB3).
      + cbn [negb]. rewrite Bool.andb_true_r. cbn [Z.b2z].
        destruct (Nat.eq_dec (length got) 0) as [L0|L0].
        * (* [comment removed for export] *)
          rewrite (proj2 (Z.eqb_eq (Z.of_nat (length got)) 0) ltac:(lia)). apply (implM_ret ssegs).
          hide HD3. hide HEB3. step. if_true. step. if_false. step. rewrite (eqb_lits_eq (Z.of_nat (length got)) 0) by lia. change (negb true) with false. cbv iota. do 2 step. unhide HD3. unhide HEB3.
          eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RBS_Eof 0%Z); [exact MI3 | exact ST3 | exact AG03 | exact G3 | exact OF1 | exact FR | exact HD3 |].
          cbn. split; [reflexivity|]. split; [lia|]. split; [reflexivity| exact HEB3].
        * (* [comment removed for export] *)
          rewrite (proj2 (Z.eqb_neq (Z.of_nat (length got)) 0) ltac:(lia)).
          hide HD3. hide HEB3. ienter. step. if_true. step. if_false. step. rewrite (nez_true (Z.of_nat (length got))) by lia. cbv iota. unhide HD3. unhide HEB3.
          apply evt_done. apply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' MI3 ST3 AG03 G3 OF1 FR HD3 HEB3).
  Qed.
  End Sz1.
  Theorem read_bytes_proof : ltac:(let t := eval cbv delta [read_bytes_proof__stmt] in read_bytes_proof__stmt in exact t).
  Proof using FERROR FMT FREAD HFL SFL SNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af D n EB lo foe dest junk ej. ltac2:(SecDiet.SzSec.closeP 'read_bytes_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RB.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB.
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

Section WithCeil.
Context {CEILV : CEIL}.
Definition FMT_ERR_READING : Z := 0x108d6.   (* [comment removed for export] *)
Definition FMT_TRUNC_PCAPNG : Z := 0x103e5. (* [comment removed for export] *)

Section RB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.

  Open Scope bv_scope.

  Definition read_bytes_proof__stmt : Prop := read_bytes_stmt HO K sites.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af D n EB lo foe dest junk ej : ltac2:(SecDiet.SzSec.tyM 'read_bytes_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma read_bytes_proof__body : ltac2:(SecDiet.SzSec.bodyP 'read_bytes_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FERROR FMT FREAD HFL SFL SNPRINTF. pin_using (fun (FERROR FMT FREAD HFL SFL SNPRINTF : unit) => tt).
 intros PRE HinF HD -> -> -> -> -> Hn HDST CRD HEB EBR DISJ EB8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    assert (CRE : client_range R CL (bv_unsigned sp) EB 256).
    { destruct EBR as [Hs|Hb]; [right; exact Hs| left]. intros a Ha. unfold iv_in_block in Hb. unfold in_block.
      apply Exists_exists in Hb as (b & Hin & Hb). apply Exists_exists. exists b. split; [exact Hin|]. cbn [fst snd] in Hb. lia. }
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold READ_BYTES_STACK, PCAP_L1_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & A5 & _).
    cbn [cb_addr cb_size fst snd] in A1, A4, A5. unfold FILE_BLOCK in A4, A5.
    pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    pose proof (rw_cells_bound _ _ _ _ HDST) as BD. cbn [cells_size csize Nat.add] in BD.
    assert (CLB : forall a, in_block CL a -> a < CEILZ).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. lia. }
    assert (EBX : EB + 256 <= CEILZ \/ bv_unsigned sp <= EB).
    { destruct CRE as [Hb|Hs]; [left; pose proof (CLB (EB + 255)%Z ltac:(apply Hb; lia)); lia| right; lia]. }
    assert (DX : (D + n <= CEILZ \/ bv_unsigned sp <= D \/ n = 0)%Z).
    { destruct (Z.eq_dec n 0%Z) as [->|NZ]; [right; right; reflexivity|].
      destruct CRD as [Hb|Hs]; [left; pose proof (CLB (D + n - 1)%Z ltac:(apply Hb; lia)); lia| right; left; lia]. }
    unfold read_bytes, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims]. unfold READ_BYTES_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide HEB. hide HDST.
    ienter. carve_frame 64%nat ST. do 19 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R s CL FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AGa : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256)) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|Ha] _]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]);
      unhide HEB; assert (HEB1 : rw_cells usegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
      unhide HDST; assert (HD1 : rw_cells usegs mm D [CB (Z.to_nat n) junk])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HDST | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia])
    end.
    clear MU WM HEB HDST.
    (* [comment removed for export] *)
    name_sp sp (-64)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { apply implM_mget. rewrite HD.
      eapply FREAD; [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact HD1
                    | destruct CRD as [Hb|Hs]; [left; exact Hb| right; rewrite Hsp; lia] ]. }
    intros got s' ms' PO. cbv beta in PO.
    destruct PO as (av & m2 & junk' & E & OF1 & MI1 & ST1 & AG1 & G1 & -> & GL & GR & HD2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 94344)) with (Z_to_bv 64 94344) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (KEEP : forall A cs, rw_cells usegs m0 A cs -> (bv_unsigned sp + -64 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells usegs m2 A cs).
    { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG1 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in FR; [|lia|cbn [cells_size csize Nat.add]; lia].
    assert (HEB2 : rw_cells usegs m2 EB [CB 256 ej]).
    { eapply agrees_rw_cells; [exact AG1 | exact HEB1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      split; [destruct CRE as [Hb|Hs]; [right; apply Hb; lia | left; lia]| lia]. }
    clear KEEP HEB1 HD1 MI.
    assert (AG02 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] [Hd _]]; (split; [|exact Hd]); [left; lia| right; exact Ha]. }
    clear AGa AG1 G0.
    unfold zlength in *. pose proof GL as GL'.
    (* [comment removed for export] *)
    assert (EXIT : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (x2' x3' : word) (m3 : mem) (ps3 : PS) (st : rb_status) (sv : Z),
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -64) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      GIo K R ps3 CL FB m3 -> ps_outfile ps3 = ps_outfile s ->
      rw_cells usegs m3 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk0))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
      match st with
      | RBS_Ok => sv = 1%Z /\ Z.of_nat (length got) = n /\ rw_cells usegs m3 EB [CB 256 ej]
      | RBS_Eof => sv = 0%Z /\ Z.of_nat (length got) = 0%Z /\ foe = false /\ rw_cells usegs m3 EB [CB 256 ej]
      | RBS_Err msg => exists junk'', sv = (-1)%Z /\ rw_cells usegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''] /\ (Z.of_nat (length msg) < 256)%Z
                       /\ Forall (fun z => 0 < z < 256)%Z msg
      end ->
      evt usegs (POSTQ (st, got) ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                 x2' x3' (Z_to_bv 64 sv) (Z_to_bv 64 Af) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x170f8) fc None m3 (seg_rom usegs))).
    { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2' x3' m3 ps3 st sv MI3 ST3 AG3 G3 OF3 FR3 HD3 HST.
      hide HD3. hide HST.
      do 10 step.
      release_frame FR3 ST3 (bv_unsigned sp).
      unhide HD3. unhide HST.
      apply evt_done. subst POSTQ. unfold read_bytes_post.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 sv), mm, junk' end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [exact OF3|].
      split; [assumption|]. split; [assumption|]. split; [exact AG3|]. split; [exact G3|]. split; [exact HD3|].
      split; [exact GR|]. split; [unfold zlength; lia|].
      destruct st as [| |msg]; [destruct HST as (-> & E1 & X); auto| destruct HST as (-> & E1 & Ef & X); unfold zlength; auto| ].
      destruct HST as (j'' & -> & X & L & OK). exists j''. auto. }
    (* [comment removed for export] *)
    assert (KSNP : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (x2' : word) (m3 : mem) (ps3 : PS),
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -64) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      GIo K R ps3 CL FB m3 -> ps_outfile ps3 = ps_outfile s ->
      rw_cells usegs m3 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk0))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
      rw_cells usegs m3 EB [CB 256 ej] ->
      implM usegs (mret (RBS_Err (Msg.trunc_pcapng n (Z.of_nat (length got))), got)) ps3 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                 x2' (Z_to_bv 64 (Z.of_nat (length got))) (Z_to_bv 64 1) (Z_to_bv 64 Af) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x170d8) fc None m3 (seg_rom usegs))).
    { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2' m3 ps3 MI3 ST3 AG3 G3 OF3 FR3 HD3 HEB3.
      apply (implM_ret usegs). hide HD3. hide HEB3.
      do 7 step.
      assert (MSG : fmt_at m3 FMT_TRUNC_PCAPNG "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
        by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_TRUNC_PCAPNG; lia| unfold FMT_TRUNC_PCAPNG; cbn; lia]).
      unhide HEB3.
      name_sp sp (-64)%Z.
      eapply evt_cut.
      { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps3 CL FB lo EB 256%Z FMT_TRUNC_PCAPNG
                  "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string [AInt n; AInt (Z.of_nat (length got))] ej);
          [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
          | reflexivity | reflexivity | reflexivity | lia | exact MSG | reflexivity | cbn; lia | | exact HEB3
          | destruct CRE as [Hb|Hs]; [left; exact Hb | right; rewrite Hsp; lia] ].
        cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
      cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 94452)) with (Z_to_bv 64 94452) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -64 - STDIO_STACK, bv_unsigned sp + -64); (EB, EB + 256)]%Z a) m3 m4)
        by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
      unfold STDIO_STACK in AGS.
      assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk0))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply agrees_rw_cells; [exact AGS | exact FR3 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]).
      unhide HD3.
      assert (HD4 : rw_cells usegs m4 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']).
      { eapply agrees_rw_cells; [exact AGS | exact HD3 |]. intros a Ha; cbn [outside cells_size csize Nat.add] in *.
        assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia. lia. }
      assert (G4 : GIo K R ps3 CL FB m4).
      { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |].
        apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, STDIO_STACK; lia|]. apply Forall_cons; [| apply Forall_nil].
        destruct EBR as [Hs|Hb]; [left; cbn [fst snd]; unfold rc_lo; lia | right; exact Hb]. }
      assert (AG4 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m4).
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
      change (Z.to_nat 256) with 256%nat in HEB4.
      hide HD4. hide HEB4. step. unhide HD4. unhide HEB4.
      eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RBS_Err _) (-1)%Z); [exact MI4 | exact ST4 | exact AG4 | exact G4 | exact OF3 | exact FR4 | exact HD4 |].
      eexists. split; [reflexivity|]. unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE.
      pose proof (snprintf_length 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string [AInt n; AInt (Z.of_nat (length got))]) as LS.
      change (Z.to_nat (256 - 1)) with 255%nat in LS.
      replace (256 - length (Fmt.snprintf 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu" [AInt n; AInt (Z.of_nat (length got))]) - 1)%nat
        with (255 - length (Fmt.snprintf 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu" [AInt n; AInt (Z.of_nat (length got))]))%nat in HEB4 by lia.
      split; [exact HEB4|]. split; [lia|]. apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2]. }
    (* [comment removed for export] *)
    destruct (Z.eq_dec (Z.of_nat (length got)) n) as [LEQ|LNE].
    { rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb]. apply (implM_ret usegs).
      hide HD2. hide HEB2. step. rewrite (eqb_lits_eq _ _ LEQ). cbv iota. unhide HD2. unhide HEB2.
      eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RBS_Ok 1%Z); [exact MI1 | exact ST1 | exact AG02 | exact G1 | exact OF1 | exact FR | exact HD2 |].
      cbn. split; [reflexivity|]. split; [exact LEQ| exact HEB2]. }
    rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
    hide HD2. hide HEB2. ienter. step. rewrite (eqb_lits_false (Z.of_nat (length got)) n ltac:(lia) ltac:(lia) LNE). cbv iota. do 3 step. unhide HD2. unhide HEB2.
    name_sp sp (-64)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { eapply FERROR; [| exact HinF | reflexivity].
      split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    intros e ps3 ms3 PO. cbv beta in PO. destruct PO as (av3 & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 94360)) with (Z_to_bv 64 94360) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FR; [|lia].
    assert (HD3 : rw_cells usegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']).
    { eapply agrees_rw_cells; [exact AG3 | exact HD2 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia.
      destruct CRD as [Hb|Hs]; [right; apply Hb; lia | left; lia]. }
    assert (HEB3 : rw_cells usegs m3 EB [CB 256 ej]).
    { eapply agrees_rw_cells; [exact AG3 | exact HEB2 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      destruct CRE as [Hb|Hs]; [right; apply Hb; lia | left; lia]. }
    assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3).
    { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]. }
    clear HD2 HEB2 AG3 MI1 ST1 G1.
    destruct e.
    - (* [comment removed for export] *)
      cbv iota. destruct (ERRNO eq_refl) as [EN2 EB2]. clear ERRNO.
      unfold utp in EN2. rewrite <- TP in EN2.
      eapply implM_pure; [reflexivity|]. cbn [fst snd].
      set (err := lc_errno (ps_libc s')) in *.
      hide HD3. hide HEB3.
      pose proof (GIo_tls K _ _ _ _ _ G3) as [_ TB]. unfold tls_block_ok_u in TB.
      pose proof TB as TB'. unfold utp in TB'. rewrite <- TP in TB'.
      assert (E4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
      { destruct TB' as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * 4 + 9)%Z. lia. }
      cbn [Z.b2z]. step. if_false. do 4 step.
      replace (ret_pc (Z_to_bv 64 94368)) with (Z_to_bv 64 94368) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      (* [comment removed for export] *)
      step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(clear - TB'; lia)).
      step. rewrite (and3_aligned (bv_unsigned tp + -164)) by (clear - TB' E4; lia). step. if_false.
      do 5 step.
      replace (sx32 (Z_to_bv 64 err)) with (Z_to_bv 64 (s32 err)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      step.
      assert (MSG : fmt_at m3 FMT_ERR_READING "error reading dump file"%string)
        by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_ERR_READING; lia| unfold FMT_ERR_READING; cbn; lia]).
      unhide HEB3.
      name_sp sp (-64)%Z.
      eapply evt_cut.
      { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s' CL FB lo EB FMT_ERR_READING err "error reading dump file"%string [] ej);
          [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB3
           | destruct CRE as [Hb|Hs]; [left; exact Hb | right; rewrite Hsp; lia] | exact EB8 ].
        split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & junk4 & -> & MI4 & ST4 & AG4 & G4 & HEB4).
      rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 94404)) with (Z_to_bv 64 94404) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      lazymatch type of FR with rw_cells _ _ ?A ?cs =>
        assert (FR4 : rw_cells usegs m4 A cs) by (eapply agrees_rw_cells; [exact AG4 | exact FR | intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]]) end.
      clear FR. rename FR4 into FR.
      unhide HD3.
      assert (HD4 : rw_cells usegs m4 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']).
      { eapply agrees_rw_cells; [exact AG4 | exact HD3 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
        assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia.
        split; [destruct CRD as [Hb|Hs]; [right; apply Hb; lia | left; lia]| lia]. }
      assert (AG04 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m4).
      { eapply agrees_on_trans; [exact AG03|]. eapply agrees_on_weaken; [exact AG4|]. intros a [[Ha|Ha] [_ Hn2]]; (split; [|exact Hn2]); [left; lia| right; exact Ha]. }
      hide HD4. hide HEB4. do 2 step. unhide HD4. unhide HEB4.
      eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RBS_Err _) (-1)%Z); [exact MI4 | exact ST4 | exact AG04 | exact G4 | exact OF1 | exact FR | exact HD4 |].
      exists junk4. split; [reflexivity|]. split; [exact HEB4|]. split; [pose proof (fmt_errmsg_length "error reading dump file"%string [] err); lia|].
      apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor].
    - (* [comment removed for export] *)
      cbv iota. clear ERRNO.
      destruct foe.
      + (* [comment removed for export] *) cbn [negb andb]. rewrite Bool.andb_false_r.
        hide HD3. hide HEB3. cbn [Z.b2z]. ienter. step. if_true. step. if_true. unhide HD3. unhide HEB3.
        apply evt_done. apply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' MI3 ST3 AG03 G3 OF1 FR HD3 HEB3).
      + cbn [negb]. rewrite Bool.andb_true_r. cbn [Z.b2z].
        destruct (Nat.eq_dec (length got) 0) as [L0|L0].
        * (* [comment removed for export] *)
          rewrite (proj2 (Z.eqb_eq (Z.of_nat (length got)) 0) ltac:(lia)). apply (implM_ret usegs).
          hide HD3. hide HEB3. step. if_true. step. if_false. step. rewrite (eqb_lits_eq (Z.of_nat (length got)) 0) by lia. change (negb true) with false. cbv iota. do 2 step. unhide HD3. unhide HEB3.
          eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RBS_Eof 0%Z); [exact MI3 | exact ST3 | exact AG03 | exact G3 | exact OF1 | exact FR | exact HD3 |].
          cbn. split; [reflexivity|]. split; [lia|]. split; [reflexivity| exact HEB3].
        * (* [comment removed for export] *)
          rewrite (proj2 (Z.eqb_neq (Z.of_nat (length got)) 0) ltac:(lia)).
          hide HD3. hide HEB3. ienter. step. if_true. step. if_false. step. rewrite (nez_true (Z.of_nat (length got))) by lia. cbv iota. unhide HD3. unhide HEB3.
          apply evt_done. apply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' MI3 ST3 AG03 G3 OF1 FR HD3 HEB3).
  Qed.
  End Sz1.
  Theorem read_bytes_proof : ltac:(let t := eval cbv delta [read_bytes_proof__stmt] in read_bytes_proof__stmt in exact t).
  Proof using FERROR FMT FREAD HFL SFL SNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af D n EB lo foe dest junk ej. ltac2:(SecDiet.SzSec.closeP 'read_bytes_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RB.

End WithCeil.
End TwB.
End F_sfpcapng_rb.
