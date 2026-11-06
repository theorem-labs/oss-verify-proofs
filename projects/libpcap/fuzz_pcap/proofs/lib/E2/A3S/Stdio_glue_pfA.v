(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase AMalloc_iface RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA Pcap_ifaceA Fuzz_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fread_top__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_fmtA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Vfprintf_leafA Stdio_repA Stdio_glueKitA StdioLawsA Stdio_glueA Stdio_glue_snA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.F_vfprintf_file OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_fprintf_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_printf_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_fmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.Printf_pitems OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Vfprintf_leafA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_snA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sbl_is_big n := lazymatch n with S _ => let b := eval vm_compute in (Nat.leb 200 n) in lazymatch b with true => idtac end end.
Local Ltac sbl_pose_in H :=
  (let T := type of H in let T' := eval hnf in T in change T' in H);
  repeat match type of H with
  | context [repeat ?b ?n] => sbl_is_big n; let z := fresh "sblz" in pose (z := repeat b n); change (repeat b n) with z in H
  | context [CB ?n _] => sbl_is_big n; let x := fresh "sblv" in pose (x := n); change n with x in H
  end.
Local Ltac sbl_subst_all :=
  repeat match goal with
  | z := repeat _ ?n |- _ => sbl_is_big n; subst z
  | x := ?n |- _ => sbl_is_big n; subst x
  end.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithRc. Context {rc : runConstT}.
#[using="Type"] Lemma fmt_pieces_small_aux : forall fuel s args,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true ->
  Forall (fun p => zlength p <= zlength s + 80 + fargs_len args) (fmt_pieces (parse_fmt_aux fuel s) args).
Proof.
  induction fuel as [|f IH]; intros s args Hlen OK.
  - destruct s as [|c s0]; [| cbn in Hlen; lia]. cbn. constructor.
  - destruct s as [|c s0]. { cbn. constructor. }
    cbn in Hlen. pose proof (fargs_len_nonneg args) as AN. destruct (Z.eqb_spec c 37) as [E37|N37].
    + subst c. rewrite parse_pct_shape in *.
      destruct (parse_conv s0) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc OK].
      cbn [fmt_pieces hd tl]. pose proof (conv_len_bound cv a OKc) as CB. unfold conv_len in CB.
      assert (LR : (List.length r' < S (List.length s0))%nat).
      { pose proof (parse_conv_cases _ _ _ PC) as SH. destruct cv;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [List.length]; lia. }
      pose proof (IH r' args' ltac:(lia) OK) as IHr. pose proof (fargs_len_nonneg args') as AN'.
      constructor; [change (zlength (@nil Z)) with 0; cbn [fargs_len]; destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; unfold zlength in *; cbn [length]; lia|].
      apply Forall_app. split.
      * apply Forall_forall. intros pc Hpc. pose proof (in_split _ _ Hpc) as (l1 & l2 & E).
        assert (zlength pc <= zlength (List.concat (Fmt.conv_pieces cv a))).
        { rewrite E, concat_app. cbn [List.concat]. rewrite !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app. pose proof (zlength_nonneg (List.concat l1)). pose proof (zlength_nonneg (List.concat l2)). lia. }
        cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
      * eapply Forall_impl; [| exact IHr]. cbv beta. intros pc Hpc. cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons.
        pose proof (zlength_nonneg r'). destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; unfold zlength in *; lia.
    + rewrite (parse_lit_shape f c s0 N37) in *.
      destruct (take_lit (c :: s0)) as [l r] eqn:TL. destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. apply andb_prop in OK as [OKl OK].
      cbn [fmt_pieces]. pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      assert (Hl : (1 <= List.length l)%nat).
      { destruct l as [|c' l0]; [| cbn; lia]. exfalso. cbn in E1. destruct R1 as [->|[r'' ->]]; [discriminate E1|]. injection E1 as E _. exact (N37 E). }
      pose proof (IH r args ltac:(lia) OK) as IHr.
      constructor; [rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons; unfold zlength in *; lia|].
      eapply Forall_impl; [| exact IHr]. cbv beta. intros pc Hpc. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
Qed.

#[using="Type"] Lemma fmt_pieces_small : forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> zlength (str fs) + 80 + fargs_len args <= PIECE_MAX -> pieces_small (fmt_pieces (fmt fs) args).
Proof.
  intros fs args OK B. unfold pieces_small. eapply Forall_impl; [| apply fmt_pieces_small_aux; [unfold fmt, parse_fmt; lia | exact OK]].
  cbv beta. intros p Hp. unfold fmt, parse_fmt in B. lia.
Qed.

(* [comment removed for export] *)
Definition fmt_facts__stmt : Prop := forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> (length args <= 2)%nat -> Forall (fun a => farg_len a <= 2^24) args ->
  zlength (str fs) < 4096 ->
  Forall (fun c => 0 <= c < 256) (str fs ++ [0])
  /\ pass1_ok (str fs ++ [0]) = true
  /\ printf_pieces (str fs ++ [0]) (to_pargs (fmt fs) args) = Some (fmt_pieces (fmt fs) args, zlength (fmt_output (fmt fs) args))
  /\ pieces_small (fmt_pieces (fmt fs) args)
  /\ 0 <= zlength (fmt_output (fmt fs) args) < 2^31 - 1.
Section Sz3.
Variables fs : ltac2:(SecDiet.SzSec.tyM 'fmt_facts__stmt "vk" @fs).
#[using="Type"] Lemma fmt_facts__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_facts__stmt "vk").
Proof.
  intros args OK L2 SM FL.
  assert (FL4 : fargs_len args <= 2 * (80 + 2^24)).
  { clear -SM L2. destruct args as [|a [|b [|c args]]]; cbn [length] in L2; [cbn; lia| | |lia].
    - inversion SM; subst. cbn [fargs_len]. lia.
    - inversion SM as [|a' l Ha SM']; subst. inversion SM'; subst. cbn [fargs_len]. lia. }
  pose proof (fmt_output_bound fs args OK) as OB. pose proof (fmt_output_nonneg (fmt fs) args) as ON.
  split; [apply str_range|]. split; [apply (fmt_pass1 fs args OK); unfold INT_MAX; lia|].
  split; [apply fmt_bridge; [exact OK| unfold INT_MAX; lia]|].
  split; [apply fmt_pieces_small; [exact OK| unfold PIECE_MAX; lia]|]. lia.
Qed.
End Sz3.
#[using="Type"] Lemma fmt_facts : ltac:(let t := eval cbv delta [fmt_facts__stmt] in fmt_facts__stmt in exact t).
Proof. intros fs args. ltac2:(SecDiet.SzSec.closeP 'fmt_facts__body "vk"). Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma s32_facts_sx : forall v, 0 <= v < 2^32 ->
  -2^31 <= s32 v < 2^31 /\ bv_unsigned (sx32 (Z_to_bv 64 v)) mod 2^32 = s32 v mod 2^32.
Proof.
  intros v Hv. pose proof (s32_facts v) as [R E]. split; [exact R|]. rewrite <- E.
  unfold sx32. rewrite (unsigned_lit v) by lia. rewrite unsigned_lit_wrap, mod32_of_mod64.
  rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.bv_swrap32_eq.
  replace ((v + 2^31) mod 2^32 - 2^31) with (v - ((v + 2^31) / 2^32) * 2^32) by (Z.div_mod_to_equations; lia).
  rewrite <- Zminus_mod_idemp_r, Z_mod_mult, Z.sub_0_r. reflexivity.
Qed.



(* [comment removed for export] *)
Definition fmt_staticA (fs : string) (A : Z) : Prop :=
  ro_bytes_b asegs A (zb (str fs ++ [0])) = true /\ 65536 <= A /\ A + zlength (str fs ++ [0]) <= 204800.
#[using="Type"] Lemma fmt_bytesA : forall m fs A, mem_inv asegs m -> fmt_staticA fs A -> bytes_at asegs m A (zb (str fs ++ [0])).
Proof.
  intros m fs A MI (RO & LO & HI). unfold zlength in HI.
  apply ro_bytes_at; [exact MI | lia | rewrite zb_length; lia |]. apply ro_bytes_b_sound. exact RO.
Qed.

(* [comment removed for export] *)
Definition fmt_call_okA (FMT : Z) (fs : string) (args : list farg) (pargs : list parg) (ps : list (list Z)) : Prop :=
  Forall (fun c => 0 <= c < 256) (str fs ++ [0]) /\ pass1_ok (str fs ++ [0]) = true
  /\ printf_pieces (str fs ++ [0]) pargs = Some (ps, zlength (fmt_output (fmt fs) args)) /\ pieces_small ps
  /\ (65536 <= FMT /\ FMT + zlength (str fs ++ [0]) <= 204800)
  /\ (forall m, mem_inv asegs m -> bytes_at asegs m FMT (zb (str fs ++ [0])))
  /\ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true
  /\ In (FMT, zlength (str fs ++ [0])) client_globals.   (* [comment removed for export] *)

#[using="Type"] Lemma fmt_call_okA_intro : forall fs FMT args,
  fmt_staticA fs FMT -> In (FMT, zlength (str fs ++ [0])) client_globals -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> (length args <= 2)%nat ->
  Forall (fun a => farg_len a <= 2^24) args -> zlength (str fs) < 4096 ->
  fmt_call_okA FMT fs args (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args).
Proof.
  intros fs FMT args FS GLB OK L2 SM FL.
  destruct (fmt_facts fs args OK L2 SM FL) as (HF & P1 & PIECES & SMALL & RB).
  pose proof FS as (RO & LO & HI).
  split; [exact HF|]. split; [exact P1|]. split; [exact PIECES|]. split; [exact SMALL|].
  split; [split; [exact LO| exact HI]|]. split; [intros m MI; exact (fmt_bytesA m fs FMT MI FS) |]. split; [exact OK | exact GLB].
Qed.
End WithRc.

Local Close Scope string_scope.

Local Ltac fmt_callA :=
  apply fmt_call_okA_intro;
    [ split; [vm_compute; reflexivity | vm_compute; split; intros HH; discriminate HH]
    | vm_compute; repeat (first [left; reflexivity | right])
    | vm_compute; reflexivity
    | cbn [length]; Lia.lia
    | repeat constructor; cbn [farg_len]; try assumption; try Lia.lia
    | vm_compute; reflexivity ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Open Scope string_scope.
Definition FS_FAILED_REMOVE : string := "failed remove, errno=%d
".
Definition FS_FAILED_OPEN : string := "failed open, errno=%d
".
Definition FS_COULDNT_OPEN : string := "Couldn't open pcap file %s
".
Definition FS_PACKET_LENGTH : string := "packet length=%d/%d
".
Local Close Scope string_scope.

Section WithRc2. Context {rc : runConstT}.
#[using="Type"] Lemma call_failed_removeA : forall v, fmt_call_okA FMT_FAILED_REMOVE FS_FAILED_REMOVE [AInt v] [PA_i (s32 v)] (pieces_failed_remove v).
Proof. intros v. change (fmt_call_okA FMT_FAILED_REMOVE FS_FAILED_REMOVE [AInt v] (to_pargs (fmt FS_FAILED_REMOVE) [AInt v]) (fmt_pieces (fmt FS_FAILED_REMOVE) [AInt v])). fmt_callA. Qed.
#[using="Type"] Lemma call_failed_openA : forall v, fmt_call_okA FMT_FAILED_OPEN FS_FAILED_OPEN [AInt v] [PA_i (s32 v)] (pieces_failed_open v).
Proof. intros v. change (fmt_call_okA FMT_FAILED_OPEN FS_FAILED_OPEN [AInt v] (to_pargs (fmt FS_FAILED_OPEN) [AInt v]) (fmt_pieces (fmt FS_FAILED_OPEN) [AInt v])). fmt_callA. Qed.
#[using="Type"] Lemma call_packet_lengthA : forall v1 v2, fmt_call_okA FMT_PACKET_LENGTH FS_PACKET_LENGTH [AInt v1; AInt v2] [PA_i (s32 v1); PA_i (s32 v2)] (pieces_packet_length v1 v2).
Proof. intros v1 v2. change (fmt_call_okA FMT_PACKET_LENGTH FS_PACKET_LENGTH [AInt v1; AInt v2] (to_pargs (fmt FS_PACKET_LENGTH) [AInt v1; AInt v2]) (fmt_pieces (fmt FS_PACKET_LENGTH) [AInt v1; AInt v2])). fmt_callA. Qed.
#[using="Type"] Lemma call_couldnt_openA : forall s, zlength s <= 2^24 -> fmt_call_okA FMT_COULDNT_OPEN FS_COULDNT_OPEN [AStr s] [PA_s s] (pieces_couldnt_open s).
Proof. intros s Hs. change (fmt_call_okA FMT_COULDNT_OPEN FS_COULDNT_OPEN [AStr s] (to_pargs (fmt FS_COULDNT_OPEN) [AStr s]) (fmt_pieces (fmt FS_COULDNT_OPEN) [AStr s])). fmt_callA. Qed.
End WithRc2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GluePf.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).

  Lemma implMG_rd_lc : forall {B} RNG (k : libc_st hptr -> M PS B) (s : PS) Q ms,
    implMG RNG (k (ps_libc s)) s Q ms -> implMG RNG (mbind (rd_lc ps_libc) k) s Q ms.
  Proof using Type. pin_using tt. intros B RNG k s Q ms IM. exact IM. Qed.

  (* [comment removed for export] *)
  Lemma in_block_FB_range : forall L RNG (s : PS) CL FB FL m a, GIOA L RNG s CL FB FL m -> in_block FB a -> 0x603000 <= a < ATOP.
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros L RNG s CL FB FL m a G HB. unfold in_block in HB. apply Exists_exists in HB. sbl_pose_in HB. destruct HB as (b & HIN & Hb). sbl_subst_all.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; right; exact HIN)) as ((ABLK & _) & _).
    unfold ablk, AIMG_HI, KLS in ABLK. pose proof (@ATOP_lo rc). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition GIOA_stdout_step__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' (f' : file_st) lo SP,
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo <= SP ->
    munch [(lo, SP); (A_STDOUT, A_STDOUT + 232); (A_STDOUT_BUF, A_STDOUT_BUF + 1024)] m m' -> wmono asegs m m' ->
    FILE_R m' f' A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 -> stdout_inv f' ->
    GIOA L RNG (set_libc (set_stdout f' (ps_libc s)) s) CL FB FL m' /\ agrees_on (client_keeps FL CL SP) m m'.
  Section Sz13.
  Variables L RNG s CL FB FL m m' f' lo SP : ltac2:(SecDiet.SzSec.tyM 'GIOA_stdout_step__stmt "vvvvvvvvvvv" @L).
  Lemma GIOA_stdout_step__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_stdout_step__stmt "vvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G LOA LOSP MU WM FR' INV'.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (@ATOP_lo rc) as ATL.
    unfold A_STDOUT, A_STDOUT_BUF in MU.
    assert (HW : Forall (stdio_ivA FB SP) [(lo, SP); (695440, 695440 + 232); (6299856, 6299856 + 1024)]).
    { unfold stdio_ivA. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd];
        [left; lia | right; right; left; lia | right; right; right; left; lia]. }
    rewrite <- (app_nil_r [(lo, SP); (695440, 695440 + 232); (6299856, 6299856 + 1024)]) in MU.
    split.
    2:{ eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| exact HW| lia]|].
        intros a Ha. split; [exact Ha | exact I]. }
    eapply (gs_step _ GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| exact HW| apply Forall_nil| lia| |].
    { eapply (errno_cell_kept FO GIOA fflagA GL GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| | apply Forall_nil].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd];
        [left; lia | right; right; left; lia | right; right; right; lia]. }
    rewrite app_nil_r in MU.
    unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_stdout].
    assert (AG : agrees_on (fun a => outside [(lo, SP); (695440, 695440 + 232); (6299856, 6299856 + 1024)] a) m m').
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. exact Hs. }
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SEI as (_ & _ & SEbs & _).
    split; [exact FR'|]. split; [exact INV'|].
    split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; cbn [outside]; lia | rewrite SEbs; intros a Ha; cbn [outside]; lia]. }
    split; [exact SEI|].
    split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; cbn [outside]; lia. }
    split; [eapply agrees_rw_cells; [exact AG | exact U1 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact U2 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact U3 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact OL | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact OH | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [| exact ND].
    eapply files_R_agree; [exact FS | exact AG |]. intros a Ha. pose proof (in_block_FB_range _ _ _ _ _ _ _ _ G Ha) as R. cbn [outside]. lia.
  Qed.
  End Sz13.
  Lemma GIOA_stdout_step : ltac:(let t := eval cbv delta [GIOA_stdout_step__stmt] in GIOA_stdout_step__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' f' lo SP. ltac2:(SecDiet.SzSec.closeP 'GIOA_stdout_step__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition printf_d_genA__stmt : Prop := forall FMT (mk : Z -> list (list Z)) fs,
    (forall v, fmt_call_okA FMT fs [AInt v] [PA_i (s32 v)] (mk v)) -> printf_d_stmt_o GIOA FMT mk.
  Section Sz14.
  Variables FMT mk fs ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo v : ltac2:(SecDiet.SzSec.tyM 'printf_d_genA__stmt "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @FMT).
  Lemma printf_d_genA__body : ltac2:(SecDiet.SzSec.bodyP 'printf_d_genA__stmt "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros CALL.
 intros SPO -> -> HV.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK in *.
    sbl_pose_in SO. destruct SO as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SOI as (CH1 & FD1 & BS1 & NRD1 & NWR1 & EOF1 & RB1 & LBF1).
    pose proof (CALL v) as (HF & P1 & PIECES & SMALL & HA & BYf & IOK & GLB).
    pose proof (s32_facts v) as [S32a S32b].
    rewrite BS1 in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    destruct (pitems_facts fs [AInt v] [Z_to_bv 64 v] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (PW : pwords_ok RNG lo sp m (pitems fs [AInt v] [Z_to_bv 64 v]) [Z_to_bv 64 v; a2; a3; a4; a5; a6; a7]).
    { apply (pwords_ok_more RNG lo sp m _ [Z_to_bv 64 v] [a2; a3; a4; a5; a6; a7]).
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact I | apply Forall2_nil]]. }
    pose proof (gia_global_mobjA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G GLB RIMG RIMGSH) as MOF.
    destruct (gs_statics _ GSL _ _ _ _ _ _ _ G RIMG RIMGSH) as [SOS1 SOS2].
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    unfold s_printf, printf. apply implMG_rd_lc.
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold PRINTF_ENTRY.
      eapply (printf_i_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT lo
                (str fs ++ [0]) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 [PA_i (s32 v)] (mk v) _ canary (zb (str fs)) (pitems fs [AInt v] [Z_to_bv 64 v]) true true)
        with (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stdout (ps_libc s)))) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | reflexivity | exact FC | exact FLG | exact BUF | exact BP | exact WB0
             | exact BS1 | exact WBL | exact NWR1 | exact RB1
             | (rewrite CH1; left; exact FD1) | exact CH1 | (intros _; reflexivity)
             | (apply BYf; exact MI)
             | (cbn [args_ok]; split; [split; [exact S32a | exact S32b] | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact PW
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp) G); (keep_hyps rc lo v LOA sp LOB L SPT TOP47; lia))
             | (apply mobjA_sobj; [exact MOF | unfold zlength in *; (keep_hyps rc H hptr FMT fs s v HA; lia)])
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc v; lia) | (keep_hyps rc v; lia)])
             | (eapply sobj_sub; [exact SOS1 | unfold A_STDOUT; (keep_hyps rc lo v GLO sp LOA LOB; lia) | (keep_hyps rc sp L v SPT TOP47; lia) | unfold A_STDOUT; (keep_hyps rc v; lia)])
             | (eapply sobj_sub; [exact SOS2 | unfold A_STDOUT_BUF; (keep_hyps rc lo v GLO sp LOA LOB; lia) | (keep_hyps rc sp L v SPT TOP47; lia) | unfold A_STDOUT_BUF; (keep_hyps rc v; lia)])
             | (eapply rng_sub'; [exact RIMG | unfold A_STDOUT_BUF; (keep_hyps rc v; lia)])
             | (unfold PRINTF_I_DEPTH, GLOBALS_TOP in *; (keep_hyps rc sp lo v LOB GLO L SPT TOP47; lia))
             | idtac "PFD-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    sbl_pose_in PO. destruct PO as (-> & INV' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & flags' & mode' & bufbytes' & m' & rpos' & rend'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & RP' & FL' & BUF' & BP' & WBL'). sbl_subst_all.
    assert (BSnz : f_bufsize (lc_stdout (ps_libc s)) <> 0) by (rewrite BS1; unfold BUFSIZ; lia).
    pose proof (vfprintf_leaf_buffered _ _ _ _ _ BSnz LF) as [FX _].
    pose proof (vfprintf_leaf_buffered_wl _ _ _ _ _ BSnz LF) as WL.
    pose proof INV' as (WA' & RB' & BS' & NW' & FDC' & _ & CHN').
    rewrite RB1 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    assert (FR' : FILE_R m' f' A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { exists flags', mode', rpos', tail, bufbytes'.
      rewrite WA', RB', BS'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      assert (Erend : rend' = rpos') by (rewrite RB1 in RP'; change (zlength (@nil Z)) with 0 in RP'; lia).
      rewrite Erend in FC'.
      split; [exact FC'|]. split; [exact FL'|]. split; [exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN]. }
    assert (SOI' : stdout_inv f').
    { pose proof FX as (E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & SW' & LB').
      unfold stdout_inv. rewrite E1, E2, E4, E5, E6.
      split; [exact CH1|]. split; [exact FD1|]. split; [exact BS'|]. split; [exact NRD1|]. split; [exact NWR1|]. split; [exact EOF1|]. split; [exact RB'|].
      destruct WL as [[W1 W2]|[W1 W2]]; rewrite W1, ?W2; [exact LBF1| intros X; discriminate X]. }
    destruct (GIOA_stdout_step L RNG s CL FB FL m m' f' lo (bv_unsigned sp) G LOA ltac:(lia) MU WM FR' SOI') as [G' AG].
    unfold upd_lc. apply implMG_upd. apply evtF_done.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz14.
  Lemma printf_d_genA : ltac:(let t := eval cbv delta [printf_d_genA__stmt] in printf_d_genA__stmt in exact t).
  Proof using GL GSL. intros FMT mk fs CALL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo v. ltac2:(SecDiet.SzSec.closeP 'printf_d_genA__body "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Theorem printf_failed_remove_proofA : printf_d_stmt_o GIOA FMT_FAILED_REMOVE pieces_failed_remove.
  Proof using GL GSL. exact (printf_d_genA _ _ _ call_failed_removeA). Qed.
  Theorem printf_failed_open_proofA : printf_d_stmt_o GIOA FMT_FAILED_OPEN pieces_failed_open.
  Proof using GL GSL. exact (printf_d_genA _ _ _ call_failed_openA). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vfprintf_nowr_unrA : forall RNG (fs0 : file_st) ps (s : PS) (Q : unit -> PS -> footprint -> machine_state -> Prop) ms h,
    heap_file_inv fs0 -> f_nowr fs0 = true ->
    implMG RNG (mbind (vfprintf fs0 ps) (store_file ps_libc set_libc eqb h)) s Q ms.
  Proof using Type. pin_using tt.
    intros RNG fs0 ps s Q ms h INV NOWR. pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct (NOWRi NOWR) as [WACT _].
    unfold vfprintf. rewrite BS. change (BUFSIZ =? 0) with false. cbv iota.
    unfold ensure_w. rewrite WACT. unfold towrite. rewrite NOWR.
    apply implMG_bind_assoc. cbn [mbind munr ebind bind]. apply implMG_unr.
  Qed.

  (* [comment removed for export] *)
  Definition hfile_after__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PS) (m : mem) (lo : Z) (canary : word) (ps : list (list Z)) (Af : Z) (fs0 : file_st) (pv nx : Z) (tail : list byte) (rp : Z)
      (f' : file_st) (st' : PS) (ms' : machine_state),
    heap_file_inv fs0 -> f_nowr fs0 = false -> 0 <= rp -> rp + zlength (f_rbuf fs0) < 2^63 -> firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
    vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail lo
                       canary true false rp (rp + zlength (f_rbuf fs0)) m s f' st' ms' ->
    mleaf (vfprintf fs0 ps) s f' st' ->
    st' = s /\
    exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (Af, Af + 232); (Af + FILE_BUF_OFF, Af + FILE_BUF_OFF + 1024)] m m' /\ wmono asegs m m'
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx /\ heap_file_inv f'.
  Section Sz18.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s m lo canary ps Af fs0 pv nx tail rp f' st' ms' : ltac2:(SecDiet.SzSec.tyM 'hfile_after__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma hfile_after__body : ltac2:(SecDiet.SzSec.bodyP 'hfile_after__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc.
 intros INV NOWR RP0 RP1 GLN PO LF.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    assert (RBN : f_rbuf fs0 = []) by (apply NORDi; rewrite NRW, NOWR; reflexivity).
    rewrite RBN in RP1. change (zlength (@nil Z)) with 0 in RP1.
    sbl_pose_in PO. destruct PO as (-> & INV' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & flags' & mode' & bufbytes' & m' & rpos' & rend'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & RP' & FL' & BUF' & BP' & WBL'). sbl_subst_all.
    assert (BSnz : f_bufsize fs0 <> 0) by (rewrite BS; unfold BUFSIZ; lia).
    pose proof (vfprintf_leaf_buffered _ _ _ _ _ BSnz LF) as [FX _].
    pose proof INV' as (WA' & RB' & BS' & NW' & FDC' & _ & CHN').
    split; [reflexivity|].
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split; [| exact (heap_file_inv_fx fs0 f' INV NOWR FX)].
    exists flags', mode', rpos', tail, bufbytes'.
    rewrite WA', RB', BS'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
    assert (Erend : rend' = rpos') by (rewrite RBN in RP'; change (zlength (@nil Z)) with 0 in RP'; lia).
    rewrite Erend in FC'.
    split; [exact FC'|]. split; [exact FL'|]. split; [exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [exact WBL'|].
    split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN].
  Qed.
  End Sz18.
  Lemma hfile_after : ltac:(let t := eval cbv delta [hfile_after__stmt] in hfile_after__stmt in exact t).
  Proof using rc. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s m lo canary ps Af fs0 pv nx tail rp f' st' ms'. ltac2:(SecDiet.SzSec.closeP 'hfile_after__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fprintf_packet_length_proofA__stmt : Prop := fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Section Sz19.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo v1 v2 : ltac2:(SecDiet.SzSec.tyM 'fprintf_packet_length_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fprintf_packet_length_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_packet_length_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
 intros SPO HIN -> -> -> -> HV1 HV2.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs0 & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    unfold STDIO_STACK, FILE_BLOCK in *.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    unfold s_fprintf, Stdio.fprintf, with_file_.
    apply implMG_bind_assoc. eapply implMG_lookup_file; [exact LK|].
    destruct (f_nowr fs0) eqn:NOWR; [apply vfprintf_nowr_unrA; [exact INV| exact NOWR]|].
    assert (RBN : f_rbuf fs0 = []) by (apply NORDi; rewrite NRW; reflexivity).
    sbl_pose_in FR. destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    rewrite BS in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    pose proof (call_packet_lengthA v1 v2) as (HF & P1 & PIECES & SMALL & HA & BYf & IOK & GLB).
    pose proof (s32_facts_sx v1 HV1) as [S1a S1b]. pose proof (s32_facts_sx v2 HV2) as [S2a S2b].
    destruct (pitems_facts FS_PACKET_LENGTH [AInt v1; AInt v2] [sx32 (Z_to_bv 64 v1); sx32 (Z_to_bv 64 v2)] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (PW : pwords_ok RNG lo sp m (pitems FS_PACKET_LENGTH [AInt v1; AInt v2] [sx32 (Z_to_bv 64 v1); sx32 (Z_to_bv 64 v2)])
                   [sx32 (Z_to_bv 64 v1); sx32 (Z_to_bv 64 v2); a4; a5; a6; a7]).
    { apply (pwords_ok_more RNG lo sp m _ [sx32 (Z_to_bv 64 v1); sx32 (Z_to_bv 64 v2)] [a4; a5; a6; a7]).
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact I | apply Forall2_cons; [exact I | apply Forall2_nil]]]. }
    pose proof (gia_global_mobjA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G GLB RIMG RIMGSH) as MOF.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    assert (SOFp : sobj RNG m Af (Af + 232)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (SOB : sobj RNG m (Af + 240) (Af + 240 + 1024)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (RGFp : rng RNG Af 232) by (eapply rng_sub'; [exact RGF | lia]).
    assert (RGB : rng RNG (Af + 240) 1024) by (eapply rng_sub'; [exact RGF | lia]).
    assert (IESF : iesafe [(Af, Af + 232)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (IESB : iesafe [(Af + 240, Af + 240 + 1024)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold FPRINTF_ENTRY.
      eapply (fprintf_i_file_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail
                FMT_PACKET_LENGTH lo (str FS_PACKET_LENGTH ++ [0]) (sx32 (Z_to_bv 64 v1)) (sx32 (Z_to_bv 64 v2)) a4 a5 a6 a7 [PA_i (s32 v1); PA_i (s32 v2)]
                (pieces_packet_length v1 v2) _ canary (zb (str FS_PACKET_LENGTH)) (pitems FS_PACKET_LENGTH [AInt v1; AInt v2] [sx32 (Z_to_bv 64 v1); sx32 (Z_to_bv 64 v2)]) true false)
        with (rpos := rp) (rend := rp + zlength (f_rbuf fs0)) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: unfold FILE_BUF_OFF.
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | exact IESF | exact IESB | exact RGFp | exact RGB
             | reflexivity | exact FC | exact FLG | exact BUF | exact BP | exact WB0
             | exact BS | exact WBL | exact NOWR | exact RBN
             | (rewrite NCH; exact FD) | exact NCH | (intros _; reflexivity)
             | (apply BYf; exact MI)
             | (cbn [args_ok]; split; [split; [exact S1a | exact S1b] |]; split; [split; [exact S2a | exact S2b] | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact PW | exact SOFp | exact SOB
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp) G); (keep_hyps rc lo v1 v2 LOA sp LOB L SPT TOP47; lia))
             | (apply mobjA_sobj; [exact MOF | unfold zlength in *; (keep_hyps rc v1 v2 fs0 HA; lia)])
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc v1 v2; lia) | (keep_hyps rc v1 v2; lia)])
             | (right; unfold GLOBALS_TOP; (keep_hyps rc Af lo v1 v2 FALO FA3; lia))
             | (unfold FPRINTF_I_DEPTH, GLOBALS_TOP in *; (keep_hyps rc sp lo v1 v2 LOB GLO L SPT TOP47; lia))
             | idtac "FPL-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    destruct (hfile_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s m lo canary _ Af fs0 pv nx tail rp f' st' ms' INV NOWR RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FR' & INV').
    unfold FILE_BUF_OFF in MU.
    rewrite <- (app_nil_r [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]) in MU.
    destruct (GIOA_file_step HO FO GIOA fflagA GL GSL EQB L RNG s CL FB FL m m' f Af f' pv nx [] lo (bv_unsigned sp) G HIN LOA ltac:(lia) MU WM ltac:(apply Forall_nil) UPD FR' INV') as [G' KP].
    unfold store_file, upd_lc. apply implMG_upd. apply evtF_done.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply agrees_on_weaken; [exact KP|]. intros a Ha. split; [exact Ha| exact I]. }
    exact G'.
  Qed.
  End Sz19.
  Theorem fprintf_packet_length_proofA : ltac:(let t := eval cbv delta [fprintf_packet_length_proofA__stmt] in fprintf_packet_length_proofA__stmt in exact t).
  Proof using EQB GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo v1 v2. ltac2:(SecDiet.SzSec.closeP 'fprintf_packet_length_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition str_arg_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m lo SP Fp FS B BS ap P (str slack : list byte),
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo <= ap -> ap + 8 <= SP ->
    bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
    (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
    cobjA RNG m FL CL P (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) -> Z.of_nat (length slack) <= 2^24 ->
    (P + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= Fp \/ Fp + FS <= P) ->
    (P + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= B \/ B + BS <= P) ->
    arg_ok Fp FS B BS RNG m lo SP ap (Z_to_bv 64 P) (PA_s (map bv_unsigned str))
    /\ (forall sp : word, bv_unsigned sp = SP -> pword_ok RNG lo sp m (AStr (map bv_unsigned str)) (Z_to_bv 64 P)).
  Section Sz20.
  Variables L RNG s CL FB FL m lo SP Fp FS B BS ap P str slack : ltac2:(SecDiet.SzSec.tyM 'str_arg_factsA__stmt "vvvvvvvvvvvvvvvvv" @L).
  Lemma str_arg_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'str_arg_factsA__stmt "vvvvvvvvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOA LAP APSP BY NZ LB PAD CR SLK DF DB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof (pad8_range (P + Z.of_nat (length str) + 1)) as PR. unfold pad8 in PR.
    set (pd := (- (P + Z.of_nat (length str) + 1)) mod 8) in *.
    destruct (cobjA_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ P _ lo G CR ltac:(lia) LOA) as (D0 & DLO & D3 & D47 & SOD & RGD & IESD & _).
    assert (EP : bv_unsigned (Z_to_bv 64 P : word) = P) by (apply unsigned_lit; lia).
    assert (SOS : sobj RNG m P (P + (Z.of_nat (length str) + 1))) by (eapply sobj_sub; [exact SOD | lia | lia | lia]).
    assert (NZF : Forall (fun b : byte => bv_unsigned b <> 0) str).
    { apply Forall_forall. intros b Hb E. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|].
      rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b), E. reflexivity. }
    split.
    - cbn [arg_ok]. rewrite EP. exists (firstn (Z.to_nat pd) slack).
      assert (LS : length (firstn (Z.to_nat pd) slack) = Z.to_nat pd) by (rewrite length_firstn; lia).
      unfold zlength. rewrite length_map, LS.
      split. { rewrite zb_unsigned. rewrite <- (firstn_skipn (Z.to_nat pd) slack) in BY.
               change (str ++ Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack ++ skipn (Z.to_nat pd) slack)
                 with (str ++ (Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack) ++ skipn (Z.to_nat pd) slack) in BY.
               rewrite app_assoc in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split. { apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
               pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
               pose proof (proj1 (Forall_forall _ _) NZF b Hb) as Nb. cbv beta in Nb. lia. }
      split; [lia|]. split; [lia|]. split; [left; lia|]. split; [lia|]. split; [lia|]. split; [left; lia|]. split; [lia|].
      split; [eapply rng_sub'; [exact RGD | lia]|].
      replace (P + Z.of_nat (length str) + 1) with (P + (Z.of_nat (length str) + 1)) by lia. exact SOS.
    - intros sp ESP. cbn [pword_ok]. rewrite EP, zb_unsigned. unfold pstrL.
      split. { change (str ++ Z_to_bv 8 0 :: slack) with (str ++ [Z_to_bv 8 0] ++ slack) in BY. rewrite app_assoc in BY.
               apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split; [exact NZF|]. split; [left; lia|]. split; [lia|]. split; [exact SOS|]. eapply rng_sub'; [exact RGD | lia].
  Qed.
  End Sz20.
  Lemma str_arg_factsA : ltac:(let t := eval cbv delta [str_arg_factsA__stmt] in str_arg_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m lo SP Fp FS B BS ap P str slack. ltac2:(SecDiet.SzSec.closeP 'str_arg_factsA__body "vvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fprintf_s_stmt_oS (FMT : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af lo P : Z) (str slack : list byte),
      std_pre_o GIOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
      cobjA RNG m FL CL P (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) -> Z.of_nat (length slack) <= 2^24 ->
      implMG RNG (s_fprintf HO f (mk (map bv_unsigned str))) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIOA L RNG' s' CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fprintf_couldnt_open_proofA__stmt : Prop := fprintf_s_stmt_o HO GIOA FMT_COULDNT_OPEN pieces_couldnt_open.
  Section Sz21.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo P str slack : ltac2:(SecDiet.SzSec.tyM 'fprintf_couldnt_open_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fprintf_couldnt_open_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_couldnt_open_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
 intros SPO HIN -> -> -> BY NZ LEN PAD CR SLK.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs0 & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    pose proof (cobjA_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ P _ lo G CR ltac:(lia) LOA) as (_ & _ & _ & _ & _ & _ & _ & DAP).
    pose proof (DAP _ _ HIN) as DAPf.
    unfold STDIO_STACK, FILE_BLOCK in *.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    unfold s_fprintf, Stdio.fprintf, with_file_.
    apply implMG_bind_assoc. eapply implMG_lookup_file; [exact LK|].
    destruct (f_nowr fs0) eqn:NOWR; [apply vfprintf_nowr_unrA; [exact INV| exact NOWR]|].
    assert (RBN : f_rbuf fs0 = []) by (apply NORDi; rewrite NRW; reflexivity).
    sbl_pose_in FR. destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    rewrite BS in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    assert (EL : zlength (map bv_unsigned str) = Z.of_nat (length str)) by (unfold zlength; rewrite length_map; reflexivity).
    pose proof (call_couldnt_openA (map bv_unsigned str) ltac:(rewrite EL; lia)) as (HF & P1 & PIECES & SMALL & HA & BYf & IOK & GLB).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    destruct (str_arg_factsA L RNG s CL FB FL m lo (bv_unsigned sp) Af 232 (Af + 240) 1024 (bv_unsigned sp - 480) P str slack
                G LOA ltac:(lia) ltac:(lia) BY NZ LEN PAD CR SLK ltac:(lia) ltac:(lia)) as [AOK1 PWD1].
    destruct (pitems_facts FS_COULDNT_OPEN [AStr (map bv_unsigned str)] [Z_to_bv 64 P] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (PW : pwords_ok RNG lo sp m (pitems FS_COULDNT_OPEN [AStr (map bv_unsigned str)] [Z_to_bv 64 P]) [Z_to_bv 64 P; a3; a4; a5; a6; a7]).
    { apply (pwords_ok_more RNG lo sp m _ [Z_to_bv 64 P] [a3; a4; a5; a6; a7]).
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact (PWD1 sp eq_refl) | apply Forall2_nil]]. }
    pose proof (gia_global_mobjA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G GLB RIMG RIMGSH) as MOF.
    assert (SOFp : sobj RNG m Af (Af + 232)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (SOB : sobj RNG m (Af + 240) (Af + 240 + 1024)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (RGFp : rng RNG Af 232) by (eapply rng_sub'; [exact RGF | lia]).
    assert (RGB : rng RNG (Af + 240) 1024) by (eapply rng_sub'; [exact RGF | lia]).
    assert (IESF : iesafe [(Af, Af + 232)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (IESB : iesafe [(Af + 240, Af + 240 + 1024)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold FPRINTF_ENTRY.
      eapply (fprintf_i_file_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail
                FMT_COULDNT_OPEN lo (Fmt.str FS_COULDNT_OPEN ++ [0]) (Z_to_bv 64 P) a3 a4 a5 a6 a7 [PA_s (map bv_unsigned str)]
                (pieces_couldnt_open (map bv_unsigned str)) _ canary (zb (Fmt.str FS_COULDNT_OPEN)) (pitems FS_COULDNT_OPEN [AStr (map bv_unsigned str)] [Z_to_bv 64 P]) true false)
        with (rpos := rp) (rend := rp + zlength (f_rbuf fs0)) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: unfold FILE_BUF_OFF.
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | exact IESF | exact IESB | exact RGFp | exact RGB
             | reflexivity | exact FC | exact FLG | exact BUF | exact BP | exact WB0
             | exact BS | exact WBL | exact NOWR | exact RBN
             | (rewrite NCH; exact FD) | exact NCH | (intros _; reflexivity)
             | (apply BYf; exact MI)
             | (cbn [args_ok]; split; [exact AOK1 | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact PW | exact SOFp | exact SOB
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp) G); (keep_hyps rc lo P str slack LOA sp LOB L SPT TOP47; lia))
             | (apply mobjA_sobj; [exact MOF | unfold zlength in *; (keep_hyps rc P str slack fs0 HA; lia)])
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc P str slack; lia) | (keep_hyps rc P str slack; lia)])
             | (right; unfold GLOBALS_TOP; (keep_hyps rc Af lo P str slack FALO FA3; lia))
             | (unfold FPRINTF_I_DEPTH, GLOBALS_TOP in *; (keep_hyps rc sp lo P str slack LOB GLO L SPT TOP47; lia))
             | idtac "FCO-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    destruct (hfile_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s m lo canary _ Af fs0 pv nx tail rp f' st' ms' INV NOWR RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FR' & INV').
    unfold FILE_BUF_OFF in MU.
    rewrite <- (app_nil_r [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]) in MU.
    destruct (GIOA_file_step HO FO GIOA fflagA GL GSL EQB L RNG s CL FB FL m m' f Af f' pv nx [] lo (bv_unsigned sp) G HIN LOA ltac:(lia) MU WM ltac:(apply Forall_nil) UPD FR' INV') as [G' KP].
    unfold store_file, upd_lc. apply implMG_upd. apply evtF_done.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply agrees_on_weaken; [exact KP|]. intros a Ha. split; [exact Ha| exact I]. }
    exact G'.
  Qed.
  End Sz21.
  Theorem fprintf_couldnt_open_proofA : ltac:(let t := eval cbv delta [fprintf_couldnt_open_proofA__stmt] in fprintf_couldnt_open_proofA__stmt in exact t).
  Proof using EQB GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo P str slack. ltac2:(SecDiet.SzSec.closeP 'fprintf_couldnt_open_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GluePf.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.F_vfprintf_file.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_fprintf_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_printf_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_fmtA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.Printf_pitems.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Vfprintf_leafA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_snA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sbl_is_big n := lazymatch n with S _ => let b := eval vm_compute in (Nat.leb 200 n) in lazymatch b with true => idtac end end.
Local Ltac sbl_pose_in H :=
  (let T := type of H in let T' := eval hnf in T in change T' in H);
  repeat match type of H with
  | context [repeat ?b ?n] => sbl_is_big n; let z := fresh "sblz" in pose (z := repeat b n); change (repeat b n) with z in H
  | context [CB ?n _] => sbl_is_big n; let x := fresh "sblv" in pose (x := n); change n with x in H
  end.
Local Ltac sbl_subst_all :=
  repeat match goal with
  | z := repeat _ ?n |- _ => sbl_is_big n; subst z
  | x := ?n |- _ => sbl_is_big n; subst x
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithRc. Context {rc : runConstT}.
#[using="Type"] Lemma fmt_pieces_small_aux : forall fuel s args,
  (List.length s <= fuel)%nat -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux fuel s) args = true ->
  Forall (fun p => zlength p <= zlength s + 80 + fargs_len args) (fmt_pieces (parse_fmt_aux fuel s) args).
Proof.
  induction fuel as [|f IH]; intros s args Hlen OK.
  - destruct s as [|c s0]; [| cbn in Hlen; lia]. cbn. constructor.
  - destruct s as [|c s0]. { cbn. constructor. }
    cbn in Hlen. pose proof (fargs_len_nonneg args) as AN. destruct (Z.eqb_spec c 37) as [E37|N37].
    + subst c. rewrite parse_pct_shape in *.
      destruct (parse_conv s0) as [[cv r']|] eqn:PC; [| cbn in OK; discriminate].
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. destruct args as [|a args']; [discriminate|]. apply andb_prop in OK as [OKc OK].
      cbn [fmt_pieces hd tl]. pose proof (conv_len_bound cv a OKc) as CB. unfold conv_len in CB.
      assert (LR : (List.length r' < S (List.length s0))%nat).
      { pose proof (parse_conv_cases _ _ _ PC) as SH. destruct cv;
          repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst s0; cbn [List.length]; lia. }
      pose proof (IH r' args' ltac:(lia) OK) as IHr. pose proof (fargs_len_nonneg args') as AN'.
      constructor; [change (zlength (@nil Z)) with 0; cbn [fargs_len]; destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; unfold zlength in *; cbn [length]; lia|].
      apply Forall_app. split.
      * apply Forall_forall. intros pc Hpc. pose proof (in_split _ _ Hpc) as (l1 & l2 & E).
        assert (zlength pc <= zlength (List.concat (Fmt.conv_pieces cv a))).
        { rewrite E, concat_app. cbn [List.concat]. rewrite !OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app. pose proof (zlength_nonneg (List.concat l1)). pose proof (zlength_nonneg (List.concat l2)). lia. }
        cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
      * eapply Forall_impl; [| exact IHr]. cbv beta. intros pc Hpc. cbn [fargs_len]. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons.
        pose proof (zlength_nonneg r'). destruct a as [z|cs]; cbn; [| pose proof (zlength_nonneg cs)]; unfold zlength in *; lia.
    + rewrite (parse_lit_shape f c s0 N37) in *.
      destruct (take_lit (c :: s0)) as [l r] eqn:TL. destruct (take_lit_spec _ _ _ TL) as (E1 & N1 & R1).
      cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok] in OK. apply andb_prop in OK as [OKl OK].
      cbn [fmt_pieces]. pose proof (f_equal (@List.length Z) E1) as LEN. rewrite length_app in LEN. cbn [List.length] in LEN.
      assert (Hl : (1 <= List.length l)%nat).
      { destruct l as [|c' l0]; [| cbn; lia]. exfalso. cbn in E1. destruct R1 as [->|[r'' ->]]; [discriminate E1|]. injection E1 as E _. exact (N37 E). }
      pose proof (IH r args ltac:(lia) OK) as IHr.
      constructor; [rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons; unfold zlength in *; lia|].
      eapply Forall_impl; [| exact IHr]. cbv beta. intros pc Hpc. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_cons. unfold zlength in *. lia.
Qed.

#[using="Type"] Lemma fmt_pieces_small : forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> zlength (str fs) + 80 + fargs_len args <= PIECE_MAX -> pieces_small (fmt_pieces (fmt fs) args).
Proof.
  intros fs args OK B. unfold pieces_small. eapply Forall_impl; [| apply fmt_pieces_small_aux; [unfold fmt, parse_fmt; lia | exact OK]].
  cbv beta. intros p Hp. unfold fmt, parse_fmt in B. lia.
Qed.

(* [comment removed for export] *)
Definition fmt_facts__stmt : Prop := forall fs args,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> (length args <= 2)%nat -> Forall (fun a => farg_len a <= 2^24) args ->
  zlength (str fs) < 4096 ->
  Forall (fun c => 0 <= c < 256) (str fs ++ [0])
  /\ pass1_ok (str fs ++ [0]) = true
  /\ printf_pieces (str fs ++ [0]) (to_pargs (fmt fs) args) = Some (fmt_pieces (fmt fs) args, zlength (fmt_output (fmt fs) args))
  /\ pieces_small (fmt_pieces (fmt fs) args)
  /\ 0 <= zlength (fmt_output (fmt fs) args) < 2^31 - 1.
Section Sz3.
Variables fs : ltac2:(SecDiet.SzSec.tyM 'fmt_facts__stmt "vk" @fs).
#[using="Type"] Lemma fmt_facts__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_facts__stmt "vk").
Proof.
  intros args OK L2 SM FL.
  assert (FL4 : fargs_len args <= 2 * (80 + 2^24)).
  { clear -SM L2. destruct args as [|a [|b [|c args]]]; cbn [length] in L2; [cbn; lia| | |lia].
    - inversion SM; subst. cbn [fargs_len]. lia.
    - inversion SM as [|a' l Ha SM']; subst. inversion SM'; subst. cbn [fargs_len]. lia. }
  pose proof (fmt_output_bound fs args OK) as OB. pose proof (fmt_output_nonneg (fmt fs) args) as ON.
  split; [apply str_range|]. split; [apply (fmt_pass1 fs args OK); unfold INT_MAX; lia|].
  split; [apply fmt_bridge; [exact OK| unfold INT_MAX; lia]|].
  split; [apply fmt_pieces_small; [exact OK| unfold PIECE_MAX; lia]|]. lia.
Qed.
End Sz3.
#[using="Type"] Lemma fmt_facts : ltac:(let t := eval cbv delta [fmt_facts__stmt] in fmt_facts__stmt in exact t).
Proof. intros fs args. ltac2:(SecDiet.SzSec.closeP 'fmt_facts__body "vk"). Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma s32_facts_sx : forall v, 0 <= v < 2^32 ->
  -2^31 <= s32 v < 2^31 /\ bv_unsigned (sx32 (Z_to_bv 64 v)) mod 2^32 = s32 v mod 2^32.
Proof.
  intros v Hv. pose proof (s32_facts v) as [R E]. split; [exact R|]. rewrite <- E.
  unfold sx32. rewrite (unsigned_lit v) by lia. rewrite unsigned_lit_wrap, mod32_of_mod64.
  rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB.bv_swrap32_eq.
  replace ((v + 2^31) mod 2^32 - 2^31) with (v - ((v + 2^31) / 2^32) * 2^32) by (Z.div_mod_to_equations; lia).
  rewrite <- Zminus_mod_idemp_r, Z_mod_mult, Z.sub_0_r. reflexivity.
Qed.



(* [comment removed for export] *)
Definition fmt_staticA (fs : string) (A : Z) : Prop :=
  ro_bytes_b asegs A (zb (str fs ++ [0])) = true /\ 65536 <= A /\ A + zlength (str fs ++ [0]) <= 204800.
#[using="Type"] Lemma fmt_bytesA : forall m fs A, mem_inv asegs m -> fmt_staticA fs A -> bytes_at asegs m A (zb (str fs ++ [0])).
Proof.
  intros m fs A MI (RO & LO & HI). unfold zlength in HI.
  apply ro_bytes_at; [exact MI | lia | rewrite zb_length; lia |]. apply ro_bytes_b_sound. exact RO.
Qed.

(* [comment removed for export] *)
Definition fmt_call_okA (FMT : Z) (fs : string) (args : list farg) (pargs : list parg) (ps : list (list Z)) : Prop :=
  Forall (fun c => 0 <= c < 256) (str fs ++ [0]) /\ pass1_ok (str fs ++ [0]) = true
  /\ printf_pieces (str fs ++ [0]) pargs = Some (ps, zlength (fmt_output (fmt fs) args)) /\ pieces_small ps
  /\ (65536 <= FMT /\ FMT + zlength (str fs ++ [0]) <= 204800)
  /\ (forall m, mem_inv asegs m -> bytes_at asegs m FMT (zb (str fs ++ [0])))
  /\ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true
  /\ In (FMT, zlength (str fs ++ [0])) client_globals.   (* [comment removed for export] *)

#[using="Type"] Lemma fmt_call_okA_intro : forall fs FMT args,
  fmt_staticA fs FMT -> In (FMT, zlength (str fs ++ [0])) client_globals -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (fmt fs) args = true -> (length args <= 2)%nat ->
  Forall (fun a => farg_len a <= 2^24) args -> zlength (str fs) < 4096 ->
  fmt_call_okA FMT fs args (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args).
Proof.
  intros fs FMT args FS GLB OK L2 SM FL.
  destruct (fmt_facts fs args OK L2 SM FL) as (HF & P1 & PIECES & SMALL & RB).
  pose proof FS as (RO & LO & HI).
  split; [exact HF|]. split; [exact P1|]. split; [exact PIECES|]. split; [exact SMALL|].
  split; [split; [exact LO| exact HI]|]. split; [intros m MI; exact (fmt_bytesA m fs FMT MI FS) |]. split; [exact OK | exact GLB].
Qed.
End WithRc.

Local Close Scope string_scope.

Local Ltac fmt_callA :=
  apply fmt_call_okA_intro;
    [ split; [vm_compute; reflexivity | vm_compute; split; intros HH; discriminate HH]
    | vm_compute; repeat (first [left; reflexivity | right])
    | vm_compute; reflexivity
    | cbn [length]; Lia.lia
    | repeat constructor; cbn [farg_len]; try assumption; try Lia.lia
    | vm_compute; reflexivity ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Open Scope string_scope.
Definition FS_FAILED_REMOVE : string := "failed remove, errno=%d
".
Definition FS_FAILED_OPEN : string := "failed open, errno=%d
".
Definition FS_COULDNT_OPEN : string := "Couldn't open pcap file %s
".
Definition FS_PACKET_LENGTH : string := "packet length=%d/%d
".
Local Close Scope string_scope.

Section WithRc2. Context {rc : runConstT}.
#[using="Type"] Lemma call_failed_removeA : forall v, fmt_call_okA FMT_FAILED_REMOVE FS_FAILED_REMOVE [AInt v] [PA_i (s32 v)] (pieces_failed_remove v).
Proof. intros v. change (fmt_call_okA FMT_FAILED_REMOVE FS_FAILED_REMOVE [AInt v] (to_pargs (fmt FS_FAILED_REMOVE) [AInt v]) (fmt_pieces (fmt FS_FAILED_REMOVE) [AInt v])). fmt_callA. Qed.
#[using="Type"] Lemma call_failed_openA : forall v, fmt_call_okA FMT_FAILED_OPEN FS_FAILED_OPEN [AInt v] [PA_i (s32 v)] (pieces_failed_open v).
Proof. intros v. change (fmt_call_okA FMT_FAILED_OPEN FS_FAILED_OPEN [AInt v] (to_pargs (fmt FS_FAILED_OPEN) [AInt v]) (fmt_pieces (fmt FS_FAILED_OPEN) [AInt v])). fmt_callA. Qed.
#[using="Type"] Lemma call_packet_lengthA : forall v1 v2, fmt_call_okA FMT_PACKET_LENGTH FS_PACKET_LENGTH [AInt v1; AInt v2] [PA_i (s32 v1); PA_i (s32 v2)] (pieces_packet_length v1 v2).
Proof. intros v1 v2. change (fmt_call_okA FMT_PACKET_LENGTH FS_PACKET_LENGTH [AInt v1; AInt v2] (to_pargs (fmt FS_PACKET_LENGTH) [AInt v1; AInt v2]) (fmt_pieces (fmt FS_PACKET_LENGTH) [AInt v1; AInt v2])). fmt_callA. Qed.
#[using="Type"] Lemma call_couldnt_openA : forall s, zlength s <= 2^24 -> fmt_call_okA FMT_COULDNT_OPEN FS_COULDNT_OPEN [AStr s] [PA_s s] (pieces_couldnt_open s).
Proof. intros s Hs. change (fmt_call_okA FMT_COULDNT_OPEN FS_COULDNT_OPEN [AStr s] (to_pargs (fmt FS_COULDNT_OPEN) [AStr s]) (fmt_pieces (fmt FS_COULDNT_OPEN) [AStr s])). fmt_callA. Qed.
End WithRc2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GluePf.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).

  Lemma implMG_rd_lc : forall {B} RNG (k : libc_st hptr -> M PS B) (s : PS) Q ms,
    implMG RNG (k (ps_libc s)) s Q ms -> implMG RNG (mbind (rd_lc ps_libc) k) s Q ms.
  Proof using Type. pin_using tt. intros B RNG k s Q ms IM. exact IM. Qed.

  (* [comment removed for export] *)
  Lemma in_block_FB_range : forall L RNG (s : PS) CL FB FL m a, GIOA L RNG s CL FB FL m -> in_block FB a -> 0x604000 <= a < ATOP.
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros L RNG s CL FB FL m a G HB. unfold in_block in HB. apply Exists_exists in HB. sbl_pose_in HB. destruct HB as (b & HIN & Hb). sbl_subst_all.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; right; exact HIN)) as ((ABLK & _) & _).
    unfold ablk, AIMG_HI, KLS in ABLK. pose proof (@ATOP_lo rc). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition GIOA_stdout_step__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' (f' : file_st) lo SP,
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo <= SP ->
    munch [(lo, SP); (A_STDOUT, A_STDOUT + 232); (A_STDOUT_BUF, A_STDOUT_BUF + 1024)] m m' -> wmono asegs m m' ->
    FILE_R m' f' A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 -> stdout_inv f' ->
    GIOA L RNG (set_libc (set_stdout f' (ps_libc s)) s) CL FB FL m' /\ agrees_on (client_keeps FL CL SP) m m'.
  Section Sz13.
  Variables L RNG s CL FB FL m m' f' lo SP : ltac2:(SecDiet.SzSec.tyM 'GIOA_stdout_step__stmt "vvvvvvvvvvv" @L).
  Lemma GIOA_stdout_step__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_stdout_step__stmt "vvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G LOA LOSP MU WM FR' INV'.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (@ATOP_lo rc) as ATL.
    unfold A_STDOUT, A_STDOUT_BUF in MU.
    assert (HW : Forall (stdio_ivA FB SP) [(lo, SP); (696432, 696432 + 232); (6300880, 6300880 + 1024)]).
    { unfold stdio_ivA. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd];
        [left; lia | right; right; left; lia | right; right; right; left; lia]. }
    rewrite <- (app_nil_r [(lo, SP); (696432, 696432 + 232); (6300880, 6300880 + 1024)]) in MU.
    split.
    2:{ eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| exact HW| lia]|].
        intros a Ha. split; [exact Ha | exact I]. }
    eapply (gs_step _ GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| exact HW| apply Forall_nil| lia| |].
    { eapply (errno_cell_kept FO GIOA fflagA GL GSL L RNG s CL FB FL m m' _ [] SP); [exact G| exact MU| exact WM| | apply Forall_nil].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd];
        [left; lia | right; right; left; lia | right; right; right; lia]. }
    rewrite app_nil_r in MU.
    unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_stdout].
    assert (AG : agrees_on (fun a => outside [(lo, SP); (696432, 696432 + 232); (6300880, 6300880 + 1024)] a) m m').
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. exact Hs. }
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SEI as (_ & _ & SEbs & _).
    split; [exact FR'|]. split; [exact INV'|].
    split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; cbn [outside]; lia | rewrite SEbs; intros a Ha; cbn [outside]; lia]. }
    split; [exact SEI|].
    split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; cbn [outside]; lia. }
    split; [eapply agrees_rw_cells; [exact AG | exact U1 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact U2 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact U3 | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact OL | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [eapply agrees_rw_cells; [exact AG | exact OH | intros a Ha; cbn in Ha; cbn [outside]; lia]|].
    split; [| exact ND].
    eapply files_R_agree; [exact FS | exact AG |]. intros a Ha. pose proof (in_block_FB_range _ _ _ _ _ _ _ _ G Ha) as R. cbn [outside]. lia.
  Qed.
  End Sz13.
  Lemma GIOA_stdout_step : ltac:(let t := eval cbv delta [GIOA_stdout_step__stmt] in GIOA_stdout_step__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' f' lo SP. ltac2:(SecDiet.SzSec.closeP 'GIOA_stdout_step__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition printf_d_genA__stmt : Prop := forall FMT (mk : Z -> list (list Z)) fs,
    (forall v, fmt_call_okA FMT fs [AInt v] [PA_i (s32 v)] (mk v)) -> printf_d_stmt_o GIOA FMT mk.
  Section Sz14.
  Variables FMT mk fs ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo v : ltac2:(SecDiet.SzSec.tyM 'printf_d_genA__stmt "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @FMT).
  Lemma printf_d_genA__body : ltac2:(SecDiet.SzSec.bodyP 'printf_d_genA__stmt "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros CALL.
 intros SPO -> -> HV.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK in *.
    sbl_pose_in SO. destruct SO as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    pose proof SOI as (CH1 & FD1 & BS1 & NRD1 & NWR1 & EOF1 & RB1 & LBF1).
    pose proof (CALL v) as (HF & P1 & PIECES & SMALL & HA & BYf & IOK & GLB).
    pose proof (s32_facts v) as [S32a S32b].
    rewrite BS1 in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    destruct (pitems_facts fs [AInt v] [Z_to_bv 64 v] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (PW : pwords_ok RNG lo sp m (pitems fs [AInt v] [Z_to_bv 64 v]) [Z_to_bv 64 v; a2; a3; a4; a5; a6; a7]).
    { apply (pwords_ok_more RNG lo sp m _ [Z_to_bv 64 v] [a2; a3; a4; a5; a6; a7]).
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact I | apply Forall2_nil]]. }
    pose proof (gia_global_mobjA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G GLB RIMG RIMGSH) as MOF.
    destruct (gs_statics _ GSL _ _ _ _ _ _ _ G RIMG RIMGSH) as [SOS1 SOS2].
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    unfold s_printf, printf. apply implMG_rd_lc.
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold PRINTF_ENTRY.
      eapply (printf_i_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0 tail FMT lo
                (str fs ++ [0]) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 [PA_i (s32 v)] (mk v) _ canary (zb (str fs)) (pitems fs [AInt v] [Z_to_bv 64 v]) true true)
        with (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stdout (ps_libc s)))) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | reflexivity | exact FC | exact FLG | exact BUF | exact BP | exact WB0
             | exact BS1 | exact WBL | exact NWR1 | exact RB1
             | (rewrite CH1; left; exact FD1) | exact CH1 | (intros _; reflexivity)
             | (apply BYf; exact MI)
             | (cbn [args_ok]; split; [split; [exact S32a | exact S32b] | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact PW
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp) G); (keep_hyps rc lo v LOA sp LOB L SPT TOP47; lia))
             | (apply mobjA_sobj; [exact MOF | unfold zlength in *; (keep_hyps rc H hptr FMT fs s v HA; lia)])
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc v; lia) | (keep_hyps rc v; lia)])
             | (eapply sobj_sub; [exact SOS1 | unfold A_STDOUT; (keep_hyps rc lo v GLO sp LOA LOB; lia) | (keep_hyps rc sp L v SPT TOP47; lia) | unfold A_STDOUT; (keep_hyps rc v; lia)])
             | (eapply sobj_sub; [exact SOS2 | unfold A_STDOUT_BUF; (keep_hyps rc lo v GLO sp LOA LOB; lia) | (keep_hyps rc sp L v SPT TOP47; lia) | unfold A_STDOUT_BUF; (keep_hyps rc v; lia)])
             | (eapply rng_sub'; [exact RIMG | unfold A_STDOUT_BUF; (keep_hyps rc v; lia)])
             | (unfold PRINTF_I_DEPTH, GLOBALS_TOP in *; (keep_hyps rc sp lo v LOB GLO L SPT TOP47; lia))
             | idtac "PFD-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    sbl_pose_in PO. destruct PO as (-> & INV' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & flags' & mode' & bufbytes' & m' & rpos' & rend'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & RP' & FL' & BUF' & BP' & WBL'). sbl_subst_all.
    assert (BSnz : f_bufsize (lc_stdout (ps_libc s)) <> 0) by (rewrite BS1; unfold BUFSIZ; lia).
    pose proof (vfprintf_leaf_buffered _ _ _ _ _ BSnz LF) as [FX _].
    pose proof (vfprintf_leaf_buffered_wl _ _ _ _ _ BSnz LF) as WL.
    pose proof INV' as (WA' & RB' & BS' & NW' & FDC' & _ & CHN').
    rewrite RB1 in RP1. change (zlength (@nil Z)) with 0 in RP1.
    assert (FR' : FILE_R m' f' A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { exists flags', mode', rpos', tail, bufbytes'.
      rewrite WA', RB', BS'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      assert (Erend : rend' = rpos') by (rewrite RB1 in RP'; change (zlength (@nil Z)) with 0 in RP'; lia).
      rewrite Erend in FC'.
      split; [exact FC'|]. split; [exact FL'|]. split; [exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN]. }
    assert (SOI' : stdout_inv f').
    { pose proof FX as (E1 & E2 & E3 & E4 & E5 & E6 & _ & _ & SW' & LB').
      unfold stdout_inv. rewrite E1, E2, E4, E5, E6.
      split; [exact CH1|]. split; [exact FD1|]. split; [exact BS'|]. split; [exact NRD1|]. split; [exact NWR1|]. split; [exact EOF1|]. split; [exact RB'|].
      destruct WL as [[W1 W2]|[W1 W2]]; rewrite W1, ?W2; [exact LBF1| intros X; discriminate X]. }
    destruct (GIOA_stdout_step L RNG s CL FB FL m m' f' lo (bv_unsigned sp) G LOA ltac:(lia) MU WM FR' SOI') as [G' AG].
    unfold upd_lc. apply implMG_upd. apply evtF_done.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. exact G'.
  Qed.
  End Sz14.
  Lemma printf_d_genA : ltac:(let t := eval cbv delta [printf_d_genA__stmt] in printf_d_genA__stmt in exact t).
  Proof using GL GSL. intros FMT mk fs CALL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo v. ltac2:(SecDiet.SzSec.closeP 'printf_d_genA__body "vvvhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Theorem printf_failed_remove_proofA : printf_d_stmt_o GIOA FMT_FAILED_REMOVE pieces_failed_remove.
  Proof using GL GSL. exact (printf_d_genA _ _ _ call_failed_removeA). Qed.
  Theorem printf_failed_open_proofA : printf_d_stmt_o GIOA FMT_FAILED_OPEN pieces_failed_open.
  Proof using GL GSL. exact (printf_d_genA _ _ _ call_failed_openA). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vfprintf_nowr_unrA : forall RNG (fs0 : file_st) ps (s : PS) (Q : unit -> PS -> footprint -> machine_state -> Prop) ms h,
    heap_file_inv fs0 -> f_nowr fs0 = true ->
    implMG RNG (mbind (vfprintf fs0 ps) (store_file ps_libc set_libc eqb h)) s Q ms.
  Proof using Type. pin_using tt.
    intros RNG fs0 ps s Q ms h INV NOWR. pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct (NOWRi NOWR) as [WACT _].
    unfold vfprintf. rewrite BS. change (BUFSIZ =? 0) with false. cbv iota.
    unfold ensure_w. rewrite WACT. unfold towrite. rewrite NOWR.
    apply implMG_bind_assoc. cbn [mbind munr ebind bind]. apply implMG_unr.
  Qed.

  (* [comment removed for export] *)
  Definition hfile_after__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PS) (m : mem) (lo : Z) (canary : word) (ps : list (list Z)) (Af : Z) (fs0 : file_st) (pv nx : Z) (tail : list byte) (rp : Z)
      (f' : file_st) (st' : PS) (ms' : machine_state),
    heap_file_inv fs0 -> f_nowr fs0 = false -> 0 <= rp -> rp + zlength (f_rbuf fs0) < 2^63 -> firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
    vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail lo
                       canary true false rp (rp + zlength (f_rbuf fs0)) m s f' st' ms' ->
    mleaf (vfprintf fs0 ps) s f' st' ->
    st' = s /\
    exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (Af, Af + 232); (Af + FILE_BUF_OFF, Af + FILE_BUF_OFF + 1024)] m m' /\ wmono asegs m m'
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx /\ heap_file_inv f'.
  Section Sz18.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s m lo canary ps Af fs0 pv nx tail rp f' st' ms' : ltac2:(SecDiet.SzSec.tyM 'hfile_after__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma hfile_after__body : ltac2:(SecDiet.SzSec.bodyP 'hfile_after__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc.
 intros INV NOWR RP0 RP1 GLN PO LF.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    assert (RBN : f_rbuf fs0 = []) by (apply NORDi; rewrite NRW, NOWR; reflexivity).
    rewrite RBN in RP1. change (zlength (@nil Z)) with 0 in RP1.
    sbl_pose_in PO. destruct PO as (-> & INV' & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & flags' & mode' & bufbytes' & m' & rpos' & rend'
                     & -> & MU & WM & MI' & ST' & SSP' & FC' & RP' & FL' & BUF' & BP' & WBL'). sbl_subst_all.
    assert (BSnz : f_bufsize fs0 <> 0) by (rewrite BS; unfold BUFSIZ; lia).
    pose proof (vfprintf_leaf_buffered _ _ _ _ _ BSnz LF) as [FX _].
    pose proof INV' as (WA' & RB' & BS' & NW' & FDC' & _ & CHN').
    split; [reflexivity|].
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split; [| exact (heap_file_inv_fx fs0 f' INV NOWR FX)].
    exists flags', mode', rpos', tail, bufbytes'.
    rewrite WA', RB', BS'. change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
    assert (Erend : rend' = rpos') by (rewrite RBN in RP'; change (zlength (@nil Z)) with 0 in RP'; lia).
    rewrite Erend in FC'.
    split; [exact FC'|]. split; [exact FL'|]. split; [exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [exact WBL'|].
    split; [intros X; exfalso; exact (X eq_refl)|]. split; [lia|]. split; [lia| exact GLN].
  Qed.
  End Sz18.
  Lemma hfile_after : ltac:(let t := eval cbv delta [hfile_after__stmt] in hfile_after__stmt in exact t).
  Proof using rc. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s m lo canary ps Af fs0 pv nx tail rp f' st' ms'. ltac2:(SecDiet.SzSec.closeP 'hfile_after__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fprintf_packet_length_proofA__stmt : Prop := fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Section Sz19.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo v1 v2 : ltac2:(SecDiet.SzSec.tyM 'fprintf_packet_length_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fprintf_packet_length_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_packet_length_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
 intros SPO HIN -> -> -> -> HV1 HV2.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs0 & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    unfold STDIO_STACK, FILE_BLOCK in *.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    unfold s_fprintf, Stdio.fprintf, with_file_.
    apply implMG_bind_assoc. eapply implMG_lookup_file; [exact LK|].
    destruct (f_nowr fs0) eqn:NOWR; [apply vfprintf_nowr_unrA; [exact INV| exact NOWR]|].
    assert (RBN : f_rbuf fs0 = []) by (apply NORDi; rewrite NRW; reflexivity).
    sbl_pose_in FR. destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    rewrite BS in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    pose proof (call_packet_lengthA v1 v2) as (HF & P1 & PIECES & SMALL & HA & BYf & IOK & GLB).
    pose proof (s32_facts_sx v1 HV1) as [S1a S1b]. pose proof (s32_facts_sx v2 HV2) as [S2a S2b].
    destruct (pitems_facts FS_PACKET_LENGTH [AInt v1; AInt v2] [sx32 (Z_to_bv 64 v1); sx32 (Z_to_bv 64 v2)] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (PW : pwords_ok RNG lo sp m (pitems FS_PACKET_LENGTH [AInt v1; AInt v2] [sx32 (Z_to_bv 64 v1); sx32 (Z_to_bv 64 v2)])
                   [sx32 (Z_to_bv 64 v1); sx32 (Z_to_bv 64 v2); a4; a5; a6; a7]).
    { apply (pwords_ok_more RNG lo sp m _ [sx32 (Z_to_bv 64 v1); sx32 (Z_to_bv 64 v2)] [a4; a5; a6; a7]).
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact I | apply Forall2_cons; [exact I | apply Forall2_nil]]]. }
    pose proof (gia_global_mobjA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G GLB RIMG RIMGSH) as MOF.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    assert (SOFp : sobj RNG m Af (Af + 232)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (SOB : sobj RNG m (Af + 240) (Af + 240 + 1024)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (RGFp : rng RNG Af 232) by (eapply rng_sub'; [exact RGF | lia]).
    assert (RGB : rng RNG (Af + 240) 1024) by (eapply rng_sub'; [exact RGF | lia]).
    assert (IESF : iesafe [(Af, Af + 232)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (IESB : iesafe [(Af + 240, Af + 240 + 1024)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold FPRINTF_ENTRY.
      eapply (fprintf_i_file_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail
                FMT_PACKET_LENGTH lo (str FS_PACKET_LENGTH ++ [0]) (sx32 (Z_to_bv 64 v1)) (sx32 (Z_to_bv 64 v2)) a4 a5 a6 a7 [PA_i (s32 v1); PA_i (s32 v2)]
                (pieces_packet_length v1 v2) _ canary (zb (str FS_PACKET_LENGTH)) (pitems FS_PACKET_LENGTH [AInt v1; AInt v2] [sx32 (Z_to_bv 64 v1); sx32 (Z_to_bv 64 v2)]) true false)
        with (rpos := rp) (rend := rp + zlength (f_rbuf fs0)) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: unfold FILE_BUF_OFF.
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | exact IESF | exact IESB | exact RGFp | exact RGB
             | reflexivity | exact FC | exact FLG | exact BUF | exact BP | exact WB0
             | exact BS | exact WBL | exact NOWR | exact RBN
             | (rewrite NCH; exact FD) | exact NCH | (intros _; reflexivity)
             | (apply BYf; exact MI)
             | (cbn [args_ok]; split; [split; [exact S1a | exact S1b] |]; split; [split; [exact S2a | exact S2b] | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact PW | exact SOFp | exact SOB
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp) G); (keep_hyps rc lo v1 v2 LOA sp LOB L SPT TOP47; lia))
             | (apply mobjA_sobj; [exact MOF | unfold zlength in *; (keep_hyps rc v1 v2 fs0 HA; lia)])
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc v1 v2; lia) | (keep_hyps rc v1 v2; lia)])
             | (right; unfold GLOBALS_TOP; (keep_hyps rc Af lo v1 v2 FALO FA3; lia))
             | (unfold FPRINTF_I_DEPTH, GLOBALS_TOP in *; (keep_hyps rc sp lo v1 v2 LOB GLO L SPT TOP47; lia))
             | idtac "FPL-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    destruct (hfile_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s m lo canary _ Af fs0 pv nx tail rp f' st' ms' INV NOWR RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FR' & INV').
    unfold FILE_BUF_OFF in MU.
    rewrite <- (app_nil_r [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]) in MU.
    destruct (GIOA_file_step HO FO GIOA fflagA GL GSL EQB L RNG s CL FB FL m m' f Af f' pv nx [] lo (bv_unsigned sp) G HIN LOA ltac:(lia) MU WM ltac:(apply Forall_nil) UPD FR' INV') as [G' KP].
    unfold store_file, upd_lc. apply implMG_upd. apply evtF_done.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply agrees_on_weaken; [exact KP|]. intros a Ha. split; [exact Ha| exact I]. }
    exact G'.
  Qed.
  End Sz19.
  Theorem fprintf_packet_length_proofA : ltac:(let t := eval cbv delta [fprintf_packet_length_proofA__stmt] in fprintf_packet_length_proofA__stmt in exact t).
  Proof using EQB GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo v1 v2. ltac2:(SecDiet.SzSec.closeP 'fprintf_packet_length_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition str_arg_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m lo SP Fp FS B BS ap P (str slack : list byte),
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo <= ap -> ap + 8 <= SP ->
    bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
    (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
    cobjA RNG m FL CL P (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) -> Z.of_nat (length slack) <= 2^24 ->
    (P + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= Fp \/ Fp + FS <= P) ->
    (P + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= B \/ B + BS <= P) ->
    arg_ok Fp FS B BS RNG m lo SP ap (Z_to_bv 64 P) (PA_s (map bv_unsigned str))
    /\ (forall sp : word, bv_unsigned sp = SP -> pword_ok RNG lo sp m (AStr (map bv_unsigned str)) (Z_to_bv 64 P)).
  Section Sz20.
  Variables L RNG s CL FB FL m lo SP Fp FS B BS ap P str slack : ltac2:(SecDiet.SzSec.tyM 'str_arg_factsA__stmt "vvvvvvvvvvvvvvvvv" @L).
  Lemma str_arg_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'str_arg_factsA__stmt "vvvvvvvvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOA LAP APSP BY NZ LB PAD CR SLK DF DB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof (pad8_range (P + Z.of_nat (length str) + 1)) as PR. unfold pad8 in PR.
    set (pd := (- (P + Z.of_nat (length str) + 1)) mod 8) in *.
    destruct (cobjA_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ P _ lo G CR ltac:(lia) LOA) as (D0 & DLO & D3 & D47 & SOD & RGD & IESD & _).
    assert (EP : bv_unsigned (Z_to_bv 64 P : word) = P) by (apply unsigned_lit; lia).
    assert (SOS : sobj RNG m P (P + (Z.of_nat (length str) + 1))) by (eapply sobj_sub; [exact SOD | lia | lia | lia]).
    assert (NZF : Forall (fun b : byte => bv_unsigned b <> 0) str).
    { apply Forall_forall. intros b Hb E. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|].
      rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b), E. reflexivity. }
    split.
    - cbn [arg_ok]. rewrite EP. exists (firstn (Z.to_nat pd) slack).
      assert (LS : length (firstn (Z.to_nat pd) slack) = Z.to_nat pd) by (rewrite length_firstn; lia).
      unfold zlength. rewrite length_map, LS.
      split. { rewrite zb_unsigned. rewrite <- (firstn_skipn (Z.to_nat pd) slack) in BY.
               change (str ++ Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack ++ skipn (Z.to_nat pd) slack)
                 with (str ++ (Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack) ++ skipn (Z.to_nat pd) slack) in BY.
               rewrite app_assoc in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split. { apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
               pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
               pose proof (proj1 (Forall_forall _ _) NZF b Hb) as Nb. cbv beta in Nb. lia. }
      split; [lia|]. split; [lia|]. split; [left; lia|]. split; [lia|]. split; [lia|]. split; [left; lia|]. split; [lia|].
      split; [eapply rng_sub'; [exact RGD | lia]|].
      replace (P + Z.of_nat (length str) + 1) with (P + (Z.of_nat (length str) + 1)) by lia. exact SOS.
    - intros sp ESP. cbn [pword_ok]. rewrite EP, zb_unsigned. unfold pstrL.
      split. { change (str ++ Z_to_bv 8 0 :: slack) with (str ++ [Z_to_bv 8 0] ++ slack) in BY. rewrite app_assoc in BY.
               apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split; [exact NZF|]. split; [left; lia|]. split; [lia|]. split; [exact SOS|]. eapply rng_sub'; [exact RGD | lia].
  Qed.
  End Sz20.
  Lemma str_arg_factsA : ltac:(let t := eval cbv delta [str_arg_factsA__stmt] in str_arg_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m lo SP Fp FS B BS ap P str slack. ltac2:(SecDiet.SzSec.closeP 'str_arg_factsA__body "vvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fprintf_s_stmt_oS (FMT : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af lo P : Z) (str slack : list byte),
      std_pre_o GIOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
      cobjA RNG m FL CL P (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) -> Z.of_nat (length slack) <= 2^24 ->
      implMG RNG (s_fprintf HO f (mk (map bv_unsigned str))) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIOA L RNG' s' CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fprintf_couldnt_open_proofA__stmt : Prop := fprintf_s_stmt_o HO GIOA FMT_COULDNT_OPEN pieces_couldnt_open.
  Section Sz21.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo P str slack : ltac2:(SecDiet.SzSec.tyM 'fprintf_couldnt_open_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fprintf_couldnt_open_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fprintf_couldnt_open_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
 intros SPO HIN -> -> -> BY NZ LEN PAD CR SLK.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs0 & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    pose proof (cobjA_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ P _ lo G CR ltac:(lia) LOA) as (_ & _ & _ & _ & _ & _ & _ & DAP).
    pose proof (DAP _ _ HIN) as DAPf.
    unfold STDIO_STACK, FILE_BLOCK in *.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    unfold s_fprintf, Stdio.fprintf, with_file_.
    apply implMG_bind_assoc. eapply implMG_lookup_file; [exact LK|].
    destruct (f_nowr fs0) eqn:NOWR; [apply vfprintf_nowr_unrA; [exact INV| exact NOWR]|].
    assert (RBN : f_rbuf fs0 = []) by (apply NORDi; rewrite NRW; reflexivity).
    sbl_pose_in FR. destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP0 & RP1 & GLN). sbl_subst_all.
    rewrite BS in FC, BUF, WBL. unfold BUFSIZ in FC, BUF, WBL.
    assert (EL : zlength (map bv_unsigned str) = Z.of_nat (length str)) by (unfold zlength; rewrite length_map; reflexivity).
    pose proof (call_couldnt_openA (map bv_unsigned str) ltac:(rewrite EL; lia)) as (HF & P1 & PIECES & SMALL & HA & BYf & IOK & GLB).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    destruct (str_arg_factsA L RNG s CL FB FL m lo (bv_unsigned sp) Af 232 (Af + 240) 1024 (bv_unsigned sp - 480) P str slack
                G LOA ltac:(lia) ltac:(lia) BY NZ LEN PAD CR SLK ltac:(lia) ltac:(lia)) as [AOK1 PWD1].
    destruct (pitems_facts FS_COULDNT_OPEN [AStr (map bv_unsigned str)] [Z_to_bv 64 P] IOK eq_refl) as (FSTR & NOZ & EF & OKI).
    assert (PW : pwords_ok RNG lo sp m (pitems FS_COULDNT_OPEN [AStr (map bv_unsigned str)] [Z_to_bv 64 P]) [Z_to_bv 64 P; a3; a4; a5; a6; a7]).
    { apply (pwords_ok_more RNG lo sp m _ [Z_to_bv 64 P] [a3; a4; a5; a6; a7]).
      apply pitems_words_fs; [exact IOK | apply Forall2_cons; [exact (PWD1 sp eq_refl) | apply Forall2_nil]]. }
    pose proof (gia_global_mobjA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G GLB RIMG RIMGSH) as MOF.
    assert (SOFp : sobj RNG m Af (Af + 232)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (SOB : sobj RNG m (Af + 240) (Af + 240 + 1024)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (RGFp : rng RNG Af 232) by (eapply rng_sub'; [exact RGF | lia]).
    assert (RGB : rng RNG (Af + 240) 1024) by (eapply rng_sub'; [exact RGF | lia]).
    assert (IESF : iesafe [(Af, Af + 232)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (IESB : iesafe [(Af + 240, Af + 240 + 1024)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    eapply implMG_bind.
    { eapply implMG_leaf. apply implAM_implMG. unfold FPRINTF_ENTRY.
      eapply (fprintf_i_file_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx tail
                FMT_COULDNT_OPEN lo (Fmt.str FS_COULDNT_OPEN ++ [0]) (Z_to_bv 64 P) a3 a4 a5 a6 a7 [PA_s (map bv_unsigned str)]
                (pieces_couldnt_open (map bv_unsigned str)) _ canary (zb (Fmt.str FS_COULDNT_OPEN)) (pitems FS_COULDNT_OPEN [AStr (map bv_unsigned str)] [Z_to_bv 64 P]) true false)
        with (rpos := rp) (rend := rp + zlength (f_rbuf fs0)) (flags := flags) (mode := mode) (bufbytes := bufbytes).
      all: unfold FILE_BUF_OFF.
      all: match goal with |- ?g => first
             [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RSTK | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OKI
             | exact IESF | exact IESB | exact RGFp | exact RGB
             | reflexivity | exact FC | exact FLG | exact BUF | exact BP | exact WB0
             | exact BS | exact WBL | exact NOWR | exact RBN
             | (rewrite NCH; exact FD) | exact NCH | (intros _; reflexivity)
             | (apply BYf; exact MI)
             | (cbn [args_ok]; split; [exact AOK1 | exact I])
             | exact ST | exact SSP | exact MI | exact ENV | exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G) | exact PW | exact SOFp | exact SOB
             | (apply (gs_stack _ GSL _ _ _ _ _ _ _ lo (bv_unsigned sp) G); (keep_hyps rc lo P str slack LOA sp LOB L SPT TOP47; lia))
             | (apply mobjA_sobj; [exact MOF | unfold zlength in *; (keep_hyps rc P str slack fs0 HA; lia)])
             | (apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; (keep_hyps rc P str slack; lia) | (keep_hyps rc P str slack; lia)])
             | (right; unfold GLOBALS_TOP; (keep_hyps rc Af lo P str slack FALO FA3; lia))
             | (unfold FPRINTF_I_DEPTH, GLOBALS_TOP in *; (keep_hyps rc sp lo P str slack LOB GLO L SPT TOP47; lia))
             | idtac "FCO-LEFT:" g ] end. }
    cbv beta. intros f' st' RNG' ms' [(-> & PO) LF].
    destruct (hfile_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s m lo canary _ Af fs0 pv nx tail rp f' st' ms' INV NOWR RP0 RP1 GLN PO LF)
      as (-> & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FR' & INV').
    unfold FILE_BUF_OFF in MU.
    rewrite <- (app_nil_r [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]) in MU.
    destruct (GIOA_file_step HO FO GIOA fflagA GL GSL EQB L RNG s CL FB FL m m' f Af f' pv nx [] lo (bv_unsigned sp) G HIN LOA ltac:(lia) MU WM ltac:(apply Forall_nil) UPD FR' INV') as [G' KP].
    unfold store_file, upd_lc. apply implMG_upd. apply evtF_done.
    split; [apply fp_le_refl|].
    exists a0', m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s; reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply agrees_on_weaken; [exact KP|]. intros a Ha. split; [exact Ha| exact I]. }
    exact G'.
  Qed.
  End Sz21.
  Theorem fprintf_couldnt_open_proofA : ltac:(let t := eval cbv delta [fprintf_couldnt_open_proofA__stmt] in fprintf_couldnt_open_proofA__stmt in exact t).
  Proof using EQB GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo P str slack. ltac2:(SecDiet.SzSec.closeP 'fprintf_couldnt_open_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GluePf.
End TwB.
