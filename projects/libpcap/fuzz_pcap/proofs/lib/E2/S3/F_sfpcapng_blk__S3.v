(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_main_A__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_chkD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcapng_ai__U3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chk__U3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfpcapng_blk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_rb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
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
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Definition FMT_BLK_LT : Z := 0x105fa.      (* [comment removed for export] *)
Definition FMT_BLK_MULT4 : Z := 0x10af8.   (* [comment removed for export] *)
Definition FMT_BLK_GTMAX : Z := 0x10666.   (* [comment removed for export] *)
Definition FMT_BLK_TRAILER : Z := 0x10a58. (* [comment removed for export] *)
Definition STR_OOM : Z := 0x10df2.         (* [comment removed for export] *)

Section Blk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.

  (* [comment removed for export] *)
  Definition rb_body (f : hptr) (bt tl : Z) (p0 : pcapT) : M PS block_result :=
    let p1 := set_bufdata (le_bytes 4 bt ++ le_bytes 4 tl) p0 in
    mo_bind MOps (read_bytes MOps (prims HO fo_nop sites) f (DHeap (pc_buffer p1) 8) (tl - 8) true) (fun x => let '(st, data) := x in
    let p2 := set_bufdata (pc_bufdata p1 ++ data) p1 in
    match st with
    | RBS_Err m => mo_ret MOps (RB_Err m p2)
    | RBS_Eof => mo_ret MOps (RB_Err [] p2)
    | RBS_Ok =>
      let toff := tl - 4 in
      let p3 := if pc_swapped p2 then set_bufdata (swap_field 4 toff (pc_bufdata p2)) p2 else p2 in
      let trailer_length := get_le32 (pc_bufdata p3) toff in
      if negb (tl =? trailer_length)
      then mo_ret MOps (RB_Err (Msg.header_trailer_mismatch tl trailer_length) p3)
      else mo_ret MOps (RB_Ok (mkCursor 8 (tl - 12) bt) p3)
    end).

  Definition rb_tail (f : hptr) (bt tl : Z) (p : pcapT) : M PS block_result :=
    if tl <? 12 then mo_ret MOps (RB_Err (Msg.block_length_lt tl) p)
    else if negb (tl mod 4 =? 0) then mo_ret MOps (RB_Err (Msg.block_length_not_mult4 tl) p)
    else
    mo_bind MOps
      (if pc_bufsize p <? tl then
         if ng_max_blocksize (ng_of p) <? tl
         then mo_ret MOps (Some (Msg.block_size_gt_max tl (ng_max_blocksize (ng_of p))), p)
         else
           mo_bind MOps (e_realloc (prims HO fo_nop sites) (pc_buffer p) tl) (fun r =>
           match r with
           | None => mo_ret MOps (Some Msg.out_of_memory, p)
           | Some b => mo_ret MOps (@None (list Z), set_buffer b (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p)
           end)
       else mo_ret MOps (@None (list Z), p))
      (fun x => let '(gerr, p0) := x in
       match gerr with
       | Some m => mo_ret MOps (RB_Err m p0)
       | None => rb_body f bt tl p0
       end).

  Lemma read_block_eq : forall a_bhdr (p : pcapT),
    read_block MOps (prims HO fo_nop sites) a_bhdr p =
    mo_bind MOps (read_bytes MOps (prims HO fo_nop sites) (pc_rfile p) a_bhdr 8 false) (fun x => let '(st, bh) := x in
      match st with
      | RBS_Eof => mo_ret MOps (RB_Eof p)
      | RBS_Err m => mo_ret MOps (RB_Err m p)
      | RBS_Ok => rb_tail (pc_rfile p)
                    (if pc_swapped p then bswap32 (get_le32 bh 0) else get_le32 bh 0)
                    (if pc_swapped p then bswap32 (get_le32 bh 4) else get_le32 bh 4) p
      end).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Open Scope bv_scope.

  Definition read_block_proof__stmt : Prop := read_block_stmt HO K sites.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R st C1 C2 FB f Af P B CUR EB lo p s i a_bhdr bs ej ccs : ltac2:(SecDiet.SzSec.tyM 'read_block_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma read_block_proof__body : ltac2:(SecDiet.SzSec.bodyP 'read_block_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FERROR FMT FREAD HAL HFL HPL REALLOC SFL SNPRINTF. pin_using (fun (FERROR FMT FREAD HAL HFL HPL REALLOC SFL SNPRINTF : unit) => tt).
    intros PRE HinF RF HS HinP HBH -> -> -> -> HH HBUF PFX LENB HCUR Hccs CUR1 CUR2 CUR8 HEB EBR EB8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    destruct (rw_cells_forget _ _ _ _ HCUR) as [cj HCUR']. clear HCUR. rewrite Hccs in HCUR'. rename HCUR' into HCUR.
    destruct HH as (HBS & HPV & HMB & WBS & WMB & WBA & BSA).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold READ_BLOCK_STACK, PCAP_L1_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & _).
    cbn [cb_addr cb_size fst snd] in A1, A4. unfold FILE_BLOCK in A4.
    (* [comment removed for export] *)
    assert (HinP' : In (pc_self p, P, PCAP_NG_SF_TOTAL) ((C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) ++ FB)).
    { apply in_or_app. left. apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; right; exact X]. }
    assert (HinB' : In (pc_buffer p, B, pc_bufalloc p) ((C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) ++ FB)).
    { apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
    pose proof (GIo_block_ok K _ _ _ _ _ _ G HinP') as (P1 & P2 & P3 & P4 & _). cbn [cb_addr cb_size fst snd] in P1, P2, P3, P4. unfold PCAP_NG_SF_TOTAL in P4.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G HinB') as (B1 & B2 & B3 & B4 & _). cbn [cb_addr cb_size fst snd] in B1, B2, B3, B4.
    assert (APB : (P + 680 <= B \/ B + pc_bufalloc p <= P)%Z).
    { pose proof (mid_apart K _ _ _ _ _ _ _ _ G HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
    assert (CLB : forall a, in_block (C1 ++ C2) a -> (a < CEILZ)%Z).
    { intros a Ha. apply in_block_app in Ha. destruct (GIo_CLc_facts K R st (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) [] FB m a ltac:(rewrite app_nil_r; exact G)) as [Hc _]; [| lia].
      apply in_block_app. destruct Ha as [Ha|Ha]; [left; exact Ha| right; right; exact Ha]. }
    (* [comment removed for export] *)
    assert (EBX : ((bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ (EB = P + 216))%Z) by (destruct EBR as [X|X]; [left| right]; lia).
    clear EBR.
    assert (CRE : client_range R (C1 ++ C2) (bv_unsigned sp) EB 256).
    { destruct EBX as [X| ->]; [right; lia| left]. intros a Ha. apply in_block_In. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (EBiv : client_iv R (C1 ++ C2) (EB, (EB + 256)%Z)).
    { destruct EBX as [X| ->]; [left; cbn [fst snd]; unfold rc_lo; lia| right]. unfold iv_in_block. apply Exists_exists. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    (* [comment removed for export] *)
    rewrite (read_block_eq a_bhdr p). unfold read_bytes, errmsg_for_errno. rewrite RF. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims].
    unfold READ_BLOCK_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    hide HEB. hide HBUF. hide HCUR. hide HBS. hide HMB. unfold PCAP_PRIV_OFF in HPV.
    ienter. carve_frame 96%nat ST. do 23 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R st (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp - 96, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho])
    end.
    clear MU WM.
    assert (T0 : forall A cs, rw_cells ssegs m A cs -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp - 96 \/ bv_unsigned sp <= A)%Z -> rw_cells ssegs m0 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AG0 | exact HC | intros a Ha; cbn [outside]; lia]. }
    unhide HEB. unhide HBUF. unhide HCUR. unhide HBS. unhide HMB.
    apply T0 in HEB; [|cbn [cells_size csize Nat.add]; destruct EBX as [X| ->]; lia].
    apply T0 in HBUF; [|cbn [cells_size csize Nat.add]; lia].
    apply T0 in HCUR; [|cbn [cells_size csize Nat.add]; lia]. apply T0 in HBS; [|cbn [cells_size csize Nat.add]; lia].
    apply T0 in HMB; [|cbn [cells_size csize Nat.add]; lia].
    assert (AGa : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m0).
    { eapply agrees_on_weaken; [exact AG0|]. intros a [[Ha|Ha] _]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]. }
    clear AG0 T0.
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 1 FR) as [HDR FRS]. clear FR. cbn [firstn skipn cells_size csize Nat.add] in HDR, FRS.
    replace (bv_unsigned sp + -96 + Z.of_nat 8)%Z with (bv_unsigned sp + -88)%Z in FRS by lia.
    (* [comment removed for export] *)
    apply evt_done. apply (implM_bind_assoc ssegs). apply (implM_bind_assoc ssegs).
    name_sp sp (-96)%Z.
    apply implM_mget. rewrite (HBH st). replace (bv_unsigned sp - 96)%Z with (bv_unsigned sp + -96)%Z by lia.
    eapply (implM_bind ssegs).
    { eapply FREAD; [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | exact Esp | reflexivity | reflexivity | reflexivity | lia | exact HDR | right; rewrite Hsp; lia ]. }
    intros got s' ms' PO. cbv beta in PO.
    destruct PO as (av & m2 & junk' & E & OF1 & MI1 & ST1 & AG1 & G1 & -> & GL & GR & HD2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 93308)) with (Z_to_bv 64 93308) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INP : forall a, (P <= a < P + 680)%Z -> in_block (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) a).
    { intros a Ha. assert (X : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2)).
      { apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; right; exact X]. }
      apply in_block_In. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact X|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B <= a < B + pc_bufalloc p)%Z -> in_block (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) a).
    { intros a Ha. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (INPc : forall a, (P <= a < P + 680)%Z -> in_block (C1 ++ C2) a).
    { intros a Ha. apply in_block_In. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    (* [comment removed for export] *)
    transport FRS m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport HCUR m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport HBS m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; apply INP; lia| lia]).
    transport HPV m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; apply INP; lia| lia]).
    transport HMB m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; apply INP; lia| lia]).
    transport HBUF m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; apply INB; lia| lia]).
    transport HEB m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [destruct EBX as [X| ->]; [left; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs a X Ha; lia)| right; apply INP; (keep_hyps CEILV hptr sp R P B CUR p ccs a Ha; lia)]| destruct EBX as [X| ->]; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs a X Ha H K C1 C2 FB s' m2 LO BU P4 G1; lia)]).
    assert (AG02 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] _]; [split; [left; lia| lia]|].
      pose proof (CLB a Ha). split; [right; apply in_block_app in Ha as [X|X]; apply in_block_app; [left; exact X| right; right; exact X]| lia]. }
    clear AGa AG1 G0.
    unfold zlength in *.
    (* [comment removed for export] *)
    assert (EXIT : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : word)
                          (m3 : mem) (ps3 : PS) (r : block_result) (rv : Z) (hdr : list cell),
      ps_outfile ps3 = ps_outfile st -> mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells ssegs m3 (bv_unsigned sp + -96) hdr -> cells_size hdr = 8%nat ->
      rw_cells ssegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      (exists (p' : pcapT) B' bs',
        GIo K R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB m3
        /\ blk_handle p' s P B' m3
        /\ rw_cells ssegs m3 B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
        /\ (Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p')%Z
        /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p /\ same_meta p' p
        /\ match r with
           | RB_Ok c p'' => p'' = p' /\ rv = 1%Z /\ rw_cells ssegs m3 EB [CB 256 ej]
               /\ (exists cpad, rw_cells ssegs m3 CUR [C8 (Z_to_bv 64 (B' + 8)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad])
               /\ cur_off c = 8%Z /\ (0 <= cur_remaining c)%Z /\ (cur_remaining c + 12 <= pc_bufalloc p')%Z /\ (cur_remaining c + 12 <= 2^30)%Z /\ (0 <= cur_block_type c < 2^32)%Z
               /\ Z.of_nat (length (pc_bufdata p')) = (cur_remaining c + 12)%Z /\ Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p')
           | RB_Eof p'' => p'' = p' /\ rv = 0%Z /\ rw_cells ssegs m3 EB [CB 256 ej]
               /\ (exists ccs', rw_cells ssegs m3 CUR ccs' /\ cells_size ccs' = 24%nat)
           | RB_Err msg p'' => p'' = p' /\ rv = (-1)%Z
               /\ (exists junk'', rw_cells ssegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
               /\ (Z.of_nat (length msg) < 256)%Z /\ Forall (fun z => 0 < z < 256)%Z msg
               /\ (exists ccs', rw_cells ssegs m3 CUR ccs' /\ cells_size ccs' = 24%nat)
           end) ->
      evt ssegs (POSTQ r ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' y0 y1 (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7'
                 y2 y3 y4 y5 y6 y7 y8 y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16d90) fc None m3 (seg_rom ssegs))).
    { intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 m3 ps3 r rv hdr OF3 MI3 ST3 AG3 HDR3 Hhdr FRS3 REST.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      destruct (rw_cells_forget _ _ _ _ HDR3) as [hj HDR3']. clear HDR3. rewrite Hhdr in HDR3'.
      pose proof (rw_cells_uncut _ _ _ _ _ HDR3' FRS3 ltac:(cbn; lia)) as FR3. clear HDR3' FRS3. cbn [app] in FR3.
      do 13 step.
      release_frame FR3 ST3 (bv_unsigned sp).
      apply evt_done. subst POSTQ. unfold read_block_post.
      destruct REST as (p' & B' & bs' & G3 & BH3 & BUF3 & PFX3 & LEN3 & E1 & E2 & E3 & E4 & E5 & E6 & RM).
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 rv), mm, p', B', bs' end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [exact OF3|]. split; [assumption|]. split; [assumption|]. split; [exact AG3|]. split; [exact G3|]. split; [exact BH3|]. split; [exact BUF3|]. split; [exact PFX3|].
      split; [exact LEN3|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|].
      destruct r as [p''|msg p''|c p''].
      - destruct RM as (X1 & -> & X3 & X4). split; [exact X1|]. split; [reflexivity|]. split; [exact X3| exact X4].
      - destruct RM as (X1 & -> & X3 & X4 & X4b & X5). split; [exact X1|]. split; [reflexivity|]. split; [exact X3|]. split; [exact X4|]. split; [exact X4b| exact X5].
      - destruct RM as (X1 & -> & X3 & X4 & X5 & X6 & X7 & X7b & X8 & X9 & X10). split; [exact X1|]. split; [reflexivity|]. split; [exact X3|]. split; [exact X4|].
        split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact X7b|]. split; [exact X8|]. split; [exact X9| exact X10]. }
    (* [comment removed for export] *)
    assert (RESTp : forall mX psX, GIo K R psX (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB mX ->
              rw_cells ssegs mX (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B)] ->
              rw_cells ssegs mX (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
              rw_cells ssegs mX (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
              rw_cells ssegs mX B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
              GIo K R psX ((pc_buffer p, B, pc_bufalloc p) :: C1 ++ C2) FB mX /\ blk_handle p s P B mX
              /\ rw_cells ssegs mX B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p)
              /\ (Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p)%Z
              /\ pc_priv p = pc_priv p /\ pc_rfile p = pc_rfile p /\ pc_self p = pc_self p /\ pc_bufsize p = pc_bufsize p /\ pc_swapped p = pc_swapped p).
    { intros mX psX GX X1 X2 X3 X4. split; [eapply (GIo_perm K HPL); [exact GX| apply Permutation_sym; apply Permutation_middle]|].
      split; [split; [exact X1|]; split; [exact X2|]; split; [exact X3|]; split; [exact WBS|]; split; [exact WMB|]; split; [exact WBA| exact BSA]|].
      split; [exact X4|]. split; [exact PFX|]. split; [exact LENB|]. repeat split; reflexivity. }
    (* [comment removed for export] *)
    assert (SNP : forall (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 a3v a4v : word) (RA : Z)
                         (m3 : mem) (ps3 : PS) (fs : string) (args : list farg) (FMTA : Z) (msg : list Z) (p' : pcapT) (hdr : list cell),
      (RA = 0x16d8c \/ RA = 0x16d68)%Z -> ps_outfile ps3 = ps_outfile st ->
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells ssegs m3 (bv_unsigned sp + -96) hdr -> cells_size hdr = 8%nat ->
      rw_cells ssegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m3 EB [CB 256 ej] ->
      fmt_at m3 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      (forall (CL : list cblk) D dn, Forall2 (farg_word R CL (bv_unsigned sp + -96) D dn m3) args (firstn (length args) [a3v; a4v; a5'])) ->
      Fmt.snprintf 256 fs args = msg -> items_okb (fmt fs) = true -> Forall arg_ok args ->
      (exists B' bs', GIo K R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB m3 /\ blk_handle p' s P B' m3
         /\ rw_cells ssegs m3 B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
         /\ (Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p')%Z
         /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p /\ same_meta p' p
         /\ (exists ccs', rw_cells ssegs m3 CUR ccs' /\ cells_size ccs' = 24%nat)) ->
      evt ssegs (POSTQ (RB_Err msg p') ps3)
        (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 EB) y1 (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3v a4v a5' a6' a7'
                 y2 y3 y4 y5 y6 y7 y8 y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m3 (seg_rom ssegs))).
    { intros t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 a3v a4v RA m3 ps3 fs args FMTA msg p' hdr
             HRA OF3 MI3 ST3 AG3 HDR3 Hhdr FRS3 HEB3 FAT FOK ALEN FW EMSG FIT AOK REST.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      destruct REST as (B' & bs' & G3 & BH3 & BUF3 & PFX3 & LEN3 & E1 & E2 & E3 & E4 & E5 & E6 & ccs' & HCUR3 & Hccs').
      pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
      assert (APB' : (P + 680 <= B' \/ B' + pc_bufalloc p' <= P)%Z).
      { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
      name_sp sp (-96)%Z.
      eapply evt_cut.
      { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB lo EB 256%Z FMTA fs args ej);
          [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
          | reflexivity | reflexivity | reflexivity | lia | exact FAT | exact FOK | exact ALEN | rewrite Hsp; apply FW | exact HEB3
          | destruct CRE as [Hb|Hs]; [left; intros a Ha; unfold in_block; apply Exists_cons_tl; exact (Hb a Ha) | right; rewrite Hsp; lia] ]. }
      cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -96 - STDIO_STACK, bv_unsigned sp + -96); (EB, EB + 256)]%Z a) m3 m4)
        by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
      unfold STDIO_STACK in AGS.
      assert (G4 : GIo K R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB m4).
      { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |].
        apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, STDIO_STACK; lia|]. apply Forall_cons; [| apply Forall_nil].
        destruct EBiv as [X|X]; [left; exact X| right]. unfold iv_in_block. apply Exists_cons_tl. exact X. }
      transport HDR3 m4 AGS ltac:(prs). transport FRS3 m4 AGS ltac:((keep_hyps CEILV H hptr K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R C1 C2 FB P B CUR EB lo p ccs got ps3 args p' hdr B' ccs' m4 LO BU P4 EBX G4; prs)). transport HCUR3 m4 AGS ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 args p' hdr B' ccs' m4 LO BU CUR1 P4 EBX Hccs' G4; prs)). transport BUF3 m4 AGS ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 args p' hdr B' bs' ccs' m4 LO BU EBX Q4 APB' G4; prs)).
      destruct BH3 as (Y1 & Y2 & Y3 & YR).
      transport Y1 m4 AGS ltac:(prs). transport Y2 m4 AGS ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 args p' hdr B' ccs' m4 LO BU P4 EBX G4; prs)). transport Y3 m4 AGS ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s ccs got ps3 args p' hdr B' ccs' m4 LO BU P4 EBX G4; prs)).
      assert (AG4 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m4).
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] (_ & _ & Hn)]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
      hide HDR3. hide FRS3. hide HCUR3. hide BUF3. hide Y1. hide Y2. hide Y3. hide HEB4.
      destruct HRA as [-> | ->];
        [ replace (ret_pc (Z_to_bv 64 93580)) with (Z_to_bv 64 93580) by (symmetry; apply ret_pc_even; [lia|reflexivity]); step
        | replace (ret_pc (Z_to_bv 64 93544)) with (Z_to_bv 64 93544) by (symmetry; apply ret_pc_even; [lia|reflexivity]); do 2 step ].
      all: unhide HDR3; unhide FRS3; unhide HCUR3; unhide BUF3; unhide Y1; unhide Y2; unhide Y3; unhide HEB4.
      all: eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 ps3 (RB_Err msg p') (-1)%Z hdr);
        [exact OF3 | exact MI4 | exact ST4 | exact AG4 | exact HDR3 | exact Hhdr | exact FRS3 |].
      all: exists p', B', bs'; split; [exact G4|]; split; [exact (conj Y1 (conj Y2 (conj Y3 YR)))|]; split; [exact BUF3|]; split; [exact PFX3|]; split; [exact LEN3|].
      all: split; [exact E1|]; split; [exact E2|]; split; [exact E3|]; split; [exact E4|]; split; [exact E5|]; split; [exact E6|].
      all: cbv beta iota; split; [reflexivity|]; split; [reflexivity|].
      all: pose proof (snprintf_length 256 fs args) as LS; change (Z.to_nat (256 - 1)) with 255%nat in LS; rewrite EMSG in LS, HEB4.
      all: change (Z.to_nat 256) with 256%nat in HEB4.
      all: replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB4 by lia.
      all: split; [exists junk4; exact HEB4|]; split; [lia|]; split; [rewrite <- EMSG; apply snprintf_ok; [exact FIT| exact AOK]|]; exists ccs'; split; [exact HCUR3| exact Hccs']. }
    (* [comment removed for export] *)
    assert (KFMT : forall (ra' t0' t1' t2' a0' a1' a4' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 : word)
                          (m3 : mem) (ps3 : PS) (err : Z) (p' : pcapT) (hdr : list cell),
      ps_outfile ps3 = ps_outfile st -> mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells ssegs m3 (bv_unsigned sp + -96) hdr -> cells_size hdr = 8%nat ->
      rw_cells ssegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m3 EB [CB 256 ej] ->
      (-2^31 <= err < 2^31)%Z ->
      (exists B' bs', GIo K R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB m3 /\ blk_handle p' s P B' m3
         /\ rw_cells ssegs m3 B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
         /\ (Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p')%Z
         /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p /\ same_meta p' p
         /\ (exists ccs', rw_cells ssegs m3 CUR ccs' /\ cells_size ccs' = 24%nat)) ->
      evt ssegs (POSTQ (RB_Err (fmt_errmsg "error reading dump file" [] err) p') ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 EB) y1 a0' a1' (Z_to_bv 64 (s32 err)) (Z_to_bv 64 FMT_ERR_READING) a4' a5' a6' a7'
                 y2 y3 y4 y5 y6 y7 y8 y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16d2c) fc None m3 (seg_rom ssegs))).
    { intros ra' t0' t1' t2' a0' a1' a4' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 m3 ps3 err p' hdr
             OF3 MI3 ST3 AG3 HDR3 Hhdr FRS3 HEB3 ERR REST.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      destruct REST as (B' & bs' & G3 & BH3 & BUF3 & PFX3 & LEN3 & E1 & E2 & E3 & E4 & E5 & E6 & ccs' & HCUR3 & Hccs').
      pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
      assert (APB' : (P + 680 <= B' \/ B' + pc_bufalloc p' <= P)%Z).
      { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
      assert (INB' : forall a, (B' <= a < B' + pc_bufalloc p')%Z -> in_block ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) a).
      { intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (INP' : forall a, (P <= a < P + 680)%Z -> in_block ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) a).
      { intros a Ha. unfold in_block. apply Exists_cons_tl. apply Exists_exists. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
      assert (MSG : fmt_at m3 FMT_ERR_READING "error reading dump file"%string)
        by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_ERR_READING; lia| unfold FMT_ERR_READING; cbn; lia]).
      hide HDR3. hide FRS3. hide HCUR3. hide BUF3. hide BH3. hide HEB3.
      do 3 step. unhide HEB3.
      name_sp sp (-96)%Z.
      eapply evt_cut.
      { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB lo EB FMT_ERR_READING err "error reading dump file"%string [] ej);
          [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB3
           | destruct CRE as [Hb|Hs]; [left; intros a Ha; unfold in_block; apply Exists_cons_tl; exact (Hb a Ha) | right; rewrite Hsp; lia] | exact EB8 ].
        split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      cbv beta. intros ms' PO. destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m4 & junk4 & -> & MI4 & ST4 & AG4 & G4 & HEB4).
      rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 93496)) with (Z_to_bv 64 93496) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide HDR3. unhide FRS3. unhide HCUR3. unhide BUF3. unhide BH3.
      transport HDR3 m4 AG4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 p' hdr B' ccs' m4 LO BU P4 EBX Hhdr G4; prs)). transport FRS3 m4 AG4 ltac:((keep_hyps CEILV H hptr K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R C1 C2 FB P B CUR EB lo p ccs got ps3 p' hdr B' ccs' m4 LO BU P4 EBX G4; prs)). transport HCUR3 m4 AG4 ltac:(prs). transport BUF3 m4 AG4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 p' hdr B' bs' ccs' m4 LO BU EBX Q4 APB' INB' G4; prs)).
      destruct BH3 as (Y1 & Y2 & Y3 & YR).
      transport Y1 m4 AG4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 p' hdr B' ccs' m4 LO BU P4 EBX INP' G4; prs)). transport Y2 m4 AG4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 p' hdr B' ccs' m4 LO BU P4 EBX INP' G4; prs)). transport Y3 m4 AG4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s ccs got ps3 p' hdr B' ccs' m4 LO BU P4 EBX INP' G4; prs)).
      hide HDR3. hide FRS3. hide HCUR3. hide BUF3. hide Y1. hide Y2. hide Y3. hide HEB4.
      do 2 step.
      unhide HDR3. unhide FRS3. unhide HCUR3. unhide BUF3. unhide Y1. unhide Y2. unhide Y3. unhide HEB4.
      eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 ps3 (RB_Err _ p') (-1)%Z hdr);
        [exact OF3 | exact MI4 | exact ST4 | | exact HDR3 | exact Hhdr | exact FRS3 |].
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AG4|]. intros a [[Ha|Ha] (_ & _ & Hn)]; (split; [|exact Hn]); [left; lia| right].
        unfold in_block. apply Exists_cons_tl. exact Ha. }
      exists p', B', bs'. split; [exact G4|]. split; [exact (conj Y1 (conj Y2 (conj Y3 YR)))|]. split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LEN3|].
      split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|].
      cbv beta iota. split; [reflexivity|]. split; [reflexivity|].
      split; [exists junk4; exact HEB4|]. split; [pose proof (fmt_errmsg_length "error reading dump file"%string [] err); lia|].
      split; [apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor]|].
      exists ccs'. split; [exact HCUR3| exact Hccs']. }
    (* [comment removed for export] *)
    assert (KBODY : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y5 y6 y7 y9 : word)
                           (m3 : mem) (ps3 : PS) (p0 : pcapT) (B0 : Z) (bs0 : list byte) (bt tl : Z),
      ps_outfile ps3 = ps_outfile st -> (0 <= bt < 2^32)%Z -> (12 <= tl <= 2^30)%Z ->
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells ssegs m3 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
      rw_cells ssegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      GIo K R ps3 ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB m3 ->
      rw_cells ssegs m3 (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B0)] ->
      rw_cells ssegs m3 (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells ssegs m3 (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
      rw_cells ssegs m3 B0 [CB (Z.to_nat (pc_bufalloc p0)) bs0] ->
      firstn (length (pc_bufdata p0)) bs0 = map b8 (pc_bufdata p0) -> (Z.of_nat (length (pc_bufdata p0)) <= pc_bufalloc p0)%Z ->
      (tl <= pc_bufalloc p0)%Z -> (pc_bufalloc p0 < 2^32)%Z -> (pc_bufsize p0 <= pc_bufalloc p0)%Z ->
      pc_priv p0 = pc_priv p -> pc_rfile p0 = pc_rfile p -> pc_self p0 = pc_self p -> pc_bufsize p0 = pc_bufsize p -> pc_swapped p0 = pc_swapped p -> same_meta p0 p ->
      rw_cells ssegs m3 CUR [CB 24 cj] -> rw_cells ssegs m3 EB [CB 256 ej] ->
      implM ssegs (rb_body f bt tl p0) ps3 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 CUR) (Z_to_bv 64 B0) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 P) (Z_to_bv 64 Af) (Z_to_bv 64 tl) y5 y6 y7 (Z_to_bv 64 (s32 tl)) y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16e14) fc None m3 (seg_rom ssegs))).
    { intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y5 y6 y7 y9 m3 ps3 p0 B0 bs0 bt tl
             OF3 BT TL MI3 ST3 AG3 HDR3 FRS3 G3 HBS3 HPV3 HMB3 HBUF3 PFX0 LEN0 TLB BA0 BSA0 E1 E2 E3 E4 E5 E6 HCUR3 HEB3.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
      assert (APB0 : (P + 680 <= B0 \/ B0 + pc_bufalloc p0 <= P)%Z).
      { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
      assert (INB0 : forall a, (B0 <= a < B0 + pc_bufalloc p0)%Z -> in_block ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) a).
      { intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (INP0 : forall a, (P <= a < P + 680)%Z -> in_block ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) a).
      { intros a Ha. unfold in_block. apply Exists_cons_tl. apply Exists_exists. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
      assert (CLB0 : forall a, in_block (C1 ++ C2) a -> ~ (B0 <= a < B0 + pc_bufalloc p0)%Z).
      { intros a Ha Hr'. destruct (proj1 (in_block_In _ _) Ha) as (b' & Hin & Hr). pose proof (head_apart K _ _ _ _ _ _ _ G3 Hin) as AP. cbn [cb_addr cb_size fst snd] in AP, Hr. lia. }
      assert (LB0 : length bs0 = Z.to_nat (pc_bufalloc p0)) by (destruct HBUF3 as [[WF _] _]; cbn in WF; lia).
      (* [comment removed for export] *)
      pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [8%nat; (Z.to_nat (pc_bufalloc p0) - 8)%nat] HBUF3 ltac:(cbn; lia)) as HB'. clear HBUF3.
      cbn [mk_CB_cells app] in HB'.
      destruct (rw_cells_cut _ _ _ 1 HB') as [HB8 HBT]. clear HB'. cbn [firstn skipn cells_size csize Nat.add] in HB8, HBT.
      lazymatch type of HBT with rw_cells _ _ ?A _ => replace A with (B0 + 8)%Z in HBT by lia end.
      (* [comment removed for export] *)
      set (V := (bt + 4294967296 * tl)%Z).
      assert (HV : (0 <= V < 2^64)%Z) by (subst V; lia).
      assert (HDR8 : rw_cells ssegs m3 (bv_unsigned sp + -96) [C8 (Z_to_bv 64 V)]).
      { eapply rw_cells_recell; [exact HDR3 | cbn; repeat split; try exact Logic.I |].
        cbn [cells_bytes cbytes app]. subst V. rewrite le8_two by lia. rewrite !le4_le_bytes by lia. rewrite map_app, !app_nil_r. reflexivity. }
      clear HDR3.
      unfold rb_body, read_bytes, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims pc_buffer pc_bufdata pc_swapped set_bufdata].
      unfold implM. iprefix.
      hide FRS3. hide HBS3. hide HPV3. hide HMB3. hide HBT. hide HCUR3. hide HEB3.
      eapply evt_cut.
      { eapply (hdr_copy_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V B0);
          [exact MI3 | exact HV | lia | unfold rc_lo in *; lia | lia | reflexivity | exact HDR8 | exact HB8]. }
      cbv beta. intros ms' PO. destruct PO as (z1 & z2 & z3 & z4 & z5 & z6 & m4 & -> & MU4 & WM4 & MI4 & HB84 & HDR4). clear HB8 HDR8.
      assert (AGS4 : agrees_on (fun a => outside [(B0, B0 + 8)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
      unhide FRS3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HBT. unhide HCUR3. unhide HEB3.
      transport FRS3 m4 AGS4 ltac:(prs). transport HBS3 m4 AGS4 ltac:(prs). transport HPV3 m4 AGS4 ltac:(prs). transport HMB3 m4 AGS4 ltac:(prs).
      transport HBT m4 AGS4 ltac:(prs). transport HCUR3 m4 AGS4 ltac:(prs). transport HEB3 m4 AGS4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ej ccs got m3 ps3 p0 B0 bs0 bt tl LO BU EBX BT G3 TLB Q4 APB0 HV; prs)).
      assert (G4 : GIo K R ps3 ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB m4).
      { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (ST4 : stk ssegs m4 lo (bv_unsigned sp + -96)).
      { eapply stk_transport_disjoint; [exact ST3 | exact MU4 | exact WM4 | cbn [disjoint_from]; unfold rc_lo in *; lia]. }
      assert (AG4 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m4).
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS4|]. intros a [[Ha|Ha] _]; cbn [outside]; (split; [| exact Logic.I]); [lia|]. exact (CLB0 a Ha ltac:(fail)) || (pose proof (CLB0 a Ha); (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl a TL TLB H0; lia)). }
      clear AGS4 MI3 ST3 G3 AG3.
      subst V. rewrite le8_two in HB84 by lia.
      (* [comment removed for export] *)
      hide FRS3. hide HPV3. hide HMB3. hide HBT. hide HCUR3. hide HEB3. hide HB84. hide HDR4.
      do 8 step.
      unhide FRS3. unhide HPV3. unhide HMB3. unhide HBT. unhide HCUR3. unhide HEB3. unhide HB84. unhide HDR4.
      apply evt_done. apply (implM_bind_assoc ssegs). apply (implM_bind_assoc ssegs). apply implM_mget. cbn [eval_rdest fo_site fo_nop]. unfold blk_addr.
      rewrite (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G4 ltac:(apply in_or_app; left; left; reflexivity)).
      pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat (tl - 8); (Z.to_nat (pc_bufalloc p0) - 8 - Z.to_nat (tl - 8))%nat] HBT ltac:(cbn; lia)) as HB'. clear HBT.
      cbn [mk_CB_cells app] in HB'.
      destruct (rw_cells_cut _ _ _ 1 HB') as [HDST HREST]. clear HB'. cbn [firstn skipn cells_size csize Nat.add] in HDST, HREST.
      lazymatch type of HREST with rw_cells _ _ ?A _ => replace A with (B0 + tl)%Z in HREST by lia end.
      name_sp sp (-96)%Z.
      eapply (implM_bind ssegs).
      { eapply FREAD; [ split; [exact G4|]; split; [rewrite Hsp; exact ST4|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                        split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                      | exact HinF | reflexivity | reflexivity | f_equal; lia | reflexivity | lia | exact HDST | left; intros a Ha; apply INB0; lia ]. }
      intros got2 ps5 ms5 PO. cbv beta in PO.
      destruct PO as (av & m5 & junk5 & E & OF5 & MI5 & ST5 & AG5 & G5 & -> & GL2 & GR2 & HD5).
      unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 93812)) with (Z_to_bv 64 93812) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      transport FRS3 m5 AG5 ltac:(prs). transport HDR4 m5 AG5 ltac:(prs). transport HCUR3 m5 AG5 ltac:(prs). transport HBS3 m5 AG5 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 tl TLB APB0 INP0; prs)).
      transport HPV3 m5 AG5 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 tl TLB APB0 INP0; prs)). transport HMB3 m5 AG5 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p s ccs got p0 B0 bs0 tl TLB APB0 INP0; prs)). transport HEB3 m5 AG5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ej ccs got p0 B0 bs0 tl ps5 m5 LO BU EBX TLB Q4 APB0 INP0 G5; prs)). transport HB84 m5 AG5 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 bt tl TL TLB INB0; prs)).
      transport HREST m5 AG5 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 tl TL INB0; prs)).
      assert (AG5' : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m5).
      { eapply agrees_on_trans; [exact AG4|]. eapply agrees_on_weaken; [exact AG5|]. intros a [[Ha|Ha] _]; [split; [left; lia| lia]|].
        pose proof (CLB0 a Ha). split; [right; unfold in_block; apply Exists_cons_tl; exact Ha| lia]. }
      clear AG5 MU4 WM4 MI4 ST4 G4 AG4.
      unfold zlength in *.
      pose proof (rw_cells_bound _ _ _ _ HREST) as BREST. cbn [cells_size csize Nat.add] in BREST.
      (* [comment removed for export] *)
      assert (RESTd : forall (mX : mem) (psX : PS) (d : list Z) (bsX : list byte) (ccsX : list cell),
                GIo K R psX ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB mX ->
                rw_cells ssegs mX (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B0)] ->
                rw_cells ssegs mX (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
                rw_cells ssegs mX (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
                rw_cells ssegs mX B0 [CB (Z.to_nat (pc_bufalloc p0)) bsX] ->
                firstn (length d) bsX = map b8 d -> (Z.of_nat (length d) <= pc_bufalloc p0)%Z ->
                rw_cells ssegs mX CUR ccsX -> cells_size ccsX = 24%nat ->
                exists bs', GIo K R psX ((pc_buffer (set_bufdata d p0), B0, pc_bufalloc (set_bufdata d p0)) :: C1 ++ C2) FB mX
                  /\ blk_handle (set_bufdata d p0) s P B0 mX
                  /\ rw_cells ssegs mX B0 [CB (Z.to_nat (pc_bufalloc (set_bufdata d p0))) bs']
                  /\ firstn (length (pc_bufdata (set_bufdata d p0))) bs' = map b8 (pc_bufdata (set_bufdata d p0))
                  /\ (Z.of_nat (length (pc_bufdata (set_bufdata d p0))) <= pc_bufalloc (set_bufdata d p0))%Z
                  /\ pc_priv (set_bufdata d p0) = pc_priv p /\ pc_rfile (set_bufdata d p0) = pc_rfile p /\ pc_self (set_bufdata d p0) = pc_self p
                  /\ pc_bufsize (set_bufdata d p0) = pc_bufsize p /\ pc_swapped (set_bufdata d p0) = pc_swapped p /\ same_meta (set_bufdata d p0) p
                  /\ (exists ccs', rw_cells ssegs mX CUR ccs' /\ cells_size ccs' = 24%nat)).
      { intros mX psX d bsX ccsX GX X1 X2 X3 X4 PF LE XC XS. exists bsX. unfold blk_handle. cbn [pc_buffer pc_bufalloc pc_bufdata pc_priv pc_rfile pc_self pc_bufsize pc_swapped set_bufdata].
        split; [exact GX|]. split; [split; [rewrite E4; exact X1|]; split; [rewrite E5; exact X2|]; split; [exact X3|]; rewrite E4; split; [exact WBS|]; split; [exact WMB|]; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 tl got2 d ccsX BA0 BSA0 E4 Q3; lia)|].
        split; [exact X4|]. split; [exact PF|]. split; [exact LE|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|].
        exists ccsX. split; [exact XC| exact XS]. }
      assert (L8h : length (map b8 (le_bytes 4 bt ++ le_bytes 4 tl)) = 8%nat) by (rewrite length_map, length_app, !length_le_bytes; reflexivity).
      assert (GRh : Forall (fun z => 0 <= z < 256)%Z (le_bytes 4 bt ++ le_bytes 4 tl)) by (apply Forall_app; split; apply le_bytes_4_range).
      destruct (Z.eq_dec (Z.of_nat (length got2)) (tl - 8)) as [LF|LF].
      2:{ (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq _ _) LF). cbn [negb andb]. rewrite Bool.andb_false_r. apply (implM_bind_assoc ssegs).
        hide FRS3. hide HDR4. hide HCUR3. hide HBS3. hide HPV3. hide HMB3. hide HEB3. hide HB84. hide HREST. hide HD5.
        unfold implM. iprefix. step. rewrite (eqb_lits_false (Z.of_nat (length got2)) (tl + -8) ltac:((keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got2 TL GL2; lia)) ltac:((keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got2 TL; lia)) ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got2 LF; lia))). change (negb false) with true. cbv iota. do 3 step.
        unhide FRS3. unhide HDR4. unhide HCUR3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HEB3. unhide HB84. unhide HREST. unhide HD5.
        name_sp sp (-96)%Z.
        apply evt_done. eapply (implM_bind ssegs).
        { eapply FERROR; [| exact HinF | reflexivity].
          split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
        intros e ps6 ms6 PO. cbv beta in PO. destruct PO as (av6 & m6 & E & MI6 & ST6 & AG6 & G6 & -> & -> & ERRNO).
        unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 93928)) with (Z_to_bv 64 93928) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        transport FRS3 m6 AG6 ltac:(prs). transport HDR4 m6 AG6 ltac:(prs). transport HCUR3 m6 AG6 ltac:(prs). transport HBS3 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p ccs got p0 B0 bs0 bt tl got2 INP0; prs)).
        transport HPV3 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p ccs got p0 B0 bs0 bt tl got2 INP0; prs)). transport HMB3 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p s ccs got p0 B0 bs0 bt tl got2 INP0; prs)). transport HEB3 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ej ccs got p0 B0 bs0 bt tl got2 EBX INP0; prs)). transport HB84 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 bt tl got2 TL TLB INB0; prs)).
        transport HREST m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 bt tl got2 TL INB0; prs)). transport HD5 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 bt tl got2 junk5 TLB INB0 GL2; prs)).
        assert (AG6' : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right]. unfold in_block. apply Exists_cons_tl. exact Ha. }
        clear AG6 MI5 ST5 G5.
        (* [comment removed for export] *)
        pose proof HB84 as HBUF6. join_cells HBUF6 HD5. join_cells HBUF6 HREST. merge_all HBUF6.
        lazymatch type of HBUF6 with rw_cells _ _ _ [CB ?n _] => replace n with (Z.to_nat (pc_bufalloc p0)) in HBUF6 by lia end.
        assert (PFX6 : forall junkX restX, firstn (length ((le_bytes 4 bt ++ le_bytes 4 tl) ++ got2)) (map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got2 ++ junkX ++ restX)
                                            = map b8 ((le_bytes 4 bt ++ le_bytes 4 tl) ++ got2)).
        { intros junkX restX. rewrite (map_app b8 (le_bytes 4 bt ++ le_bytes 4 tl) got2).
          replace (map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got2 ++ junkX ++ restX) with ((map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got2) ++ (junkX ++ restX)) by (rewrite <- !app_assoc; reflexivity).
          apply firstn_len_app'. rewrite !length_app, !length_map. reflexivity. }
        destruct e.
        - (* [comment removed for export] *)
          cbv iota. destruct (ERRNO eq_refl) as [EN2 EB2]. clear ERRNO. unfold utp in EN2. rewrite <- TP in EN2.
          eapply implM_pure; [reflexivity|]. cbn [fst snd].
          set (err := lc_errno (ps_libc ps5)) in *.
          hide FRS3. hide HDR4. hide HCUR3. hide HBS3. hide HPV3. hide HMB3. hide HEB3. hide HBUF6.
          cbn [Z.b2z]. step. if_false. do 4 step.
          replace (ret_pc (Z_to_bv 64 93936)) with (Z_to_bv 64 93936) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
          do 4 step.
          replace (sx32 (Z_to_bv 64 err)) with (Z_to_bv 64 (s32 err)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
          unhide FRS3. unhide HDR4. unhide HCUR3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HEB3. unhide HBUF6.
          eapply (KFMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps5 err); [exact (eq_trans OF5 OF3) | exact MI6 | exact ST6 | exact AG6' | exact HDR4 | reflexivity | exact FRS3 | exact HEB3 | lia |].
          exists B0. eapply RESTd; [exact G6 | exact HBS3 | exact HPV3 | exact HMB3 | exact HBUF6 | apply PFX6 | rewrite length_app, <- (length_map b8), L8h; lia | exact HCUR3 | reflexivity].
        - (* [comment removed for export] *)
          cbv iota. clear ERRNO. apply (implM_retb ssegs). cbv beta iota. apply (implM_ret ssegs).
          hide FRS3. hide HDR4. hide HCUR3. hide HBS3. hide HPV3. hide HMB3. hide HEB3. hide HBUF6.
          cbn [Z.b2z]. step. if_true. do 8 step.
          unhide FRS3. unhide HDR4. unhide HCUR3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HEB3. unhide HBUF6.
          replace (tl + -8)%Z with (tl - 8)%Z by lia.
          assert (MSG : fmt_at m6 FMT_TRUNC_PCAPNG "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
            by (apply (fmt_at_intro m6 _ _ MI6); [vm_compute; reflexivity| unfold FMT_TRUNC_PCAPNG; lia| unfold FMT_TRUNC_PCAPNG; cbn; lia]).
          eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps5 _ [AInt (tl - 8); AInt (Z.of_nat (length got2))] FMT_TRUNC_PCAPNG);
            [left; reflexivity | exact (eq_trans OF5 OF3) | exact MI6 | exact ST6 | exact AG6' | exact HDR4 | reflexivity | exact FRS3 | exact HEB3 | exact MSG | reflexivity | cbn; lia
            | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] | unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE; reflexivity
            | vm_compute; reflexivity | apply args_ok_ints2 |].
          exists B0. eapply RESTd; [exact G6 | exact HBS3 | exact HPV3 | exact HMB3 | exact HBUF6 | apply PFX6 | rewrite length_app, <- (length_map b8), L8h; lia | exact HCUR3 | reflexivity].
      }
      (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LF). cbn [negb]. apply (implM_retb ssegs). cbv beta iota.
      rewrite E5.
      destruct (lastn4 got2 ltac:(lia)) as (got1 & u0 & u1 & u2 & u3 & EG & LG1). rewrite EG in GR2. subst got2.
      apply Forall_app in GR2 as [GR1 GU].
      apply Forall_cons_iff in GU as [U0 GU]. apply Forall_cons_iff in GU as [U1 GU]. apply Forall_cons_iff in GU as [U2 GU]. apply Forall_cons_iff in GU as [U3 _].
      rewrite length_app in LF, LG1, HD5. cbn [length] in LF, LG1, HD5.
      (* [comment removed for export] *)
      destruct (rw_cells_cut _ _ _ 1 HD5) as [HD6 _]. clear HD5. cbn [firstn] in HD6.
      rewrite map_app in HD6.
      pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [length got1; 4%nat] HD6 ltac:(cbn; lia)) as HD7. clear HD6. cbn [mk_CB_cells app] in HD7.
      rewrite (firstn_len_app' (map b8 got1)) in HD7 by (symmetry; apply length_map).
      replace (skipn (length got1) (map b8 got1 ++ map b8 [u0; u1; u2; u3])) with (map b8 [u0; u1; u2; u3]) in HD7
        by (rewrite <- (length_map b8 got1) at 1; symmetry; apply skipn_len_app).
      cbn [map firstn] in HD7.
      destruct (rw_cells_cut _ _ _ 1 HD7) as [HG1 HT]. clear HD7. cbn [firstn skipn cells_size csize Nat.add] in HG1, HT.
      lazymatch type of HT with rw_cells _ _ ?A _ => replace A with (B0 + tl + -4)%Z in HT by lia end.
      assert (HT' : rw_cells ssegs m5 (B0 + tl + -4) [C4 (Z_to_bv 64 (le4val u0 u1 u2 u3))]).
      { eapply rw_cells_recell; [exact HT | cbn; repeat split; try exact Logic.I |]. cbn [cells_bytes cbytes app]. rewrite (le4_lit u0 u1 u2 u3) by lia. reflexivity. }
      clear HT.
      (* [comment removed for export] *)
      assert (K80 : forall (rav t0v t1v t2v a1v a2v a4v a5v a6v a7v t3v t4v t5v t6v : word) (hi : Z) (m6 : mem) (w0 w1 w2 w3 : Z) (d3 : list Z),
        (bv_unsigned a4v = le4val w0 w1 w2 w3 + 4294967296 * hi)%Z -> (0 <= hi < 2^32)%Z ->
        (0 <= w0 < 256)%Z -> (0 <= w1 < 256)%Z -> (0 <= w2 < 256)%Z -> (0 <= w3 < 256)%Z ->
        d3 = (le_bytes 4 bt ++ le_bytes 4 tl) ++ got1 ++ [w0; w1; w2; w3] ->
        mem_inv ssegs m6 -> stk ssegs m6 lo (bv_unsigned sp + -96) ->
        agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m6 ->
        rw_cells ssegs m6 (bv_unsigned sp + -96) [C8 (Z_to_bv 64 (bt + 4294967296 * tl))] ->
        rw_cells ssegs m6 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        GIo K R ps5 ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB m6 ->
        rw_cells ssegs m6 (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B0)] ->
        rw_cells ssegs m6 (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
        rw_cells ssegs m6 (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
        rw_cells ssegs m6 B0 [CB 8 (map b8 (le_bytes 4 bt ++ le_bytes 4 tl))] ->
        rw_cells ssegs m6 (B0 + 8) [CB (length got1) (map b8 got1)] ->
        rw_cells ssegs m6 (B0 + tl + -4) [C4 (Z_to_bv 64 (le4val w0 w1 w2 w3))] ->
        rw_cells ssegs m6 (B0 + tl) [CB (Z.to_nat (pc_bufalloc p0) - 8 - Z.to_nat (tl - 8)) (firstn (Z.to_nat (pc_bufalloc p0) - 8 - Z.to_nat (tl - 8)) (skipn (Z.to_nat (tl - 8)) (firstn (Z.to_nat (pc_bufalloc p0) - 8) (skipn 8 bs0))))] ->
        rw_cells ssegs m6 CUR [CB 24 cj] -> rw_cells ssegs m6 EB [CB 256 ej] ->
        implM ssegs (if negb (tl =? get_le32 d3 (tl - 4))
                     then mo_ret MOps (RB_Err (Msg.header_trailer_mismatch tl (get_le32 d3 (tl - 4))) (set_bufdata d3 p0))
                     else mo_ret MOps (RB_Ok (mkCursor 8 (tl - 12) bt) (set_bufdata d3 p0))) ps5 POSTQ
          (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0v t1v t2v (Z_to_bv 64 EB) (Z_to_bv 64 CUR) (Z_to_bv 64 (B0 + tl)) a1v a2v (Z_to_bv 64 (s32 tl)) a4v a5v a6v a7v
                   (Z_to_bv 64 P) (Z_to_bv 64 Af) (Z_to_bv 64 tl) (Z_to_bv 64 (B0 + 8)) (Z_to_bv 64 (tl + -8)) (Z_to_bv 64 (bt + 4294967296 * tl)) (Z_to_bv 64 (s32 tl)) (Z_to_bv 64 B0) s10 s11 t3v t4v t5v t6v)
              F (Z_to_bv 64 0x16ebc) fc None m6 (seg_rom ssegs))).
      { intros rav t0v t1v t2v a1v a2v a4v a5v a6v a7v t3v t4v t5v t6v hi m6 w0 w1 w2 w3 d3 HW4 Hhi W0 W1 W2 W3 Ed3 MI6 ST6 AG6 HDR6 FRS6 G6 HBS6 HPV6 HMB6 HB86 HG16 HT6 HREST6 HCUR6 HEB6.
        clear HDR4 FRS3 HBS3 HPV3 HMB3 HB84 HG1 HT' HREST HCUR3 HEB3 MI5 ST5.
        assert (LG1' : Z.of_nat (length got1) = (tl - 12)%Z) by (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 LF; lia).
        assert (TRL : get_le32 d3 (tl - 4) = le4val w0 w1 w2 w3).
        { rewrite Ed3. rewrite (app_assoc (le_bytes 4 bt ++ le_bytes 4 tl) got1 [w0; w1; w2; w3]). apply get_le32_last4. rewrite !length_app, !length_le_bytes. (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 LF; lia). }
        rewrite TRL.
        assert (LD3 : length d3 = Z.to_nat tl) by (rewrite Ed3, !length_app, !length_le_bytes; cbn [length]; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 LF; lia)).
        assert (GD3 : Forall (fun z => 0 <= z < 256)%Z d3).
        { rewrite Ed3. apply Forall_app. split; [exact GRh|]. apply Forall_app. split; [exact GR1|]. repeat constructor; (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 w0 d3 W0 w1 W1 w2 W2 w3 W3; lia). }
        (* [comment removed for export] *)
        assert (HT8 : rw_cells ssegs m6 (B0 + tl + -4) [CB 4 (map b8 [w0; w1; w2; w3])]).
        { eapply rw_cells_recell; [exact HT6 | cbn; repeat split; try exact Logic.I |]. cbn [cells_bytes cbytes app map]. rewrite (le4_lit w0 w1 w2 w3) by (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 w0 d3 W0 w1 W1 w2 W2 w3 W3; lia). reflexivity. }
        pose proof HB86 as HBUF7. join_cells HBUF7 HG16. join_cells HBUF7 HT8. join_cells HBUF7 HREST6. merge_all HBUF7.
        lazymatch type of HBUF7 with rw_cells _ _ _ [CB ?n _] => replace n with (Z.to_nat (pc_bufalloc p0)) in HBUF7 by (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 TLB LF; lia) end.
        assert (PFX7 : forall restX, firstn (length d3) (map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got1 ++ [b8 w0; b8 w1; b8 w2; b8 w3] ++ restX) = map b8 d3).
        { intros restX. set (A := map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got1 ++ [b8 w0; b8 w1; b8 w2; b8 w3]).
          assert (EA : map b8 d3 = A) by (subst A; rewrite Ed3, !map_app; reflexivity).
          rewrite EA. replace (length d3) with (length A) by (rewrite <- (length_map b8 d3), EA; reflexivity).
          replace (map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got1 ++ [b8 w0; b8 w1; b8 w2; b8 w3] ++ restX) with (A ++ restX)
            by (subst A; rewrite <- !app_assoc; reflexivity).
          apply firstn_len_app. }
        destruct (Z.eq_dec tl (le4val w0 w1 w2 w3)) as [TE|TE].
        - (* [comment removed for export] *)
          rewrite <- TE, Z.eqb_refl. cbn [negb]. apply (implM_ret ssegs).
          pose proof (munch_refl [(CUR, CUR + 24)]%Z m6) as MU7. pose proof (wmono_refl ssegs m6) as WM7.
          hide HDR6. hide FRS6. hide HBS6. hide HPV6. hide HMB6. hide HBUF7. hide HEB6.
          step. rewrite (swrap32_low _ _ _ HW4). rewrite <- TE.
          step. replace (bv_eqb (Z_to_bv 64 (s32 tl)) (Z_to_bv 64 (s32 tl))) with true by (symmetry; apply Z.eqb_refl). cbn [negb]. cbv iota.
          do 6 step.
          unhide HDR6. unhide FRS6. unhide HBS6. unhide HPV6. unhide HMB6. unhide HBUF7. unhide HEB6.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            assert (AGS7 : agrees_on (fun a => outside [(CUR, CUR + 24)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]);
            assert (G7 : GIo K R ps5 ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB mm)
              by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU7 | exact WM7 |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 LO BU CUR1 CUR2; lia)| apply Forall_nil])
          end.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            transport HDR6 mm AGS7 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 CUR1; prs)); transport FRS6 mm AGS7 ltac:((keep_hyps CEILV hptr ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 CUR1; prs)); transport HBS6 mm AGS7 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got p0 B0 bs0 bt tl ps5 got1 u0 u1 u2 u3 d3 m1 LO BU CUR1 P4 G7; prs)); transport HPV6 mm AGS7 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got p0 B0 bs0 bt tl ps5 got1 u0 u1 u2 u3 d3 m1 LO BU CUR1 P4 G7; prs));
            transport HMB6 mm AGS7 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s ccs got p0 B0 bs0 bt tl ps5 got1 u0 u1 u2 u3 d3 m1 LO BU CUR1 P4 G7; prs)); transport HBUF7 mm AGS7 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got p0 B0 bs0 bt tl ps5 got1 u0 u1 u2 u3 w0 w1 w2 w3 d3 m1 LO BU CUR1 SPW Q4; prs)); transport HEB6 mm AGS7 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ej ccs got p0 B0 bs0 bt tl ps5 got1 u0 u1 u2 u3 d3 m1 LO BU CUR1 SPW P4 EBX; prs)) end.
          eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ps5 (RB_Ok _ _) 1%Z); [exact (eq_trans OF5 OF3) | assumption | exact ST6 | | exact HDR6 | reflexivity | exact FRS6 |].
          { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGS7|]. intros a (_ & _ & Hc & _). cbn [outside]. split; [exact Hc| exact Logic.I]. }
          destruct (RESTd _ ps5 d3 _ _ G7 HBS6 HPV6 HMB6 HBUF7 (PFX7 _) ltac:(rewrite LD3; lia) HCUR6 ltac:(reflexivity)) as (bs' & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & _).
          exists (set_bufdata d3 p0), B0, bs'. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
          split; [exact X6|]. split; [exact X7|]. split; [exact X8|]. split; [exact X9|]. split; [exact X10|]. split; [exact X11|].
          cbv beta iota. split; [reflexivity|]. split; [reflexivity|]. split; [exact HEB6|].
          cbn [cur_off cur_remaining cur_block_type pc_bufdata pc_bufalloc set_bufdata].
          split.
          { lazymatch type of HCUR6 with rw_cells _ _ _ [_; _; _; CB 4 ?pad] => exists pad end.
            eapply rw_cells_recell; [exact HCUR6 | pose proof (proj1 (proj1 HCUR6)) as WF; cbn in WF |- *; clear - WF; tauto |].
            cbn [cells_bytes cbytes app]. rewrite (le4_mod32 bt tl) by lia. replace (tl + -12)%Z with (tl - 12)%Z by lia. reflexivity. }
          split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite LD3; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 TL; lia)| exact GD3].
        - (* [comment removed for export] *)
          rewrite (proj2 (Z.eqb_neq _ _) TE). cbn [negb]. apply (implM_ret ssegs).
          hide HDR6. hide FRS6. hide HBS6. hide HPV6. hide HMB6. hide HBUF7. hide HEB6. hide HCUR6.
          step. rewrite (swrap32_low _ _ _ HW4).
          step. rewrite (eqb_s32 tl (le4val w0 w1 w2 w3)) by (unfold le4val; (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 TL lo w0 w1 w2 w3 W0 W1 W2 W3; lia)). rewrite (proj2 (Z.eqb_neq _ _) TE). cbn [negb]. cbv iota.
          do 7 step.
          unhide HDR6. unhide FRS6. unhide HBS6. unhide HPV6. unhide HMB6. unhide HBUF7. unhide HEB6. unhide HCUR6.
          assert (MSG : fmt_at m6 FMT_BLK_TRAILER "block total length in header %u and trailer %u don't match"%string)
            by (apply (fmt_at_intro m6 _ _ MI6); [vm_compute; reflexivity| unfold FMT_BLK_TRAILER; lia| unfold FMT_BLK_TRAILER; cbn; lia]).
          eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps5 _ [AInt (s32 tl); AInt (s32 (le4val w0 w1 w2 w3))] FMT_BLK_TRAILER);
            [left; reflexivity | exact (eq_trans OF5 OF3) | exact MI6 | exact ST6 | exact AG6 | exact HDR6 | reflexivity | exact FRS6 | exact HEB6 | exact MSG | reflexivity | cbn; lia
            | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
            | unfold Msg.header_trailer_mismatch, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
              replace (convs (fmt "block total length in header %u and trailer %u don't match")) with [Cu; Cu] by (vm_compute; reflexivity);
              apply pargs_cons; [apply aeq_s32; reflexivity|]; apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
            | vm_compute; reflexivity | apply args_ok_ints2 |].
          exists B0. eapply RESTd; [exact G6 | exact HBS6 | exact HPV6 | exact HMB6 | exact HBUF7 | apply PFX7 | rewrite LD3; lia | exact HCUR6 | reflexivity]. }
      (* [comment removed for export] *)
      replace (Z.of_nat (length (got1 ++ [u0; u1; u2; u3]))) with (tl + -8)%Z by (rewrite length_app; cbn [length]; lia).
      destruct (pc_swapped p); cbv iota; rewrite !set_bufdata_twice, !pc_bufdata_set; cbn [Z.b2z] in HPV3.
      - (* [comment removed for export] *)
        rewrite (app_assoc (le_bytes 4 bt ++ le_bytes 4 tl) got1 [u0; u1; u2; u3]).
        rewrite (swap_field_last4 _ u0 u1 u2 u3 tl) by (rewrite !length_app, !length_le_bytes; lia).
        rewrite <- (app_assoc (le_bytes 4 bt ++ le_bytes 4 tl) got1 [u3; u2; u1; u0]).
        unfold implM. iprefix.
        hide HDR4. hide FRS3. hide HCUR3. hide HBS3. hide HMB3. hide HEB3. hide HB84. hide HG1. hide HREST.
        step. rewrite (eqb_lits_eq (tl + -8)%Z (tl + -8)%Z eq_refl). cbn [negb]. cbv iota.
        do 4 step. step. if_false.
        eapply evt_cut.
        { eapply (trl_swap_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (B0 + tl) u0 u1 u2 u3);
            [exact MI5 | (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 Q1 LF; lia) | (keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got p0 B0 bs0 bt tl ps5 m5 got1 u0 u1 u2 u3 TLB Q4; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U0; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U1; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U2; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U3; lia) | reflexivity | reflexivity | exact HT']. }
        cbv beta. intros ms' PO. destruct PO as (q1 & q2 & q4 & q5 & hi4 & m6 & -> & MU6 & WM6 & MI6 & HT6 & HW4 & Hhi4). clear HT'.
        assert (AGS6 : agrees_on (fun a => outside [(B0 + tl + -4, B0 + tl)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
        unhide HDR4. unhide FRS3. unhide HCUR3. unhide HBS3. unhide HMB3. unhide HEB3. unhide HB84. unhide HG1. unhide HREST.
        transport HDR4 m6 AGS6 ltac:(prs). transport FRS3 m6 AGS6 ltac:(prs). transport HCUR3 m6 AGS6 ltac:(prs). transport HBS3 m6 AGS6 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 TLB APB0 LF; prs)).
        transport HPV3 m6 AGS6 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 TLB APB0 LF; prs)). transport HMB3 m6 AGS6 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p s ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 TLB APB0 LF; prs)). transport HEB3 m6 AGS6 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ej ccs got p0 B0 bs0 bt tl ps5 m5 got1 u0 u1 u2 u3 LO BU EBX TLB Q4 APB0 G5 LF; prs)). transport HB84 m6 AGS6 ltac:(prs).
        transport HG1 m6 AGS6 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 LF; prs)). transport HREST m6 AGS6 ltac:(prs).
        assert (G6 : GIo K R ps5 ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB m6).
        { eapply (GIo_client_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        assert (ST6 : stk ssegs m6 lo (bv_unsigned sp + -96)).
        { eapply stk_transport_disjoint; [exact ST5 | exact MU6 | exact WM6 | cbn [disjoint_from]; unfold rc_lo in *; lia]. }
        assert (AG6 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AGS6|]. intros a [[Ha|Ha] _]; cbn [outside]; (split; [| exact Logic.I]); [lia|]. pose proof (CLB0 a Ha). (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 a TL TLB H0; lia). }
        apply evt_done.
        eapply (K80 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi4 m6 u3 u2 u1 u0);
          [exact HW4 | exact Hhi4 | lia | lia | lia | lia | reflexivity | exact MI6 | exact ST6 | exact AG6 | exact HDR4 | exact FRS3 | exact G6
          | exact HBS3 | exact HPV3 | exact HMB3 | exact HB84 | exact HG1 | exact HT6 | exact HREST | exact HCUR3 | exact HEB3].
      - (* [comment removed for export] *)
        unfold implM. iprefix.
        hide HDR4. hide FRS3. hide HCUR3. hide HBS3. hide HMB3. hide HEB3. hide HB84. hide HG1. hide HREST.
        step. rewrite (eqb_lits_eq (tl + -8)%Z (tl + -8)%Z eq_refl). cbn [negb]. cbv iota.
        do 4 step. step. if_true.
        unhide HDR4. unhide FRS3. unhide HCUR3. unhide HBS3. unhide HMB3. unhide HEB3. unhide HB84. unhide HG1. unhide HREST.
        apply evt_done.
        eapply (K80 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ((u3 / 128) * 4294967295)%Z m5 u0 u1 u2 u3);
          [rewrite unsigned_sx32 by (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U0 U1 U2 U3; lia); unfold sxv; (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3; lia) | Z.div_mod_to_equations; (keep_hyps CEILV hptr R EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 q r U3 H0 H1; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U0; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U1; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U2; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U3; lia) | reflexivity | exact MI5 | exact ST5 | exact AG5' | exact HDR4 | exact FRS3 | exact G5
          | exact HBS3 | exact HPV3 | exact HMB3 | exact HB84 | exact HG1 | exact HT' | exact HREST | exact HCUR3 | exact HEB3].
    }
    (* [comment removed for export] *)
    assert (KGE12 : forall (rav t0' t1' t2' a2v a4v a5v a6v a7v t3' t4' t5' t6' y4 y7 y8 y9 W : word) (hi : Z) (m3 : mem) (bt tl : Z),
      (0 <= bt < 2^32)%Z -> (12 <= tl < 2^32)%Z -> (0 <= hi < 2^32)%Z -> (bv_unsigned W = tl + 4294967296 * hi)%Z ->
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells ssegs m3 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
      rw_cells ssegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      GIo K R s' (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB m3 ->
      rw_cells ssegs m3 (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B)] ->
      rw_cells ssegs m3 (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells ssegs m3 (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
      rw_cells ssegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      rw_cells ssegs m3 CUR [CB 24 cj] -> rw_cells ssegs m3 EB [CB 256 ej] ->
      implM ssegs (rb_tail f bt tl p) s' POSTQ
        (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 CUR) W (Z_to_bv 64 11) a2v (Z_to_bv 64 (s32 tl)) a4v a5v a6v a7v
                 (Z_to_bv 64 P) (Z_to_bv 64 Af) y4 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 8) y7 y8 y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16d4c) fc None m3 (seg_rom ssegs))).
    { intros rav t0' t1' t2' a2v a4v a5v a6v a7v t3' t4' t5' t6' y4 y7 y8 y9 W hi m3 bt tl BT TL Hhi HW MI3 ST3 AG3 HDR3 FRS3 G3 HBS3 HPV3 HMB3 HBUF3 HCUR3 HEB3.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      assert (LBS : length bs = Z.to_nat (pc_bufalloc p)) by (destruct HBUF3 as [[WF _] _]; cbn in WF; lia).
      assert (TM : (0 <= tl mod 4 < 4)%Z) by (Z.div_mod_to_equations; (keep_hyps CEILV hptr R EB p bs ccs got r H1; lia)).
      unfold rb_tail. rewrite (proj2 (Z.ltb_ge tl 12)) by lia. unfold ng_of. rewrite HS. cbv iota.
      cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_realloc prims].
      unfold implM. iprefix.
      hide HDR3. hide FRS3. hide HBS3. hide HPV3. hide HMB3. hide HBUF3. hide HCUR3. hide HEB3.
      step. change (bv_wrap 64 3) with 3%Z. rewrite (land3_low _ _ _ HW) by lia.
      step.
      destruct (Z.eq_dec (tl mod 4) 0) as [M4|M4].
      2:{ (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq _ _) M4). cbn [negb]. rewrite (eqb_lits_false (tl mod 4) 0 ltac:(lia) ltac:(lia) M4). cbv iota.
        apply evt_done. apply (implM_ret ssegs).
        do 5 step.
        unhide HDR3. unhide FRS3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HBUF3. unhide HCUR3. unhide HEB3.
        assert (MSG : fmt_at m3 FMT_BLK_MULT4 "block in pcapng dump file has a length of %u that is not a multiple of 4"%string)
          by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_BLK_MULT4; lia| unfold FMT_BLK_MULT4; cbn; lia]).
        eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' _ [AInt (s32 tl)] FMT_BLK_MULT4);
          [right; reflexivity | exact OF1 | exact MI3 | exact ST3 | exact AG3 | exact HDR3 | reflexivity | exact FRS3 | exact HEB3 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; constructor; [reflexivity| constructor]
          | unfold Msg.block_length_not_mult4, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            replace (convs (fmt "block in pcapng dump file has a length of %u that is not a multiple of 4")) with [Cu] by (vm_compute; reflexivity);
            apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
          | vm_compute; reflexivity | apply args_ok_ints1 |].
        destruct (RESTp m3 s' G3 HBS3 HPV3 HMB3 HBUF3) as (X1 & X2 & X3 & X4 & X5 & _).
        exists B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
        do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. exists [CB 24 cj]. split; [exact HCUR3| reflexivity]. }
      (* [comment removed for export] *)
      rewrite M4. cbn [Z.eqb negb]. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
      unhide HBS3. step. hide HBS3. rewrite (sx32_s32 (pc_bufsize p)) by lia.
      do 2 step. rewrite (shl_shr_32 _ _ _ HW) by lia.
      step.
      destruct (Z.lt_ge_cases (pc_bufsize p) tl) as [BLT|BGE].
      2:{ (* [comment removed for export] *)
        rewrite (proj2 (Z.ltb_ge _ _) BGE). if_tf true.
        unhide HBS3. do 3 step.
        unhide HDR3. unhide FRS3. unhide HPV3. unhide HMB3. unhide HBUF3. unhide HCUR3. unhide HEB3.
        apply evt_done. apply (implM_retb ssegs). cbv beta iota.
        eapply (KBODY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' p B bs bt tl);
          [exact OF1 | lia | lia | exact MI3 | exact ST3 | exact AG3 | exact HDR3 | exact FRS3 | eapply (GIo_perm K HPL); [exact G3| apply Permutation_sym; apply Permutation_middle]
          | exact HBS3 | exact HPV3 | exact HMB3 | exact HBUF3 | exact PFX | exact LENB | lia | lia | exact BSA | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | unfold same_meta; repeat split
          | exact HCUR3 | exact HEB3]. }
      (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_lt _ _) BLT). if_tf false.
      unhide HMB3. step. hide HMB3. rewrite (sx32_s32 (ng_max_blocksize s)) by lia.
      step.
      destruct (Z.lt_ge_cases (ng_max_blocksize s) tl) as [MLT|MGE].
      { (* [comment removed for export] *)
        rewrite (proj2 (Z.ltb_lt _ _) MLT). if_tf false.
        apply evt_done. apply (implM_retb ssegs). cbv beta iota. apply (implM_ret ssegs).
        do 8 step.
        unhide HDR3. unhide FRS3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HBUF3. unhide HCUR3. unhide HEB3.
        assert (MSG : fmt_at m3 FMT_BLK_GTMAX "pcapng block size %u > maximum %u"%string)
          by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_BLK_GTMAX; lia| unfold FMT_BLK_GTMAX; cbn; lia]).
        eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' _ [AInt (s32 tl); AInt (s32 (ng_max_blocksize s))] FMT_BLK_GTMAX);
          [left; reflexivity | exact OF1 | exact MI3 | exact ST3 | exact AG3 | exact HDR3 | reflexivity | exact FRS3 | exact HEB3 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
          | unfold Msg.block_size_gt_max, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            replace (convs (fmt "pcapng block size %u > maximum %u")) with [Cu; Cu] by (vm_compute; reflexivity);
            apply pargs_cons; [apply aeq_s32; reflexivity|]; apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
          | vm_compute; reflexivity | apply args_ok_ints2 |].
        destruct (RESTp m3 s' G3 HBS3 HPV3 HMB3 HBUF3) as (X1 & X2 & X3 & X4 & X5 & _).
        exists B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
        do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. exists [CB 24 cj]. split; [exact HCUR3| reflexivity]. }
      (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_ge _ _) MGE). if_tf true.
      unhide HBS3. do 4 step.
      unhide HDR3. unhide FRS3. unhide HPV3. unhide HMB3. unhide HBUF3. unhide HCUR3. unhide HEB3.
      apply evt_done. apply (implM_bind_assoc ssegs).
      name_sp sp (-96)%Z.
      eapply (implM_bind ssegs).
      { eapply REALLOC; [| reflexivity | reflexivity | lia | exact HBUF3].
        split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros r ps4 ms4 PO. cbv beta in PO. destruct PO as (av4 & m4 & E & OF4 & MI4 & ST4 & AG4 & RM).
      unfold hpost_regs in E. destruct_exs E. subst ms4. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 93708)) with (Z_to_bv 64 93708) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      transport HDR3 m4 AG4 ltac:(prs). transport FRS3 m4 AG4 ltac:(prs). transport HCUR3 m4 AG4 ltac:(prs). transport HBS3 m4 AG4 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p bs ccs got tl INPc; prs)).
      transport HPV3 m4 AG4 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p bs ccs got tl INPc; prs)). transport HMB3 m4 AG4 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p s bs ccs got tl INPc; prs)). transport HEB3 m4 AG4 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p bs ej ccs got tl EBX INPc; prs)). clear HBUF3.
      assert (AG04 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m4).
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AG4|]. intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]. }
      clear AG4 MI3 ST3 G3 AG3.
      destruct r as [b'|].
      - (* [comment removed for export] *)
        destruct RM as (A' & junkR & -> & G4 & HB4).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G4 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
        apply (implM_retb ssegs). cbv beta iota.
        pose proof (munch_refl [(P + 24, P + 32)]%Z m4) as MU5. pose proof (wmono_refl ssegs m4) as WM5.
        unfold implM. iprefix.
        hide HDR3. hide FRS3. hide HCUR3. hide HPV3. hide HMB3. hide HEB3. hide HB4.
        step. rewrite (eqb_lits_false A' 0 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs got tl b' ps4 m4 A' TL Q1 Q4; lia)) ltac:((keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A'; lia)) ltac:((keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A' Q1; lia))). cbv iota.
        step.
        unhide HDR3. unhide FRS3. unhide HCUR3. unhide HPV3. unhide HMB3. unhide HEB3. unhide HB4.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGS5 : agrees_on (fun a => outside [(P + 24, P + 32)]%Z a) m4 mm) by (eapply agrees_on_of_munch; [exact MU5 | exact WM5 | intros a _ Ho; exact Ho]);
          assert (G5 : GIo K R ps4 ((b', A', tl) :: C1 ++ C2) FB mm)
            by (eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MU5 | exact WM5 |]; apply Forall_cons; [| apply Forall_nil]; right; unfold iv_in_block; apply Exists_cons_tl;
                apply Exists_exists; exists (pc_self p, P, PCAP_NG_SF_TOTAL); split; [exact HinP|]; cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A'; lia));
          transport HDR3 mm AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs got bt tl b' ps4 A' m1 LO BU P4 G5; prs)); transport FRS3 mm AGS5 ltac:((keep_hyps CEILV H hptr K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R C1 C2 FB P B CUR EB lo p bs ccs got tl b' ps4 A' m1 LO BU P4 G5; prs)); transport HCUR3 mm AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs cj got tl b' ps4 A' m1 LO BU CUR1 SPW P4; prs)); transport HPV3 mm AGS5 ltac:((keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A'; prs));
          transport HMB3 mm AGS5 ltac:((keep_hyps CEILV hptr sp R P B CUR EB p s bs ccs got tl A'; prs)); transport HEB3 mm AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ej ccs got tl b' ps4 A' m1 LO BU P4 EBX G5; prs));
          transport HB4 mm AGS5 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside] in *; pose proof (head_apart K _ _ _ _ _ _ _ G4 HinP) as AP; cbn [cb_addr cb_size fst snd] in AP; unfold PCAP_NG_SF_TOTAL in AP; (keep_hyps CEILV hptr sp R P B CUR EB lo p bs ccs got tl A' a B3 Ha AP; lia))
        end.
        merge_all HB4. lazymatch type of HB4 with rw_cells _ _ _ [CB ?n _] => replace n with (Z.to_nat tl) in HB4 by lia end.
        apply evt_done.
        eapply (KBODY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ps4 (set_buffer b' (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p) A' _ bt tl);
          [exact (eq_trans OF4 OF1) | (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got bt tl A' BT; lia) | (keep_hyps CEILV hptr sp R P B CUR EB lo p s bs ccs got tl A' WMB TL MGE; lia) | assumption | assumption | | exact HDR3 | exact FRS3 | exact G5 | exact HBS3 | exact HPV3 | exact HMB3 | exact HB4
          | cbn [pc_bufdata set_buffer]; unfold zfirstn; apply realloc_prefix; [exact PFX | exact LENB | exact LBS | (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A' TL; lia)]
          | cbn [pc_bufdata pc_bufalloc set_buffer]; unfold zfirstn; rewrite length_firstn; (keep_hyps CEILV hptr sp R P B CUR EB lo p bs ccs got tl A' TL; lia)
          | cbn [pc_bufalloc set_buffer]; (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A'; lia) | cbn [pc_bufalloc set_buffer]; (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A' TL; lia) | cbn [pc_bufsize pc_bufalloc set_buffer]; (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A' BLT; lia)
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | unfold same_meta; repeat split | exact HCUR3 | exact HEB3 ].
        { eapply agrees_on_trans; [exact AG04|]. eapply agrees_on_weaken; [exact AGS5|]. intros a (_ & Hn & _). cbn [outside]. split; [exact Hn| exact Logic.I]. }
      - (* [comment removed for export] *)
        destruct RM as (-> & G4 & HB4 & _).
        apply (implM_retb ssegs). cbv beta iota. apply (implM_ret ssegs).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G4 HinP') as (_ & _ & _ & _ & P5 & _). cbn [cb_addr cb_size fst snd] in P5. unfold PCAP_NG_SF_TOTAL in P5.
        assert (OOMS : fmt_at m4 STR_OOM "out of memory"%string)
          by (apply (fmt_at_intro m4 _ _ MI4); [vm_compute; reflexivity| unfold STR_OOM; lia| unfold STR_OOM; cbn; lia]).
        destruct OOMS as [OOMB _].
        pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [14%nat; 242%nat] HEB3 ltac:(reflexivity)) as HE'. clear HEB3. cbn [mk_CB_cells app] in HE'.
        destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
        hide HDR3. hide FRS3. hide HCUR3. hide HBS3. hide HPV3. hide HMB3. hide HB4. hide HE2.
        step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
        do 5 step.
        eapply evt_cut.
        { eapply (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB STR_OOM 14);
            [reflexivity | reflexivity | reflexivity | exact OOMB | reflexivity | lia | exact HE1 | unfold STR_OOM; gio_ceil_fact; clear -CLO__ EBX P5 LO BU SPW; lia | lia | unfold STR_OOM; lia | exact MI4]. }
        cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m5 & -> & MU5 & WM5 & MI5 & HE1' & _). clear HE1.
        replace (ret_pc (Z_to_bv 64 94016)) with (Z_to_bv 64 94016) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (AGS5 : agrees_on (fun a => outside [(EB, EB + 14)]%Z a) m4 m5) by (eapply agrees_on_of_munch; [exact MU5 | exact WM5 | intros a _ Ho; exact Ho]).
        unhide HDR3. unhide FRS3. unhide HCUR3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HB4. unhide HE2.
        transport HDR3 m5 AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs got bt tl ps4 m4 LO BU P4 EBX G4; prs)). transport FRS3 m5 AGS5 ltac:(prs). transport HCUR3 m5 AGS5 ltac:(prs). transport HBS3 m5 AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs got tl ps4 m4 LO BU P4 EBX G4; prs)).
        transport HPV3 m5 AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs got tl ps4 m4 LO BU P4 EBX G4; prs)). transport HMB3 m5 AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s bs ccs got tl ps4 m4 LO BU P4 EBX G4; prs)). transport HB4 m5 AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs got tl ps4 m4 LO BU B4 APB EBX G4; prs)). transport HE2 m5 AGS5 ltac:(prs).
        assert (G5 : GIo K R ps4 (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB m5).
        { eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MU5 | exact WM5 |]. apply Forall_cons; [| apply Forall_nil].
          destruct EBX as [X| ->]; [left; cbn [fst snd]; unfold rc_lo; lia| right]. unfold iv_in_block. apply Exists_exists.
          exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [| cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia].
          apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; right; exact X]. }
        assert (ST5 : stk ssegs m5 lo (bv_unsigned sp + -96)).
        { eapply stk_transport_disjoint; [exact ST4 | exact MU5 | exact WM5 | cbn [disjoint_from]; destruct EBX as [X| ->]; unfold rc_lo in *; (keep_hyps CEILV hptr sp R P B CUR EB lo p bs ccs got tl X H K C1 C2 FB ps4 m5 LO P4 G5; lia)]. }
        assert (AG05 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m5).
        { eapply agrees_on_trans; [exact AG04|]. eapply agrees_on_weaken; [exact AGS5|]. intros a (_ & _ & _ & Hn). cbn [outside]. split; [lia| exact Logic.I]. }
        hide HDR3. hide FRS3. hide HCUR3. hide HBS3. hide HPV3. hide HMB3. hide HB4. hide HE2. hide HE1'.
        do 2 step.
        unhide HDR3. unhide FRS3. unhide HCUR3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HB4. unhide HE2. unhide HE1'.
        eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps4 (RB_Err _ p) (-1)%Z);
          [exact (eq_trans OF4 OF1) | exact MI5 | exact ST5 | exact AG05 | exact HDR3 | reflexivity | exact FRS3 |].
        destruct (RESTp m5 ps4 G5 HBS3 HPV3 HMB3 HB4) as (X1 & X2 & X3 & X4 & X5 & _).
        exists p, B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
        do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. cbv beta iota. split; [reflexivity|]. split; [reflexivity|].
        assert (OOM : Msg.out_of_memory = [111; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121]%Z) by (vm_compute; reflexivity).
        rewrite OOM. cbn [length Nat.add Nat.sub map app].
        split; [| split; [cbn; lia| split; [repeat constructor| exists [CB 24 cj]; split; [exact HCUR3| reflexivity]]]].
        lazymatch type of HE2 with rw_cells _ _ _ [CB _ ?j] => exists j end. join_cells HE1' HE2.
        eapply rw_cells_recell; [exact HE1' | pose proof (proj1 (proj1 HE1')) as WF; cbn in WF |- *; clear - WF; tauto | reflexivity]. }
    (* [comment removed for export] *)
    assert (KLT12 : forall (rav t0' t1' t2' a0v a2v a4v a5v a6v a7v t3' t4' t5' t6' y4 y7 y8 y9 : word) (m3 : mem) (bt tl : Z),
      (0 <= bt < 2^32)%Z -> (0 <= tl < 12)%Z ->
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells ssegs m3 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
      rw_cells ssegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      GIo K R s' (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB m3 ->
      rw_cells ssegs m3 (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B)] ->
      rw_cells ssegs m3 (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells ssegs m3 (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
      rw_cells ssegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      rw_cells ssegs m3 CUR [CB 24 cj] -> rw_cells ssegs m3 EB [CB 256 ej] ->
      implM ssegs (rb_tail f bt tl p) s' POSTQ
        (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 CUR) a0v (Z_to_bv 64 11) a2v (Z_to_bv 64 (s32 tl)) a4v a5v a6v a7v
                 (Z_to_bv 64 P) (Z_to_bv 64 Af) y4 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 8) y7 y8 y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16cf4) fc None m3 (seg_rom ssegs))).
    { intros rav t0' t1' t2' a0v a2v a4v a5v a6v a7v t3' t4' t5' t6' y4 y7 y8 y9 m3 bt tl BT TL MI3 ST3 AG3 HDR3 FRS3 G3 HBS3 HPV3 HMB3 HBUF3 HCUR3 HEB3.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      unfold rb_tail. rewrite (proj2 (Z.ltb_lt tl 12)) by lia. apply (implM_ret ssegs).
      rewrite (s32_small tl) by lia.
      hide HDR3. hide FRS3. hide HBS3. hide HPV3. hide HMB3. hide HBUF3. hide HCUR3. hide HEB3.
      do 7 step.
      unhide HDR3. unhide FRS3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HBUF3. unhide HCUR3. unhide HEB3.
      assert (MSG : fmt_at m3 FMT_BLK_LT "block in pcapng dump file has a length of %u < %zu"%string)
        by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_BLK_LT; lia| unfold FMT_BLK_LT; cbn; lia]).
      eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' _ [AInt tl; AInt 12] FMT_BLK_LT);
        [left; reflexivity | exact OF1 | exact MI3 | exact ST3 | exact AG3 | exact HDR3 | reflexivity | exact FRS3 | exact HEB3 | exact MSG | reflexivity | cbn; lia
        | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | unfold Msg.block_length_lt, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints2 |].
      destruct (RESTp m3 s' G3 HBS3 HPV3 HMB3 HBUF3) as (X1 & X2 & X3 & X4 & X5 & _).
      exists B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
      do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. exists [CB 24 cj]. split; [exact HCUR3| reflexivity]. }
    (* [comment removed for export] *)
    destruct (Z.eq_dec (Z.of_nat (length got)) 8) as [L8|L8].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) L8). cbn [negb]. apply (implM_bind_assoc ssegs).
      hide HBS. hide HPV. hide HMB. hide HBUF. hide HEB. hide HCUR. hide HD2. hide FRS.
      ienter. step. rewrite (eqb_lits_false (Z.of_nat (length got)) 8 ltac:(lia) ltac:(lia) L8). change (negb false) with true. cbv iota. do 3 step.
      unhide HBS. unhide HPV. unhide HMB. unhide HBUF. unhide HEB. unhide HCUR. unhide HD2. unhide FRS.
      name_sp sp (-96)%Z.
      apply evt_done. eapply (implM_bind ssegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros e ps3 ms3 PO. cbv beta in PO. destruct PO as (av3 & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO).
      unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 93464)) with (Z_to_bv 64 93464) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      transport FRS m3 AG3 ltac:(prs). transport HD2 m3 AG3 ltac:(prs). transport HCUR m3 AG3 ltac:(prs). transport HBS m3 AG3 ltac:(prs).
      transport HPV m3 AG3 ltac:(prs). transport HMB m3 AG3 ltac:(prs). transport HBUF m3 AG3 ltac:(prs). transport HEB m3 AG3 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ej ccs got EBX INP; prs)).
      assert (AG03 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3).
      { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] _]; [left; lia| right].
        apply in_block_app in Ha as [X|X]; apply in_block_app; [left; exact X| right; right; exact X]. }
      clear AG3 MI1 ST1 G1.
      assert (X8 : (Z.of_nat (length got) + Z.of_nat (8 - length got) = 8)%Z) by lia.
      destruct e.
      - (* [comment removed for export] *)
        cbv iota. destruct (ERRNO eq_refl) as [EN2 EB2]. clear ERRNO.
        unfold utp in EN2. rewrite <- TP in EN2.
        eapply implM_pure; [reflexivity|]. cbn [fst snd].
        set (err := lc_errno (ps_libc s')) in *.
        hide HBS. hide HPV. hide HMB. hide HBUF. hide HEB. hide HCUR. hide HD2. hide FRS.
        cbn [Z.b2z]. step. if_false. do 4 step.
        replace (ret_pc (Z_to_bv 64 93472)) with (Z_to_bv 64 93472) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        do 3 step.
        replace (sx32 (Z_to_bv 64 err)) with (Z_to_bv 64 (s32 err)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
        unhide HBS. unhide HPV. unhide HMB. unhide HBUF. unhide HEB. unhide HCUR. unhide HD2. unhide FRS.
        eapply (KFMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' err p); [exact OF1 | exact MI3 | exact ST3 | exact AG03 | exact HD2 | cbn [cells_size csize Nat.add]; lia | exact FRS | exact HEB | lia |].
        destruct (RESTp m3 s' G3 HBS HPV HMB HBUF) as (X1 & X2 & X3 & X4 & X5 & _).
        exists B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
        do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. exists [CB 24 cj]. split; [exact HCUR| reflexivity].
      - (* [comment removed for export] *)
        cbv iota. clear ERRNO. cbn [negb andb]. rewrite Bool.andb_true_r.
        destruct (Nat.eq_dec (length got) 0) as [L0|L0].
        + (* [comment removed for export] *)
          rewrite (proj2 (Z.eqb_eq (Z.of_nat (length got)) 0) ltac:(lia)). apply (implM_retb ssegs). cbv beta iota. apply (implM_ret ssegs).
          hide HBS. hide HPV. hide HMB. hide HBUF. hide HEB. hide HCUR. hide HD2. hide FRS.
          cbn [Z.b2z]. step. if_true. step. rewrite (eqb_lits_eq (Z.of_nat (length got)) 0) by lia. cbv iota. do 2 step.
          unhide HBS. unhide HPV. unhide HMB. unhide HBUF. unhide HEB. unhide HCUR. unhide HD2. unhide FRS.
          eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' (RB_Eof p) 0%Z);
            [exact OF1 | exact MI3 | exact ST3 | exact AG03 | exact HD2 | cbn [cells_size csize Nat.add]; lia | exact FRS |].
          destruct (RESTp m3 s' G3 HBS HPV HMB HBUF) as (X1 & X2 & X3 & X4 & X5 & _).
          exists p, B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
          do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. cbv beta iota. split; [reflexivity|]. split; [reflexivity|]. split; [exact HEB|]. exists [CB 24 cj]. split; [exact HCUR| reflexivity].
        + (* [comment removed for export] *)
          rewrite (proj2 (Z.eqb_neq (Z.of_nat (length got)) 0) ltac:(lia)). apply (implM_retb ssegs). cbv beta iota. apply (implM_ret ssegs).
          hide HBS. hide HPV. hide HMB. hide HBUF. hide HEB. hide HCUR. hide HD2. hide FRS.
          cbn [Z.b2z]. step. if_true. step. rewrite (eqb_lits_false (Z.of_nat (length got)) 0 ltac:((keep_hyps CEILV hptr sp R P B CUR EB p ccs got GL; lia)) ltac:((keep_hyps CEILV hptr sp R P B CUR EB p ccs got; lia)) ltac:((keep_hyps CEILV hptr sp R P B CUR EB p ccs got L0; lia))). cbv iota. do 7 step.
          unhide HBS. unhide HPV. unhide HMB. unhide HBUF. unhide HEB. unhide HCUR. unhide HD2. unhide FRS.
          assert (MSG : fmt_at m3 FMT_TRUNC_PCAPNG "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
            by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_TRUNC_PCAPNG; lia| unfold FMT_TRUNC_PCAPNG; cbn; lia]).
          eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' _ [AInt 8; AInt (Z.of_nat (length got))] FMT_TRUNC_PCAPNG _ p);
            [left; reflexivity | exact OF1 | exact MI3 | exact ST3 | exact AG03 | exact HD2 | cbn [cells_size csize Nat.add]; lia | exact FRS | exact HEB | exact MSG | reflexivity | cbn; lia
            | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] | unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE; reflexivity
            | vm_compute; reflexivity | apply args_ok_ints2 |].
          destruct (RESTp m3 s' G3 HBS HPV HMB HBUF) as (X1 & X2 & X3 & X4 & X5 & _).
          exists B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
          do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. exists [CB 24 cj]. split; [exact HCUR| reflexivity]. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) L8). cbn [negb]. apply (implM_retb ssegs). cbv beta iota.
    assert (L8n : length got = 8%nat) by lia.
    destruct got as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|gx gr]]]]]]]]]; try (exfalso; cbn in L8n; (keep_hyps CEILV hptr sp R P B CUR EB p ccs L8n g0 g1 g2 g3 g4 g5 g6 g7 gx gr; lia)). clear L8n L8.
    pose proof GR as GR'.
    apply Forall_cons_iff in GR' as [R0 GR']. apply Forall_cons_iff in GR' as [R1 GR']. apply Forall_cons_iff in GR' as [R2 GR']. apply Forall_cons_iff in GR' as [R3 GR'].
    apply Forall_cons_iff in GR' as [R4 GR']. apply Forall_cons_iff in GR' as [R5 GR']. apply Forall_cons_iff in GR' as [R6 GR']. apply Forall_cons_iff in GR' as [R7 _].
    assert (LJ : length junk' = 0%nat) by (destruct HD2 as [[WF _] _]; cbn in WF; lia). destruct junk' as [|jx jr]; [|discriminate LJ]. clear LJ.
    assert (HD5 : rw_cells ssegs m2 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7))]).
    { eapply rw_cells_recell; [exact HD2 | cbn; repeat split; try exact Logic.I |]. cbn [cells_bytes cbytes map app]. rewrite (le4_lit g0 g1 g2 g3), (le4_lit g4 g5 g6 g7) by (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R0 R1 R2 R3 R4 R5 R6 R7; lia). reflexivity. }
    clear HD2.
    unfold get_le32, zslice, zfirstn, zskipn. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. cbn [firstn skipn].
    replace (Z.of_nat (length [g0; g1; g2; g3; g4; g5; g6; g7])) with 8%Z by reflexivity.
    unfold implM. iprefix.
    hide FRS. hide HCUR. hide HBS. hide HMB. hide HBUF. hide HEB.
    step. if_false.
    destruct (pc_swapped p); cbn [Z.b2z] in HPV |- *.
    - (* [comment removed for export] *)
      rewrite (bswap32_bytes g0 g1 g2 g3), (bswap32_bytes g4 g5 g6 g7) by (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R0 R1 R2 R3 R4 R5 R6 R7; lia). rewrite !le_of_bytes_4.
      replace (g3 + 256 * g2 + 65536 * g1 + 16777216 * g0)%Z with (le4val g3 g2 g1 g0) by reflexivity.
      replace (g7 + 256 * g6 + 65536 * g5 + 16777216 * g4)%Z with (le4val g7 g6 g5 g4) by reflexivity.
      step. step. if_false.
      eapply evt_cut.
      { eapply (blk_swap_hdr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g0 g1 g2 g3 g4 g5 g6 g7);
          [exact MI1 | (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs g0 g1 g2 g3 g4 g5 g6 g7 LO BU SPW; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R0; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R1; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R2; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R3; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R4; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R5; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R6; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R7; lia) | exact HD5]. }
      cbv beta. intros ms' PO. destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & hi & m3 & -> & MU3 & WM3 & MI3 & HD3 & HW & Hhi). clear HD5.
      assert (AGS3 : agrees_on (fun a => outside [(bv_unsigned sp + -96, bv_unsigned sp + -88)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]).
      unhide FRS. unhide HCUR. unhide HBS. unhide HMB. unhide HBUF. unhide HEB.
      transport FRS m3 AGS3 ltac:(prs). transport HCUR m3 AGS3 ltac:(prs). transport HBS m3 AGS3 ltac:(prs). transport HPV m3 AGS3 ltac:(prs).
      transport HMB m3 AGS3 ltac:(prs). transport HBUF m3 AGS3 ltac:(prs). transport HEB m3 AGS3 ltac:(prs).
      assert (G3 : GIo K R s' (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB m3).
      { eapply (GIo_client_frame K HFL SFL); [exact G1 | exact MU3 | exact WM3 |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (ST3 : stk ssegs m3 lo (bv_unsigned sp + -96)).
      { eapply stk_transport_disjoint; [exact ST1 | exact MU3 | exact WM3 | cbn [disjoint_from]; lia]. }
      assert (AG03 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3).
      { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AGS3|]. intros a [[Ha|Ha] _]; cbn [outside]; (split; [| exact Logic.I]); [lia|]. pose proof (CLB a Ha). lia. }
      hide FRS. hide HCUR. hide HBS. hide HPV. hide HMB. hide HBUF. hide HEB. hide HD3.
      step. rewrite (swrap32_low _ _ _ HW). do 2 step.
      unhide FRS. unhide HCUR. unhide HBS. unhide HPV. unhide HMB. unhide HBUF. unhide HEB. unhide HD3.
      destruct (Z.lt_ge_cases (le4val g7 g6 g5 g4) 12) as [LT|GE].
      + if_tf false. apply evt_done.
        eapply (KLT12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3); [unfold le4val; lia | unfold le4val in *; lia | exact MI3 | exact ST3 | exact AG03 | exact HD3 | exact FRS | exact G3
          | exact HBS | exact HPV | exact HMB | exact HBUF | exact HCUR | exact HEB].
      + if_tf true. apply evt_done.
        eapply (KGE12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi m3); [unfold le4val; lia | unfold le4val in *; lia | exact Hhi | exact HW | exact MI3 | exact ST3 | exact AG03 | exact HD3 | exact FRS | exact G3
          | exact HBS | exact HPV | exact HMB | exact HBUF | exact HCUR | exact HEB].
    - (* [comment removed for export] *)
      rewrite !le_of_bytes_4.
      replace (g0 + 256 * g1 + 65536 * g2 + 16777216 * g3)%Z with (le4val g0 g1 g2 g3) by reflexivity.
      replace (g4 + 256 * g5 + 65536 * g6 + 16777216 * g7)%Z with (le4val g4 g5 g6 g7) by reflexivity.
      step. step. if_true.
      step. step.
      rewrite (swrap32_low (bv_unsigned (sx32 (Z_to_bv 64 (le4val g4 g5 g6 g7)))) (le4val g4 g5 g6 g7) ((g7 / 128) * 4294967295)%Z ltac:(rewrite unsigned_sx32 by lia; unfold sxv; lia)).
      do 2 step.
      unhide FRS. unhide HCUR. unhide HBS. unhide HMB. unhide HBUF. unhide HEB.
      destruct (Z.lt_ge_cases (le4val g4 g5 g6 g7) 12) as [LT|GE].
      + if_tf true. apply evt_done.
        eapply (KLT12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2); [unfold le4val; lia | unfold le4val in *; lia | exact MI1 | exact ST1 | exact AG02 | exact HD5 | exact FRS | exact G1
          | exact HBS | exact HPV | exact HMB | exact HBUF | exact HCUR | exact HEB].
      + if_tf false. apply evt_done.
        eapply (KGE12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ((g7 / 128) * 4294967295)%Z m2);
          [unfold le4val; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs g0 g1 g2 g3 g4 g5 g6 g7 R0 R1 R2 R3; lia) | unfold le4val in *; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs g0 g1 g2 g3 g4 g5 g6 g7 R4 R5 R6 R7 GE; lia) | Z.div_mod_to_equations; (keep_hyps CEILV hptr R EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 q r R7 H0 H1; lia) | rewrite unsigned_sx32 by (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R4 R5 R6 R7; lia); unfold sxv; (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7; lia)
          | exact MI1 | exact ST1 | exact AG02 | exact HD5 | exact FRS | exact G1 | exact HBS | exact HPV | exact HMB | exact HBUF | exact HCUR | exact HEB].
  Qed.
  End Sz2.
  Theorem read_block_proof : ltac:(let t := eval cbv delta [read_block_proof__stmt] in read_block_proof__stmt in exact t).
  Proof using FERROR FMT FREAD HAL HFL HPL REALLOC SFL SNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R st C1 C2 FB f Af P B CUR EB lo p s i a_bhdr bs ej ccs. ltac2:(SecDiet.SzSec.closeP 'read_block_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Blk.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_rb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA.TwB.
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
Definition FMT_BLK_LT : Z := 0x105fa.      (* [comment removed for export] *)
Definition FMT_BLK_MULT4 : Z := 0x10af8.   (* [comment removed for export] *)
Definition FMT_BLK_GTMAX : Z := 0x10666.   (* [comment removed for export] *)
Definition FMT_BLK_TRAILER : Z := 0x10a58. (* [comment removed for export] *)
Definition STR_OOM : Z := 0x10df2.         (* [comment removed for export] *)

Section Blk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.

  (* [comment removed for export] *)
  Definition rb_body (f : hptr) (bt tl : Z) (p0 : pcapT) : M PS block_result :=
    let p1 := set_bufdata (le_bytes 4 bt ++ le_bytes 4 tl) p0 in
    mo_bind MOps (read_bytes MOps (prims HO fo_nop sites) f (DHeap (pc_buffer p1) 8) (tl - 8) true) (fun x => let '(st, data) := x in
    let p2 := set_bufdata (pc_bufdata p1 ++ data) p1 in
    match st with
    | RBS_Err m => mo_ret MOps (RB_Err m p2)
    | RBS_Eof => mo_ret MOps (RB_Err [] p2)
    | RBS_Ok =>
      let toff := tl - 4 in
      let p3 := if pc_swapped p2 then set_bufdata (swap_field 4 toff (pc_bufdata p2)) p2 else p2 in
      let trailer_length := get_le32 (pc_bufdata p3) toff in
      if negb (tl =? trailer_length)
      then mo_ret MOps (RB_Err (Msg.header_trailer_mismatch tl trailer_length) p3)
      else mo_ret MOps (RB_Ok (mkCursor 8 (tl - 12) bt) p3)
    end).

  Definition rb_tail (f : hptr) (bt tl : Z) (p : pcapT) : M PS block_result :=
    if tl <? 12 then mo_ret MOps (RB_Err (Msg.block_length_lt tl) p)
    else if negb (tl mod 4 =? 0) then mo_ret MOps (RB_Err (Msg.block_length_not_mult4 tl) p)
    else
    mo_bind MOps
      (if pc_bufsize p <? tl then
         if ng_max_blocksize (ng_of p) <? tl
         then mo_ret MOps (Some (Msg.block_size_gt_max tl (ng_max_blocksize (ng_of p))), p)
         else
           mo_bind MOps (e_realloc (prims HO fo_nop sites) (pc_buffer p) tl) (fun r =>
           match r with
           | None => mo_ret MOps (Some Msg.out_of_memory, p)
           | Some b => mo_ret MOps (@None (list Z), set_buffer b (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p)
           end)
       else mo_ret MOps (@None (list Z), p))
      (fun x => let '(gerr, p0) := x in
       match gerr with
       | Some m => mo_ret MOps (RB_Err m p0)
       | None => rb_body f bt tl p0
       end).

  Lemma read_block_eq : forall a_bhdr (p : pcapT),
    read_block MOps (prims HO fo_nop sites) a_bhdr p =
    mo_bind MOps (read_bytes MOps (prims HO fo_nop sites) (pc_rfile p) a_bhdr 8 false) (fun x => let '(st, bh) := x in
      match st with
      | RBS_Eof => mo_ret MOps (RB_Eof p)
      | RBS_Err m => mo_ret MOps (RB_Err m p)
      | RBS_Ok => rb_tail (pc_rfile p)
                    (if pc_swapped p then bswap32 (get_le32 bh 0) else get_le32 bh 0)
                    (if pc_swapped p then bswap32 (get_le32 bh 4) else get_le32 bh 4) p
      end).
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Open Scope bv_scope.

  Definition read_block_proof__stmt : Prop := read_block_stmt HO K sites.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R st C1 C2 FB f Af P B CUR EB lo p s i a_bhdr bs ej ccs : ltac2:(SecDiet.SzSec.tyM 'read_block_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma read_block_proof__body : ltac2:(SecDiet.SzSec.bodyP 'read_block_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FERROR FMT FREAD HAL HFL HPL REALLOC SFL SNPRINTF. pin_using (fun (FERROR FMT FREAD HAL HFL HPL REALLOC SFL SNPRINTF : unit) => tt).
 intros PRE HinF RF HS HinP HBH -> -> -> -> HH HBUF PFX LENB HCUR Hccs CUR1 CUR2 CUR8 HEB EBR EB8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    destruct (rw_cells_forget _ _ _ _ HCUR) as [cj HCUR']. clear HCUR. rewrite Hccs in HCUR'. rename HCUR' into HCUR.
    destruct HH as (HBS & HPV & HMB & WBS & WMB & WBA & BSA).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. unfold rc_lo in LO. unfold READ_BLOCK_STACK, PCAP_L1_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & _).
    cbn [cb_addr cb_size fst snd] in A1, A4. unfold FILE_BLOCK in A4.
    (* [comment removed for export] *)
    assert (HinP' : In (pc_self p, P, PCAP_NG_SF_TOTAL) ((C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) ++ FB)).
    { apply in_or_app. left. apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; right; exact X]. }
    assert (HinB' : In (pc_buffer p, B, pc_bufalloc p) ((C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) ++ FB)).
    { apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
    pose proof (GIo_block_ok K _ _ _ _ _ _ G HinP') as (P1 & P2 & P3 & P4 & _). cbn [cb_addr cb_size fst snd] in P1, P2, P3, P4. unfold PCAP_NG_SF_TOTAL in P4.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G HinB') as (B1 & B2 & B3 & B4 & _). cbn [cb_addr cb_size fst snd] in B1, B2, B3, B4.
    assert (APB : (P + 680 <= B \/ B + pc_bufalloc p <= P)%Z).
    { pose proof (mid_apart K _ _ _ _ _ _ _ _ G HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
    assert (CLB : forall a, in_block (C1 ++ C2) a -> (a < CEILZ)%Z).
    { intros a Ha. apply in_block_app in Ha. destruct (GIo_CLc_facts K R st (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) [] FB m a ltac:(rewrite app_nil_r; exact G)) as [Hc _]; [| lia].
      apply in_block_app. destruct Ha as [Ha|Ha]; [left; exact Ha| right; right; exact Ha]. }
    (* [comment removed for export] *)
    assert (EBX : ((bv_unsigned sp <= EB /\ EB + 256 <= rc_spmain R /\ (EB + 256 <= CUR \/ CUR + 24 <= EB)) \/ (EB = P + 216))%Z) by (destruct EBR as [X|X]; [left| right]; lia).
    clear EBR.
    assert (CRE : client_range R (C1 ++ C2) (bv_unsigned sp) EB 256).
    { destruct EBX as [X| ->]; [right; lia| left]. intros a Ha. apply in_block_In. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (EBiv : client_iv R (C1 ++ C2) (EB, (EB + 256)%Z)).
    { destruct EBX as [X| ->]; [left; cbn [fst snd]; unfold rc_lo; lia| right]. unfold iv_in_block. apply Exists_exists. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    (* [comment removed for export] *)
    rewrite (read_block_eq a_bhdr p). unfold read_bytes, errmsg_for_errno. rewrite RF. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims].
    unfold READ_BLOCK_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide HEB. hide HBUF. hide HCUR. hide HBS. hide HMB. unfold PCAP_PRIV_OFF in HPV.
    pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47.
    assert (P8 : (P mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r P); apply aligned16_8; [exact P2| reflexivity]).
    pose proof (aligned16_8 P 648 P2 eq_refl) as P648.
    ienter. carve_frame 96%nat ST. do 13 step.
    (* [comment removed for export] *)
    step. rewrite (and7_aligned P) by (clear - P1 P4 P8; lia). step. if_false.
    do 10 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIo K R st (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB mm)
        by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp - 96, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho])
    end.
    clear MU WM.
    assert (T0 : forall A cs, rw_cells usegs m A cs -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp - 96 \/ bv_unsigned sp <= A)%Z -> rw_cells usegs m0 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AG0 | exact HC | intros a Ha; cbn [outside]; lia]. }
    unhide HEB. unhide HBUF. unhide HCUR. unhide HBS. unhide HMB.
    apply T0 in HEB; [|cbn [cells_size csize Nat.add]; destruct EBX as [X| ->]; lia].
    apply T0 in HBUF; [|cbn [cells_size csize Nat.add]; lia].
    apply T0 in HCUR; [|cbn [cells_size csize Nat.add]; lia]. apply T0 in HBS; [|cbn [cells_size csize Nat.add]; lia].
    apply T0 in HMB; [|cbn [cells_size csize Nat.add]; lia].
    assert (AGa : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m0).
    { eapply agrees_on_weaken; [exact AG0|]. intros a [[Ha|Ha] _]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]. }
    clear AG0 T0.
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 1 FR) as [HDR FRS]. clear FR. cbn [firstn skipn cells_size csize Nat.add] in HDR, FRS.
    replace (bv_unsigned sp + -96 + Z.of_nat 8)%Z with (bv_unsigned sp + -88)%Z in FRS by lia.
    (* [comment removed for export] *)
    apply evt_done. apply (implM_bind_assoc usegs). apply (implM_bind_assoc usegs).
    name_sp sp (-96)%Z.
    apply implM_mget. rewrite (HBH st). replace (bv_unsigned sp - 96)%Z with (bv_unsigned sp + -96)%Z by lia.
    eapply (implM_bind usegs).
    { eapply FREAD; [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | exact Esp | reflexivity | reflexivity | reflexivity | lia | exact HDR | right; rewrite Hsp; lia ]. }
    intros got s' ms' PO. cbv beta in PO.
    destruct PO as (av & m2 & junk' & E & OF1 & MI1 & ST1 & AG1 & G1 & -> & GL & GR & HD2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 94600)) with (Z_to_bv 64 94600) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INP : forall a, (P <= a < P + 680)%Z -> in_block (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) a).
    { intros a Ha. assert (X : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2)).
      { apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; right; exact X]. }
      apply in_block_In. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact X|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B <= a < B + pc_bufalloc p)%Z -> in_block (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) a).
    { intros a Ha. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (INPc : forall a, (P <= a < P + 680)%Z -> in_block (C1 ++ C2) a).
    { intros a Ha. apply in_block_In. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    (* [comment removed for export] *)
    transport FRS m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport HCUR m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport HBS m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; apply INP; lia| lia]).
    transport HPV m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; apply INP; lia| lia]).
    transport HMB m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; apply INP; lia| lia]).
    transport HBUF m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; apply INB; lia| lia]).
    transport HEB m2 AG1 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [destruct EBX as [X| ->]; [left; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs a X Ha; lia)| right; apply INP; (keep_hyps CEILV hptr sp R P B CUR p ccs a Ha; lia)]| destruct EBX as [X| ->]; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs a X Ha H K C1 C2 FB s' m2 LO BU P4 G1; lia)]).
    assert (AG02 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_weaken; [exact AG1|]. intros a [[Ha|Ha] _]; [split; [left; lia| lia]|].
      pose proof (CLB a Ha). split; [right; apply in_block_app in Ha as [X|X]; apply in_block_app; [left; exact X| right; right; exact X]| lia]. }
    clear AGa AG1 G0.
    unfold zlength in *.
    (* [comment removed for export] *)
    assert (EXIT : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : word)
                          (m3 : mem) (ps3 : PS) (r : block_result) (rv : Z) (hdr : list cell),
      ps_outfile ps3 = ps_outfile st -> mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells usegs m3 (bv_unsigned sp + -96) hdr -> cells_size hdr = 8%nat ->
      rw_cells usegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      (exists (p' : pcapT) B' bs',
        GIo K R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB m3
        /\ blk_handle p' s P B' m3
        /\ rw_cells usegs m3 B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
        /\ (Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p')%Z
        /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p /\ same_meta p' p
        /\ match r with
           | RB_Ok c p'' => p'' = p' /\ rv = 1%Z /\ rw_cells usegs m3 EB [CB 256 ej]
               /\ (exists cpad, rw_cells usegs m3 CUR [C8 (Z_to_bv 64 (B' + 8)); C8 (Z_to_bv 64 (cur_remaining c)); C4 (Z_to_bv 64 (cur_block_type c)); CB 4 cpad])
               /\ cur_off c = 8%Z /\ (0 <= cur_remaining c)%Z /\ (cur_remaining c + 12 <= pc_bufalloc p')%Z /\ (cur_remaining c + 12 <= 2^30)%Z /\ (0 <= cur_block_type c < 2^32)%Z
               /\ Z.of_nat (length (pc_bufdata p')) = (cur_remaining c + 12)%Z /\ Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p')
           | RB_Eof p'' => p'' = p' /\ rv = 0%Z /\ rw_cells usegs m3 EB [CB 256 ej]
               /\ (exists ccs', rw_cells usegs m3 CUR ccs' /\ cells_size ccs' = 24%nat)
           | RB_Err msg p'' => p'' = p' /\ rv = (-1)%Z
               /\ (exists junk'', rw_cells usegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
               /\ (Z.of_nat (length msg) < 256)%Z /\ Forall (fun z => 0 < z < 256)%Z msg
               /\ (exists ccs', rw_cells usegs m3 CUR ccs' /\ cells_size ccs' = 24%nat)
           end) ->
      evt usegs (POSTQ r ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' y0 y1 (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7'
                 y2 y3 y4 y5 y6 y7 y8 y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x172a8) fc None m3 (seg_rom usegs))).
    { intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 m3 ps3 r rv hdr OF3 MI3 ST3 AG3 HDR3 Hhdr FRS3 REST.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      destruct (rw_cells_forget _ _ _ _ HDR3) as [hj HDR3']. clear HDR3. rewrite Hhdr in HDR3'.
      pose proof (rw_cells_uncut _ _ _ _ _ HDR3' FRS3 ltac:(cbn; lia)) as FR3. clear HDR3' FRS3. cbn [app] in FR3.
      do 13 step.
      release_frame FR3 ST3 (bv_unsigned sp).
      apply evt_done. subst POSTQ. unfold read_block_post.
      destruct REST as (p' & B' & bs' & G3 & BH3 & BUF3 & PFX3 & LEN3 & E1 & E2 & E3 & E4 & E5 & E6 & RM).
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 rv), mm, p', B', bs' end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [exact OF3|]. split; [assumption|]. split; [assumption|]. split; [exact AG3|]. split; [exact G3|]. split; [exact BH3|]. split; [exact BUF3|]. split; [exact PFX3|].
      split; [exact LEN3|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|].
      destruct r as [p''|msg p''|c p''].
      - destruct RM as (X1 & -> & X3 & X4). split; [exact X1|]. split; [reflexivity|]. split; [exact X3| exact X4].
      - destruct RM as (X1 & -> & X3 & X4 & X4b & X5). split; [exact X1|]. split; [reflexivity|]. split; [exact X3|]. split; [exact X4|]. split; [exact X4b| exact X5].
      - destruct RM as (X1 & -> & X3 & X4 & X5 & X6 & X7 & X7b & X8 & X9 & X10). split; [exact X1|]. split; [reflexivity|]. split; [exact X3|]. split; [exact X4|].
        split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact X7b|]. split; [exact X8|]. split; [exact X9| exact X10]. }
    (* [comment removed for export] *)
    assert (RESTp : forall mX psX, GIo K R psX (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB mX ->
              rw_cells usegs mX (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B)] ->
              rw_cells usegs mX (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
              rw_cells usegs mX (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
              rw_cells usegs mX B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
              GIo K R psX ((pc_buffer p, B, pc_bufalloc p) :: C1 ++ C2) FB mX /\ blk_handle p s P B mX
              /\ rw_cells usegs mX B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p)
              /\ (Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p)%Z
              /\ pc_priv p = pc_priv p /\ pc_rfile p = pc_rfile p /\ pc_self p = pc_self p /\ pc_bufsize p = pc_bufsize p /\ pc_swapped p = pc_swapped p).
    { intros mX psX GX X1 X2 X3 X4. split; [eapply (GIo_perm K HPL); [exact GX| apply Permutation_sym; apply Permutation_middle]|].
      split; [split; [exact X1|]; split; [exact X2|]; split; [exact X3|]; split; [exact WBS|]; split; [exact WMB|]; split; [exact WBA| exact BSA]|].
      split; [exact X4|]. split; [exact PFX|]. split; [exact LENB|]. repeat split; reflexivity. }
    (* [comment removed for export] *)
    assert (SNP : forall (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 a3v a4v : word) (RA : Z)
                         (m3 : mem) (ps3 : PS) (fs : string) (args : list farg) (FMTA : Z) (msg : list Z) (p' : pcapT) (hdr : list cell),
      (RA = 0x172a4 \/ RA = 0x17280)%Z -> ps_outfile ps3 = ps_outfile st ->
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells usegs m3 (bv_unsigned sp + -96) hdr -> cells_size hdr = 8%nat ->
      rw_cells usegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m3 EB [CB 256 ej] ->
      fmt_at m3 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      (forall (CL : list cblk) D dn, Forall2 (farg_word R CL (bv_unsigned sp + -96) D dn m3) args (firstn (length args) [a3v; a4v; a5'])) ->
      Fmt.snprintf 256 fs args = msg -> items_okb (fmt fs) = true -> Forall arg_ok args ->
      (exists B' bs', GIo K R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB m3 /\ blk_handle p' s P B' m3
         /\ rw_cells usegs m3 B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
         /\ (Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p')%Z
         /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p /\ same_meta p' p
         /\ (exists ccs', rw_cells usegs m3 CUR ccs' /\ cells_size ccs' = 24%nat)) ->
      evt usegs (POSTQ (RB_Err msg p') ps3)
        (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 EB) y1 (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3v a4v a5' a6' a7'
                 y2 y3 y4 y5 y6 y7 y8 y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m3 (seg_rom usegs))).
    { intros t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 a3v a4v RA m3 ps3 fs args FMTA msg p' hdr
             HRA OF3 MI3 ST3 AG3 HDR3 Hhdr FRS3 HEB3 FAT FOK ALEN FW EMSG FIT AOK REST.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      destruct REST as (B' & bs' & G3 & BH3 & BUF3 & PFX3 & LEN3 & E1 & E2 & E3 & E4 & E5 & E6 & ccs' & HCUR3 & Hccs').
      pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
      assert (APB' : (P + 680 <= B' \/ B' + pc_bufalloc p' <= P)%Z).
      { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
      name_sp sp (-96)%Z.
      eapply evt_cut.
      { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB lo EB 256%Z FMTA fs args ej);
          [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
          | reflexivity | reflexivity | reflexivity | lia | exact FAT | exact FOK | exact ALEN | rewrite Hsp; apply FW | exact HEB3
          | destruct CRE as [Hb|Hs]; [left; intros a Ha; unfold in_block; apply Exists_cons_tl; exact (Hb a Ha) | right; rewrite Hsp; lia] ]. }
      cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -96 - STDIO_STACK, bv_unsigned sp + -96); (EB, EB + 256)]%Z a) m3 m4)
        by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
      unfold STDIO_STACK in AGS.
      assert (G4 : GIo K R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB m4).
      { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |].
        apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, STDIO_STACK; lia|]. apply Forall_cons; [| apply Forall_nil].
        destruct EBiv as [X|X]; [left; exact X| right]. unfold iv_in_block. apply Exists_cons_tl. exact X. }
      transport HDR3 m4 AGS ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 args p' hdr B' ccs' m4 LO BU P4 EBX Hhdr G4; prs)). transport FRS3 m4 AGS ltac:((keep_hyps CEILV H hptr K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R C1 C2 FB P B CUR EB lo p ccs got ps3 args p' hdr B' ccs' m4 LO BU P4 EBX G4; prs)). transport HCUR3 m4 AGS ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 args p' hdr B' ccs' m4 LO BU CUR1 P4 EBX Hccs' G4; prs)). transport BUF3 m4 AGS ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 args p' hdr B' bs' ccs' m4 LO BU EBX Q4 APB' G4; prs)).
      destruct BH3 as (Y1 & Y2 & Y3 & YR).
      transport Y1 m4 AGS ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 args p' hdr B' ccs' m4 LO BU P4 EBX G4; prs)). transport Y2 m4 AGS ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 args p' hdr B' ccs' m4 LO BU P4 EBX G4; prs)). transport Y3 m4 AGS ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s ccs got ps3 args p' hdr B' ccs' m4 LO BU P4 EBX G4; prs)).
      assert (AG4 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m4).
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] (_ & _ & Hn)]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
      hide HDR3. hide FRS3. hide HCUR3. hide BUF3. hide Y1. hide Y2. hide Y3. hide HEB4.
      destruct HRA as [-> | ->];
        [ replace (ret_pc (Z_to_bv 64 94884)) with (Z_to_bv 64 94884) by (symmetry; apply ret_pc_even; [lia|reflexivity]); step
        | replace (ret_pc (Z_to_bv 64 94848)) with (Z_to_bv 64 94848) by (symmetry; apply ret_pc_even; [lia|reflexivity]); do 2 step ].
      all: unhide HDR3; unhide FRS3; unhide HCUR3; unhide BUF3; unhide Y1; unhide Y2; unhide Y3; unhide HEB4.
      all: eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 ps3 (RB_Err msg p') (-1)%Z hdr);
        [exact OF3 | exact MI4 | exact ST4 | exact AG4 | exact HDR3 | exact Hhdr | exact FRS3 |].
      all: exists p', B', bs'; split; [exact G4|]; split; [exact (conj Y1 (conj Y2 (conj Y3 YR)))|]; split; [exact BUF3|]; split; [exact PFX3|]; split; [exact LEN3|].
      all: split; [exact E1|]; split; [exact E2|]; split; [exact E3|]; split; [exact E4|]; split; [exact E5|]; split; [exact E6|].
      all: cbv beta iota; split; [reflexivity|]; split; [reflexivity|].
      all: pose proof (snprintf_length 256 fs args) as LS; change (Z.to_nat (256 - 1)) with 255%nat in LS; rewrite EMSG in LS, HEB4.
      all: change (Z.to_nat 256) with 256%nat in HEB4.
      all: replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB4 by lia.
      all: split; [exists junk4; exact HEB4|]; split; [lia|]; split; [rewrite <- EMSG; apply snprintf_ok; [exact FIT| exact AOK]|]; exists ccs'; split; [exact HCUR3| exact Hccs']. }
    (* [comment removed for export] *)
    assert (KFMT : forall (ra' t0' t1' t2' a0' a1' a4' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 : word)
                          (m3 : mem) (ps3 : PS) (err : Z) (p' : pcapT) (hdr : list cell),
      ps_outfile ps3 = ps_outfile st -> mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells usegs m3 (bv_unsigned sp + -96) hdr -> cells_size hdr = 8%nat ->
      rw_cells usegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m3 EB [CB 256 ej] ->
      (-2^31 <= err < 2^31)%Z ->
      (exists B' bs', GIo K R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB m3 /\ blk_handle p' s P B' m3
         /\ rw_cells usegs m3 B' [CB (Z.to_nat (pc_bufalloc p')) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
         /\ (Z.of_nat (length (pc_bufdata p')) <= pc_bufalloc p')%Z
         /\ pc_priv p' = pc_priv p /\ pc_rfile p' = pc_rfile p /\ pc_self p' = pc_self p /\ pc_bufsize p' = pc_bufsize p /\ pc_swapped p' = pc_swapped p /\ same_meta p' p
         /\ (exists ccs', rw_cells usegs m3 CUR ccs' /\ cells_size ccs' = 24%nat)) ->
      evt usegs (POSTQ (RB_Err (fmt_errmsg "error reading dump file" [] err) p') ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 EB) y1 a0' a1' (Z_to_bv 64 (s32 err)) (Z_to_bv 64 FMT_ERR_READING) a4' a5' a6' a7'
                 y2 y3 y4 y5 y6 y7 y8 y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x17244) fc None m3 (seg_rom usegs))).
    { intros ra' t0' t1' t2' a0' a1' a4' a5' a6' a7' t3' t4' t5' t6' y1 y2 y3 y4 y5 y6 y7 y8 y9 m3 ps3 err p' hdr
             OF3 MI3 ST3 AG3 HDR3 Hhdr FRS3 HEB3 ERR REST.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      destruct REST as (B' & bs' & G3 & BH3 & BUF3 & PFX3 & LEN3 & E1 & E2 & E3 & E4 & E5 & E6 & ccs' & HCUR3 & Hccs').
      pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
      assert (APB' : (P + 680 <= B' \/ B' + pc_bufalloc p' <= P)%Z).
      { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
      assert (INB' : forall a, (B' <= a < B' + pc_bufalloc p')%Z -> in_block ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) a).
      { intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (INP' : forall a, (P <= a < P + 680)%Z -> in_block ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) a).
      { intros a Ha. unfold in_block. apply Exists_cons_tl. apply Exists_exists. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
      assert (MSG : fmt_at m3 FMT_ERR_READING "error reading dump file"%string)
        by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_ERR_READING; lia| unfold FMT_ERR_READING; cbn; lia]).
      hide HDR3. hide FRS3. hide HCUR3. hide BUF3. hide BH3. hide HEB3.
      do 3 step. unhide HEB3.
      name_sp sp (-96)%Z.
      eapply evt_cut.
      { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps3 ((pc_buffer p', B', pc_bufalloc p') :: C1 ++ C2) FB lo EB FMT_ERR_READING err "error reading dump file"%string [] ej);
          [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB3
           | destruct CRE as [Hb|Hs]; [left; intros a Ha; unfold in_block; apply Exists_cons_tl; exact (Hb a Ha) | right; rewrite Hsp; lia] | exact EB8 ].
        split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      cbv beta. intros ms' PO. destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m4 & junk4 & -> & MI4 & ST4 & AG4 & G4 & HEB4).
      rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 94800)) with (Z_to_bv 64 94800) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide HDR3. unhide FRS3. unhide HCUR3. unhide BUF3. unhide BH3.
      transport HDR3 m4 AG4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 p' hdr B' ccs' m4 LO BU P4 EBX Hhdr G4; prs)). transport FRS3 m4 AG4 ltac:((keep_hyps CEILV H hptr K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R C1 C2 FB P B CUR EB lo p ccs got ps3 p' hdr B' ccs' m4 LO BU P4 EBX G4; prs)). transport HCUR3 m4 AG4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 p' hdr B' ccs' m4 LO BU CUR1 P4 EBX Hccs' G4; prs)). transport BUF3 m4 AG4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 p' hdr B' bs' ccs' m4 LO BU EBX Q4 APB' INB' G4; prs)).
      destruct BH3 as (Y1 & Y2 & Y3 & YR).
      transport Y1 m4 AG4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 p' hdr B' ccs' m4 LO BU P4 EBX INP' G4; prs)). transport Y2 m4 AG4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got ps3 p' hdr B' ccs' m4 LO BU P4 EBX INP' G4; prs)). transport Y3 m4 AG4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s ccs got ps3 p' hdr B' ccs' m4 LO BU P4 EBX INP' G4; prs)).
      hide HDR3. hide FRS3. hide HCUR3. hide BUF3. hide Y1. hide Y2. hide Y3. hide HEB4.
      do 2 step.
      unhide HDR3. unhide FRS3. unhide HCUR3. unhide BUF3. unhide Y1. unhide Y2. unhide Y3. unhide HEB4.
      eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 ps3 (RB_Err _ p') (-1)%Z hdr);
        [exact OF3 | exact MI4 | exact ST4 | | exact HDR3 | exact Hhdr | exact FRS3 |].
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AG4|]. intros a [[Ha|Ha] (_ & _ & Hn)]; (split; [|exact Hn]); [left; lia| right].
        unfold in_block. apply Exists_cons_tl. exact Ha. }
      exists p', B', bs'. split; [exact G4|]. split; [exact (conj Y1 (conj Y2 (conj Y3 YR)))|]. split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LEN3|].
      split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|].
      cbv beta iota. split; [reflexivity|]. split; [reflexivity|].
      split; [exists junk4; exact HEB4|]. split; [pose proof (fmt_errmsg_length "error reading dump file"%string [] err); lia|].
      split; [apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor]|].
      exists ccs'. split; [exact HCUR3| exact Hccs']. }
    (* [comment removed for export] *)
    assert (KBODY : forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' y5 y6 y7 y8 y9 : word)
                           (m3 : mem) (ps3 : PS) (p0 : pcapT) (B0 : Z) (bs0 : list byte) (bt tl : Z),
      ps_outfile ps3 = ps_outfile st -> (0 <= bt < 2^32)%Z -> (12 <= tl <= 2^30)%Z -> (tl mod 4 = 0)%Z ->
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells usegs m3 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
      rw_cells usegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      GIo K R ps3 ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB m3 ->
      rw_cells usegs m3 (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B0)] ->
      rw_cells usegs m3 (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells usegs m3 (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
      rw_cells usegs m3 B0 [CB (Z.to_nat (pc_bufalloc p0)) bs0] ->
      firstn (length (pc_bufdata p0)) bs0 = map b8 (pc_bufdata p0) -> (Z.of_nat (length (pc_bufdata p0)) <= pc_bufalloc p0)%Z ->
      (tl <= pc_bufalloc p0)%Z -> (pc_bufalloc p0 < 2^32)%Z -> (pc_bufsize p0 <= pc_bufalloc p0)%Z ->
      pc_priv p0 = pc_priv p -> pc_rfile p0 = pc_rfile p -> pc_self p0 = pc_self p -> pc_bufsize p0 = pc_bufsize p -> pc_swapped p0 = pc_swapped p -> same_meta p0 p ->
      rw_cells usegs m3 CUR [CB 24 cj] -> rw_cells usegs m3 EB [CB 256 ej] ->
      implM usegs (rb_body f bt tl p0) ps3 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 CUR) a0' a1' a2' (Z_to_bv 64 (s32 tl)) a4' a5' a6' a7'
                 (Z_to_bv 64 P) (Z_to_bv 64 Af) (Z_to_bv 64 tl) y5 y6 y7 y8 y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x17330) fc None m3 (seg_rom usegs))).
    { intros ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' y5 y6 y7 y8 y9 m3 ps3 p0 B0 bs0 bt tl
             OF3 BT TL M4 MI3 ST3 AG3 HDR3 FRS3 G3 HBS3 HPV3 HMB3 HBUF3 PFX0 LEN0 TLB BA0 BSA0 E1 E2 E3 E4 E5 E6 HCUR3 HEB3.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      pose proof (GIo_block_ok K _ _ _ _ _ _ G3 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
      assert (APB0 : (P + 680 <= B0 \/ B0 + pc_bufalloc p0 <= P)%Z).
      { pose proof (head_apart K _ _ _ _ _ _ _ G3 HinP) as AP. cbn [cb_addr cb_size fst snd] in AP. unfold PCAP_NG_SF_TOTAL in AP. lia. }
      assert (INB0 : forall a, (B0 <= a < B0 + pc_bufalloc p0)%Z -> in_block ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) a).
      { intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (INP0 : forall a, (P <= a < P + 680)%Z -> in_block ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) a).
      { intros a Ha. unfold in_block. apply Exists_cons_tl. apply Exists_exists. exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP|]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
      assert (CLB0 : forall a, in_block (C1 ++ C2) a -> ~ (B0 <= a < B0 + pc_bufalloc p0)%Z).
      { intros a Ha Hr'. destruct (proj1 (in_block_In _ _) Ha) as (b' & Hin & Hr). pose proof (head_apart K _ _ _ _ _ _ _ G3 Hin) as AP. cbn [cb_addr cb_size fst snd] in AP, Hr. lia. }
      assert (LB0 : length bs0 = Z.to_nat (pc_bufalloc p0)) by (destruct HBUF3 as [[WF _] _]; cbn in WF; lia).
      (* [comment removed for export] *)
      pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [8%nat; (Z.to_nat (pc_bufalloc p0) - 8)%nat] HBUF3 ltac:(cbn; lia)) as HB'. clear HBUF3.
      cbn [mk_CB_cells app] in HB'.
      destruct (rw_cells_cut _ _ _ 1 HB') as [HB8 HBT]. clear HB'. cbn [firstn skipn cells_size csize Nat.add] in HB8, HBT.
      lazymatch type of HBT with rw_cells _ _ ?A _ => replace A with (B0 + 8)%Z in HBT by lia end.
      (* [comment removed for export] *)
      set (V := (bt + 4294967296 * tl)%Z).
      assert (HV : (0 <= V < 2^64)%Z) by (subst V; lia).
      assert (HDR8 : rw_cells usegs m3 (bv_unsigned sp + -96) [C8 (Z_to_bv 64 V)]).
      { eapply rw_cells_recell; [exact HDR3 | cbn; repeat split; try exact Logic.I |].
        cbn [cells_bytes cbytes app]. subst V. rewrite le8_two by lia. rewrite !le4_le_bytes by lia. rewrite map_app, !app_nil_r. reflexivity. }
      clear HDR3.
      unfold rb_body, read_bytes, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims pc_buffer pc_bufdata pc_swapped set_bufdata].
      unfold implM. iprefix.
      hide FRS3. hide HPV3. hide HMB3. hide HBT. hide HCUR3. hide HEB3.
      do 3 step.   (* [comment removed for export] *)
      hide HBS3. hide HDR8.
      eapply evt_cut.
      { eapply (hdr_copy_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V B0);
          [exact MI3 | exact HV | lia | lia | exact HB8]. }
      cbv beta. intros ms' PO. destruct PO as (z1 & z2 & z3 & z4 & z5 & z6 & m4 & -> & MU4 & WM4 & MI4 & HB84). clear HB8.
      assert (AGS4 : agrees_on (fun a => outside [(B0, B0 + 8)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
      unhide FRS3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HBT. unhide HCUR3. unhide HEB3. unhide HDR8.
      transport HDR8 m4 AGS4 ltac:(prs). rename HDR8 into HDR4.
      transport FRS3 m4 AGS4 ltac:(prs). transport HBS3 m4 AGS4 ltac:(prs). transport HPV3 m4 AGS4 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl TL TLB APB0; prs)). transport HMB3 m4 AGS4 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p s ccs got p0 B0 bs0 bt tl TL TLB APB0; prs)).
      transport HBT m4 AGS4 ltac:(prs). transport HCUR3 m4 AGS4 ltac:(prs). transport HEB3 m4 AGS4 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ej ccs got m3 ps3 p0 B0 bs0 bt tl LO BU EBX TL G3 TLB Q4 APB0; prs)).
      assert (G4 : GIo K R ps3 ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB m4).
      { eapply (GIo_client_frame K HFL SFL); [exact G3 | exact MU4 | exact WM4 |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (ST4 : stk usegs m4 lo (bv_unsigned sp + -96)).
      { eapply stk_transport_disjoint; [exact ST3 | exact MU4 | exact WM4 | cbn [disjoint_from]; unfold rc_lo in *; lia]. }
      assert (AG4 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m4).
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS4|]. intros a [[Ha|Ha] _]; cbn [outside]; (split; [| exact Logic.I]); [lia|]. exact (CLB0 a Ha ltac:(fail)) || (pose proof (CLB0 a Ha); (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl a TL TLB H0; lia)). }
      clear AGS4 MI3 ST3 G3 AG3.
      subst V. rewrite le8_two in HB84 by (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl BT TL; lia).
      (* [comment removed for export] *)
      hide FRS3. hide HPV3. hide HMB3. hide HBT. hide HCUR3. hide HEB3. hide HB84. hide HDR4.
      do 3 step. step. if_false_by (geu_lits_false 8 (B0 + 8) ltac:(clear - Q1; lia) ltac:(clear - Q3 Q4; lia)).
      do 6 step.
      unhide FRS3. unhide HPV3. unhide HMB3. unhide HBT. unhide HCUR3. unhide HEB3. unhide HB84. unhide HDR4.
      apply evt_done. apply (implM_bind_assoc usegs). apply (implM_bind_assoc usegs). apply implM_mget. cbn [eval_rdest fo_site fo_nop]. unfold blk_addr.
      rewrite (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G4 ltac:(apply in_or_app; left; left; reflexivity)).
      pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat (tl - 8); (Z.to_nat (pc_bufalloc p0) - 8 - Z.to_nat (tl - 8))%nat] HBT ltac:(cbn; lia)) as HB'. clear HBT.
      cbn [mk_CB_cells app] in HB'.
      destruct (rw_cells_cut _ _ _ 1 HB') as [HDST HREST]. clear HB'. cbn [firstn skipn cells_size csize Nat.add] in HDST, HREST.
      lazymatch type of HREST with rw_cells _ _ ?A _ => replace A with (B0 + tl)%Z in HREST by lia end.
      name_sp sp (-96)%Z.
      eapply (implM_bind usegs).
      { eapply FREAD; [ split; [exact G4|]; split; [rewrite Hsp; exact ST4|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                        split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                      | exact HinF | reflexivity | reflexivity | f_equal; lia | reflexivity | lia | exact HDST | left; intros a Ha; apply INB0; lia ]. }
      intros got2 ps5 ms5 PO. cbv beta in PO.
      destruct PO as (av & m5 & junk5 & E & OF5 & MI5 & ST5 & AG5 & G5 & -> & GL2 & GR2 & HD5).
      unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 95136)) with (Z_to_bv 64 95136) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      transport FRS3 m5 AG5 ltac:(prs). transport HDR4 m5 AG5 ltac:(prs). transport HCUR3 m5 AG5 ltac:(prs). transport HBS3 m5 AG5 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 tl TLB APB0 INP0; prs)).
      transport HPV3 m5 AG5 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 tl TLB APB0 INP0; prs)). transport HMB3 m5 AG5 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p s ccs got p0 B0 bs0 tl TLB APB0 INP0; prs)). transport HEB3 m5 AG5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ej ccs got p0 B0 bs0 tl ps5 m5 LO BU EBX TLB Q4 APB0 INP0 G5; prs)). transport HB84 m5 AG5 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 bt tl TL TLB INB0; prs)).
      transport HREST m5 AG5 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 tl TL INB0; prs)).
      assert (AG5' : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m5).
      { eapply agrees_on_trans; [exact AG4|]. eapply agrees_on_weaken; [exact AG5|]. intros a [[Ha|Ha] _]; [split; [left; lia| lia]|].
        pose proof (CLB0 a Ha). split; [right; unfold in_block; apply Exists_cons_tl; exact Ha| (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 tl a TLB H0; lia)]. }
      clear AG5 MU4 WM4 MI4 ST4 G4 AG4.
      unfold zlength in *.
      pose proof (rw_cells_bound _ _ _ _ HREST) as BREST. cbn [cells_size csize Nat.add] in BREST.
      (* [comment removed for export] *)
      assert (RESTd : forall (mX : mem) (psX : PS) (d : list Z) (bsX : list byte) (ccsX : list cell),
                GIo K R psX ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB mX ->
                rw_cells usegs mX (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B0)] ->
                rw_cells usegs mX (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
                rw_cells usegs mX (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
                rw_cells usegs mX B0 [CB (Z.to_nat (pc_bufalloc p0)) bsX] ->
                firstn (length d) bsX = map b8 d -> (Z.of_nat (length d) <= pc_bufalloc p0)%Z ->
                rw_cells usegs mX CUR ccsX -> cells_size ccsX = 24%nat ->
                exists bs', GIo K R psX ((pc_buffer (set_bufdata d p0), B0, pc_bufalloc (set_bufdata d p0)) :: C1 ++ C2) FB mX
                  /\ blk_handle (set_bufdata d p0) s P B0 mX
                  /\ rw_cells usegs mX B0 [CB (Z.to_nat (pc_bufalloc (set_bufdata d p0))) bs']
                  /\ firstn (length (pc_bufdata (set_bufdata d p0))) bs' = map b8 (pc_bufdata (set_bufdata d p0))
                  /\ (Z.of_nat (length (pc_bufdata (set_bufdata d p0))) <= pc_bufalloc (set_bufdata d p0))%Z
                  /\ pc_priv (set_bufdata d p0) = pc_priv p /\ pc_rfile (set_bufdata d p0) = pc_rfile p /\ pc_self (set_bufdata d p0) = pc_self p
                  /\ pc_bufsize (set_bufdata d p0) = pc_bufsize p /\ pc_swapped (set_bufdata d p0) = pc_swapped p /\ same_meta (set_bufdata d p0) p
                  /\ (exists ccs', rw_cells usegs mX CUR ccs' /\ cells_size ccs' = 24%nat)).
      { intros mX psX d bsX ccsX GX X1 X2 X3 X4 PF LE XC XS. exists bsX. unfold blk_handle. cbn [pc_buffer pc_bufalloc pc_bufdata pc_priv pc_rfile pc_self pc_bufsize pc_swapped set_bufdata].
        split; [exact GX|]. split; [split; [rewrite E4; exact X1|]; split; [rewrite E5; exact X2|]; split; [exact X3|]; rewrite E4; split; [exact WBS|]; split; [exact WMB|]; lia|].
        split; [exact X4|]. split; [exact PF|]. split; [exact LE|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|].
        exists ccsX. split; [exact XC| exact XS]. }
      assert (L8h : length (map b8 (le_bytes 4 bt ++ le_bytes 4 tl)) = 8%nat) by (rewrite length_map, length_app, !length_le_bytes; reflexivity).
      assert (GRh : Forall (fun z => 0 <= z < 256)%Z (le_bytes 4 bt ++ le_bytes 4 tl)) by (apply Forall_app; split; apply le_bytes_4_range).
      destruct (Z.eq_dec (Z.of_nat (length got2)) (tl - 8)) as [LF|LF].
      2:{ (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq _ _) LF). cbn [negb andb]. rewrite Bool.andb_false_r. apply (implM_bind_assoc usegs).
        hide FRS3. hide HDR4. hide HCUR3. hide HBS3. hide HPV3. hide HMB3. hide HEB3. hide HB84. hide HREST. hide HD5.
        unfold implM. iprefix. step. rewrite (eqb_lits_false (Z.of_nat (length got2)) (tl + -8) ltac:((keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got2 TL GL2; lia)) ltac:((keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got2 TL; lia)) ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got2 LF; lia))). change (negb false) with true. cbv iota. do 3 step.
        unhide FRS3. unhide HDR4. unhide HCUR3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HEB3. unhide HB84. unhide HREST. unhide HD5.
        name_sp sp (-96)%Z.
        apply evt_done. eapply (implM_bind usegs).
        { eapply FERROR; [| exact HinF | reflexivity].
          split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
          split; [rewrite Hsp; (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got2 SPM; lia)|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
        intros e ps6 ms6 PO. cbv beta in PO. destruct PO as (av6 & m6 & E & MI6 & ST6 & AG6 & G6 & -> & -> & ERRNO).
        unfold hpost_regs in E. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 95252)) with (Z_to_bv 64 95252) by (symmetry; apply ret_pc_even; [(keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got2; lia)|reflexivity]).
        transport FRS3 m6 AG6 ltac:(prs). transport HDR4 m6 AG6 ltac:(prs). transport HCUR3 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs cj got p0 B0 bs0 bt tl got2 CUR1; prs)). transport HBS3 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p ccs got p0 B0 bs0 bt tl got2 INP0; prs)).
        transport HPV3 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p ccs got p0 B0 bs0 bt tl got2 INP0; prs)). transport HMB3 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p s ccs got p0 B0 bs0 bt tl got2 INP0; prs)). transport HEB3 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ej ccs got p0 B0 bs0 bt tl got2 EBX INP0; prs)). transport HB84 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 bt tl got2 TL TLB INB0; prs)).
        transport HREST m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 bt tl got2 TL INB0; prs)). transport HD5 m6 AG6 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ccs got p0 B0 bs0 bt tl got2 junk5 TLB INB0 GL2; prs)).
        assert (AG6' : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right]. unfold in_block. apply Exists_cons_tl. exact Ha. }
        clear AG6 MI5 ST5 G5.
        (* [comment removed for export] *)
        pose proof HB84 as HBUF6. join_cells HBUF6 HD5. join_cells HBUF6 HREST. merge_all HBUF6.
        lazymatch type of HBUF6 with rw_cells _ _ _ [CB ?n _] => replace n with (Z.to_nat (pc_bufalloc p0)) in HBUF6 by lia end.
        assert (PFX6 : forall junkX restX, firstn (length ((le_bytes 4 bt ++ le_bytes 4 tl) ++ got2)) (map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got2 ++ junkX ++ restX)
                                            = map b8 ((le_bytes 4 bt ++ le_bytes 4 tl) ++ got2)).
        { intros junkX restX. rewrite (map_app b8 (le_bytes 4 bt ++ le_bytes 4 tl) got2).
          replace (map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got2 ++ junkX ++ restX) with ((map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got2) ++ (junkX ++ restX)) by (rewrite <- !app_assoc; reflexivity).
          apply firstn_len_app'. rewrite !length_app, !length_map. reflexivity. }
        destruct e.
        - (* [comment removed for export] *)
          cbv iota. destruct (ERRNO eq_refl) as [EN2 EB2]. clear ERRNO. unfold utp in EN2. rewrite <- TP in EN2.
          eapply implM_pure; [reflexivity|]. cbn [fst snd].
          set (err := lc_errno (ps_libc ps5)) in *.
          hide FRS3. hide HDR4. hide HCUR3. hide HBS3. hide HPV3. hide HMB3. hide HEB3. hide HBUF6.
          cbn [Z.b2z]. step. if_false. do 4 step.
          replace (ret_pc (Z_to_bv 64 95260)) with (Z_to_bv 64 95260) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
          (* [comment removed for export] *)
          pose proof (GIo_tls K _ _ _ _ _ G6) as [_ TB]. unfold tls_block_ok_u, utp in TB. rewrite <- TP in TB.
          assert (T4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
          { destruct TB as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * 4 + 9)%Z. lia. }
          step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(clear - TB; lia)).
          step. rewrite (and3_aligned (bv_unsigned tp + -164)) by (clear - TB T4; lia). step. if_false.
          do 4 step.
          replace (sx32 (Z_to_bv 64 err)) with (Z_to_bv 64 (s32 err)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
          unhide FRS3. unhide HDR4. unhide HCUR3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HEB3. unhide HBUF6.
          eapply (KFMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps5 err); [exact (eq_trans OF5 OF3) | exact MI6 | exact ST6 | exact AG6' | exact HDR4 | reflexivity | exact FRS3 | exact HEB3 | lia |].
          exists B0. eapply RESTd; [exact G6 | exact HBS3 | exact HPV3 | exact HMB3 | exact HBUF6 | apply PFX6 | rewrite length_app, <- (length_map b8), L8h; lia | exact HCUR3 | reflexivity].
        - (* [comment removed for export] *)
          cbv iota. clear ERRNO. apply (implM_retb usegs). cbv beta iota. apply (implM_ret usegs).
          hide FRS3. hide HDR4. hide HCUR3. hide HBS3. hide HPV3. hide HMB3. hide HEB3. hide HBUF6.
          cbn [Z.b2z]. step. if_true. do 8 step.
          unhide FRS3. unhide HDR4. unhide HCUR3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HEB3. unhide HBUF6.
          replace (tl + -8)%Z with (tl - 8)%Z by lia.
          assert (MSG : fmt_at m6 FMT_TRUNC_PCAPNG "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
            by (apply (fmt_at_intro m6 _ _ MI6); [vm_compute; reflexivity| unfold FMT_TRUNC_PCAPNG; lia| unfold FMT_TRUNC_PCAPNG; cbn; lia]).
          eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps5 _ [AInt (tl - 8); AInt (Z.of_nat (length got2))] FMT_TRUNC_PCAPNG);
            [left; reflexivity | exact (eq_trans OF5 OF3) | exact MI6 | exact ST6 | exact AG6' | exact HDR4 | reflexivity | exact FRS3 | exact HEB3 | exact MSG | reflexivity | cbn; lia
            | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] | unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE; reflexivity
            | vm_compute; reflexivity | apply args_ok_ints2 |].
          exists B0. eapply RESTd; [exact G6 | exact HBS3 | exact HPV3 | exact HMB3 | exact HBUF6 | apply PFX6 | rewrite length_app, <- (length_map b8), L8h; lia | exact HCUR3 | reflexivity].
      }
      (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LF). cbn [negb]. apply (implM_retb usegs). cbv beta iota.
      rewrite E5.
      destruct (lastn4 got2 ltac:(lia)) as (got1 & u0 & u1 & u2 & u3 & EG & LG1). rewrite EG in GR2. subst got2.
      apply Forall_app in GR2 as [GR1 GU].
      apply Forall_cons_iff in GU as [U0 GU]. apply Forall_cons_iff in GU as [U1 GU]. apply Forall_cons_iff in GU as [U2 GU]. apply Forall_cons_iff in GU as [U3 _].
      rewrite length_app in LF, LG1, HD5. cbn [length] in LF, LG1, HD5.
      (* [comment removed for export] *)
      destruct (rw_cells_cut _ _ _ 1 HD5) as [HD6 _]. clear HD5. cbn [firstn] in HD6.
      rewrite map_app in HD6.
      pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [length got1; 4%nat] HD6 ltac:(cbn; lia)) as HD7. clear HD6. cbn [mk_CB_cells app] in HD7.
      rewrite (firstn_len_app' (map b8 got1)) in HD7 by (symmetry; apply length_map).
      replace (skipn (length got1) (map b8 got1 ++ map b8 [u0; u1; u2; u3])) with (map b8 [u0; u1; u2; u3]) in HD7
        by (rewrite <- (length_map b8 got1) at 1; symmetry; apply skipn_len_app).
      cbn [map firstn] in HD7.
      destruct (rw_cells_cut _ _ _ 1 HD7) as [HG1 HT]. clear HD7. cbn [firstn skipn cells_size csize Nat.add] in HG1, HT.
      lazymatch type of HT with rw_cells _ _ ?A _ => replace A with (B0 + tl + -4)%Z in HT by lia end.
      assert (HT' : rw_cells usegs m5 (B0 + tl + -4) [C4 (Z_to_bv 64 (le4val u0 u1 u2 u3))]).
      { eapply rw_cells_recell; [exact HT | cbn; repeat split; try exact Logic.I |]. cbn [cells_bytes cbytes app]. rewrite (le4_lit u0 u1 u2 u3) by (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U0 U1 U2 U3; lia). reflexivity. }
      clear HT.
      (* [comment removed for export] *)
      assert (K1C : forall (rav t0v t1v t2v a1v a2v a4v a5v a6v a7v t3v t4v t5v t6v : word) (m6 : mem) (w0 w1 w2 w3 : Z) (d3 : list Z),
        (0 <= w0 < 256)%Z -> (0 <= w1 < 256)%Z -> (0 <= w2 < 256)%Z -> (0 <= w3 < 256)%Z ->
        d3 = (le_bytes 4 bt ++ le_bytes 4 tl) ++ got1 ++ [w0; w1; w2; w3] ->
        mem_inv usegs m6 -> stk usegs m6 lo (bv_unsigned sp + -96) ->
        agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m6 ->
        rw_cells usegs m6 (bv_unsigned sp + -96) [C8 (Z_to_bv 64 (bt + 4294967296 * tl))] ->
        rw_cells usegs m6 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        GIo K R ps5 ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB m6 ->
        rw_cells usegs m6 (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B0)] ->
        rw_cells usegs m6 (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
        rw_cells usegs m6 (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
        rw_cells usegs m6 B0 [CB 8 (map b8 (le_bytes 4 bt ++ le_bytes 4 tl))] ->
        rw_cells usegs m6 (B0 + 8) [CB (length got1) (map b8 got1)] ->
        rw_cells usegs m6 (B0 + tl + -4) [C4 (Z_to_bv 64 (le4val w0 w1 w2 w3))] ->
        rw_cells usegs m6 (B0 + tl) [CB (Z.to_nat (pc_bufalloc p0) - 8 - Z.to_nat (tl - 8)) (firstn (Z.to_nat (pc_bufalloc p0) - 8 - Z.to_nat (tl - 8)) (skipn (Z.to_nat (tl - 8)) (firstn (Z.to_nat (pc_bufalloc p0) - 8) (skipn 8 bs0))))] ->
        rw_cells usegs m6 CUR [CB 24 cj] -> rw_cells usegs m6 EB [CB 256 ej] ->
        implM usegs (if negb (tl =? get_le32 d3 (tl - 4))
                     then mo_ret MOps (RB_Err (Msg.header_trailer_mismatch tl (get_le32 d3 (tl - 4))) (set_bufdata d3 p0))
                     else mo_ret MOps (RB_Ok (mkCursor 8 (tl - 12) bt) (set_bufdata d3 p0))) ps5 POSTQ
          (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0v t1v t2v (Z_to_bv 64 EB) (Z_to_bv 64 CUR) (Z_to_bv 64 (B0 + tl + -4)) a1v a2v (Z_to_bv 64 (s32 tl)) a4v a5v a6v a7v
                   (Z_to_bv 64 P) (Z_to_bv 64 Af) (Z_to_bv 64 tl) (Z_to_bv 64 (B0 + 8)) (Z_to_bv 64 (tl + -8)) (Z_to_bv 64 (bt + 4294967296 * tl)) (Z_to_bv 64 (s32 tl)) (Z_to_bv 64 B0) s10 s11 t3v t4v t5v t6v)
              F (Z_to_bv 64 0x17458) fc None m6 (seg_rom usegs))).
      { intros rav t0v t1v t2v a1v a2v a4v a5v a6v a7v t3v t4v t5v t6v m6 w0 w1 w2 w3 d3 W0 W1 W2 W3 Ed3 MI6 ST6 AG6 HDR6 FRS6 G6 HBS6 HPV6 HMB6 HB86 HG16 HT6 HREST6 HCUR6 HEB6.
        clear HDR4 FRS3 HBS3 HPV3 HMB3 HB84 HG1 HT' HREST HCUR3 HEB3 MI5 ST5.
        assert (LG1' : Z.of_nat (length got1) = (tl - 12)%Z) by lia.
        assert (TRL : get_le32 d3 (tl - 4) = le4val w0 w1 w2 w3).
        { rewrite Ed3. rewrite (app_assoc (le_bytes 4 bt ++ le_bytes 4 tl) got1 [w0; w1; w2; w3]). apply get_le32_last4. rewrite !length_app, !length_le_bytes. (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 LF; lia). }
        rewrite TRL.
        assert (LD3 : length d3 = Z.to_nat tl) by (rewrite Ed3, !length_app, !length_le_bytes; cbn [length]; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 LF; lia)).
        assert (GD3 : Forall (fun z => 0 <= z < 256)%Z d3).
        { rewrite Ed3. apply Forall_app. split; [exact GRh|]. apply Forall_app. split; [exact GR1|]. repeat constructor; (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 w0 d3 W0 w1 W1 w2 W2 w3 W3; lia). }
        (* [comment removed for export] *)
        assert (HT8 : rw_cells usegs m6 (B0 + tl + -4) [CB 4 (map b8 [w0; w1; w2; w3])]).
        { eapply rw_cells_recell; [exact HT6 | cbn; repeat split; try exact Logic.I |]. cbn [cells_bytes cbytes app map]. rewrite (le4_lit w0 w1 w2 w3) by lia. reflexivity. }
        pose proof HB86 as HBUF7. join_cells HBUF7 HG16. join_cells HBUF7 HT8. join_cells HBUF7 HREST6. merge_all HBUF7.
        lazymatch type of HBUF7 with rw_cells _ _ _ [CB ?n _] => replace n with (Z.to_nat (pc_bufalloc p0)) in HBUF7 by (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 TLB LF; lia) end.
        assert (PFX7 : forall restX, firstn (length d3) (map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got1 ++ [b8 w0; b8 w1; b8 w2; b8 w3] ++ restX) = map b8 d3).
        { intros restX. set (A := map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got1 ++ [b8 w0; b8 w1; b8 w2; b8 w3]).
          assert (EA : map b8 d3 = A) by (subst A; rewrite Ed3, !map_app; reflexivity).
          rewrite EA. replace (length d3) with (length A) by (rewrite <- (length_map b8 d3), EA; reflexivity).
          replace (map b8 (le_bytes 4 bt ++ le_bytes 4 tl) ++ map b8 got1 ++ [b8 w0; b8 w1; b8 w2; b8 w3] ++ restX) with (A ++ restX)
            by (subst A; rewrite <- !app_assoc; reflexivity).
          apply firstn_len_app. }
        destruct (Z.eq_dec tl (le4val w0 w1 w2 w3)) as [TE|TE].
        - (* [comment removed for export] *)
          rewrite <- TE, Z.eqb_refl. cbn [negb]. apply (implM_ret usegs).
          pose proof (munch_refl [(CUR, CUR + 24)]%Z m6) as MU7. pose proof (wmono_refl usegs m6) as WM7.
          hide HDR6. hide FRS6. hide HBS6. hide HPV6. hide HMB6. hide HBUF7. hide HEB6.
          step. rewrite (sx32_s32 (le4val w0 w1 w2 w3)) by (unfold le4val; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 w0 w1 w2 w3 d3 W0 W1 W2 W3; lia)).    (* [comment removed for export] *)
          rewrite <- TE.
          step. replace (bv_eqb (Z_to_bv 64 (s32 tl)) (Z_to_bv 64 (s32 tl))) with true by (symmetry; apply Z.eqb_refl). cbn [negb]. cbv iota.
          (* [comment removed for export] *)
          step. rewrite (and7_aligned CUR) by (clear - CUR1 CUR2 CUR8 RSP SP47; unfold rc_spmain in CUR2; lia). step. if_false.
          do 6 step.
          unhide HDR6. unhide FRS6. unhide HBS6. unhide HPV6. unhide HMB6. unhide HBUF7. unhide HEB6.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            assert (AGS7 : agrees_on (fun a => outside [(CUR, CUR + 24)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]);
            assert (G7 : GIo K R ps5 ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB mm)
              by (eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MU7 | exact WM7 |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil])
          end.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            transport HDR6 mm AGS7 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 CUR1; prs)); transport FRS6 mm AGS7 ltac:((keep_hyps CEILV hptr ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 CUR1; prs)); transport HBS6 mm AGS7 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got p0 B0 bs0 bt tl ps5 got1 u0 u1 u2 u3 d3 m1 LO BU CUR1 P4 G7; prs)); transport HPV6 mm AGS7 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got p0 B0 bs0 bt tl ps5 got1 u0 u1 u2 u3 d3 m1 LO BU CUR1 P4 G7; prs));
            transport HMB6 mm AGS7 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s ccs got p0 B0 bs0 bt tl ps5 got1 u0 u1 u2 u3 d3 m1 LO BU CUR1 P4 G7; prs)); transport HBUF7 mm AGS7 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got p0 B0 bs0 bt tl ps5 got1 u0 u1 u2 u3 w0 w1 w2 w3 d3 m1 LO BU CUR1 SPW Q4; prs)); transport HEB6 mm AGS7 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ej ccs got p0 B0 bs0 bt tl ps5 got1 u0 u1 u2 u3 d3 m1 LO BU CUR1 SPW P4 EBX; prs)) end.
          eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ps5 (RB_Ok _ _) 1%Z); [exact (eq_trans OF5 OF3) | assumption | exact ST6 | | exact HDR6 | reflexivity | exact FRS6 |].
          { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGS7|]. intros a (_ & _ & Hc & _). cbn [outside]. split; [exact Hc| exact Logic.I]. }
          destruct (RESTd _ ps5 d3 _ _ G7 HBS6 HPV6 HMB6 HBUF7 (PFX7 _) ltac:(rewrite LD3; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 TLB LF; lia)) HCUR6 ltac:(reflexivity)) as (bs' & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & _).
          exists (set_bufdata d3 p0), B0, bs'. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
          split; [exact X6|]. split; [exact X7|]. split; [exact X8|]. split; [exact X9|]. split; [exact X10|]. split; [exact X11|].
          cbv beta iota. split; [reflexivity|]. split; [reflexivity|]. split; [exact HEB6|].
          cbn [cur_off cur_remaining cur_block_type pc_bufdata pc_bufalloc set_bufdata].
          split.
          { lazymatch type of HCUR6 with rw_cells _ _ _ [_; _; _; CB 4 ?pad] => exists pad end.
            eapply rw_cells_recell; [exact HCUR6 | pose proof (proj1 (proj1 HCUR6)) as WF; cbn in WF |- *; clear - WF; tauto |].
            cbn [cells_bytes cbytes app]. rewrite (le4_mod32 bt tl) by (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 BT TL; lia). replace (tl + -12)%Z with (tl - 12)%Z by lia. reflexivity. }
          split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite LD3; lia| exact GD3].
        - (* [comment removed for export] *)
          rewrite (proj2 (Z.eqb_neq _ _) TE). cbn [negb]. apply (implM_ret usegs).
          hide HDR6. hide FRS6. hide HBS6. hide HPV6. hide HMB6. hide HBUF7. hide HEB6. hide HCUR6.
          step. rewrite (sx32_s32 (le4val w0 w1 w2 w3)) by (unfold le4val; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 w0 w1 w2 w3 d3 W0 W1 W2 W3; lia)).    (* [comment removed for export] *)
          step. rewrite (eqb_s32 tl (le4val w0 w1 w2 w3)) by (unfold le4val; (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 d3 TL lo w0 w1 w2 w3 W0 W1 W2 W3; lia)). rewrite (proj2 (Z.eqb_neq _ _) TE). cbn [negb]. cbv iota.
          do 7 step.
          unhide HDR6. unhide FRS6. unhide HBS6. unhide HPV6. unhide HMB6. unhide HBUF7. unhide HEB6. unhide HCUR6.
          assert (MSG : fmt_at m6 FMT_BLK_TRAILER "block total length in header %u and trailer %u don't match"%string)
            by (apply (fmt_at_intro m6 _ _ MI6); [vm_compute; reflexivity| unfold FMT_BLK_TRAILER; lia| unfold FMT_BLK_TRAILER; cbn; lia]).
          eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps5 _ [AInt (s32 tl); AInt (s32 (le4val w0 w1 w2 w3))] FMT_BLK_TRAILER);
            [left; reflexivity | exact (eq_trans OF5 OF3) | exact MI6 | exact ST6 | exact AG6 | exact HDR6 | reflexivity | exact FRS6 | exact HEB6 | exact MSG | reflexivity | cbn; lia
            | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
            | unfold Msg.header_trailer_mismatch, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
              replace (convs (fmt "block total length in header %u and trailer %u don't match")) with [Cu; Cu] by (vm_compute; reflexivity);
              apply pargs_cons; [apply aeq_s32; reflexivity|]; apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
            | vm_compute; reflexivity | apply args_ok_ints2 |].
          exists B0. eapply RESTd; [exact G6 | exact HBS6 | exact HPV6 | exact HMB6 | exact HBUF7 | apply PFX7 | rewrite LD3; lia | exact HCUR6 | reflexivity]. }
      (* [comment removed for export] *)
      replace (Z.of_nat (length (got1 ++ [u0; u1; u2; u3]))) with (tl + -8)%Z by (rewrite length_app; cbn [length]; lia).
      destruct (pc_swapped p); cbv iota; rewrite !set_bufdata_twice, !pc_bufdata_set; cbn [Z.b2z] in HPV3.
      - (* [comment removed for export] *)
        rewrite (app_assoc (le_bytes 4 bt ++ le_bytes 4 tl) got1 [u0; u1; u2; u3]).
        rewrite (swap_field_last4 _ u0 u1 u2 u3 tl) by (rewrite !length_app, !length_le_bytes; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 LF; lia)).
        rewrite <- (app_assoc (le_bytes 4 bt ++ le_bytes 4 tl) got1 [u3; u2; u1; u0]).
        unfold implM. iprefix.
        hide HDR4. hide FRS3. hide HCUR3. hide HBS3. hide HMB3. hide HEB3. hide HB84. hide HG1. hide HREST.
        step. rewrite (eqb_lits_eq (tl + -8)%Z (tl + -8)%Z eq_refl). cbn [negb]. cbv iota.
        (* [comment removed for export] *)
        step. rewrite (unsigned_lit (B0 + 8)) by lia. rewrite (lxor_ones64 (B0 + 8)) by lia.
        step. if_false_by (ltu_lits_false (18446744073709551615 - (B0 + 8)) (tl + -8) ltac:(clear - Q1 Q4 TL TLB; lia) ltac:(clear - Q1 Q4 TL TLB; lia)).
        do 2 step. step. if_false_by (ltu_lits_false (B0 + tl) 5 ltac:(clear - Q1 Q4 TL TLB; lia) ltac:(clear - Q1 Q4 TL TLB; lia)).
        (* [comment removed for export] *)
        do 2 step.
        step. rewrite (and3_aligned (B0 + tl + -4)) by (clear - Q1 Q2 Q4 M4 TL TLB; fastfirst (first [ noevar_assumption |lia | Z.div_mod_to_equations; lia])).
        step. step. if_false.
        step. if_false.   (* [comment removed for export] *)
        eapply evt_cut.
        { eapply (trl_swap_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (B0 + tl + -4) u0 u1 u2 u3);
            [exact MI5 | (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 Q1 LF; lia) | (keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ccs got p0 B0 bs0 bt tl ps5 m5 got1 u0 u1 u2 u3 TLB Q4; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U0; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U1; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U2; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U3; lia) | reflexivity | exact HT']. }
        cbv beta. intros ms' PO. destruct PO as (q1 & q2 & q4 & q5 & m6 & -> & MU6 & WM6 & MI6 & HT6). clear HT'.
        assert (AGS6 : agrees_on (fun a => outside [(B0 + tl + -4, B0 + tl + -4 + 4)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
        unhide HDR4. unhide FRS3. unhide HCUR3. unhide HBS3. unhide HMB3. unhide HEB3. unhide HB84. unhide HG1. unhide HREST.
        transport HDR4 m6 AGS6 ltac:(prs). transport FRS3 m6 AGS6 ltac:(prs). transport HCUR3 m6 AGS6 ltac:(prs). transport HBS3 m6 AGS6 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 TLB APB0 LF; prs)).
        transport HPV3 m6 AGS6 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 TLB APB0 LF; prs)). transport HMB3 m6 AGS6 ltac:((keep_hyps CEILV hptr sp R P B CUR EB lo p s ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 TLB APB0 LF; prs)). transport HEB3 m6 AGS6 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ej ccs got p0 B0 bs0 bt tl ps5 m5 got1 u0 u1 u2 u3 LO BU EBX TLB Q4 APB0 G5 LF; prs)). transport HB84 m6 AGS6 ltac:(prs).
        transport HG1 m6 AGS6 ltac:(prs). transport HREST m6 AGS6 ltac:(prs).
        assert (G6 : GIo K R ps5 ((pc_buffer p0, B0, pc_bufalloc p0) :: C1 ++ C2) FB m6).
        { eapply (GIo_client_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        assert (ST6 : stk usegs m6 lo (bv_unsigned sp + -96)).
        { eapply stk_transport_disjoint; [exact ST5 | exact MU6 | exact WM6 | cbn [disjoint_from]; unfold rc_lo in *; lia]. }
        assert (AG6 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m6).
        { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AGS6|]. intros a [[Ha|Ha] _]; cbn [outside]; (split; [| exact Logic.I]); [lia|]. pose proof (CLB0 a Ha). (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 a TL TLB H0; lia). }
        apply evt_done.
        eapply (K1C _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 u3 u2 u1 u0);
          [(keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U3; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U2; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U1; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U0; lia) | reflexivity | exact MI6 | exact ST6 | exact AG6 | exact HDR4 | exact FRS3 | exact G6
          | exact HBS3 | exact HPV3 | exact HMB3 | exact HB84 | exact HG1 | exact HT6 | exact HREST | exact HCUR3 | exact HEB3].
      - (* [comment removed for export] *)
        unfold implM. iprefix.
        hide HDR4. hide FRS3. hide HCUR3. hide HBS3. hide HMB3. hide HEB3. hide HB84. hide HG1. hide HREST.
        step. rewrite (eqb_lits_eq (tl + -8)%Z (tl + -8)%Z eq_refl). cbn [negb]. cbv iota.
        (* [comment removed for export] *)
        step. rewrite (unsigned_lit (B0 + 8)) by lia. rewrite (lxor_ones64 (B0 + 8)) by lia.
        step. if_false_by (ltu_lits_false (18446744073709551615 - (B0 + 8)) (tl + -8) ltac:(clear - Q1 Q4 TL TLB; lia) ltac:(clear - Q1 Q4 TL TLB; lia)).
        do 2 step. step. if_false_by (ltu_lits_false (B0 + tl) 5 ltac:(clear - Q1 Q4 TL TLB; lia) ltac:(clear - Q1 Q4 TL TLB; lia)).
        (* [comment removed for export] *)
        do 2 step.
        step. rewrite (and3_aligned (B0 + tl + -4)) by (clear - Q1 Q2 Q4 M4 TL TLB; fastfirst (first [ noevar_assumption |lia | Z.div_mod_to_equations; lia])).
        step. step. if_true.
        step. if_false.   (* [comment removed for export] *)
        unhide HDR4. unhide FRS3. unhide HCUR3. unhide HBS3. unhide HMB3. unhide HEB3. unhide HB84. unhide HG1. unhide HREST.
        apply evt_done.
        eapply (K1C _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 u0 u1 u2 u3);
          [(keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U0; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U1; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U2; lia) | (keep_hyps CEILV hptr sp R P B CUR EB p ccs got p0 B0 bs0 bt tl got1 u0 u1 u2 u3 U3; lia) | reflexivity | exact MI5 | exact ST5 | exact AG5' | exact HDR4 | exact FRS3 | exact G5
          | exact HBS3 | exact HPV3 | exact HMB3 | exact HB84 | exact HG1 | exact HT' | exact HREST | exact HCUR3 | exact HEB3].
    }
    (* [comment removed for export] *)
    assert (KGE12 : forall (rav t0' t1' t2' a2v a4v a5v a6v a7v t3' t4' t5' t6' y4 y7 y8 y9 W : word) (hi : Z) (m3 : mem) (bt tl : Z),
      (0 <= bt < 2^32)%Z -> (12 <= tl < 2^32)%Z -> (0 <= hi < 2^32)%Z -> (bv_unsigned W = tl + 4294967296 * hi)%Z ->
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells usegs m3 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
      rw_cells usegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      GIo K R s' (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB m3 ->
      rw_cells usegs m3 (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B)] ->
      rw_cells usegs m3 (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells usegs m3 (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
      rw_cells usegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      rw_cells usegs m3 CUR [CB 24 cj] -> rw_cells usegs m3 EB [CB 256 ej] ->
      implM usegs (rb_tail f bt tl p) s' POSTQ
        (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 CUR) W (Z_to_bv 64 11) a2v (Z_to_bv 64 (s32 tl)) a4v a5v a6v a7v
                 (Z_to_bv 64 P) (Z_to_bv 64 Af) y4 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 8) y7 y8 y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x17264) fc None m3 (seg_rom usegs))).
    { intros rav t0' t1' t2' a2v a4v a5v a6v a7v t3' t4' t5' t6' y4 y7 y8 y9 W hi m3 bt tl BT TL Hhi HW MI3 ST3 AG3 HDR3 FRS3 G3 HBS3 HPV3 HMB3 HBUF3 HCUR3 HEB3.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      assert (LBS : length bs = Z.to_nat (pc_bufalloc p)) by (destruct HBUF3 as [[WF _] _]; cbn in WF; lia).
      assert (TM : (0 <= tl mod 4 < 4)%Z) by (Z.div_mod_to_equations; (keep_hyps CEILV hptr R EB p bs ccs got r H1; lia)).
      unfold rb_tail. rewrite (proj2 (Z.ltb_ge tl 12)) by lia. unfold ng_of. rewrite HS. cbv iota.
      cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_realloc prims].
      unfold implM. iprefix.
      hide HDR3. hide FRS3. hide HBS3. hide HPV3. hide HMB3. hide HBUF3. hide HCUR3. hide HEB3.
      step. change (bv_wrap 64 3) with 3%Z. rewrite (land3_low _ _ _ HW) by lia.
      step.
      destruct (Z.eq_dec (tl mod 4) 0) as [M4|M4].
      2:{ (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq _ _) M4). cbn [negb]. rewrite (eqb_lits_false (tl mod 4) 0 ltac:(lia) ltac:(lia) M4). cbv iota.
        apply evt_done. apply (implM_ret usegs).
        do 5 step.
        unhide HDR3. unhide FRS3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HBUF3. unhide HCUR3. unhide HEB3.
        assert (MSG : fmt_at m3 FMT_BLK_MULT4 "block in pcapng dump file has a length of %u that is not a multiple of 4"%string)
          by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_BLK_MULT4; lia| unfold FMT_BLK_MULT4; cbn; lia]).
        eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' _ [AInt (s32 tl)] FMT_BLK_MULT4);
          [right; reflexivity | exact OF1 | exact MI3 | exact ST3 | exact AG3 | exact HDR3 | reflexivity | exact FRS3 | exact HEB3 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; constructor; [reflexivity| constructor]
          | unfold Msg.block_length_not_mult4, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            replace (convs (fmt "block in pcapng dump file has a length of %u that is not a multiple of 4")) with [Cu] by (vm_compute; reflexivity);
            apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
          | vm_compute; reflexivity | apply args_ok_ints1 |].
        destruct (RESTp m3 s' G3 HBS3 HPV3 HMB3 HBUF3) as (X1 & X2 & X3 & X4 & X5 & _).
        exists B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
        do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. exists [CB 24 cj]. split; [exact HCUR3| reflexivity]. }
      (* [comment removed for export] *)
      rewrite M4. cbn [Z.eqb negb]. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
      unhide HBS3. step. hide HBS3. rewrite (sx32_s32 (pc_bufsize p)) by lia.
      do 2 step. rewrite (shl_shr_32 _ _ _ HW) by lia.
      step.
      destruct (Z.lt_ge_cases (pc_bufsize p) tl) as [BLT|BGE].
      2:{ (* [comment removed for export] *)
        rewrite (proj2 (Z.ltb_ge _ _) BGE). if_tf true.
        unhide HBS3. unhide HDR3. unhide FRS3. unhide HPV3. unhide HMB3. unhide HBUF3. unhide HCUR3. unhide HEB3.
        apply evt_done. apply (implM_retb usegs). cbv beta iota.
        eapply (KBODY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' p B bs bt tl);
          [exact OF1 | lia | lia | exact M4 | exact MI3 | exact ST3 | exact AG3 | exact HDR3 | exact FRS3 | eapply (GIo_perm K HPL); [exact G3| apply Permutation_sym; apply Permutation_middle]
          | exact HBS3 | exact HPV3 | exact HMB3 | exact HBUF3 | exact PFX | exact LENB | lia | lia | exact BSA | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | unfold same_meta; repeat split
          | exact HCUR3 | exact HEB3]. }
      (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_lt _ _) BLT). if_tf false.
      (* [comment removed for export] *)
      step. if_false_by (eqz_false (P + 648) ltac:(clear - P1 P4; lia)). step. rewrite (and7_aligned (P + 648)) by (clear - P1 P4 P648; lia). step. if_false.
      unhide HMB3. step. hide HMB3. rewrite (sx32_s32 (ng_max_blocksize s)) by lia.
      step.
      destruct (Z.lt_ge_cases (ng_max_blocksize s) tl) as [MLT|MGE].
      { (* [comment removed for export] *)
        rewrite (proj2 (Z.ltb_lt _ _) MLT). if_tf false.
        apply evt_done. apply (implM_retb usegs). cbv beta iota. apply (implM_ret usegs).
        do 8 step.
        unhide HDR3. unhide FRS3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HBUF3. unhide HCUR3. unhide HEB3.
        assert (MSG : fmt_at m3 FMT_BLK_GTMAX "pcapng block size %u > maximum %u"%string)
          by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_BLK_GTMAX; lia| unfold FMT_BLK_GTMAX; cbn; lia]).
        eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' _ [AInt (s32 tl); AInt (s32 (ng_max_blocksize s))] FMT_BLK_GTMAX);
          [left; reflexivity | exact OF1 | exact MI3 | exact ST3 | exact AG3 | exact HDR3 | reflexivity | exact FRS3 | exact HEB3 | exact MSG | reflexivity | cbn; lia
          | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
          | unfold Msg.block_size_gt_max, PCAP_ERRBUF_SIZE; apply snprintf_pargs;
            replace (convs (fmt "pcapng block size %u > maximum %u")) with [Cu; Cu] by (vm_compute; reflexivity);
            apply pargs_cons; [apply aeq_s32; reflexivity|]; apply pargs_cons; [apply aeq_s32; reflexivity| apply pargs_nil]
          | vm_compute; reflexivity | apply args_ok_ints2 |].
        destruct (RESTp m3 s' G3 HBS3 HPV3 HMB3 HBUF3) as (X1 & X2 & X3 & X4 & X5 & _).
        exists B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
        do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. exists [CB 24 cj]. split; [exact HCUR3| reflexivity]. }
      (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_ge _ _) MGE). if_tf true.
      unhide HBS3. do 4 step.
      unhide HDR3. unhide FRS3. unhide HPV3. unhide HMB3. unhide HBUF3. unhide HCUR3. unhide HEB3.
      apply evt_done. apply (implM_bind_assoc usegs).
      name_sp sp (-96)%Z.
      eapply (implM_bind usegs).
      { eapply REALLOC; [| reflexivity | reflexivity | lia | exact HBUF3].
        split; [exact G3|]. split; [rewrite Hsp; exact ST3|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros r ps4 ms4 PO. cbv beta in PO. destruct PO as (av4 & m4 & E & OF4 & MI4 & ST4 & AG4 & RM).
      unfold hpost_regs in E. destruct_exs E. subst ms4. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 95012)) with (Z_to_bv 64 95012) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      transport HDR3 m4 AG4 ltac:(prs). transport FRS3 m4 AG4 ltac:(prs). transport HCUR3 m4 AG4 ltac:(prs). transport HBS3 m4 AG4 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p bs ccs got tl INPc; prs)).
      transport HPV3 m4 AG4 ltac:(prs). transport HMB3 m4 AG4 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p s bs ccs got tl INPc; prs)). transport HEB3 m4 AG4 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p bs ej ccs got tl EBX INPc; prs)). clear HBUF3.
      assert (AG04 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m4).
      { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AG4|]. intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]. }
      clear AG4 MI3 ST3 G3 AG3.
      destruct r as [b'|].
      - (* [comment removed for export] *)
        destruct RM as (A' & junkR & -> & G4 & HB4).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G4 ltac:(left; reflexivity)) as (Q1 & Q2 & Q3 & Q4 & _). cbn [cb_addr cb_size fst snd] in Q1, Q2, Q3, Q4.
        apply (implM_retb usegs). cbv beta iota.
        pose proof (munch_refl [(P + 24, P + 32)]%Z m4) as MU5. pose proof (wmono_refl usegs m4) as WM5.
        unfold implM. iprefix.
        hide HDR3. hide FRS3. hide HCUR3. hide HPV3. hide HMB3. hide HEB3. hide HB4.
        step. rewrite (eqb_lits_false A' 0 ltac:(lia) ltac:(lia) ltac:(lia)). cbv iota.
        step. step.   (* [comment removed for export] *)
        unhide HDR3. unhide FRS3. unhide HCUR3. unhide HPV3. unhide HMB3. unhide HEB3. unhide HB4.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGS5 : agrees_on (fun a => outside [(P + 24, P + 32)]%Z a) m4 mm) by (eapply agrees_on_of_munch; [exact MU5 | exact WM5 | intros a _ Ho; exact Ho]);
          assert (G5 : GIo K R ps4 ((b', A', tl) :: C1 ++ C2) FB mm)
            by (eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MU5 | exact WM5 |]; apply Forall_cons; [| apply Forall_nil]; right; unfold iv_in_block; apply Exists_cons_tl;
                apply Exists_exists; exists (pc_self p, P, PCAP_NG_SF_TOTAL); split; [exact HinP|]; cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A'; lia));
          transport HDR3 mm AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs got bt tl b' ps4 A' m1 LO BU P4 G5; prs)); transport FRS3 mm AGS5 ltac:((keep_hyps CEILV H hptr K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R C1 C2 FB P B CUR EB lo p bs ccs got tl b' ps4 A' m1 LO BU P4 G5; prs)); transport HCUR3 mm AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs cj got tl b' ps4 A' m1 LO BU CUR1 SPW P4; prs)); transport HPV3 mm AGS5 ltac:((keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A'; prs));
          transport HMB3 mm AGS5 ltac:((keep_hyps CEILV hptr sp R P B CUR EB p s bs ccs got tl A'; prs)); transport HEB3 mm AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ej ccs got tl b' ps4 A' m1 LO BU P4 EBX G5; prs));
          transport HB4 mm AGS5 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside] in *; pose proof (head_apart K _ _ _ _ _ _ _ G4 HinP) as AP; cbn [cb_addr cb_size fst snd] in AP; unfold PCAP_NG_SF_TOTAL in AP; (keep_hyps CEILV hptr sp R P B CUR EB lo p bs ccs got tl A' a B3 Ha AP; lia))
        end.
        merge_all HB4. lazymatch type of HB4 with rw_cells _ _ _ [CB ?n _] => replace n with (Z.to_nat tl) in HB4 by (keep_hyps CEILV hptr sp R P B CUR EB lo p bs ccs got tl A' B3; lia) end.
        apply evt_done.
        eapply (KBODY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ps4 (set_buffer b' (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p) A' _ bt tl);
          [exact (eq_trans OF4 OF1) | (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got bt tl A' BT; lia) | (keep_hyps CEILV hptr sp R P B CUR EB lo p s bs ccs got tl A' WMB TL MGE; lia) | exact M4 | assumption | assumption | | exact HDR3 | exact FRS3 | exact G5 | exact HBS3 | exact HPV3 | exact HMB3 | exact HB4
          | cbn [pc_bufdata set_buffer]; unfold zfirstn; apply realloc_prefix; [exact PFX | exact LENB | exact LBS | (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A' TL; lia)]
          | cbn [pc_bufdata pc_bufalloc set_buffer]; unfold zfirstn; rewrite length_firstn; (keep_hyps CEILV hptr sp R P B CUR EB lo p bs ccs got tl A' TL; lia)
          | cbn [pc_bufalloc set_buffer]; (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A'; lia) | cbn [pc_bufalloc set_buffer]; (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A' TL; lia) | cbn [pc_bufsize pc_bufalloc set_buffer]; (keep_hyps CEILV hptr sp R P B CUR EB p bs ccs got tl A' BLT; lia)
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | unfold same_meta; repeat split | exact HCUR3 | exact HEB3 ].
        { eapply agrees_on_trans; [exact AG04|]. eapply agrees_on_weaken; [exact AGS5|]. intros a (_ & Hn & _). cbn [outside]. split; [exact Hn| exact Logic.I]. }
      - (* [comment removed for export] *)
        destruct RM as (-> & G4 & HB4 & _).
        apply (implM_retb usegs). cbv beta iota. apply (implM_ret usegs).
        pose proof (GIo_block_ok K _ _ _ _ _ _ G4 HinP') as (_ & _ & _ & _ & P5 & _). cbn [cb_addr cb_size fst snd] in P5. unfold PCAP_NG_SF_TOTAL in P5.
        assert (OOMS : fmt_at m4 STR_OOM "out of memory"%string)
          by (apply (fmt_at_intro m4 _ _ MI4); [vm_compute; reflexivity| unfold STR_OOM; lia| unfold STR_OOM; cbn; lia]).
        destruct OOMS as [OOMB _].
        pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [14%nat; 242%nat] HEB3 ltac:(reflexivity)) as HE'. clear HEB3. cbn [mk_CB_cells app] in HE'.
        destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
        hide HDR3. hide FRS3. hide HCUR3. hide HBS3. hide HPV3. hide HMB3. hide HB4. hide HE2.
        step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
        do 5 step.
        eapply evt_cut.
        { eapply (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB STR_OOM 14);
            [reflexivity | reflexivity | reflexivity | exact OOMB | reflexivity | lia | exact HE1 | unfold STR_OOM; gio_ceil_fact; clear -CLO__ EBX P5 LO BU SPW; lia | lia | unfold STR_OOM; lia | exact MI4]. }
        cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m5 & -> & MU5 & WM5 & MI5 & HE1' & _). clear HE1.
        replace (ret_pc (Z_to_bv 64 95396)) with (Z_to_bv 64 95396) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        assert (AGS5 : agrees_on (fun a => outside [(EB, EB + 14)]%Z a) m4 m5) by (eapply agrees_on_of_munch; [exact MU5 | exact WM5 | intros a _ Ho; exact Ho]).
        unhide HDR3. unhide FRS3. unhide HCUR3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HB4. unhide HE2.
        transport HDR3 m5 AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs got bt tl ps4 m4 LO BU P4 EBX G4; prs)). transport FRS3 m5 AGS5 ltac:((keep_hyps CEILV H hptr K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R C1 C2 FB P B CUR EB lo p bs ccs got tl ps4 m4 LO BU P4 EBX G4; prs)). transport HCUR3 m5 AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs cj got tl ps4 m4 LO BU CUR1 P4 EBX G4; prs)). transport HBS3 m5 AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs got tl ps4 m4 LO BU P4 EBX G4; prs)).
        transport HPV3 m5 AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs got tl ps4 m4 LO BU P4 EBX G4; prs)). transport HMB3 m5 AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p s bs ccs got tl ps4 m4 LO BU P4 EBX G4; prs)). transport HB4 m5 AGS5 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p bs ccs got tl ps4 m4 LO BU B4 APB EBX G4; prs)). transport HE2 m5 AGS5 ltac:(prs).
        assert (G5 : GIo K R ps4 (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB m5).
        { eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MU5 | exact WM5 |]. apply Forall_cons; [| apply Forall_nil].
          destruct EBX as [X| ->]; [left; cbn [fst snd]; unfold rc_lo; (keep_hyps CEILV hptr sp R P B CUR EB lo p bs ccs got tl LO BU X; lia)| right]. unfold iv_in_block. apply Exists_exists.
          exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [| cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia].
          apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; right; exact X]. }
        assert (ST5 : stk usegs m5 lo (bv_unsigned sp + -96)).
        { eapply stk_transport_disjoint; [exact ST4 | exact MU5 | exact WM5 | cbn [disjoint_from]; destruct EBX as [X| ->]; unfold rc_lo in *; (keep_hyps CEILV hptr sp R P B CUR EB lo p bs ccs got tl X H K C1 C2 FB ps4 m5 LO P4 G5; lia)]. }
        assert (AG05 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m5).
        { eapply agrees_on_trans; [exact AG04|]. eapply agrees_on_weaken; [exact AGS5|]. intros a (_ & _ & _ & Hn). cbn [outside]. split; [lia| exact Logic.I]. }
        hide HDR3. hide FRS3. hide HCUR3. hide HBS3. hide HPV3. hide HMB3. hide HB4. hide HE2. hide HE1'.
        do 2 step.
        unhide HDR3. unhide FRS3. unhide HCUR3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HB4. unhide HE2. unhide HE1'.
        eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps4 (RB_Err _ p) (-1)%Z);
          [exact (eq_trans OF4 OF1) | exact MI5 | exact ST5 | exact AG05 | exact HDR3 | reflexivity | exact FRS3 |].
        destruct (RESTp m5 ps4 G5 HBS3 HPV3 HMB3 HB4) as (X1 & X2 & X3 & X4 & X5 & _).
        exists p, B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
        do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. cbv beta iota. split; [reflexivity|]. split; [reflexivity|].
        assert (OOM : Msg.out_of_memory = [111; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121]%Z) by (vm_compute; reflexivity).
        rewrite OOM. cbn [length Nat.add Nat.sub map app].
        split; [| split; [cbn; lia| split; [repeat constructor| exists [CB 24 cj]; split; [exact HCUR3| reflexivity]]]].
        lazymatch type of HE2 with rw_cells _ _ _ [CB _ ?j] => exists j end. join_cells HE1' HE2.
        eapply rw_cells_recell; [exact HE1' | pose proof (proj1 (proj1 HE1')) as WF; cbn in WF |- *; clear - WF; tauto | reflexivity]. }
    (* [comment removed for export] *)
    assert (KLT12 : forall (rav t0' t1' t2' a0v a2v a4v a5v a6v a7v t3' t4' t5' t6' y4 y7 y8 y9 : word) (m3 : mem) (bt tl : Z),
      (0 <= bt < 2^32)%Z -> (0 <= tl < 12)%Z ->
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -96) ->
      agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
      rw_cells usegs m3 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 bt); C4 (Z_to_bv 64 tl)] ->
      rw_cells usegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      GIo K R s' (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB m3 ->
      rw_cells usegs m3 (P + 20) [C4 (Z_to_bv 64 (pc_bufsize p)); C8 (Z_to_bv 64 B)] ->
      rw_cells usegs m3 (P + 48) [C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))] ->
      rw_cells usegs m3 (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize s))] ->
      rw_cells usegs m3 B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      rw_cells usegs m3 CUR [CB 24 cj] -> rw_cells usegs m3 EB [CB 256 ej] ->
      implM usegs (rb_tail f bt tl p) s' POSTQ
        (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 CUR) a0v (Z_to_bv 64 11) a2v (Z_to_bv 64 (s32 tl)) a4v a5v a6v a7v
                 (Z_to_bv 64 P) (Z_to_bv 64 Af) y4 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 8) y7 y8 y9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x17200) fc None m3 (seg_rom usegs))).
    { intros rav t0' t1' t2' a0v a2v a4v a5v a6v a7v t3' t4' t5' t6' y4 y7 y8 y9 m3 bt tl BT TL MI3 ST3 AG3 HDR3 FRS3 G3 HBS3 HPV3 HMB3 HBUF3 HCUR3 HEB3.
      clear HBS HPV HMB HBUF HEB HCUR FRS HD2.
      unfold rb_tail. rewrite (proj2 (Z.ltb_lt tl 12)) by lia. apply (implM_ret usegs).
      rewrite (s32_small tl) by lia.
      hide HDR3. hide FRS3. hide HBS3. hide HPV3. hide HMB3. hide HBUF3. hide HCUR3. hide HEB3.
      do 7 step.
      unhide HDR3. unhide FRS3. unhide HBS3. unhide HPV3. unhide HMB3. unhide HBUF3. unhide HCUR3. unhide HEB3.
      assert (MSG : fmt_at m3 FMT_BLK_LT "block in pcapng dump file has a length of %u < %zu"%string)
        by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_BLK_LT; lia| unfold FMT_BLK_LT; cbn; lia]).
      eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' _ [AInt tl; AInt 12] FMT_BLK_LT);
        [left; reflexivity | exact OF1 | exact MI3 | exact ST3 | exact AG3 | exact HDR3 | reflexivity | exact FRS3 | exact HEB3 | exact MSG | reflexivity | cbn; lia
        | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | unfold Msg.block_length_lt, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints2 |].
      destruct (RESTp m3 s' G3 HBS3 HPV3 HMB3 HBUF3) as (X1 & X2 & X3 & X4 & X5 & _).
      exists B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
      do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. exists [CB 24 cj]. split; [exact HCUR3| reflexivity]. }
    (* [comment removed for export] *)
    destruct (Z.eq_dec (Z.of_nat (length got)) 8) as [L8|L8].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) L8). cbn [negb]. apply (implM_bind_assoc usegs).
      hide HBS. hide HPV. hide HMB. hide HBUF. hide HEB. hide HCUR. hide HD2. hide FRS.
      ienter. step. rewrite (eqb_lits_false (Z.of_nat (length got)) 8 ltac:(lia) ltac:(lia) L8). change (negb false) with true. cbv iota. do 3 step.
      unhide HBS. unhide HPV. unhide HMB. unhide HBUF. unhide HEB. unhide HCUR. unhide HD2. unhide FRS.
      name_sp sp (-96)%Z.
      apply evt_done. eapply (implM_bind usegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros e ps3 ms3 PO. cbv beta in PO. destruct PO as (av3 & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO).
      unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 94756)) with (Z_to_bv 64 94756) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      transport FRS m3 AG3 ltac:(prs). transport HD2 m3 AG3 ltac:(prs). transport HCUR m3 AG3 ltac:(prs). transport HBS m3 AG3 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p ccs got INP; prs)).
      transport HPV m3 AG3 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p ccs got INP; prs)). transport HMB m3 AG3 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB p s ccs got INP; prs)). transport HBUF m3 AG3 ltac:(prs). transport HEB m3 AG3 ltac:((keep_hyps CEILV hptr sp R C1 C2 P B CUR EB lo p ej ccs got EBX INP; prs)).
      assert (AG03 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3).
      { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AG3|]. intros a [[Ha|Ha] _]; [left; lia| right].
        apply in_block_app in Ha as [X|X]; apply in_block_app; [left; exact X| right; right; exact X]. }
      clear AG3 MI1 ST1 G1.
      assert (X8 : (Z.of_nat (length got) + Z.of_nat (8 - length got) = 8)%Z) by lia.
      destruct e.
      - (* [comment removed for export] *)
        cbv iota. destruct (ERRNO eq_refl) as [EN2 EB2]. clear ERRNO.
        unfold utp in EN2. rewrite <- TP in EN2.
        eapply implM_pure; [reflexivity|]. cbn [fst snd].
        set (err := lc_errno (ps_libc s')) in *.
        hide HBS. hide HPV. hide HMB. hide HBUF. hide HEB. hide HCUR. hide HD2. hide FRS.
        cbn [Z.b2z]. step. if_false. do 4 step.
        replace (ret_pc (Z_to_bv 64 94764)) with (Z_to_bv 64 94764) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        (* [comment removed for export] *)
        pose proof (GIo_tls K _ _ _ _ _ G3) as [_ TB]. unfold tls_block_ok_u, utp in TB. rewrite <- TP in TB.
        assert (T4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z).
        { destruct TB as (TBA & _). apply Z.mod_divide in TBA; [|lia]. destruct TBA as [q Hq]. apply Z.mod_divide; [lia|]. exists (q * 4 + 9)%Z. lia. }
        step. if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(clear - TB; lia)).
        step. rewrite (and3_aligned (bv_unsigned tp + -164)) by (clear - TB T4; lia). step. if_false.
        do 3 step.
        replace (sx32 (Z_to_bv 64 err)) with (Z_to_bv 64 (s32 err)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
        unhide HBS. unhide HPV. unhide HMB. unhide HBUF. unhide HEB. unhide HCUR. unhide HD2. unhide FRS.
        eapply (KFMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' err p); [exact OF1 | exact MI3 | exact ST3 | exact AG03 | exact HD2 | cbn [cells_size csize Nat.add]; lia | exact FRS | exact HEB | lia |].
        destruct (RESTp m3 s' G3 HBS HPV HMB HBUF) as (X1 & X2 & X3 & X4 & X5 & _).
        exists B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
        do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. exists [CB 24 cj]. split; [exact HCUR| reflexivity].
      - (* [comment removed for export] *)
        cbv iota. clear ERRNO. cbn [negb andb]. rewrite Bool.andb_true_r.
        destruct (Nat.eq_dec (length got) 0) as [L0|L0].
        + (* [comment removed for export] *)
          rewrite (proj2 (Z.eqb_eq (Z.of_nat (length got)) 0) ltac:(lia)). apply (implM_retb usegs). cbv beta iota. apply (implM_ret usegs).
          hide HBS. hide HPV. hide HMB. hide HBUF. hide HEB. hide HCUR. hide HD2. hide FRS.
          cbn [Z.b2z]. step. if_true. step. rewrite (eqb_lits_eq (Z.of_nat (length got)) 0) by lia. cbv iota. do 2 step.
          unhide HBS. unhide HPV. unhide HMB. unhide HBUF. unhide HEB. unhide HCUR. unhide HD2. unhide FRS.
          eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' (RB_Eof p) 0%Z);
            [exact OF1 | exact MI3 | exact ST3 | exact AG03 | exact HD2 | cbn [cells_size csize Nat.add]; lia | exact FRS |].
          destruct (RESTp m3 s' G3 HBS HPV HMB HBUF) as (X1 & X2 & X3 & X4 & X5 & _).
          exists p, B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
          do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. cbv beta iota. split; [reflexivity|]. split; [reflexivity|]. split; [exact HEB|]. exists [CB 24 cj]. split; [exact HCUR| reflexivity].
        + (* [comment removed for export] *)
          rewrite (proj2 (Z.eqb_neq (Z.of_nat (length got)) 0) ltac:(lia)). apply (implM_retb usegs). cbv beta iota. apply (implM_ret usegs).
          hide HBS. hide HPV. hide HMB. hide HBUF. hide HEB. hide HCUR. hide HD2. hide FRS.
          cbn [Z.b2z]. step. if_true. step. rewrite (eqb_lits_false (Z.of_nat (length got)) 0 ltac:((keep_hyps CEILV hptr sp R P B CUR EB p ccs got GL; lia)) ltac:((keep_hyps CEILV hptr sp R P B CUR EB p ccs got; lia)) ltac:((keep_hyps CEILV hptr sp R P B CUR EB p ccs got L0; lia))). cbv iota. do 7 step.
          unhide HBS. unhide HPV. unhide HMB. unhide HBUF. unhide HEB. unhide HCUR. unhide HD2. unhide FRS.
          assert (MSG : fmt_at m3 FMT_TRUNC_PCAPNG "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
            by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| unfold FMT_TRUNC_PCAPNG; lia| unfold FMT_TRUNC_PCAPNG; cbn; lia]).
          eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' _ [AInt 8; AInt (Z.of_nat (length got))] FMT_TRUNC_PCAPNG _ p);
            [left; reflexivity | exact OF1 | exact MI3 | exact ST3 | exact AG03 | exact HD2 | cbn [cells_size csize Nat.add]; lia | exact FRS | exact HEB | exact MSG | reflexivity | cbn; lia
            | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] | unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE; reflexivity
            | vm_compute; reflexivity | apply args_ok_ints2 |].
          destruct (RESTp m3 s' G3 HBS HPV HMB HBUF) as (X1 & X2 & X3 & X4 & X5 & _).
          exists B, bs. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
          do 5 (split; [reflexivity|]). split; [unfold same_meta; repeat split|]. exists [CB 24 cj]. split; [exact HCUR| reflexivity]. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) L8). cbn [negb]. apply (implM_retb usegs). cbv beta iota.
    assert (L8n : length got = 8%nat) by lia.
    destruct got as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|gx gr]]]]]]]]]; try (exfalso; cbn in L8n; (keep_hyps CEILV hptr sp R P B CUR EB p ccs L8n g0 g1 g2 g3 g4 g5 g6 g7 gx gr; lia)). clear L8n L8.
    pose proof GR as GR'.
    apply Forall_cons_iff in GR' as [R0 GR']. apply Forall_cons_iff in GR' as [R1 GR']. apply Forall_cons_iff in GR' as [R2 GR']. apply Forall_cons_iff in GR' as [R3 GR'].
    apply Forall_cons_iff in GR' as [R4 GR']. apply Forall_cons_iff in GR' as [R5 GR']. apply Forall_cons_iff in GR' as [R6 GR']. apply Forall_cons_iff in GR' as [R7 _].
    assert (LJ : length junk' = 0%nat) by (destruct HD2 as [[WF _] _]; cbn in WF; lia). destruct junk' as [|jx jr]; [|discriminate LJ]. clear LJ.
    assert (HD5 : rw_cells usegs m2 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7))]).
    { eapply rw_cells_recell; [exact HD2 | cbn; repeat split; try exact Logic.I |]. cbn [cells_bytes cbytes map app]. rewrite (le4_lit g0 g1 g2 g3), (le4_lit g4 g5 g6 g7) by (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R0 R1 R2 R3 R4 R5 R6 R7; lia). reflexivity. }
    clear HD2.
    unfold get_le32, zslice, zfirstn, zskipn. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. cbn [firstn skipn].
    replace (Z.of_nat (length [g0; g1; g2; g3; g4; g5; g6; g7])) with 8%Z by reflexivity.
    unfold implM. iprefix.
    hide FRS. hide HCUR. hide HBS. hide HMB. hide HBUF. hide HEB.
    step. if_false.
    destruct (pc_swapped p); cbn [Z.b2z] in HPV |- *.
    - (* [comment removed for export] *)
      rewrite (bswap32_bytes g0 g1 g2 g3), (bswap32_bytes g4 g5 g6 g7) by lia. rewrite !le_of_bytes_4.
      replace (g3 + 256 * g2 + 65536 * g1 + 16777216 * g0)%Z with (le4val g3 g2 g1 g0) by reflexivity.
      replace (g7 + 256 * g6 + 65536 * g5 + 16777216 * g4)%Z with (le4val g7 g6 g5 g4) by reflexivity.
      step. step. if_false.
      eapply evt_cut.
      { eapply (blk_swap_hdr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g0 g1 g2 g3 g4 g5 g6 g7);
          [exact MI1 | lia | lia | lia | lia | lia | lia | lia | lia | lia | exact HD5]. }
      cbv beta. intros ms' PO. destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & hi & m3 & -> & MU3 & WM3 & MI3 & HD3 & HW & Hhi). clear HD5.
      assert (AGS3 : agrees_on (fun a => outside [(bv_unsigned sp + -96, bv_unsigned sp + -88)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]).
      unhide FRS. unhide HCUR. unhide HBS. unhide HMB. unhide HBUF. unhide HEB.
      transport FRS m3 AGS3 ltac:(prs). transport HCUR m3 AGS3 ltac:(prs). transport HBS m3 AGS3 ltac:(prs). transport HPV m3 AGS3 ltac:(prs).
      transport HMB m3 AGS3 ltac:(prs). transport HBUF m3 AGS3 ltac:(prs). transport HEB m3 AGS3 ltac:((keep_hyps CEILV H hptr K sp R C1 C2 FB P B CUR EB lo p ej ccs g0 g1 g2 g3 g4 g5 g6 g7 s' m2 LO BU P4 EBX G1; prs)).
      assert (G3 : GIo K R s' (C1 ++ (pc_buffer p, B, pc_bufalloc p) :: C2) FB m3).
      { eapply (GIo_client_frame K HFL SFL); [exact G1 | exact MU3 | exact WM3 |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (ST3 : stk usegs m3 lo (bv_unsigned sp + -96)).
      { eapply stk_transport_disjoint; [exact ST1 | exact MU3 | exact WM3 | cbn [disjoint_from]; lia]. }
      assert (AG03 : agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + 24 <= a < P + 32) /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256))%Z m m3).
      { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AGS3|]. intros a [[Ha|Ha] _]; cbn [outside]; (split; [| exact Logic.I]); [lia|]. pose proof (CLB a Ha). lia. }
      hide FRS. hide HCUR. hide HBS. hide HPV. hide HMB. hide HBUF. hide HEB. hide HD3.
      step. rewrite (swrap32_low _ _ _ HW). do 2 step.
      unhide FRS. unhide HCUR. unhide HBS. unhide HPV. unhide HMB. unhide HBUF. unhide HEB. unhide HD3.
      destruct (Z.lt_ge_cases (le4val g7 g6 g5 g4) 12) as [LT|GE].
      + if_tf false. apply evt_done.
        eapply (KLT12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3); [unfold le4val; lia | unfold le4val in *; lia | exact MI3 | exact ST3 | exact AG03 | exact HD3 | exact FRS | exact G3
          | exact HBS | exact HPV | exact HMB | exact HBUF | exact HCUR | exact HEB].
      + if_tf true. apply evt_done.
        eapply (KGE12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi m3); [unfold le4val; lia | unfold le4val in *; lia | exact Hhi | exact HW | exact MI3 | exact ST3 | exact AG03 | exact HD3 | exact FRS | exact G3
          | exact HBS | exact HPV | exact HMB | exact HBUF | exact HCUR | exact HEB].
    - (* [comment removed for export] *)
      rewrite !le_of_bytes_4.
      replace (g0 + 256 * g1 + 65536 * g2 + 16777216 * g3)%Z with (le4val g0 g1 g2 g3) by reflexivity.
      replace (g4 + 256 * g5 + 65536 * g6 + 16777216 * g7)%Z with (le4val g4 g5 g6 g7) by reflexivity.
      step. step. if_true.
      step. step.
      rewrite (swrap32_low (bv_unsigned (sx32 (Z_to_bv 64 (le4val g4 g5 g6 g7)))) (le4val g4 g5 g6 g7) ((g7 / 128) * 4294967295)%Z ltac:(rewrite unsigned_sx32 by lia; unfold sxv; lia)).
      do 2 step.
      unhide FRS. unhide HCUR. unhide HBS. unhide HMB. unhide HBUF. unhide HEB.
      destruct (Z.lt_ge_cases (le4val g4 g5 g6 g7) 12) as [LT|GE].
      + if_tf true. apply evt_done.
        eapply (KLT12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2); [unfold le4val; lia | unfold le4val in *; lia | exact MI1 | exact ST1 | exact AG02 | exact HD5 | exact FRS | exact G1
          | exact HBS | exact HPV | exact HMB | exact HBUF | exact HCUR | exact HEB].
      + if_tf false. apply evt_done.
        eapply (KGE12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ((g7 / 128) * 4294967295)%Z m2);
          [unfold le4val; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs g0 g1 g2 g3 g4 g5 g6 g7 R0 R1 R2 R3; lia) | unfold le4val in *; (keep_hyps CEILV hptr sp R P B CUR EB lo p ccs g0 g1 g2 g3 g4 g5 g6 g7 R4 R5 R6 R7 GE; lia) | Z.div_mod_to_equations; (keep_hyps CEILV hptr R EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 q r R7 H0 H1; lia) | rewrite unsigned_sx32 by (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7 R4 R5 R6 R7; lia); unfold sxv; (keep_hyps CEILV hptr sp R P B CUR EB p ccs g0 g1 g2 g3 g4 g5 g6 g7; lia)
          | exact MI1 | exact ST1 | exact AG02 | exact HD5 | exact FRS | exact G1 | exact HBS | exact HPV | exact HMB | exact HBUF | exact HCUR | exact HEB].
  Qed.
  End Sz2.
  Theorem read_block_proof : ltac:(let t := eval cbv delta [read_block_proof__stmt] in read_block_proof__stmt in exact t).
  Proof using FERROR FMT FREAD HAL HFL HPL REALLOC SFL SNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R st C1 C2 FB f Af P B CUR EB lo p s i a_bhdr bs ej ccs. ltac2:(SecDiet.SzSec.closeP 'read_block_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Blk.

End WithCeil.
End TwB.
End F_sfpcapng_blk.

(* [comment removed for export] *)
Module Stdio_glue.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section Agree.
  Context {hptr : Type}.
  Notation cblk := (@cblock hptr).

  Definition FILE_R_agree__stmt : Prop := forall P m m' f Fp BA closefn readfn seekfn prev next,
    FILE_R m f Fp BA closefn readfn seekfn prev next ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> P a) -> (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    FILE_R m' f Fp BA closefn readfn seekfn prev next.
  Section Sz1.
  Variables P m m' f Fp BA closefn readfn seekfn prev next : ltac2:(SecDiet.SzSec.tyM 'FILE_R_agree__stmt "vvvvvvvvvvv" @P).
  Lemma FILE_R_agree__body : ltac2:(SecDiet.SzSec.bodyP 'FILE_R_agree__stmt "vvvvvvvvvvv").
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros FR AG HP1 HP2.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - eapply agrees_rw_cells; [exact AG | exact FC |]. unfold fcells. rewrite file_cells_size. intros a Ha. apply HP1. lia.
    - pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
      eapply agrees_rw_cells; [exact AG | exact BUF |]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP2. lia.
  Qed.
  End Sz1.
  Lemma FILE_R_agree : ltac:(let t := eval cbv delta [FILE_R_agree__stmt] in FILE_R_agree__stmt in exact t).
  Proof using CEILV. intros P m m' f Fp BA closefn readfn seekfn prev next. ltac2:(SecDiet.SzSec.closeP 'FILE_R_agree__body "vvvvvvvvvvv"). Qed.

  Lemma files_R_agree : forall fs (FB : list cblk) P m m' prev,
    files_R m prev fs FB -> agrees_on P m m' ->
    (forall a, in_block FB a -> P a) ->
    files_R m' prev fs FB.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    induction fs as [|[q f] fs IH]; intros [|[[q' A] n] FB] P m m' prev H AG HP; cbn in H |- *; try exact H.
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    pose proof INV as INV'. destruct INV as (_ & _ & BS & _).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
    split.
    { eapply FILE_R_agree; [exact FR | exact AG | |].
      + intros a Ha. apply HP. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold FILE_ALLOC. lia.
      + intros a Ha. apply HP. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. rewrite BS in Ha. unfold FILE_ALLOC, FILE_BUF_OFF, BUFSIZ in *. lia. }
    split; [exact INV'|].
    eapply IH; [exact REST | exact AG |]. intros a Ha. apply HP. unfold in_block in *. apply Exists_cons_tl. exact Ha.
  Qed.

  Lemma STDIOR_agree : forall (l : libc_st hptr) FB m m' P,
    STDIOR l FB m -> agrees_on P m m' ->
    (forall a, GI.stdio_static a -> P a) -> (forall a, in_block FB a -> P a) ->
    STDIOR l FB m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros l FB m m' P SR AG HS HB.
    destruct SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold GI.stdio_static in HS.
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SOI as SOI'. pose proof SEI as SEI'.
    destruct SOI as (_ & _ & SObs & _). destruct SEI as (_ & _ & SEbs & _).
    unfold STDIOR. unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD.
    Ltac tra AG HS A := eapply agrees_rw_cells; [exact AG | exact A | intros a Ha; apply HS; cbn in Ha; lia].
    split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HS; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HS; lia]. }
    split; [exact SOI'|].
    split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HS; lia | rewrite SEbs; intros a Ha; apply HS; lia]. }
    split; [exact SEI'|].
    split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HS; lia. }
    split; [tra AG HS U1|]. split; [tra AG HS U2|]. split; [tra AG HS U3|]. split; [tra AG HS OL|]. split; [tra AG HS OH|].
    split; [| exact ND].
    eapply files_R_agree; [exact FS | exact AG | exact HB].
  Qed.
End Agree.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Files.
  Context {hptr : Type} (ptr_eqb : hptr -> hptr -> bool).
  Hypothesis EQB : forall p q, ptr_eqb p q = true <-> p = q.
  Notation cblk := (@cblock hptr).

  Lemma eqb_refl' : forall p, ptr_eqb p p = true.
  Proof using EQB. pin_using (fun (EQB : unit) => tt). intros p. apply (proj2 (EQB p p)). reflexivity. Qed.
  Lemma eqb_neq : forall p q, p <> q -> ptr_eqb p q = false.
  Proof using EQB. pin_using (fun (EQB : unit) => tt). intros p q NE. destruct (ptr_eqb p q) eqn:E; [|reflexivity]. exfalso. apply NE. apply (proj1 (EQB p q)). exact E. Qed.

  (* [comment removed for export] *)
  Lemma files_R_toks : forall m prev fs (FB : list cblk), files_R m prev fs FB -> map cb_tok FB = map fst fs.
  Proof using Type. pin_using tt.
    intros m prev fs; revert prev.
    induction fs as [|[q f] fs IH]; intros prev [|[[q' A] n] FB] H; cbn in H |- *; try reflexivity; try contradiction.
    destruct H as (-> & _ & _ & _ & _ & _ & REST). f_equal. eapply IH. exact REST.
  Qed.

  (* [comment removed for export] *)
  Definition files_R_pick__stmt : Prop := forall m prev fs (FB : list cblk) q A n,
    files_R m prev fs FB -> List.NoDup (map fst fs) -> In (q, A, n) FB ->
    exists f pv nx,
      files_lookup ptr_eqb fs q = Some f /\ In (q, f) fs /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx
      /\ heap_file_inv f.
  Section Sz6.
  Variables m prev : ltac2:(SecDiet.SzSec.tyM 'files_R_pick__stmt "vvk" @m).
  Lemma files_R_pick__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_pick__stmt "vvk").
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros fs; revert prev.
    induction fs as [|[q1 f1] fs IH]; intros prev [|[[q1' A1] n1] FB] q A n H ND HIN; cbn in H; try contradiction; try (exfalso; exact HIN).
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    destruct HIN as [E | HIN].
    - injection E as <- <- <-. exists f1, prev, (hd_addr FB). cbn [files_lookup]. rewrite eqb_refl'.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR| exact INV].
    - destruct (IH A1 FB q A n REST ND HIN) as (f & pv & nx & LK & INf & En & B0 & Bhi & FRf & INVf).
      assert (NE : q1 <> q).
      { intros ->. apply NI. change q with (fst (q, f)). apply in_map. exact INf. }
      exists f, pv, nx. cbn [files_lookup]. rewrite (eqb_neq _ _ NE).
      split; [exact LK|]. split; [right; exact INf|]. split; [exact En|]. split; [exact B0|]. split; [exact Bhi|]. split; [exact FRf| exact INVf].
  Qed.
  End Sz6.
  Lemma files_R_pick : ltac:(let t := eval cbv delta [files_R_pick__stmt] in files_R_pick__stmt in exact t).
  Proof using EQB. intros m prev fs. ltac2:(SecDiet.SzSec.closeP 'files_R_pick__body "vvk"). Qed.

  (* [comment removed for export] *)
  Definition files_R_frame__stmt : Prop := forall m m' prev fs (FB : list cblk),
    files_R m prev fs FB ->
    (forall q2 A2 n2 f2 pv nx, In (q2, A2, n2) FB ->
                     FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f2 ->
                     FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx) ->
    files_R m' prev fs FB.
  Section Sz7.
  Variables m m' prev FB : ltac2:(SecDiet.SzSec.tyM 'files_R_frame__stmt "vvvkv" @m).
  Lemma files_R_frame__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_frame__stmt "vvvkv").
  Proof using Type. pin_using tt.
    intros fs.
 revert prev FB.
    induction fs as [|[q3 f3] fs IH]; intros pv0 [|[[q3' A3] n3] FB] H HF; cbn in H |- *; try exact H.
    destruct H as (-> & -> & B0 & Bhi & FR3 & INV3 & REST3).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
    split; [exact (HF q3 A3 FILE_ALLOC f3 pv0 (hd_addr FB) (or_introl eq_refl) FR3 INV3)|]. split; [exact INV3|].
    apply IH; [exact REST3|]. intros q2 A2 n2 f2 pv nx HIN2. apply (HF q2 A2 n2 f2 pv nx (or_intror HIN2)).
  Qed.
  End Sz7.
  Lemma files_R_frame : ltac:(let t := eval cbv delta [files_R_frame__stmt] in files_R_frame__stmt in exact t).
  Proof using Type. intros m m' prev fs FB. ltac2:(SecDiet.SzSec.closeP 'files_R_frame__body "vvvkv"). Qed.

  Lemma files_update_keys : forall fs q f', map fst (files_update ptr_eqb fs q f') = map fst fs.
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q f'; cbn; [reflexivity|].
    destruct (ptr_eqb k q); cbn; [reflexivity| f_equal; apply IH].
  Qed.

  Lemma files_remove_keys : forall fs q, incl (map fst (files_remove ptr_eqb fs q)) (map fst fs).
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q; cbn; [apply incl_refl|].
    destruct (ptr_eqb k q); cbn.
    - apply incl_tl, incl_refl.
    - apply incl_cons; [left; reflexivity| apply incl_tl, IH].
  Qed.

  Lemma files_lookup_In : forall fs q f, List.NoDup (map fst fs) -> In (q, f) fs -> files_lookup ptr_eqb fs q = Some f.
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    induction fs as [|[k g] fs IH]; intros q f ND HIN; [destruct HIN|].
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND]. cbn.
    destruct HIN as [E|HIN].
    - injection E as -> ->. rewrite eqb_refl'. reflexivity.
    - assert (NE : k <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact HIN).
      rewrite (eqb_neq _ _ NE). apply IH; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition files_R_focus__stmt : Prop := forall m prev fs (FB : list cblk) q A n,
    files_R m prev fs FB -> List.NoDup (map fst fs) -> In (q, A, n) FB ->
    exists f pv nx,
      files_lookup ptr_eqb fs q = Some f /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx
      /\ heap_file_inv f
      /\ (forall m' f', FILE_R m' f' A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
            (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) FB -> q2 <> q ->
                     FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
                     FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
            files_R m' prev (files_update ptr_eqb fs q f') FB).
  Section Sz11.
  Variables m prev : ltac2:(SecDiet.SzSec.tyM 'files_R_focus__stmt "vvk" @m).
  Lemma files_R_focus__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_focus__stmt "vvk").
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros fs; revert prev.
    induction fs as [|[q1 f1] fs IH]; intros prev [|[[q1' A1] n1] FB] q A n H ND HIN; cbn in H; try contradiction; try (exfalso; exact HIN).
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    pose proof (files_R_toks _ _ _ _ REST) as TK.
    destruct HIN as [E | HIN].
    - injection E as <- <- <-. exists f1, prev, (hd_addr FB). cbn [files_lookup files_update]. rewrite eqb_refl'.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR|]. split; [exact INV|].
      intros m' f' FR' INV' HF. cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR'|]. split; [exact INV'|].
      eapply files_R_frame; [exact REST|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2. apply (HF q2 A2 n2 f2 pv2 nx2 (or_intror HIN2)).
      intros ->. apply NI. rewrite <- TK. change q1 with (cb_tok (q1, A2, n2)). apply in_map. exact HIN2.
    - destruct (IH A1 FB q A n REST ND HIN) as (f & pv & nx & LK & En & B0 & Bhi & FRf & INVf & UPD).
      assert (NE : q1 <> q).
      { intros ->. apply NI. rewrite <- TK. change q with (cb_tok (q, A, n)). apply in_map. exact HIN. }
      exists f, pv, nx. cbn [files_lookup files_update]. rewrite (eqb_neq _ _ NE).
      split; [exact LK|]. split; [exact En|]. split; [exact B0|]. split; [exact Bhi|]. split; [exact FRf|]. split; [exact INVf|].
      intros m' f' FR' INV' HF. cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact (HF q1 A1 FILE_ALLOC f1 prev (hd_addr FB) (or_introl eq_refl) NE FR INV)|].
      split; [exact INV|].
      apply UPD; [exact FR'| exact INV'|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2. apply (HF q2 A2 n2 f2 pv2 nx2); [right; exact HIN2| exact NE2].
  Qed.
  End Sz11.
  Lemma files_R_focus : ltac:(let t := eval cbv delta [files_R_focus__stmt] in files_R_focus__stmt in exact t).
  Proof using EQB. intros m prev fs. ltac2:(SecDiet.SzSec.closeP 'files_R_focus__body "vvk"). Qed.
End Files.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glue.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.

  (* [comment removed for export] *)
  Theorem stdio_fp_proof : stdio_fp_law K.
  Proof using CEILV KST. pin_using (fun (CEILV KST : unit) => tt).
    intros l R FB m m' MS AG. apply (proj2 (KST l R FB m')).
    eapply STDIOR_agree; [apply (proj1 (KST l R FB m)); exact MS | exact AG | |].
    - intros a Ha. left. exact Ha.
    - intros a Ha. right. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma core_ssp : forall R m, CORE_LIBC R m -> ssp_cells m (rc_canary R).
  Proof using Type. pin_using tt. intros R m (_ & G & U & _). split; [exact G | exact U]. Qed.

  (* [comment removed for export] *)
  Definition stdio_iv (R : rctx) (CL FB : list cblk) (SP : Z) (iv : Z * Z) : Prop :=
    (CEILZ <= fst iv /\ snd iv <= rc_spmain R) \/ iv_in_block (CL ++ FB) iv
    \/ (0x23660 <= fst iv /\ snd iv <= 0x23930) \/ (0x54148 <= fst iv /\ snd iv <= 0x54970).

  Lemma in_block_of_iv : forall (LB : list cblk) iv a, iv_in_block LB iv -> fst iv <= a < snd iv -> in_block LB a.
  Proof using Type. pin_using tt.
    intros LB iv a Hiv Ha. unfold iv_in_block, in_block in *. apply Exists_exists in Hiv as (b & Hb & H1 & H2).
    apply Exists_exists. exists b. split; [exact Hb| lia].
  Qed.

  (* [comment removed for export] *)
  Definition GIo_stdio_step__stmt : Prop := forall R (s : PS) CL FB m m' W SP l',
    GIo K R s CL FB m -> munch W m m' -> wmono ssegs m m' ->
    Forall (stdio_iv R CL FB SP) W -> SP <= rc_spmain R ->
    STDIOR l' FB m' ->
    GIo K R (set_libc l' s) CL FB m'.
  Section Sz15.
  Variables R s CL FB m m' W SP l' : ltac2:(SecDiet.SzSec.tyM 'GIo_stdio_step__stmt "vvvvvvvvv" @R).
  Lemma GIo_stdio_step__body : ltac2:(SecDiet.SzSec.bodyP 'GIo_stdio_step__stmt "vvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros G MU WM HW HSP SR'.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA].
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold rc_spmain in HSP. unfold stdio_iv, rc_spmain in HW.
    (* [comment removed for export] *)
    assert (OUT : forall a, 0 <= a < 2^64 ->
              ~ (CEILZ <= a < usp0 R - 48) -> ~ in_block (CL ++ FB) a -> ~ (0x23660 <= a < 0x23930) -> ~ (0x54148 <= a < 0x54970) -> outside W a).
    { intros a Ha N1 N2 N3 N4. eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd].
      destruct Hiv as [X|[X|[X|X]]]; cbn [fst snd] in X; try lia.
      intros Hin. apply N2. eapply in_block_of_iv; [exact X| cbn [fst snd]; lia]. }
    assert (BF : forall a, in_block (CL ++ FB) a -> 0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x55000 <= a) /\ (a < utp R - 200 \/ utp R - 200 + 4096 <= a)).
    { intros a Ha. exact (in_block_facts (utp R) (CL ++ FB) a BO Ha). }
    unfold GIo, set_libc. cbn [ps_heap ps_libc ps_outfile ps_tls].
    split.
    { eapply HFL; [exact HH| exact MU| exact WM|].
      apply Forall_forall. intros [lo hi] Hiv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as X. unfold heap_client_iv, stdio_iv in *. cbn [fst snd] in *.
      destruct X as [X|[X|[X|X]]]; [left; lia | right; left; exact X | right; right; left; lia | right; right; left; lia]. }
    split; [apply (proj2 (KST l' R FB m')); exact SR'|].
    split. { eapply HARNR_agree; [| |exact HA]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT.
             - exact Ha.
             - lia.
             - intros Hb; destruct (BF a Hb); lia.
             - lia.
             - lia. }
    split. { eapply CORE_TLS_agree; [| |exact CT]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT.
             - exact Ha.
             - clear - Hp TBC. lia.
             - intros Hb; destruct (BF a Hb); lia.
             - lia.
             - lia. }
    split. { eapply PCAP_TLS_agree; [| |exact PT]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
    split. { eapply CORE_LIBC_agree; [| |exact CLI]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
    split. { eapply CORE_MISC_agree; [| |exact CM]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
    split. { eapply CORE_EXIT_agree; [| |exact CE]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
    split. { eapply CORE_STK_agree; [| |exact CS]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
    split; [exact Etls|]. split; [exact TB|]. split; [exact BOK| exact SPW].
  Qed.
  End Sz15.
  Lemma GIo_stdio_step : ltac:(let t := eval cbv delta [GIo_stdio_step__stmt] in GIo_stdio_step__stmt in exact t).
  Proof using HFL KST. intros R s CL FB m m' W SP l'. ltac2:(SecDiet.SzSec.closeP 'GIo_stdio_step__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition keeps_of_stdio__stmt : Prop := forall R (s : PS) CL FB m m' W SP (X : Z -> Prop),
    GIo K R s CL FB m -> munch W m m' -> wmono ssegs m m' ->
    Forall (fun iv => (CEILZ <= fst iv /\ snd iv <= SP) \/ iv_in_block FB iv
                      \/ (0x23660 <= fst iv /\ snd iv <= 0x23930) \/ (0x54148 <= fst iv /\ snd iv <= 0x54970)
                      \/ (forall a, fst iv <= a < snd iv -> X a)) W ->
    CEILZ <= SP ->
    agrees_on (fun a => client_keeps CL SP a /\ ~ X a) m m'.
  Section Sz16.
  Variables R s CL FB m m' W SP X : ltac2:(SecDiet.SzSec.tyM 'keeps_of_stdio__stmt "vvvvvvvvv" @R).
  Lemma keeps_of_stdio__body : ltac2:(SecDiet.SzSec.bodyP 'keeps_of_stdio__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G MU WM HW HSP.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [Hk NX].
    eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd]. intros Hin.
    destruct Hk as [Hk|Hk].
    - destruct Hiv as [Y|[Y|[Y|[Y|Y]]]]; cbn [fst snd] in Y; try lia.
      + pose proof (in_block_facts (utp R) FB a BO2 (in_block_of_iv FB (lo, hi) a Y ltac:(cbn; lia))) as (F1 & F2 & F3 & F4). lia.
      + exact (NX (Y a Hin)).
    - pose proof (in_block_facts (utp R) CL a BO1 Hk) as (F1 & F2 & F3 & F4).
      destruct Hiv as [Y|[Y|[Y|[Y|Y]]]]; cbn [fst snd] in Y; try lia.
      + apply in_block_In in Hk as (b & HbIn & Hb). pose proof (in_block_of_iv FB (lo, hi) a Y ltac:(cbn; lia)) as Hk'.
        apply in_block_In in Hk' as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia.
      + exact (NX (Y a Hin)).
  Qed.
  End Sz16.
  Lemma keeps_of_stdio : ltac:(let t := eval cbv delta [keeps_of_stdio__stmt] in keeps_of_stdio__stmt in exact t).
  Proof using Type. intros R s CL FB m m' W SP X. ltac2:(SecDiet.SzSec.closeP 'keeps_of_stdio__body "vvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation eqb := (ho_eqb HO).

  Lemma implM_lookup_file : forall {B} h (k : file_st -> M PS B) (s : PS) Q ms f,
    files_lookup eqb (lc_files (ps_libc s)) h = Some f ->
    implM ssegs (k f) s Q ms -> implM ssegs (mbind (lookup_file ps_libc eqb h) k) s Q ms.
  Proof using Type. pin_using tt.
    intros B h k s Q ms f LK IM. unfold implM, lookup_file, rd_lc, mbind, mget, mret in *.
    cbn [ebind bind fst snd]. rewrite LK. cbn [ebind bind fst snd]. exact IM.
  Qed.

  Lemma implM_upd_lc : forall {B} (g : libc_st hptr -> libc_st hptr) (k : unit -> M PS B) (s : PS) Q ms,
    implM ssegs (k tt) (set_libc (g (ps_libc s)) s) Q ms -> implM ssegs (mbind (upd_lc ps_libc set_libc g) k) s Q ms.
  Proof using Type. pin_using tt. intros. exact H0. Qed.

  Lemma implM_upd_lc_last : forall (g : libc_st hptr -> libc_st hptr) (s : PS) (Q : unit -> PS -> machine_state -> Prop) ms,
    evt ssegs (Q tt (set_libc (g (ps_libc s)) s)) ms -> implM ssegs (upd_lc ps_libc set_libc g) s Q ms.
  Proof using Type. pin_using tt. intros g s Q ms Hq. unfold upd_lc. apply implM_upd. exact Hq. Qed.

  Lemma implM_rd_lc : forall {B} (k : libc_st hptr -> M PS B) (s : PS) Q ms,
    implM ssegs (k (ps_libc s)) s Q ms -> implM ssegs (mbind (rd_lc ps_libc) k) s Q ms.
  Proof using Type. pin_using tt. intros. exact H0. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition spo_facts__stmt : Prop := forall sp tp R (s : PS) CL FB lo budget m,
    std_pre_o K sp tp R s CL FB lo budget m ->
    GIo K R s CL FB m /\ STDIOR (ps_libc s) FB m /\ stk ssegs m lo (bv_unsigned sp) /\ mem_inv ssegs m
    /\ ssp_cells m (rc_canary R) /\ blocks_ok (utp R) (CL ++ FB)
    /\ rc_lo R <= lo /\ lo + budget <= bv_unsigned sp /\ bv_unsigned sp <= rc_spmain R /\ tp = rc_tp R /\ bv_unsigned sp mod 16 = 0
    /\ CEILZ <= rc_lo R /\ rc_spmain R + 48 <= 2^47.
  Section Sz21.
  Variables sp tp R s CL FB lo budget m : ltac2:(SecDiet.SzSec.tyM 'spo_facts__stmt "vvvvvvvvv" @sp).
  Lemma spo_facts__body : ltac2:(SecDiet.SzSec.bodyP 'spo_facts__stmt "vvvvvvvvv").
  Proof using KST. pin_using (fun (KST : unit) => tt).
    intros (G & ST & LOR & LOB & SPM & MI & Etp & AL).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    split; [exact G|]. split; [apply (proj1 (KST _ R _ _)); exact HS|]. split; [exact ST|]. split; [exact MI|].
    split; [exact (core_ssp R m CLI)|]. split; [exact BOK|].
    split; [exact LOR|]. split; [exact LOB|]. split; [exact SPM|]. split; [exact Etp|]. split; [exact AL|].
    unfold rc_lo, rc_spmain in *. lia.
  Qed.
  End Sz21.
  Lemma spo_facts : ltac:(let t := eval cbv delta [spo_facts__stmt] in spo_facts__stmt in exact t).
  Proof using KST. intros sp tp R s CL FB lo budget m. ltac2:(SecDiet.SzSec.closeP 'spo_facts__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma file_block_facts : forall R (CL FB : list cblk) q A n,
    blocks_ok (utp R) (CL ++ FB) -> In (q, A, n) FB ->
    0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= CEILZ /\ (A + n <= 0x10000 \/ 0x55000 <= A) /\ (A + n <= utp R - 200 \/ utp R - 200 + 4096 <= A).
  Proof using Type. pin_using tt.
    intros R CL FB q A n [BO _] HIN.
    pose proof (proj1 (Forall_forall _ _) BO (q, A, n) ltac:(apply in_or_app; right; exact HIN)) as X.
    unfold block_ok, cb_addr, cb_size in X. cbn [fst snd] in X. exact X.
  Qed.

  (* [comment removed for export] *)
  Definition client_range_apart__stmt : Prop := forall R (CL FB : list cblk) SP S len q A n,
    blocks_ok (utp R) (CL ++ FB) -> In (q, A, n) FB ->
    client_range R CL SP S len -> 0 < len -> CEILZ <= SP -> 0 < n ->
    S + len <= A \/ A + n <= S.
  Section Sz23.
  Variables R CL FB SP S len q A n : ltac2:(SecDiet.SzSec.tyM 'client_range_apart__stmt "vvvvvvvvv" @R).
  Lemma client_range_apart__body : ltac2:(SecDiet.SzSec.bodyP 'client_range_apart__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros BOK HIN CR LEN HSP NPOS.
    pose proof BOK as [BO BA]. pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    pose proof (file_block_facts R CL FB q A n BOK HIN) as (A1 & A2 & A3 & A4 & A5 & A6).
    destruct CR as [CR | CR].
    - destruct (Z_lt_le_dec S (A + n)); [|right; lia]. destruct (Z_lt_le_dec A (S + len)); [|left; lia]. exfalso.
      pose proof (CR (Z.max S A) ltac:(lia)) as Hin. apply in_block_In in Hin as (b & HbIn & Hb).
      pose proof (BAX b (q, A, n) HbIn HIN) as AP. unfold apart, cb_addr, cb_size in AP, Hb. cbn [fst snd] in AP, Hb. lia.
    - right. lia.
  Qed.
  End Sz23.
  Lemma client_range_apart : ltac:(let t := eval cbv delta [client_range_apart__stmt] in client_range_apart__stmt in exact t).
  Proof using Type. intros R CL FB SP S len q A n. ltac2:(SecDiet.SzSec.closeP 'client_range_apart__body "vvvvvvvvv"). Qed.

  Definition client_range_lo__stmt : Prop := forall R (s : PS) (CL FB : list cblk) m SP S len lo,
    GIo K R s CL FB m -> client_range R CL SP S len -> 0 < len -> rc_lo R <= lo -> lo <= SP ->
    0 < S /\ (S + len <= lo \/ SP <= S) /\ S + len <= 2^47
    /\ (S + len <= 0x10000 \/ 0x55000 <= S \/ SP <= S).
  Section Sz24.
  Variables R s CL FB m SP S len lo : ltac2:(SecDiet.SzSec.tyM 'client_range_lo__stmt "vvvvvvvvv" @R).
  Lemma client_range_lo__body : ltac2:(SecDiet.SzSec.bodyP 'client_range_lo__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G CR LEN LOR LOS.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    destruct CR as [CR | CR]; unfold rc_lo, rc_spmain in *.
    - destruct (in_block_facts _ _ S BO1 (CR S ltac:(lia))) as (X1 & X2 & X3 & X4).
      destruct (in_block_facts _ _ (S + len - 1) BO1 (CR (S + len - 1) ltac:(lia))) as (Y1 & Y2 & Y3 & Y4).
      split; [lia|]. split; [left; lia|]. split; [lia|].
      destruct (Z_le_gt_dec (S + len) 0x10000); [left; lia|]. destruct (Z_le_gt_dec 0x55000 S); [right; left; lia|]. exfalso.
      destruct (in_block_facts _ _ (Z.max S 0x10000) BO1 (CR (Z.max S 0x10000) ltac:(lia))) as (W1 & W2 & W3 & W4). lia.
    - split; [lia|]. split; [right; lia|]. split; [lia|]. right; right; lia.
  Qed.
  End Sz24.
  Lemma client_range_lo : ltac:(let t := eval cbv delta [client_range_lo__stmt] in client_range_lo__stmt in exact t).
  Proof using Type. intros R s CL FB m SP S len lo. ltac2:(SecDiet.SzSec.closeP 'client_range_lo__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition heap_file_inv_fx__stmt : Prop := forall f f', heap_file_inv f -> f_nowr f = false -> fx_inv f f' -> heap_file_inv f'.
  Section Sz25.
  Variables f f' : ltac2:(SecDiet.SzSec.tyM 'heap_file_inv_fx__stmt "vv" @f).
  Lemma heap_file_inv_fx__body : ltac2:(SecDiet.SzSec.bodyP 'heap_file_inv_fx__stmt "vv").
  Proof using Type. pin_using tt.
    intros (NCH & FD & BS & NRW & NOWRi & NORDi & RBR) NOWR (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
    unfold heap_file_inv. rewrite E1, E2, E3, E4, E5. rewrite NOWR in *.
    split; [exact NCH|]. split; [exact FD|]. split; [exact BS|].
    split; [exact NRW|]. split; [intros X; discriminate X|].
    split; [intros Hn; rewrite RB; rewrite (NORDi Hn); destruct (f_wactive f); reflexivity|].
    rewrite RB. destruct (f_wactive f); [exact RBR| apply Forall_nil].
  Qed.
  End Sz25.
  Lemma heap_file_inv_fx : ltac:(let t := eval cbv delta [heap_file_inv_fx__stmt] in heap_file_inv_fx__stmt in exact t).
  Proof using Type. intros f f'. ltac2:(SecDiet.SzSec.closeP 'heap_file_inv_fx__body "vv"). Qed.

  Theorem fwrite_o_proof : fwrite_stmt_o HO K.
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
    intros until src. intros SPO HIN -> -> -> -> HSRC CR LENB.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    specialize (LENB fs LK).
    pose proof (file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold FILE_BLOCK, STDIO_STACK in *.
    pose proof (bytes_at_bound _ _ _ _ HSRC) as BSRC.
    unfold s_fwrite, Stdio.fwrite, with_file_.
    apply implM_bind_assoc. eapply implM_lookup_file; [exact LK|].
    apply implM_bind_assoc.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct (f_nowr fs) eqn:NOWR.
    { (* [comment removed for export] *)
      destruct (NOWRi eq_refl) as [WACT _].
      unfold fwrite_file, fwritex, ensure_w. rewrite WACT. unfold towrite. rewrite NOWR.
      apply implM_bind_assoc. cbn [mbind munr ebind bind]. apply implM_unr. }
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    (* [comment removed for export] *)
    assert (HS : exists S, (Z_to_bv 64 SRC : word) = Z_to_bv 64 S /\ 0 <= S /\ S + Z.of_nat (length src) < 2^64 /\ bytes_at ssegs m S src
                 /\ (Z.of_nat (length src) = 0 \/ S = SRC)
                 /\ (Z.of_nat (length src) = 0 \/ S + Z.of_nat (length src) <= 2^47)).   (* [comment removed for export] *)
    { destruct (Z.eq_dec (Z.of_nat (length src)) 0) as [L0|L0].
      - exists (SRC mod 2^64). split; [symmetry; apply Z_to_bv_mod64|]. pose proof (Z.mod_pos_bound SRC (2^64) ltac:(lia)).
        split; [lia|]. split; [lia|]. split; [| split; left; exact L0]. destruct src; [| cbn in L0; lia]. apply bytes_at_nil. lia.
      - exists SRC. destruct (client_range_lo R s CL FB m (bv_unsigned sp) SRC (Z.of_nat (length src)) lo G CR ltac:(lia) LOR ltac:(lia)) as (C1 & C2 & C3 & C4).
        split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HSRC|]. split; [right; reflexivity | right; lia]. }
    destruct HS as (S & ES & S0 & Shi & SRC' & SOR & S47). rewrite ES.
    eapply implM_bind.
    { eapply (fwrite_spec (St:=PS)) with (f := fs) (s := map bv_unsigned src) (S := S) (lo := lo) (canary := rc_canary R)
        (Fp := Af) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf fs)) (closefn := F_STDIO_CLOSE) (readfn := F_STDIO_READ)
        (seekfn := F_STDIO_SEEK) (B := Af + FILE_BUF_OFF) (prev := pv) (next := nx) (mode := mode) (tail := tail) (bufbytes := bufbytes)
        (size := 1) (nmemb := Z.of_nat (length src)).
      all: try unfold fcells in *.
      all: rewrite ?BS in *. all: unfold BUFSIZ, FILE_BUF_OFF, FWRITE_DEPTH, got_ssp, ssp_guard in *.
      all: try fastfirst (first [ exact FC | exact BUF | exact BP | exact WB0 | exact ST | exact MI | exact SSP | exact FLsvb | rewrite NOWR in FLw; exact FLw
                 | change (map bv_unsigned src) with (of_bytes src); rewrite to_of_bytes; exact SRC'
                 | apply Forall_map; apply Forall_forall; intros b _; pose proof (bv_unsigned_in_range 8 b); unfold bv_modulus in *; cbn in *; (keep_hyps CEILV sp Af src b H0; lia)
                 | reflexivity
                 | unfold zlength; rewrite length_map; reflexivity
                 | unfold zlength; rewrite length_map; f_equal; (keep_hyps CEILV sp Af src S Shi S47; lia)
                 | rewrite NCH; exact FD
                 | unfold zlength in *; rewrite ?length_map; (keep_hyps CEILV sp Af src fs LENB lo LOB R LOR CEILLO SPM SP47 A0 FA4 FA5 WBL S S0; lia) ]). 
      (* [comment removed for export] *)
      all: try (unfold zlength; rewrite length_map;
                destruct SOR as [L0 | ->]; [left; exact L0 |];
                destruct (Z.eq_dec (Z.of_nat (length src)) 0) as [L0|L0]; [left; exact L0| right];
                pose proof (client_range_apart R CL FB (bv_unsigned sp) SRC (Z.of_nat (length src)) f Af 1264 BOK HIN CR ltac:((keep_hyps CEILV sp Af src L0; lia)) ltac:((keep_hyps CEILV sp R Af lo src LOR LOB CEILLO; lia)) ltac:((keep_hyps CEILV sp Af src; lia))) as AP;
                destruct (client_range_lo R s CL FB m (bv_unsigned sp) SRC (Z.of_nat (length src)) lo G CR ltac:((keep_hyps CEILV sp Af src L0; lia)) LOR ltac:((keep_hyps CEILV sp Af lo src LOB; lia))) as (C1 & C2 & C3 & C4);
                repeat split; (keep_hyps CEILV sp SRC lo src C2 R Af AP; lia)).
      all: match goal with |- implM _ _ _ _ _ => idtac | |- ?g => idtac "FWLEFT:" g end. }
    cbv beta. intros f' st' ms' (-> & INV' & PO).
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP').
    unfold store_file. apply implM_upd_lc. apply implM_ret. apply evt_done.
    unfold fx_W in MU. rewrite ?BS in MU. unfold BUFSIZ, FILE_BUF_OFF in MU.
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    assert (HW : Forall (stdio_iv R CL FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]).
    { unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
      - left. lia.
      - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
      - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia]. }
    split.
    { eapply agrees_on_weaken.
      - eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
        + left. lia.
        + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
        + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
      - intros a Ha. split; [exact Ha| intros X; exact X]. }
    split.
    { eapply (GIo_stdio_step R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| exact SPM|].
      cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
      assert (AGS : agrees_on (fun a => GI.stdio_static a) m m').
      { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. unfold GI.stdio_static in Hs. cbn [outside]. lia. }
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      Ltac trs AGS A := eapply agrees_rw_cells; [exact AGS | exact A | intros a Ha; unfold GI.stdio_static; cbn in Ha; lia].
      split. { eapply FILE_R_agree; [exact SO | exact AGS | intros a Ha; unfold GI.stdio_static; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; unfold GI.stdio_static; lia]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AGS | intros a Ha; unfold GI.stdio_static; lia | rewrite SEbs; intros a Ha; unfold GI.stdio_static; lia]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AGS | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; unfold GI.stdio_static; lia. }
      split; [trs AGS U1|]. split; [trs AGS U2|]. split; [trs AGS U3|]. split; [trs AGS OL|]. split; [trs AGS OH|].
      split.
      2:{ rewrite files_update_keys. exact ND. }
      apply UPD.
      - (* [comment removed for export] *)
        pose proof INV' as (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
        assert (RBN : f_rbuf fs = []) by (apply NORDi; rewrite NRW; reflexivity).
        assert (RBN' : f_rbuf f' = []) by (rewrite RB, RBN; destruct (f_wactive fs); reflexivity).
        rewrite RBN in FC'.
        exists flags, mode', (if f_wactive fs then rp else 0), tail, bufbytes'.
        rewrite WA, RBN', E1, E3, BS.
        split. { unfold fcells, BUFSIZ, FILE_BUF_OFF in *. rewrite ?BS in FC'; destruct (f_wactive fs); cbn [zlength length Z.of_nat] in FC' |- *; rewrite ?Z.add_0_r in FC' |- *; exact FC'. }
        split. { unfold flags_ok in *. rewrite E2, E4, E5, E6. exact FL. }
        split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite ?BS in BUF'; exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [rewrite BS in WBL'; exact WBL'|].
        split; [intros X; exfalso; exact (X eq_refl)|]. destruct (f_wactive fs); unfold zlength in RP |- *; cbn [length Z.of_nat]; (split; [lia| split; [lia| exact (proj2 (proj2 RP))]]).
      - exact (heap_file_inv_fx fs f' INV NOWR INV').
      - (* [comment removed for export] *)
        intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2 FR2 INV2.
        pose proof INV2 as (_ & _ & BS2 & _).
        destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB q2 A2 n2 FS ND HIN2) as (f2' & pv2' & nx2' & _ & En2 & _). subst n2.
        pose proof (file_block_facts R CL FB q2 A2 FILE_ALLOC BOK HIN2) as (B1 & B2 & B3 & B4 & B5 & B6). unfold FILE_ALLOC in B3, B4, B5, B6.
        assert (AP : A2 + 1264 <= Af \/ Af + 1264 <= A2).
        { destruct (GIo_apart K R s CL FB m (q2, A2, FILE_ALLOC) (f, Af, 1264) G ltac:(apply in_or_app; right; exact HIN2) ltac:(apply in_or_app; right; exact HIN)) as [E|AP].
          - exfalso. apply NE2. congruence.
          - unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
        eapply (FILE_R_agree (fun a => A2 <= a < A2 + 1264)); [exact FR2| | intros a Ha; lia | intros a Ha; rewrite BS2 in Ha; unfold BUFSIZ, FILE_BUF_OFF in Ha; lia].
        eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hb. cbn [outside]. (keep_hyps CEILV sp R Af lo src A2 a LOR CEILLO B4 AP Hb; lia). }
    split; [change (1 =? 0) with false; cbv iota; unfold zlength; rewrite length_map; reflexivity|]. unfold zlength. rewrite length_map. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_stdio_step_same : forall R (s : PS) CL FB m m' W SP,
    GIo K R s CL FB m -> munch W m m' -> wmono ssegs m m' ->
    Forall (stdio_iv R CL FB SP) W -> SP <= rc_spmain R ->
    STDIOR (ps_libc s) FB m' ->
    GIo K R s CL FB m'.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros R s CL FB m m' W SP G MU WM HW HSP SR'.
    pose proof (GIo_stdio_step R s CL FB m m' W SP (ps_libc s) G MU WM HW HSP SR') as G'.
    destruct s; cbn in G'. exact G'.
  Qed.

  (* [comment removed for export] *)
  Definition STDIOR_stack_only__stmt : Prop := forall (l : libc_st hptr) FB (CL : list cblk) R m m' W,
    STDIOR l FB m -> blocks_ok (utp R) (CL ++ FB) -> munch W m m' -> wmono ssegs m m' ->
    Forall (fun iv => CEILZ <= fst iv) W ->
    STDIOR l FB m'.
  Section Sz27.
  Variables l FB CL R m m' W : ltac2:(SecDiet.SzSec.tyM 'STDIOR_stack_only__stmt "vvvvvvv" @l).
  Lemma STDIOR_stack_only__body : ltac2:(SecDiet.SzSec.bodyP 'STDIOR_stack_only__stmt "vvvvvvv").
  Proof using Type. pin_using tt.
    intros SR BOK MU WM HW.
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    eapply (STDIOR_agree l FB m m' (fun a => a < CEILZ)); [exact SR| | |].
    - eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hc.
      eapply outside_of_Forall; [exact HW|]. intros [lo hi] X; cbn [fst snd] in *. lia.
    - intros a Ha. unfold GI.stdio_static in Ha. lia.
    - intros a Ha. destruct (in_block_facts _ _ a BO2 Ha) as (_ & X & _). exact X.
  Qed.
  End Sz27.
  Lemma STDIOR_stack_only : ltac:(let t := eval cbv delta [STDIOR_stack_only__stmt] in STDIOR_stack_only__stmt in exact t).
  Proof using Type. intros l FB CL R m m' W. ltac2:(SecDiet.SzSec.closeP 'STDIOR_stack_only__body "vvvvvvv"). Qed.

  Lemma ferr_clear : forall x, 0 <= x -> Z.land x F_ERR = 0 -> (x / 32) mod 2 = 0.
  Proof using Type. pin_using tt.
    intros x Hx HL. unfold F_ERR in HL.
    pose proof (Z.testbit_spec' x 5 ltac:(lia)) as T. change (2^5) with 32 in T. rewrite <- T.
    assert (E : Z.testbit x 5 = Z.testbit (Z.land x 32) 5).
    { rewrite Z.land_spec. replace (Z.testbit 32 5) with true by reflexivity. rewrite andb_true_r. reflexivity. }
    rewrite E, HL. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ferror_o_proof__stmt : Prop := ferror_stmt_o HO K.
  Section Sz29.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo : ltac2:(SecDiet.SzSec.tyM 'ferror_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ferror_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'ferror_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
    intros SPO HIN ->.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold FILE_BLOCK, STDIO_STACK in *.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    unfold s_ferror, Stdio.ferror. eapply implM_lookup_file; [exact LK|]. apply implM_ret.
    pose proof (bv_unsigned_in_range 64 flags) as FLR.
    eapply evt_mono.
    { unfold fcells in FC. eapply (ferror_spec ra sp gp tp) with (lo := lo); rewrite ?unsigned_lit by lia; [exact ST| exact FC| exact MI| lia| lia]. }
    cbv beta. intros ms' PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & FC').
    rewrite (ferr_clear (bv_unsigned flags) ltac:(lia) FLerr).
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply agrees_on_weaken; [eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia]|].
             - apply Forall_cons; [left; cbn; lia| apply Forall_nil].
             - intros a Ha. split; [exact Ha| intros X; exact X]. }
    split. { eapply (GIo_stdio_step_same R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| | exact SPM|].
             - apply Forall_cons; [left; cbn; lia| apply Forall_nil].
             - eapply (STDIOR_stack_only _ FB CL R m m'); [exact SR| exact BOK| exact MU| exact WM|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    split; [reflexivity|]. split; [reflexivity|]. intros X; discriminate X.
  Qed.
  End Sz29.
  Theorem ferror_o_proof : ltac:(let t := eval cbv delta [ferror_o_proof__stmt] in ferror_o_proof__stmt in exact t).
  Proof using EQB HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo. ltac2:(SecDiet.SzSec.closeP 'ferror_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fileno_o_proof__stmt : Prop := fileno_stmt_o HO K.
  Section Sz30.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo : ltac2:(SecDiet.SzSec.tyM 'fileno_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fileno_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fileno_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
    intros SPO HIN ->.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold FILE_BLOCK, STDIO_STACK in *.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    pose proof INV as (NCH & FD & BS & _).
    unfold s_fileno, Stdio.fileno. eapply implM_lookup_file; [exact LK|]. apply implM_ret.
    eapply evt_mono.
    { unfold fcells in FC. eapply (fileno_spec ra sp gp tp) with (lo := lo); rewrite ?unsigned_lit by lia; [exact ST| exact FC| exact MI| lia| lia| lia]. }
    cbv beta. intros ms' PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & FC').
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply agrees_on_weaken; [eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia]|].
             - apply Forall_cons; [left; cbn; lia| apply Forall_nil].
             - intros a Ha. split; [exact Ha| intros X; exact X]. }
    split. { eapply (GIo_stdio_step_same R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| | exact SPM|].
             - apply Forall_cons; [left; cbn; lia| apply Forall_nil].
             - eapply (STDIOR_stack_only _ FB CL R m m'); [exact SR| exact BOK| exact MU| exact WM|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    split; [reflexivity|]. split; [reflexivity|]. lia.
  Qed.
  End Sz30.
  Theorem fileno_o_proof : ltac:(let t := eval cbv delta [fileno_o_proof__stmt] in fileno_o_proof__stmt in exact t).
  Proof using EQB HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo. ltac2:(SecDiet.SzSec.closeP 'fileno_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stderr_inv_fx__stmt : Prop := forall f f', stderr_inv f -> fx_inv f f' -> stderr_inv f'.
  Section Sz31.
  Variables f f' : ltac2:(SecDiet.SzSec.tyM 'stderr_inv_fx__stmt "vv" @f).
  Lemma stderr_inv_fx__body : ltac2:(SecDiet.SzSec.bodyP 'stderr_inv_fx__stmt "vv").
  Proof using Type. pin_using tt.
    intros (CH & FD & BS & NRD & NWR & EOF & RB & SW & LB) (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB' & SW' & LB').
    unfold stderr_inv. rewrite E1, E2, E3, E4, E5, E6, RB', RB.
    split; [exact CH|]. split; [exact FD|]. split; [exact BS|]. split; [exact NRD|]. split; [exact NWR|]. split; [exact EOF|].
    split; [destruct (f_wactive f); reflexivity|].
    split; [destruct (f_stdoutw f'); [exfalso; pose proof (SW' eq_refl) as X; rewrite SW in X; discriminate X| reflexivity]|].
    destruct (f_lbf_nl f'); [exfalso; pose proof (LB' eq_refl) as X; rewrite LB in X; discriminate X| reflexivity].
  Qed.
  End Sz31.
  Lemma stderr_inv_fx : ltac:(let t := eval cbv delta [stderr_inv_fx__stmt] in stderr_inv_fx__stmt in exact t).
  Proof using Type. intros f f'. ltac2:(SecDiet.SzSec.closeP 'stderr_inv_fx__body "vv"). Qed.

  Theorem efwrite_proof : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.efwrite_stmt K.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros until bs. intros ([FB G] & ST & LOR & LOB & SPM & MI & Etp & AL) -> -> -> -> HSRC ROD LEN1.
    assert (SPO : std_pre_o K sp tp R s CL FB lo STDIO_STACK m) by (split; [exact G|]; split; [exact ST|]; split; [exact LOR|]; split; [exact LOB|]; split; [exact SPM|]; split; [exact MI|]; split; [exact Etp| exact AL]).
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (_ & SR & _ & _ & SSP & BOK & _ & _ & _ & _ & _ & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE in *.
    destruct SE as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    rewrite NW2 in FLw. rewrite BS2 in *.
    pose proof (bytes_at_bound _ _ _ _ HSRC) as BSRC.
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. unfold zlength in WBL. cbn [length] in WBL. lia. }
    unfold efwrite. apply implM_rd_lc.
    eapply implM_bind.
    { unfold A_STDERR, A_STDERR_BUF in *.
      eapply (fwrite_spec (St:=PS)) with (f := lc_stderr (ps_libc s)) (s := map bv_unsigned bs) (S := MSG) (lo := lo) (canary := rc_canary R)
        (Fp := 0x23660) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stderr (ps_libc s)))) (closefn := F_STDIO_CLOSE) (readfn := 0)
        (seekfn := F_STDIO_SEEK) (B := 0x54160) (prev := 0) (next := 0) (mode := mode) (tail := tail) (bufbytes := bufbytes)
        (size := Z.of_nat (length bs)) (nmemb := 1).
      all: try unfold fcells in *. all: rewrite ?BS2 in *.
      all: unfold FWRITE_DEPTH, got_ssp, ssp_guard in *.
      all: try fastfirst (first [ exact FC | exact BUF | exact BP | exact WB0 | exact ST | exact MI | exact SSP | exact FLsvb | exact FLw
                 | change (map bv_unsigned bs) with (of_bytes bs); rewrite to_of_bytes; exact HSRC
                 | apply Forall_map; apply Forall_forall; intros b _; pose proof (bv_unsigned_in_range 8 b); unfold bv_modulus in *; cbn in *; (keep_hyps CEILV sp bs b H0; lia)
                 | reflexivity
                 | unfold zlength; rewrite length_map; reflexivity
                 | unfold zlength; rewrite length_map; f_equal; (keep_hyps CEILV sp bs MSG ROD R lo LOR CEILLO; lia)
                 | rewrite CH2; right; exact FD2
                 | rewrite WBN; unfold zlength in *; rewrite ?length_map; cbn [length Z.of_nat]; (keep_hyps CEILV H hptr sp s bs R lo MSG ROD; lia)
                 | unfold zlength in *; rewrite ?length_map; (keep_hyps CEILV H hptr sp s MSG bs ROD lo LOB R LOR CEILLO SPM SP47; lia) ]).
      all: try (right; unfold zlength; rewrite length_map; repeat split; lia). }
    cbv beta. intros f' st' ms' (-> & INV' & PO).
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP').
    apply implM_upd_lc_last. apply evt_done.
    unfold fx_W in MU. rewrite ?BS2 in MU. unfold A_STDERR, A_STDERR_BUF in *.
    unfold out_post. exists u0, u1, u2, (Z_to_bv 64 (if Z.of_nat (length bs) =? 0 then 0 else 1)), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    assert (HW : Forall (stdio_iv R CL FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (0x23660, 0x23660 + 232); (0x54160, 0x54160 + 0)]).
    { unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd]; [left; lia| right; right; left; lia| right; right; right; lia]. }
    split.
    { eapply agrees_on_weaken; [eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia]|].
      - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd]; [left; lia| right; right; left; lia| right; right; right; left; lia].
      - intros a Ha. split; [exact Ha| intros X; exact X]. }
    exists FB.
    eapply (GIo_stdio_step R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| exact SPM|].
    cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_stderr].
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof SOI as (_ & _ & SObs & _).
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    Ltac trw MU WM A := eapply rw_cells_transport; [exact A | exact MU | exact WM | cbn; lia].
    split. { eapply FILE_R_transport; [exact SO| exact MU| exact WM| | | rewrite SObs; unfold BUFSIZ; lia].
             - repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
             - rewrite SObs. unfold BUFSIZ. repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil. }
    split; [exact SOI|].
    split. { pose proof INV' as (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
             assert (RBN' : f_rbuf f' = []) by (rewrite RB, RB2; destruct (f_wactive (lc_stderr (ps_libc s))); reflexivity).
             rewrite RB2 in FC'.
             exists flags, mode', (if f_wactive (lc_stderr (ps_libc s)) then rp else 0), tail, bufbytes'.
             rewrite WA, RBN', E1, E3, BS2.
             split. { unfold fcells in *. rewrite ?BS2 in FC'. destruct (f_wactive (lc_stderr (ps_libc s))); cbn [zlength length Z.of_nat] in FC' |- *; rewrite ?Z.add_0_r in FC' |- *; exact FC'. }
             split. { unfold flags_ok in *. rewrite E2, E4, E5, E6. rewrite NW2 in FL |- *. exact FL. }
             split; [rewrite ?BS2 in BUF'; exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [rewrite ?BS2 in WBL'; exact WBL'|].
             split; [intros X; exfalso; exact (X eq_refl)|]. destruct (f_wactive (lc_stderr (ps_libc s))); unfold zlength in RP |- *; cbn [length Z.of_nat]; (split; [lia| split; [lia| exact (proj2 (proj2 RP))]]). }
    split; [exact (stderr_inv_fx _ _ SEI INV')|].
    split. { eapply rw_cells_transport; [exact SIN | exact MU | exact WM |]. unfold stdin_cells. rewrite file_cells_size. cbn. lia. }
    split; [trw MU WM U1|]. split; [trw MU WM U2|]. split; [trw MU WM U3|]. split; [trw MU WM OL|]. split; [trw MU WM OH|].
    split; [| exact ND].
    eapply files_R_transport; [exact FS| exact MU| exact WM|].
    apply Forall_forall. intros [lo' hi'] Hiv. apply Forall_forall. intros [[q' A'] n'] Hb. cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) BO2 _ Hb) as (K1 & K2 & K3 & K4 & K5 & K6). unfold cb_addr, cb_size in *. cbn [fst snd] in *.
    cbn in Hiv. destruct Hiv as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  Qed.


End Glue.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP.TwB.
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
Section Agree.
  Context {hptr : Type}.
  Notation cblk := (@cblock hptr).

  Definition FILE_R_agree__stmt : Prop := forall P m m' f Fp BA closefn readfn seekfn prev next,
    FILE_R m f Fp BA closefn readfn seekfn prev next ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> P a) -> (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    FILE_R m' f Fp BA closefn readfn seekfn prev next.
  Section Sz1.
  Variables P m m' f Fp BA closefn readfn seekfn prev next : ltac2:(SecDiet.SzSec.tyM 'FILE_R_agree__stmt "vvvvvvvvvvv" @P).
  Lemma FILE_R_agree__body : ltac2:(SecDiet.SzSec.bodyP 'FILE_R_agree__stmt "vvvvvvvvvvv").
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros FR AG HP1 HP2.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - eapply agrees_rw_cells; [exact AG | exact FC |]. unfold fcells. rewrite file_cells_size. intros a Ha. apply HP1. lia.
    - pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
      eapply agrees_rw_cells; [exact AG | exact BUF |]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP2. lia.
  Qed.
  End Sz1.
  Lemma FILE_R_agree : ltac:(let t := eval cbv delta [FILE_R_agree__stmt] in FILE_R_agree__stmt in exact t).
  Proof using CEILV. intros P m m' f Fp BA closefn readfn seekfn prev next. ltac2:(SecDiet.SzSec.closeP 'FILE_R_agree__body "vvvvvvvvvvv"). Qed.

  Lemma files_R_agree : forall fs (FB : list cblk) P m m' prev,
    files_R m prev fs FB -> agrees_on P m m' ->
    (forall a, in_block FB a -> P a) ->
    files_R m' prev fs FB.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    induction fs as [|[q f] fs IH]; intros [|[[q' A] n] FB] P m m' prev H AG HP; cbn in H |- *; try exact H.
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    pose proof INV as INV'. destruct INV as (_ & _ & BS & _).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
    split.
    { eapply FILE_R_agree; [exact FR | exact AG | |].
      + intros a Ha. apply HP. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold FILE_ALLOC. lia.
      + intros a Ha. apply HP. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. rewrite BS in Ha. unfold FILE_ALLOC, FILE_BUF_OFF, BUFSIZ in *. lia. }
    split; [exact INV'|].
    eapply IH; [exact REST | exact AG |]. intros a Ha. apply HP. unfold in_block in *. apply Exists_cons_tl. exact Ha.
  Qed.

  Lemma STDIOR_agree : forall (l : libc_st hptr) FB m m' P,
    STDIOR l FB m -> agrees_on P m m' ->
    (forall a, S3.GI.TwB.stdio_static a -> P a) -> (forall a, in_block FB a -> P a) ->
    STDIOR l FB m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros l FB m m' P SR AG HS HB.
    destruct SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold S3.GI.TwB.stdio_static in HS.
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SOI as SOI'. pose proof SEI as SEI'.
    destruct SOI as (_ & _ & SObs & _). destruct SEI as (_ & _ & SEbs & _).
    unfold STDIOR. unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD.
    Ltac tra AG HS A := eapply agrees_rw_cells; [exact AG | exact A | intros a Ha; apply HS; cbn in Ha; lia].
    split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HS; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HS; lia]. }
    split; [exact SOI'|].
    split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HS; lia | rewrite SEbs; intros a Ha; apply HS; lia]. }
    split; [exact SEI'|].
    split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HS; lia. }
    split; [tra AG HS U1|]. split; [tra AG HS U2|]. split; [tra AG HS U3|]. split; [tra AG HS OL|]. split; [tra AG HS OH|].
    split; [| exact ND].
    eapply files_R_agree; [exact FS | exact AG | exact HB].
  Qed.
End Agree.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Files.
  Context {hptr : Type} (ptr_eqb : hptr -> hptr -> bool).
  Hypothesis EQB : forall p q, ptr_eqb p q = true <-> p = q.
  Notation cblk := (@cblock hptr).

  Lemma eqb_refl' : forall p, ptr_eqb p p = true.
  Proof using EQB. pin_using (fun (EQB : unit) => tt). intros p. apply (proj2 (EQB p p)). reflexivity. Qed.
  Lemma eqb_neq : forall p q, p <> q -> ptr_eqb p q = false.
  Proof using EQB. pin_using (fun (EQB : unit) => tt). intros p q NE. destruct (ptr_eqb p q) eqn:E; [|reflexivity]. exfalso. apply NE. apply (proj1 (EQB p q)). exact E. Qed.

  (* [comment removed for export] *)
  Lemma files_R_toks : forall m prev fs (FB : list cblk), files_R m prev fs FB -> map cb_tok FB = map fst fs.
  Proof using Type. pin_using tt.
    intros m prev fs; revert prev.
    induction fs as [|[q f] fs IH]; intros prev [|[[q' A] n] FB] H; cbn in H |- *; try reflexivity; try contradiction.
    destruct H as (-> & _ & _ & _ & _ & _ & REST). f_equal. eapply IH. exact REST.
  Qed.

  (* [comment removed for export] *)
  Definition files_R_pick__stmt : Prop := forall m prev fs (FB : list cblk) q A n,
    files_R m prev fs FB -> List.NoDup (map fst fs) -> In (q, A, n) FB ->
    exists f pv nx,
      files_lookup ptr_eqb fs q = Some f /\ In (q, f) fs /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx
      /\ heap_file_inv f.
  Section Sz6.
  Variables m prev : ltac2:(SecDiet.SzSec.tyM 'files_R_pick__stmt "vvk" @m).
  Lemma files_R_pick__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_pick__stmt "vvk").
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros fs; revert prev.
    induction fs as [|[q1 f1] fs IH]; intros prev [|[[q1' A1] n1] FB] q A n H ND HIN; cbn in H; try contradiction; try (exfalso; exact HIN).
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    destruct HIN as [E | HIN].
    - injection E as <- <- <-. exists f1, prev, (hd_addr FB). cbn [files_lookup]. rewrite eqb_refl'.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR| exact INV].
    - destruct (IH A1 FB q A n REST ND HIN) as (f & pv & nx & LK & INf & En & B0 & Bhi & FRf & INVf).
      assert (NE : q1 <> q).
      { intros ->. apply NI. change q with (fst (q, f)). apply in_map. exact INf. }
      exists f, pv, nx. cbn [files_lookup]. rewrite (eqb_neq _ _ NE).
      split; [exact LK|]. split; [right; exact INf|]. split; [exact En|]. split; [exact B0|]. split; [exact Bhi|]. split; [exact FRf| exact INVf].
  Qed.
  End Sz6.
  Lemma files_R_pick : ltac:(let t := eval cbv delta [files_R_pick__stmt] in files_R_pick__stmt in exact t).
  Proof using EQB. intros m prev fs. ltac2:(SecDiet.SzSec.closeP 'files_R_pick__body "vvk"). Qed.

  (* [comment removed for export] *)
  Definition files_R_frame__stmt : Prop := forall m m' prev fs (FB : list cblk),
    files_R m prev fs FB ->
    (forall q2 A2 n2 f2 pv nx, In (q2, A2, n2) FB ->
                     FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f2 ->
                     FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx) ->
    files_R m' prev fs FB.
  Section Sz7.
  Variables m m' prev FB : ltac2:(SecDiet.SzSec.tyM 'files_R_frame__stmt "vvvkv" @m).
  Lemma files_R_frame__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_frame__stmt "vvvkv").
  Proof using Type. pin_using tt.
    intros fs.
 revert prev FB.
    induction fs as [|[q3 f3] fs IH]; intros pv0 [|[[q3' A3] n3] FB] H HF; cbn in H |- *; try exact H.
    destruct H as (-> & -> & B0 & Bhi & FR3 & INV3 & REST3).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
    split; [exact (HF q3 A3 FILE_ALLOC f3 pv0 (hd_addr FB) (or_introl eq_refl) FR3 INV3)|]. split; [exact INV3|].
    apply IH; [exact REST3|]. intros q2 A2 n2 f2 pv nx HIN2. apply (HF q2 A2 n2 f2 pv nx (or_intror HIN2)).
  Qed.
  End Sz7.
  Lemma files_R_frame : ltac:(let t := eval cbv delta [files_R_frame__stmt] in files_R_frame__stmt in exact t).
  Proof using Type. intros m m' prev fs FB. ltac2:(SecDiet.SzSec.closeP 'files_R_frame__body "vvvkv"). Qed.

  Lemma files_update_keys : forall fs q f', map fst (files_update ptr_eqb fs q f') = map fst fs.
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q f'; cbn; [reflexivity|].
    destruct (ptr_eqb k q); cbn; [reflexivity| f_equal; apply IH].
  Qed.

  Lemma files_remove_keys : forall fs q, incl (map fst (files_remove ptr_eqb fs q)) (map fst fs).
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q; cbn; [apply incl_refl|].
    destruct (ptr_eqb k q); cbn.
    - apply incl_tl, incl_refl.
    - apply incl_cons; [left; reflexivity| apply incl_tl, IH].
  Qed.

  Lemma files_lookup_In : forall fs q f, List.NoDup (map fst fs) -> In (q, f) fs -> files_lookup ptr_eqb fs q = Some f.
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    induction fs as [|[k g] fs IH]; intros q f ND HIN; [destruct HIN|].
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND]. cbn.
    destruct HIN as [E|HIN].
    - injection E as -> ->. rewrite eqb_refl'. reflexivity.
    - assert (NE : k <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact HIN).
      rewrite (eqb_neq _ _ NE). apply IH; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition files_R_focus__stmt : Prop := forall m prev fs (FB : list cblk) q A n,
    files_R m prev fs FB -> List.NoDup (map fst fs) -> In (q, A, n) FB ->
    exists f pv nx,
      files_lookup ptr_eqb fs q = Some f /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx
      /\ heap_file_inv f
      /\ (forall m' f', FILE_R m' f' A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
            (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) FB -> q2 <> q ->
                     FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
                     FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
            files_R m' prev (files_update ptr_eqb fs q f') FB).
  Section Sz11.
  Variables m prev : ltac2:(SecDiet.SzSec.tyM 'files_R_focus__stmt "vvk" @m).
  Lemma files_R_focus__body : ltac2:(SecDiet.SzSec.bodyP 'files_R_focus__stmt "vvk").
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros fs; revert prev.
    induction fs as [|[q1 f1] fs IH]; intros prev [|[[q1' A1] n1] FB] q A n H ND HIN; cbn in H; try contradiction; try (exfalso; exact HIN).
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    pose proof (files_R_toks _ _ _ _ REST) as TK.
    destruct HIN as [E | HIN].
    - injection E as <- <- <-. exists f1, prev, (hd_addr FB). cbn [files_lookup files_update]. rewrite eqb_refl'.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR|]. split; [exact INV|].
      intros m' f' FR' INV' HF. cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR'|]. split; [exact INV'|].
      eapply files_R_frame; [exact REST|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2. apply (HF q2 A2 n2 f2 pv2 nx2 (or_intror HIN2)).
      intros ->. apply NI. rewrite <- TK. change q1 with (cb_tok (q1, A2, n2)). apply in_map. exact HIN2.
    - destruct (IH A1 FB q A n REST ND HIN) as (f & pv & nx & LK & En & B0 & Bhi & FRf & INVf & UPD).
      assert (NE : q1 <> q).
      { intros ->. apply NI. rewrite <- TK. change q with (cb_tok (q, A, n)). apply in_map. exact HIN. }
      exists f, pv, nx. cbn [files_lookup files_update]. rewrite (eqb_neq _ _ NE).
      split; [exact LK|]. split; [exact En|]. split; [exact B0|]. split; [exact Bhi|]. split; [exact FRf|]. split; [exact INVf|].
      intros m' f' FR' INV' HF. cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact (HF q1 A1 FILE_ALLOC f1 prev (hd_addr FB) (or_introl eq_refl) NE FR INV)|].
      split; [exact INV|].
      apply UPD; [exact FR'| exact INV'|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2. apply (HF q2 A2 n2 f2 pv2 nx2); [right; exact HIN2| exact NE2].
  Qed.
  End Sz11.
  Lemma files_R_focus : ltac:(let t := eval cbv delta [files_R_focus__stmt] in files_R_focus__stmt in exact t).
  Proof using EQB. intros m prev fs. ltac2:(SecDiet.SzSec.closeP 'files_R_focus__body "vvk"). Qed.
End Files.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glue.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.

  (* [comment removed for export] *)
  Theorem stdio_fp_proof : stdio_fp_law K.
  Proof using CEILV KST. pin_using (fun (CEILV KST : unit) => tt).
    intros l R FB m m' MS AG. apply (proj2 (KST l R FB m')).
    eapply STDIOR_agree; [apply (proj1 (KST l R FB m)); exact MS | exact AG | |].
    - intros a Ha. left. exact Ha.
    - intros a Ha. right. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma core_ssp : forall R m, CORE_LIBC R m -> ssp_cells m (rc_canary R).
  Proof using Type. pin_using tt. intros R m (_ & G & U & _). split; [exact G | exact U]. Qed.

  (* [comment removed for export] *)
  Definition stdio_iv (R : rctx) (CL FB : list cblk) (SP : Z) (iv : Z * Z) : Prop :=
    (CEILZ <= fst iv /\ snd iv <= rc_spmain R) \/ iv_in_block (CL ++ FB) iv
    \/ (0x23e20 <= fst iv /\ snd iv <= 0x240f0) \/ (0x54908 <= fst iv /\ snd iv <= 0x55130).

  Lemma in_block_of_iv : forall (LB : list cblk) iv a, iv_in_block LB iv -> fst iv <= a < snd iv -> in_block LB a.
  Proof using Type. pin_using tt.
    intros LB iv a Hiv Ha. unfold iv_in_block, in_block in *. apply Exists_exists in Hiv as (b & Hb & H1 & H2).
    apply Exists_exists. exists b. split; [exact Hb| lia].
  Qed.

  (* [comment removed for export] *)
  Definition GIo_stdio_step__stmt : Prop := forall R (s : PS) CL FB m m' W SP l',
    GIo K R s CL FB m -> munch W m m' -> wmono usegs m m' ->
    Forall (stdio_iv R CL FB SP) W -> SP <= rc_spmain R ->
    STDIOR l' FB m' ->
    GIo K R (set_libc l' s) CL FB m'.
  Section Sz15.
  Variables R s CL FB m m' W SP l' : ltac2:(SecDiet.SzSec.tyM 'GIo_stdio_step__stmt "vvvvvvvvv" @R).
  Lemma GIo_stdio_step__body : ltac2:(SecDiet.SzSec.bodyP 'GIo_stdio_step__stmt "vvvvvvvvv").
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros G MU WM HW HSP SR'.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA].
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold rc_spmain in HSP. unfold stdio_iv, rc_spmain in HW.
    (* [comment removed for export] *)
    assert (OUT : forall a, 0 <= a < 2^64 ->
              ~ (CEILZ <= a < usp0 R - 48) -> ~ in_block (CL ++ FB) a -> ~ (0x23e20 <= a < 0x240f0) -> ~ (0x54908 <= a < 0x55130) -> outside W a).
    { intros a Ha N1 N2 N3 N4. eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd].
      destruct Hiv as [X|[X|[X|X]]]; cbn [fst snd] in X; try lia.
      intros Hin. apply N2. eapply in_block_of_iv; [exact X| cbn [fst snd]; lia]. }
    assert (BF : forall a, in_block (CL ++ FB) a -> 0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x56000 <= a) /\ (a < utp R - 200 \/ utp R - 200 + 4096 <= a)).
    { intros a Ha. exact (in_block_facts (utp R) (CL ++ FB) a BO Ha). }
    unfold GIo, set_libc. cbn [ps_heap ps_libc ps_outfile ps_tls].
    split.
    { eapply HFL; [exact HH| exact MU| exact WM|].
      apply Forall_forall. intros [lo hi] Hiv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as X. unfold heap_client_iv, stdio_iv in *. cbn [fst snd] in *.
      destruct X as [X|[X|[X|X]]]; [left; lia | right; left; exact X | right; right; left; lia | right; right; left; lia]. }
    split; [apply (proj2 (KST l' R FB m')); exact SR'|].
    split. { eapply HARNR_agree; [| |exact HA]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT.
             - exact Ha.
             - lia.
             - intros Hb; destruct (BF a Hb); lia.
             - lia.
             - lia. }
    split. { eapply CORE_TLS_agree; [| |exact CT]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT.
             - exact Ha.
             - clear - Hp TBC. lia.
             - intros Hb; destruct (BF a Hb); lia.
             - lia.
             - lia. }
    split. { eapply PCAP_TLS_agree; [| |exact PT]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
    split. { eapply CORE_LIBC_agree; [| |exact CLI]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
    split. { eapply CORE_MISC_agree; [| |exact CM]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
    split. { eapply CORE_EXIT_agree; [| |exact CE]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
    split. { eapply CORE_STK_agree; [| |exact CS]. 2:{ intros a Hp; exact Hp. }
             eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hp. hnf in Hp.
             apply OUT; [exact Ha| lia| intros Hb; destruct (BF a Hb); lia| lia| lia]. }
    split; [exact Etls|]. split; [exact TB|]. split; [exact BOK| exact SPW].
  Qed.
  End Sz15.
  Lemma GIo_stdio_step : ltac:(let t := eval cbv delta [GIo_stdio_step__stmt] in GIo_stdio_step__stmt in exact t).
  Proof using HFL KST. intros R s CL FB m m' W SP l'. ltac2:(SecDiet.SzSec.closeP 'GIo_stdio_step__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition keeps_of_stdio__stmt : Prop := forall R (s : PS) CL FB m m' W SP (X : Z -> Prop),
    GIo K R s CL FB m -> munch W m m' -> wmono usegs m m' ->
    Forall (fun iv => (CEILZ <= fst iv /\ snd iv <= SP) \/ iv_in_block FB iv
                      \/ (0x23e20 <= fst iv /\ snd iv <= 0x240f0) \/ (0x54908 <= fst iv /\ snd iv <= 0x55130)
                      \/ (forall a, fst iv <= a < snd iv -> X a)) W ->
    CEILZ <= SP ->
    agrees_on (fun a => client_keeps CL SP a /\ ~ X a) m m'.
  Section Sz16.
  Variables R s CL FB m m' W SP X : ltac2:(SecDiet.SzSec.tyM 'keeps_of_stdio__stmt "vvvvvvvvv" @R).
  Lemma keeps_of_stdio__body : ltac2:(SecDiet.SzSec.bodyP 'keeps_of_stdio__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G MU WM HW HSP.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [Hk NX].
    eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd]. intros Hin.
    destruct Hk as [Hk|Hk].
    - destruct Hiv as [Y|[Y|[Y|[Y|Y]]]]; cbn [fst snd] in Y; try lia.
      + pose proof (in_block_facts (utp R) FB a BO2 (in_block_of_iv FB (lo, hi) a Y ltac:(cbn; lia))) as (F1 & F2 & F3 & F4). lia.
      + exact (NX (Y a Hin)).
    - pose proof (in_block_facts (utp R) CL a BO1 Hk) as (F1 & F2 & F3 & F4).
      destruct Hiv as [Y|[Y|[Y|[Y|Y]]]]; cbn [fst snd] in Y; try lia.
      + apply in_block_In in Hk as (b & HbIn & Hb). pose proof (in_block_of_iv FB (lo, hi) a Y ltac:(cbn; lia)) as Hk'.
        apply in_block_In in Hk' as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia.
      + exact (NX (Y a Hin)).
  Qed.
  End Sz16.
  Lemma keeps_of_stdio : ltac:(let t := eval cbv delta [keeps_of_stdio__stmt] in keeps_of_stdio__stmt in exact t).
  Proof using Type. intros R s CL FB m m' W SP X. ltac2:(SecDiet.SzSec.closeP 'keeps_of_stdio__body "vvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation eqb := (ho_eqb HO).

  Lemma implM_lookup_file : forall {B} h (k : file_st -> M PS B) (s : PS) Q ms f,
    files_lookup eqb (lc_files (ps_libc s)) h = Some f ->
    implM usegs (k f) s Q ms -> implM usegs (mbind (lookup_file ps_libc eqb h) k) s Q ms.
  Proof using Type. pin_using tt.
    intros B h k s Q ms f LK IM. unfold implM, lookup_file, rd_lc, mbind, mget, mret in *.
    cbn [ebind bind fst snd]. rewrite LK. cbn [ebind bind fst snd]. exact IM.
  Qed.

  Lemma implM_upd_lc : forall {B} (g : libc_st hptr -> libc_st hptr) (k : unit -> M PS B) (s : PS) Q ms,
    implM usegs (k tt) (set_libc (g (ps_libc s)) s) Q ms -> implM usegs (mbind (upd_lc ps_libc set_libc g) k) s Q ms.
  Proof using Type. pin_using tt. intros. exact H0. Qed.

  Lemma implM_upd_lc_last : forall (g : libc_st hptr -> libc_st hptr) (s : PS) (Q : unit -> PS -> machine_state -> Prop) ms,
    evt usegs (Q tt (set_libc (g (ps_libc s)) s)) ms -> implM usegs (upd_lc ps_libc set_libc g) s Q ms.
  Proof using Type. pin_using tt. intros g s Q ms Hq. unfold upd_lc. apply implM_upd. exact Hq. Qed.

  Lemma implM_rd_lc : forall {B} (k : libc_st hptr -> M PS B) (s : PS) Q ms,
    implM usegs (k (ps_libc s)) s Q ms -> implM usegs (mbind (rd_lc ps_libc) k) s Q ms.
  Proof using Type. pin_using tt. intros. exact H0. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition spo_facts__stmt : Prop := forall sp tp R (s : PS) CL FB lo budget m,
    std_pre_o K sp tp R s CL FB lo budget m ->
    GIo K R s CL FB m /\ STDIOR (ps_libc s) FB m /\ stk usegs m lo (bv_unsigned sp) /\ mem_inv usegs m
    /\ ssp_cells m (rc_canary R) /\ blocks_ok (utp R) (CL ++ FB)
    /\ rc_lo R <= lo /\ lo + budget <= bv_unsigned sp /\ bv_unsigned sp <= rc_spmain R /\ tp = rc_tp R /\ bv_unsigned sp mod 16 = 0
    /\ CEILZ <= rc_lo R /\ rc_spmain R + 48 <= 2^47.
  Section Sz21.
  Variables sp tp R s CL FB lo budget m : ltac2:(SecDiet.SzSec.tyM 'spo_facts__stmt "vvvvvvvvv" @sp).
  Lemma spo_facts__body : ltac2:(SecDiet.SzSec.bodyP 'spo_facts__stmt "vvvvvvvvv").
  Proof using KST. pin_using (fun (KST : unit) => tt).
    intros (G & ST & LOR & LOB & SPM & MI & Etp & AL).
    pose proof G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    split; [exact G|]. split; [apply (proj1 (KST _ R _ _)); exact HS|]. split; [exact ST|]. split; [exact MI|].
    split; [exact (core_ssp R m CLI)|]. split; [exact BOK|].
    split; [exact LOR|]. split; [exact LOB|]. split; [exact SPM|]. split; [exact Etp|]. split; [exact AL|].
    unfold rc_lo, rc_spmain in *. lia.
  Qed.
  End Sz21.
  Lemma spo_facts : ltac:(let t := eval cbv delta [spo_facts__stmt] in spo_facts__stmt in exact t).
  Proof using KST. intros sp tp R s CL FB lo budget m. ltac2:(SecDiet.SzSec.closeP 'spo_facts__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma file_block_facts : forall R (CL FB : list cblk) q A n,
    blocks_ok (utp R) (CL ++ FB) -> In (q, A, n) FB ->
    0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= CEILZ /\ (A + n <= 0x10000 \/ 0x56000 <= A) /\ (A + n <= utp R - 200 \/ utp R - 200 + 4096 <= A).
  Proof using Type. pin_using tt.
    intros R CL FB q A n [BO _] HIN.
    pose proof (proj1 (Forall_forall _ _) BO (q, A, n) ltac:(apply in_or_app; right; exact HIN)) as X.
    unfold block_ok, cb_addr, cb_size in X. cbn [fst snd] in X. exact X.
  Qed.

  (* [comment removed for export] *)
  Definition client_range_apart__stmt : Prop := forall R (CL FB : list cblk) SP S len q A n,
    blocks_ok (utp R) (CL ++ FB) -> In (q, A, n) FB ->
    client_range R CL SP S len -> 0 < len -> CEILZ <= SP -> 0 < n ->
    S + len <= A \/ A + n <= S.
  Section Sz23.
  Variables R CL FB SP S len q A n : ltac2:(SecDiet.SzSec.tyM 'client_range_apart__stmt "vvvvvvvvv" @R).
  Lemma client_range_apart__body : ltac2:(SecDiet.SzSec.bodyP 'client_range_apart__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros BOK HIN CR LEN HSP NPOS.
    pose proof BOK as [BO BA]. pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    pose proof (file_block_facts R CL FB q A n BOK HIN) as (A1 & A2 & A3 & A4 & A5 & A6).
    destruct CR as [CR | CR].
    - destruct (Z_lt_le_dec S (A + n)); [|right; lia]. destruct (Z_lt_le_dec A (S + len)); [|left; lia]. exfalso.
      pose proof (CR (Z.max S A) ltac:(lia)) as Hin. apply in_block_In in Hin as (b & HbIn & Hb).
      pose proof (BAX b (q, A, n) HbIn HIN) as AP. unfold apart, cb_addr, cb_size in AP, Hb. cbn [fst snd] in AP, Hb. lia.
    - right. lia.
  Qed.
  End Sz23.
  Lemma client_range_apart : ltac:(let t := eval cbv delta [client_range_apart__stmt] in client_range_apart__stmt in exact t).
  Proof using Type. intros R CL FB SP S len q A n. ltac2:(SecDiet.SzSec.closeP 'client_range_apart__body "vvvvvvvvv"). Qed.

  Definition client_range_lo__stmt : Prop := forall R (s : PS) (CL FB : list cblk) m SP S len lo,
    GIo K R s CL FB m -> client_range R CL SP S len -> 0 < len -> rc_lo R <= lo -> lo <= SP ->
    0 < S /\ (S + len <= lo \/ SP <= S) /\ S + len <= 2^47
    /\ (S + len <= 0x10000 \/ 0x56000 <= S \/ SP <= S).
  Section Sz24.
  Variables R s CL FB m SP S len lo : ltac2:(SecDiet.SzSec.tyM 'client_range_lo__stmt "vvvvvvvvv" @R).
  Lemma client_range_lo__body : ltac2:(SecDiet.SzSec.bodyP 'client_range_lo__stmt "vvvvvvvvv").
  Proof using Type. pin_using tt.
    intros G CR LEN LOR LOS.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    destruct CR as [CR | CR]; unfold rc_lo, rc_spmain in *.
    - destruct (in_block_facts _ _ S BO1 (CR S ltac:(lia))) as (X1 & X2 & X3 & X4).
      destruct (in_block_facts _ _ (S + len - 1) BO1 (CR (S + len - 1) ltac:(lia))) as (Y1 & Y2 & Y3 & Y4).
      split; [lia|]. split; [left; lia|]. split; [lia|].
      destruct (Z_le_gt_dec (S + len) 0x10000); [left; lia|]. destruct (Z_le_gt_dec 0x56000 S); [right; left; lia|]. exfalso.
      destruct (in_block_facts _ _ (Z.max S 0x10000) BO1 (CR (Z.max S 0x10000) ltac:(lia))) as (W1 & W2 & W3 & W4). lia.
    - split; [lia|]. split; [right; lia|]. split; [lia|]. right; right; lia.
  Qed.
  End Sz24.
  Lemma client_range_lo : ltac:(let t := eval cbv delta [client_range_lo__stmt] in client_range_lo__stmt in exact t).
  Proof using Type. intros R s CL FB m SP S len lo. ltac2:(SecDiet.SzSec.closeP 'client_range_lo__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition heap_file_inv_fx__stmt : Prop := forall f f', heap_file_inv f -> f_nowr f = false -> fx_inv f f' -> heap_file_inv f'.
  Section Sz25.
  Variables f f' : ltac2:(SecDiet.SzSec.tyM 'heap_file_inv_fx__stmt "vv" @f).
  Lemma heap_file_inv_fx__body : ltac2:(SecDiet.SzSec.bodyP 'heap_file_inv_fx__stmt "vv").
  Proof using Type. pin_using tt.
    intros (NCH & FD & BS & NRW & NOWRi & NORDi & RBR) NOWR (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
    unfold heap_file_inv. rewrite E1, E2, E3, E4, E5. rewrite NOWR in *.
    split; [exact NCH|]. split; [exact FD|]. split; [exact BS|].
    split; [exact NRW|]. split; [intros X; discriminate X|].
    split; [intros Hn; rewrite RB; rewrite (NORDi Hn); destruct (f_wactive f); reflexivity|].
    rewrite RB. destruct (f_wactive f); [exact RBR| apply Forall_nil].
  Qed.
  End Sz25.
  Lemma heap_file_inv_fx : ltac:(let t := eval cbv delta [heap_file_inv_fx__stmt] in heap_file_inv_fx__stmt in exact t).
  Proof using Type. intros f f'. ltac2:(SecDiet.SzSec.closeP 'heap_file_inv_fx__body "vv"). Qed.

  Theorem fwrite_o_proof : fwrite_stmt_o HO K.
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
    intros until src. intros SPO HIN -> -> -> -> HSRC CR LENB.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    specialize (LENB fs LK).
    pose proof (file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold FILE_BLOCK, STDIO_STACK in *.
    pose proof (bytes_at_bound _ _ _ _ HSRC) as BSRC.
    unfold s_fwrite, Stdio.fwrite, with_file_.
    apply implM_bind_assoc. eapply implM_lookup_file; [exact LK|].
    apply implM_bind_assoc.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct (f_nowr fs) eqn:NOWR.
    { (* [comment removed for export] *)
      destruct (NOWRi eq_refl) as [WACT _].
      unfold fwrite_file, fwritex, ensure_w. rewrite WACT. unfold towrite. rewrite NOWR.
      apply implM_bind_assoc. cbn [mbind munr ebind bind]. apply implM_unr. }
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    (* [comment removed for export] *)
    assert (HS : exists S, (Z_to_bv 64 SRC : word) = Z_to_bv 64 S /\ 0 <= S /\ S + Z.of_nat (length src) < 2^64 /\ bytes_at usegs m S src
                 /\ (Z.of_nat (length src) = 0 \/ S = SRC)
                 /\ (Z.of_nat (length src) = 0 \/ S + Z.of_nat (length src) <= 2^47)).   (* [comment removed for export] *)
    { destruct (Z.eq_dec (Z.of_nat (length src)) 0) as [L0|L0].
      - exists (SRC mod 2^64). split; [symmetry; apply Z_to_bv_mod64|]. pose proof (Z.mod_pos_bound SRC (2^64) ltac:(lia)).
        split; [lia|]. split; [lia|]. split; [| split; left; exact L0]. destruct src; [| cbn in L0; lia]. apply bytes_at_nil. lia.
      - exists SRC. destruct (client_range_lo R s CL FB m (bv_unsigned sp) SRC (Z.of_nat (length src)) lo G CR ltac:(lia) LOR ltac:(lia)) as (C1 & C2 & C3 & C4).
        split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact HSRC|]. split; [right; reflexivity | right; lia]. }
    destruct HS as (S & ES & S0 & Shi & SRC' & SOR & S47). rewrite ES.
    eapply implM_bind.
    { eapply (fwrite_spec (St:=PS)) with (f := fs) (s := map bv_unsigned src) (S := S) (lo := lo) (canary := rc_canary R)
        (Fp := Af) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf fs)) (closefn := F_STDIO_CLOSE) (readfn := F_STDIO_READ)
        (seekfn := F_STDIO_SEEK) (B := Af + FILE_BUF_OFF) (prev := pv) (next := nx) (mode := mode) (tail := tail) (bufbytes := bufbytes)
        (size := 1) (nmemb := Z.of_nat (length src)).
      all: try unfold fcells in *.
      all: rewrite ?BS in *. all: unfold BUFSIZ, FILE_BUF_OFF, FWRITE_DEPTH, got_ssp, ssp_guard in *.
      all: try fastfirst (first [ exact FC | exact BUF | exact BP | exact WB0 | exact ST | exact MI | exact SSP | exact FLsvb | rewrite NOWR in FLw; exact FLw
                 | change (map bv_unsigned src) with (of_bytes src); rewrite to_of_bytes; exact SRC'
                 | apply Forall_map; apply Forall_forall; intros b _; pose proof (bv_unsigned_in_range 8 b); unfold bv_modulus in *; cbn in *; (keep_hyps CEILV sp Af src b H0; lia)
                 | reflexivity
                 | unfold zlength; rewrite length_map; reflexivity
                 | unfold zlength; rewrite length_map; f_equal; (keep_hyps CEILV sp Af src S Shi S47; lia)
                 | rewrite NCH; exact FD
                 | unfold zlength in *; rewrite ?length_map; (keep_hyps CEILV sp Af src fs LENB lo LOB R LOR CEILLO SPM SP47 A0 FA4 FA5 WBL S S0; lia) ]). 
      (* [comment removed for export] *)
      all: try (unfold zlength; rewrite length_map;
                destruct SOR as [L0 | ->]; [left; exact L0 |];
                destruct (Z.eq_dec (Z.of_nat (length src)) 0) as [L0|L0]; [left; exact L0| right];
                pose proof (client_range_apart R CL FB (bv_unsigned sp) SRC (Z.of_nat (length src)) f Af 1264 BOK HIN CR ltac:((keep_hyps CEILV sp Af src fs L0; lia)) ltac:((keep_hyps CEILV sp R Af lo src LOR LOB CEILLO; lia)) ltac:((keep_hyps CEILV sp Af src; lia))) as AP;
                destruct (client_range_lo R s CL FB m (bv_unsigned sp) SRC (Z.of_nat (length src)) lo G CR ltac:((keep_hyps CEILV sp Af src fs L0; lia)) LOR ltac:((keep_hyps CEILV sp Af lo src LOB; lia))) as (C1 & C2 & C3 & C4);
                repeat split; (keep_hyps CEILV sp SRC lo src C2 R Af fs AP; lia)).
      all: match goal with |- implM _ _ _ _ _ => idtac | |- ?g => idtac "FWLEFT:" g end. }
    cbv beta. intros f' st' ms' (-> & INV' & PO).
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP').
    unfold store_file. apply implM_upd_lc. apply implM_ret. apply evt_done.
    unfold fx_W in MU. rewrite ?BS in MU. unfold BUFSIZ, FILE_BUF_OFF in MU.
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    assert (HW : Forall (stdio_iv R CL FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]).
    { unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
      - left. lia.
      - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
      - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia]. }
    split.
    { eapply agrees_on_weaken.
      - eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
        + left. lia.
        + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
        + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
      - intros a Ha. split; [exact Ha| intros X; exact X]. }
    split.
    { eapply (GIo_stdio_step R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| exact SPM|].
      cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
      assert (AGS : agrees_on (fun a => S3.GI.TwB.stdio_static a) m m').
      { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. unfold S3.GI.TwB.stdio_static in Hs. cbn [outside]. lia. }
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      Ltac trs AGS A := eapply agrees_rw_cells; [exact AGS | exact A | intros a Ha; unfold S3.GI.TwB.stdio_static; cbn in Ha; lia].
      split. { eapply FILE_R_agree; [exact SO | exact AGS | intros a Ha; unfold S3.GI.TwB.stdio_static; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; unfold S3.GI.TwB.stdio_static; lia]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AGS | intros a Ha; unfold S3.GI.TwB.stdio_static; lia | rewrite SEbs; intros a Ha; unfold S3.GI.TwB.stdio_static; lia]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AGS | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; unfold S3.GI.TwB.stdio_static; lia. }
      split; [trs AGS U1|]. split; [trs AGS U2|]. split; [trs AGS U3|]. split; [trs AGS OL|]. split; [trs AGS OH|].
      split.
      2:{ rewrite files_update_keys. exact ND. }
      apply UPD.
      - (* [comment removed for export] *)
        pose proof INV' as (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
        assert (RBN : f_rbuf fs = []) by (apply NORDi; rewrite NRW; reflexivity).
        assert (RBN' : f_rbuf f' = []) by (rewrite RB, RBN; destruct (f_wactive fs); reflexivity).
        rewrite RBN in FC'.
        exists flags, mode', (if f_wactive fs then rp else 0), tail, bufbytes'.
        rewrite WA, RBN', E1, E3, BS.
        split. { unfold fcells, BUFSIZ, FILE_BUF_OFF in *. rewrite ?BS in FC'; destruct (f_wactive fs); cbn [zlength length Z.of_nat] in FC' |- *; rewrite ?Z.add_0_r in FC' |- *; exact FC'. }
        split. { unfold flags_ok in *. rewrite E2, E4, E5, E6. exact FL. }
        split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite ?BS in BUF'; exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [rewrite BS in WBL'; exact WBL'|].
        split; [intros X; exfalso; exact (X eq_refl)|]. destruct (f_wactive fs); unfold zlength in RP |- *; cbn [length Z.of_nat]; (split; [lia| split; [lia| exact (proj2 (proj2 RP))]]).
      - exact (heap_file_inv_fx fs f' INV NOWR INV').
      - (* [comment removed for export] *)
        intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2 FR2 INV2.
        pose proof INV2 as (_ & _ & BS2 & _).
        destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB q2 A2 n2 FS ND HIN2) as (f2' & pv2' & nx2' & _ & En2 & _). subst n2.
        pose proof (file_block_facts R CL FB q2 A2 FILE_ALLOC BOK HIN2) as (B1 & B2 & B3 & B4 & B5 & B6). unfold FILE_ALLOC in B3, B4, B5, B6.
        assert (AP : A2 + 1264 <= Af \/ Af + 1264 <= A2).
        { destruct (GIo_apart K R s CL FB m (q2, A2, FILE_ALLOC) (f, Af, 1264) G ltac:(apply in_or_app; right; exact HIN2) ltac:(apply in_or_app; right; exact HIN)) as [E|AP].
          - exfalso. apply NE2. congruence.
          - unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
        eapply (FILE_R_agree (fun a => A2 <= a < A2 + 1264)); [exact FR2| | intros a Ha; lia | intros a Ha; rewrite BS2 in Ha; unfold BUFSIZ, FILE_BUF_OFF in Ha; lia].
        eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hb. cbn [outside]. (keep_hyps CEILV sp R Af lo src fs A2 a LOR CEILLO B4 AP Hb; lia). }
    split; [change (1 =? 0) with false; cbv iota; unfold zlength; rewrite length_map; reflexivity|]. unfold zlength. rewrite length_map. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_stdio_step_same : forall R (s : PS) CL FB m m' W SP,
    GIo K R s CL FB m -> munch W m m' -> wmono usegs m m' ->
    Forall (stdio_iv R CL FB SP) W -> SP <= rc_spmain R ->
    STDIOR (ps_libc s) FB m' ->
    GIo K R s CL FB m'.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros R s CL FB m m' W SP G MU WM HW HSP SR'.
    pose proof (GIo_stdio_step R s CL FB m m' W SP (ps_libc s) G MU WM HW HSP SR') as G'.
    destruct s; cbn in G'. exact G'.
  Qed.

  (* [comment removed for export] *)
  Definition STDIOR_stack_only__stmt : Prop := forall (l : libc_st hptr) FB (CL : list cblk) R m m' W,
    STDIOR l FB m -> blocks_ok (utp R) (CL ++ FB) -> munch W m m' -> wmono usegs m m' ->
    Forall (fun iv => CEILZ <= fst iv) W ->
    STDIOR l FB m'.
  Section Sz27.
  Variables l FB CL R m m' W : ltac2:(SecDiet.SzSec.tyM 'STDIOR_stack_only__stmt "vvvvvvv" @l).
  Lemma STDIOR_stack_only__body : ltac2:(SecDiet.SzSec.bodyP 'STDIOR_stack_only__stmt "vvvvvvv").
  Proof using Type. pin_using tt.
    intros SR BOK MU WM HW.
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    eapply (STDIOR_agree l FB m m' (fun a => a < CEILZ)); [exact SR| | |].
    - eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hc.
      eapply outside_of_Forall; [exact HW|]. intros [lo hi] X; cbn [fst snd] in *. lia.
    - intros a Ha. unfold S3.GI.TwB.stdio_static in Ha. lia.
    - intros a Ha. destruct (in_block_facts _ _ a BO2 Ha) as (_ & X & _). exact X.
  Qed.
  End Sz27.
  Lemma STDIOR_stack_only : ltac:(let t := eval cbv delta [STDIOR_stack_only__stmt] in STDIOR_stack_only__stmt in exact t).
  Proof using Type. intros l FB CL R m m' W. ltac2:(SecDiet.SzSec.closeP 'STDIOR_stack_only__body "vvvvvvv"). Qed.

  Lemma ferr_clear : forall x, 0 <= x -> Z.land x F_ERR = 0 -> (x / 32) mod 2 = 0.
  Proof using Type. pin_using tt.
    intros x Hx HL. unfold F_ERR in HL.
    pose proof (Z.testbit_spec' x 5 ltac:(lia)) as T. change (2^5) with 32 in T. rewrite <- T.
    assert (E : Z.testbit x 5 = Z.testbit (Z.land x 32) 5).
    { rewrite Z.land_spec. replace (Z.testbit 32 5) with true by reflexivity. rewrite andb_true_r. reflexivity. }
    rewrite E, HL. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ferror_o_proof__stmt : Prop := ferror_stmt_o HO K.
  Section Sz29.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo : ltac2:(SecDiet.SzSec.tyM 'ferror_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ferror_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'ferror_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
 intros SPO HIN ->.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold FILE_BLOCK, STDIO_STACK in *.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    unfold s_ferror, Stdio.ferror. eapply implM_lookup_file; [exact LK|]. apply implM_ret.
    pose proof (bv_unsigned_in_range 64 flags) as FLR.
    eapply evt_mono.
    { unfold fcells in FC. eapply (ferror_spec ra sp gp tp) with (lo := lo); rewrite ?unsigned_lit by lia; [exact ST| exact FC| exact MI| lia| lia]. }
    cbv beta. intros ms' PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & FC').
    rewrite (ferr_clear (bv_unsigned flags) ltac:(lia) FLerr).
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply agrees_on_weaken; [eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia]|].
             - apply Forall_cons; [left; cbn; lia| apply Forall_nil].
             - intros a Ha. split; [exact Ha| intros X; exact X]. }
    split. { eapply (GIo_stdio_step_same R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| | exact SPM|].
             - apply Forall_cons; [left; cbn; lia| apply Forall_nil].
             - eapply (STDIOR_stack_only _ FB CL R m m'); [exact SR| exact BOK| exact MU| exact WM|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    split; [reflexivity|]. split; [reflexivity|]. intros X; discriminate X.
  Qed.
  End Sz29.
  Theorem ferror_o_proof : ltac:(let t := eval cbv delta [ferror_o_proof__stmt] in ferror_o_proof__stmt in exact t).
  Proof using EQB HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo. ltac2:(SecDiet.SzSec.closeP 'ferror_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fileno_o_proof__stmt : Prop := fileno_stmt_o HO K.
  Section Sz30.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo : ltac2:(SecDiet.SzSec.tyM 'fileno_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fileno_o_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fileno_o_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB HFL KST. pin_using (fun (EQB HFL KST : unit) => tt).
 intros SPO HIN ->.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold FILE_BLOCK, STDIO_STACK in *.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    pose proof INV as (NCH & FD & BS & _).
    unfold s_fileno, Stdio.fileno. eapply implM_lookup_file; [exact LK|]. apply implM_ret.
    eapply evt_mono.
    { unfold fcells in FC. eapply (fileno_spec ra sp gp tp) with (lo := lo); rewrite ?unsigned_lit by lia; [exact ST| exact FC| exact MI| lia| lia| lia]. }
    cbv beta. intros ms' PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & FC').
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply agrees_on_weaken; [eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia]|].
             - apply Forall_cons; [left; cbn; lia| apply Forall_nil].
             - intros a Ha. split; [exact Ha| intros X; exact X]. }
    split. { eapply (GIo_stdio_step_same R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| | exact SPM|].
             - apply Forall_cons; [left; cbn; lia| apply Forall_nil].
             - eapply (STDIOR_stack_only _ FB CL R m m'); [exact SR| exact BOK| exact MU| exact WM|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    split; [reflexivity|]. split; [reflexivity|]. lia.
  Qed.
  End Sz30.
  Theorem fileno_o_proof : ltac:(let t := eval cbv delta [fileno_o_proof__stmt] in fileno_o_proof__stmt in exact t).
  Proof using EQB HFL KST. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB f Af lo. ltac2:(SecDiet.SzSec.closeP 'fileno_o_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition stderr_inv_fx__stmt : Prop := forall f f', stderr_inv f -> fx_inv f f' -> stderr_inv f'.
  Section Sz31.
  Variables f f' : ltac2:(SecDiet.SzSec.tyM 'stderr_inv_fx__stmt "vv" @f).
  Lemma stderr_inv_fx__body : ltac2:(SecDiet.SzSec.bodyP 'stderr_inv_fx__stmt "vv").
  Proof using Type. pin_using tt.
    intros (CH & FD & BS & NRD & NWR & EOF & RB & SW & LB) (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB' & SW' & LB').
    unfold stderr_inv. rewrite E1, E2, E3, E4, E5, E6, RB', RB.
    split; [exact CH|]. split; [exact FD|]. split; [exact BS|]. split; [exact NRD|]. split; [exact NWR|]. split; [exact EOF|].
    split; [destruct (f_wactive f); reflexivity|].
    split; [destruct (f_stdoutw f'); [exfalso; pose proof (SW' eq_refl) as X; rewrite SW in X; discriminate X| reflexivity]|].
    destruct (f_lbf_nl f'); [exfalso; pose proof (LB' eq_refl) as X; rewrite LB in X; discriminate X| reflexivity].
  Qed.
  End Sz31.
  Lemma stderr_inv_fx : ltac:(let t := eval cbv delta [stderr_inv_fx__stmt] in stderr_inv_fx__stmt in exact t).
  Proof using Type. intros f f'. ltac2:(SecDiet.SzSec.closeP 'stderr_inv_fx__body "vv"). Qed.

  Theorem efwrite_proof : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB.efwrite_stmt K.
  Proof using HFL KST. pin_using (fun (HFL KST : unit) => tt).
    intros until bs. intros ([FB G] & ST & LOR & LOB & SPM & MI & Etp & AL) -> -> -> -> HSRC ROD LEN1.
    assert (SPO : std_pre_o K sp tp R s CL FB lo STDIO_STACK m) by (split; [exact G|]; split; [exact ST|]; split; [exact LOR|]; split; [exact LOB|]; split; [exact SPM|]; split; [exact MI|]; split; [exact Etp| exact AL]).
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (_ & SR & _ & _ & SSP & BOK & _ & _ & _ & _ & _ & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold STDIO_STACK, STDERR_FILE in *.
    destruct SE as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof SEI as (CH2 & FD2 & BS2 & ND2 & NW2 & EOF2 & RB2 & SW2 & LB2).
    rewrite NW2 in FLw. rewrite BS2 in *.
    pose proof (bytes_at_bound _ _ _ _ HSRC) as BSRC.
    assert (WBN : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. unfold zlength in WBL. cbn [length] in WBL. lia. }
    unfold efwrite. apply implM_rd_lc.
    eapply implM_bind.
    { unfold A_STDERR, A_STDERR_BUF in *.
      eapply (fwrite_spec (St:=PS)) with (f := lc_stderr (ps_libc s)) (s := map bv_unsigned bs) (S := MSG) (lo := lo) (canary := rc_canary R)
        (Fp := 0x23e20) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf (lc_stderr (ps_libc s)))) (closefn := F_STDIO_CLOSE) (readfn := 0)
        (seekfn := F_STDIO_SEEK) (B := 0x54920) (prev := 0) (next := 0) (mode := mode) (tail := tail) (bufbytes := bufbytes)
        (size := Z.of_nat (length bs)) (nmemb := 1).
      all: try unfold fcells in *. all: rewrite ?BS2 in *.
      all: unfold FWRITE_DEPTH, got_ssp, ssp_guard in *.
      all: try fastfirst (first [ exact FC | exact BUF | exact BP | exact WB0 | exact ST | exact MI | exact SSP | exact FLsvb | exact FLw
                 | change (map bv_unsigned bs) with (of_bytes bs); rewrite to_of_bytes; exact HSRC
                 | apply Forall_map; apply Forall_forall; intros b _; pose proof (bv_unsigned_in_range 8 b); unfold bv_modulus in *; cbn in *; (keep_hyps CEILV sp bs b H0; lia)
                 | reflexivity
                 | unfold zlength; rewrite length_map; reflexivity
                 | unfold zlength; rewrite length_map; f_equal; (keep_hyps CEILV sp bs MSG ROD R lo LOR CEILLO; lia)
                 | rewrite CH2; right; exact FD2
                 | rewrite WBN; unfold zlength in *; rewrite ?length_map; cbn [length Z.of_nat]; (keep_hyps CEILV H hptr sp s bs R lo MSG ROD; lia)
                 | unfold zlength in *; rewrite ?length_map; (keep_hyps CEILV H hptr sp s MSG bs ROD lo LOB R LOR CEILLO SPM SP47; lia) ]).
      all: try (right; unfold zlength; rewrite length_map; repeat split; lia). }
    cbv beta. intros f' st' ms' (-> & INV' & PO).
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP').
    apply implM_upd_lc_last. apply evt_done.
    unfold fx_W in MU. rewrite ?BS2 in MU. unfold A_STDERR, A_STDERR_BUF in *.
    unfold out_post. exists u0, u1, u2, (Z_to_bv 64 (if Z.of_nat (length bs) =? 0 then 0 else 1)), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    assert (HW : Forall (stdio_iv R CL FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (0x23e20, 0x23e20 + 232); (0x54920, 0x54920 + 0)]).
    { unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd]; [left; lia| right; right; left; lia| right; right; right; lia]. }
    split.
    { eapply agrees_on_weaken; [eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun _ => False)); [exact G| exact MU| exact WM| | lia]|].
      - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd]; [left; lia| right; right; left; lia| right; right; right; left; lia].
      - intros a Ha. split; [exact Ha| intros X; exact X]. }
    exists FB.
    eapply (GIo_stdio_step R s CL FB m m' _ (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| exact SPM|].
    cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_stderr].
    pose proof BOK as [BO BA]. apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof SOI as (_ & _ & SObs & _).
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    Ltac trw MU WM A := eapply rw_cells_transport; [exact A | exact MU | exact WM | cbn; lia].
    split. { eapply FILE_R_transport; [exact SO| exact MU| exact WM| | | rewrite SObs; unfold BUFSIZ; lia].
             - repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
             - rewrite SObs. unfold BUFSIZ. repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil. }
    split; [exact SOI|].
    split. { pose proof INV' as (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
             assert (RBN' : f_rbuf f' = []) by (rewrite RB, RB2; destruct (f_wactive (lc_stderr (ps_libc s))); reflexivity).
             rewrite RB2 in FC'.
             exists flags, mode', (if f_wactive (lc_stderr (ps_libc s)) then rp else 0), tail, bufbytes'.
             rewrite WA, RBN', E1, E3, BS2.
             split. { unfold fcells in *. rewrite ?BS2 in FC'. destruct (f_wactive (lc_stderr (ps_libc s))); cbn [zlength length Z.of_nat] in FC' |- *; rewrite ?Z.add_0_r in FC' |- *; exact FC'. }
             split. { unfold flags_ok in *. rewrite E2, E4, E5, E6. rewrite NW2 in FL |- *. exact FL. }
             split; [rewrite ?BS2 in BUF'; exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [rewrite ?BS2 in WBL'; exact WBL'|].
             split; [intros X; exfalso; exact (X eq_refl)|]. destruct (f_wactive (lc_stderr (ps_libc s))); unfold zlength in RP |- *; cbn [length Z.of_nat]; (split; [lia| split; [lia| exact (proj2 (proj2 RP))]]). }
    split; [exact (stderr_inv_fx _ _ SEI INV')|].
    split. { eapply rw_cells_transport; [exact SIN | exact MU | exact WM |]. unfold stdin_cells. rewrite file_cells_size. cbn. lia. }
    split; [trw MU WM U1|]. split; [trw MU WM U2|]. split; [trw MU WM U3|]. split; [trw MU WM OL|]. split; [trw MU WM OH|].
    split; [| exact ND].
    eapply files_R_transport; [exact FS| exact MU| exact WM|].
    apply Forall_forall. intros [lo' hi'] Hiv. apply Forall_forall. intros [[q' A'] n'] Hb. cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) BO2 _ Hb) as (K1 & K2 & K3 & K4 & K5 & K6). unfold cb_addr, cb_size in *. cbn [fst snd] in *.
    cbn in Hiv. destruct Hiv as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  Qed.


End Glue.

End WithCeil.
End TwB.
End Stdio_glue.

(* [comment removed for export] *)
Module Stdio_glue_init.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_main_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.GIInit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
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
Section GlueInit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition blob1_cells : list cell :=
    file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDIO_WRITE F_STDIO_SEEK A_STDERR_BUF 0 0 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)
    ++ [C8 (Z_to_bv 64 A_STDERR)]
    ++ stdin_cells
    ++ [C8 (Z_to_bv 64 A_STDIN)]
    ++ file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDOUT_WRITE F_STDIO_SEEK A_STDOUT_BUF 1024 0 0 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80)
    ++ [C8 (Z_to_bv 64 A_STDOUT)].
  Definition blob2_cells : list cell :=
    [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); CB 8 (repeat (Z_to_bv 8 0) 8)]
    ++ [CB 0 []]
    ++ [CB 8 (repeat (Z_to_bv 8 0) 8); CB 1024 (repeat (Z_to_bv 8 0) 1024); CB 8 (repeat (Z_to_bv 8 0) 8)]
    ++ [CB 1024 (repeat (Z_to_bv 8 0) 1024)].

  Lemma bytes_eq_of_unsigned : forall bs bs' : list byte, map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
  Proof using Type. pin_using tt.
    induction bs as [|b bs IH]; intros [|b' bs'] E; cbn in E; try discriminate E; [reflexivity|].
    injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
  Qed.
  Lemma blob1_ok : cells_wf blob1_cells /\ cells_bytes blob1_cells = wimg 0x23660 720 /\ cells_size blob1_cells = 720%nat.
  Proof using Type. pin_using tt. split; [| split]; [vm_compute; repeat split; exact I | apply bytes_eq_of_unsigned; vm_compute; reflexivity | vm_compute; reflexivity]. Qed.
  Lemma blob2_ok : cells_wf blob2_cells /\ cells_bytes blob2_cells = wimg 0x54148 2088 /\ cells_size blob2_cells = 2088%nat.
  Proof using Type. pin_using tt. split; [| split]; [vm_compute; repeat split; exact I | apply bytes_eq_of_unsigned; vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

  Theorem stdio_init_proof : stdio_init_law K.
  Proof using KST. pin_using (fun (KST : unit) => tt).
    intros R m [SF1 SF2]. apply (proj2 (KST libc_init R [] m)).
    pose proof blob1_ok as (W1 & E1 & Z1). pose proof blob2_ok as (W2 & E2 & Z2).
    (* [comment removed for export] *)
    pose proof (rw_cells_recast m 0x23660 _ blob1_cells SF1 W1 ltac:(cbn [cells_bytes cbytes]; rewrite app_nil_r; exact E1) ltac:(rewrite Z1; reflexivity)) as B1.
    pose proof (rw_cells_recast m 0x54148 _ blob2_cells SF2 W2 ltac:(cbn [cells_bytes cbytes]; rewrite app_nil_r; exact E2) ltac:(rewrite Z2; reflexivity)) as B2.
    clear SF1 SF2. unfold blob1_cells in B1. unfold blob2_cells in B2.
    apply (proj1 (rw_cells_app ssegs m _ _ _)) in B1 as [SE B1]. rewrite file_cells_size in B1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in B1.
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in B1 as [UE B1]. (sl_lit_sizes_in B1; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1).
    apply (proj1 (rw_cells_app ssegs m _ _ _)) in B1 as [SI B1]. unfold stdin_cells in B1 at 1. rewrite file_cells_size in B1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1.
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in B1 as [UI B1]. (sl_lit_sizes_in B1; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1).
    apply (proj1 (rw_cells_app ssegs m _ _ _)) in B1 as [SO UO]. rewrite file_cells_size in UO. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in UO.
    apply (proj1 (rw_cells_app ssegs m _ _ _)) in B2 as [OFL B2]. (sl_lit_sizes_in B2; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B2).
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in B2 as [EB B2]. (sl_lit_sizes_in B2; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B2).
    apply (proj1 (rw_cells_app ssegs m _ _ _)) in B2 as [IB OB]. (sl_lit_sizes_in OB; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in OB).
    apply (proj1 (rw_cells_app ssegs m _ [_;_] _)) in OFL as [OL OH]. (sl_lit_sizes_in OH; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in OH).
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in OL as [OL _].
    apply (proj1 (rw_cells_app ssegs m _ [_] _)) in OH as [OH _].
    eapply (stdio_init (hptr:=hptr)); unfold A_STDOUT, A_STDERR, A_STDIN, A_STDOUT_BUF, A_STDERR_BUF, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD;
      first [exact SO | exact SE | exact SI | eexists; exact OB | exact EB | exact UE | exact UI | exact UO | exact OL | exact OH
            | match goal with |- ?g => idtac "INITLEFT:" g end].
  Qed.


End GlueInit.

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
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_main_A__S3.GIInit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.
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
Section GlueInit.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition blob1_cells : list cell :=
    file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDIO_WRITE F_STDIO_SEEK A_STDERR_BUF 0 0 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)
    ++ [C8 (Z_to_bv 64 A_STDERR)]
    ++ stdin_cells
    ++ [C8 (Z_to_bv 64 A_STDIN)]
    ++ file_cells (Z_to_bv 64 5) 0 0 F_STDIO_CLOSE 0 0 0 0 F_STDOUT_WRITE F_STDIO_SEEK A_STDOUT_BUF 1024 0 0 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80)
    ++ [C8 (Z_to_bv 64 A_STDOUT)].
  Definition blob2_cells : list cell :=
    [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); CB 8 (repeat (Z_to_bv 8 0) 8)]
    ++ [CB 0 []]
    ++ [CB 8 (repeat (Z_to_bv 8 0) 8); CB 1024 (repeat (Z_to_bv 8 0) 1024); CB 8 (repeat (Z_to_bv 8 0) 8)]
    ++ [CB 1024 (repeat (Z_to_bv 8 0) 1024)].

  Lemma bytes_eq_of_unsigned : forall bs bs' : list byte, map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
  Proof using Type. pin_using tt.
    induction bs as [|b bs IH]; intros [|b' bs'] E; cbn in E; try discriminate E; [reflexivity|].
    injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
  Qed.
  Lemma blob1_ok : cells_wf blob1_cells /\ cells_bytes blob1_cells = wimg 0x23e20 720 /\ cells_size blob1_cells = 720%nat.
  Proof using Type. pin_using tt. split; [| split]; [vm_compute; repeat split; exact I | apply bytes_eq_of_unsigned; vm_compute; reflexivity | vm_compute; reflexivity]. Qed.
  Lemma blob2_ok : cells_wf blob2_cells /\ cells_bytes blob2_cells = wimg 0x54908 2088 /\ cells_size blob2_cells = 2088%nat.
  Proof using Type. pin_using tt. split; [| split]; [vm_compute; repeat split; exact I | apply bytes_eq_of_unsigned; vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

  Theorem stdio_init_proof : stdio_init_law K.
  Proof using KST. pin_using (fun (KST : unit) => tt).
    intros R m [SF1 SF2]. apply (proj2 (KST libc_init R [] m)).
    pose proof blob1_ok as (W1 & E1 & Z1). pose proof blob2_ok as (W2 & E2 & Z2).
    (* [comment removed for export] *)
    pose proof (rw_cells_recast m 0x23e20 _ blob1_cells SF1 W1 ltac:(cbn [cells_bytes cbytes]; rewrite app_nil_r; exact E1) ltac:(rewrite Z1; reflexivity)) as B1.
    pose proof (rw_cells_recast m 0x54908 _ blob2_cells SF2 W2 ltac:(cbn [cells_bytes cbytes]; rewrite app_nil_r; exact E2) ltac:(rewrite Z2; reflexivity)) as B2.
    clear SF1 SF2. unfold blob1_cells in B1. unfold blob2_cells in B2.
    apply (proj1 (rw_cells_app usegs m _ _ _)) in B1 as [SE B1]. rewrite file_cells_size in B1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in B1.
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in B1 as [UE B1]. (sl_lit_sizes_in B1; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1).
    apply (proj1 (rw_cells_app usegs m _ _ _)) in B1 as [SI B1]. unfold stdin_cells in B1 at 1. rewrite file_cells_size in B1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1.
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in B1 as [UI B1]. (sl_lit_sizes_in B1; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B1).
    apply (proj1 (rw_cells_app usegs m _ _ _)) in B1 as [SO UO]. rewrite file_cells_size in UO. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in UO.
    apply (proj1 (rw_cells_app usegs m _ _ _)) in B2 as [OFL B2]. (sl_lit_sizes_in B2; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B2).
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in B2 as [EB B2]. (sl_lit_sizes_in B2; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in B2).
    apply (proj1 (rw_cells_app usegs m _ _ _)) in B2 as [IB OB]. (sl_lit_sizes_in OB; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in OB).
    apply (proj1 (rw_cells_app usegs m _ [_;_] _)) in OFL as [OL OH]. (sl_lit_sizes_in OH; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.add_carry] in OH).
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in OL as [OL _].
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in OH as [OH _].
    eapply (stdio_init (hptr:=hptr)); unfold A_STDOUT, A_STDERR, A_STDIN, A_STDOUT_BUF, A_STDERR_BUF, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD;
      first [exact SO | exact SE | exact SI | eexists; exact OB | exact EB | exact UE | exact UI | exact UO | exact OL | exact OH
            | match goal with |- ?g => idtac "INITLEFT:" g end].
  Qed.


End GlueInit.

End WithCeil.
End TwB.
End Stdio_glue_init.

(* [comment removed for export] *)
Module Stdio_glue_rd.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_fwritex__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_misc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
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
Section GlueRd.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).
  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.spo_facts K KST).
  #[local] Notation GIo_stdio_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.GIo_stdio_step K KST HFL).
  #[local] Notation GIo_stdio_step_same := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.GIo_stdio_step_same K KST HFL).
  #[local] Notation keeps_of_stdio := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.keeps_of_stdio K).
  #[local] Notation client_range_lo := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.client_range_lo K).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma implM_mget : forall {B} (k : PS -> M PS B) (s : PS) Q ms,
    implM ssegs (k s) s Q ms -> implM ssegs (mbind mget k) s Q ms.
  Proof using Type. pin_using tt. intros. exact H0. Qed.

  Lemma set_rbuf_same : forall f, set_rbuf (f_rbuf f) f = f.
  Proof using Type. pin_using tt. intros f. destruct f; reflexivity. Qed.

  Theorem fread_o_proof : fread_stmt_o HO K.
  Proof using EQB HAL HFL KST. pin_using (fun (EQB HAL HFL KST : unit) => tt).
    intros until junk. intros SPO HIN -> -> -> -> NB DST CR.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold FILE_BLOCK, STDIO_STACK in *.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    assert (LJ : length junk = Z.to_nat n) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
    assert (WFR : 0 <= wfn_of fs < 2^64) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw fs); cbn; lia).
    assert (LBR : 0 <= lbf_of fs < 2^64) by (unfold lbf_of; destruct (f_lbf_nl fs); cbn; lia).
    pose proof WBL as WBL'. unfold zlength in WBL'. rewrite BS in WBL'. unfold BUFSIZ in WBL'.
    (* [comment removed for export] *)
    unfold s_fread, Stdio.fread. apply implM_mget. unfold with_file.
    apply implM_bind_assoc. eapply implM_lookup_file; [exact LK|].
    unfold file_buf_addr, blk_addr.
    pose proof (HAL _ _ _ _ (f, Af, 1264) (proj1 G) ltac:(apply in_or_app; right; exact HIN)) as HADDR. cbn [cb_tok cb_addr fst snd] in HADDR. rewrite HADDR.
    (* [comment removed for export] *)
    assert (TAIL : forall (got : list Z) (f' : file_st) (m' : mem) (mode' flags' : word) (rp' : Z) (bufbytes' junk' : list byte)
                     (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
              munch [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024); (D, D + n)] m m' -> wmono ssegs m m' -> mem_inv ssegs m' ->
              stk ssegs m' lo (bv_unsigned sp) ->
              FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
              0 <= zlength got <= n -> Forall (fun z => 0 <= z < 256) got ->
              rw_cells ssegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
              implM ssegs (mbind (store_file ps_libc set_libc eqb f f') (fun _ : unit => mret got)) s
                (fun got s' ms' => exists a0v mq junkq, hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v mq ms'
                   /\ ps_outfile s' = ps_outfile s /\ mem_inv ssegs mq /\ stk ssegs mq lo (bv_unsigned sp)
                   /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n)) m mq
                   /\ GIo K R s' CL FB mq
                   /\ a0v = Z_to_bv 64 (zlength got) /\ 0 <= zlength got <= n /\ Forall (fun z => 0 <= z < 256) got
                   /\ rw_cells ssegs mq D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junkq])
                (MS (mkR ra sp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 (zlength got)) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                    F (ret_pc ra) fc None m' (seg_rom ssegs))).
    { intros got f' m' mode' flags' rp' bufbytes' junk' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MU WM MI' ST' FR' INV' GB GF DST'.
      unfold store_file. apply implM_upd_lc. apply implM_ret. apply evt_done.
      eexists _, m', junk'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|].
      split. { eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun a => D <= a < D + n)); [exact G| exact MU| exact WM| | lia].
               apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]; cbn [fst snd].
               - left. lia.
               - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
               - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
               - right; right; right; right. intros a Ha. exact Ha. }
      split; [| split; [reflexivity| split; [exact GB| split; [exact GF| exact DST']]]].
      (* [comment removed for export] *)
      assert (MU' : exists W', munch W' m m' /\ Forall (stdio_iv R CL FB (bv_unsigned sp)) W').
      { destruct (Z_lt_le_dec 0 n) as [NP|NZ].
        - destruct CR as [CR|CR].
          + (* [comment removed for export] *)
            exists ([(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)] ++ map (fun b : cblk => (Z.max D (cb_addr b), Z.min (D + n) (cb_addr b + cb_size b))) CL).
            split.
            * intros x Hx. apply MU. assert (OA : forall W1 W2 y, outside (W1 ++ W2) y -> outside W1 y /\ outside W2 y).
              { induction W1 as [|[u v] W1 IH]; intros W2 y Hy; cbn in *; [split; [exact I| exact Hy]|]. destruct Hy as [Y1 Y2]. destruct (IH _ _ Y2) as [Y3 Y4]. repeat split; assumption. }
              destruct (OA _ _ _ Hx) as [O1 O2]. cbn [outside] in O1 |- *. destruct O1 as (O1a & O1b & O1c & _).
              split; [exact O1a|]. split; [exact O1b|]. split; [exact O1c|]. split; [| exact I].
              intros HDn. pose proof (CR (bv_unsigned x) HDn) as Hb. apply in_block_In in Hb as (b & HbIn & Hb).
              assert (OM : forall (L : list cblk) y, outside (map (fun b : cblk => (Z.max D (cb_addr b), Z.min (D + n) (cb_addr b + cb_size b))) L) y ->
                             forall b', In b' L -> ~ (Z.max D (cb_addr b') <= y < Z.min (D + n) (cb_addr b' + cb_size b'))).
              { induction L as [|c L IHL]; intros y Hy b' Hb'; [destruct Hb'|]. cbn in Hy. destruct Hy as [Y1 Y2]. destruct Hb' as [<-|Hb']; [exact Y1| apply IHL; assumption]. }
              apply (OM CL (bv_unsigned x) O2 b HbIn). lia.
            * apply Forall_app. split.
              -- unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
                 ++ left. lia.
                 ++ right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
                 ++ right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
              -- apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b & <- & HbIn). unfold stdio_iv. right; left.
                 unfold iv_in_block. apply Exists_exists. exists b. split; [apply in_or_app; left; exact HbIn| cbn [fst snd]; lia].
          + (* [comment removed for export] *)
            exists [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024); (D, D + n)]. split; [exact MU|].
            unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]; cbn [fst snd].
            * left. lia.
            * right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
            * right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
            * left. destruct CR as [CR1 CR2]. split; lia.
        - (* [comment removed for export] *)
          exists [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]. split.
          + intros x Hx. apply MU. cbn [outside] in Hx |- *. destruct Hx as (O1 & O2 & O3 & _). repeat split; try assumption. lia.
          + unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
            * left. lia.
            * right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
            * right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia]. }
      destruct MU' as (W' & MUW & HW).
      eapply (GIo_stdio_step R s CL FB m m' W' (bv_unsigned sp)); [exact G| exact MUW| exact WM| exact HW| exact SPM|].
      cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
      pose proof BOK as [BO BA]. pose proof BO as BO'. apply Forall_app in BO'. destruct BO' as [BO1 BO2].
      (* [comment removed for export] *)
      assert (AGS : agrees_on (fun a => GI.stdio_static a) m m').
      { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. unfold GI.stdio_static in Hs. cbn [outside].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [| exact I].
        intros HDa. destruct (Z_lt_le_dec 0 n) as [NP|NZ]; [| lia].
        destruct (client_range_lo R s CL FB m (bv_unsigned sp) D n lo G CR NP LOR ltac:(lia)) as (C1 & C2 & C3 & C4). lia. }
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      Ltac trs2 AGS A := eapply agrees_rw_cells; [exact AGS | exact A | intros a Ha; unfold GI.stdio_static; cbn in Ha; lia].
      split. { eapply FILE_R_agree; [exact SO | exact AGS | intros a Ha; unfold GI.stdio_static; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; unfold GI.stdio_static; lia]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AGS | intros a Ha; unfold GI.stdio_static; lia | rewrite SEbs; intros a Ha; unfold GI.stdio_static; lia]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AGS | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; unfold GI.stdio_static; lia. }
      split; [trs2 AGS U1|]. split; [trs2 AGS U2|]. split; [trs2 AGS U3|]. split; [trs2 AGS OL|]. split; [trs2 AGS OH|].
      split.
      2:{ rewrite files_update_keys. exact ND. }
      apply UPD; [exact FR'| exact INV'|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2 FR2 INV2.
      pose proof INV2 as (_ & _ & BS2 & _).
      destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB q2 A2 n2 FS ND HIN2) as (f2' & pv2' & nx2' & _ & En2 & _). subst n2.
      pose proof (file_block_facts R CL FB q2 A2 FILE_ALLOC BOK HIN2) as (B1 & B2 & B3 & B4 & B5 & B6). unfold FILE_ALLOC in B3, B4, B5, B6.
      assert (AP : A2 + 1264 <= Af \/ Af + 1264 <= A2).
      { destruct (GIo_apart K R s CL FB m (q2, A2, FILE_ALLOC) (f, Af, 1264) G ltac:(apply in_or_app; right; exact HIN2) ltac:(apply in_or_app; right; exact HIN)) as [E|AP].
        - exfalso. apply NE2. congruence.
        - unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
      assert (APD : n = 0 \/ D + n <= A2 \/ A2 + 1264 <= D).
      { destruct (Z_lt_le_dec 0 n) as [NP|NZ]; [right | left; lia].
        exact (client_range_apart R CL FB (bv_unsigned sp) D n q2 A2 FILE_ALLOC BOK HIN2 CR NP ltac:(lia) ltac:(unfold FILE_ALLOC; lia)). }
      eapply (FILE_R_agree (fun a => A2 <= a < A2 + 1264)); [exact FR2| | intros a Ha; lia | intros a Ha; rewrite BS2 in Ha; unfold BUFSIZ, FILE_BUF_OFF in Ha; lia].
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hb. cbn [outside]. (keep_hyps CEILV sp R Af D n lo junk fs A2 a LOR CEILLO B4 AP APD Hb; lia). }
    (* [comment removed for export] *)
    destruct (Z.eq_dec n 0) as [NZ|NZ].
    { (* [comment removed for export] *)
      subst n.
      assert (HDm : exists D', (Z_to_bv 64 D : word) = Z_to_bv 64 D' /\ 0 <= D' < 2^64).
      { exists (D mod 2^64). split; [symmetry; apply Z_to_bv_mod64| apply Z.mod_pos_bound; lia]. }
      destruct HDm as (D' & -> & HD').
      eapply implM_bind.
      { unfold fcells in FC.
        eapply (fread_zero_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail lo m)
          with (flags := flags) (mode := mode) (rp := rp) (wfn := wfn_of fs) (fd := f_fd fs) (lbf := lbf_of fs) (D := D') (Dm := D);
          rewrite ?BS in *; unfold BUFSIZ, FILE_BUF_OFF in *;
          first [ exact FC | exact ST | exact MI | (keep_hyps CEILV sp Af D lo junk fs LOB R SPM SP47 A0 LOR CEILLO FA4 rp tail RP WFR FD LBR D' HD'; lia) | destruct (f_wactive fs); unfold zlength in *; (keep_hyps CEILV sp R Af D lo junk fs A0 FA4 FA1 WBL'; lia)
                | match goal with |- ?g => idtac "ZLEFT:" g end ]. }
      cbv beta. intros r st' ms' (-> & -> & PO).
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & m' & -> & MU & WM & MI' & ST' & FC').
      cbn [fst snd]. rewrite set_rbuf_same.
      replace (Z_to_bv 64 0 : word) with (Z_to_bv 64 (zlength (@nil Z)) : word) by reflexivity.
      eapply (TAIL [] fs m' mode' flags rp bufbytes junk); try assumption.
      - eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
      - exists flags, mode', rp, tail, bufbytes. split; [unfold fcells in *; rewrite ?BS in FC' |- *; unfold BUFSIZ, FILE_BUF_OFF in *; exact FC'|].
        split; [exact FL|]. split; [| split; [exact BP| split; [exact WB0| split; [exact WBL| split; [exact RR| exact RP]]]]].
        eapply rw_cells_transport; [exact BUF| exact MU| exact WM|]. rewrite BS. cbn. unfold BUFSIZ, FILE_BUF_OFF. lia.
      - unfold zlength. cbn. lia.
      - constructor.
      - cbn [length map Z.to_nat Nat.sub]. replace junk with (@nil byte) by (destruct junk; [reflexivity| cbn in LJ; lia]).
        apply rw_cells_CB0. apply rw_cells_nil0; lia. }
    destruct (f_nord fs) eqn:NORD.
    { (* [comment removed for export] *)
      pose proof (NORDi eq_refl) as RBN.
      destruct (client_range_lo R s CL FB m (bv_unsigned sp) D n lo G CR ltac:(lia) LOR ltac:(lia)) as (C1 & C2 & C3 & C4).
      eapply implM_bind.
      { eapply (fread_nord_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail lo (rc_canary R) m)
          with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes);
          rewrite ?BS in *; rewrite ?RBN in *; unfold BUFSIZ, FILE_BUF_OFF, got_ssp, ssp_guard in *;
          first [ exact FC | exact ST | exact MI | exact SSP | exact FLn | exact FLe | exact FLsvb | exact BP | exact WB0 | exact NCH | exact FD | reflexivity
                | rewrite NORD; first [exact FLn | reflexivity]
                | unfold zlength in *; cbn [length Z.of_nat] in *; (keep_hyps CEILV sp Af D n lo junk fs rp tail LOB R LOR CEILLO SPM SP47 A0 FA4 bufbytes FA5 WBL RP NB NZ; lia)
                | match goal with |- rw_cells _ _ Af _ => unfold zlength in FC; cbn [length Z.of_nat] in FC; rewrite Z.add_0_r in FC; exact FC end
                | exact BUF
                | match goal with |- ?g => idtac "NLEFT:" g end ]. }
      cbv beta. intros r st' ms' []. }
    (* [comment removed for export] *)
    assert (NOWR : f_nowr fs = true) by (destruct (f_nowr fs) eqn:E; [reflexivity| cbn in NRW; congruence]).
    destruct (NOWRi NOWR) as [WACT WBN].
    destruct (client_range_lo R s CL FB m (bv_unsigned sp) D n lo G CR ltac:(lia) LOR ltac:(lia)) as (C1 & C2 & C3 & C4).
    pose proof (client_range_apart R CL FB (bv_unsigned sp) D n f Af 1264 BOK HIN CR ltac:(lia) ltac:(lia) ltac:(lia)) as APD.
    rewrite WACT in FC.
    eapply implM_bind.
    { eapply (fread_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail D n lo (rc_canary R) m)
        with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes) (djunk := junk);
        rewrite ?BS in *; unfold BUFSIZ, FILE_BUF_OFF, FREAD_DEPTH, got_ssp, ssp_guard in *;
        first [ exact FC | exact FL | exact ST | exact MI | exact SSP | exact BP | exact DST | exact RR | exact WACT | exact WBN | exact NCH | exact FD | exact RBR | reflexivity
              | exact BUF
              | unfold rc_spmain in *; (keep_hyps CEILV sp Af D n junk fs NB lo LOB R LOR CEILLO SPM SP47 A0 FA4 FA5 C4 C1 C3 C2 APD rp tail RP; lia)
              | match goal with |- ?g => idtac "RLEFT:" g end ]. }
    cbv beta. intros [got f'] st' ms' (-> & INV' & GB & GF & GRB & PO). cbn [fst snd] in INV', GB, GF, GRB, PO |- *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & flags' & mode' & rp' & bufbytes' & rest' & m' & -> & MU & WM & MI' & ST' & FC' & FL' & BUF' & RR' & RP1' & RP2' & DST' & SSP').
    unfold fr_W, FREAD_DEPTH in MU. rewrite ?BS in MU. unfold BUFSIZ in MU.
    pose proof INV' as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
    eapply (TAIL got f' m' mode' flags' rp' bufbytes' rest'); try assumption.
    - eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. (keep_hyps CEILV sp R Af D n lo junk fs got x LOB Hx; lia).
    - exists flags', mode', rp', tail, bufbytes'. rewrite I6, I7, I1, I3, BS.
      split. { unfold fcells, BUFSIZ, FILE_BUF_OFF in *. rewrite BS in FC'. unfold zlength in FC' |- *. cbn [length Z.of_nat] in FC' |- *. exact FC'. }
      split; [exact FL'|]. split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite BS in BUF'; exact BUF'|]. split; [reflexivity|]. split; [intros _; reflexivity|].
      split; [unfold zlength, BUFSIZ; cbn [length Z.of_nat]; lia|].
      split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite BS in RR'; exact RR'| exact (conj RP1' (conj RP2' (proj2 (proj2 RP))))].
    - unfold heap_file_inv. rewrite I1, I2, I3, I4, I5, I6, I7, NORD.
      split; [exact NCH|]. split; [exact FD|]. split; [exact BS|]. split; [exact NRW|].
      split; [intros _; split; reflexivity|]. split; [intros X; discriminate X| exact GRB].
    - unfold zlength in GB |- *. lia.
  Qed.
End GlueRd.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Startup.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Fuzz_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.F_fread_misc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_stdio_leaf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_fwritex__S3.Stdio_ifaceP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.
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
Section GlueRd.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis KST : forall l R FB m, mk_stdio K l R FB m <-> STDIOR l FB m.
  Hypothesis HFL : heap_frame_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).
  #[local] Notation spo_facts := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.spo_facts K KST).
  #[local] Notation GIo_stdio_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.GIo_stdio_step K KST HFL).
  #[local] Notation GIo_stdio_step_same := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.GIo_stdio_step_same K KST HFL).
  #[local] Notation keeps_of_stdio := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.keeps_of_stdio K).
  #[local] Notation client_range_lo := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blk__S3.Stdio_glue.TwB.client_range_lo K).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma implM_mget : forall {B} (k : PS -> M PS B) (s : PS) Q ms,
    implM usegs (k s) s Q ms -> implM usegs (mbind mget k) s Q ms.
  Proof using Type. pin_using tt. intros. exact H0. Qed.

  Lemma set_rbuf_same : forall f, set_rbuf (f_rbuf f) f = f.
  Proof using Type. pin_using tt. intros f. destruct f; reflexivity. Qed.

  Theorem fread_o_proof : fread_stmt_o HO K.
  Proof using EQB HAL HFL KST. pin_using (fun (EQB HAL HFL KST : unit) => tt).
    intros until junk. intros SPO HIN -> -> -> -> NB DST CR.
    pose proof (spo_facts _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & SSP & BOK & LOR & LOB & SPM & Etp & AL & CEILLO & SP47).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_facts R CL FB f Af FILE_BLOCK BOK HIN) as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
    unfold FILE_BLOCK, STDIO_STACK in *.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    assert (LJ : length junk = Z.to_nat n) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
    assert (WFR : 0 <= wfn_of fs < 2^64) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw fs); cbn; lia).
    assert (LBR : 0 <= lbf_of fs < 2^64) by (unfold lbf_of; destruct (f_lbf_nl fs); cbn; lia).
    pose proof WBL as WBL'. unfold zlength in WBL'. rewrite BS in WBL'. unfold BUFSIZ in WBL'.
    (* [comment removed for export] *)
    unfold s_fread, Stdio.fread. apply implM_mget. unfold with_file.
    apply implM_bind_assoc. eapply implM_lookup_file; [exact LK|].
    unfold file_buf_addr, blk_addr.
    pose proof (HAL _ _ _ _ (f, Af, 1264) (proj1 G) ltac:(apply in_or_app; right; exact HIN)) as HADDR. cbn [cb_tok cb_addr fst snd] in HADDR. rewrite HADDR.
    (* [comment removed for export] *)
    assert (TAIL : forall (got : list Z) (f' : file_st) (m' : mem) (mode' flags' : word) (rp' : Z) (bufbytes' junk' : list byte)
                     (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
              munch [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024); (D, D + n)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
              stk usegs m' lo (bv_unsigned sp) ->
              FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
              0 <= zlength got <= n -> Forall (fun z => 0 <= z < 256) got ->
              rw_cells usegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
              implM usegs (mbind (store_file ps_libc set_libc eqb f f') (fun _ : unit => mret got)) s
                (fun got s' ms' => exists a0v mq junkq, hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v mq ms'
                   /\ ps_outfile s' = ps_outfile s /\ mem_inv usegs mq /\ stk usegs mq lo (bv_unsigned sp)
                   /\ agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (D <= a < D + n)) m mq
                   /\ GIo K R s' CL FB mq
                   /\ a0v = Z_to_bv 64 (zlength got) /\ 0 <= zlength got <= n /\ Forall (fun z => 0 <= z < 256) got
                   /\ rw_cells usegs mq D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junkq])
                (MS (mkR ra sp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 (zlength got)) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                    F (ret_pc ra) fc None m' (seg_rom usegs))).
    { intros got f' m' mode' flags' rp' bufbytes' junk' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MU WM MI' ST' FR' INV' GB GF DST'.
      unfold store_file. apply implM_upd_lc. apply implM_ret. apply evt_done.
      eexists _, m', junk'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|].
      split. { eapply (keeps_of_stdio R s CL FB m m' _ (bv_unsigned sp) (fun a => D <= a < D + n)); [exact G| exact MU| exact WM| | lia].
               apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]; cbn [fst snd].
               - left. lia.
               - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
               - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
               - right; right; right; right. intros a Ha. exact Ha. }
      split; [| split; [reflexivity| split; [exact GB| split; [exact GF| exact DST']]]].
      (* [comment removed for export] *)
      assert (MU' : exists W', munch W' m m' /\ Forall (stdio_iv R CL FB (bv_unsigned sp)) W').
      { destruct (Z_lt_le_dec 0 n) as [NP|NZ].
        - destruct CR as [CR|CR].
          + (* [comment removed for export] *)
            exists ([(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)] ++ map (fun b : cblk => (Z.max D (cb_addr b), Z.min (D + n) (cb_addr b + cb_size b))) CL).
            split.
            * intros x Hx. apply MU. assert (OA : forall W1 W2 y, outside (W1 ++ W2) y -> outside W1 y /\ outside W2 y).
              { induction W1 as [|[u v] W1 IH]; intros W2 y Hy; cbn in *; [split; [exact I| exact Hy]|]. destruct Hy as [Y1 Y2]. destruct (IH _ _ Y2) as [Y3 Y4]. repeat split; assumption. }
              destruct (OA _ _ _ Hx) as [O1 O2]. cbn [outside] in O1 |- *. destruct O1 as (O1a & O1b & O1c & _).
              split; [exact O1a|]. split; [exact O1b|]. split; [exact O1c|]. split; [| exact I].
              intros HDn. pose proof (CR (bv_unsigned x) HDn) as Hb. apply in_block_In in Hb as (b & HbIn & Hb).
              assert (OM : forall (L : list cblk) y, outside (map (fun b : cblk => (Z.max D (cb_addr b), Z.min (D + n) (cb_addr b + cb_size b))) L) y ->
                             forall b', In b' L -> ~ (Z.max D (cb_addr b') <= y < Z.min (D + n) (cb_addr b' + cb_size b'))).
              { induction L as [|c L IHL]; intros y Hy b' Hb'; [destruct Hb'|]. cbn in Hy. destruct Hy as [Y1 Y2]. destruct Hb' as [<-|Hb']; [exact Y1| apply IHL; assumption]. }
              apply (OM CL (bv_unsigned x) O2 b HbIn). lia.
            * apply Forall_app. split.
              -- unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
                 ++ left. lia.
                 ++ right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
                 ++ right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
              -- apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b & <- & HbIn). unfold stdio_iv. right; left.
                 unfold iv_in_block. apply Exists_exists. exists b. split; [apply in_or_app; left; exact HbIn| cbn [fst snd]; lia].
          + (* [comment removed for export] *)
            exists [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024); (D, D + n)]. split; [exact MU|].
            unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]; cbn [fst snd].
            * left. lia.
            * right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
            * right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
            * left. destruct CR as [CR1 CR2]. split; lia.
        - (* [comment removed for export] *)
          exists [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]. split.
          + intros x Hx. apply MU. cbn [outside] in Hx |- *. destruct Hx as (O1 & O2 & O3 & _). repeat split; try assumption. lia.
          + unfold stdio_iv. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
            * left. lia.
            * right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia].
            * right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [apply in_or_app; right; exact HIN| cbn; lia]. }
      destruct MU' as (W' & MUW & HW).
      eapply (GIo_stdio_step R s CL FB m m' W' (bv_unsigned sp)); [exact G| exact MUW| exact WM| exact HW| exact SPM|].
      cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
      pose proof BOK as [BO BA]. pose proof BO as BO'. apply Forall_app in BO'. destruct BO' as [BO1 BO2].
      (* [comment removed for export] *)
      assert (AGS : agrees_on (fun a => S3.GI.TwB.stdio_static a) m m').
      { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. unfold S3.GI.TwB.stdio_static in Hs. cbn [outside].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [| exact I].
        intros HDa. destruct (Z_lt_le_dec 0 n) as [NP|NZ]; [| lia].
        destruct (client_range_lo R s CL FB m (bv_unsigned sp) D n lo G CR NP LOR ltac:(lia)) as (C1 & C2 & C3 & C4). lia. }
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      Ltac trs2 AGS A := eapply agrees_rw_cells; [exact AGS | exact A | intros a Ha; unfold S3.GI.TwB.stdio_static; cbn in Ha; lia].
      split. { eapply FILE_R_agree; [exact SO | exact AGS | intros a Ha; unfold S3.GI.TwB.stdio_static; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; unfold S3.GI.TwB.stdio_static; lia]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AGS | intros a Ha; unfold S3.GI.TwB.stdio_static; lia | rewrite SEbs; intros a Ha; unfold S3.GI.TwB.stdio_static; lia]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AGS | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; unfold S3.GI.TwB.stdio_static; lia. }
      split; [trs2 AGS U1|]. split; [trs2 AGS U2|]. split; [trs2 AGS U3|]. split; [trs2 AGS OL|]. split; [trs2 AGS OH|].
      split.
      2:{ rewrite files_update_keys. exact ND. }
      apply UPD; [exact FR'| exact INV'|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2 FR2 INV2.
      pose proof INV2 as (_ & _ & BS2 & _).
      destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB q2 A2 n2 FS ND HIN2) as (f2' & pv2' & nx2' & _ & En2 & _). subst n2.
      pose proof (file_block_facts R CL FB q2 A2 FILE_ALLOC BOK HIN2) as (B1 & B2 & B3 & B4 & B5 & B6). unfold FILE_ALLOC in B3, B4, B5, B6.
      assert (AP : A2 + 1264 <= Af \/ Af + 1264 <= A2).
      { destruct (GIo_apart K R s CL FB m (q2, A2, FILE_ALLOC) (f, Af, 1264) G ltac:(apply in_or_app; right; exact HIN2) ltac:(apply in_or_app; right; exact HIN)) as [E|AP].
        - exfalso. apply NE2. congruence.
        - unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
      assert (APD : n = 0 \/ D + n <= A2 \/ A2 + 1264 <= D).
      { destruct (Z_lt_le_dec 0 n) as [NP|NZ]; [right | left; lia].
        exact (client_range_apart R CL FB (bv_unsigned sp) D n q2 A2 FILE_ALLOC BOK HIN2 CR NP ltac:(lia) ltac:(unfold FILE_ALLOC; lia)). }
      eapply (FILE_R_agree (fun a => A2 <= a < A2 + 1264)); [exact FR2| | intros a Ha; lia | intros a Ha; rewrite BS2 in Ha; unfold BUFSIZ, FILE_BUF_OFF in Ha; lia].
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hb. cbn [outside]. (keep_hyps CEILV sp R Af D n lo junk fs A2 a LOR CEILLO B4 AP APD Hb; lia). }
    (* [comment removed for export] *)
    destruct (Z.eq_dec n 0) as [NZ|NZ].
    { (* [comment removed for export] *)
      subst n.
      assert (HDm : exists D', (Z_to_bv 64 D : word) = Z_to_bv 64 D' /\ 0 <= D' < 2^64).
      { exists (D mod 2^64). split; [symmetry; apply Z_to_bv_mod64| apply Z.mod_pos_bound; lia]. }
      destruct HDm as (D' & -> & HD').
      eapply implM_bind.
      { unfold fcells in FC.
        eapply (fread_zero_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail lo m)
          with (flags := flags) (mode := mode) (rp := rp) (wfn := wfn_of fs) (fd := f_fd fs) (lbf := lbf_of fs) (D := D') (Dm := D);
          rewrite ?BS in *; unfold BUFSIZ, FILE_BUF_OFF in *;
          first [ exact FC | exact ST | exact MI | (keep_hyps CEILV sp Af D lo junk fs LOB R SPM SP47 A0 LOR CEILLO FA4 rp tail RP WFR FD LBR D' HD'; lia) | destruct (f_wactive fs); unfold zlength in *; (keep_hyps CEILV sp R Af D lo junk fs A0 FA4 FA1 WBL'; lia)
                | match goal with |- ?g => idtac "ZLEFT:" g end ]. }
      cbv beta. intros r st' ms' (-> & -> & PO).
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & m' & -> & MU & WM & MI' & ST' & FC').
      cbn [fst snd]. rewrite set_rbuf_same.
      replace (Z_to_bv 64 0 : word) with (Z_to_bv 64 (zlength (@nil Z)) : word) by reflexivity.
      eapply (TAIL [] fs m' mode' flags rp bufbytes junk); try assumption.
      - eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
      - exists flags, mode', rp, tail, bufbytes. split; [unfold fcells in *; rewrite ?BS in FC' |- *; unfold BUFSIZ, FILE_BUF_OFF in *; exact FC'|].
        split; [exact FL|]. split; [| split; [exact BP| split; [exact WB0| split; [exact WBL| split; [exact RR| exact RP]]]]].
        eapply rw_cells_transport; [exact BUF| exact MU| exact WM|]. rewrite BS. cbn. unfold BUFSIZ, FILE_BUF_OFF. lia.
      - unfold zlength. cbn. lia.
      - constructor.
      - cbn [length map Z.to_nat Nat.sub]. replace junk with (@nil byte) by (destruct junk; [reflexivity| cbn in LJ; lia]).
        apply rw_cells_CB0. apply rw_cells_nil0; lia. }
    destruct (f_nord fs) eqn:NORD.
    { (* [comment removed for export] *)
      pose proof (NORDi eq_refl) as RBN.
      destruct (client_range_lo R s CL FB m (bv_unsigned sp) D n lo G CR ltac:(lia) LOR ltac:(lia)) as (C1 & C2 & C3 & C4).
      eapply implM_bind.
      { eapply (fread_nord_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail lo (rc_canary R) m)
          with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes);
          rewrite ?BS in *; rewrite ?RBN in *; unfold BUFSIZ, FILE_BUF_OFF, got_ssp, ssp_guard in *;
          first [ exact FC | exact ST | exact MI | exact SSP | exact FLn | exact FLe | exact FLsvb | exact BP | exact WB0 | exact NCH | exact FD | reflexivity
                | rewrite NORD; first [exact FLn | reflexivity]
                | unfold zlength in *; cbn [length Z.of_nat] in *; (keep_hyps CEILV sp Af D n lo junk fs rp tail LOB R LOR CEILLO SPM SP47 A0 FA4 bufbytes FA5 WBL RP NB NZ; lia)
                | match goal with |- rw_cells _ _ Af _ => unfold zlength in FC; cbn [length Z.of_nat] in FC; rewrite Z.add_0_r in FC; exact FC end
                | exact BUF
                | match goal with |- ?g => idtac "NLEFT:" g end ]. }
      cbv beta. intros r st' ms' []. }
    (* [comment removed for export] *)
    assert (NOWR : f_nowr fs = true) by (destruct (f_nowr fs) eqn:E; [reflexivity| cbn in NRW; congruence]).
    destruct (NOWRi NOWR) as [WACT WBN].
    destruct (client_range_lo R s CL FB m (bv_unsigned sp) D n lo G CR ltac:(lia) LOR ltac:(lia)) as (C1 & C2 & C3 & C4).
    pose proof (client_range_apart R CL FB (bv_unsigned sp) D n f Af 1264 BOK HIN CR ltac:(lia) ltac:(lia) ltac:(lia)) as APD.
    rewrite WACT in FC.
    eapply implM_bind.
    { eapply (fread_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail D n lo (rc_canary R) m)
        with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes) (djunk := junk);
        rewrite ?BS in *; unfold BUFSIZ, FILE_BUF_OFF, FREAD_DEPTH, got_ssp, ssp_guard in *;
        first [ exact FC | exact FL | exact ST | exact MI | exact SSP | exact BP | exact DST | exact RR | exact WACT | exact WBN | exact NCH | exact FD | exact RBR | reflexivity
              | exact BUF
              | unfold rc_spmain in *; (keep_hyps CEILV sp Af D n junk fs NB lo LOB R LOR CEILLO SPM SP47 A0 FA4 FA5 C4 C1 C3 C2 APD rp tail RP; lia)
              | match goal with |- ?g => idtac "RLEFT:" g end ]. }
    cbv beta. intros [got f'] st' ms' (-> & INV' & GB & GF & GRB & PO). cbn [fst snd] in INV', GB, GF, GRB, PO |- *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & flags' & mode' & rp' & bufbytes' & rest' & m' & -> & MU & WM & MI' & ST' & FC' & FL' & BUF' & RR' & RP1' & RP2' & DST' & SSP').
    unfold fr_W, FREAD_DEPTH in MU. rewrite ?BS in MU. unfold BUFSIZ in MU.
    pose proof INV' as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
    eapply (TAIL got f' m' mode' flags' rp' bufbytes' rest'); try assumption.
    - eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. (keep_hyps CEILV sp R Af D n lo junk fs got x LOB Hx; lia).
    - exists flags', mode', rp', tail, bufbytes'. rewrite I6, I7, I1, I3, BS.
      split. { unfold fcells, BUFSIZ, FILE_BUF_OFF in *. rewrite BS in FC'. unfold zlength in FC' |- *. cbn [length Z.of_nat] in FC' |- *. exact FC'. }
      split; [exact FL'|]. split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite BS in BUF'; exact BUF'|]. split; [reflexivity|]. split; [intros _; reflexivity|].
      split; [unfold zlength, BUFSIZ; cbn [length Z.of_nat]; lia|].
      split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite BS in RR'; exact RR'| exact (conj RP1' (conj RP2' (proj2 (proj2 RP))))].
    - unfold heap_file_inv. rewrite I1, I2, I3, I4, I5, I6, I7, NORD.
      split; [exact NCH|]. split; [exact FD|]. split; [exact BS|]. split; [exact NRW|].
      split; [intros _; split; reflexivity|]. split; [intros X; discriminate X| exact GRB].
    - unfold zlength in GB |- *. lia.
  Qed.
End GlueRd.

End WithCeil.
End TwB.
End Stdio_glue_rd.

(* [comment removed for export] *)
Module F_fmt_errmsg.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_strerror__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_strerror OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Vsn_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_err.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac pstep := step; fix_lit_store.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Section WithCeil.
Context {CEILV : CEIL}.
Lemma length_list_ascii fs : length (String.list_ascii_of_string fs) = String.length fs.
Proof using Type. pin_using tt. induction fs as [|c fs IH]; cbn; [reflexivity| now rewrite IH]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition item_bytes_in (P : Z -> Prop) (it : fitem) : Prop :=
  match it with FLit l => Forall P l | FConv _ => True | FBad l => Forall P l end.

Lemma take_lit_sub : forall s l r, take_lit s = (l, r) -> s = l ++ r.
Proof using Type. pin_using tt.
  induction s as [|c s IH]; intros l r E; cbn in E.
  - inversion E; subst. reflexivity.
  - destruct (c =? 37).
    + inversion E; subst. reflexivity.
    + destruct (take_lit s) as [l0 r0] eqn:E0. inversion E; subst.
      cbn. f_equal. apply IH. reflexivity.
Qed.

Definition parse_conv_suffix__stmt : Prop := forall s c r, parse_conv s = Some (c, r) -> exists p, s = p ++ r.
Section Sz2.
Variables s c r : ltac2:(SecDiet.SzSec.tyM 'parse_conv_suffix__stmt "vvv" @s).
Lemma parse_conv_suffix__body : ltac2:(SecDiet.SzSec.bodyP 'parse_conv_suffix__stmt "vvv").
Proof using Type. pin_using tt.
  intros E.
 unfold parse_conv in E.
  repeat (cbn in E; lazymatch type of E with
          | context [match ?x with _ => _ end] => is_var x; destruct x; try discriminate E
          | _ => fail end).
  all: inversion E; subst.
  all: lazymatch goal with
       | |- exists p, ?a :: ?b :: ?c :: ?t = p ++ ?t => exists [a; b; c]; reflexivity
       | |- exists p, ?a :: ?b :: ?t = p ++ ?t => exists [a; b]; reflexivity
       | |- exists p, ?a :: ?t = p ++ ?t => exists [a]; reflexivity
       end.
Qed.
End Sz2.
Lemma parse_conv_suffix : ltac:(let t := eval cbv delta [parse_conv_suffix__stmt] in parse_conv_suffix__stmt in exact t).
Proof using Type. intros s c r. ltac2:(SecDiet.SzSec.closeP 'parse_conv_suffix__body "vvv"). Qed.

Lemma parse_fmt_aux_bytes : forall (P : Z -> Prop) fuel s,
  Forall P s -> Forall (item_bytes_in P) (parse_fmt_aux fuel s).
Proof using Type. pin_using tt.
  induction fuel as [|fuel IH]; intros s Hs; cbn [parse_fmt_aux].
  - destruct s; constructor; [exact Hs| constructor].
  - destruct s as [|c s']; [constructor|].
    destruct (Z.eq_dec c 37) as [->|NE].
    + cbn. destruct (parse_conv s') as [[cv r]|] eqn:E.
      * constructor; [exact I|]. apply IH. destruct (parse_conv_suffix _ _ _ E) as [p ->].
        apply Forall_inv_tail in Hs. apply Forall_app in Hs. tauto.
      * constructor; [exact Hs| constructor].
    + replace (match c with 37 => _ | _ => let (l, r) := take_lit (c :: s') in FLit l :: parse_fmt_aux fuel r end)
        with (let (l, r) := take_lit (c :: s') in FLit l :: parse_fmt_aux fuel r).
      2:{ destruct c as [|p|p]; try reflexivity. repeat (destruct p; try reflexivity). exfalso; apply NE; reflexivity. }
      destruct (take_lit (c :: s')) as [l r] eqn:E.
      pose proof (take_lit_sub _ _ _ E) as Hsplit.
      rewrite Hsplit in Hs. apply Forall_app in Hs as [Hl Hr].
      constructor; [exact Hl| apply IH; exact Hr].
Qed.

Lemma str_bytes : forall s, Forall (fun z => 0 <= z < 256) (str s).
Proof using Type. pin_using tt.
  intros s. unfold str. apply Forall_map. apply Forall_forall. intros a _.
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.

Lemma fmt_bytes : forall fs, Forall (item_bytes_in (fun z => 0 <= z < 256)) (fmt fs).
Proof using Type. pin_using tt. intros fs. unfold fmt, parse_fmt. apply parse_fmt_aux_bytes. apply str_bytes. Qed.

(* [comment removed for export] *)
Lemma items_ok_okb : forall its args,
  Forall (item_bytes_in (fun z => 0 <= z < 256)) its -> items_ok its args = true -> items_okb its = true.
Proof using Type. pin_using tt.
  induction its as [|it its IH]; intros args HB HO; [reflexivity|].
  apply Forall_cons_iff in HB as [HBi HB]. cbn [items_ok] in HO. change (items_okb (it :: its)) with (item_okb it && items_okb its)%bool.
  destruct it as [l|c|l]; cbn [item_okb].
  - apply andb_prop in HO as [Hl HO]. rewrite (IH _ HB HO), andb_true_r.
    unfold bytes_okb. apply forallb_forall. intros z Hz.
    pose proof (proj1 (forallb_forall _ _) Hl z Hz) as Hz'. cbn in Hz'.
    pose proof (proj1 (Forall_forall _ _) HBi z Hz) as Hb. cbn in Hb.
    apply andb_prop in Hz' as [H0 _]. destruct (Z.eqb_spec z 0); [discriminate|].
    apply andb_true_intro; split; [apply Z.ltb_lt; lia| apply Z.ltb_lt; lia].
  - destruct args as [|a args']; [discriminate|]. apply andb_prop in HO as [_ HO]. exact (IH _ HB HO).
  - discriminate.
Qed.

Lemma fmt_ok_items_okb : forall fs args, fmt_ok fs args = true -> items_okb (fmt fs) = true.
Proof using Type. pin_using tt.
  intros fs args H. unfold fmt_ok in H. apply andb_prop in H as [H _].
  exact (items_ok_okb _ _ (fmt_bytes fs) H).
Qed.

(* [comment removed for export] *)
Lemma map_b8_no_nul : forall l, bytes_ok l -> ~ In (Z_to_bv 8 0) (map b8 l).
Proof using Type. pin_using tt.
  induction l as [|z l IH]; intros HB Hin; [exact Hin|].
  apply Forall_cons_iff in HB as [Hz HB]. cbn [map] in Hin. destruct Hin as [E|Hin]; [| exact (IH HB Hin)].
  unfold b8 in E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_small in E by (unfold bv_modulus; cbn; lia). lia.
Qed.
Lemma map_unsigned_b8 : forall l, bytes_ok l -> map bv_unsigned (map b8 l) = l.
Proof using Type. pin_using tt.
  induction l as [|z l IH]; intros HB; [reflexivity|]. apply Forall_cons_iff in HB as [Hz HB]. cbn [map]. f_equal; [| exact (IH HB)].
  unfold b8. apply Z_to_bv_small. unfold bv_modulus. cbn. lia.
Qed.
(* [comment removed for export] *)
Lemma farg_words_ok : forall {hptr} R (CL : list (@cblock hptr)) SP D dn m args ws,
  Forall2 (farg_word R CL SP D dn m) args ws -> Forall arg_ok args.
Proof using Type. pin_using tt.
  intros hptr R CL SP D dn m args ws FW. induction FW as [|a w args' ws' Ha _ IH]; constructor; [| exact IH].
  destruct a as [v|cs]; cbn [arg_ok farg_word] in *; [exact Logic.I|].
  destruct Ha as (P & bs & slack & _ & _ & NN & -> & _). apply bytes_ok_of_bytes. exact NN.
Qed.

(* [comment removed for export] *)
Lemma client_range_sub : forall {hptr} R (CL : list (@cblock hptr)) SP SP' A n A' n',
  client_range R CL SP A n -> (SP' <= SP)%Z -> (A <= A')%Z -> (A' + n' <= A + n)%Z -> client_range R CL SP' A' n'.
Proof using Type. pin_using tt.
  intros hptr R CL SP SP' A n A' n' [HB|HS] H1 H2 H3; [left; intros a Ha; apply HB; lia| right; lia].
Qed.

(* [comment removed for export] *)
Lemma farg_word_frame : forall {H hptr} (K : modkit H hptr) R s (CL FB : list (@cblock hptr)) SP SP' D dn m m' W a w,
  GIo K R s CL FB m ->
  farg_word R CL SP D dn m a w -> (SP' <= SP)%Z -> (SP mod 8 = 0)%Z ->
  agrees_on (fun x => outside W x) m m' -> Forall (fun iv => alloc_ceiling <= fst iv /\ snd iv <= SP)%Z W ->
  farg_word R CL SP' D dn m' a w.
Proof using Type. pin_using tt.
  intros H hptr K R s CL FB SP SP' D dn m m' W a w G FWa LE AL8 AG HW.
  destruct a as [v|cs]; cbn [farg_word] in *; [exact FWa|].
  destruct FWa as (P & bs & slack & -> & HB & NN & -> & LEN & SLK & DIS & LOC).
  set (k := ((- (P + Z.of_nat (length bs) + 1)) mod 8)%Z) in *.
  assert (Hk : (0 <= k < 8)%Z) by (subst k; apply Z.mod_pos_bound; lia).
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
  (* [comment removed for export] *)
  assert (HB' : bytes_at ssegs m P ((bs ++ [Z_to_bv 8 0]) ++ firstn (Z.to_nat k) slack)).
  { rewrite <- app_assoc. cbn [app].
    rewrite <- (firstn_skipn (Z.to_nat k) slack) in HB.
    change (bs ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) slack ++ skipn (Z.to_nat k) slack) with (bs ++ ([Z_to_bv 8 0] ++ (firstn (Z.to_nat k) slack ++ skipn (Z.to_nat k) slack))) in HB.
    rewrite !app_assoc in HB. apply (proj1 (bytes_at_app _ _ _ _ _)) in HB. destruct HB as [HB _].
    rewrite <- !app_assoc in HB. exact HB. }
  assert (LK : length (firstn (Z.to_nat k) slack) = Z.to_nat k) by (rewrite length_firstn; lia).
  (* [comment removed for export] *)
  assert (RNG : (P + Z.of_nat (length bs) + 1 + k <= alloc_ceiling \/ SP <= P)%Z).
  { destruct LOC as [[HBk|HS]|[HR|HT]].
    - left. destruct (GIo_CLc_facts K R s CL [] FB m P ltac:(rewrite app_nil_r; exact G) ltac:(apply HBk; lia)) as [HC _].
      pose proof (GIo_CLc_facts K R s CL [] FB m (P + Z.of_nat (length bs))%Z ltac:(rewrite app_nil_r; exact G) ltac:(apply HBk; lia)) as [[_ HC2] _].
      (* [comment removed for export] *)
      subst k. clear - HC2 BB. Z.div_mod_to_equations. lia.
    - right. lia.
    - left. subst k. clear - HR BB. Z.div_mod_to_equations. lia.
    - left. pose proof (GIo_tls K _ _ _ _ _ G) as [_ TB]. unfold tls_block_ok in TB. subst k. clear - HT TB Hk. lia. }
  exists P, bs, (firstn (Z.to_nat k) slack).
  split; [reflexivity|]. split.
  { eapply agrees_bytes_at; [exact AG | rewrite <- app_assoc in HB'; cbn [app] in HB'; exact HB' |].
    intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. rewrite LK in Hx. cbv beta.
    apply (outside_of_Forall _ _ _ HW). intros iv [H1 H2]. destruct RNG as [R1|R2]; lia. }
  split; [exact NN|]. split; [reflexivity|]. split; [exact LEN|]. split; [rewrite LK; lia|]. split; [rewrite LK; clear -DIS Hk SLK; lia|].
  destruct LOC as [HC|[HR|HT]]; [left; eapply client_range_sub; [exact HC| lia | lia | lia] | right; left; exact HR | right; right].
  rewrite LK. lia.
Qed.

Lemma farg_words_frame : forall {H hptr} (K : modkit H hptr) R s (CL FB : list (@cblock hptr)) SP SP' D dn m m' W args ws,
  GIo K R s CL FB m -> (SP' <= SP)%Z -> (SP mod 8 = 0)%Z ->
  agrees_on (fun x => outside W x) m m' -> Forall (fun iv => alloc_ceiling <= fst iv /\ snd iv <= SP)%Z W ->
  Forall2 (farg_word R CL SP D dn m) args ws -> Forall2 (farg_word R CL SP' D dn m') args ws.
Proof using Type. pin_using tt.
  intros H hptr K R s CL FB SP SP' D dn m m' W args ws G LE AL AG HW FW.
  induction FW; constructor; [eapply farg_word_frame; eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma outside_In_not : forall W x iv, outside W x -> In iv W -> ~ (fst iv <= x < snd iv)%Z.
Proof using Type. pin_using tt.
  induction W as [|[lo hi] W IH]; intros x iv Ho Hin; [destruct Hin|].
  cbn in Ho. destruct Ho as [H1 H2]. destruct Hin as [<-|Hin]; [cbn; lia| exact (IH _ _ H2 Hin)].
Qed.
Lemma GIo_client_frame_cr : forall {H hptr} (K : modkit H hptr) (HFL : heap_frame_law K) (SFL : stdio_fp_law K)
    R s (CL FB : list (@cblock hptr)) m m' lo' hi A n SP,
  GIo K R s CL FB m -> munch [(lo', hi); (A, A + n)]%Z m m' -> wmono ssegs m m' ->
  (rc_lo R <= lo')%Z -> (hi <= rc_spmain R)%Z -> (rc_lo R <= SP)%Z -> client_range R CL SP A n ->
  GIo K R s CL FB m'.
Proof using Type. pin_using tt.
  intros H' hptr' K' HFL' SFL' R' s' CL' FB' mA mB lo' hi A n SP G' MU WM H1 H2 H3 CR'.
  destruct CR' as [HB|HS].
  - eapply (GIo_client_frame K' HFL' SFL') with (W := ((lo', hi) :: map (fun b => (Z.max A (cb_addr b), Z.min (A + n) (cb_addr b + cb_size b)))%Z CL')); [exact G' | | exact WM |].
    + eapply munch_weaken; [| exact MU]. intros x Ho. cbn in Ho |- *. destruct Ho as [Hx Ho]. split; [exact Hx|]. split; [| exact Logic.I].
      intros Hin. destruct (proj1 (in_block_In _ _) (HB x Hin)) as (b & Hb & Hxb).
      apply (outside_In_not _ _ _ Ho (in_map _ _ _ Hb)). cbn [fst snd]. lia.
    + constructor; [left; cbn [fst snd]; lia|]. apply Forall_map. apply Forall_forall. intros b Hb. right.
      unfold iv_in_block. apply Exists_exists. exists b. split; [exact Hb|]. cbn [fst snd]. lia.
  - eapply (GIo_client_frame K' HFL' SFL'); [exact G' | exact MU | exact WM |].
    constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia| constructor].
Qed.

(* [comment removed for export] *)
Lemma snprintf_length_le : forall n f args, (1 <= n)%Z -> (Z.of_nat (length (Fmt.snprintf n f args)) <= n - 1)%Z.
Proof using Type. pin_using tt. intros n f args Hn. unfold Fmt.snprintf, snprintf_out. rewrite length_firstn. lia. Qed.

Lemma strerror_len : forall e, (-2^31 <= e < 2^31)%Z -> (length (Fmt.strerror e) <= 40)%nat.
Proof using Type. pin_using tt.
  intros e He. pose proof (strerror_msgb_length e) as ML. rewrite (strerror_tables_agree e He), length_map in ML. exact ML.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End WithCeil.

Open Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Section FmtErrmsg.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis VSNPRINTF : vsnprintf_spec4_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis STRERROR : pcap_strerror_stmt K.

  Definition fmt_errmsg_proof__stmt : Prop := fmt_errmsg_stmt K.
  Section Sz18.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo EB FMTA e fs junk : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv" @ra).
  Lemma fmt_errmsg_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv").
  Proof using HFL SFL SNPRINTF STRERROR VSNPRINTF. pin_using (fun (HFL SFL SNPRINTF STRERROR VSNPRINTF : unit) => tt).
    intros args PRE -> -> -> HE -> FMT5 FOK LA FW HEB CR E8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. unfold rc_lo in LO. unfold PCAP_L1_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    pose proof (GIo_tls K _ _ _ _ _ G) as [_ TB]. unfold tls_block_ok in TB.
    assert (CLB : forall a, in_block CL a -> (0 < a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact Hc. }
    (* [comment removed for export] *)
    assert (EBR : (EB + 256 <= alloc_ceiling \/ bv_unsigned sp <= EB)%Z).
    { destruct CR as [HBk|HS]; [left| right; lia]. pose proof (CLB _ (HBk (EB + 255)%Z ltac:(lia))). lia. }
    assert (EBT : (EB + 256 <= utp R - 200 \/ utp R - 200 + 4096 <= EB)%Z).
    { destruct CR as [HBk|HS].
      - (* [comment removed for export] *)
        assert (PW : forall a, (EB <= a < EB + 256)%Z -> ~ (utp R - 200 <= a < utp R - 200 + 4096)%Z).
        { intros a Ha Hin. pose proof (HBk a Ha) as Hb. unfold in_block in Hb. apply Exists_exists in Hb as (b & Hinb & Hab).
          pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; left; exact Hinb)) as (_ & _ & _ & _ & _ & B6).
          cbn [cb_addr cb_size] in Hab, B6. lia. }
        destruct (Z.lt_ge_cases (EB + 255) (utp R - 200)) as [X|X]; [left; lia|].
        destruct (Z.le_gt_cases (utp R - 200 + 4096) EB) as [Y|Y]; [right; lia|].
        exfalso. destruct (Z.le_gt_cases EB (utp R - 200)) as [Z1|Z1].
        + apply (PW (utp R - 200)%Z); lia.
        + apply (PW EB); lia.
      - right. lia. }
    pose proof (farg_words_ok _ _ _ _ _ _ _ _ FW) as AOK.
    pose proof (fmt_ok_items_okb _ _ FOK) as IOK.
    set (out := Fmt.snprintf 256 fs args). set (len := length out).
    pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LENB. fold out len in LENB.
    pose proof (snprintf_ok 256 fs args IOK AOK) as OUTOK. fold out in OUTOK.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    hide HEB.
    unfold PCAP_FMT_ERRMSG_ENTRY. carve_frame 80%nat ST.
    apply (rw_cells_split_CB ssegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB _ ?t] =>
      lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
    do 18 pstep.
    unhide HEB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGP : agrees_on (fun a => outside [(bv_unsigned sp - 80, bv_unsigned sp)]%Z a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m0 end.
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HEB; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    assert (G0 : GIo K R s CL FB m0).
    { eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    assert (FMT0 : fmt_at m0 FMTA fs).
    { destruct FMT5 as [FB5 FR5]. split; [|exact FR5]. eapply agrees_bytes_at; [exact AGP | exact FB5 |].
      intros a Ha. rewrite length_app, length_map in Ha. cbn [length] in Ha. cbn [outside]. rewrite length_list_ascii in Ha. unfold rc_lo in *. lia. }
    assert (FW0 : Forall2 (farg_word R CL (bv_unsigned sp + -80) EB 256 m0) args (firstn (length args) [a4])).
    { eapply (farg_words_frame K _ _ _ _ (bv_unsigned sp) _ _ _ _ _ [(bv_unsigned sp - 80, bv_unsigned sp)]%Z);
        [exact G | lia | clear - ALN; Z.div_mod_to_equations; lia | exact AGP | | exact FW].
      apply Forall_cons; [cbn [fst snd]; unfold rc_lo in *; lia| apply Forall_nil]. }
    clear MU WM FW FMT5.
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 6 FR) as [FRL FRA]. cbn [firstn skipn cells_size csize Nat.add] in FRL, FRA.
    replace (bv_unsigned sp + -80 + Z.of_nat 48)%Z with (bv_unsigned sp + -32)%Z in FRA by lia.
    (* [comment removed for export] *)
    destruct args as [|x1 [|x2 args2]]; [ | | cbn [length] in LA; exfalso; lia].
    all: cbn [length firstn] in FW0.
    1: destruct (rw_cells_cut _ _ _ 0 FRA) as [AP0 _]; cbn [firstn skipn cells_size csize Nat.add] in AP0.
    2: destruct (rw_cells_cut _ _ _ 1 FRA) as [AP0 _]; cbn [firstn skipn cells_size csize Nat.add] in AP0.
    all: step; name_sp sp (-80)%Z.
    all: lazymatch type of FW0 with Forall2 _ ?xargs ?xws => eapply evt_cut; [ (eapply (VSNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo EB 256%Z FMTA (bv_unsigned sp + -32)%Z fs xargs xws junk);
        [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact FMT0 | exact FOK
        | reflexivity | cbn; lia | rewrite Hsp; exact FW0
        | first [exact AP0 | cbn [map]; exact AP0] | rewrite Hsp; lia | cbn [length]; lia | cbn [length]; lia | exact HEB
        | eapply client_range_sub; [exact CR | rewrite Hsp; lia | lia | lia] ]) |] end.
    all: cbv beta; intros ms' PO; destruct PO as (av & m1 & junk1 & E & MU1 & WM1 & MI1 & ST1 & -> & HD1);
         unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hsp in *; unname_sp.
    all: replace (ret_pc (Z_to_bv 64 84224)) with (Z_to_bv 64 84224) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    1: rename FW0 into FWX; generalize dependent (@nil farg).
    2: rename FW0 into FWX; clear AP0; generalize dependent [x1].
    all: intros args FOK LA AOK out len LENB OUTOK FWX HD1; clear FWX LA.
    all: unfold STDIO_STACK in MU1.
    all: assert (AG1 : agrees_on (fun a => outside [(bv_unsigned sp + -80 - 65536, bv_unsigned sp + -80); (EB, EB + 256)]%Z a) m0 m1)
           by (eapply agrees_on_of_munch; [exact MU1 | exact WM1 | intros a _ Ho; exact Ho]).
    all: apply (agrees_rw_cells _ _ _ _ _ AG1) in FRL; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG1) in FRA; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: assert (G1 : GIo K R s CL FB m1)
           by (eapply (GIo_client_frame_cr K HFL SFL); [exact G0 | exact MU1 | exact WM1 | unfold rc_lo; lia | lia | | exact CR]; unfold rc_lo; lia).
    all: assert (AG01 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m1)
           by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGP| intros a [[Ha|Ha] Hn]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]]|];
               eapply agrees_on_weaken; [exact AG1| intros a [[Ha|Ha] Hn]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]]).
    all: clear AGP MU1 WM1 G0 MI FR ST AG1; try clear AP0.
    all: change (Z.to_nat 256) with 256%nat in HD1; fold out in HD1; fold len in HD1.
    all: assert (LJ1 : length junk1 = (255 - len)%nat) by (destruct HD1 as [[WF _] _]; cbn [cells_wf cell_wf csize] in WF; rewrite length_app, length_map in WF; cbn [length] in WF; lia).
    (* [comment removed for export] *)
    all: hide FRL; hide FRA.
    all: pose proof (munch_refl ([] : list (Z * Z)) m1) as MU; pose proof (wmono_refl ssegs m1) as WM.
    all: do 2 step.
    all: eapply evt_cut; [ eapply (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (map b8 out) junk1);
        [ rewrite unsigned_lit by lia; pose proof (rw_cells_bytes_at _ _ _ _ HD1) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r, <- app_assoc in X; exact X
        | apply map_b8_no_nul; exact OUTOK
        | rewrite unsigned_lit, length_map, LJ1 by lia; fold len; clear - E8 LENB BEB; Z.div_mod_to_equations; lia
        | exact MI1 ] |].
    all: cbv beta; intros ms' PO; destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m2 & -> & MU2 & WM2 & MI2 & _).
    all: replace (ret_pc (Z_to_bv 64 84232)) with (Z_to_bv 64 84232) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: rewrite length_map; fold len.
    all: assert (AG2 : agrees_on (fun _ => True) m1 m2) by (eapply agrees_on_of_munch; [exact MU2 | exact WM2 | intros a _ _; cbn; exact Logic.I]).
    all: unhide FRL; unhide FRA.
    all: apply (agrees_rw_cells _ _ _ _ _ AG2) in FRL; [| intros; exact Logic.I].
    all: apply (agrees_rw_cells _ _ _ _ _ AG2) in FRA; [| intros; exact Logic.I].
    all: apply (agrees_rw_cells _ _ _ _ _ AG2) in HD1; [| intros; exact Logic.I].
    all: assert (G2 : GIo K R s CL FB m2) by (eapply (GIo_client_frame K HFL SFL); [exact G1 | exact MU2 | exact WM2 | apply Forall_nil]).
    all: assert (ST2 : stk ssegs m2 lo (bv_unsigned sp + -80)) by (eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn; exact Logic.I]).
    all: assert (AG02 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m2)
           by (eapply agrees_on_trans; [exact AG01 | eapply agrees_on_weaken; [exact AG2| intros; exact Logic.I]]).
    all: clear MU WM MU2 WM2 AG2 MI1 ST1 G1 AG01 HEB FMT0.
    all: pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp + -80); (EB + Z.of_nat len, EB + Z.of_nat len + 3)]%Z m2) as MU; pose proof (wmono_refl ssegs m2) as WM.
    all: hide FRA; hide HD1.
    all: step; step; if_cases Kr; zify_cond Kr.
    (* [comment removed for export] *)
    1,3: unhide FRA; unhide HD1; do 6 step.
    1,2: pose proof (rw_cells_uncut _ _ _ _ _ FRL FRA ltac:(cbn; lia)) as FR; cbn [app] in FR; release_frame FR ST2 (bv_unsigned sp).
    1,2: apply evt_done; do 17 eexists; split; [reflexivity|].
    1,2: split; [exact MI2|]; split; [assumption|]; split; [exact AG02|]; split; [exact G2|].
    1,2: unfold fmt_errmsg, PCAP_ERRBUF_SIZE; fold out; unfold zlength; fold len;
         replace (256 <? Z.of_nat len + 3) with true by (symmetry; apply Z.ltb_lt; lia);
         replace (255 - length out)%nat with (256 - len - 1)%nat by (subst len; lia); exact HD1.
    (* [comment removed for export] *)
    all: assert (L2 : (2 <= length junk1)%nat) by lia.
    all: destruct junk1 as [|jb0 [|jb1 jrest]]; try (exfalso; cbn [length] in L2; lia); cbn [length] in LJ1.
    all: unhide HD1;
         assert (HD5 : rw_cells ssegs m2 EB [CB len (map b8 out); CB 1 [Z_to_bv 8 0]; CB 1 [jb0]; CB 1 [jb1]; CB (253 - len) jrest])
           by (eapply rw_cells_recell; [exact HD1 | cbn; rewrite length_map; repeat split; try reflexivity; lia | cbn [cells_bytes cbytes]; rewrite <- !app_assoc, !app_nil_r; reflexivity]);
         clear HD1.
    all: destruct (rw_cells_cut _ _ _ 1 HD5) as [HDo HDr]; clear HD5; cbn [firstn skipn cells_size csize Nat.add] in HDo, HDr; rewrite Nat.add_0_r in HDr.
    all: destruct (rw_cells_cut _ _ _ 3 HDr) as [HD3 HDrest]; clear HDr; cbn [firstn skipn cells_size csize Nat.add] in HD3, HDrest.
    all: hide HDo; hide HDrest.
    all: do 5 step.
    (* [comment removed for export] *)
    all: remember (EB + Z.of_nat len)%Z as Q eqn:HQ in *.
    all: do 3 pstep.
    (* [comment removed for export] *)
    all: try change (cbytes (C1 (Z_to_bv 8 0))) with [Z_to_bv 8 0].
    all: step; step; step.
    all: subst Q.
    (* [comment removed for export] *)
    all: unhide HDo; unhide HDrest; unhide FRA.
    (* [comment removed for export] *)
    all: lazymatch type of MU with munch _ ?mo ?mm =>
           assert (AGC : agrees_on (fun a => outside [(EB + Z.of_nat len, EB + Z.of_nat len + 3)]%Z a) mo mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; cbn [outside] in Ho |- *; split; [lia| exact Ho]]);
           assert (G3 : GIo K R s CL FB mm)
             by (eapply (GIo_client_frame_cr K HFL SFL _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp)); [exact G2 | exact MU | exact WM | unfold rc_lo; lia | lia | unfold rc_lo; lia | eapply client_range_sub; [exact CR | lia | lia | lia]]);
           try rename mm into m3
         end.
    all: rename ST2 into ST3; rename MI2 into MI3.
    all: apply (agrees_rw_cells _ _ _ _ _ AGC) in FRA; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AGC) in HDo; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; rewrite ?length_map in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AGC) in HDrest; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m3)
           by (eapply agrees_on_trans; [exact AG02|]; eapply agrees_on_weaken; [exact AGC|]; intros a [_ Hn]; cbn [outside]; lia).
    all: clear MU WM AGC G2 AG02.
    all: name_sp sp (-80)%Z.
    all: eapply evt_cut; [ (eapply (STRERROR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo e);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L0_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | exact HE ]) |].
    all: cbv beta; intros ms' PO; destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m4 & rest & -> & MI4 & ST4 & AG4 & G4 & TLS4);
         rewrite Hsp in *; unname_sp.
    all: replace (ret_pc (Z_to_bv 64 84284)) with (Z_to_bv 64 84284) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: apply (keeps_rw_cells_stack _ _ _ _ _ _ AG4) in FRL; [|lia]; apply (keeps_rw_cells_stack _ _ _ _ _ _ AG4) in FRA; [|lia].
    all: assert (EBK : forall a, (EB <= a < EB + 256)%Z -> client_keeps CL (bv_unsigned sp + -80) a)
           by (intros a Ha; destruct CR as [HBk|HS]; [right; apply HBk; exact Ha| left; lia]).
    all: apply (agrees_rw_cells _ _ _ _ _ AG4) in HDo; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; rewrite ?length_map in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG4) in HD3; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG4) in HDrest; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; lia].
    all: assert (AG04 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m4)
           by (eapply agrees_on_trans; [exact AG03|]; eapply agrees_on_weaken; [exact AG4|]; intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]).
    all: clear AG4 ST3 G3 MI3 AG03.
    all: pose proof (strerror_len e HE) as SEL; set (se := Fmt.strerror e) in *.
    all: assert (LR : length rest = (255 - length se)%nat) by (destruct TLS4 as [[WF _] _]; cbn [cells_wf cell_wf csize] in WF; lia).
    (* [comment removed for export] *)
    all: hide FRA; hide TLS4.
    all: pose proof (munch_refl ([] : list (Z * Z)) m4) as MU; pose proof (wmono_refl ssegs m4) as WM.
    all: do 6 step.
    all: unhide FRA; unhide TLS4.
    all: assert (MSG : fmt_at m4 0x107e7 "%s"%string)
           by (split; [|cbn; lia]; exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m4 0x107e7 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "%s"%string) ++ [Z_to_bv 8 0])
                                     MI4 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))).
    (* [comment removed for export] *)
    all: destruct (rw_cells_cut _ _ _ 2 HD3) as [HC2 HZ]; clear HD3; cbn [firstn skipn cells_size csize Nat.add] in HC2, HZ.
    all: pose proof (rw_cells_uncut _ _ _ _ _ HZ HDrest ltac:(cbn; lia)) as HDST0; clear HZ HDrest.
    all: pose proof (rw_cells_merge ssegs m4 _ [] _ [] ltac:(rewrite app_nil_r; exact HDST0)) as HDST; clear HDST0;
         cbn [app cells_size csize cells_bytes cbytes Nat.add] in HDST.
    all: replace (EB + Z.of_nat len + Z.of_nat 2)%Z with (EB + Z.of_nat len + 2)%Z in HDST by lia.
    all: replace (S (253 - len + 0)) with (Z.to_nat (254 - Z.of_nat len)) in HDST by lia.
    (* [comment removed for export] *)
    all: assert (FWS : Forall2 (farg_word R CL (bv_unsigned sp + -80) (EB + Z.of_nat len + 2) (254 - Z.of_nat len) m4) [AStr se] [tp])
           by (constructor; [| constructor]; cbn [farg_word]; exists (bv_unsigned tp), (map b8 se), rest;
               split; [symmetry; apply Z_to_bv_bv_unsigned|];
               split; [pose proof (rw_cells_bytes_at _ _ _ _ TLS4) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r, <- app_assoc in X; exact X|];
               split; [apply map_b8_no_nul; subst se; apply strerror_ok|];
               split; [symmetry; apply map_unsigned_b8; subst se; apply strerror_ok|];
               rewrite length_map, LR; unfold utp in *; rewrite <- TP in *;
               split; [lia|]; split; [clear - SEL; Z.div_mod_to_equations; lia|]; split; [lia|];
               right; right; lia).
    all: name_sp sp (-80)%Z.
    all: eapply evt_cut; [ (eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (EB + Z.of_nat len + 2)%Z (254 - Z.of_nat len)%Z 0x107e7%Z "%s"%string [AStr se] (Z_to_bv 8 0 :: jrest ++ []));
        [ split; [exact G4|]; split; [rewrite Hsp; exact ST4|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | f_equal; rewrite unsigned_lit by lia; lia | reflexivity | lia | exact MSG | reflexivity | cbn; lia
        | cbn [length firstn]; rewrite Hsp; exact FWS | exact HDST
        | eapply client_range_sub; [exact CR | rewrite Hsp; lia | lia | lia] ]) |].
    all: cbv beta; intros ms' PO; destruct PO as (av5 & m5 & junk5 & E & MU5 & WM5 & MI5 & ST5 & -> & HD2);
         unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hsp in *; unname_sp.
    all: replace (ret_pc (Z_to_bv 64 84308)) with (Z_to_bv 64 84308) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unfold STDIO_STACK in MU5.
    all: assert (AG5 : agrees_on (fun a => outside [(bv_unsigned sp + -80 - 65536, bv_unsigned sp + -80); (EB + Z.of_nat len + 2, EB + Z.of_nat len + 2 + (254 - Z.of_nat len))]%Z a) m4 m5)
           by (eapply agrees_on_of_munch; [exact MU5 | exact WM5 | intros a _ Ho; exact Ho]).
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in FRL; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in FRA; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in HC2; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in HDo; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; rewrite ?length_map in Ha; lia].
    all: assert (G5 : GIo K R s CL FB m5)
           by (eapply (GIo_client_frame_cr K HFL SFL _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp)); [exact G4 | exact MU5 | exact WM5 | unfold rc_lo; lia | lia | unfold rc_lo; lia | eapply client_range_sub; [exact CR | lia | lia | lia]]).
    all: assert (AG05 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m5)
           by (eapply agrees_on_trans; [exact AG04|]; eapply agrees_on_weaken; [exact AG5|]; intros a [[Ha|Ha] Hn]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]).
    all: clear MU WM MU5 WM5 AG5 G4 ST4 AG04 MI4.
    (* [comment removed for export] *)
    all: hide HD2; hide HC2; hide HDo; hide TLS4.
    all: pose proof (munch_refl ([] : list (Z * Z)) m5) as MU; pose proof (wmono_refl ssegs m5) as WM.
    all: do 6 step.
    all: pose proof (rw_cells_uncut _ _ _ _ _ FRL FRA ltac:(cbn; lia)) as FR; cbn [app] in FR; release_frame FR ST5 (bv_unsigned sp).
    all: unhide HD2; unhide HC2; unhide HDo.
    all: apply evt_done; do 16 eexists; exists junk5; split; [reflexivity|].
    all: split; [exact MI5|]; split; [assumption|]; split; [exact AG05|]; split; [exact G5|].
    (* [comment removed for export] *)
    all: set (out2 := Fmt.snprintf (254 - Z.of_nat len) "%s" [AStr se]) in *.
    all: pose proof (snprintf_length_le (254 - Z.of_nat len) "%s" [AStr se] ltac:(lia)) as L2B; fold out2 in L2B.
    all: assert (LJ5 : length junk5 = (253 - len - length out2)%nat) by (destruct HD2 as [[WF _] _]; cbn [cells_wf cell_wf csize] in WF; rewrite length_app, length_map in WF; cbn [length] in WF; lia).
    all: assert (EFM : fmt_errmsg fs args e = out ++ [58; 32]%Z ++ out2)
           by (unfold fmt_errmsg, PCAP_ERRBUF_SIZE; fold out; unfold zlength;
               replace (256 <? Z.of_nat (length out) + 3) with false by (symmetry; apply Z.ltb_ge; subst len; lia);
               unfold strerror_r; fold se; unfold zlength; replace (Z.of_nat (length se) <? 256) with true by (symmetry; apply Z.ltb_lt; lia); cbn [snd];
               replace (256 - Z.of_nat (length out) - 2)%Z with (254 - Z.of_nat len)%Z by (subst len; lia); reflexivity).
    all: rewrite EFM; rewrite !length_app; cbn [length].
    all: pose proof (rw_cells_uncut _ _ _ _ _ HDo HC2 ltac:(cbn; rewrite ?length_map; lia)) as J1.
    all: pose proof (rw_cells_uncut _ _ _ _ _ J1 HD2 ltac:(cbn; rewrite ?length_map; lia)) as J2.
    all: eapply rw_cells_recell; [exact J2 | | ].
    2,4: cbn [cells_bytes cbytes app map]; rewrite !map_app; cbn [map app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
    all: cbn [cells_wf cell_wf csize]; rewrite !length_app, !length_map, !length_app; cbn [length]; repeat split; lia.
  Qed.
  End Sz18.
  Theorem fmt_errmsg_proof : ltac:(let t := eval cbv delta [fmt_errmsg_proof__stmt] in fmt_errmsg_proof__stmt in exact t).
  Proof using HFL SFL SNPRINTF STRERROR VSNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo EB FMTA e fs args junk. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv"). Qed.
End FmtErrmsg.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_strerror.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.Vsn_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_err.TwB.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac pstep := step; fix_lit_store.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Section WithCeil.
Context {CEILV : CEIL}.
Lemma length_list_ascii fs : length (String.list_ascii_of_string fs) = String.length fs.
Proof using Type. pin_using tt. induction fs as [|c fs IH]; cbn; [reflexivity| now rewrite IH]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition item_bytes_in (P : Z -> Prop) (it : fitem) : Prop :=
  match it with FLit l => Forall P l | FConv _ => True | FBad l => Forall P l end.

Lemma take_lit_sub : forall s l r, take_lit s = (l, r) -> s = l ++ r.
Proof using Type. pin_using tt.
  induction s as [|c s IH]; intros l r E; cbn in E.
  - inversion E; subst. reflexivity.
  - destruct (c =? 37).
    + inversion E; subst. reflexivity.
    + destruct (take_lit s) as [l0 r0] eqn:E0. inversion E; subst.
      cbn. f_equal. apply IH. reflexivity.
Qed.

Definition parse_conv_suffix__stmt : Prop := forall s c r, parse_conv s = Some (c, r) -> exists p, s = p ++ r.
Section Sz2.
Variables s c r : ltac2:(SecDiet.SzSec.tyM 'parse_conv_suffix__stmt "vvv" @s).
Lemma parse_conv_suffix__body : ltac2:(SecDiet.SzSec.bodyP 'parse_conv_suffix__stmt "vvv").
Proof using Type. pin_using tt.
  intros E.
 unfold parse_conv in E.
  repeat (cbn in E; lazymatch type of E with
          | context [match ?x with _ => _ end] => is_var x; destruct x; try discriminate E
          | _ => fail end).
  all: inversion E; subst.
  all: lazymatch goal with
       | |- exists p, ?a :: ?b :: ?c :: ?t = p ++ ?t => exists [a; b; c]; reflexivity
       | |- exists p, ?a :: ?b :: ?t = p ++ ?t => exists [a; b]; reflexivity
       | |- exists p, ?a :: ?t = p ++ ?t => exists [a]; reflexivity
       end.
Qed.
End Sz2.
Lemma parse_conv_suffix : ltac:(let t := eval cbv delta [parse_conv_suffix__stmt] in parse_conv_suffix__stmt in exact t).
Proof using Type. intros s c r. ltac2:(SecDiet.SzSec.closeP 'parse_conv_suffix__body "vvv"). Qed.

Lemma parse_fmt_aux_bytes : forall (P : Z -> Prop) fuel s,
  Forall P s -> Forall (item_bytes_in P) (parse_fmt_aux fuel s).
Proof using Type. pin_using tt.
  induction fuel as [|fuel IH]; intros s Hs; cbn [parse_fmt_aux].
  - destruct s; constructor; [exact Hs| constructor].
  - destruct s as [|c s']; [constructor|].
    destruct (Z.eq_dec c 37) as [->|NE].
    + cbn. destruct (parse_conv s') as [[cv r]|] eqn:E.
      * constructor; [exact I|]. apply IH. destruct (parse_conv_suffix _ _ _ E) as [p ->].
        apply Forall_inv_tail in Hs. apply Forall_app in Hs. tauto.
      * constructor; [exact Hs| constructor].
    + replace (match c with 37 => _ | _ => let (l, r) := take_lit (c :: s') in FLit l :: parse_fmt_aux fuel r end)
        with (let (l, r) := take_lit (c :: s') in FLit l :: parse_fmt_aux fuel r).
      2:{ destruct c as [|p|p]; try reflexivity. repeat (destruct p; try reflexivity). exfalso; apply NE; reflexivity. }
      destruct (take_lit (c :: s')) as [l r] eqn:E.
      pose proof (take_lit_sub _ _ _ E) as Hsplit.
      rewrite Hsplit in Hs. apply Forall_app in Hs as [Hl Hr].
      constructor; [exact Hl| apply IH; exact Hr].
Qed.

Lemma str_bytes : forall s, Forall (fun z => 0 <= z < 256) (str s).
Proof using Type. pin_using tt.
  intros s. unfold str. apply Forall_map. apply Forall_forall. intros a _.
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.

Lemma fmt_bytes : forall fs, Forall (item_bytes_in (fun z => 0 <= z < 256)) (fmt fs).
Proof using Type. pin_using tt. intros fs. unfold fmt, parse_fmt. apply parse_fmt_aux_bytes. apply str_bytes. Qed.

(* [comment removed for export] *)
Lemma items_ok_okb : forall its args,
  Forall (item_bytes_in (fun z => 0 <= z < 256)) its -> items_ok its args = true -> items_okb its = true.
Proof using Type. pin_using tt.
  induction its as [|it its IH]; intros args HB HO; [reflexivity|].
  apply Forall_cons_iff in HB as [HBi HB]. cbn [items_ok] in HO. change (items_okb (it :: its)) with (item_okb it && items_okb its)%bool.
  destruct it as [l|c|l]; cbn [item_okb].
  - apply andb_prop in HO as [Hl HO]. rewrite (IH _ HB HO), andb_true_r.
    unfold bytes_okb. apply forallb_forall. intros z Hz.
    pose proof (proj1 (forallb_forall _ _) Hl z Hz) as Hz'. cbn in Hz'.
    pose proof (proj1 (Forall_forall _ _) HBi z Hz) as Hb. cbn in Hb.
    apply andb_prop in Hz' as [H0 _]. destruct (Z.eqb_spec z 0); [discriminate|].
    apply andb_true_intro; split; [apply Z.ltb_lt; lia| apply Z.ltb_lt; lia].
  - destruct args as [|a args']; [discriminate|]. apply andb_prop in HO as [_ HO]. exact (IH _ HB HO).
  - discriminate.
Qed.

Lemma fmt_ok_items_okb : forall fs args, fmt_ok fs args = true -> items_okb (fmt fs) = true.
Proof using Type. pin_using tt.
  intros fs args H. unfold fmt_ok in H. apply andb_prop in H as [H _].
  exact (items_ok_okb _ _ (fmt_bytes fs) H).
Qed.

(* [comment removed for export] *)
Lemma map_b8_no_nul : forall l, bytes_ok l -> ~ In (Z_to_bv 8 0) (map b8 l).
Proof using Type. pin_using tt.
  induction l as [|z l IH]; intros HB Hin; [exact Hin|].
  apply Forall_cons_iff in HB as [Hz HB]. cbn [map] in Hin. destruct Hin as [E|Hin]; [| exact (IH HB Hin)].
  unfold b8 in E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_small in E by (unfold bv_modulus; cbn; lia). lia.
Qed.
Lemma map_unsigned_b8 : forall l, bytes_ok l -> map bv_unsigned (map b8 l) = l.
Proof using Type. pin_using tt.
  induction l as [|z l IH]; intros HB; [reflexivity|]. apply Forall_cons_iff in HB as [Hz HB]. cbn [map]. f_equal; [| exact (IH HB)].
  unfold b8. apply Z_to_bv_small. unfold bv_modulus. cbn. lia.
Qed.
(* [comment removed for export] *)
Lemma farg_words_ok : forall {hptr} R (CL : list (@cblock hptr)) SP D dn m args ws,
  Forall2 (farg_word R CL SP D dn m) args ws -> Forall arg_ok args.
Proof using Type. pin_using tt.
  intros hptr R CL SP D dn m args ws FW. induction FW as [|a w args' ws' Ha _ IH]; constructor; [| exact IH].
  destruct a as [v|cs]; cbn [arg_ok farg_word] in *; [exact Logic.I|].
  destruct Ha as (P & bs & slack & _ & _ & NN & -> & _). apply bytes_ok_of_bytes. exact NN.
Qed.

(* [comment removed for export] *)
Lemma client_range_sub : forall {hptr} R (CL : list (@cblock hptr)) SP SP' A n A' n',
  client_range R CL SP A n -> (SP' <= SP)%Z -> (A <= A')%Z -> (A' + n' <= A + n)%Z -> client_range R CL SP' A' n'.
Proof using Type. pin_using tt.
  intros hptr R CL SP SP' A n A' n' [HB|HS] H1 H2 H3; [left; intros a Ha; apply HB; lia| right; lia].
Qed.

(* [comment removed for export] *)
Lemma farg_word_frame : forall {H hptr} (K : modkit H hptr) R s (CL FB : list (@cblock hptr)) SP SP' D dn m m' W a w,
  GIo K R s CL FB m ->
  farg_word R CL SP D dn m a w -> (SP' <= SP)%Z -> (SP mod 8 = 0)%Z ->
  agrees_on (fun x => outside W x) m m' -> Forall (fun iv => alloc_ceiling <= fst iv /\ snd iv <= SP)%Z W ->
  farg_word R CL SP' D dn m' a w.
Proof using Type. pin_using tt.
  intros H hptr K R s CL FB SP SP' D dn m m' W a w G FWa LE AL8 AG HW.
  destruct a as [v|cs]; cbn [farg_word] in *; [exact FWa|].
  destruct FWa as (P & bs & slack & -> & HB & NN & -> & LEN & SLK & DIS & LOC).
  set (k := ((- (P + Z.of_nat (length bs) + 1)) mod 8)%Z) in *.
  assert (Hk : (0 <= k < 8)%Z) by (subst k; apply Z.mod_pos_bound; lia).
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
  (* [comment removed for export] *)
  assert (HB' : bytes_at usegs m P ((bs ++ [Z_to_bv 8 0]) ++ firstn (Z.to_nat k) slack)).
  { rewrite <- app_assoc. cbn [app].
    rewrite <- (firstn_skipn (Z.to_nat k) slack) in HB.
    change (bs ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) slack ++ skipn (Z.to_nat k) slack) with (bs ++ ([Z_to_bv 8 0] ++ (firstn (Z.to_nat k) slack ++ skipn (Z.to_nat k) slack))) in HB.
    rewrite !app_assoc in HB. apply (proj1 (bytes_at_app _ _ _ _ _)) in HB. destruct HB as [HB _].
    rewrite <- !app_assoc in HB. exact HB. }
  assert (LK : length (firstn (Z.to_nat k) slack) = Z.to_nat k) by (rewrite length_firstn; lia).
  (* [comment removed for export] *)
  assert (RNG : (P + Z.of_nat (length bs) + 1 + k <= alloc_ceiling \/ SP <= P)%Z).
  { destruct LOC as [[HBk|HS]|[HR|HT]].
    - left. destruct (GIo_CLc_facts K R s CL [] FB m P ltac:(rewrite app_nil_r; exact G) ltac:(apply HBk; lia)) as [HC _].
      pose proof (GIo_CLc_facts K R s CL [] FB m (P + Z.of_nat (length bs))%Z ltac:(rewrite app_nil_r; exact G) ltac:(apply HBk; lia)) as [[_ HC2] _].
      (* [comment removed for export] *)
      subst k. clear - HC2 BB. Z.div_mod_to_equations. lia.
    - right. lia.
    - left. subst k. clear - HR BB. Z.div_mod_to_equations. lia.
    - left. pose proof (GIo_tls K _ _ _ _ _ G) as [_ TB]. unfold tls_block_ok_u in TB. subst k. clear - HT TB Hk. lia. }
  exists P, bs, (firstn (Z.to_nat k) slack).
  split; [reflexivity|]. split.
  { eapply agrees_bytes_at; [exact AG | rewrite <- app_assoc in HB'; cbn [app] in HB'; exact HB' |].
    intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. rewrite LK in Hx. cbv beta.
    apply (outside_of_Forall _ _ _ HW). intros iv [H1 H2]. destruct RNG as [R1|R2]; lia. }
  split; [exact NN|]. split; [reflexivity|]. split; [exact LEN|]. split; [rewrite LK; lia|]. split; [rewrite LK; clear -DIS Hk SLK; lia|].
  destruct LOC as [HC|[HR|HT]]; [left; eapply client_range_sub; [exact HC| lia | lia | lia] | right; left; exact HR | right; right].
  rewrite LK. lia.
Qed.

Lemma farg_words_frame : forall {H hptr} (K : modkit H hptr) R s (CL FB : list (@cblock hptr)) SP SP' D dn m m' W args ws,
  GIo K R s CL FB m -> (SP' <= SP)%Z -> (SP mod 8 = 0)%Z ->
  agrees_on (fun x => outside W x) m m' -> Forall (fun iv => alloc_ceiling <= fst iv /\ snd iv <= SP)%Z W ->
  Forall2 (farg_word R CL SP D dn m) args ws -> Forall2 (farg_word R CL SP' D dn m') args ws.
Proof using Type. pin_using tt.
  intros H hptr K R s CL FB SP SP' D dn m m' W args ws G LE AL AG HW FW.
  induction FW; constructor; [eapply farg_word_frame; eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma outside_In_not : forall W x iv, outside W x -> In iv W -> ~ (fst iv <= x < snd iv)%Z.
Proof using Type. pin_using tt.
  induction W as [|[lo hi] W IH]; intros x iv Ho Hin; [destruct Hin|].
  cbn in Ho. destruct Ho as [H1 H2]. destruct Hin as [<-|Hin]; [cbn; lia| exact (IH _ _ H2 Hin)].
Qed.
Lemma GIo_client_frame_cr : forall {H hptr} (K : modkit H hptr) (HFL : heap_frame_law K) (SFL : stdio_fp_law K)
    R s (CL FB : list (@cblock hptr)) m m' lo' hi A n SP,
  GIo K R s CL FB m -> munch [(lo', hi); (A, A + n)]%Z m m' -> wmono usegs m m' ->
  (rc_lo R <= lo')%Z -> (hi <= rc_spmain R)%Z -> (rc_lo R <= SP)%Z -> client_range R CL SP A n ->
  GIo K R s CL FB m'.
Proof using Type. pin_using tt.
  intros H' hptr' K' HFL' SFL' R' s' CL' FB' mA mB lo' hi A n SP G' MU WM H1 H2 H3 CR'.
  destruct CR' as [HB|HS].
  - eapply (GIo_client_frame K' HFL' SFL') with (W := ((lo', hi) :: map (fun b => (Z.max A (cb_addr b), Z.min (A + n) (cb_addr b + cb_size b)))%Z CL')); [exact G' | | exact WM |].
    + eapply munch_weaken; [| exact MU]. intros x Ho. cbn in Ho |- *. destruct Ho as [Hx Ho]. split; [exact Hx|]. split; [| exact Logic.I].
      intros Hin. destruct (proj1 (in_block_In _ _) (HB x Hin)) as (b & Hb & Hxb).
      apply (outside_In_not _ _ _ Ho (in_map _ _ _ Hb)). cbn [fst snd]. lia.
    + constructor; [left; cbn [fst snd]; lia|]. apply Forall_map. apply Forall_forall. intros b Hb. right.
      unfold iv_in_block. apply Exists_exists. exists b. split; [exact Hb|]. cbn [fst snd]. lia.
  - eapply (GIo_client_frame K' HFL' SFL'); [exact G' | exact MU | exact WM |].
    constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia| constructor].
Qed.

(* [comment removed for export] *)
Lemma snez_pos : forall x, (0 < x < 2^64)%Z -> v_sltu z64 (Z_to_bv 64 x) = Z_to_bv 64 1.
Proof using Type. pin_using tt.
  intros x Hx. rewrite v_sltu_b2z. change (bv_unsigned z64) with 0%Z. rewrite (unsigned_lit x) by lia.
  destruct (Z.ltb_spec 0 x); [reflexivity| exfalso; lia].
Qed.
Lemma seqz_pos : forall x, (0 < x < 2^64)%Z -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof using Type. pin_using tt.
  intros x Hx. unfold v_sltiu. rewrite (unsigned_lit x) by lia. change (bv_wrap 64 1) with 1%Z.
  destruct (Z.ltb_spec x 1); [exfalso; lia| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma snprintf_length_le : forall n f args, (1 <= n)%Z -> (Z.of_nat (length (Fmt.snprintf n f args)) <= n - 1)%Z.
Proof using Type. pin_using tt. intros n f args Hn. unfold Fmt.snprintf, snprintf_out. rewrite length_firstn. lia. Qed.

Lemma strerror_len : forall e, (-2^31 <= e < 2^31)%Z -> (length (Fmt.strerror e) <= 40)%nat.
Proof using Type. pin_using tt.
  intros e He. pose proof (strerror_msgb_length e) as ML. rewrite (strerror_tables_agree e He), length_map in ML. exact ML.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End WithCeil.

Open Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Section FmtErrmsg.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis VSNPRINTF : vsnprintf_spec4_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis STRERROR : pcap_strerror_stmt K.

  Definition fmt_errmsg_proof__stmt : Prop := fmt_errmsg_stmt K.
  Section Sz20.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo EB FMTA e fs junk : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv" @ra).
  Lemma fmt_errmsg_proof__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv").
  Proof using HFL SFL SNPRINTF STRERROR VSNPRINTF. pin_using (fun (HFL SFL SNPRINTF STRERROR VSNPRINTF : unit) => tt).
    intros args.
 intros PRE -> -> -> HE -> FMT5 FOK LA FW HEB CR E8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. unfold rc_lo in LO. unfold PCAP_L1_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (rw_cells_bound _ _ _ _ HEB) as BEB. cbn [cells_size csize Nat.add] in BEB.
    pose proof (GIo_tls K _ _ _ _ _ G) as [_ TB]. unfold tls_block_ok_u in TB.
    assert (CLB : forall a, in_block CL a -> (0 < a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact Hc. }
    (* [comment removed for export] *)
    assert (EBR : (EB + 256 <= alloc_ceiling \/ bv_unsigned sp <= EB)%Z).
    { destruct CR as [HBk|HS]; [left| right; lia]. pose proof (CLB _ (HBk (EB + 255)%Z ltac:(lia))). lia. }
    assert (EBT : (EB + 256 <= utp R - 200 \/ utp R - 200 + 4096 <= EB)%Z).
    { destruct CR as [HBk|HS].
      - (* [comment removed for export] *)
        assert (PW : forall a, (EB <= a < EB + 256)%Z -> ~ (utp R - 200 <= a < utp R - 200 + 4096)%Z).
        { intros a Ha Hin. pose proof (HBk a Ha) as Hb. unfold in_block in Hb. apply Exists_exists in Hb as (b & Hinb & Hab).
          pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; left; exact Hinb)) as (_ & _ & _ & _ & _ & B6).
          cbn [cb_addr cb_size] in Hab, B6. lia. }
        destruct (Z.lt_ge_cases (EB + 255) (utp R - 200)) as [X|X]; [left; lia|].
        destruct (Z.le_gt_cases (utp R - 200 + 4096) EB) as [Y|Y]; [right; lia|].
        exfalso. destruct (Z.le_gt_cases EB (utp R - 200)) as [Z1|Z1].
        + apply (PW (utp R - 200)%Z); lia.
        + apply (PW EB); lia.
      - right. lia. }
    pose proof (farg_words_ok _ _ _ _ _ _ _ _ FW) as AOK.
    pose proof (fmt_ok_items_okb _ _ FOK) as IOK.
    set (out := Fmt.snprintf 256 fs args). set (len := length out).
    pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LENB. fold out len in LENB.
    pose proof (snprintf_ok 256 fs args IOK AOK) as OUTOK. fold out in OUTOK.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide HEB.
    unfold PCAP_FMT_ERRMSG_ENTRY. carve_frame 80%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB _ ?t] =>
      lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
    do 18 pstep.
    unhide HEB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGP : agrees_on (fun a => outside [(bv_unsigned sp - 80, bv_unsigned sp)]%Z a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m0 end.
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HEB; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    assert (G0 : GIo K R s CL FB m0).
    { eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    assert (FMT0 : fmt_at m0 FMTA fs).
    { destruct FMT5 as [FB5 FR5]. split; [|exact FR5]. eapply agrees_bytes_at; [exact AGP | exact FB5 |].
      intros a Ha. rewrite length_app, length_map in Ha. cbn [length] in Ha. cbn [outside]. rewrite length_list_ascii in Ha. unfold rc_lo in *. lia. }
    assert (FW0 : Forall2 (farg_word R CL (bv_unsigned sp + -80) EB 256 m0) args (firstn (length args) [a4])).
    { eapply (farg_words_frame K _ _ _ _ (bv_unsigned sp) _ _ _ _ _ [(bv_unsigned sp - 80, bv_unsigned sp)]%Z);
        [exact G | lia | clear - ALN; Z.div_mod_to_equations; lia | exact AGP | | exact FW].
      apply Forall_cons; [cbn [fst snd]; unfold rc_lo in *; lia| apply Forall_nil]. }
    clear MU WM FW FMT5.
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 6 FR) as [FRL FRA]. cbn [firstn skipn cells_size csize Nat.add] in FRL, FRA.
    replace (bv_unsigned sp + -80 + Z.of_nat 48)%Z with (bv_unsigned sp + -32)%Z in FRA by lia.
    (* [comment removed for export] *)
    destruct args as [|x1 [|x2 args2]]; [ | | cbn [length] in LA; exfalso; lia].
    all: cbn [length firstn] in FW0.
    1: destruct (rw_cells_cut _ _ _ 0 FRA) as [AP0 _]; cbn [firstn skipn cells_size csize Nat.add] in AP0.
    2: destruct (rw_cells_cut _ _ _ 1 FRA) as [AP0 _]; cbn [firstn skipn cells_size csize Nat.add] in AP0.
    all: step; name_sp sp (-80)%Z.
    all: lazymatch type of FW0 with Forall2 _ ?xargs ?xws => eapply evt_cut; [ (eapply (VSNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo EB 256%Z FMTA (bv_unsigned sp + -32)%Z fs xargs xws junk);
        [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact FMT0 | exact FOK
        | reflexivity | cbn; lia | rewrite Hsp; exact FW0
        | first [exact AP0 | cbn [map]; exact AP0] | rewrite Hsp; lia | cbn [length]; lia | cbn [length]; lia | exact HEB
        | eapply client_range_sub; [exact CR | rewrite Hsp; lia | lia | lia] ]) |] end.
    all: cbv beta; intros ms' PO; destruct PO as (av & m1 & junk1 & E & MU1 & WM1 & MI1 & ST1 & -> & HD1);
         unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hsp in *; unname_sp.
    all: replace (ret_pc (Z_to_bv 64 84684)) with (Z_to_bv 64 84684) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    1: rename FW0 into FWX; generalize dependent (@nil farg).
    2: rename FW0 into FWX; clear AP0; generalize dependent [x1].
    all: intros args FOK LA AOK out len LENB OUTOK FWX HD1; clear FWX LA.
    all: unfold STDIO_STACK in MU1.
    all: assert (AG1 : agrees_on (fun a => outside [(bv_unsigned sp + -80 - 65536, bv_unsigned sp + -80); (EB, EB + 256)]%Z a) m0 m1)
           by (eapply agrees_on_of_munch; [exact MU1 | exact WM1 | intros a _ Ho; exact Ho]).
    all: apply (agrees_rw_cells _ _ _ _ _ AG1) in FRL; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG1) in FRA; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: assert (G1 : GIo K R s CL FB m1)
           by (eapply (GIo_client_frame_cr K HFL SFL); [exact G0 | exact MU1 | exact WM1 | unfold rc_lo; lia | lia | | exact CR]; unfold rc_lo; lia).
    all: assert (AG01 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m1)
           by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGP| intros a [[Ha|Ha] Hn]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]]|];
               eapply agrees_on_weaken; [exact AG1| intros a [[Ha|Ha] Hn]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]]).
    all: clear AGP MU1 WM1 G0 MI FR ST AG1; try clear AP0.
    all: change (Z.to_nat 256) with 256%nat in HD1; fold out in HD1; fold len in HD1.
    all: assert (LJ1 : length junk1 = (255 - len)%nat) by (destruct HD1 as [[WF _] _]; cbn [cells_wf cell_wf csize] in WF; rewrite length_app, length_map in WF; cbn [length] in WF; lia).
    (* [comment removed for export] *)
    all: hide FRL; hide FRA.
    all: pose proof (munch_refl ([] : list (Z * Z)) m1) as MU; pose proof (wmono_refl usegs m1) as WM.
    all: do 2 step.
    all: eapply evt_cut; [ eapply (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (map b8 out) junk1);
        [ rewrite unsigned_lit by lia; pose proof (rw_cells_bytes_at _ _ _ _ HD1) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r, <- app_assoc in X; exact X
        | apply map_b8_no_nul; exact OUTOK
        | rewrite unsigned_lit, length_map, LJ1 by lia; fold len; clear - E8 LENB BEB; Z.div_mod_to_equations; lia
        | exact MI1 ] |].
    all: cbv beta; intros ms' PO; destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m2 & -> & MU2 & WM2 & MI2 & _).
    all: replace (ret_pc (Z_to_bv 64 84692)) with (Z_to_bv 64 84692) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: rewrite length_map; fold len.
    all: assert (AG2 : agrees_on (fun _ => True) m1 m2) by (eapply agrees_on_of_munch; [exact MU2 | exact WM2 | intros a _ _; cbn; exact Logic.I]).
    all: unhide FRL; unhide FRA.
    all: apply (agrees_rw_cells _ _ _ _ _ AG2) in FRL; [| intros; exact Logic.I].
    all: apply (agrees_rw_cells _ _ _ _ _ AG2) in FRA; [| intros; exact Logic.I].
    all: apply (agrees_rw_cells _ _ _ _ _ AG2) in HD1; [| intros; exact Logic.I].
    all: assert (G2 : GIo K R s CL FB m2) by (eapply (GIo_client_frame K HFL SFL); [exact G1 | exact MU2 | exact WM2 | apply Forall_nil]).
    all: assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -80)) by (eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn; exact Logic.I]).
    all: assert (AG02 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m2)
           by (eapply agrees_on_trans; [exact AG01 | eapply agrees_on_weaken; [exact AG2| intros; exact Logic.I]]).
    all: clear MU WM MU2 WM2 AG2 MI1 ST1 G1 AG01 HEB FMT0.
    all: pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp + -80); (EB + Z.of_nat len, EB + Z.of_nat len + 3)]%Z m2) as MU; pose proof (wmono_refl usegs m2) as WM.
    all: hide FRA; hide HD1.
    all: step; step; if_cases Kr; zify_cond Kr.
    (* [comment removed for export] *)
    1,3: unhide FRA; unhide HD1; do 6 step.
    1,2: pose proof (rw_cells_uncut _ _ _ _ _ FRL FRA ltac:(cbn; lia)) as FR; cbn [app] in FR; release_frame FR ST2 (bv_unsigned sp).
    1,2: apply evt_done; do 17 eexists; split; [reflexivity|].
    1,2: split; [exact MI2|]; split; [assumption|]; split; [exact AG02|]; split; [exact G2|].
    1,2: unfold fmt_errmsg, PCAP_ERRBUF_SIZE; fold out; unfold zlength; fold len;
         replace (256 <? Z.of_nat len + 3) with true by (symmetry; apply Z.ltb_lt; lia);
         replace (255 - length out)%nat with (256 - len - 1)%nat by (subst len; lia); exact HD1.
    (* [comment removed for export] *)
    all: assert (L2 : (2 <= length junk1)%nat) by lia.
    all: destruct junk1 as [|jb0 [|jb1 jrest]]; try (exfalso; cbn [length] in L2; lia); cbn [length] in LJ1.
    all: unhide HD1;
         assert (HD5 : rw_cells usegs m2 EB [CB len (map b8 out); CB 1 [Z_to_bv 8 0]; CB 1 [jb0]; CB 1 [jb1]; CB (253 - len) jrest])
           by (eapply rw_cells_recell; [exact HD1 | cbn; rewrite length_map; repeat split; try reflexivity; lia | cbn [cells_bytes cbytes]; rewrite <- !app_assoc, !app_nil_r; reflexivity]);
         clear HD1.
    all: destruct (rw_cells_cut _ _ _ 1 HD5) as [HDo HDr]; clear HD5; cbn [firstn skipn cells_size csize Nat.add] in HDo, HDr; rewrite Nat.add_0_r in HDr.
    all: destruct (rw_cells_cut _ _ _ 3 HDr) as [HD3 HDrest]; clear HDr; cbn [firstn skipn cells_size csize Nat.add] in HD3, HDrest.
    all: hide HDo; hide HDrest.
    all: assert (EBP : (0 < EB)%Z) by (destruct CR as [HBk|HS]; [exact (proj1 (CLB _ (HBk EB ltac:(lia)))) | unfold rc_lo in *; lia]).
    all: step.                                                          (* [comment removed for export] *)
    (* [comment removed for export] *)
    all: remember (EB + Z.of_nat len)%Z as Q eqn:HQ in *.
    all: step; if_cases Kc; [zify_cond Kc; exfalso; lia|]; clear Kc.   (* [comment removed for export] *)
    all: step; rewrite (snez_pos EB) by lia.                            (* [comment removed for export] *)
    all: step; rewrite (seqz_pos Q) by lia.                             (* [comment removed for export] *)
    all: step.                                                          (* [comment removed for export] *)
    all: try replace (Z.lxor (bv_unsigned (Z_to_bv 64 1)) (bv_unsigned z64)) with 1%Z by reflexivity.
    all: step; if_false.                                                (* [comment removed for export] *)
    all: step; if_false_by (eqz_false EB ltac:(lia)).                   (* [comment removed for export] *)
    all: step; step; if_cases Kc; [zify_cond Kc; exfalso; lia|]; clear Kc.   (* [comment removed for export] *)
    all: step; step; pstep.                                             (* [comment removed for export] *)
    all: try change (cbytes (C1 (Z_to_bv 8 0))) with [Z_to_bv 8 0].   (* [comment removed for export] *)
    all: step; if_cases Kc; [zify_cond Kc; exfalso; lia|]; clear Kc.   (* [comment removed for export] *)
    all: step; step; step; pstep; pstep; step; step; step.              (* [comment removed for export] *)
    all: try change (cbytes (C1 (Z_to_bv 8 0))) with [Z_to_bv 8 0].   (* [comment removed for export] *)
    all: subst Q.
    (* [comment removed for export] *)
    all: unhide HDo; unhide HDrest; unhide FRA.
    (* [comment removed for export] *)
    all: lazymatch type of MU with munch _ ?mo ?mm =>
           assert (AGC : agrees_on (fun a => outside [(EB + Z.of_nat len, EB + Z.of_nat len + 3)]%Z a) mo mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; cbn [outside] in Ho |- *; split; [lia| exact Ho]]);
           assert (G3 : GIo K R s CL FB mm)
             by (eapply (GIo_client_frame_cr K HFL SFL _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp)); [exact G2 | exact MU | exact WM | unfold rc_lo; lia | lia | unfold rc_lo; lia | eapply client_range_sub; [exact CR | lia | lia | lia]]);
           try rename mm into m3
         end.
    all: rename ST2 into ST3; rename MI2 into MI3.
    all: apply (agrees_rw_cells _ _ _ _ _ AGC) in FRA; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AGC) in HDo; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; rewrite ?length_map in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AGC) in HDrest; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m3)
           by (eapply agrees_on_trans; [exact AG02|]; eapply agrees_on_weaken; [exact AGC|]; intros a [_ Hn]; cbn [outside]; lia).
    all: clear MU WM AGC G2 AG02.
    all: name_sp sp (-80)%Z.
    all: eapply evt_cut; [ (eapply (STRERROR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo e);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L0_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | exact HE ]) |].
    all: cbv beta; intros ms' PO; destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m4 & rest & -> & MI4 & ST4 & AG4 & G4 & TLS4);
         rewrite Hsp in *; unname_sp.
    all: replace (ret_pc (Z_to_bv 64 84784)) with (Z_to_bv 64 84784) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: apply (keeps_rw_cells_stack _ _ _ _ _ _ AG4) in FRL; [|lia]; apply (keeps_rw_cells_stack _ _ _ _ _ _ AG4) in FRA; [|lia].
    all: assert (EBK : forall a, (EB <= a < EB + 256)%Z -> client_keeps CL (bv_unsigned sp + -80) a)
           by (intros a Ha; destruct CR as [HBk|HS]; [right; apply HBk; exact Ha| left; lia]).
    all: apply (agrees_rw_cells _ _ _ _ _ AG4) in HDo; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; rewrite ?length_map in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG4) in HD3; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG4) in HDrest; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; lia].
    all: assert (AG04 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m4)
           by (eapply agrees_on_trans; [exact AG03|]; eapply agrees_on_weaken; [exact AG4|]; intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]).
    all: clear AG4 ST3 G3 MI3 AG03.
    all: pose proof (strerror_len e HE) as SEL; set (se := Fmt.strerror e) in *.
    all: assert (LR : length rest = (255 - length se)%nat) by (destruct TLS4 as [[WF _] _]; cbn [cells_wf cell_wf csize] in WF; lia).
    (* [comment removed for export] *)
    all: hide FRA; hide TLS4.
    all: pose proof (munch_refl ([] : list (Z * Z)) m4) as MU; pose proof (wmono_refl usegs m4) as WM.
    all: do 6 step.
    all: unhide FRA; unhide TLS4.
    all: assert (MSG : fmt_at m4 0x107e7 "%s"%string)
           by (split; [|cbn; lia]; exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image usegs m4 0x107e7 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "%s"%string) ++ [Z_to_bv 8 0])
                                     MI4 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))).
    (* [comment removed for export] *)
    all: destruct (rw_cells_cut _ _ _ 2 HD3) as [HC2 HZ]; clear HD3; cbn [firstn skipn cells_size csize Nat.add] in HC2, HZ.
    all: pose proof (rw_cells_uncut _ _ _ _ _ HZ HDrest ltac:(cbn; lia)) as HDST0; clear HZ HDrest.
    all: pose proof (rw_cells_merge usegs m4 _ [] _ [] ltac:(rewrite app_nil_r; exact HDST0)) as HDST; clear HDST0;
         cbn [app cells_size csize cells_bytes cbytes Nat.add] in HDST.
    all: replace (EB + Z.of_nat len + Z.of_nat 2)%Z with (EB + Z.of_nat len + 2)%Z in HDST by lia.
    all: replace (S (253 - len + 0)) with (Z.to_nat (254 - Z.of_nat len)) in HDST by lia.
    (* [comment removed for export] *)
    all: assert (FWS : Forall2 (farg_word R CL (bv_unsigned sp + -80) (EB + Z.of_nat len + 2) (254 - Z.of_nat len) m4) [AStr se] [tp])
           by (constructor; [| constructor]; cbn [farg_word]; exists (bv_unsigned tp), (map b8 se), rest;
               split; [symmetry; apply Z_to_bv_bv_unsigned|];
               split; [pose proof (rw_cells_bytes_at _ _ _ _ TLS4) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r, <- app_assoc in X; exact X|];
               split; [apply map_b8_no_nul; subst se; apply strerror_ok|];
               split; [symmetry; apply map_unsigned_b8; subst se; apply strerror_ok|];
               rewrite length_map, LR; unfold utp in *; rewrite <- TP in *;
               split; [lia|]; split; [clear - SEL; Z.div_mod_to_equations; lia|]; split; [lia|];
               right; right; lia).
    all: name_sp sp (-80)%Z.
    all: eapply evt_cut; [ (eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R s CL FB lo (EB + Z.of_nat len + 2)%Z (254 - Z.of_nat len)%Z 0x107e7%Z "%s"%string [AStr se] (Z_to_bv 8 0 :: jrest ++ []));
        [ split; [exact G4|]; split; [rewrite Hsp; exact ST4|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | f_equal; rewrite unsigned_lit by lia; lia | reflexivity | lia | exact MSG | reflexivity | cbn; lia
        | cbn [length firstn]; rewrite Hsp; exact FWS | exact HDST
        | eapply client_range_sub; [exact CR | rewrite Hsp; lia | lia | lia] ]) |].
    all: cbv beta; intros ms' PO; destruct PO as (av5 & m5 & junk5 & E & MU5 & WM5 & MI5 & ST5 & -> & HD2);
         unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hsp in *; unname_sp.
    all: replace (ret_pc (Z_to_bv 64 84808)) with (Z_to_bv 64 84808) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unfold STDIO_STACK in MU5.
    all: assert (AG5 : agrees_on (fun a => outside [(bv_unsigned sp + -80 - 65536, bv_unsigned sp + -80); (EB + Z.of_nat len + 2, EB + Z.of_nat len + 2 + (254 - Z.of_nat len))]%Z a) m4 m5)
           by (eapply agrees_on_of_munch; [exact MU5 | exact WM5 | intros a _ Ho; exact Ho]).
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in FRL; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in FRA; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in HC2; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in HDo; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; rewrite ?length_map in Ha; lia].
    all: assert (G5 : GIo K R s CL FB m5)
           by (eapply (GIo_client_frame_cr K HFL SFL _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp)); [exact G4 | exact MU5 | exact WM5 | unfold rc_lo; lia | lia | unfold rc_lo; lia | eapply client_range_sub; [exact CR | lia | lia | lia]]).
    all: assert (AG05 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256))%Z m m5)
           by (eapply agrees_on_trans; [exact AG04|]; eapply agrees_on_weaken; [exact AG5|]; intros a [[Ha|Ha] Hn]; cbn [outside]; [lia| pose proof (CLB a Ha); lia]).
    all: clear MU WM MU5 WM5 AG5 G4 ST4 AG04 MI4.
    (* [comment removed for export] *)
    all: hide HD2; hide HC2; hide HDo; hide TLS4.
    all: pose proof (munch_refl ([] : list (Z * Z)) m5) as MU; pose proof (wmono_refl usegs m5) as WM.
    all: do 6 step.
    all: pose proof (rw_cells_uncut _ _ _ _ _ FRL FRA ltac:(cbn; lia)) as FR; cbn [app] in FR; release_frame FR ST5 (bv_unsigned sp).
    all: unhide HD2; unhide HC2; unhide HDo.
    all: apply evt_done; do 16 eexists; exists junk5; split; [reflexivity|].
    all: split; [exact MI5|]; split; [assumption|]; split; [exact AG05|]; split; [exact G5|].
    (* [comment removed for export] *)
    all: set (out2 := Fmt.snprintf (254 - Z.of_nat len) "%s" [AStr se]) in *.
    all: pose proof (snprintf_length_le (254 - Z.of_nat len) "%s" [AStr se] ltac:(lia)) as L2B; fold out2 in L2B.
    all: assert (LJ5 : length junk5 = (253 - len - length out2)%nat) by (destruct HD2 as [[WF _] _]; cbn [cells_wf cell_wf csize] in WF; rewrite length_app, length_map in WF; cbn [length] in WF; lia).
    all: assert (EFM : fmt_errmsg fs args e = out ++ [58; 32]%Z ++ out2)
           by (unfold fmt_errmsg, PCAP_ERRBUF_SIZE; fold out; unfold zlength;
               replace (256 <? Z.of_nat (length out) + 3) with false by (symmetry; apply Z.ltb_ge; subst len; lia);
               unfold strerror_r; fold se; unfold zlength; replace (Z.of_nat (length se) <? 256) with true by (symmetry; apply Z.ltb_lt; lia); cbn [snd];
               replace (256 - Z.of_nat (length out) - 2)%Z with (254 - Z.of_nat len)%Z by (subst len; lia); reflexivity).
    all: rewrite EFM; rewrite !length_app; cbn [length].
    all: pose proof (rw_cells_uncut _ _ _ _ _ HDo HC2 ltac:(cbn; rewrite ?length_map; lia)) as J1.
    all: pose proof (rw_cells_uncut _ _ _ _ _ J1 HD2 ltac:(cbn; rewrite ?length_map; lia)) as J2.
    all: eapply rw_cells_recell; [exact J2 | | ].
    2,4: cbn [cells_bytes cbytes app map]; rewrite !map_app; cbn [map app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
    all: cbn [cells_wf cell_wf csize]; rewrite !length_app, !length_map, !length_app; cbn [length]; repeat split; lia.
  Qed.
  End Sz20.
  Theorem fmt_errmsg_proof : ltac:(let t := eval cbv delta [fmt_errmsg_proof__stmt] in fmt_errmsg_proof__stmt in exact t).
  Proof using HFL SFL SNPRINTF STRERROR VSNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo EB FMTA e fs args junk. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv"). Qed.
End FmtErrmsg.

End WithCeil.
End TwB.
End F_fmt_errmsg.

(* [comment removed for export] *)
Module F_sfpcapng_chk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_chkD__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcap_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_chkF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_ai OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_sfpcapng_chkD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_sfpcapng_chkE.
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
Lemma ltu_lits : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y)%Z.
Proof using Type. pin_using tt. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.
Lemma sxv_range : forall a b c d, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z -> (0 <= sxv a b c d < 2^64)%Z.
Proof using Type. pin_using tt. intros. unfold sxv, le4val. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Lemma eqb_sxv_lit : forall a b c d v, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z -> (0 <= v < 2^31)%Z ->
  bv_eqb (Z_to_bv 64 (sxv a b c d)) (Z_to_bv 64 v) = (le4val a b c d =? v)%Z.
Proof using Type. pin_using tt.
  intros a b c d v Ha Hb Hc Hd Hv. unfold bv_eqb. pose proof (sxv_range a b c d Ha Hb Hc Hd) as R.
  rewrite (unsigned_lit (sxv a b c d)), (unsigned_lit v) by lia. unfold sxv in *.
  destruct (Z.eqb_spec (le4val a b c d) v) as [E|NE]; [apply Z.eqb_eq | apply Z.eqb_neq]; unfold le4val in *; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Lemma shb_len_ltu : forall (w : word) TL hi, (bv_unsigned w = TL + 4294967296 * hi)%Z -> (0 <= TL < 2^32)%Z -> (0 <= hi < 2^32)%Z ->
  bv_ltu (Z_to_bv 64 (-1048550)) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned w + 18446744073708503039))) = ((28 <=? TL) && (TL <=? 1048576))%Z.
Proof using Type. pin_using tt.
  intros w TL hi E HT Hh. unfold bv_ltu. rewrite E. rewrite !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul Z.div Z.ltb Z.leb andb Z.pow].
  change (2^64)%Z with 18446744073709551616%Z. change (2 ^ (32 - 1))%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z.
  destruct (Z.leb_spec 28 TL); destruct (Z.leb_spec TL 1048576); cbn [andb];
    first [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Definition swapw (w : word) : word :=
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 24)))
                                                    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned w) 65280))) 8))))))
                    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned w) 8))) 65280)))
                                                    (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned w)) 24)))))))).
Lemma swapw_eq : forall w,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 24)))
                                                    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned w) 65280))) 8))))))
                    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned w) 8))) 65280)))
                                                    (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned w)) 24))))))))
  = swapw w.
Proof using Type. pin_using tt. reflexivity. Qed.
Lemma swapw_sxv : forall a b c d, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z ->
  bv_unsigned (swapw (Z_to_bv 64 (sxv a b c d))) = (le4val d c b a + 4294967296 * (b + 256 * c + 65536 * d + 16777216 * ((d / 128 * 4294967295) mod 256)))%Z.
Proof using Type. pin_using tt.
  intros a b c d Ha Hb Hc Hd. unfold swapw. pose proof (sxv_range a b c d Ha Hb Hc Hd) as R.
  rewrite (swap32_val _ a b c d (d / 128 * 4294967295)); [unfold le4val; lia | lia | lia | lia | lia | Z.div_mod_to_equations; lia |].
  rewrite unsigned_lit by lia. unfold sxv, le4val. lia.
Qed.
Lemma swapw_hi_range : forall b c d x, (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z ->
  (0 <= b + 256 * c + 65536 * d + 16777216 * (x mod 256) < 2^32)%Z.
Proof using Type. pin_using tt. intros. pose proof (Z.mod_pos_bound x 256 ltac:(lia)). lia. Qed.

Section ChkNgMain.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREE : free_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis OPEN_COMMON : open_offline_common_stmt HO K sites.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis RBYTES : read_bytes_stmt HO K sites.
  Hypothesis RB : read_block_stmt HO K sites.
  Hypothesis AI : add_interface_stmt HO K sites.

  Open Scope bv_scope.
  (* [comment removed for export] *)
  Lemma ngc_hc40 : forall (sp : word) mx ca cb ct,
    rw_cells ssegs mx (bv_unsigned sp + -128) [CB 32 ca] -> rw_cells ssegs mx (bv_unsigned sp + -96) cb -> cells_size cb = 4%nat ->
    rw_cells ssegs mx (bv_unsigned sp + -92) ct -> cells_size ct = 4%nat ->
    exists hc, rw_cells ssegs mx (bv_unsigned sp + -128) hc /\ cells_size hc = 40%nat.
  Proof using Type. pin_using tt.
    intros sp mx ca cb ct HA HB Hcb HT Hct. exists ([CB 32 ca] ++ cb ++ ct).
    pose proof (rw_cells_uncut _ _ _ _ _ HB HT ltac:(rewrite Hcb; lia)) as HBT.
    pose proof (rw_cells_uncut _ _ _ _ _ HA HBT ltac:(cbn; lia)) as HABT.
    split; [exact HABT|]. rewrite !cells_size_app, Hcb, Hct. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition ngc_notme__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' : word) (pcx : Z) (m3 : mem) (ps3 : PS)
           (e : list byte) (hc : list cell),
      ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (pcx = 0x1677c)%Z \/ ((pcx = 0x16780)%Z /\ a0' = Z_to_bv 64 0) ->
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3 ->
      GIo K R ps3 CL FB m3 -> ps_outfile ps3 = ps_outfile s ->
      rw_cells ssegs m3 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat ->
      rw_cells ssegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m3 ERR [C4 (Z_to_bv 64 0)] -> rw_cells ssegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m3 EB [CB 256 e] ->
      evt ssegs (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s) CH_NotMe ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 pcx) fc None m3 (seg_rom ssegs)).
  Section Sz9.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' pcx m3 ps3 e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_notme__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_notme__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_notme__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros CTX HPC MI3 ST3 AG3 G3 OF3 HC3 Hhc FRS3 ERR3 MG3 HEB3.
    destruct CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (rw_cells_forget _ _ _ _ HC3) as [fj HC']. clear HC3. rewrite Hhc in HC'.
    hide HEB3. hide MG3. hide ERR3.
    destruct HPC as [-> |[-> ->]]; [do 14 step | do 13 step].
    all: release_frame HC' ST3 (bv_unsigned sp + -88)%Z; release_frame FRS3 ST3 (bv_unsigned sp).
    all: unhide HEB3; unhide MG3; unhide ERR3.
    all: destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL; cbn [map] in MG3.
    all: apply evt_done; unfold check_header_post.
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, (Z_to_bv 64 0) end.
    all: split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    all: split; [exact OF3|]; split; [assumption|]; split; [assumption|].
    all: split; [exact AG3|].
    all: split; [eapply rw_cells_recell; [exact MG3 | cbn; repeat split; exact Logic.I | reflexivity]|].
    all: split; [exact ERR3|].
    all: split; [reflexivity|]; split; [reflexivity|]; split; [exact G3| exists e; exact HEB3].
  Qed.
  End Sz9.
  Lemma ngc_notme : ltac:(let t := eval cbv delta [ngc_notme__stmt] in ngc_notme__stmt in exact t).
  Proof using Type. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' pcx m3 ps3 e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_notme__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_short__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s7' s9' t3' t4' t5' t6' : word) (pcx : Z) (m2 : mem) (ps2 : PS)
           (e : list byte) (hc : list cell),
      ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (pcx = 0x166b0 \/ pcx = 0x166e8)%Z ->
      mem_inv ssegs m2 -> stk ssegs m2 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m2 ->
      GIo K R ps2 CL FB m2 -> ps_outfile ps2 = ps_outfile s ->
      rw_cells ssegs m2 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat ->
      rw_cells ssegs m2 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m2 ERR [C4 (Z_to_bv 64 0)] -> rw_cells ssegs m2 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m2 EB [CB 256 e] ->
      implM ssegs (mbind (e_ferror (prims HO fo_nop sites) f) (fun er : bool =>
                     if er then mbind (errmsg_for_errno MOps (prims HO fo_nop sites) "error reading dump file"%string []) (fun mm => mret (CH_Err mm))
                     else mret CH_NotMe)) ps2
        (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 3) (Z_to_bv 64 FA) s4' s5' s6' s7' (Z_to_bv 64 0) s9' s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 pcx) fc None m2 (seg_rom ssegs)).
  Section Sz10.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s7' s9' t3' t4' t5' t6' pcx m2 ps2 e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_short__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FERROR FMT HFL SFL. pin_using (fun (FERROR FMT HFL SFL : unit) => tt).
    intros CTX HPC MI2 ST2 AG2 G2 OF2 HC2 Hhc FRS2 ERR2 MG2 HEB2.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_ferror e_last_errno prims].
    hide HC2. hide FRS2. hide ERR2. hide MG2. hide HEB2.
    unfold implM. iprefix.
    destruct HPC as [-> | ->]; do 2 step.
    all: name_sp sp (-128)%Z.
    all: apply evt_done; eapply (implM_bind ssegs);
      [ eapply FERROR; [| exact HinF | reflexivity];
        split; [exact G2|]; split; [rewrite Hsp; exact ST2|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
        split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]] |].
    all: intros er ps3 ms3 PO; cbv beta in PO; destruct PO as (av3 & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO);
         unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hsp in *; unname_sp.
    1: replace (ret_pc (Z_to_bv 64 0x166b8)) with (Z_to_bv 64 0x166b8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    2: replace (ret_pc (Z_to_bv 64 0x166f0)) with (Z_to_bv 64 0x166f0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unhide HC2; unhide FRS2; unhide ERR2; unhide MG2; unhide HEB2.
    all: (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in HC2; [|lia]); (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FRS2; [|lia]);
         (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in ERR2; [|lia]); (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in MG2; [|lia]);
         (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in HEB2; [|lia]).
    all: assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3)
           by (eapply agrees_on_trans; [exact AG2|]; eapply agrees_on_weaken; [exact AG3|]; intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]).
    all: clear AG3 MI2 ST2.
    all: destruct er; cbv iota.
    2,4: (* [comment removed for export] *)
         clear ERRNO; apply (implM_ret ssegs); hide HC2; hide FRS2; hide ERR2; hide MG2; hide HEB2; cbn [Z.b2z]; step; if_true;
         unhide HC2; unhide FRS2; unhide ERR2; unhide MG2; unhide HEB2;
         eapply ngc_notme; [exact CTX | right; split; reflexivity | exact MI3 | exact ST3 | exact AG03 | exact G3 | exact OF2 | exact HC2 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB2].
    all: destruct (ERRNO eq_refl) as [EN2 ER]; clear ERRNO; unfold utp in EN2; rewrite <- TP in EN2.
    all: eapply implM_pure; [reflexivity|]; cbn [fst snd].
    all: set (err := lc_errno (ps_libc ps2)) in *.
    all: hide HC2; hide FRS2; hide ERR2; hide MG2; hide HEB2.
    all: cbn [Z.b2z]; step; if_false.
    1: do 11 step. 2: do 10 step.
    all: replace (sx32 (Z_to_bv 64 err)) with (Z_to_bv 64 (s32 err)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
    all: assert (MSG : fmt_at m3 0x108d6 "error reading dump file"%string)
           by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| lia| cbn; lia]).
    all: unhide HEB2; name_sp sp (-128)%Z.
    all: eapply evt_cut;
      [ eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps2 CL FB lo EB 0x108d6%Z err "error reading dump file"%string [] e);
          [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB2
           | right; rewrite Hsp; lia | exact E8 ];
        split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|];
        split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]] |].
    all: cbv beta; intros ms' PO; destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & junk4 & -> & MI4 & ST4 & AG4 & G4 & HEB4);
         rewrite Hsp in *; unname_sp.
    all: replace (ret_pc (Z_to_bv 64 0x16710)) with (Z_to_bv 64 0x16710) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unhide HC2; unhide FRS2; unhide ERR2; unhide MG2.
    all: transport HC2 m4 AG4 ltac:(intros a Ha; rewrite Hhc in Ha; split; [left; lia| lia]).
    all: transport FRS2 m4 AG4 ltac:(prs); transport ERR2 m4 AG4 ltac:(prs); transport MG2 m4 AG4 ltac:(prsMG GL).
    all: assert (AG04 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m4)
           by (eapply agrees_on_trans; [exact AG03|]; eapply agrees_on_weaken; [exact AG4|]; intros a [[Ha|Ha] [Hn _]]; (split; [|exact Hn]); [left; lia| right; exact Ha]).
    all: change (Z.to_nat 256) with 256%nat in HEB4.
    all: eapply (ngc_err_exit K sites HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m);
      [ exact CTX | right; left; reflexivity | exact MI4 | exact ST4 | exact AG04 | exact G4 | exact HC2 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB4
      | pose proof (fmt_errmsg_length "error reading dump file"%string [] err); lia
      | apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor] | exact OF2 ].
  Qed.
  End Sz10.
  Lemma ngc_short : ltac:(let t := eval cbv delta [ngc_short__stmt] in ngc_short__stmt in exact t).
  Proof using FERROR FMT HFL SFL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s7' s9' t3' t4' t5' t6' pcx m2 ps2 e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_short__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_lenfail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' w9 t3' t4' t5' t6' : word) (TL hi9 : Z) (m2 : mem) (ps2 : PS)
           (e : list byte) (hc : list cell),
      ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (bv_unsigned w9 = TL + 4294967296 * hi9)%Z -> (0 <= TL < 2^32)%Z -> (0 <= hi9 < 2^32)%Z ->
      mem_inv ssegs m2 -> stk ssegs m2 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m2 ->
      GIo K R ps2 CL FB m2 -> ps_outfile ps2 = ps_outfile s ->
      rw_cells ssegs m2 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat ->
      rw_cells ssegs m2 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m2 ERR [C4 (Z_to_bv 64 0)] -> rw_cells ssegs m2 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m2 EB [CB 256 e] ->
      evt ssegs (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)
                   (CH_Err (Msg.shb_invalid_length TL)) ps2)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4' s5' s6' s7' s8' w9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16758) fc None m2 (seg_rom ssegs)).
  Section Sz11.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' w9 t3' t4' t5' t6' TL hi9 m2 ps2 e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_lenfail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_lenfail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_lenfail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL SFL SNPRINTF. pin_using (fun (HFL SFL SNPRINTF : unit) => tt).
    intros CTX W9 TLR HI9 MI2 ST2 AG2 G2 OF2 HC2 Hhc FRS2 ERR2 MG2 HEB2.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    hide HC2. hide FRS2. hide ERR2. hide MG2. hide HEB2.
    do 8 step.
    rewrite (swrap32_low _ TL hi9 W9).
    set (fs := "Section Header Block in pcapng dump file has invalid length %zu < _%u_ < %u (BT_SHB_INSANE_MAX)"%string).
    assert (MSG : fmt_at m2 0x107ea fs) by (apply (fmt_at_intro m2 _ _ MI2); [vm_compute; reflexivity| lia| cbn; lia]).
    unhide HEB2. name_sp sp (-128)%Z.
    eapply evt_cut.
    { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps2 CL FB lo EB 256%Z 0x107ea%Z fs [AInt 28; AInt (s32 TL); AInt 1048576] e);
        [ split; [exact G2|]; split; [rewrite Hsp; exact ST2|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI2|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | reflexivity | reflexivity | lia | exact MSG | subst fs; vm_compute; reflexivity | cbn; lia | | exact HEB2 | right; rewrite Hsp; lia ].
      cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
    cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x16778)) with (Z_to_bv 64 0x16778) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -128 - STDIO_STACK, bv_unsigned sp + -128); (EB, EB + 256)]%Z a) m2 m4)
      by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    unfold STDIO_STACK in AGS, MU4.
    assert (G4 : GIo K R ps2 CL FB m4).
    { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU4 | exact WM4 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    unhide HC2. unhide FRS2. unhide ERR2. unhide MG2.
    transport HC2 m4 AGS ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia).
    transport FRS2 m4 AGS ltac:(prs). transport ERR2 m4 AGS ltac:(prs). transport MG2 m4 AGS ltac:(prsMG GL).
    assert (AG4 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m4).
    { eapply agrees_on_trans; [exact AG2|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn _]]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
    assert (EMSG : Fmt.snprintf 256 fs [AInt 28; AInt (s32 TL); AInt 1048576] = Msg.shb_invalid_length TL).
    { unfold Msg.shb_invalid_length, PCAP_ERRBUF_SIZE. subst fs. apply snprintf_pargs.
      replace (convs (fmt "Section Header Block in pcapng dump file has invalid length %zu < _%u_ < %u (BT_SHB_INSANE_MAX)")) with [Czu; Cu; Cu] by (vm_compute; reflexivity).
      apply pargs_cons; [apply aeq_same|]. apply pargs_cons; [apply aeq_s32; reflexivity|]. apply pargs_cons; [apply aeq_same| apply pargs_nil]. }
    pose proof (snprintf_length 256 fs [AInt 28; AInt (s32 TL); AInt 1048576]) as LS. change (Z.to_nat (256 - 1)) with 255%nat in LS.
    rewrite EMSG in LS, HEB4. change (Z.to_nat 256) with 256%nat in HEB4.
    replace (256 - length (Msg.shb_invalid_length TL) - 1)%nat with (255 - length (Msg.shb_invalid_length TL))%nat in HEB4 by lia.
    hide HC2. hide FRS2. hide ERR2. hide MG2. hide HEB4. step. unhide HC2. unhide FRS2. unhide ERR2. unhide MG2. unhide HEB4.
    eapply (ngc_err_exit K sites HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m);
      [ exact CTX | right; left; reflexivity | exact MI4 | exact ST4 | exact AG4 | exact G4 | exact HC2 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB4
      | lia | rewrite <- EMSG; subst fs; apply snprintf_ok; [vm_compute; reflexivity| repeat constructor] | exact OF2 ].
  Qed.
  End Sz11.
  Lemma ngc_lenfail : ltac:(let t := eval cbv delta [ngc_lenfail__stmt] in ngc_lenfail__stmt in exact t).
  Proof using HFL SFL SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' w9 t3' t4' t5' t6' TL hi9 m2 ps2 e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_lenfail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_bomk (fuel : nat) (f : hptr) (tlb bomb : list Z) :=
    let '(ok, swapped, total_length) :=
       (if get_le32 bomb 0 =? BYTE_ORDER_MAGIC then (true, false, get_le32 tlb 0)
        else if bswap32 (get_le32 bomb 0) =? BYTE_ORDER_MAGIC then (true, true, bswap32 (get_le32 tlb 0))
        else (false, false, get_le32 tlb 0)) in
    if negb ok then mret CH_NotMe else
    if ((total_length <? 28) || (BT_SHB_INSANE_MAX <? total_length))%Z then mret (CH_Err (Msg.shb_invalid_length total_length))
    else ngc_open MOps (prims HO fo_nop sites) fuel f 0 BT_SHB swapped total_length.

  (* [comment removed for export] *)
  Definition ngc_bom__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem) (fuel : nat)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) (ps2 : PS)
           (e ca jb jt : list byte) (t0 t1 t2 t3 b0 b1 b2 b3 : Z),
      ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (0 <= t0 < 256)%Z -> (0 <= t1 < 256)%Z -> (0 <= t2 < 256)%Z -> (0 <= t3 < 256)%Z ->
      (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z -> (0 <= b2 < 256)%Z -> (0 <= b3 < 256)%Z ->
      mem_inv ssegs m2 -> stk ssegs m2 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m2 ->
      GIo K R ps2 CL FB m2 -> ps_outfile ps2 = ps_outfile s ->
      rw_cells ssegs m2 (bv_unsigned sp + -128) [CB 32 ca] ->
      rw_cells ssegs m2 (bv_unsigned sp + -96) [CB 4 (map b8 [b0; b1; b2; b3]); CB 0 jb] ->
      rw_cells ssegs m2 (bv_unsigned sp + -92) [CB 4 (map b8 [t0; t1; t2; t3]); CB 0 jt] ->
      rw_cells ssegs m2 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m2 ERR [C4 (Z_to_bv 64 0)] -> rw_cells ssegs m2 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m2 EB [CB 256 e] ->
      implM ssegs (ngc_bomk fuel f [t0; t1; t2; t3] [b0; b1; b2; b3]) ps2
        (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 3) (Z_to_bv 64 FA) s4 s5 s6 s7 (Z_to_bv 64 0) s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16720) fc None m2 (seg_rom ssegs)).
  Section Sz12.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 e ca jb jt t0 t1 t2 t3 b0 b1 b2 b3 : ltac2:(SecDiet.SzSec.tyM 'ngc_bom__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_bom__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_bom__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AI FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. pin_using (fun (AI FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF : unit) => tt).
    intros CTX T0 T1 T2 T3 B0 B1 B2 B3 MI2 ST2 AG2 G2 OF2 HCA HB HT FRS2 ERR2 MG2 HEB2.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    (* [comment removed for export] *)
    assert (LJ : length jb = 0%nat /\ length jt = 0%nat) by (destruct HB as [[WF _] _]; destruct HT as [[WF' _] _]; cbn in WF, WF'; lia).
    destruct jb; [|exfalso; cbn in LJ; lia]. destruct jt; [|exfalso; cbn in LJ; lia]. clear LJ.
    assert (HB4 : rw_cells ssegs m2 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (le4val b0 b1 b2 b3))]).
    { eapply rw_cells_recell; [exact HB | cbn; repeat split; reflexivity |]. cbn [cells_bytes cbytes map app]. rewrite (le4_lit b0 b1 b2 b3) by lia. rewrite app_nil_r. reflexivity. }
    assert (HT4 : rw_cells ssegs m2 (bv_unsigned sp + -92) [C4 (Z_to_bv 64 (le4val t0 t1 t2 t3))]).
    { eapply rw_cells_recell; [exact HT | cbn; repeat split; reflexivity |]. cbn [cells_bytes cbytes map app]. rewrite (le4_lit t0 t1 t2 t3) by lia. rewrite app_nil_r. reflexivity. }
    clear HB HT.
    unfold ngc_bomk, get_le32, zslice, zfirstn, zskipn. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. cbn [firstn skipn].
    rewrite (bswap32_bytes b0 b1 b2 b3), (bswap32_bytes t0 t1 t2 t3) by lia. rewrite !le_of_bytes_4.
    change (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)%Z with (le4val b0 b1 b2 b3).
    change (t0 + 256 * t1 + 65536 * t2 + 16777216 * t3)%Z with (le4val t0 t1 t2 t3).
    change (b3 + 256 * b2 + 65536 * b1 + 16777216 * b0)%Z with (le4val b3 b2 b1 b0).
    change (t3 + 256 * t2 + 65536 * t1 + 16777216 * t0)%Z with (le4val t3 t2 t1 t0).
    hide HCA. hide FRS2. hide ERR2. hide MG2. hide HEB2.
    ienter. step. rewrite (sx32_lit b0 b1 b2 b3) by lia. do 3 step.
    rewrite (eqb_sxv_lit b0 b1 b2 b3 1295788826) by lia.
    destruct (Z.eqb_spec (le4val b0 b1 b2 b3) 1295788826) as [EQS|NES].
    - (* [comment removed for export] *)
      replace (le4val b0 b1 b2 b3 =? BYTE_ORDER_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; rewrite EQS; discriminate).
      replace (le4val b3 b2 b1 b0 =? BYTE_ORDER_MAGIC)%Z with true by (symmetry; apply Z.eqb_eq; unfold le4val, BYTE_ORDER_MAGIC in *; lia).
      cbv beta iota.
      do 7 step. step. rewrite (sx32_lit t0 t1 t2 t3) by lia. do 13 step. rewrite !swapw_eq. do 6 step.
      pose proof (swapw_sxv t0 t1 t2 t3 T0 T1 T2 T3) as W9. pose proof (swapw_hi_range t1 t2 t3 (t3 / 128 * 4294967295) T1 T2 T3) as HI9.
      pose proof (swapw_sxv b0 b1 b2 b3 B0 B1 B2 B3) as W7. pose proof (swapw_hi_range b1 b2 b3 (b3 / 128 * 4294967295) B1 B2 B3) as HI7.
      rewrite (shb_len_ltu _ (le4val t3 t2 t1 t0) _ W9) by (unfold le4val; lia).
      destruct ((28 <=? le4val t3 t2 t1 t0) && (le4val t3 t2 t1 t0 <=? 1048576))%Z eqn:LC.
      + (* [comment removed for export] *)
        replace ((le4val t3 t2 t1 t0 <? 28) || (BT_SHB_INSANE_MAX <? le4val t3 t2 t1 t0))%Z with false by (unfold BT_SHB_INSANE_MAX; lia).
        cbn [negb].
        unhide HCA. unhide FRS2. unhide ERR2. unhide MG2. unhide HEB2.
        destruct (ngc_hc40 sp m2 ca _ _ HCA HB4 eq_refl HT4 eq_refl) as (hc & HC40 & Hhc).
        apply evt_done. eapply ngc_fill.
        all: try exact CTX. all: try assumption.
        1: exact W9. 1: exact HI9. 1: lia.
        1: replace BYTE_ORDER_MAGIC with (le4val b3 b2 b1 b0) by (unfold le4val, BYTE_ORDER_MAGIC in *; lia); exact W7.
        1: exact HI7. 1: exact HC40. 1: exact Hhc. 1: exact ERR2. 1: exact HEB2.
      + (* [comment removed for export] *)
        replace ((le4val t3 t2 t1 t0 <? 28) || (BT_SHB_INSANE_MAX <? le4val t3 t2 t1 t0))%Z with true by (unfold BT_SHB_INSANE_MAX; lia).
        cbn [negb].
        unhide HCA. unhide FRS2. unhide ERR2. unhide MG2. unhide HEB2.
        destruct (ngc_hc40 sp m2 ca _ _ HCA HB4 eq_refl HT4 eq_refl) as (hc & HC40 & Hhc).
        apply evt_done. apply (implM_ret ssegs).
        eapply ngc_lenfail; [exact CTX | exact W9 | unfold le4val; lia | exact HI9 | exact MI2 | exact ST2 | exact AG2 | exact G2 | exact OF2 | exact HC40 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB2].
    - (* [comment removed for export] *)
      do 3 step. rewrite (eqb_sxv_lit b0 b1 b2 b3 439041101) by lia.
      destruct (Z.eqb_spec (le4val b0 b1 b2 b3) 439041101) as [EQN|NEN].
      + (* [comment removed for export] *)
        replace (le4val b0 b1 b2 b3 =? BYTE_ORDER_MAGIC)%Z with true by (symmetry; apply Z.eqb_eq; exact EQN).
        cbn [negb]. cbv beta iota.
        step. rewrite (sx32_lit t0 t1 t2 t3) by lia. do 6 step.
        assert (W9 : bv_unsigned (Z_to_bv 64 (sxv t0 t1 t2 t3)) = (le4val t0 t1 t2 t3 + 4294967296 * (t3 / 128 * 4294967295))%Z)
          by (rewrite <- (sx32_lit t0 t1 t2 t3) by lia; apply unsigned_sx32; lia).
        assert (HI9 : (0 <= t3 / 128 * 4294967295 < 2^32)%Z) by (clear - T3; Z.div_mod_to_equations; lia).
        rewrite (shb_len_ltu _ (le4val t0 t1 t2 t3) _ W9) by (unfold le4val; lia).
        unhide HCA. unhide FRS2. unhide ERR2. unhide MG2. unhide HEB2.
        destruct (ngc_hc40 sp m2 ca _ _ HCA HB4 eq_refl HT4 eq_refl) as (hc & HC40 & Hhc).
        destruct ((28 <=? le4val t0 t1 t2 t3) && (le4val t0 t1 t2 t3 <=? 1048576))%Z eqn:LC.
        * (* [comment removed for export] *)
          replace ((le4val t0 t1 t2 t3 <? 28) || (BT_SHB_INSANE_MAX <? le4val t0 t1 t2 t3))%Z with false by (unfold BT_SHB_INSANE_MAX; lia).
          cbv iota. apply evt_done. eapply ngc_fill.
          all: try exact CTX. all: try assumption.
          1: exact W9. 1: exact HI9. 1: lia. 1: rewrite unsigned_lit by lia; unfold BYTE_ORDER_MAGIC; instantiate (1 := 0%Z); reflexivity.
          1: lia. 1: exact HC40. 1: exact Hhc. 1: exact ERR2. 1: exact HEB2.
        * (* [comment removed for export] *)
          replace ((le4val t0 t1 t2 t3 <? 28) || (BT_SHB_INSANE_MAX <? le4val t0 t1 t2 t3))%Z with true by (unfold BT_SHB_INSANE_MAX; lia).
          cbv iota. apply evt_done. apply (implM_ret ssegs).
          eapply ngc_lenfail; [exact CTX | exact W9 | unfold le4val; lia | exact HI9 | exact MI2 | exact ST2 | exact AG2 | exact G2 | exact OF2 | exact HC40 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB2].
      + (* [comment removed for export] *)
        replace (le4val b0 b1 b2 b3 =? BYTE_ORDER_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; exact NEN).
        replace (le4val b3 b2 b1 b0 =? BYTE_ORDER_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; intros X; apply NES; unfold le4val, BYTE_ORDER_MAGIC in *; lia).
        cbn [negb]. cbv beta iota.
        unhide HCA. unhide FRS2. unhide ERR2. unhide MG2. unhide HEB2.
        destruct (ngc_hc40 sp m2 ca _ _ HCA HB4 eq_refl HT4 eq_refl) as (hc & HC40 & Hhc).
        apply evt_done. apply (implM_ret ssegs).
        eapply ngc_notme; [exact CTX | left; reflexivity | exact MI2 | exact ST2 | exact AG2 | exact G2 | exact OF2 | exact HC40 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB2].
  Qed.
  End Sz12.
  Lemma ngc_bom : ltac:(let t := eval cbv delta [ngc_bom__stmt] in ngc_bom__stmt in exact t).
  Proof using AI FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 e ca jb jt t0 t1 t2 t3 b0 b1 b2 b3. ltac2:(SecDiet.SzSec.closeP 'ngc_bom__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition pcap_ng_check_header_proof__stmt : Prop := pcap_ng_check_header_stmt HO K sites.
  Section Sz13.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo MG FA EB ERR f magic ej ec fuel : ltac2:(SecDiet.SzSec.tyM 'pcap_ng_check_header_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_ng_check_header_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_ng_check_header_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AI FERROR FMT FREAD FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. pin_using (fun (AI FERROR FMT FREAD FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF : unit) => tt).
    intros PRE HinF SITES -> -> -> -> -> HMG GR GL HEB HERR Hec R1 R2 R3 E1 E2 D1 E4 E8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. unfold rc_lo in LO. unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    assert (CTX : ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m).
    { split; [exact G|]. repeat (split; [fastfirst (first [eassumption | lia])|]). exact E8. }
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL.
    pose proof GR as GR'. apply Forall_cons_iff in GR' as [K0 GR']. apply Forall_cons_iff in GR' as [K1 GR']. apply Forall_cons_iff in GR' as [K2 GR']. apply Forall_cons_iff in GR' as [K3 _].
    cbv beta in K0, K1, K2, K3.
    cbn [map] in HMG.
    assert (MG4 : rw_cells ssegs m MG [C1 (Z_to_bv 8 k0); C1 (Z_to_bv 8 k1); C1 (Z_to_bv 8 k2); C1 (Z_to_bv 8 k3)]).
    { eapply rw_cells_recell; [exact HMG | cbn; repeat split; exact Logic.I | reflexivity]. }
    clear HMG.
    destruct (rw_cells_forget _ _ _ _ HERR) as [ej0 ERRc]. clear HERR. cbn [cells_size] in ERRc. rewrite Hec in ERRc. change (4 + 0)%nat with 4%nat in ERRc.
    unfold PCAP_NG_CHECK_HEADER_ENTRY.
    rewrite (ngc_head_eq MOps (prims HO fo_nop sites)). unfold ngc_head. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. rewrite le_of_bytes_4.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (ERR, ERR + 4)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    hide HEB.
    destruct (Z.eq_dec (k0 + 256 * k1 + 65536 * k2 + 16777216 * k3) BT_SHB) as [EQM|NEM].
    2: { (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) NEM). cbn [negb]. apply (implM_ret ssegs).
      carve_frame 128%nat ST.
      lazymatch goal with
    | FRx : rw_cells ssegs ?mm ?A [CB 128 ?j] |- _ =>
        apply (rw_cells_split_CB ssegs mm A [] 128 j [] [40; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.   (* [comment removed for export] *)
      do 14 step. pstep.
      do 4 step. rewrite ?zxb_lit, ?sxb_lit by lia. do 7 step. rewrite (magic_word k0 k1 k2 k3) by lia.
      step. step.
      pose proof (magic_sx_range k0 k1 k2 k3 K0 K1 K2 K3) as WR. unfold BT_SHB in NEM.
      rewrite (eqb_lits_false (magic_sx k0 k1 k2 k3) 168627466); [| lia | lia | unfold magic_sx; clear - NEM K0 K1 K2 K3; Z.div_mod_to_equations; lia].
      cbn [negb]. cbv iota.
      destruct (rw_cells_cut _ _ _ 1 FR) as [HC FRS]. cbn [firstn skipn cells_size csize Nat.add app] in HC, FRS.
      lazymatch type of FRS with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -88)%Z in FRS by lia end.
      unhide HEB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp - 128, bv_unsigned sp); (ERR, ERR + 4)]%Z a) m m1) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      eapply ngc_notme; [exact CTX | left; reflexivity | assumption | assumption | | | reflexivity | exact HC | reflexivity | exact FRS | exact ERRc | exact MG4 | ].
      - eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia.
      - eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil].
      - transport HEB m1 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside] in *; lia). exact HEB. }
    (* [comment removed for export] *)
    rewrite EQM, Z.eqb_refl. cbn [negb mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
    assert (E128 : magic_sx k0 k1 k2 k3 = 168627466%Z) by (unfold magic_sx; unfold BT_SHB in EQM; clear - EQM K0 K1 K2 K3; Z.div_mod_to_equations; lia).
    ienter. carve_frame 128%nat ST.
    lazymatch goal with
    | FRx : rw_cells ssegs ?mm ?A [CB 128 ?j] |- _ =>
        apply (rw_cells_split_CB ssegs mm A [] 128 j [] [40; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.   (* [comment removed for export] *)
    do 14 step. pstep.
    do 4 step. rewrite ?zxb_lit, ?sxb_lit by lia. do 7 step. rewrite (magic_word k0 k1 k2 k3) by lia.
    step. step. rewrite (eqb_lits_eq _ _ E128). cbn [negb]. cbv iota.
    destruct (rw_cells_cut _ _ _ 1 FR) as [HC FRS]. clear FR. cbn [firstn skipn cells_size csize Nat.add app] in HC, FRS.
    lazymatch type of FRS with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -88)%Z in FRS by lia end.
    pose proof (rw_cells_split_CB ssegs _ _ [] 40 _ [] [32; 4; 4]%nat HC eq_refl) as HC3. clear HC. cbn [mk_CB_cells app] in HC3.
    destruct (rw_cells_cut _ _ _ 1 HC3) as [HCA HBT]. clear HC3. cbn [firstn skipn cells_size csize Nat.add app] in HCA, HBT.
    destruct (rw_cells_cut _ _ _ 1 HBT) as [HB HT]. clear HBT. cbn [firstn skipn cells_size csize Nat.add app] in HB, HT.
    lazymatch type of HB with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -96)%Z in HB by lia end.
    lazymatch type of HT with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -92)%Z in HT by lia end.
    do 7 step.
    destruct (rw_cells_forget _ _ _ _ HCA) as [ca HCA']. clear HCA. destruct (rw_cells_forget _ _ _ _ HB) as [jb0 HB']. clear HB. destruct (rw_cells_forget _ _ _ _ HT) as [jt0 HT']. clear HT.
    cbn [cells_size csize Nat.add] in HCA', HB', HT'.
    unhide HEB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G1 : GIo K R s CL FB mm) by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AG1 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|]; pose proof (CLB a Ha); lia);
      assert (HEB1 : rw_cells ssegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia])
    end.
    clear MU WM HEB.
    name_sp sp (-128)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop].
      replace (sites SiteNgTotalLength + 0)%Z with (bv_unsigned sp + -92)%Z by (rewrite SITES; unfold sites_at, D_CHECK_HEADER; lia).
      eapply FREAD; [ split; [exact G1|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact HT' | right; rewrite Hsp; lia]. }
    intros got ps2 ms2 PO. cbv beta in PO.
    destruct PO as (av & m2 & junk' & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & GOTL & GOTR & HD2).
    unfold hpost_regs in E. destruct_exs E. subst ms2. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x166a8)) with (Z_to_bv 64 0x166a8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (KEEP : forall A cs, rw_cells ssegs m1 A cs -> (bv_unsigned sp + -128 <= A)%Z ->
                   (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -92 \/ bv_unsigned sp + -88 <= A)%Z -> rw_cells ssegs m2 A cs).
    { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG2 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in HCA'; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in HB'; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KEEP in MG4; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in HEB1; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear KEEP.
    assert (AG02 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m2).
    { eapply agrees_on_trans; [exact AG1|]. eapply agrees_on_weaken; [exact AG2|].
      intros a [[Ha|Ha] [Hn1 Hn2]]; [split; [left; lia| lia]|]. pose proof (CLB a Ha). split; [right; exact Ha| lia]. }
    clear AG1 AG2 HT' G1 MI ST.
    unfold zlength in GOTL |- *.
    destruct (Z.eq_dec (Z.of_nat (length got)) 4) as [L4|L4].
    2: { (* [comment removed for export] *)
      replace (Z.of_nat (length got) <? 4)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      assert (HC40 : exists hc, rw_cells ssegs m2 (bv_unsigned sp + -128) hc /\ cells_size hc = 40%nat).
      { exists ([CB 32 ca] ++ [CB 4 jb0] ++ [CB (length got) (map b8 got); CB (Z.to_nat 4 - length got) junk']).
        pose proof (rw_cells_uncut _ _ _ _ _ HB' HD2 ltac:(cbn; lia)) as X.
        split; [eapply rw_cells_uncut; [exact HCA' | exact X | cbn; lia]| cbn [cells_size csize Nat.add app]; lia]. }
      destruct HC40 as (hc & HC40 & Hhc). clear HCA' HB' HD2.
      hide HC40. hide FRS. hide ERRc. hide MG4. hide HEB1.
      unfold implM. iprefix. step. step.
      rewrite ltu_lits by lia. replace (3 <? Z.of_nat (length got))%Z with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      unhide HC40. unhide FRS. unhide ERRc. unhide MG4. unhide HEB1.
      apply evt_done.
      eapply ngc_short; [exact CTX | left; reflexivity | exact MI2 | exact ST2 | exact AG02 | exact G2 | exact OF2 | exact HC40 | exact Hhc | exact FRS | exact ERRc | exact MG4 | exact HEB1]. }
    (* [comment removed for export] *)
    replace (Z.of_nat (length got) <? 4)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    destruct got as [|g0 [|g1 [|g2 [|g3 [|gx gr]]]]]; try (exfalso; cbn in L4; lia). clear L4 GOTL.
    pose proof GOTR as GR'. apply Forall_cons_iff in GR' as [T0 GR']. apply Forall_cons_iff in GR' as [T1 GR']. apply Forall_cons_iff in GR' as [T2 GR']. apply Forall_cons_iff in GR' as [T3 _].
    cbv beta in T0, T1, T2, T3.
    change (length [g0; g1; g2; g3]) with 4%nat in *. change (Z.to_nat 4 - 4)%nat with 0%nat in HD2. change (Z.of_nat 4) with 4%Z.
    hide HCA'. hide HB'. hide HD2. hide FRS. hide ERRc. hide MG4. hide HEB1.
    unfold implM. iprefix. step. step. rewrite ltu_lits by lia. replace (3 <? 4)%Z with true by reflexivity. cbv iota.
    do 5 step.
    unhide HB'.
    name_sp sp (-128)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop].
      replace (sites SiteNgByteOrderMagic + 0)%Z with (bv_unsigned sp + -96)%Z by (rewrite SITES; unfold sites_at, D_CHECK_HEADER; lia).
      eapply FREAD; [ split; [exact G2|]; split; [rewrite Hsp; exact ST2|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [exact MI2|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact HB' | right; rewrite Hsp; lia]. }
    intros got ps3 ms3 PO. cbv beta in PO.
    destruct PO as (av & m3 & junk3 & E & OF3 & MI3 & ST3 & AG3 & G3 & -> & GOTL & GOTR' & HD3).
    unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x166e4)) with (Z_to_bv 64 0x166e4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide HCA'. unhide HD2. unhide FRS. unhide ERRc. unhide MG4. unhide HEB1.
    assert (KEEP : forall A cs, rw_cells ssegs m2 A cs -> (bv_unsigned sp + -128 <= A)%Z ->
                   (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -96 \/ bv_unsigned sp + -92 <= A)%Z -> rw_cells ssegs m3 A cs).
    { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG3 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in HCA'; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in HD2; [|lia|cbn [cells_size csize Nat.add length]; lia].
    apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KEEP in MG4; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in HEB1; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear KEEP.
    assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3).
    { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AG3|].
      intros a [[Ha|Ha] [Hn1 Hn2]]; [split; [left; lia| lia]|]. pose proof (CLB a Ha). split; [right; exact Ha| lia]. }
    clear AG02 AG3 HB' G2 MI2 ST2.
    unfold zlength in GOTL |- *.
    destruct (Z.eq_dec (Z.of_nat (length got)) 4) as [L4|L4].
    2: { (* [comment removed for export] *)
      replace (Z.of_nat (length got) <? 4)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      assert (HC40 : exists hc, rw_cells ssegs m3 (bv_unsigned sp + -128) hc /\ cells_size hc = 40%nat).
      { exists ([CB 32 ca] ++ [CB (length got) (map b8 got); CB (Z.to_nat 4 - length got) junk3] ++ [CB 4 (map b8 [g0; g1; g2; g3]); CB 0 junk']).
        pose proof (rw_cells_uncut _ _ _ _ _ HD3 HD2 ltac:(cbn; lia)) as X.
        split; [eapply rw_cells_uncut; [exact HCA' | exact X | cbn; lia]| cbn [cells_size csize Nat.add app]; lia]. }
      destruct HC40 as (hc & HC40 & Hhc). clear HCA' HD3 HD2.
      hide HC40. hide FRS. hide ERRc. hide MG4. hide HEB1.
      unfold implM. iprefix. step.
      rewrite ltu_lits by lia. replace (3 <? Z.of_nat (length got))%Z with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      unhide HC40. unhide FRS. unhide ERRc. unhide MG4. unhide HEB1.
      apply evt_done.
      eapply ngc_short; [exact CTX | right; reflexivity | exact MI3 | exact ST3 | exact AG03 | exact G3 | exact (eq_trans OF3 OF2) | exact HC40 | exact Hhc | exact FRS | exact ERRc | exact MG4 | exact HEB1]. }
    (* [comment removed for export] *)
    replace (Z.of_nat (length got) <? 4)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    destruct got as [|b0 [|b1 [|b2 [|b3 [|bx br]]]]]; try (exfalso; cbn in L4; lia). clear L4 GOTL.
    pose proof GOTR' as GR'. apply Forall_cons_iff in GR' as [B0 GR']. apply Forall_cons_iff in GR' as [B1 GR']. apply Forall_cons_iff in GR' as [B2 GR']. apply Forall_cons_iff in GR' as [B3 _].
    cbv beta in B0, B1, B2, B3.
    change (length [b0; b1; b2; b3]) with 4%nat in *. change (Z.to_nat 4 - 4)%nat with 0%nat in HD3. change (Z.of_nat 4) with 4%Z.
    hide HCA'. hide HD2. hide HD3. hide FRS. hide ERRc. hide MG4. hide HEB1.
    unfold implM. iprefix. step. rewrite ltu_lits by lia. replace (3 <? 4)%Z with true by reflexivity. cbv iota.
    unhide HCA'. unhide HD2. unhide HD3. unhide FRS. unhide ERRc. unhide MG4. unhide HEB1.
    apply evt_done.
    eapply ngc_bom; [exact CTX | exact T0 | exact T1 | exact T2 | exact T3 | exact B0 | exact B1 | exact B2 | exact B3 | exact MI3 | exact ST3 | exact AG03 | exact G3
                    | exact (eq_trans OF3 OF2) | exact HCA' | exact HD3 | exact HD2 | exact FRS | exact ERRc | exact MG4 | exact HEB1].
  Qed.
  End Sz13.
  Theorem pcap_ng_check_header_proof : ltac:(let t := eval cbv delta [pcap_ng_check_header_proof__stmt] in pcap_ng_check_header_proof__stmt in exact t).
  Proof using AI FERROR FMT FREAD FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. red. unfold check_header_stmt_for. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo MG FA EB ERR f magic ej ec fuel. ltac2:(SecDiet.SzSec.closeP 'pcap_ng_check_header_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkNgMain.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcapng_ai__U3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chk__U3.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcapng_chkK. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_chkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_chkF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkB.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcapng_ai__U3.F_sfpcapng_chkC. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_sfpcapng_chkD.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chk__U3.F_sfpcapng_chkE.
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
Lemma ltu_lits : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y)%Z.
Proof using Type. pin_using tt. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.
Lemma sxv_range : forall a b c d, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z -> (0 <= sxv a b c d < 2^64)%Z.
Proof using Type. pin_using tt. intros. unfold sxv, le4val. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Lemma eqb_sxv_lit : forall a b c d v, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z -> (0 <= v < 2^31)%Z ->
  bv_eqb (Z_to_bv 64 (sxv a b c d)) (Z_to_bv 64 v) = (le4val a b c d =? v)%Z.
Proof using Type. pin_using tt.
  intros a b c d v Ha Hb Hc Hd Hv. unfold bv_eqb. pose proof (sxv_range a b c d Ha Hb Hc Hd) as R.
  rewrite (unsigned_lit (sxv a b c d)), (unsigned_lit v) by lia. unfold sxv in *.
  destruct (Z.eqb_spec (le4val a b c d) v) as [E|NE]; [apply Z.eqb_eq | apply Z.eqb_neq]; unfold le4val in *; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Lemma shb_len_ltu : forall (w : word) TL hi, (bv_unsigned w = TL + 4294967296 * hi)%Z -> (0 <= TL < 2^32)%Z -> (0 <= hi < 2^32)%Z ->
  bv_ltu (Z_to_bv 64 (-1048550)) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned w + 18446744073708503039))) = ((28 <=? TL) && (TL <=? 1048576))%Z.
Proof using Type. pin_using tt.
  intros w TL hi E HT Hh. unfold bv_ltu. rewrite E. rewrite !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul Z.div Z.ltb Z.leb andb Z.pow].
  change (2^64)%Z with 18446744073709551616%Z. change (2 ^ (32 - 1))%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z.
  destruct (Z.leb_spec 28 TL); destruct (Z.leb_spec TL 1048576); cbn [andb];
    first [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Definition swapw (w : word) : word :=
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 24)))
                                                    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned w) 65280))) 8))))))
                    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned w) 8))) 65280)))
                                                    (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned w)) 24)))))))).
Lemma swapw_eq : forall w,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 24)))
                                                    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned w) 65280))) 8))))))
                    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned w) 8))) 65280)))
                                                    (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned w)) 24))))))))
  = swapw w.
Proof using Type. pin_using tt. reflexivity. Qed.
Lemma swapw_sxv : forall a b c d, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z ->
  bv_unsigned (swapw (Z_to_bv 64 (sxv a b c d))) = (le4val d c b a + 4294967296 * (b + 256 * c + 65536 * d + 16777216 * ((d / 128 * 4294967295) mod 256)))%Z.
Proof using Type. pin_using tt.
  intros a b c d Ha Hb Hc Hd. unfold swapw. pose proof (sxv_range a b c d Ha Hb Hc Hd) as R.
  rewrite (swap32_val _ a b c d (d / 128 * 4294967295)); [unfold le4val; lia | lia | lia | lia | lia | Z.div_mod_to_equations; lia |].
  rewrite unsigned_lit by lia. unfold sxv, le4val. lia.
Qed.
Lemma swapw_hi_range : forall b c d x, (0 <= b < 256)%Z -> (0 <= c < 256)%Z -> (0 <= d < 256)%Z ->
  (0 <= b + 256 * c + 65536 * d + 16777216 * (x mod 256) < 2^32)%Z.
Proof using Type. pin_using tt. intros. pose proof (Z.mod_pos_bound x 256 ltac:(lia)). lia. Qed.

Section ChkNgMain.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREE : free_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis OPEN_COMMON : open_offline_common_stmt HO K sites.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis RBYTES : read_bytes_stmt HO K sites.
  Hypothesis RB : read_block_stmt HO K sites.
  Hypothesis AI : add_interface_stmt HO K sites.

  Open Scope bv_scope.
  (* [comment removed for export] *)
  Lemma ngc_hc40 : forall (sp : word) mx ca cb ct,
    rw_cells usegs mx (bv_unsigned sp + -128) [CB 32 ca] -> rw_cells usegs mx (bv_unsigned sp + -96) cb -> cells_size cb = 4%nat ->
    rw_cells usegs mx (bv_unsigned sp + -92) ct -> cells_size ct = 4%nat ->
    exists hc, rw_cells usegs mx (bv_unsigned sp + -128) hc /\ cells_size hc = 40%nat.
  Proof using Type. pin_using tt.
    intros sp mx ca cb ct HA HB Hcb HT Hct. exists ([CB 32 ca] ++ cb ++ ct).
    pose proof (rw_cells_uncut _ _ _ _ _ HB HT ltac:(rewrite Hcb; lia)) as HBT.
    pose proof (rw_cells_uncut _ _ _ _ _ HA HBT ltac:(cbn; lia)) as HABT.
    split; [exact HABT|]. rewrite !cells_size_app, Hcb, Hct. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition ngc_notme__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' : word) (pcx : Z) (m3 : mem) (ps3 : PS)
           (e : list byte) (hc : list cell),
      ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (pcx = 0x16c4c)%Z \/ ((pcx = 0x16c50)%Z /\ a0' = Z_to_bv 64 0) ->
      mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3 ->
      GIo K R ps3 CL FB m3 -> ps_outfile ps3 = ps_outfile s ->
      rw_cells usegs m3 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat ->
      rw_cells usegs m3 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m3 ERR [C4 (Z_to_bv 64 0)] -> rw_cells usegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m3 EB [CB 256 e] ->
      evt usegs (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s) CH_NotMe ps3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 pcx) fc None m3 (seg_rom usegs)).
  Section Sz9.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' pcx m3 ps3 e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_notme__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_notme__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_notme__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros CTX HPC MI3 ST3 AG3 G3 OF3 HC3 Hhc FRS3 ERR3 MG3 HEB3.
    destruct CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct (rw_cells_forget _ _ _ _ HC3) as [fj HC']. clear HC3. rewrite Hhc in HC'.
    hide HEB3. hide MG3. hide ERR3.
    destruct HPC as [-> |[-> ->]]; [do 14 step | do 13 step].
    all: release_frame HC' ST3 (bv_unsigned sp + -88)%Z; release_frame FRS3 ST3 (bv_unsigned sp).
    all: unhide HEB3; unhide MG3; unhide ERR3.
    all: destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL; cbn [map] in MG3.
    all: apply evt_done; unfold check_header_post.
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, (Z_to_bv 64 0) end.
    all: split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    all: split; [exact OF3|]; split; [assumption|]; split; [assumption|].
    all: split; [exact AG3|].
    all: split; [eapply rw_cells_recell; [exact MG3 | cbn; repeat split; exact Logic.I | reflexivity]|].
    all: split; [exact ERR3|].
    all: split; [reflexivity|]; split; [reflexivity|]; split; [exact G3| exists e; exact HEB3].
  Qed.
  End Sz9.
  Lemma ngc_notme : ltac:(let t := eval cbv delta [ngc_notme__stmt] in ngc_notme__stmt in exact t).
  Proof using Type. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' pcx m3 ps3 e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_notme__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_short__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s9' t3' t4' t5' t6' : word) (pcx : Z) (m2 : mem) (ps2 : PS)
           (e : list byte) (hc : list cell),
      ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (pcx = 0x16b68 \/ pcx = 0x16bac)%Z ->
      mem_inv usegs m2 -> stk usegs m2 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m2 ->
      GIo K R ps2 CL FB m2 -> ps_outfile ps2 = ps_outfile s ->
      rw_cells usegs m2 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat ->
      rw_cells usegs m2 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m2 ERR [C4 (Z_to_bv 64 0)] -> rw_cells usegs m2 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m2 EB [CB 256 e] ->
      implM usegs (mbind (e_ferror (prims HO fo_nop sites) f) (fun er : bool =>
                     if er then mbind (errmsg_for_errno MOps (prims HO fo_nop sites) "error reading dump file"%string []) (fun mm => mret (CH_Err mm))
                     else mret CH_NotMe)) ps2
        (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 FA) (Z_to_bv 64 3) s4' s5' s6' (Z_to_bv 64 0) s8' s9' s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 pcx) fc None m2 (seg_rom usegs)).
  Section Sz10.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s9' t3' t4' t5' t6' pcx m2 ps2 e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_short__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FERROR FMT HFL SFL. pin_using (fun (FERROR FMT HFL SFL : unit) => tt).
 intros CTX HPC MI2 ST2 AG2 G2 OF2 HC2 Hhc FRS2 ERR2 MG2 HEB2.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_ferror e_last_errno prims].
    hide HC2. hide FRS2. hide ERR2. hide MG2. hide HEB2.
    unfold implM. iprefix.
    destruct HPC as [-> | ->]; do 2 step.
    all: name_sp sp (-128)%Z.
    all: apply evt_done; eapply (implM_bind usegs);
      [ eapply FERROR; [| exact HinF | reflexivity];
        split; [exact G2|]; split; [rewrite Hsp; exact ST2|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
        split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]] |].
    all: intros er ps3 ms3 PO; cbv beta in PO; destruct PO as (av3 & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO);
         unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hsp in *; unname_sp.
    1: replace (ret_pc (Z_to_bv 64 0x16b70)) with (Z_to_bv 64 0x16b70) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    2: replace (ret_pc (Z_to_bv 64 0x16bb4)) with (Z_to_bv 64 0x16bb4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unhide HC2; unhide FRS2; unhide ERR2; unhide MG2; unhide HEB2.
    all: (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in HC2; [|lia]); (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in FRS2; [|lia]);
         (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in ERR2; [|lia]); (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in MG2; [|lia]);
         (apply (keeps_rw_cells_stack _ _ _ _ _ _ AG3) in HEB2; [|lia]).
    all: assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3)
           by (eapply agrees_on_trans; [exact AG2|]; eapply agrees_on_weaken; [exact AG3|]; intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]).
    all: clear AG3 MI2 ST2.
    all: destruct er; cbv iota.
    2,4: (* [comment removed for export] *)
         clear ERRNO; apply (implM_ret usegs); hide HC2; hide FRS2; hide ERR2; hide MG2; hide HEB2; cbn [Z.b2z]; step; if_true;
         unhide HC2; unhide FRS2; unhide ERR2; unhide MG2; unhide HEB2;
         eapply ngc_notme; [exact CTX | right; split; reflexivity | exact MI3 | exact ST3 | exact AG03 | exact G3 | exact OF2 | exact HC2 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB2].
    all: destruct (ERRNO eq_refl) as [EN2 ER]; clear ERRNO; unfold utp in EN2; rewrite <- TP in EN2.
    all: eapply implM_pure; [reflexivity|]; cbn [fst snd].
    all: set (err := lc_errno (ps_libc ps2)) in *.
    all: hide HC2; hide FRS2; hide ERR2; hide MG2; hide HEB2.
    all: pose proof (GIo_tls K _ _ _ _ _ G3) as [_ TB]; unfold tls_block_ok_u in TB; unfold utp in TB; rewrite <- TP in TB.
    all: assert (T4 : ((bv_unsigned tp + -164) mod 4 = 0)%Z) by (destruct TB as (TBA & _); apply Z.mod_divide in TBA; [|lia]; destruct TBA as [tq Hq]; apply Z.mod_divide; [lia|]; exists (tq * 4 + 9)%Z; lia).
    all: cbn [Z.b2z]; step; if_false.
    all: do 5 step; if_false_by (eqz_false (bv_unsigned tp + -164) ltac:(clear - TB; lia)).
    all: step; rewrite (and3_aligned (bv_unsigned tp + -164)) by (clear - TB T4; lia); step; if_false.
    1: do 7 step. 2: do 6 step.
    all: replace (sx32 (Z_to_bv 64 err)) with (Z_to_bv 64 (s32 err)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
    all: assert (MSG : fmt_at m3 0x108d6 "error reading dump file"%string)
           by (apply (fmt_at_intro m3 _ _ MI3); [vm_compute; reflexivity| lia| cbn; lia]).
    all: unhide HEB2; name_sp sp (-128)%Z.
    all: eapply evt_cut;
      [ eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps2 CL FB lo EB 0x108d6%Z err "error reading dump file"%string [] e);
          [| reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact HEB2
           | right; rewrite Hsp; lia | exact E8 ];
        split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|];
        split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]] |].
    all: cbv beta; intros ms' PO; destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & junk4 & -> & MI4 & ST4 & AG4 & G4 & HEB4);
         rewrite Hsp in *; unname_sp.
    all: replace (ret_pc (Z_to_bv 64 0x16be0)) with (Z_to_bv 64 0x16be0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unhide HC2; unhide FRS2; unhide ERR2; unhide MG2.
    all: transport HC2 m4 AG4 ltac:(intros a Ha; rewrite Hhc in Ha; split; [left; lia| lia]).
    all: transport FRS2 m4 AG4 ltac:(prs); transport ERR2 m4 AG4 ltac:(prs); transport MG2 m4 AG4 ltac:(prsMG GL).
    all: assert (AG04 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m4)
           by (eapply agrees_on_trans; [exact AG03|]; eapply agrees_on_weaken; [exact AG4|]; intros a [[Ha|Ha] [Hn _]]; (split; [|exact Hn]); [left; lia| right; exact Ha]).
    all: change (Z.to_nat 256) with 256%nat in HEB4.
    all: eapply (ngc_err_exit K sites HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m);
      [ exact CTX | right; left; reflexivity | exact MI4 | exact ST4 | exact AG04 | exact G4 | exact HC2 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB4
      | pose proof (fmt_errmsg_length "error reading dump file"%string [] err); lia
      | apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor] | exact OF2 ].
  Qed.
  End Sz10.
  Lemma ngc_short : ltac:(let t := eval cbv delta [ngc_short__stmt] in ngc_short__stmt in exact t).
  Proof using FERROR FMT HFL SFL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s8' s9' t3' t4' t5' t6' pcx m2 ps2 e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_short__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_lenfail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' w9 s9' t3' t4' t5' t6' : word) (TL hi9 : Z) (m2 : mem) (ps2 : PS)
           (e : list byte) (hc : list cell),
      ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (bv_unsigned w9 = TL + 4294967296 * hi9)%Z -> (0 <= TL < 2^32)%Z -> (0 <= hi9 < 2^32)%Z ->
      mem_inv usegs m2 -> stk usegs m2 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m2 ->
      GIo K R ps2 CL FB m2 -> ps_outfile ps2 = ps_outfile s ->
      rw_cells usegs m2 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat ->
      rw_cells usegs m2 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m2 ERR [C4 (Z_to_bv 64 0)] -> rw_cells usegs m2 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m2 EB [CB 256 e] ->
      evt usegs (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)
                   (CH_Err (Msg.shb_invalid_length TL)) ps2)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4' s5' s6' s7' w9 s9' s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16c28) fc None m2 (seg_rom usegs)).
  Section Sz11.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' w9 s9' t3' t4' t5' t6' TL hi9 m2 ps2 e hc : ltac2:(SecDiet.SzSec.tyM 'ngc_lenfail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_lenfail__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_lenfail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using HFL SFL SNPRINTF. pin_using (fun (HFL SFL SNPRINTF : unit) => tt).
 intros CTX W9 TLR HI9 MI2 ST2 AG2 G2 OF2 HC2 Hhc FRS2 ERR2 MG2 HEB2.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    hide HC2. hide FRS2. hide ERR2. hide MG2. hide HEB2.
    do 8 step.
    rewrite (swrap32_low _ TL hi9 W9).
    set (fs := "Section Header Block in pcapng dump file has invalid length %zu < _%u_ < %u (BT_SHB_INSANE_MAX)"%string).
    assert (MSG : fmt_at m2 0x107ea fs) by (apply (fmt_at_intro m2 _ _ MI2); [vm_compute; reflexivity| lia| cbn; lia]).
    unhide HEB2. name_sp sp (-128)%Z.
    eapply evt_cut.
    { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps2 CL FB lo EB 256%Z 0x107ea%Z fs [AInt 28; AInt (s32 TL); AInt 1048576] e);
        [ split; [exact G2|]; split; [rewrite Hsp; exact ST2|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI2|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | reflexivity | reflexivity | lia | exact MSG | subst fs; vm_compute; reflexivity | cbn; lia | | exact HEB2 | right; rewrite Hsp; lia ].
      cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
    cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x16c48)) with (Z_to_bv 64 0x16c48) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -128 - STDIO_STACK, bv_unsigned sp + -128); (EB, EB + 256)]%Z a) m2 m4)
      by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    unfold STDIO_STACK in AGS, MU4.
    assert (G4 : GIo K R ps2 CL FB m4).
    { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU4 | exact WM4 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    unhide HC2. unhide FRS2. unhide ERR2. unhide MG2.
    transport HC2 m4 AGS ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia).
    transport FRS2 m4 AGS ltac:(prs). transport ERR2 m4 AGS ltac:(prs). transport MG2 m4 AGS ltac:(prsMG GL).
    assert (AG4 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m4).
    { eapply agrees_on_trans; [exact AG2|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn _]]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia. }
    assert (EMSG : Fmt.snprintf 256 fs [AInt 28; AInt (s32 TL); AInt 1048576] = Msg.shb_invalid_length TL).
    { unfold Msg.shb_invalid_length, PCAP_ERRBUF_SIZE. subst fs. apply snprintf_pargs.
      replace (convs (fmt "Section Header Block in pcapng dump file has invalid length %zu < _%u_ < %u (BT_SHB_INSANE_MAX)")) with [Czu; Cu; Cu] by (vm_compute; reflexivity).
      apply pargs_cons; [apply aeq_same|]. apply pargs_cons; [apply aeq_s32; reflexivity|]. apply pargs_cons; [apply aeq_same| apply pargs_nil]. }
    pose proof (snprintf_length 256 fs [AInt 28; AInt (s32 TL); AInt 1048576]) as LS. change (Z.to_nat (256 - 1)) with 255%nat in LS.
    rewrite EMSG in LS, HEB4. change (Z.to_nat 256) with 256%nat in HEB4.
    replace (256 - length (Msg.shb_invalid_length TL) - 1)%nat with (255 - length (Msg.shb_invalid_length TL))%nat in HEB4 by lia.
    hide HC2. hide FRS2. hide ERR2. hide MG2. hide HEB4. step. unhide HC2. unhide FRS2. unhide ERR2. unhide MG2. unhide HEB4.
    eapply (ngc_err_exit K sites HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m);
      [ exact CTX | right; left; reflexivity | exact MI4 | exact ST4 | exact AG4 | exact G4 | exact HC2 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB4
      | lia | rewrite <- EMSG; subst fs; apply snprintf_ok; [vm_compute; reflexivity| repeat constructor] | exact OF2 ].
  Qed.
  End Sz11.
  Lemma ngc_lenfail : ltac:(let t := eval cbv delta [ngc_lenfail__stmt] in ngc_lenfail__stmt in exact t).
  Proof using HFL SFL SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' w9 s9' t3' t4' t5' t6' TL hi9 m2 ps2 e hc. ltac2:(SecDiet.SzSec.closeP 'ngc_lenfail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngc_bomk (fuel : nat) (f : hptr) (tlb bomb : list Z) :=
    let '(ok, swapped, total_length) :=
       (if get_le32 bomb 0 =? BYTE_ORDER_MAGIC then (true, false, get_le32 tlb 0)
        else if bswap32 (get_le32 bomb 0) =? BYTE_ORDER_MAGIC then (true, true, bswap32 (get_le32 tlb 0))
        else (false, false, get_le32 tlb 0)) in
    if negb ok then mret CH_NotMe else
    if ((total_length <? 28) || (BT_SHB_INSANE_MAX <? total_length))%Z then mret (CH_Err (Msg.shb_invalid_length total_length))
    else ngc_open MOps (prims HO fo_nop sites) fuel f 0 BT_SHB swapped total_length.

  (* [comment removed for export] *)
  Definition ngc_bom__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z) (m : mem) (fuel : nat)
           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) (ps2 : PS)
           (e ca jb jt : list byte) (t0 t1 t2 t3 b0 b1 b2 b3 : Z),
      ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m ->
      (0 <= t0 < 256)%Z -> (0 <= t1 < 256)%Z -> (0 <= t2 < 256)%Z -> (0 <= t3 < 256)%Z ->
      (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z -> (0 <= b2 < 256)%Z -> (0 <= b3 < 256)%Z ->
      mem_inv usegs m2 -> stk usegs m2 lo (bv_unsigned sp + -128) ->
      agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m2 ->
      GIo K R ps2 CL FB m2 -> ps_outfile ps2 = ps_outfile s ->
      rw_cells usegs m2 (bv_unsigned sp + -128) [CB 32 ca] ->
      rw_cells usegs m2 (bv_unsigned sp + -96) [CB 4 (map b8 [b0; b1; b2; b3]); CB 0 jb] ->
      rw_cells usegs m2 (bv_unsigned sp + -92) [CB 4 (map b8 [t0; t1; t2; t3]); CB 0 jt] ->
      rw_cells usegs m2 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m2 ERR [C4 (Z_to_bv 64 0)] -> rw_cells usegs m2 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells usegs m2 EB [CB 256 e] ->
      implM usegs (ngc_bomk fuel f [t0; t1; t2; t3] [b0; b1; b2; b3]) ps2
        (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 FA) (Z_to_bv 64 3) s4 s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16bf0) fc None m2 (seg_rom usegs)).
  Section Sz12.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 e ca jb jt t0 t1 t2 t3 b0 b1 b2 b3 : ltac2:(SecDiet.SzSec.tyM 'ngc_bom__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ngc_bom__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_bom__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AI FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. pin_using (fun (AI FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF : unit) => tt).
 intros CTX T0 T1 T2 T3 B0 B1 B2 B3 MI2 ST2 AG2 G2 OF2 HCA HB HT FRS2 ERR2 MG2 HEB2.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    (* [comment removed for export] *)
    assert (LJ : length jb = 0%nat /\ length jt = 0%nat) by (destruct HB as [[WF _] _]; destruct HT as [[WF' _] _]; cbn in WF, WF'; lia).
    destruct jb; [|exfalso; cbn in LJ; lia]. destruct jt; [|exfalso; cbn in LJ; lia]. clear LJ.
    assert (HB4 : rw_cells usegs m2 (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (le4val b0 b1 b2 b3))]).
    { eapply rw_cells_recell; [exact HB | cbn; repeat split; reflexivity |]. cbn [cells_bytes cbytes map app]. rewrite (le4_lit b0 b1 b2 b3) by lia. rewrite app_nil_r. reflexivity. }
    assert (HT4 : rw_cells usegs m2 (bv_unsigned sp + -92) [C4 (Z_to_bv 64 (le4val t0 t1 t2 t3))]).
    { eapply rw_cells_recell; [exact HT | cbn; repeat split; reflexivity |]. cbn [cells_bytes cbytes map app]. rewrite (le4_lit t0 t1 t2 t3) by lia. rewrite app_nil_r. reflexivity. }
    clear HB HT.
    unfold ngc_bomk, get_le32, zslice, zfirstn, zskipn. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. cbn [firstn skipn].
    rewrite (bswap32_bytes b0 b1 b2 b3), (bswap32_bytes t0 t1 t2 t3) by lia. rewrite !le_of_bytes_4.
    change (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)%Z with (le4val b0 b1 b2 b3).
    change (t0 + 256 * t1 + 65536 * t2 + 16777216 * t3)%Z with (le4val t0 t1 t2 t3).
    change (b3 + 256 * b2 + 65536 * b1 + 16777216 * b0)%Z with (le4val b3 b2 b1 b0).
    change (t3 + 256 * t2 + 65536 * t1 + 16777216 * t0)%Z with (le4val t3 t2 t1 t0).
    hide HCA. hide FRS2. hide ERR2. hide MG2. hide HEB2.
    ienter. step. rewrite (sx32_lit b0 b1 b2 b3) by lia. do 3 step.
    rewrite (eqb_sxv_lit b0 b1 b2 b3 1295788826) by lia.
    destruct (Z.eqb_spec (le4val b0 b1 b2 b3) 1295788826) as [EQS|NES].
    - (* [comment removed for export] *)
      replace (le4val b0 b1 b2 b3 =? BYTE_ORDER_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; rewrite EQS; discriminate).
      replace (le4val b3 b2 b1 b0 =? BYTE_ORDER_MAGIC)%Z with true by (symmetry; apply Z.eqb_eq; unfold le4val, BYTE_ORDER_MAGIC in *; lia).
      cbv beta iota.
      do 7 step. step. rewrite (sx32_lit t0 t1 t2 t3) by lia. do 13 step. rewrite !swapw_eq. do 6 step.
      pose proof (swapw_sxv t0 t1 t2 t3 T0 T1 T2 T3) as W9. pose proof (swapw_hi_range t1 t2 t3 (t3 / 128 * 4294967295) T1 T2 T3) as HI9.
      pose proof (swapw_sxv b0 b1 b2 b3 B0 B1 B2 B3) as W7. pose proof (swapw_hi_range b1 b2 b3 (b3 / 128 * 4294967295) B1 B2 B3) as HI7.
      rewrite (shb_len_ltu _ (le4val t3 t2 t1 t0) _ W9) by (unfold le4val; lia).
      destruct ((28 <=? le4val t3 t2 t1 t0) && (le4val t3 t2 t1 t0 <=? 1048576))%Z eqn:LC.
      + (* [comment removed for export] *)
        replace ((le4val t3 t2 t1 t0 <? 28) || (BT_SHB_INSANE_MAX <? le4val t3 t2 t1 t0))%Z with false by (unfold BT_SHB_INSANE_MAX; lia).
        cbn [negb].
        unhide HCA. unhide FRS2. unhide ERR2. unhide MG2. unhide HEB2.
        destruct (ngc_hc40 sp m2 ca _ _ HCA HB4 eq_refl HT4 eq_refl) as (hc & HC40 & Hhc).
        apply evt_done. eapply ngc_fill.
        all: try exact CTX. all: try assumption.
        1: exact W9. 1: exact HI9. 1: lia.
        1: replace BYTE_ORDER_MAGIC with (le4val b3 b2 b1 b0) by (unfold le4val, BYTE_ORDER_MAGIC in *; lia); exact W7.
        1: exact HI7. 1: exact HC40. 1: exact Hhc. 1: exact ERR2. 1: exact HEB2.
      + (* [comment removed for export] *)
        replace ((le4val t3 t2 t1 t0 <? 28) || (BT_SHB_INSANE_MAX <? le4val t3 t2 t1 t0))%Z with true by (unfold BT_SHB_INSANE_MAX; lia).
        cbn [negb].
        unhide HCA. unhide FRS2. unhide ERR2. unhide MG2. unhide HEB2.
        destruct (ngc_hc40 sp m2 ca _ _ HCA HB4 eq_refl HT4 eq_refl) as (hc & HC40 & Hhc).
        apply evt_done. apply (implM_ret usegs).
        eapply ngc_lenfail; [exact CTX | exact W9 | unfold le4val; lia | exact HI9 | exact MI2 | exact ST2 | exact AG2 | exact G2 | exact OF2 | exact HC40 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB2].
    - (* [comment removed for export] *)
      do 3 step. rewrite (eqb_sxv_lit b0 b1 b2 b3 439041101) by lia.
      destruct (Z.eqb_spec (le4val b0 b1 b2 b3) 439041101) as [EQN|NEN].
      + (* [comment removed for export] *)
        replace (le4val b0 b1 b2 b3 =? BYTE_ORDER_MAGIC)%Z with true by (symmetry; apply Z.eqb_eq; exact EQN).
        cbn [negb]. cbv beta iota.
        step. rewrite (sx32_lit t0 t1 t2 t3) by lia. do 6 step.
        assert (W9 : bv_unsigned (Z_to_bv 64 (sxv t0 t1 t2 t3)) = (le4val t0 t1 t2 t3 + 4294967296 * (t3 / 128 * 4294967295))%Z)
          by (rewrite <- (sx32_lit t0 t1 t2 t3) by lia; apply unsigned_sx32; lia).
        assert (HI9 : (0 <= t3 / 128 * 4294967295 < 2^32)%Z) by (clear - T3; Z.div_mod_to_equations; lia).
        rewrite (shb_len_ltu _ (le4val t0 t1 t2 t3) _ W9) by (unfold le4val; lia).
        unhide HCA. unhide FRS2. unhide ERR2. unhide MG2. unhide HEB2.
        destruct (ngc_hc40 sp m2 ca _ _ HCA HB4 eq_refl HT4 eq_refl) as (hc & HC40 & Hhc).
        destruct ((28 <=? le4val t0 t1 t2 t3) && (le4val t0 t1 t2 t3 <=? 1048576))%Z eqn:LC.
        * (* [comment removed for export] *)
          replace ((le4val t0 t1 t2 t3 <? 28) || (BT_SHB_INSANE_MAX <? le4val t0 t1 t2 t3))%Z with false by (unfold BT_SHB_INSANE_MAX; lia).
          cbv iota. apply evt_done. eapply ngc_fill.
          all: try exact CTX. all: try assumption.
          1: exact W9. 1: exact HI9. 1: lia. 1: rewrite unsigned_lit by lia; unfold BYTE_ORDER_MAGIC; instantiate (1 := 0%Z); reflexivity.
          1: lia. 1: exact HC40. 1: exact Hhc. 1: exact ERR2. 1: exact HEB2.
        * (* [comment removed for export] *)
          replace ((le4val t0 t1 t2 t3 <? 28) || (BT_SHB_INSANE_MAX <? le4val t0 t1 t2 t3))%Z with true by (unfold BT_SHB_INSANE_MAX; lia).
          cbv iota. apply evt_done. apply (implM_ret usegs).
          eapply ngc_lenfail; [exact CTX | exact W9 | unfold le4val; lia | exact HI9 | exact MI2 | exact ST2 | exact AG2 | exact G2 | exact OF2 | exact HC40 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB2].
      + (* [comment removed for export] *)
        replace (le4val b0 b1 b2 b3 =? BYTE_ORDER_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; exact NEN).
        replace (le4val b3 b2 b1 b0 =? BYTE_ORDER_MAGIC)%Z with false by (symmetry; apply Z.eqb_neq; intros X; apply NES; unfold le4val, BYTE_ORDER_MAGIC in *; lia).
        cbn [negb]. cbv beta iota.
        unhide HCA. unhide FRS2. unhide ERR2. unhide MG2. unhide HEB2.
        destruct (ngc_hc40 sp m2 ca _ _ HCA HB4 eq_refl HT4 eq_refl) as (hc & HC40 & Hhc).
        apply evt_done. apply (implM_ret usegs).
        eapply ngc_notme; [exact CTX | left; reflexivity | exact MI2 | exact ST2 | exact AG2 | exact G2 | exact OF2 | exact HC40 | exact Hhc | exact FRS2 | exact ERR2 | exact MG2 | exact HEB2].
  Qed.
  End Sz12.
  Lemma ngc_bom : ltac:(let t := eval cbv delta [ngc_bom__stmt] in ngc_bom__stmt in exact t).
  Proof using AI FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 ps2 e ca jb jt t0 t1 t2 t3 b0 b1 b2 b3. ltac2:(SecDiet.SzSec.closeP 'ngc_bom__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition pcap_ng_check_header_proof__stmt : Prop := pcap_ng_check_header_stmt HO K sites.
  Section Sz13.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo MG FA EB ERR f magic ej ec fuel : ltac2:(SecDiet.SzSec.tyM 'pcap_ng_check_header_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_ng_check_header_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_ng_check_header_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AI FERROR FMT FREAD FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. pin_using (fun (AI FERROR FMT FREAD FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF : unit) => tt).
    intros PRE HinF SITES -> -> -> -> -> HMG GR GL HEB HERR Hec R1 R2 R3 E1 E2 D1 E4 E8.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. unfold rc_lo in LO. unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    pose proof R3 as MGU. unfold rc_spmain in MGU.
    assert (CTX : ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m).
    { split; [exact G|]. repeat (split; [fastfirst (first [eassumption | lia])|]). exact E8. }
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    destruct magic as [|k0 [|k1 [|k2 [|k3 [|? ?]]]]]; try discriminate GL.
    pose proof GR as GR'. apply Forall_cons_iff in GR' as [K0 GR']. apply Forall_cons_iff in GR' as [K1 GR']. apply Forall_cons_iff in GR' as [K2 GR']. apply Forall_cons_iff in GR' as [K3 _].
    cbv beta in K0, K1, K2, K3.
    cbn [map] in HMG.
    assert (MG4 : rw_cells usegs m MG [C1 (Z_to_bv 8 k0); C1 (Z_to_bv 8 k1); C1 (Z_to_bv 8 k2); C1 (Z_to_bv 8 k3)]).
    { eapply rw_cells_recell; [exact HMG | cbn; repeat split; exact Logic.I | reflexivity]. }
    clear HMG.
    destruct (rw_cells_forget _ _ _ _ HERR) as [ej0 ERRc]. clear HERR. cbn [cells_size] in ERRc. rewrite Hec in ERRc. change (4 + 0)%nat with 4%nat in ERRc.
    unfold PCAP_NG_CHECK_HEADER_ENTRY.
    rewrite (ngc_head_eq MOps (prims HO fo_nop sites)). unfold ngc_head. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. rewrite le_of_bytes_4.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (ERR, ERR + 4)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide HEB.
    destruct (Z.eq_dec (k0 + 256 * k1 + 65536 * k2 + 16777216 * k3) BT_SHB) as [EQM|NEM].
    2: { (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) NEM). cbn [negb]. apply (implM_ret usegs).
      carve_frame 128%nat ST.
      lazymatch goal with
    | FRx : rw_cells usegs ?mm ?A [CB 128 ?j] |- _ =>
        apply (rw_cells_split_CB usegs mm A [] 128 j [] [40; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.   (* [comment removed for export] *)
      do 12 step.
      step. if_false_by (eqz_false ERR ltac:(lia)). step. step.
      step. rewrite (and3_aligned ERR) by lia. step. if_false. step. pstep.
      do 4 step. rewrite ?zxb_lit, ?sxb_lit by lia. do 7 step. rewrite (magic_word k0 k1 k2 k3) by lia.
      step. step.
      pose proof (magic_sx_range k0 k1 k2 k3 K0 K1 K2 K3) as WR. unfold BT_SHB in NEM.
      rewrite (eqb_lits_false (magic_sx k0 k1 k2 k3) 168627466); [| lia | lia | unfold magic_sx; clear - NEM K0 K1 K2 K3; Z.div_mod_to_equations; lia].
      cbn [negb]. cbv iota.
      destruct (rw_cells_cut _ _ _ 1 FR) as [HC FRS]. cbn [firstn skipn cells_size csize Nat.add app] in HC, FRS.
      lazymatch type of FRS with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -88)%Z in FRS by lia end.
      unhide HEB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp - 128, bv_unsigned sp); (ERR, ERR + 4)]%Z a) m m1) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      eapply ngc_notme; [exact CTX | left; reflexivity | assumption | assumption | | | reflexivity | exact HC | reflexivity | exact FRS | exact ERRc | exact MG4 | ].
      - eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|]. pose proof (CLB a Ha). lia.
      - eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil].
      - transport HEB m1 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside] in *; lia). exact HEB. }
    (* [comment removed for export] *)
    rewrite EQM, Z.eqb_refl. cbn [negb mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
    assert (E128 : magic_sx k0 k1 k2 k3 = 168627466%Z) by (unfold magic_sx; unfold BT_SHB in EQM; clear - EQM K0 K1 K2 K3; Z.div_mod_to_equations; lia).
    ienter. carve_frame 128%nat ST.
    lazymatch goal with
    | FRx : rw_cells usegs ?mm ?A [CB 128 ?j] |- _ =>
        apply (rw_cells_split_CB usegs mm A [] 128 j [] [40; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.   (* [comment removed for export] *)
    do 12 step.
    step. if_false_by (eqz_false ERR ltac:(lia)). step. step.
    step. rewrite (and3_aligned ERR) by lia. step. if_false. step. pstep.
    do 4 step. rewrite ?zxb_lit, ?sxb_lit by lia. do 7 step. rewrite (magic_word k0 k1 k2 k3) by lia.
    step. step. rewrite (eqb_lits_eq _ _ E128). cbn [negb]. cbv iota.
    destruct (rw_cells_cut _ _ _ 1 FR) as [HC FRS]. clear FR. cbn [firstn skipn cells_size csize Nat.add app] in HC, FRS.
    lazymatch type of FRS with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -88)%Z in FRS by lia end.
    pose proof (rw_cells_split_CB usegs _ _ [] 40 _ [] [32; 4; 4]%nat HC eq_refl) as HC3. clear HC. cbn [mk_CB_cells app] in HC3.
    destruct (rw_cells_cut _ _ _ 1 HC3) as [HCA HBT]. clear HC3. cbn [firstn skipn cells_size csize Nat.add app] in HCA, HBT.
    destruct (rw_cells_cut _ _ _ 1 HBT) as [HB HT]. clear HBT. cbn [firstn skipn cells_size csize Nat.add app] in HB, HT.
    lazymatch type of HB with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -96)%Z in HB by lia end.
    lazymatch type of HT with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -92)%Z in HT by lia end.
    do 6 step.
    destruct (rw_cells_forget _ _ _ _ HCA) as [ca HCA']. clear HCA. destruct (rw_cells_forget _ _ _ _ HB) as [jb0 HB']. clear HB. destruct (rw_cells_forget _ _ _ _ HT) as [jt0 HT']. clear HT.
    cbn [cells_size csize Nat.add] in HCA', HB', HT'.
    unhide HEB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G1 : GIo K R s CL FB mm) by (eapply (GIo_client_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]; apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]);
      assert (AG1 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [lia|]; pose proof (CLB a Ha); lia);
      assert (HEB1 : rw_cells usegs mm EB [CB 256 ej])
        by (eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho] | exact HEB | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia])
    end.
    clear MU WM HEB.
    name_sp sp (-128)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop].
      replace (sites SiteNgTotalLength + 0)%Z with (bv_unsigned sp + -92)%Z by (rewrite SITES; unfold sites_at, D_CHECK_HEADER; lia).
      eapply FREAD; [ split; [exact G1|]; split; [rewrite Hsp; exact ST|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact HT' | right; rewrite Hsp; lia]. }
    intros got ps2 ms2 PO. cbv beta in PO.
    destruct PO as (av & m2 & junk' & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & GOTL & GOTR & HD2).
    unfold hpost_regs in E. destruct_exs E. subst ms2. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x16b60)) with (Z_to_bv 64 0x16b60) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (KEEP : forall A cs, rw_cells usegs m1 A cs -> (bv_unsigned sp + -128 <= A)%Z ->
                   (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -92 \/ bv_unsigned sp + -88 <= A)%Z -> rw_cells usegs m2 A cs).
    { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG2 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in HCA'; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in HB'; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KEEP in MG4; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in HEB1; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear KEEP.
    assert (AG02 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m2).
    { eapply agrees_on_trans; [exact AG1|]. eapply agrees_on_weaken; [exact AG2|].
      intros a [[Ha|Ha] [Hn1 Hn2]]; [split; [left; lia| lia]|]. pose proof (CLB a Ha). split; [right; exact Ha| lia]. }
    clear AG1 AG2 HT' G1 MI ST.
    unfold zlength in GOTL |- *.
    destruct (Z.eq_dec (Z.of_nat (length got)) 4) as [L4|L4].
    2: { (* [comment removed for export] *)
      replace (Z.of_nat (length got) <? 4)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      assert (HC40 : exists hc, rw_cells usegs m2 (bv_unsigned sp + -128) hc /\ cells_size hc = 40%nat).
      { exists ([CB 32 ca] ++ [CB 4 jb0] ++ [CB (length got) (map b8 got); CB (Z.to_nat 4 - length got) junk']).
        pose proof (rw_cells_uncut _ _ _ _ _ HB' HD2 ltac:(cbn; lia)) as X.
        split; [eapply rw_cells_uncut; [exact HCA' | exact X | cbn; lia]| cbn [cells_size csize Nat.add app]; lia]. }
      destruct HC40 as (hc & HC40 & Hhc). clear HCA' HB' HD2.
      hide HC40. hide FRS. hide ERRc. hide MG4. hide HEB1.
      unfold implM. iprefix. step. step.
      rewrite ltu_lits by lia. replace (3 <? Z.of_nat (length got))%Z with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      unhide HC40. unhide FRS. unhide ERRc. unhide MG4. unhide HEB1.
      apply evt_done.
      eapply ngc_short; [exact CTX | left; reflexivity | exact MI2 | exact ST2 | exact AG02 | exact G2 | exact OF2 | exact HC40 | exact Hhc | exact FRS | exact ERRc | exact MG4 | exact HEB1]. }
    (* [comment removed for export] *)
    replace (Z.of_nat (length got) <? 4)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    destruct got as [|g0 [|g1 [|g2 [|g3 [|gx gr]]]]]; try (exfalso; cbn in L4; lia). clear L4 GOTL.
    pose proof GOTR as GR'. apply Forall_cons_iff in GR' as [T0 GR']. apply Forall_cons_iff in GR' as [T1 GR']. apply Forall_cons_iff in GR' as [T2 GR']. apply Forall_cons_iff in GR' as [T3 _].
    cbv beta in T0, T1, T2, T3.
    change (length [g0; g1; g2; g3]) with 4%nat in *. change (Z.to_nat 4 - 4)%nat with 0%nat in HD2. change (Z.of_nat 4) with 4%Z.
    hide HCA'. hide HB'. hide HD2. hide FRS. hide ERRc. hide MG4. hide HEB1.
    unfold implM. iprefix. step. step. rewrite ltu_lits by lia. replace (3 <? 4)%Z with true by reflexivity. cbv iota.
    do 5 step.
    unhide HB'.
    name_sp sp (-128)%Z.
    apply evt_done. eapply (implM_bind usegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop].
      replace (sites SiteNgByteOrderMagic + 0)%Z with (bv_unsigned sp + -96)%Z by (rewrite SITES; unfold sites_at, D_CHECK_HEADER; lia).
      eapply FREAD; [ split; [exact G2|]; split; [rewrite Hsp; exact ST2|]; split; [unfold rc_lo; lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
                      split; [rewrite Hsp; lia|]; split; [exact MI2|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
                    | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact HB' | right; rewrite Hsp; lia]. }
    intros got ps3 ms3 PO. cbv beta in PO.
    destruct PO as (av & m3 & junk3 & E & OF3 & MI3 & ST3 & AG3 & G3 & -> & GOTL & GOTR' & HD3).
    unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x16ba8)) with (Z_to_bv 64 0x16ba8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide HCA'. unhide HD2. unhide FRS. unhide ERRc. unhide MG4. unhide HEB1.
    assert (KEEP : forall A cs, rw_cells usegs m2 A cs -> (bv_unsigned sp + -128 <= A)%Z ->
                   (A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -96 \/ bv_unsigned sp + -92 <= A)%Z -> rw_cells usegs m3 A cs).
    { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG3 | exact HC | intros a Ha; split; [left; lia| lia]]. }
    apply KEEP in HCA'; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in HD2; [|lia|cbn [cells_size csize Nat.add length]; lia].
    apply KEEP in FRS; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in ERRc; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KEEP in MG4; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KEEP in HEB1; [|lia|cbn [cells_size csize Nat.add]; lia].
    clear KEEP.
    assert (AG03 : agrees_on (fun a => client_keeps CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4))%Z m m3).
    { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AG3|].
      intros a [[Ha|Ha] [Hn1 Hn2]]; [split; [left; lia| lia]|]. pose proof (CLB a Ha). split; [right; exact Ha| lia]. }
    clear AG02 AG3 HB' G2 MI2 ST2.
    unfold zlength in GOTL |- *.
    destruct (Z.eq_dec (Z.of_nat (length got)) 4) as [L4|L4].
    2: { (* [comment removed for export] *)
      replace (Z.of_nat (length got) <? 4)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      assert (HC40 : exists hc, rw_cells usegs m3 (bv_unsigned sp + -128) hc /\ cells_size hc = 40%nat).
      { exists ([CB 32 ca] ++ [CB (length got) (map b8 got); CB (Z.to_nat 4 - length got) junk3] ++ [CB 4 (map b8 [g0; g1; g2; g3]); CB 0 junk']).
        pose proof (rw_cells_uncut _ _ _ _ _ HD3 HD2 ltac:(cbn; lia)) as X.
        split; [eapply rw_cells_uncut; [exact HCA' | exact X | cbn; lia]| cbn [cells_size csize Nat.add app]; lia]. }
      destruct HC40 as (hc & HC40 & Hhc). clear HCA' HD3 HD2.
      hide HC40. hide FRS. hide ERRc. hide MG4. hide HEB1.
      unfold implM. iprefix. step.
      rewrite ltu_lits by lia. replace (3 <? Z.of_nat (length got))%Z with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      unhide HC40. unhide FRS. unhide ERRc. unhide MG4. unhide HEB1.
      apply evt_done.
      eapply ngc_short; [exact CTX | right; reflexivity | exact MI3 | exact ST3 | exact AG03 | exact G3 | exact (eq_trans OF3 OF2) | exact HC40 | exact Hhc | exact FRS | exact ERRc | exact MG4 | exact HEB1]. }
    (* [comment removed for export] *)
    replace (Z.of_nat (length got) <? 4)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    destruct got as [|b0 [|b1 [|b2 [|b3 [|bx br]]]]]; try (exfalso; cbn in L4; lia). clear L4 GOTL.
    pose proof GOTR' as GR'. apply Forall_cons_iff in GR' as [B0 GR']. apply Forall_cons_iff in GR' as [B1 GR']. apply Forall_cons_iff in GR' as [B2 GR']. apply Forall_cons_iff in GR' as [B3 _].
    cbv beta in B0, B1, B2, B3.
    change (length [b0; b1; b2; b3]) with 4%nat in *. change (Z.to_nat 4 - 4)%nat with 0%nat in HD3. change (Z.of_nat 4) with 4%Z.
    hide HCA'. hide HD2. hide HD3. hide FRS. hide ERRc. hide MG4. hide HEB1.
    unfold implM. iprefix. step. rewrite ltu_lits by lia. replace (3 <? 4)%Z with true by reflexivity. cbv iota.
    unhide HCA'. unhide HD2. unhide HD3. unhide FRS. unhide ERRc. unhide MG4. unhide HEB1.
    apply evt_done.
    eapply ngc_bom; [exact CTX | exact T0 | exact T1 | exact T2 | exact T3 | exact B0 | exact B1 | exact B2 | exact B3 | exact MI3 | exact ST3 | exact AG03 | exact G3
                    | exact (eq_trans OF3 OF2) | exact HCA' | exact HD3 | exact HD2 | exact FRS | exact ERRc | exact MG4 | exact HEB1].
  Qed.
  End Sz13.
  Theorem pcap_ng_check_header_proof : ltac:(let t := eval cbv delta [pcap_ng_check_header_proof__stmt] in pcap_ng_check_header_proof__stmt in exact t).
  Proof using AI FERROR FMT FREAD FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. red. unfold check_header_stmt_for. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CL FB lo MG FA EB ERR f magic ej ec fuel. ltac2:(SecDiet.SzSec.closeP 'pcap_ng_check_header_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkNgMain.

End WithCeil.
End TwB.
End F_sfpcapng_chk.
