(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_ngA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_pcap_open2A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Definition fmt_errmsg_length__stmt : Prop := forall f args e, (length (fmt_errmsg f args e) <= 255)%nat.
Section Sz1.
Variables f args e : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_length__stmt "vvv" @f).
#[using="Type"] Lemma fmt_errmsg_length__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_length__stmt "vvv").
Proof.
 unfold fmt_errmsg, snprintf, snprintf_out, PCAP_ERRBUF_SIZE, zlength.
  set (mm := firstn (Z.to_nat (256 - 1)) (fmt_output (fmt f) args)).
  assert (Hm : (length mm <= 255)%nat) by (subst mm; rewrite length_firstn; apply Nat.le_min_l).
  destruct (256 <? Z.of_nat (length mm) + 3)%Z eqn:E; [exact Hm|].
  apply Z.ltb_ge in E. rewrite !length_app, length_firstn. cbn [length str String.list_ascii_of_string map].
  unfold str. cbn [String.list_ascii_of_string map length]. lia.
Qed.
End Sz1.
Lemma fmt_errmsg_length : ltac:(let t := eval cbv delta [fmt_errmsg_length__stmt] in fmt_errmsg_length__stmt in exact t).
Proof. intros f args e. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_length__body "vvv"). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Open.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FOPEN_OFFLINE : fopen_offline_stmt HO FO sites GIOA TP.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis GH : gia_harn_laws GIOA.

  (* [comment removed for export] *)
  Definition new_file_not_out__stmt : Prop := forall L RNG s CL FB FL m L2 RNG2 s2 CL2 FL2 m2 f Af,
    GIOA L RNG s CL FB FL m -> GIOA L2 RNG2 s2 CL2 ((f, Af, FILE_BLOCK) :: FB) FL2 m2 -> ps_outfile s2 = ps_outfile s -> ps_outfile s2 <> Some f.
  Section Sz2.
  Variables L RNG s CL FB FL m L2 RNG2 s2 CL2 FL2 m2 f Af : ltac2:(SecDiet.SzSec.tyM 'new_file_not_out__stmt "vvvvvvvvvvvvvvv" @L).
  #[using="rc tlsI HO FO fflagA GL HAL GH"] Lemma new_file_not_out__body : ltac2:(SecDiet.SzSec.bodyP 'new_file_not_out__stmt "vvvvvvvvvvvvvvv").
  Proof.
    intros G G2 EO HO2.
 rewrite EO in HO2.
    pose proof (gh_outfile _ GH _ _ _ _ _ _ _ G) as GO. rewrite HO2 in GO. destruct GO as (A & HinA & _).
    assert (E1 : blk_addr HO s2 f = Af) by (exact (HAL _ _ _ _ _ _ _ (f, Af, FILE_BLOCK) G2 ltac:(apply in_or_app; right; left; reflexivity))).
    assert (E2 : blk_addr HO s2 f = A) by (exact (HAL _ _ _ _ _ _ _ (f, A, FILE_BLOCK) G2 ltac:(apply in_or_app; right; right; exact HinA))).
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G2) as BA. apply blocks_apart_app_inv in BA as (_ & BA & _).
    cbn [blocks_apart] in BA. destruct BA as [FA _]. pose proof (proj1 (Forall_forall _ _) FA _ HinA) as AP.
    unfold apart, cb_addr, cb_size, FILE_BLOCK in AP. cbn [fst snd] in AP. lia.
  Qed.
  End Sz2.
  #[using="rc tlsI HO FO fflagA GL HAL GH"] Lemma new_file_not_out : ltac:(let t := eval cbv delta [new_file_not_out__stmt] in new_file_not_out__stmt in exact t).
  Proof. intros L RNG s CL FB FL m L2 RNG2 s2 CL2 FL2 m2 f Af. ltac2:(SecDiet.SzSec.closeP 'new_file_not_out__body "vvvvvvvvvvvvvvv"). Qed.

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  #[using="Type"] Lemma cstr_no_nul : forall (bs : list byte), ~ In (Z_to_bv 8 0) bs -> cstr (map bv_unsigned bs) = map bv_unsigned bs.
  Proof.
    induction bs as [|b bs IH]; intros Hn; [reflexivity|]. cbn [map cstr].
    destruct (bv_unsigned b =? 0)%Z eqn:E.
    - exfalso. apply Hn. left. apply Z.eqb_eq in E. apply bv_eq. rewrite E. reflexivity.
    - f_equal. apply IH. intros Hin. apply Hn. right. exact Hin.
  Qed.

  (* [comment removed for export] *)
  Definition open_offline_wtp_proofA__stmt : Prop := pcap_open_offline_wtp_stmt HO FO sites GIOA TP.
  Section Sz5.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo NAME EB name slack ej fuel : ltac2:(SecDiet.SzSec.tyM 'open_offline_wtp_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL HAL FOPEN FCLOSE FOPEN_OFFLINE FMT GH"] Lemma open_offline_wtp_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'open_offline_wtp_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros PRE UC TR NF -> Ha2 Ha1 HNAME NNUL LEN FIRST NOK SLK N1 NLS N2 HEB E1 E8 D1.
    specialize (Ha1 eq_refl). cbv beta in Ha2. subst a1 a2.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    unfold PCAP_L4_STACK in BU. destruct TR as (TRF & TRFO & TRC & TRM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rng_sp_window RSTK sp RSPW.
    pose proof (bytes_at_bound _ _ _ _ HNAME) as BN. rewrite length_app in BN. cbn [length] in BN.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof (gl_stdin _ _ _ GL _ _ _ _ _ _ _ G) as (GOT1 & GOT2 & SUNP). unfold GOT_STDIN, STDIN_P, STDIN_FILE in GOT1, GOT2, SUNP.
    pose proof (proj1 E1) as EBL. pose proof (proj1 N1) as NML.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL) as (EBLO & EBHI). pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G NLS) as (NLO & NHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL ltac:(lia)) as EBBAND. pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G NLS ltac:(lia)) as NBAND.
    band_ind EBBAND bE. band_ind NBAND bN.
    pose proof N1 as N1e.
    destruct N1 as (_ & (N0 & N47 & NUNP & NRNG & NRSH & NAR & _)).
    (* [comment removed for export] *)
    destruct name as [|c0 name']; [cbn in LEN; lia|].
    (* [comment removed for export] *)
    assert (LENZ : (1 <= Z.of_nat (length (c0 :: name')) <= 4095)%Z) by (clear - LEN; lia).
    assert (LENh : hidc ((1 <= length (c0 :: name') <= 4095)%nat)) by exact LEN. clear LEN.
    assert (HNAME0 : bytes_at asegs m NAME ((c0 :: name') ++ [Z_to_bv 8 0])).
    { pose proof HNAME as X. change ((c0 :: name') ++ Z_to_bv 8 0 :: slack) with ((c0 :: name') ++ ([Z_to_bv 8 0] ++ slack)) in X.
      rewrite app_assoc in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X. exact (proj1 X). }
    unfold Pcap.pcap_open_offline, pcap_open_offline_with_tstamp_precision, errmsg_for_errno.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_fopen_r e_last_errno e_fclose prims]. unfold PCAP_OPEN_OFFLINE_WTP_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    assert (HNAMEe : hidc (bytes_at asegs m NAME ((c0 :: name') ++ Z_to_bv 8 0 :: slack))) by exact HNAME.
    assert (HEBe : hidc (rw_cells asegs m EB [CB 256 ej])) by exact HEB.
    clear HNAME HNAME0 HEB.
    ienterG. carve_frame 48%nat ST. do 9 zstep. if_false_by (eqz_false NAME ltac:(lia)).
    do 4 zstep.
    ck NUNP 1%Z 0x84d2c%Z [11%Z; 12%Z].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp - 48, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (HNAME1 : bytes_at asegs mm NAME ((c0 :: name') ++ Z_to_bv 8 0 :: slack))
        by (eapply agrees_bytes_at; [exact AG0 | exact HNAMEe | intros a Ha; rewrite length_app in Ha; cbn [length] in Ha; cbn [outside]; cbn [length] in NHI; lia]);
      assert (HR0 : ov_read_bytes asegs mm (wa (NAME + 0)) 1 = Some [c0])
        by (rewrite (bytes_at_read asegs mm NAME _ 0 1 HNAME1 ltac:(lia) ltac:(cbn; lia)); reflexivity);
      clear HNAME1
    end.
    assert (NE45 : negb (bv_eqb (Z_to_bv 64 (bv_unsigned c0)) (Z_to_bv 64 45)) = true).
    { unfold bv_eqb. pose proof (bv_unsigned_in_range 8 c0) as Hc. unfold bv_modulus in Hc. cbn in Hc.
      rewrite !unsigned_lit by lia. apply Bool.negb_true_iff, Z.eqb_neq. intros E. apply FIRST. cbn. f_equal. apply bv_eq. rewrite E. reflexivity. }
    do 3 zstep. rewrite NE45; cbv iota. do 4 zstep.
    (* [comment removed for export] *)
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FWS : Forall (client_ivA FL CL) [(bv_unsigned sp - 48, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (RB : bytes_at asegs mm 0x212e0 ([Z_to_bv 8 114; Z_to_bv 8 98] ++ [Z_to_bv 8 0]))
        by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x212e0 [Z_to_bv 8 114; Z_to_bv 8 98; Z_to_bv 8 0] ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))));
      assert (HNAME1 : bytes_at asegs mm NAME ((c0 :: name') ++ [Z_to_bv 8 0]))
        by (pose proof (agrees_bytes_at _ _ _ _ _ AGa HNAMEe ltac:(intros a Ha; eapply clocA_keeps; [exact NLS|]; rewrite length_app in Ha; cbn [length] in Ha |- *; lia)) as X;
            change ((c0 :: name') ++ Z_to_bv 8 0 :: slack) with ((c0 :: name') ++ ([Z_to_bv 8 0] ++ slack)) in X;
            rewrite app_assoc in X; apply (proj1 (bytes_at_app _ _ _ _ _)) in X; exact (proj1 X))
    end.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ N1e G0 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AGa) ltac:(lia)) as N1k.
    clear MU WM FWS G'.
    name_sp sp (-48)%Z.
    apply evtF_done. eapply implMG_bind.
    { eapply FOPEN with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (NAME := NAME) (MODE := 0x212e0%Z) (name := c0 :: name')
                        (md := [Z_to_bv 8 114; Z_to_bv 8 98]) (wr := false) (trC := []);
        [ | eapply (ucaller_data 0%nat _ _ _ _ _ 0x84d64%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | lia]
          | rewrite unsigned_lit by lia; exact TRF
          | reflexivity | reflexivity | exact HNAME1 | exact NNUL | exact LENh | exact NOK
          | apply cobjA_robjA; [exact N1k| lia] | exact RB | split; reflexivity
          | eapply (gia_global_robjA _ _ _ GL); [exact G0 | unfold client_globals; repeat (first [left; reflexivity | right]) | cbn; lia | exact RIMG | exact RISH] ].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    intros [f|] s' RNG1 ms' PO; cbv beta iota in PO.
    - (* [comment removed for export] *)
      destruct PO as (FP1 & av & m2 & E & OF1 & MI1 & ST1 & AG1 & (Af & -> & G1)).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 544100)) with (Z_to_bv 64 544100) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 ltac:(apply in_or_app; right; left; reflexivity)) as ((FBAND & _ & FTOP & _) & A1 & _).
      cbn [cb_addr cb_size fst snd] in FBAND, FTOP, A1. unfold FILE_BLOCK in FBAND, FTOP. pose proof (ablk_lin _ _ FBAND) as (AIMG & _). unfold AIMG_HI in AIMG. clear FBAND.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (AG02 : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
      { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
      assert (HEB2 : rw_cells asegs m2 EB [CB 256 ej]) by (eapply agrees_rw_cells; [exact AG02 | exact HEBe | intros a Ha; eapply clocA_keeps; [exact EBL|]; cbn [cells_size csize Nat.add] in Ha; lia]).
      pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ E1 G1 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AG02) ltac:(lia)) as E1k.
      clear MI G0 AGa RB HNAME1 N1k NUNP SUNP GOT SHB GOT1 GOT2 HR0.
      hide HEB2.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      ienterG. zstep. zstep. if_false_by (eqz_false Af ltac:(lia)). do 4 zstep.
      unhide HEB2.
      name_sp sp (-48)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply FOPEN_OFFLINE with (L := L) (s := s') (CL := CL) (FB := (f, Af, FILE_BLOCK) :: FB) (FL := FL) (lo := lo) (FA := Af) (EB := EB) (f := f) (ej := ej) (trC := []);
          [ split; [exact G1|]; split; [rewrite Hsp; exact ST1|]; split; [lia|]; split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | eapply (ucaller_data _ _ _ _ _ _ 0x84d7c%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold depth_fopen_offline; lia]
          | rewrite unsigned_lit by lia; exact TRFO
          | exact NF
          | left; reflexivity | reflexivity | reflexivity | reflexivity | exact HEB2 | exact E1k | exact E8 ]. }
      intros [msg|p] s'' RNG2 ms'' PO; unfold open_result_post in PO.
      + (* [comment removed for export] *)
        destruct PO as (FP2 & av2 & m3 & FB' & E & OF2 & MI2 & ST2 & AG2 & (junk' & -> & -> & G2 & HEB3 & LENM & RNGM)).
        unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 544124)) with (Z_to_bv 64 544124) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
        lazymatch type of FR with rw_cells _ _ ?A ?cs =>
          assert (FR2 : rw_cells asegs m3 A cs) by (eapply agrees_rw_cells; [exact AG2 | exact FR |]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]) end.
        clear FR MI1 HEB2 E1k.
        pose proof (gl_stdin _ _ _ GL _ _ _ _ _ _ _ G2) as (GOT1 & GOT2 & SUNP). unfold GOT_STDIN, STDIN_P, STDIN_FILE in GOT1, GOT2, SUNP.
        hide HEB3.
        pose proof (munch_refl ([] : list (Z * Z)) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
        ienterG. zstep. if_false. do 2 zstep.
        ck0 SUNP; ck_go.
        zstep. zstep. if_false_by (eqb_lits_false Af 0xa9ba0 ltac:(lia) ltac:(lia) ltac:(lia)). do 2 zstep.
        name_sp sp (-48)%Z.
        apply evtF_done. eapply implMG_bind.
        { eapply FCLOSE with (L := L) (s := s'') (CL := CL) (F1 := []) (F2 := FB) (FL := FL) (f := f) (Af := Af) (lo := lo) (trC := []);
            [ split; [exact G2|]; split; [rewrite Hsp; exact ST2|]; split; [lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
              split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
              split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
            | eapply (ucaller_data 0%nat _ _ _ _ _ 0x84da8%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | lia]
            | rewrite unsigned_lit by lia; exact TRC
            | reflexivity
            | eapply new_file_not_out; [exact G | exact G2 | congruence] ]. }
        intros [] s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & av3 & m4 & E & OF3 & MI3 & ST3 & AG3 & G3).
        unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 544168)) with (Z_to_bv 64 544168) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG3) in FR2; [|lia].
        unhide HEB3. assert (HEB4 : rw_cells asegs m4 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'])
          by (eapply agrees_rw_cells; [exact AG3 | exact HEB3 | intros a Ha; eapply clocA_keeps; [exact EBL|]; cbn [cells_size csize Nat.add] in Ha; lia]).
        clear HEB3 MI2 MU3 WM3.
        repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
        pose proof (munch_refl ([] : list (Z * Z)) m4) as MU4. pose proof (wmono_refl asegs m4) as WM4.
        apply implMG_ret. do 10 zstep.
        release_frame FR2 ST3 (bv_unsigned sp).
        apply evtF_done; subst POSTQ; unfold open_result_post.
        split; [eapply fp_le_trans; [exact FP1|]; eapply fp_le_trans; [exact FP2| exact FP3]|].
        lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
        split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
        split; [congruence|].
        split; [assumption|]. split; [assumption|].
        split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG02| intros a [K _]; exact K]|]. eapply agrees_on_trans.
                 - eapply agrees_on_weaken; [exact AG2|]. intros a [K N]. split; [|exact N].
                   destruct K as [K|K]; [left; lia| right; exact K].
                 - eapply agrees_on_weaken; [exact AG3|]. intros a [K _]. destruct K as [K|K]; [left; lia| right; exact K]. }
        exists junk'. split; [reflexivity|]. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB4|]. split; [exact LENM| exact RNGM].
      + (* [comment removed for export] *)
        destruct PO as (FP2 & av2 & m3 & FB' & E & OF2 & MI2 & ST2 & AG2 & (P & PB & -> & [-> ERF] & G2 & PC2 & HEB3)).
        unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 544124)) with (Z_to_bv 64 544124) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
        lazymatch type of FR with rw_cells _ _ ?A ?cs =>
          assert (FR2 : rw_cells asegs m3 A cs) by (eapply agrees_rw_cells; [exact AG2 | exact FR |]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]) end.
        clear FR MI1 HEB2 E1k.
        pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; apply in_or_app; right; exact (PCAPR_self_in _ _ _ _ _ PC2))) as ((_ & _ & PTOP & _) & P0 & _).
        cbn [cb_addr cb_size fst snd] in P0, PTOP.
        destruct HEB3 as [e3 HEB3]. hide HEB3. hide PC2.
        pose proof (munch_refl ([] : list (Z * Z)) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
        apply implMG_ret. zstep. if_true_by (nez_true P ltac:(pose proof (psize_pos p); lia)). do 8 zstep.
        release_frame FR2 ST2 (bv_unsigned sp).
        unhide HEB3. unhide PC2.
        apply evtF_done; subst POSTQ; unfold open_result_post.
        split; [eapply fp_le_trans; [exact FP1| exact FP2]|].
        lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 P), mm, ((f, Af, FILE_BLOCK) :: FB) end.
        split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
        split; [congruence|].
        split; [assumption|]. split; [assumption|].
        split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG02| intros a [K _]; exact K]|].
                 eapply agrees_on_weaken; [exact AG2|]. intros a [K N]. split; [|exact N]. destruct K as [K|K]; [left; lia| right; exact K]. }
        exists P, PB. split; [reflexivity|]. split; [exists Af; rewrite ERF; reflexivity|]. split; [exact G2|]. split; [exact PC2| exists e3; exact HEB3].
    - (* [comment removed for export] *)
      destruct PO as (FP1 & av & m2 & E & OF1 & MI1 & ST1 & AG1 & -> & G1 & EN2 & ER).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 544100)) with (Z_to_bv 64 544100) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (AG02 : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
      { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
      assert (HEB2 : rw_cells asegs m2 EB [CB 256 ej]) by (eapply agrees_rw_cells; [exact AG02 | exact HEBe | intros a Ha; eapply clocA_keeps; [exact EBL|]; cbn [cells_size csize Nat.add] in Ha; lia]).
      assert (HNAME2 : bytes_at asegs m2 NAME ((c0 :: name') ++ Z_to_bv 8 0 :: slack))
        by (eapply agrees_bytes_at; [exact AG02 | exact HNAMEe | intros a Ha; eapply clocA_keeps; [exact NLS|]; rewrite length_app in Ha; cbn [length] in Ha |- *; lia]).
      pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ E1 G1 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AG02) ltac:(lia)) as E1k.
      pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ N1e G1 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AG02) ltac:(lia)) as N1k2.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G1 RTLS) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m2 0x21300 "%s"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m2 0x21300 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "%s"%string) ++ [Z_to_bv 8 0])
                                 MI1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      clear MI G0 AGa RB HNAME1 N1k NUNP SUNP GOT SHB GOT1 GOT2 HR0.
      apply implMG_errno_ll. set (e := lc_errno (ps_libc s')) in *. rewrite (cstr_no_nul _ NNUL).
      hide HEB2. hide HNAME2.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      ienterG. zstep. zstep. if_true.
      zstep. do 3 zstep. rewrite ETP.
      ck TUNP 4%Z 0x84dd8%Z [11%Z; 12%Z].
      zstep.
      do 5 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      unhide HEB2. unhide HNAME2.
      name_sp sp (-48)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply FMT with (L := L) (s := s') (CL := CL) (FB := FB) (FL := FL) (lo := lo) (EB := EB) (FMTA := 0x21300%Z) (e := e) (fs := "%s"%string)
                        (args := [AStr (map bv_unsigned (c0 :: name'))]) (junk := ej);
          [ split; [exact G1|]; split; [rewrite Hsp; exact ST1|]; split; [lia|]; split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | apply NF; unfold frames_open_offline, frames_open_offline_wtp; cbn; tauto
          | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia
          | cbn [length firstn]; constructor; [|constructor]; cbn [farg_word]; exists NAME, (c0 :: name'), slack;
            split; [reflexivity|]; split; [exact HNAME2|]; split; [exact NNUL|]; split; [reflexivity|]; split; [cbn [length] in *; lia|];
            split; [exact SLK|]; split; [clear - D1; cbn [length] in *; lia|]; split; [left; exact NLS|];
            split; [apply aobjA_mobjA; [exact (proj2 N1k2)| lia]| exact N2]
          | exact HEB2 | exact E1k | exact E8 ]. }
      intros r sF RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & -> & PO). destruct_exs PO.
      destruct PO as (-> & OF3 & LC3 & TL3 & MI3 & ST3 & AG3 & G3 & HEB3).
      rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 544244)) with (Z_to_bv 64 544244) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      lazymatch type of FR with rw_cells _ _ ?A ?cs =>
        lazymatch type of AG3 with agrees_on _ _ ?mm =>
          assert (FR3 : rw_cells asegs mm A cs) by (eapply agrees_rw_cells; [exact AG3 | exact FR |]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]) end end.
      clear FR MI1 MU WM. hide HEB3.
      repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      lazymatch type of AG3 with agrees_on _ _ ?mm => pose proof (munch_refl ([] : list (Z * Z)) mm) as MU; pose proof (wmono_refl asegs mm) as WM end.
      apply implMG_ret. do 9 zstep.
      release_frame FR3 ST3 (bv_unsigned sp). unhide HEB3.
      apply evtF_done; subst POSTQ; unfold open_result_post.
      split; [eapply fp_le_trans; [exact FP1| exact FP3]|].
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [congruence|].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG02| intros a [K _]; exact K]|].
               eapply agrees_on_weaken; [exact AG3|]. intros a [K N]. split; [|exact N]. destruct K as [K|K]; [left; lia| right; exact K]. }
      eexists. split; [reflexivity|]. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB3|].
      split; [pose proof (fmt_errmsg_length "%s"%string [AStr (map bv_unsigned (c0 :: name'))] e); lia|].
      apply fmt_errmsg_ok; [vm_compute; reflexivity| apply args_ok_str1; exact NNUL].
  Qed.
  End Sz5.
  #[using="fflagA GL HAL FOPEN FCLOSE FOPEN_OFFLINE FMT GH"] Theorem open_offline_wtp_proofA : ltac:(let t := eval cbv delta [open_offline_wtp_proofA__stmt] in open_offline_wtp_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo NAME EB name slack ej fuel. ltac2:(SecDiet.SzSec.closeP 'open_offline_wtp_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="fflagA GL HAL FOPEN FCLOSE FOPEN_OFFLINE FMT GH"] Theorem open_offline_proofA : pcap_open_offline_stmt HO FO sites GIOA TP.
  Proof.
    red. intros until fuel. intros PRE UC TR NF -> Ha1 _ HNAME NNUL LEN FIRST NOK SLK N1 NLS N2 HEB E1 E8 D1. cbv beta in Ha1. subst a1.
    unfold PCAP_OPEN_OFFLINE_ENTRY. apply implMG_from_evtF. do 3 zstep. apply evtF_done.
    eapply open_offline_wtp_proofA; [exact PRE | exact UC | exact TR | exact NF | reflexivity | reflexivity | intros _; reflexivity | exact HNAME | exact NNUL | exact LEN | exact FIRST
                                    | exact NOK | exact SLK | exact N1 | exact NLS | exact N2 | exact HEB | exact E1 | exact E8 | exact D1].
  Qed.
End Open.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Definition fmt_errmsg_length__stmt : Prop := forall f args e, (length (fmt_errmsg f args e) <= 255)%nat.
Section Sz1.
Variables f args e : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_length__stmt "vvv" @f).
#[using="Type"] Lemma fmt_errmsg_length__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_length__stmt "vvv").
Proof.
 unfold fmt_errmsg, snprintf, snprintf_out, PCAP_ERRBUF_SIZE, zlength.
  set (mm := firstn (Z.to_nat (256 - 1)) (fmt_output (fmt f) args)).
  assert (Hm : (length mm <= 255)%nat) by (subst mm; rewrite length_firstn; apply Nat.le_min_l).
  destruct (256 <? Z.of_nat (length mm) + 3)%Z eqn:E; [exact Hm|].
  apply Z.ltb_ge in E. rewrite !length_app, length_firstn. cbn [length str String.list_ascii_of_string map].
  unfold str. cbn [String.list_ascii_of_string map length]. lia.
Qed.
End Sz1.
Lemma fmt_errmsg_length : ltac:(let t := eval cbv delta [fmt_errmsg_length__stmt] in fmt_errmsg_length__stmt in exact t).
Proof. intros f args e. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_length__body "vvv"). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Open.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FOPEN_OFFLINE : fopen_offline_stmt HO FO sites GIOA TP.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis GH : gia_harn_laws GIOA.

  (* [comment removed for export] *)
  Definition new_file_not_out__stmt : Prop := forall L RNG s CL FB FL m L2 RNG2 s2 CL2 FL2 m2 f Af,
    GIOA L RNG s CL FB FL m -> GIOA L2 RNG2 s2 CL2 ((f, Af, FILE_BLOCK) :: FB) FL2 m2 -> ps_outfile s2 = ps_outfile s -> ps_outfile s2 <> Some f.
  Section Sz2.
  Variables L RNG s CL FB FL m L2 RNG2 s2 CL2 FL2 m2 f Af : ltac2:(SecDiet.SzSec.tyM 'new_file_not_out__stmt "vvvvvvvvvvvvvvv" @L).
  #[using="rc tlsI HO FO fflagA GL HAL GH"] Lemma new_file_not_out__body : ltac2:(SecDiet.SzSec.bodyP 'new_file_not_out__stmt "vvvvvvvvvvvvvvv").
  Proof.
    intros G G2 EO HO2.
 rewrite EO in HO2.
    pose proof (gh_outfile _ GH _ _ _ _ _ _ _ G) as GO. rewrite HO2 in GO. destruct GO as (A & HinA & _).
    assert (E1 : blk_addr HO s2 f = Af) by (exact (HAL _ _ _ _ _ _ _ (f, Af, FILE_BLOCK) G2 ltac:(apply in_or_app; right; left; reflexivity))).
    assert (E2 : blk_addr HO s2 f = A) by (exact (HAL _ _ _ _ _ _ _ (f, A, FILE_BLOCK) G2 ltac:(apply in_or_app; right; right; exact HinA))).
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G2) as BA. apply blocks_apart_app_inv in BA as (_ & BA & _).
    cbn [blocks_apart] in BA. destruct BA as [FA _]. pose proof (proj1 (Forall_forall _ _) FA _ HinA) as AP.
    unfold apart, cb_addr, cb_size, FILE_BLOCK in AP. cbn [fst snd] in AP. lia.
  Qed.
  End Sz2.
  #[using="rc tlsI HO FO fflagA GL HAL GH"] Lemma new_file_not_out : ltac:(let t := eval cbv delta [new_file_not_out__stmt] in new_file_not_out__stmt in exact t).
  Proof. intros L RNG s CL FB FL m L2 RNG2 s2 CL2 FL2 m2 f Af. ltac2:(SecDiet.SzSec.closeP 'new_file_not_out__body "vvvvvvvvvvvvvvv"). Qed.

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  #[using="Type"] Lemma cstr_no_nul : forall (bs : list byte), ~ In (Z_to_bv 8 0) bs -> cstr (map bv_unsigned bs) = map bv_unsigned bs.
  Proof.
    induction bs as [|b bs IH]; intros Hn; [reflexivity|]. cbn [map cstr].
    destruct (bv_unsigned b =? 0)%Z eqn:E.
    - exfalso. apply Hn. left. apply Z.eqb_eq in E. apply bv_eq. rewrite E. reflexivity.
    - f_equal. apply IH. intros Hin. apply Hn. right. exact Hin.
  Qed.

  (* [comment removed for export] *)
  Definition open_offline_wtp_proofA__stmt : Prop := pcap_open_offline_wtp_stmt HO FO sites GIOA TP.
  Section Sz5.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo NAME EB name slack ej fuel : ltac2:(SecDiet.SzSec.tyM 'open_offline_wtp_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL HAL FOPEN FCLOSE FOPEN_OFFLINE FMT GH"] Lemma open_offline_wtp_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'open_offline_wtp_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR NF -> Ha2 Ha1 HNAME NNUL LEN FIRST NOK SLK N1 NLS N2 HEB E1 E8 D1.
    specialize (Ha1 eq_refl). cbv beta in Ha2. subst a1 a2.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    unfold PCAP_L4_STACK in BU. destruct TR as (TRF & TRFO & TRC & TRM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rng_sp_window RSTK sp RSPW.
    pose proof (bytes_at_bound _ _ _ _ HNAME) as BN. rewrite length_app in BN. cbn [length] in BN.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof (gl_stdin _ _ _ GL _ _ _ _ _ _ _ G) as (GOT1 & GOT2 & SUNP). unfold GOT_STDIN, STDIN_P, STDIN_FILE in GOT1, GOT2, SUNP.
    pose proof (proj1 E1) as EBL. pose proof (proj1 N1) as NML.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL) as (EBLO & EBHI). pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G NLS) as (NLO & NHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL ltac:(lia)) as EBBAND. pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G NLS ltac:(lia)) as NBAND.
    band_ind EBBAND bE. band_ind NBAND bN.
    pose proof N1 as N1e.
    destruct N1 as (_ & (N0 & N47 & NUNP & NRNG & NRSH & NAR & _)).
    (* [comment removed for export] *)
    destruct name as [|c0 name']; [cbn in LEN; lia|].
    (* [comment removed for export] *)
    assert (LENZ : (1 <= Z.of_nat (length (c0 :: name')) <= 4095)%Z) by (clear - LEN; lia).
    assert (LENh : hidc ((1 <= length (c0 :: name') <= 4095)%nat)) by exact LEN. clear LEN.
    assert (HNAME0 : bytes_at asegs m NAME ((c0 :: name') ++ [Z_to_bv 8 0])).
    { pose proof HNAME as X. change ((c0 :: name') ++ Z_to_bv 8 0 :: slack) with ((c0 :: name') ++ ([Z_to_bv 8 0] ++ slack)) in X.
      rewrite app_assoc in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X. exact (proj1 X). }
    unfold Pcap.pcap_open_offline, pcap_open_offline_with_tstamp_precision, errmsg_for_errno.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_fopen_r e_last_errno e_fclose prims]. unfold PCAP_OPEN_OFFLINE_WTP_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    assert (HNAMEe : hidc (bytes_at asegs m NAME ((c0 :: name') ++ Z_to_bv 8 0 :: slack))) by exact HNAME.
    assert (HEBe : hidc (rw_cells asegs m EB [CB 256 ej])) by exact HEB.
    clear HNAME HNAME0 HEB.
    ienterG. carve_frame 48%nat ST. do 9 zstep. if_false_by (eqz_false NAME ltac:(lia)).
    do 4 zstep.
    ck NUNP 1%Z 0x84dc8%Z [11%Z; 12%Z].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp - 48, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      assert (HNAME1 : bytes_at asegs mm NAME ((c0 :: name') ++ Z_to_bv 8 0 :: slack))
        by (eapply agrees_bytes_at; [exact AG0 | exact HNAMEe | intros a Ha; rewrite length_app in Ha; cbn [length] in Ha; cbn [outside]; cbn [length] in NHI; lia]);
      assert (HR0 : ov_read_bytes asegs mm (wa (NAME + 0)) 1 = Some [c0])
        by (rewrite (bytes_at_read asegs mm NAME _ 0 1 HNAME1 ltac:(lia) ltac:(cbn; lia)); reflexivity);
      clear HNAME1
    end.
    assert (NE45 : negb (bv_eqb (Z_to_bv 64 (bv_unsigned c0)) (Z_to_bv 64 45)) = true).
    { unfold bv_eqb. pose proof (bv_unsigned_in_range 8 c0) as Hc. unfold bv_modulus in Hc. cbn in Hc.
      rewrite !unsigned_lit by lia. apply Bool.negb_true_iff, Z.eqb_neq. intros E. apply FIRST. cbn. f_equal. apply bv_eq. rewrite E. reflexivity. }
    do 3 zstep. rewrite NE45; cbv iota. do 4 zstep.
    (* [comment removed for export] *)
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FWS : Forall (client_ivA FL CL) [(bv_unsigned sp - 48, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (RB : bytes_at asegs mm 0x212e0 ([Z_to_bv 8 114; Z_to_bv 8 98] ++ [Z_to_bv 8 0]))
        by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x212e0 [Z_to_bv 8 114; Z_to_bv 8 98; Z_to_bv 8 0] ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))));
      assert (HNAME1 : bytes_at asegs mm NAME ((c0 :: name') ++ [Z_to_bv 8 0]))
        by (pose proof (agrees_bytes_at _ _ _ _ _ AGa HNAMEe ltac:(intros a Ha; eapply clocA_keeps; [exact NLS|]; rewrite length_app in Ha; cbn [length] in Ha |- *; lia)) as X;
            change ((c0 :: name') ++ Z_to_bv 8 0 :: slack) with ((c0 :: name') ++ ([Z_to_bv 8 0] ++ slack)) in X;
            rewrite app_assoc in X; apply (proj1 (bytes_at_app _ _ _ _ _)) in X; exact (proj1 X))
    end.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ N1e G0 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AGa) ltac:(lia)) as N1k.
    clear MU WM FWS G'.
    name_sp sp (-48)%Z.
    apply evtF_done. eapply implMG_bind.
    { eapply FOPEN with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (NAME := NAME) (MODE := 0x212e0%Z) (name := c0 :: name')
                        (md := [Z_to_bv 8 114; Z_to_bv 8 98]) (wr := false) (trC := []);
        [ | eapply (ucaller_data 0%nat _ _ _ _ _ 0x84e08%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | lia]
          | rewrite unsigned_lit by lia; exact TRF
          | reflexivity | reflexivity | exact HNAME1 | exact NNUL | exact LENh | exact NOK
          | apply cobjA_robjA; [exact N1k| lia] | exact RB | split; reflexivity
          | eapply (gia_global_robjA _ _ _ GL); [exact G0 | unfold client_globals; repeat (first [left; reflexivity | right]) | cbn; lia | exact RIMG | exact RISH] ].
      split; [exact G0|]. split; [rewrite Hsp; exact ST|]. split; [lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    intros [f|] s' RNG1 ms' PO; cbv beta iota in PO.
    - (* [comment removed for export] *)
      destruct PO as (FP1 & av & m2 & E & OF1 & MI1 & ST1 & AG1 & (Af & -> & G1)).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 544264)) with (Z_to_bv 64 544264) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 ltac:(apply in_or_app; right; left; reflexivity)) as ((FBAND & _ & FTOP & _) & A1 & _).
      cbn [cb_addr cb_size fst snd] in FBAND, FTOP, A1. unfold FILE_BLOCK in FBAND, FTOP. pose proof (ablk_lin _ _ FBAND) as (AIMG & _). unfold AIMG_HI in AIMG. clear FBAND.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (AG02 : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
      { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
      assert (HEB2 : rw_cells asegs m2 EB [CB 256 ej]) by (eapply agrees_rw_cells; [exact AG02 | exact HEBe | intros a Ha; eapply clocA_keeps; [exact EBL|]; cbn [cells_size csize Nat.add] in Ha; lia]).
      pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ E1 G1 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AG02) ltac:(lia)) as E1k.
      clear MI G0 AGa RB HNAME1 N1k NUNP SUNP GOT SHB GOT1 GOT2 HR0.
      hide HEB2.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      ienterG. zstep. zstep. if_false_by (eqz_false Af ltac:(lia)). do 4 zstep.
      unhide HEB2.
      name_sp sp (-48)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply FOPEN_OFFLINE with (L := L) (s := s') (CL := CL) (FB := (f, Af, FILE_BLOCK) :: FB) (FL := FL) (lo := lo) (FA := Af) (EB := EB) (f := f) (ej := ej) (trC := []);
          [ split; [exact G1|]; split; [rewrite Hsp; exact ST1|]; split; [lia|]; split; [unfold PCAP_L3_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | eapply (ucaller_data _ _ _ _ _ _ 0x84e20%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold depth_fopen_offline; lia]
          | rewrite unsigned_lit by lia; exact TRFO
          | exact NF
          | left; reflexivity | reflexivity | reflexivity | reflexivity | exact HEB2 | exact E1k | exact E8 ]. }
      intros [msg|p] s'' RNG2 ms'' PO; unfold open_result_post in PO.
      + (* [comment removed for export] *)
        destruct PO as (FP2 & av2 & m3 & FB' & E & OF2 & MI2 & ST2 & AG2 & (junk' & -> & -> & G2 & HEB3 & LENM & RNGM)).
        unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 544288)) with (Z_to_bv 64 544288) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
        lazymatch type of FR with rw_cells _ _ ?A ?cs =>
          assert (FR2 : rw_cells asegs m3 A cs) by (eapply agrees_rw_cells; [exact AG2 | exact FR |]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]) end.
        clear FR MI1 HEB2 E1k.
        pose proof (gl_stdin _ _ _ GL _ _ _ _ _ _ _ G2) as (GOT1 & GOT2 & SUNP). unfold GOT_STDIN, STDIN_P, STDIN_FILE in GOT1, GOT2, SUNP.
        hide HEB3.
        pose proof (munch_refl ([] : list (Z * Z)) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
        ienterG. zstep. if_false. do 2 zstep.
        ck0 SUNP; ck_go.
        zstep. zstep. if_false_by (eqb_lits_false Af 0xa9f80 ltac:(lia) ltac:(lia) ltac:(lia)). do 2 zstep.
        name_sp sp (-48)%Z.
        apply evtF_done. eapply implMG_bind.
        { eapply FCLOSE with (L := L) (s := s'') (CL := CL) (F1 := []) (F2 := FB) (FL := FL) (f := f) (Af := Af) (lo := lo) (trC := []);
            [ split; [exact G2|]; split; [rewrite Hsp; exact ST2|]; split; [lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
              split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
              split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
            | eapply (ucaller_data 0%nat _ _ _ _ _ 0x84e4c%Z); [rewrite Hsp, unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | lia]
            | rewrite unsigned_lit by lia; exact TRC
            | reflexivity
            | eapply new_file_not_out; [exact G | exact G2 | congruence] ]. }
        intros [] s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & av3 & m4 & E & OF3 & MI3 & ST3 & AG3 & G3).
        unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 544332)) with (Z_to_bv 64 544332) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG3) in FR2; [|lia].
        unhide HEB3. assert (HEB4 : rw_cells asegs m4 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'])
          by (eapply agrees_rw_cells; [exact AG3 | exact HEB3 | intros a Ha; eapply clocA_keeps; [exact EBL|]; cbn [cells_size csize Nat.add] in Ha; lia]).
        clear HEB3 MI2 MU3 WM3.
        repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
        pose proof (munch_refl ([] : list (Z * Z)) m4) as MU4. pose proof (wmono_refl asegs m4) as WM4.
        apply implMG_ret. do 10 zstep.
        release_frame FR2 ST3 (bv_unsigned sp).
        apply evtF_done; subst POSTQ; unfold open_result_post.
        split; [eapply fp_le_trans; [exact FP1|]; eapply fp_le_trans; [exact FP2| exact FP3]|].
        lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
        split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
        split; [congruence|].
        split; [assumption|]. split; [assumption|].
        split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG02| intros a [K _]; exact K]|]. eapply agrees_on_trans.
                 - eapply agrees_on_weaken; [exact AG2|]. intros a [K N]. split; [|exact N].
                   destruct K as [K|K]; [left; lia| right; exact K].
                 - eapply agrees_on_weaken; [exact AG3|]. intros a [K _]. destruct K as [K|K]; [left; lia| right; exact K]. }
        exists junk'. split; [reflexivity|]. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB4|]. split; [exact LENM| exact RNGM].
      + (* [comment removed for export] *)
        destruct PO as (FP2 & av2 & m3 & FB' & E & OF2 & MI2 & ST2 & AG2 & (P & PB & -> & [-> ERF] & G2 & PC2 & HEB3)).
        unfold hpost_regs in E. destruct_exs E. subst ms''. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 544288)) with (Z_to_bv 64 544288) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
        lazymatch type of FR with rw_cells _ _ ?A ?cs =>
          assert (FR2 : rw_cells asegs m3 A cs) by (eapply agrees_rw_cells; [exact AG2 | exact FR |]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]) end.
        clear FR MI1 HEB2 E1k.
        pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; apply in_or_app; right; exact (PCAPR_self_in _ _ _ _ _ PC2))) as ((_ & _ & PTOP & _) & P0 & _).
        cbn [cb_addr cb_size fst snd] in P0, PTOP.
        destruct HEB3 as [e3 HEB3]. hide HEB3. hide PC2.
        pose proof (munch_refl ([] : list (Z * Z)) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
        apply implMG_ret. zstep. if_true_by (nez_true P ltac:(pose proof (psize_pos p); lia)). do 8 zstep.
        release_frame FR2 ST2 (bv_unsigned sp).
        unhide HEB3. unhide PC2.
        apply evtF_done; subst POSTQ; unfold open_result_post.
        split; [eapply fp_le_trans; [exact FP1| exact FP2]|].
        lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 P), mm, ((f, Af, FILE_BLOCK) :: FB) end.
        split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
        split; [congruence|].
        split; [assumption|]. split; [assumption|].
        split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG02| intros a [K _]; exact K]|].
                 eapply agrees_on_weaken; [exact AG2|]. intros a [K N]. split; [|exact N]. destruct K as [K|K]; [left; lia| right; exact K]. }
        exists P, PB. split; [reflexivity|]. split; [exists Af; rewrite ERF; reflexivity|]. split; [exact G2|]. split; [exact PC2| exists e3; exact HEB3].
    - (* [comment removed for export] *)
      destruct PO as (FP1 & av & m2 & E & OF1 & MI1 & ST1 & AG1 & -> & G1 & EN2 & ER).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 544264)) with (Z_to_bv 64 544264) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
      apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia].
      assert (AG02 : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
      { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
      assert (HEB2 : rw_cells asegs m2 EB [CB 256 ej]) by (eapply agrees_rw_cells; [exact AG02 | exact HEBe | intros a Ha; eapply clocA_keeps; [exact EBL|]; cbn [cells_size csize Nat.add] in Ha; lia]).
      assert (HNAME2 : bytes_at asegs m2 NAME ((c0 :: name') ++ Z_to_bv 8 0 :: slack))
        by (eapply agrees_bytes_at; [exact AG02 | exact HNAMEe | intros a Ha; eapply clocA_keeps; [exact NLS|]; rewrite length_app in Ha; cbn [length] in Ha |- *; lia]).
      pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ E1 G1 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AG02) ltac:(lia)) as E1k.
      pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ N1e G1 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AG02) ltac:(lia)) as N1k2.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G1 RTLS) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m2 0x21300 "%s"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m2 0x21300 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "%s"%string) ++ [Z_to_bv 8 0])
                                 MI1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      clear MI G0 AGa RB HNAME1 N1k NUNP SUNP GOT SHB GOT1 GOT2 HR0.
      apply implMG_errno_ll. set (e := lc_errno (ps_libc s')) in *. rewrite (cstr_no_nul _ NNUL).
      hide HEB2. hide HNAME2.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      ienterG. zstep. zstep. if_true.
      zstep. do 3 zstep. rewrite ETP.
      (* [comment removed for export] *)
      pose proof ATPv_pg as TPG. pose proof atp_lin as ((TPLO & _) & _).
      assert (ERN : (0 < ATP + -164 < 2^64)%Z) by (unfold ATP; atop_facts; lia).
      zstep. if_false_by (eqz_false (ATP + -164) ERN).
      zstep. replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
      zstep. if_false.
      ck TUNP 4%Z 0x84e88%Z [11%Z; 12%Z].
      zstep.
      do 5 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      unhide HEB2. unhide HNAME2.
      name_sp sp (-48)%Z.
      apply evtF_done. eapply implMG_bind.
      { eapply FMT with (L := L) (s := s') (CL := CL) (FB := FB) (FL := FL) (lo := lo) (EB := EB) (FMTA := 0x21300%Z) (e := e) (fs := "%s"%string)
                        (args := [AStr (map bv_unsigned (c0 :: name'))]) (junk := ej);
          [ split; [exact G1|]; split; [rewrite Hsp; exact ST1|]; split; [lia|]; split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|];
            split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | apply NF; unfold frames_open_offline, frames_open_offline_wtp; cbn; tauto
          | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia
          | cbn [length firstn]; constructor; [|constructor]; cbn [farg_word]; exists NAME, (c0 :: name'), slack;
            split; [reflexivity|]; split; [exact HNAME2|]; split; [exact NNUL|]; split; [reflexivity|]; split; [cbn [length] in *; lia|];
            split; [exact SLK|]; split; [clear - D1; cbn [length] in *; lia|]; split; [left; exact NLS|];
            split; [apply aobjA_mobjA; [exact (proj2 N1k2)| lia]| exact N2]
          | exact HEB2 | exact E1k | exact E8 ]. }
      intros r sF RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & -> & PO). destruct_exs PO.
      destruct PO as (-> & OF3 & LC3 & TL3 & MI3 & ST3 & AG3 & G3 & HEB3).
      rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 544420)) with (Z_to_bv 64 544420) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      lazymatch type of FR with rw_cells _ _ ?A ?cs =>
        lazymatch type of AG3 with agrees_on _ _ ?mm =>
          assert (FR3 : rw_cells asegs mm A cs) by (eapply agrees_rw_cells; [exact AG3 | exact FR |]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]) end end.
      clear FR MI1 MU WM. hide HEB3.
      repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      lazymatch type of AG3 with agrees_on _ _ ?mm => pose proof (munch_refl ([] : list (Z * Z)) mm) as MU; pose proof (wmono_refl asegs mm) as WM end.
      apply implMG_ret. do 9 zstep.
      release_frame FR3 ST3 (bv_unsigned sp). unhide HEB3.
      apply evtF_done; subst POSTQ; unfold open_result_post.
      split; [eapply fp_le_trans; [exact FP1| exact FP3]|].
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [congruence|].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG02| intros a [K _]; exact K]|].
               eapply agrees_on_weaken; [exact AG3|]. intros a [K N]. split; [|exact N]. destruct K as [K|K]; [left; lia| right; exact K]. }
      eexists. split; [reflexivity|]. split; [reflexivity|]. split; [exact G3|]. split; [exact HEB3|].
      split; [pose proof (fmt_errmsg_length "%s"%string [AStr (map bv_unsigned (c0 :: name'))] e); lia|].
      apply fmt_errmsg_ok; [vm_compute; reflexivity| apply args_ok_str1; exact NNUL].
  Qed.
  End Sz5.
  #[using="fflagA GL HAL FOPEN FCLOSE FOPEN_OFFLINE FMT GH"] Theorem open_offline_wtp_proofA : ltac:(let t := eval cbv delta [open_offline_wtp_proofA__stmt] in open_offline_wtp_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo NAME EB name slack ej fuel. ltac2:(SecDiet.SzSec.closeP 'open_offline_wtp_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="fflagA GL HAL FOPEN FCLOSE FOPEN_OFFLINE FMT GH"] Theorem open_offline_proofA : pcap_open_offline_stmt HO FO sites GIOA TP.
  Proof.
    red. intros until fuel. intros PRE UC TR NF -> Ha1 _ HNAME NNUL LEN FIRST NOK SLK N1 NLS N2 HEB E1 E8 D1. cbv beta in Ha1. subst a1.
    unfold PCAP_OPEN_OFFLINE_ENTRY. apply implMG_from_evtF. do 3 zstep. apply evtF_done.
    eapply open_offline_wtp_proofA; [exact PRE | exact UC | exact TR | exact NF | reflexivity | reflexivity | intros _; reflexivity | exact HNAME | exact NNUL | exact LEN | exact FIRST
                                    | exact NOK | exact SLK | exact N1 | exact NLS | exact N2 | exact HEB | exact E1 | exact E8 | exact D1].
  Qed.
End Open.
End CANSEC1.
End TwB.
End F_pcap_open2A.

(* [comment removed for export] *)
Module F_ngblk_failA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_exitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.


Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section RbFail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.

  (* [comment removed for export] *)
  Definition rb_exit_m1__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 sp0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 : word)
      (scs ccs' : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej junk'' : list byte) (msg : list Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 88%nat ->
    rb_handle p p' s P B' mm ->
    rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''] ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    rw_cells asegs mm CUR ccs' -> cells_size ccs' = 24%nat ->
    implMG RNGx (fo_ret FO _ FF_READ_BLOCK (RB_Err msg p')) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r21 r22 r23 r24 r25 r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bdac) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 sp0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej junk'' msg : ltac2:(SecDiet.SzSec.tyM 'rb_exit_m1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_exit_m1__body : ltac2:(SecDiet.SzSec.bodyP 'rb_exit_m1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET.
 intros CTX INV FRA Hscs HDL HEB LM MOK HCUR Hccs.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep.
    apply evtF_done. subst POSTQ.
    eapply (rb_exit FO GIOA TP fflagA GL GPL FRET) with (p := p) (p' := p') (B' := B') (scs := scs);
      [ exact CTX | exact INV | exact FRA | exact Hscs | exact HDL |].
    cbn [rb_result]. split; [reflexivity|]. split; [reflexivity|]. split; [exists junk''; exact HEB|]. split; [exact LM|]. split; [exact MOK|].
    exists ccs'. split; [exact HCUR| exact Hccs].
  Qed.
  End Sz1.
  Lemma rb_exit_m1 : ltac:(let t := eval cbv delta [rb_exit_m1__stmt] in rb_exit_m1__stmt in exact t).
  Proof using GL GPL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 sp0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej junk'' msg. ltac2:(SecDiet.SzSec.closeP 'rb_exit_m1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition rb_ret_ok (pc : Z) : Prop := (pc = 0x8bdac \/ pc = 0x8bd88 \/ pc = 0x8bd68)%Z.

  (* [comment removed for export] *)
  Definition rb_snp__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (t0 t1 t2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 : word)
      (scs ccs' : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej ej' : list byte)
      (pc FMTA : Z) (fs : string) (args : list farg),
    rb_ret_ok pc ->
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 88%nat ->
    rb_handle p p' s P B' mm ->
    rw_cells asegs mm EB [CB 256 ej'] -> rw_cells asegs mm CUR ccs' -> cells_size ccs' = 24%nat ->
    fmt_at mm FMTA fs -> fmt_ok fs args = true -> (length args <= 2)%nat ->
    Forall2 (farg_word true L RNGx ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) SPA EB 256 mm) args (firstn (length args) [a3; a4]) ->
    Forall (fun z => 0 < z < 256)%Z (Fmt.snprintf 256 fs args) ->
    implMG RNGx (fo_ret FO _ FF_READ_BLOCK (RB_Err (Fmt.snprintf 256 fs args) p')) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r21 r22 r23 r24 r25 r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 SNPRINTF_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm t0 t1 t2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej ej' pc FMTA fs args : ltac2:(SecDiet.SzSec.tyM 'rb_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_snp__body : ltac2:(SecDiet.SzSec.bodyP 'rb_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET SNPRINTF.
 intros ROK CTX INV FRA Hscs HDL HEB HCUR Hccs FMT5 FOK LA FWA MOK.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p')%Z) by lia.
    rb_setup GL CTX INV AL0.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply SNPRINTF with (L := L) (s := sx) (CL := (C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) (FB := FB) (FL := (FF_READ_BLOCK, Fb, 64%Z) :: FL) (lo := lo)
                             (DST := EB) (n := 256%Z) (FMTA := FMTA) (fs := fs) (args := args) (junk := ej');
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | lia
        | rewrite Hspa; replace (firstn (length args) [a3; a4; a5]) with (firstn (length args) [a3; a4])
            by (clear - LA; destruct args as [|? [|? [|? ?]]]; cbn in LA |- *; first [reflexivity | lia]); exact FWA
        | exact HEB | exact OEB ]
      | ].
    cbv beta; intros ms' PO; destruct PO as (vav5 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
    unfold STDIO_STACK in MU6.
    assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p', B', pc_bufalloc p')] (bv_unsigned sp)) [(SPA - 16384, SPA)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    assert (FX : Forall (cobj_iv FL (C1 ++ C2)) [(EB, EB + 256)]%Z)
      by (apply Forall_cons; [split; [cbn [fst snd]; replace (EB + 256 - EB)%Z with 256%Z by lia; exact EBLOC| cbn [fst snd]; lia]| apply Forall_nil]).
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ m6 _ _ (bv_unsigned sp) FW FX G MU6 WM6 ltac:(lia)) as [G6 AG6].
    lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end; clear MU6 WM6.
    cbn [app] in G6.
    assert (INV6 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') m6).
    { unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG6|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
      split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
    assert (HDL6 : rb_handle p p' s P B' m6).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [assumption|]). assumption. }
    pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LEN.
    assert (KX : forall (ra0 : word), implMG RNGx (fo_ret FO block_result FF_READ_BLOCK (RB_Err (Fmt.snprintf 256 fs args) p')) sx POSTQ
              (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp x x0 x1 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (snprintf_ret (fmt fs) args)) x2 x3 x4 x5 x6 x7 x8
                       (Z_to_bv 64 Fb) r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r21 r22 r23 r24 r25 r26 (Z_to_bv 64 Fb) x9 x10 x11 x12)
                  F (Z_to_bv 64 0x8bdac) fc None m6 (seg_rom asegs))).
    { intros ra0. subst POSTQ.
      eapply (rb_exit_m1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx m6) with (p := p) (B' := B') (scs := scs) (ccs' := ccs');
        [ exact CTX | exact INV6 | eassumption | exact Hscs | exact HDL6 | | | | eassumption | exact Hccs ].
      - replace (255 - length (Fmt.snprintf 256 fs args))%nat with (Z.to_nat 256 - length (Fmt.snprintf 256 fs args) - 1)%nat by lia. exact HEB6.
      - lia.
      - exact MOK. }
    destruct ROK as [->|[->| ->]].
    - replace (ret_pc (Z_to_bv 64 572844)) with (Z_to_bv 64 572844) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply evtF_done. apply KX.
    - replace (ret_pc (Z_to_bv 64 572808)) with (Z_to_bv 64 572808) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      zstep. apply evtF_done. apply KX.
    - replace (ret_pc (Z_to_bv 64 572776)) with (Z_to_bv 64 572776) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      zstep. apply evtF_done. apply KX.
  Qed.
  End Sz2.
  Lemma rb_snp : ltac:(let t := eval cbv delta [rb_snp__stmt] in rb_snp__stmt in exact t).
  Proof using GL GPL FRET SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm t0 t1 t2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej ej' pc FMTA fs args. ltac2:(SecDiet.SzSec.closeP 'rb_snp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition rb_fmt__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (t0 t1 t2 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 : word)
      (scs ccs' : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej ej' : list byte)
      (e : Z) (g : list Z -> Monad.M (PState H hptr) block_result),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 88%nat ->
    rb_handle p p' s P B' mm ->
    rw_cells asegs mm EB [CB 256 ej'] -> rw_cells asegs mm CUR ccs' -> cells_size ccs' = 24%nat ->
    (-2^31 <= e < 2^31)%Z -> fmt_at mm 0x22080 "error reading dump file"%string ->
    (forall msg, g msg = fo_ret FO _ FF_READ_BLOCK (RB_Err msg p')) ->
    implMG RNGx (mbind (fo_enter FO _ FF_FMT_ERRMSG (fo_ret FO _ FF_FMT_ERRMSG (fmt_errmsg "error reading dump file"%string [] e))) g) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR (Z_to_bv 64 0x8bd68) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 (s32 e)) (Z_to_bv 64 0x22080) a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r21 r22 r23 r24 r25 r26 (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 PCAP_FMT_ERRMSG_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm t0 t1 t2 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej ej' e g : ltac2:(SecDiet.SzSec.tyM 'rb_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_fmt__body : ltac2:(SecDiet.SzSec.bodyP 'rb_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FMT.
 intros CTX INV FRA Hscs HDL HEB HCUR Hccs HE MSG Hg.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p')%Z) by lia.
    rb_setup GL CTX INV AL0.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply implMG_bind.
    { eapply (FMT _ spa) with (L := L) (s := sx) (CL := (C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) (FB := FB) (FL := (FF_READ_BLOCK, Fb, 64%Z) :: FL) (lo := lo) (EB := EB)
                             (FMTA := 0x22080%Z) (e := e) (fs := "error reading dump file"%string) (args := []) (junk := ej');
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold PCAP_L1_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | cbn [map fb_fn fst]; intros [X|X]; [discriminate X|];
          exact (NF FF_FMT_ERRMSG ltac:(unfold frames_read_block; right; left; reflexivity) X)
        | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor
        | exact HEB | exact OEB | exact EB8 ]. }
    intros r4 s4' RNG4 ms4 PO. cbv beta in PO. destruct PO as (FP4 & -> & PO). destruct_exs PO.
    destruct PO as (-> & OF4 & LC4 & TL4 & MI4 & ST4 & AG4 & G4 & HEB4).
    rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 572776)) with (Z_to_bv 64 572776) by (symmetry; apply ret_pc_even; [lia|reflexivity]). rewrite Hg.
    lazymatch type of AG4 with agrees_on _ _ ?m4 =>
      assert (KST : forall A cs, rw_cells asegs mm A cs -> (SPA <= A)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC HA'; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [left; lia| lia]);
      assert (KFR : forall A cs, rw_cells asegs mm A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 64)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; right; left; apply in_frames_In; exists (FF_READ_BLOCK, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]);
      assert (KSH : forall A cs, rw_cells asegs mm A cs -> (Z.shiftr Fb 3 + 2147450880 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Z.shiftr Fb 3 + 2147450880 + 8)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; right; right; apply in_frame_sh_In; exists (FF_READ_BLOCK, Fb, 64%Z);
            split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 64 3) with 8%Z; lia]);
      assert (KP : forall A cs, rw_cells asegs mm A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + 680)%Z ->
                     (A + Z.of_nat (cells_size cs) <= EB \/ EB + 256 <= A)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3 H4; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; left; apply in_block_app; left; apply in_block_In; exists (self, P, PCAP_NG_SF_TOTAL); split; [exact HinP|];
            cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia);
      assert (KB : forall A cs, rw_cells asegs mm A cs -> (B' <= A)%Z -> (A + Z.of_nat (cells_size cs) <= B' + pc_bufalloc p')%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; left; apply in_block_app; right; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia)
    end.
    apply KST in FR; [|lia]. apply KST in FRA; [|lia]. apply KST in HCUR; [|lia].
    apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| lia]].
    apply KFR in FRC1; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KFR in FRC3; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KSH in SHC; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KP in HBS; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KP in HPV; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KP in HMB; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KB in HBUF; [|lia|cbn [cells_size csize Nat.add]; lia].
    assert (INV4 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG4 s4' (pc_buffer p') B' (pc_bufalloc p') x14).
    { unfold rb_inv, rb_shadow. split; [eapply fp_le_trans; [exact FP| exact FP4]|]. split; [exact G4|]. split; [congruence|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG4|]. intros a (K & N1 & N2 & N3). split; [|exact N3].
               destruct K as [K|[K|[K|K]]]; [left; lia| right; left; apply in_block_app; left; exact K
                                            | right; right; left; apply in_frames_cons; exact K| right; right; right; apply in_frame_sh_cons; exact K]. }
      split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
    assert (HDL4 : rb_handle p p' s P B' x14).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [assumption|]). assumption. }
    pose proof (munch_refl ([] : list (Z * Z)) x14) as MU. pose proof (wmono_refl asegs x14) as WM.
    apply implMG_from_evtF.
    zstep.
    apply evtF_done.
    eapply (rb_exit_m1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNG4 s4' x14) with (p := p) (B' := B') (scs := scs) (ccs' := ccs');
      [ exact CTX | exact INV4 | eassumption | exact Hscs | exact HDL4 | exact HEB4 | | | eassumption | exact Hccs ].
    - pose proof (fmt_errmsg_length "error reading dump file"%string [] e). lia.
    - apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor].
  Qed.
  End Sz3.
  Lemma rb_fmt : ltac:(let t := eval cbv delta [rb_fmt__stmt] in rb_fmt__stmt in exact t).
  Proof using GL GPL FRET FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm t0 t1 t2 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej ej' e g. ltac2:(SecDiet.SzSec.closeP 'rb_fmt__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbFail.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_sfchk_fsegA__B3P.SfAuxB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_exitA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.


Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section RbFail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.

  (* [comment removed for export] *)
  Definition rb_exit_m1__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 sp0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 : word)
      (scs ccs' : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej junk'' : list byte) (msg : list Z),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 88%nat ->
    rb_handle p p' s P B' mm ->
    rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''] ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    rw_cells asegs mm CUR ccs' -> cells_size ccs' = 24%nat ->
    implMG RNGx (fo_ret FO _ FF_READ_BLOCK (RB_Err msg p')) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 sp r9 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r26 (Z_to_bv 64 Fb) r21 r22 r24 r23 r25 r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bd6c) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 sp0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej junk'' msg : ltac2:(SecDiet.SzSec.tyM 'rb_exit_m1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_exit_m1__body : ltac2:(SecDiet.SzSec.bodyP 'rb_exit_m1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET.
 intros CTX INV FRA Hscs HDL HEB LM MOK HCUR Hccs.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep.
    apply evtF_done. subst POSTQ.
    eapply (rb_exit FO GIOA TP fflagA GL GPL FRET) with (p := p) (p' := p') (B' := B') (scs := scs);
      [ exact CTX | exact INV | exact FRA | exact Hscs | exact HDL |].
    cbn [rb_result]. split; [reflexivity|]. split; [reflexivity|]. split; [exists junk''; exact HEB|]. split; [exact LM|]. split; [exact MOK|].
    exists ccs'. split; [exact HCUR| exact Hccs].
  Qed.
  End Sz1.
  Lemma rb_exit_m1 : ltac:(let t := eval cbv delta [rb_exit_m1__stmt] in rb_exit_m1__stmt in exact t).
  Proof using GL GPL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 sp0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej junk'' msg. ltac2:(SecDiet.SzSec.closeP 'rb_exit_m1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition rb_ret_ok (pc : Z) : Prop := (pc = 0x8bd6c \/ pc = 0x8bd48 \/ pc = 0x8bd28)%Z.

  (* [comment removed for export] *)
  Definition rb_snp__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (t0 t1 t2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 : word)
      (scs ccs' : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej ej' : list byte)
      (pc FMTA : Z) (fs : string) (args : list farg),
    rb_ret_ok pc ->
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 88%nat ->
    rb_handle p p' s P B' mm ->
    rw_cells asegs mm EB [CB 256 ej'] -> rw_cells asegs mm CUR ccs' -> cells_size ccs' = 24%nat ->
    fmt_at mm FMTA fs -> fmt_ok fs args = true -> (length args <= 2)%nat ->
    Forall2 (farg_word true L RNGx ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) SPA EB 256 mm) args (firstn (length args) [a3; a4]) ->
    Forall (fun z => 0 < z < 256)%Z (Fmt.snprintf 256 fs args) ->
    implMG RNGx (fo_ret FO _ FF_READ_BLOCK (RB_Err (Fmt.snprintf 256 fs args) p')) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r26 (Z_to_bv 64 Fb) r21 r22 r24 r23 r25 r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 SNPRINTF_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm t0 t1 t2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej ej' pc FMTA fs args : ltac2:(SecDiet.SzSec.tyM 'rb_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_snp__body : ltac2:(SecDiet.SzSec.bodyP 'rb_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET SNPRINTF.
 intros ROK CTX INV FRA Hscs HDL HEB HCUR Hccs FMT5 FOK LA FWA MOK.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p')%Z) by lia.
    rb_setup GL CTX INV AL0.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply SNPRINTF with (L := L) (s := sx) (CL := (C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) (FB := FB) (FL := (FF_READ_BLOCK, Fb, 64%Z) :: FL) (lo := lo)
                             (DST := EB) (n := 256%Z) (FMTA := FMTA) (fs := fs) (args := args) (junk := ej');
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | lia
        | rewrite Hspa; replace (firstn (length args) [a3; a4; a5]) with (firstn (length args) [a3; a4])
            by (clear - LA; destruct args as [|? [|? [|? ?]]]; cbn in LA |- *; first [reflexivity | lia]); exact FWA
        | exact HEB | exact OEB ]
      | ].
    cbv beta; intros ms' PO; destruct PO as (vav5 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
    unfold STDIO_STACK in MU6.
    assert (FW : Forall (own_ivA [(FF_READ_BLOCK, Fb, 64%Z)] [(pc_buffer p', B', pc_bufalloc p')] (bv_unsigned sp)) [(SPA - 16384, SPA)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    assert (FX : Forall (cobj_iv FL (C1 ++ C2)) [(EB, EB + 256)]%Z)
      by (apply Forall_cons; [split; [cbn [fst snd]; replace (EB + 256 - EB)%Z with 256%Z by lia; exact EBLOC| cbn [fst snd]; lia]| apply Forall_nil]).
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_READ_BLOCK, Fb, 64%Z)] _ m6 _ _ (bv_unsigned sp) FW FX G MU6 WM6 ltac:(lia)) as [G6 AG6].
    lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end; clear MU6 WM6.
    cbn [app] in G6.
    assert (INV6 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') m6).
    { unfold rb_inv, rb_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG6|]. intros a (K & N1 & N2 & N3). split; [exact K|]. cbn [outside fst snd]. split; [lia| exact I]. }
      split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
    assert (HDL6 : rb_handle p p' s P B' m6).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [assumption|]). assumption. }
    pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LEN.
    assert (KX : forall (ra0 : word), implMG RNGx (fo_ret FO block_result FF_READ_BLOCK (RB_Err (Fmt.snprintf 256 fs args) p')) sx POSTQ
              (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp x x0 x1 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (snprintf_ret (fmt fs) args)) x2 x3 x4 x5 x6 x7 x8
                       (Z_to_bv 64 Fb) r26 (Z_to_bv 64 Fb) r21 r22 r24 r23 r25 r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) x9 x10 x11 x12)
                  F (Z_to_bv 64 0x8bd6c) fc None m6 (seg_rom asegs))).
    { intros ra0. subst POSTQ.
      eapply (rb_exit_m1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx m6) with (p := p) (B' := B') (scs := scs) (ccs' := ccs');
        [ exact CTX | exact INV6 | eassumption | exact Hscs | exact HDL6 | | | | eassumption | exact Hccs ].
      - replace (255 - length (Fmt.snprintf 256 fs args))%nat with (Z.to_nat 256 - length (Fmt.snprintf 256 fs args) - 1)%nat by lia. exact HEB6.
      - lia.
      - exact MOK. }
    destruct ROK as [->|[->| ->]].
    - replace (ret_pc (Z_to_bv 64 572780)) with (Z_to_bv 64 572780) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      apply evtF_done. apply KX.
    - replace (ret_pc (Z_to_bv 64 572744)) with (Z_to_bv 64 572744) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      zstep. apply evtF_done. apply KX.
    - replace (ret_pc (Z_to_bv 64 572712)) with (Z_to_bv 64 572712) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      zstep. apply evtF_done. apply KX.
  Qed.
  End Sz2.
  Lemma rb_snp : ltac:(let t := eval cbv delta [rb_snp__stmt] in rb_snp__stmt in exact t).
  Proof using GL GPL FRET SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm t0 t1 t2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej ej' pc FMTA fs args. ltac2:(SecDiet.SzSec.closeP 'rb_snp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition rb_fmt__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (t0 t1 t2 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 : word)
      (scs ccs' : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej ej' : list byte)
      (e : Z) (g : list Z -> Monad.M (PState H hptr) block_result),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA scs -> cells_size scs = 88%nat ->
    rb_handle p p' s P B' mm ->
    rw_cells asegs mm EB [CB 256 ej'] -> rw_cells asegs mm CUR ccs' -> cells_size ccs' = 24%nat ->
    (-2^31 <= e < 2^31)%Z -> fmt_at mm 0x22080 "error reading dump file"%string ->
    (forall msg, g msg = fo_ret FO _ FF_READ_BLOCK (RB_Err msg p')) ->
    implMG RNGx (mbind (fo_enter FO _ FF_FMT_ERRMSG (fo_ret FO _ FF_FMT_ERRMSG (fmt_errmsg "error reading dump file"%string [] e))) g) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR (Z_to_bv 64 0x8bd28) (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 (s32 e)) (Z_to_bv 64 0x22080) a4 a5 a6 a7
               (Z_to_bv 64 Fb) r26 (Z_to_bv 64 Fb) r21 r22 r24 r23 r25 r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 PCAP_FMT_ERRMSG_ENTRY) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm t0 t1 t2 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej ej' e g : ltac2:(SecDiet.SzSec.tyM 'rb_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_fmt__body : ltac2:(SecDiet.SzSec.bodyP 'rb_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FMT.
 intros CTX INV FRA Hscs HDL HEB HCUR Hccs HE MSG Hg.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p')%Z) by lia.
    rb_setup GL CTX INV AL0.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply implMG_bind.
    { eapply (FMT _ spa) with (L := L) (s := sx) (CL := (C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) (FB := FB) (FL := (FF_READ_BLOCK, Fb, 64%Z) :: FL) (lo := lo) (EB := EB)
                             (FMTA := 0x22080%Z) (e := e) (fs := "error reading dump file"%string) (args := []) (junk := ej');
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold PCAP_L1_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | cbn [map fb_fn fst]; intros [X|X]; [discriminate X|];
          exact (NF FF_FMT_ERRMSG ltac:(unfold frames_read_block; right; left; reflexivity) X)
        | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor
        | exact HEB | exact OEB | exact EB8 ]. }
    intros r4 s4' RNG4 ms4 PO. cbv beta in PO. destruct PO as (FP4 & -> & PO). destruct_exs PO.
    destruct PO as (-> & OF4 & LC4 & TL4 & MI4 & ST4 & AG4 & G4 & HEB4).
    rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 572712)) with (Z_to_bv 64 572712) by (symmetry; apply ret_pc_even; [lia|reflexivity]). rewrite Hg.
    lazymatch type of AG4 with agrees_on _ _ ?m4 =>
      assert (KST : forall A cs, rw_cells asegs mm A cs -> (SPA <= A)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC HA'; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [left; lia| lia]);
      assert (KFR : forall A cs, rw_cells asegs mm A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 64)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; right; left; apply in_frames_In; exists (FF_READ_BLOCK, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]);
      assert (KSH : forall A cs, rw_cells asegs mm A cs -> (Z.shiftr Fb 3 + 2147450880 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Z.shiftr Fb 3 + 2147450880 + 8)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; right; right; apply in_frame_sh_In; exists (FF_READ_BLOCK, Fb, 64%Z);
            split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 64 3) with 8%Z; lia]);
      assert (KP : forall A cs, rw_cells asegs mm A cs -> (P <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + 680)%Z ->
                     (A + Z.of_nat (cells_size cs) <= EB \/ EB + 256 <= A)%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3 H4; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; left; apply in_block_app; left; apply in_block_In; exists (self, P, PCAP_NG_SF_TOTAL); split; [exact HinP|];
            cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia);
      assert (KB : forall A cs, rw_cells asegs mm A cs -> (B' <= A)%Z -> (A + Z.of_nat (cells_size cs) <= B' + pc_bufalloc p')%Z -> rw_cells asegs m4 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
            right; left; apply in_block_app; right; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia)
    end.
    apply KST in FR; [|lia]. apply KST in FRA; [|lia]. apply KST in HCUR; [|lia].
    apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| lia]].
    apply KFR in FRC1; [|lia|cbn [cells_size csize Nat.add]; lia]. apply KFR in FRC3; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KSH in SHC; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply KP in HBS; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KP in HPV; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KP in HMB; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KB in HBUF; [|lia|cbn [cells_size csize Nat.add]; lia].
    assert (INV4 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG4 s4' (pc_buffer p') B' (pc_bufalloc p') x14).
    { unfold rb_inv, rb_shadow. split; [eapply fp_le_trans; [exact FP| exact FP4]|]. split; [exact G4|]. split; [congruence|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG4|]. intros a (K & N1 & N2 & N3). split; [|exact N3].
               destruct K as [K|[K|[K|K]]]; [left; lia| right; left; apply in_block_app; left; exact K
                                            | right; right; left; apply in_frames_cons; exact K| right; right; right; apply in_frame_sh_cons; exact K]. }
      split; [exists k0, k1, k2, pre; assumption|]. split; [exists post; assumption| assumption]. }
    assert (HDL4 : rb_handle p p' s P B' x14).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [assumption|]). assumption. }
    pose proof (munch_refl ([] : list (Z * Z)) x14) as MU. pose proof (wmono_refl asegs x14) as WM.
    apply implMG_from_evtF.
    zstep.
    apply evtF_done.
    eapply (rb_exit_m1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNG4 s4' x14) with (p := p) (B' := B') (scs := scs) (ccs' := ccs');
      [ exact CTX | exact INV4 | eassumption | exact Hscs | exact HDL4 | exact HEB4 | | | eassumption | exact Hccs ].
    - pose proof (fmt_errmsg_length "error reading dump file"%string [] e). lia.
    - apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor].
  Qed.
  End Sz3.
  Lemma rb_fmt : ltac:(let t := eval cbv delta [rb_fmt__stmt] in rb_fmt__stmt in exact t).
  Proof using GL GPL FRET FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm t0 t1 t2 a4 a5 a6 a7 r19 r21 r22 r23 r24 r25 r26 t3 t4 t5 t6 scs ccs' p p' s B' ej ej' e g. ltac2:(SecDiet.SzSec.closeP 'rb_fmt__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbFail.
End CANSEC1.
End TwB.
End F_ngblk_failA.

(* [comment removed for export] *)
Module F_ngblk_shortA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.



Ltac fmt_at_solve MI A fs :=
  split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs _ A (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string fs) ++ [Z_to_bv 8 0])
                            MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
  split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]).

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section RbShort.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.

  (* [comment removed for export] *)
  Definition rb_short1__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r23 r24 r25 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 : word) (ccs : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej : list byte)
      (got : list Z) (K : rb_status * list Z -> Monad.M (PState H hptr) block_result),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p' s P B' mm ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    (0 <= zlength got <= 8)%Z -> zlength got <> 8%Z ->
    (forall msg, K (RBS_Err msg, got) = fo_ret FO _ FF_READ_BLOCK (RB_Err msg p')) ->
    K (RBS_Eof, got) = fo_ret FO _ FF_READ_BLOCK (RB_Eof p') ->
    implMG RNGx (mbind (mbind (e_ferror (prims HO FO sites) f)
                          (fun e : bool => if e then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string []) (fun m0 => mret (RBS_Err m0, got))
                                           else if (zlength got =? 0)%Z && negb false then mret (RBS_Eof, got)
                                                else mret (RBS_Err (Msg.trunc_pcapng 8 (zlength got)), got))) K) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (zlength got)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r21 (Z_to_bv 64 Af) r23 r24 r25 (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bd2c) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r23 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 ccs p p' s B' ej got K : ltac2:(SecDiet.SzSec.tyM 'rb_short1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_short1__body : ltac2:(SecDiet.SzSec.bodyP 'rb_short1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FERROR SNPRINTF FMT.
 intros CTX INV FRA HDL HEB HCUR Hccs GOTL GNE KERR KEOF.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p')%Z) by lia.
    rb_setup GL CTX INV AL0.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    cbn [e_ferror prims].
    apply implMG_bind_assoc.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. do 3 zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := (C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) (FB := FB) (FL := (FF_READ_BLOCK, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. destruct PO as (FP3 & av & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 572728)) with (Z_to_bv 64 572728) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG3 sx (pc_buffer p') B' (pc_bufalloc p') m3).
    { eapply (rb_inv_callee FO GIOA fflagA GL) with (Pn := fun _ => True);
        [ exact INV | lia | lia | exact FP3 | exact G3 | reflexivity | exact MI3' | exact ST3
        | eapply agrees_on_weaken; [exact AG3|]; intros a (KK & _); exact KK | intros; exact I | intros; exact I | intros; exact I | intros; exact I ]. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) SPA a).
    { intros a Ha. right; left. apply in_block_app. left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B' <= a < B' + pc_bufalloc p')%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) SPA a).
    { intros a Ha. right; left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply (agrees_rw_cells _ _ _ _ _ AG3) in FRA; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact (proj1 OEB)| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HBUF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia].
    assert (HDL3 : rb_handle p p' s P B' m3).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [assumption|]). assumption. }
    destruct r.
    - (* [comment removed for export] *)
      destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
      cbv iota. unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
      apply implMG_bind_assoc. apply implMG_errno_ll. set (e := lc_errno (ps_libc sx)) in *.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 (rng_fp_le _ _ _ _ FP3 RTLS)) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m3 0x22080 "error reading dump file"%string) by (fmt_at_solve MI3' 0x22080%Z "error reading dump file"%string).
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      apply implMG_from_evtF. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      ck TUNP 4%Z 0x8bd50%Z [11%Z; 12%Z].
      zstep.
      do 2 zstep. do 2 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (rb_fmt FO GIOA TP fflagA GL GPL FRET FMT) with (p := p) (p' := p') (B' := B') (ccs' := ccs) (ej' := ej)
                 (scs := [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10]);
        [ exact CTX | exact INV3 | exact FRA | reflexivity | exact HDL3 | exact HEB | exact HCUR | exact Hccs | lia | exact MSG | ].
      intros msg. exact (KERR msg).
    - (* [comment removed for export] *)
      clear ERRNO. cbv iota. cbn [negb andb]. rewrite Bool.andb_true_r.
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      destruct (Z.eq_dec (zlength got) 0) as [GZ|GNZ].
      + rewrite (proj2 (Z.eqb_eq _ _) GZ). rewrite GZ.
        apply implMG_retb. rewrite KEOF.
        apply implMG_from_evtF. zstep. if_true.
        zstep. if_true.
        do 2 zstep.
        apply evtF_done. subst POSTQ.
        eapply (rb_exit FO GIOA TP fflagA GL GPL FRET) with (p := p) (p' := p') (B' := B')
                 (scs := [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10]);
          [ exact CTX | exact INV3 | exact FRA | reflexivity | exact HDL3 |].
        cbn [rb_result]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HEB|]. exists ccs. split; [exact HCUR| exact Hccs].
      + rewrite (proj2 (Z.eqb_neq _ _) GNZ).
        apply implMG_retb. rewrite KERR.
        assert (MSG : fmt_at m3 0x22300 "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
          by (fmt_at_solve MI3' 0x22300%Z "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string).
        apply implMG_from_evtF. zstep. if_true.
        zstep. if_cases Kz; [zify_cond Kz; exfalso; lia|].
        do 6 zstep. zstep.
        apply evtF_done. subst POSTQ. unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE.
        eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bdac%Z) (p := p) (p' := p') (B' := B') (ccs' := ccs) (ej' := ej)
                 (scs := [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10])
                 (args := [AInt 8; AInt (zlength got)]);
          [ left; reflexivity | exact CTX | exact INV3 | exact FRA | reflexivity | exact HDL3 | exact HEB | exact HCUR | exact Hccs
          | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
          | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ].
  Qed.
  End Sz1.
  Lemma rb_short1 : ltac:(let t := eval cbv delta [rb_short1__stmt] in rb_short1__stmt in exact t).
  Proof using GL GPL FRET FERROR SNPRINTF FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r23 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 ccs p p' s B' ej got K. ltac2:(SecDiet.SzSec.closeP 'rb_short1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition rb_short2__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 : word) (ccs : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej : list byte)
      (got : list Z) (n : Z) (K : rb_status * list Z -> Monad.M (PState H hptr) block_result),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p' s P B' mm ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    (0 <= n <= 2^30)%Z -> (0 <= zlength got <= n)%Z -> zlength got <> n ->
    (forall msg, K (RBS_Err msg, got) = fo_ret FO _ FF_READ_BLOCK (RB_Err msg p')) ->
    implMG RNGx (mbind (mbind (e_ferror (prims HO FO sites) f)
                          (fun e : bool => if e then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string []) (fun m0 => mret (RBS_Err m0, got))
                                           else if (zlength got =? 0)%Z && negb true then mret (RBS_Eof, got)
                                                else mret (RBS_Err (Msg.trunc_pcapng n (zlength got)), got))) K) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (zlength got)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r21 (Z_to_bv 64 Af) (Z_to_bv 64 n) r24 r25 (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8c060) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 ccs p p' s B' ej got n K : ltac2:(SecDiet.SzSec.tyM 'rb_short2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_short2__body : ltac2:(SecDiet.SzSec.bodyP 'rb_short2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FERROR SNPRINTF FMT.
 intros CTX INV FRA HDL HEB HCUR Hccs Hn GOTL GNE KERR.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p')%Z) by lia.
    rb_setup GL CTX INV AL0.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    cbn [e_ferror prims].
    apply implMG_bind_assoc.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. do 3 zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := (C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) (FB := FB) (FL := (FF_READ_BLOCK, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. destruct PO as (FP3 & av & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 573548)) with (Z_to_bv 64 573548) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG3 sx (pc_buffer p') B' (pc_bufalloc p') m3).
    { eapply (rb_inv_callee FO GIOA fflagA GL) with (Pn := fun _ => True);
        [ exact INV | lia | lia | exact FP3 | exact G3 | reflexivity | exact MI3' | exact ST3
        | eapply agrees_on_weaken; [exact AG3|]; intros a (KK & _); exact KK | intros; exact I | intros; exact I | intros; exact I | intros; exact I ]. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) SPA a).
    { intros a Ha. right; left. apply in_block_app. left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B' <= a < B' + pc_bufalloc p')%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) SPA a).
    { intros a Ha. right; left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply (agrees_rw_cells _ _ _ _ _ AG3) in FRA; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact (proj1 OEB)| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HBUF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia].
    assert (HDL3 : rb_handle p p' s P B' m3).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [assumption|]). assumption. }
    destruct r.
    - (* [comment removed for export] *)
      destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
      cbv iota. unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
      apply implMG_bind_assoc. apply implMG_errno_ll. set (e := lc_errno (ps_libc sx)) in *.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 (rng_fp_le _ _ _ _ FP3 RTLS)) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m3 0x22080 "error reading dump file"%string) by (fmt_at_solve MI3' 0x22080%Z "error reading dump file"%string).
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      apply implMG_from_evtF. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      ck TUNP 4%Z 0x8c084%Z [11%Z; 12%Z].
      zstep.
      do 2 zstep. zstep. do 2 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (rb_fmt FO GIOA TP fflagA GL GPL FRET FMT) with (p := p) (p' := p') (B' := B') (ccs' := ccs) (ej' := ej)
                 (scs := [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10]);
        [ exact CTX | exact INV3 | exact FRA | reflexivity | exact HDL3 | exact HEB | exact HCUR | exact Hccs | lia | exact MSG | ].
      intros msg. exact (KERR msg).
    - (* [comment removed for export] *)
      clear ERRNO. cbv iota. cbn [negb]. rewrite Bool.andb_false_r.
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      apply implMG_retb. rewrite KERR.
      assert (MSG : fmt_at m3 0x22300 "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
        by (fmt_at_solve MI3' 0x22300%Z "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string).
      apply implMG_from_evtF. zstep. if_true.
      do 7 zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE.
      eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bdac%Z) (p := p) (p' := p') (B' := B') (ccs' := ccs) (ej' := ej)
               (scs := [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10])
               (args := [AInt n; AInt (zlength got)]);
        [ left; reflexivity | exact CTX | exact INV3 | exact FRA | reflexivity | exact HDL3 | exact HEB | exact HCUR | exact Hccs
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ].
  Qed.
  End Sz2.
  Lemma rb_short2 : ltac:(let t := eval cbv delta [rb_short2__stmt] in rb_short2__stmt in exact t).
  Proof using GL GPL FRET FERROR SNPRINTF FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 ccs p p' s B' ej got n K. ltac2:(SecDiet.SzSec.closeP 'rb_short2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbShort.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_sfchk_fsegA__B3P.SfAuxB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_ngblk_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.F_ngblk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_ngblk_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.



Ltac fmt_at_solve MI A fs :=
  split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs _ A (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string fs) ++ [Z_to_bv 8 0])
                            MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
  split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]).

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section RbShort.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.

  (* [comment removed for export] *)
  Definition rb_short1__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r23 r24 r25 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 : word) (ccs : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej : list byte)
      (got : list Z) (K : rb_status * list Z -> Monad.M (PState H hptr) block_result),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p' s P B' mm ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    (0 <= zlength got <= 8)%Z -> zlength got <> 8%Z ->
    (forall msg, K (RBS_Err msg, got) = fo_ret FO _ FF_READ_BLOCK (RB_Err msg p')) ->
    K (RBS_Eof, got) = fo_ret FO _ FF_READ_BLOCK (RB_Eof p') ->
    implMG RNGx (mbind (mbind (e_ferror (prims HO FO sites) f)
                          (fun e : bool => if e then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string []) (fun m0 => mret (RBS_Err m0, got))
                                           else if (zlength got =? 0)%Z && negb false then mret (RBS_Eof, got)
                                                else mret (RBS_Err (Msg.trunc_pcapng 8 (zlength got)), got))) K) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (zlength got)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) r21 (Z_to_bv 64 Af) r24 r23 r25 r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bce0) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r23 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 ccs p p' s B' ej got K : ltac2:(SecDiet.SzSec.tyM 'rb_short1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_short1__body : ltac2:(SecDiet.SzSec.bodyP 'rb_short1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FERROR SNPRINTF FMT.
 intros CTX INV FRA HDL HEB HCUR Hccs GOTL GNE KERR KEOF.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p')%Z) by lia.
    rb_setup GL CTX INV AL0.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    cbn [e_ferror prims].
    apply implMG_bind_assoc.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. do 3 zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := (C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) (FB := FB) (FL := (FF_READ_BLOCK, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. destruct PO as (FP3 & av & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 572652)) with (Z_to_bv 64 572652) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG3 sx (pc_buffer p') B' (pc_bufalloc p') m3).
    { eapply (rb_inv_callee FO GIOA fflagA GL) with (Pn := fun _ => True);
        [ exact INV | lia | lia | exact FP3 | exact G3 | reflexivity | exact MI3' | exact ST3
        | eapply agrees_on_weaken; [exact AG3|]; intros a (KK & _); exact KK | intros; exact I | intros; exact I | intros; exact I | intros; exact I ]. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) SPA a).
    { intros a Ha. right; left. apply in_block_app. left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B' <= a < B' + pc_bufalloc p')%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) SPA a).
    { intros a Ha. right; left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply (agrees_rw_cells _ _ _ _ _ AG3) in FRA; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact (proj1 OEB)| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HBUF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia].
    assert (HDL3 : rb_handle p p' s P B' m3).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [assumption|]). assumption. }
    destruct r.
    - (* [comment removed for export] *)
      destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
      cbv iota. unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
      apply implMG_bind_assoc. apply implMG_errno_ll. set (e := lc_errno (ps_libc sx)) in *.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 (rng_fp_le _ _ _ _ FP3 RTLS)) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m3 0x22080 "error reading dump file"%string) by (fmt_at_solve MI3' 0x22080%Z "error reading dump file"%string).
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      apply implMG_from_evtF. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      (* [comment removed for export] *)
      pose proof ATPv_pg as TPG. pose proof atp_lin as ((TPLO & _) & _).
      assert (XX : (0 < ATP + -164 < 2 ^ 64)%Z) by (unfold ATP; atop_facts; lia).
      zstep. if_false_by (eqz_false (ATP + -164) XX).
      zstep. replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
      zstep. if_false.
      ck TUNP 4%Z 0x8bd10%Z [11%Z; 12%Z].
      zstep.
      do 2 zstep. do 2 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (rb_fmt FO GIOA TP fflagA GL GPL FRET FMT) with (p := p) (p' := p') (B' := B') (ccs' := ccs) (ej' := ej)
                 (scs := [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10]);
        [ exact CTX | exact INV3 | exact FRA | reflexivity | exact HDL3 | exact HEB | exact HCUR | exact Hccs | lia | exact MSG | ].
      intros msg. exact (KERR msg).
    - (* [comment removed for export] *)
      clear ERRNO. cbv iota. cbn [negb andb]. rewrite Bool.andb_true_r.
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      destruct (Z.eq_dec (zlength got) 0) as [GZ|GNZ].
      + rewrite (proj2 (Z.eqb_eq _ _) GZ). rewrite GZ.
        apply implMG_retb. rewrite KEOF.
        apply implMG_from_evtF. zstep. if_true.
        zstep. if_true.
        do 2 zstep.
        apply evtF_done. subst POSTQ.
        eapply (rb_exit FO GIOA TP fflagA GL GPL FRET) with (p := p) (p' := p') (B' := B')
                 (scs := [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10]);
          [ exact CTX | exact INV3 | exact FRA | reflexivity | exact HDL3 |].
        cbn [rb_result]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HEB|]. exists ccs. split; [exact HCUR| exact Hccs].
      + rewrite (proj2 (Z.eqb_neq _ _) GNZ).
        apply implMG_retb. rewrite KERR.
        assert (MSG : fmt_at m3 0x22300 "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
          by (fmt_at_solve MI3' 0x22300%Z "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string).
        apply implMG_from_evtF. zstep. if_true.
        zstep. if_cases Kz; [zify_cond Kz; exfalso; lia|].
        do 6 zstep. zstep.
        apply evtF_done. subst POSTQ. unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE.
        eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bd6c%Z) (p := p) (p' := p') (B' := B') (ccs' := ccs) (ej' := ej)
                 (scs := [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10])
                 (args := [AInt 8; AInt (zlength got)]);
          [ left; reflexivity | exact CTX | exact INV3 | exact FRA | reflexivity | exact HDL3 | exact HEB | exact HCUR | exact Hccs
          | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
          | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ].
  Qed.
  End Sz1.
  Lemma rb_short1 : ltac:(let t := eval cbv delta [rb_short1__stmt] in rb_short1__stmt in exact t).
  Proof using GL GPL FRET FERROR SNPRINTF FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r23 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 ccs p p' s B' ej got K. ltac2:(SecDiet.SzSec.closeP 'rb_short1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition rb_short2__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (C1 C2 FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P CUR EB Af SPA Fb : Z) (self f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 : word) (ccs : list cell) (p p' : PcapTypes.pcap hptr hptr) (s : pcap_ng_sf) (B' : Z) (ej : list byte)
      (got : list Z) (n : Z) (K : rb_status * list Z -> Monad.M (PState H hptr) block_result),
    rb_ctx TP ra sp tp s0 L RNG C1 C2 FB FL trC lo P CUR EB Af SPA self f m ->
    rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNGx sx (pc_buffer p') B' (pc_bufalloc p') mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10] ->
    rb_handle p p' s P B' mm ->
    rw_cells asegs mm EB [CB 256 ej] -> rw_cells asegs mm CUR ccs -> cells_size ccs = 24%nat ->
    (0 <= n <= 2^30)%Z -> (0 <= zlength got <= n)%Z -> zlength got <> n ->
    (forall msg, K (RBS_Err msg, got) = fo_ret FO _ FF_READ_BLOCK (RB_Err msg p')) ->
    implMG RNGx (mbind (mbind (e_ferror (prims HO FO sites) f)
                          (fun e : bool => if e then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string []) (fun m0 => mret (RBS_Err m0, got))
                                           else if (zlength got =? 0)%Z && negb true then mret (RBS_Eof, got)
                                                else mret (RBS_Err (Msg.trunc_pcapng n (zlength got)), got))) K) sx
      (read_block_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P CUR EB p s ej m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (zlength got)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) r21 (Z_to_bv 64 Af) r24 (Z_to_bv 64 n) r25 r19 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bfe8) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 ccs p p' s B' ej got n K : ltac2:(SecDiet.SzSec.tyM 'rb_short2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma rb_short2__body : ltac2:(SecDiet.SzSec.bodyP 'rb_short2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GPL FRET FERROR SNPRINTF FMT.
 intros CTX INV FRA HDL HEB HCUR Hccs Hn GOTL GNE KERR.
    pose proof HDL as ((HBS & HPV & HMB & WBS & WMB & WBA & BSA) & (bs' & HBUF & PFX) & LENB & E1 & E2 & E3 & E4 & E5 & E6).
    assert (AL0 : (0 < pc_bufalloc p')%Z) by lia.
    rb_setup GL CTX INV AL0.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    cbn [e_ferror prims].
    apply implMG_bind_assoc.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. do 3 zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := (C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) (FB := FB) (FL := (FF_READ_BLOCK, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. destruct PO as (FP3 & av & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 573428)) with (Z_to_bv 64 573428) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INV3 : rb_inv GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG C1 C2 FB FL lo P CUR EB SPA Fb o m RNG3 sx (pc_buffer p') B' (pc_bufalloc p') m3).
    { eapply (rb_inv_callee FO GIOA fflagA GL) with (Pn := fun _ => True);
        [ exact INV | lia | lia | exact FP3 | exact G3 | reflexivity | exact MI3' | exact ST3
        | eapply agrees_on_weaken; [exact AG3|]; intros a (KK & _); exact KK | intros; exact I | intros; exact I | intros; exact I | intros; exact I ]. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) SPA a).
    { intros a Ha. right; left. apply in_block_app. left. apply in_block_In. exists (self, P, PCAP_NG_SF_TOTAL). split; [exact HinP|].
      cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (INB : forall a, (B' <= a < B' + pc_bufalloc p')%Z -> client_keeps ((FF_READ_BLOCK, Fb, 64%Z) :: FL) ((C1 ++ C2) ++ [(pc_buffer p', B', pc_bufalloc p')]) SPA a).
    { intros a Ha. right; left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply (agrees_rw_cells _ _ _ _ _ AG3) in FRA; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HCUR; [| intros a Ha; rewrite Hccs in Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact (proj1 OEB)| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HBS; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HPV; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HMB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INP; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HBUF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply INB; lia].
    assert (HDL3 : rb_handle p p' s P B' m3).
    { unfold rb_handle, blk_handle. split; [repeat (split; [assumption|]); assumption|]. split; [exists bs'; split; assumption|].
      repeat (split; [assumption|]). assumption. }
    destruct r.
    - (* [comment removed for export] *)
      destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
      cbv iota. unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
      apply implMG_bind_assoc. apply implMG_errno_ll. set (e := lc_errno (ps_libc sx)) in *.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 (rng_fp_le _ _ _ _ FP3 RTLS)) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m3 0x22080 "error reading dump file"%string) by (fmt_at_solve MI3' 0x22080%Z "error reading dump file"%string).
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      apply implMG_from_evtF. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      (* [comment removed for export] *)
      pose proof ATPv_pg as TPG. pose proof atp_lin as ((TPLO & _) & _).
      assert (XX : (0 < ATP + -164 < 2 ^ 64)%Z) by (unfold ATP; atop_facts; lia).
      zstep. if_false_by (eqz_false (ATP + -164) XX).
      zstep. replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
      zstep. if_false.
      ck TUNP 4%Z 0x8c018%Z [11%Z; 12%Z].
      zstep.
      do 2 zstep. zstep. do 2 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (rb_fmt FO GIOA TP fflagA GL GPL FRET FMT) with (p := p) (p' := p') (B' := B') (ccs' := ccs) (ej' := ej)
                 (scs := [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10]);
        [ exact CTX | exact INV3 | exact FRA | reflexivity | exact HDL3 | exact HEB | exact HCUR | exact Hccs | lia | exact MSG | ].
      intros msg. exact (KERR msg).
    - (* [comment removed for export] *)
      clear ERRNO. cbv iota. cbn [negb]. rewrite Bool.andb_false_r.
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      apply implMG_retb. rewrite KERR.
      assert (MSG : fmt_at m3 0x22300 "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
        by (fmt_at_solve MI3' 0x22300%Z "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string).
      apply implMG_from_evtF. zstep. if_true.
      do 7 zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE.
      eapply (rb_snp FO GIOA TP fflagA GL GPL FRET SNPRINTF) with (pc := 0x8bd6c%Z) (p := p) (p' := p') (B' := B') (ccs' := ccs) (ej' := ej)
               (scs := [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 (Z_to_bv 64 EB); C8 c8; C8 c9; C8 c10])
               (args := [AInt n; AInt (zlength got)]);
        [ left; reflexivity | exact CTX | exact INV3 | exact FRA | reflexivity | exact HDL3 | exact HEB | exact HCUR | exact Hccs
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ].
  Qed.
  End Sz2.
  Lemma rb_short2 : ltac:(let t := eval cbv delta [rb_short2__stmt] in rb_short2__stmt in exact t).
  Proof using GL GPL FRET FERROR SNPRINTF FMT. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG C1 C2 FB FL trC lo P CUR EB Af SPA Fb self f m o RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r21 r24 r25 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c8 c9 c10 ccs p p' s B' ej got n K. ltac2:(SecDiet.SzSec.closeP 'rb_short2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RbShort.
End CANSEC1.
End TwB.
End F_ngblk_shortA.

(* [comment removed for export] *)
Module F_ngrbA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Definition FMT_ERR_READING_A : Z := 0x22080.   (* [comment removed for export] *)
Definition FMT_TRUNC_PCAPNG_A : Z := 0x22300.  (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section RB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  (* [comment removed for export] *)
  Definition cobjA_keep0__stmt : Prop := forall L RNG RNG' s' CL CL' FB' FL FL' m m' A n,
    cobjA RNG m FL CL A n -> GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' ->
    agrees_on (in_frame_sh FL) m m' -> 0 <= n -> cobjA RNG' m' FL CL A n.
  Section Sz1.
  Variables L RNG RNG' s' CL CL' FB' FL FL' m m' A n : ltac2:(SecDiet.SzSec.tyM 'cobjA_keep0__stmt "vvvvvvvvvvvvv" @L).
  #[using="tlsI FO fflagA GL"] Lemma cobjA_keep0__body : ltac2:(SecDiet.SzSec.bodyP 'cobjA_keep0__stmt "vvvvvvvvvvvvv").
  Proof.
    intros O G' ICL IFL AG Hn.
    destruct (Z.eq_dec n 0) as [->|NZ]; [| eapply (cobjA_keep _ _ _ GL); try eassumption; lia].
    destruct O as [LOC (A0 & A47 & _)]. split; [exact LOC|].
    destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
    - eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G'| apply in_or_app; left; apply ICL; exact Hb] | exact H1 | exact H2 | lia].
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G') as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr (IFL _ Hf)) as FRA.
      eapply frameA_aobj; [exact FRA| exact H1| exact H2| lia|].
      split; [lia|]. split; [lia|]. intros; lia.
  Qed.
  End Sz1.
  #[using="tlsI FO fflagA GL"] Lemma cobjA_keep0 : ltac:(let t := eval cbv delta [cobjA_keep0__stmt] in cobjA_keep0__stmt in exact t).
  Proof. intros L RNG RNG' s' CL CL' FB' FL FL' m m' A n. ltac2:(SecDiet.SzSec.closeP 'cobjA_keep0__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_mget_l : forall {St A} RNG (k : St -> Monad.M St A) s Q ms, implMG RNG (k s) s Q ms -> implMG RNG (mbind mget k) s Q ms.
  Proof. intros St A RNG k s Q ms HH. exact HH. Qed.

  Definition read_bytes_proofA__stmt : Prop := read_bytes_stmt HO FO sites GIOA TP.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC f Af D n EB lo foe dest junk ej : ltac2:(SecDiet.SzSec.tyM 'read_bytes_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL FREAD FERROR FMT SNPRINTF"] Lemma read_bytes_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'read_bytes_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR NF HinF HD -> -> -> -> -> Hn HDST OD HEB OE DISJ EB8.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    unfold READ_BYTES_STACK, PCAP_L1_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rng_sp_window RSTK sp RSPW.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof (proj1 OE) as EBL. pose proof (proj1 OD) as DL.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL) as (EBLO & EBHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G DL) as (DLO & DHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL ltac:(lia)) as EBBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G DL ltac:(lia)) as DBAND.
    unfold read_bytes, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims]. unfold READ_BYTES_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (HEBe : hidc (rw_cells asegs m EB [CB 256 ej])) by exact HEB.
    assert (HDe : hidc (rw_cells asegs m D [CB (Z.to_nat n) junk])) by exact HDST.
    clear HEB HDST.
    ienterG. carve_frame 64%nat ST. do 23 zstep.
  (* [comment removed for export] *)
  pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MU with munch ?W _ _ =>
    assert (FWS : Forall (client_ivA FL CL) W)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
    assert (G0 : GIOA L RNG s CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
    assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
      by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
          apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end
  end.
  assert (HEB1 : rw_cells asegs m1 EB [CB 256 ej])
    by (eapply agrees_rw_cells; [exact AGa | exact HEBe | intros a Ha; eapply clocA_keeps; [exact EBL|]; cbn [cells_size csize Nat.add] in Ha; lia]).
  assert (HD1 : rw_cells asegs m1 D [CB (Z.to_nat n) junk])
    by (eapply agrees_rw_cells; [exact AGa | exact HDe | intros a Ha; eapply clocA_keeps; [exact DL|]; cbn [cells_size csize Nat.add] in Ha; lia]).
  pose proof (cobjA_keep0 _ _ _ _ _ _ _ _ _ _ _ _ _ OD G0 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AGa) ltac:(lia)) as ODk.
  pose proof (cobjA_keep0 _ _ _ _ _ _ _ _ _ _ _ _ _ OE G0 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AGa) ltac:(lia)) as OEk.
  clear MU WM FWS G'.
  name_sp sp (-64)%Z.
  apply evtF_done. eapply implMG_bind.
  { apply implMG_mget_l. rewrite HD.
    eapply FREAD with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (f := f) (Af := Af) (D := D) (n := n) (junk := junk);
      [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
        split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
        split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
      | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact HD1 | exact ODk ]. }
  intros got s' RNG1 ms' PO. cbv beta in PO.
  destruct PO as (FP1 & av & m2 & junk' & E & OF1 & MI1 & ST1 & AG1 & G1 & -> & GLn & GR & HD2).
  unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
  replace (ret_pc (Z_to_bv 64 572052)) with (Z_to_bv 64 572052) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
  assert (KEEP : forall A cs, rw_cells asegs m1 A cs -> (bv_unsigned sp + -64 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells asegs m2 A cs).
  { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG1 | exact HC | intros a Ha; split; [left; lia| lia]]. }
  apply KEEP in FR; [|lia|cbn [cells_size csize Nat.add]; lia].
  assert (HEB2 : rw_cells asegs m2 EB [CB 256 ej]).
  { eapply agrees_rw_cells; [exact AG1 | exact HEB1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    split; [eapply clocA_keeps; [exact EBL| lia] | lia]. }
  clear KEEP HEB1 HD1 MI.
  assert (AG02 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m2).
  { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGa| intros a [K _]; exact K]|].
    eapply agrees_on_weaken; [exact AG1|]. intros a [K [Hd _]]. split; [|exact Hd]. destruct K as [K|K]; [left; lia| right; exact K]. }
  clear AGa AG1 G0.
  unfold zlength in *.
  (* [comment removed for export] *)
  assert (KSH : forall mx, agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m mx ->
                agrees_on (in_frame_sh FL) m mx).
  { intros mx AGx. eapply (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ [(D, D + n); (EB, EB + 256)]%Z _ _ _ G (incl_refl _)).
    - eapply agrees_on_weaken; [exact AGx|]. intros a [K O]. cbn [outside fst snd] in O. split; [exact K| tauto].
    - apply Forall_cons; [exact DBAND|]. apply Forall_cons; [exact EBBAND| apply Forall_nil]. }
  (* [comment removed for export] *)
  assert (EXIT : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (x2' x3' : word) (m3 : mem) (ps3 : PState H hptr) (RNG3 : footprint) (st : rb_status) (sv : Z),
    fp_le RNG RNG3 -> mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -64) ->
    agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
    GIOA L RNG3 ps3 CL FB FL m3 -> ps_outfile ps3 = ps_outfile s ->
    rng RNG3 lo (bv_unsigned sp - lo) ->
    rw_cells asegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
    match st with
    | RBS_Ok => sv = 1%Z /\ Z.of_nat (length got) = n /\ rw_cells asegs m3 EB [CB 256 ej]
    | RBS_Eof => sv = 0%Z /\ Z.of_nat (length got) = 0%Z /\ foe = false /\ rw_cells asegs m3 EB [CB 256 ej]
    | RBS_Err msg => exists junk'', sv = (-1)%Z /\ rw_cells asegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''] /\ (Z.of_nat (length msg) < 256)%Z
                     /\ Forall (fun z => 0 < z < 256)%Z msg
    end ->
    evtF asegs RNG3 (POSTQ (st, got) ps3 RNG3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
               x2' x3' (Z_to_bv 64 sv) (Z_to_bv 64 Af) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x8bb08) fc None m3 (seg_rom asegs))).
  { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2' x3' m3 ps3 RNG3 st sv FP3 MI3 ST3 AG3 G3 OF3 RS3 FR3 HD3 HST.
    hide HD3. hide HST.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    do 11 zstep.
    release_frame FR3 ST3 (bv_unsigned sp).
    unhide HD3. unhide HST.
    apply evtF_done. subst POSTQ. unfold read_bytes_post. split; [exact FP3|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 sv), mm, junk' end.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF3|].
    split; [assumption|]. split; [assumption|]. split; [exact AG3|]. split; [exact G3|]. split; [exact HD3|].
    split; [exact GR|]. split; [unfold zlength; lia|].
    destruct st as [| |msg]; [destruct HST as (-> & E1 & X); auto| destruct HST as (-> & E1 & Ef & X); unfold zlength; auto| ].
    destruct HST as (j'' & -> & X & LM & OK). exists j''. auto. }
  (* [comment removed for export] *)
  assert (KSNP : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (x2' : word) (m3 : mem) (ps3 : PState H hptr) (RNG3 : footprint),
    fp_le RNG RNG3 -> mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -64) ->
    agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
    GIOA L RNG3 ps3 CL FB FL m3 -> ps_outfile ps3 = ps_outfile s ->
    rng RNG3 lo (al_top L - lo) -> rng_aimg RNG3 -> rng_aimg_sh RNG3 -> rng_atls RNG3 ->
    rw_cells asegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
    rw_cells asegs m3 EB [CB 256 ej] ->
    implMG RNG3 (mret (RBS_Err (Msg.trunc_pcapng n (Z.of_nat (length got))), got)) ps3 POSTQ
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
               x2' (Z_to_bv 64 (Z.of_nat (length got))) (Z_to_bv 64 1) (Z_to_bv 64 Af) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x8bae8) fc None m3 (seg_rom asegs))).
  { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2' m3 ps3 RNG3 FP3 MI3 ST3 AG3 G3 OF3 RS3 RI3 RH3 RT3 FR3 HD3 HEB3.
    apply implMG_ret. hide HD3. hide HEB3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    do 7 zstep.
    assert (MSG : fmt_at m3 FMT_TRUNC_PCAPNG_A "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
      by (unfold FMT_TRUNC_PCAPNG_A; split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x22300 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                               MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
          split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
    pose proof (cobjA_keep0 _ _ _ _ _ _ _ _ _ _ _ _ _ OE G3 (incl_refl _) (incl_refl _) (KSH _ AG3) ltac:(lia)) as OE3.
    unhide HEB3.
    name_sp sp (-64)%Z.
    eapply evtF_cut.
    { eapply SNPRINTF with (L := L) (s := ps3) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (DST := EB) (n := 256%Z) (FMTA := FMT_TRUNC_PCAPNG_A)
                           (fs := "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string) (args := [AInt n; AInt (Z.of_nat (length got))]) (junk := ej);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
          split; [exact RS3|]; split; [exact RI3|]; split; [exact RH3| exact RT3]
        | reflexivity | reflexivity | reflexivity | lia | exact MSG | reflexivity | cbn; lia
        | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | exact HEB3 | exact OE3 ]. }
    cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 572164)) with (Z_to_bv 64 572164) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

    unfold STDIO_STACK in MU4.
    pose proof G3 as G3'. rewrite <- (app_nil_r CL) in G3'.
    assert (FW4 : Forall (own_ivA [] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(bv_unsigned sp + -64 - 16384, bv_unsigned sp + -64)]%Z) by own_ivs.
    assert (FX4 : Forall (cobj_iv FL CL) [(EB, EB + 256)]%Z) by cobj_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ FW4 FX4 G3' MU4 WM4 ltac:(lia)) as [G4 AG4x].
    rewrite app_nil_r in G4. cbn [app] in G4.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -64 - 16384, bv_unsigned sp + -64); (EB, EB + 256)]%Z a) m3 m4)
      by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (FR4 : rw_cells asegs m4 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply agrees_rw_cells; [exact AGS | exact FR3 | intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia]).
    unhide HD3.
    assert (HD4 : rw_cells asegs m4 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']).
    { eapply agrees_rw_cells; [exact AGS | exact HD3 |]. intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *.
      assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia. lia. }
    assert (AG4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m4).
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AG4x|]. intros a [K [_ NE]]. split; [exact K|]. cbn [outside fst snd]. tauto. }
    change (Z.to_nat 256) with 256%nat in HEB4.
    hide HD4. hide HEB4.
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU5. pose proof (wmono_refl asegs m4) as WM5.
    zstep. unhide HD4. unhide HEB4.
    eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RBS_Err _) (-1)%Z); [exact FP3 | exact MI4 | exact ST4 | exact AG4 | exact G4 | exact OF3 | eapply rng_sub'; [exact RS3| lia] | exact FR4 | exact HD4 |].
    eexists. split; [reflexivity|]. unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE.
    pose proof (snprintf_length_le 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string [AInt n; AInt (Z.of_nat (length got))] ltac:(lia)) as LS.
    replace (256 - length (Fmt.snprintf 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu" [AInt n; AInt (Z.of_nat (length got))]) - 1)%nat
      with (255 - length (Fmt.snprintf 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu" [AInt n; AInt (Z.of_nat (length got))]))%nat in HEB4 by lia.
    split; [exact HEB4|]. split; [lia|]. apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2]. }
  (* [comment removed for export] *)
  destruct (Z.eq_dec (Z.of_nat (length got)) n) as [LEQ|LNE].
  { rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb]. apply implMG_ret.
    assert (EQT : bv_eqb (Z_to_bv 64 (Z.of_nat (length got))) (Z_to_bv 64 n) = true) by (rewrite LEQ; unfold bv_eqb; apply Z.eqb_refl).
    hide HD2. hide HEB2.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. rewrite EQT. cbv iota. unhide HD2. unhide HEB2.
    eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RBS_Ok 1%Z); [exact FP1 | exact MI1 | exact ST1 | exact AG02 | exact G1 | exact OF1 | exact RSPW | exact FR | exact HD2 |].
    cbn. split; [reflexivity|]. split; [exact LEQ| exact HEB2]. }
  rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
  hide HD2. hide HEB2.
  pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
  ienterG. zstep. rewrite (eqb_lits_false (Z.of_nat (length got)) n ltac:(lia) ltac:(lia) LNE). cbv iota. do 3 zstep. unhide HD2. unhide HEB2.
  clear MU WM.
  name_sp sp (-64)%Z.
  apply evtF_done. eapply implMG_bind.
  { eapply FERROR with (L := L) (s := s') (CL := CL) (FB := FB) (FL := FL) (lo := lo) (f := f) (Af := Af); [| exact HinF | reflexivity].
    split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
    split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
    split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
  intros e ps3 RNG2 ms3 PO. cbv beta in PO. destruct PO as (FP2 & av3 & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO).
  unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
  replace (ret_pc (Z_to_bv 64 572068)) with (Z_to_bv 64 572068) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
  apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG3) in FR; [|lia].
  assert (HD3 : rw_cells asegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']).
  { eapply agrees_rw_cells; [exact AG3 | exact HD2 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia.
    eapply clocA_keeps; [exact DL| lia]. }
  assert (HEB3 : rw_cells asegs m3 EB [CB 256 ej]).
  { eapply agrees_rw_cells; [exact AG3 | exact HEB2 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. eapply clocA_keeps; [exact EBL| lia]. }
  assert (AG03 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3).
  { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AG3|]. intros a [K _]. destruct K as [K|K]; [left; lia| right; exact K]. }
  assert (FP12 : fp_le RNG RNG2) by (eapply fp_le_trans; [exact FP1| exact FP2]).
  clear HD2 HEB2 AG3 MI1 ST1 G1.
  destruct e.
  - (* [comment removed for export] *)
    cbv iota. destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
    destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 RTLS) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
    assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
    assert (MSG : fmt_at m3 FMT_ERR_READING_A "error reading dump file"%string)
      by (unfold FMT_ERR_READING_A; split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x22080 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                               MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
          split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
    pose proof (cobjA_keep0 _ _ _ _ _ _ _ _ _ _ _ _ _ OE G3 (incl_refl _) (incl_refl _) (KSH _ AG03) ltac:(lia)) as OE3.
    apply implMG_errno_ll. set (err := lc_errno (ps_libc s')) in *.
    hide HD3. hide HEB3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    cbn [Z.b2z]. ienterG. zstep. if_false. do 4 zstep. rewrite ETP.
    ck TUNP 4%Z 0x8babc%Z [11%Z; 12%Z].
    zstep. do 5 zstep.
    replace (sx32 (Z_to_bv 64 err)) with (Z_to_bv 64 (s32 err)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
    unhide HEB3. clear MU WM.
    name_sp sp (-64)%Z.
    apply evtF_done. eapply implMG_bind.
    { eapply FMT with (L := L) (s := s') (CL := CL) (FB := FB) (FL := FL) (lo := lo) (EB := EB) (FMTA := FMT_ERR_READING_A) (e := err) (fs := "error reading dump file"%string)
                      (args := []) (junk := ej);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [lia|]; split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | apply NF; unfold frames_read_bytes; cbn; tauto
        | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia
        | cbn [length firstn]; constructor
        | exact HEB3 | exact OE3 | exact EB8 ]. }
    intros r sF RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & -> & PO). destruct_exs PO.
    destruct PO as (-> & OF3 & LC3 & TL3 & MI4 & ST4 & AG4 & G4 & HEB4).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 572116)) with (Z_to_bv 64 572116) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    lazymatch type of FR with rw_cells _ _ ?A ?cs =>
      lazymatch type of AG4 with agrees_on _ _ ?mm =>
        assert (FR4 : rw_cells asegs mm A cs) by (eapply agrees_rw_cells; [exact AG4 | exact FR |]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]) end end.
    clear FR. unhide HD3.
    lazymatch type of AG4 with agrees_on _ _ ?mm =>
      assert (HD4 : rw_cells asegs mm D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'])
        by (eapply agrees_rw_cells; [exact AG4 | exact HD3 |]; intros a Ha; cbn [cells_size csize Nat.add] in Ha;
            assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia;
            split; [eapply clocA_keeps; [exact DL| lia] | lia]);
      assert (AG04 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m mm)
        by (eapply agrees_on_trans; [exact AG03|]; eapply agrees_on_weaken; [exact AG4|]; intros a [K [_ NE]]; split; [|exact NE];
            destruct K as [K|K]; [left; lia| right; exact K]);
      pose proof (munch_refl ([] : list (Z * Z)) mm) as MU; pose proof (wmono_refl asegs mm) as WM
    end.
    hide HD4. hide HEB4.
    apply implMG_ret. do 2 zstep. unhide HD4. unhide HEB4.
    eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RBS_Err _) (-1)%Z);
      [eapply fp_le_trans; [exact FP12| exact FP3] | exact MI4 | exact ST4 | exact AG04 | exact G4 | congruence | eapply rng_sub'; [exact RSTK| lia] | exact FR4 | exact HD4 |].
    eexists. split; [reflexivity|]. split; [exact HEB4|]. split; [pose proof (fmt_errmsg_length "error reading dump file"%string [] err); lia|].
    apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor].
  - (* [comment removed for export] *)
    cbv iota. clear ERRNO.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    destruct foe.
    + (* [comment removed for export] *) cbn [negb andb]. rewrite Bool.andb_false_r.
      hide HD3. hide HEB3. cbn [Z.b2z]. ienterG. zstep. if_true. zstep. if_true. unhide HD3. unhide HEB3.
      apply evtF_done. apply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' RNG2 FP12 MI3 ST3 AG03 G3 OF1 RSTK RIMG RISH RTLS FR HD3 HEB3).
    + cbn [negb]. rewrite Bool.andb_true_r. cbn [Z.b2z].
      destruct (Nat.eq_dec (length got) 0) as [L0|L0].
      * (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_eq (Z.of_nat (length got)) 0) ltac:(lia)). apply implMG_ret.
        hide HD3. hide HEB3. zstep. if_true. zstep. if_false. zstep.
        replace (Z_to_bv 64 (Z.of_nat (length got))) with z64 by (rewrite L0; reflexivity). if_false. do 2 zstep. unhide HD3. unhide HEB3.
        eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RBS_Eof 0%Z); [exact FP12 | exact MI3 | exact ST3 | exact AG03 | exact G3 | exact OF1 | eapply rng_sub'; [exact RSTK| lia] | exact FR | exact HD3 |].
        cbn. split; [reflexivity|]. split; [lia|]. split; [reflexivity| exact HEB3].
      * (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq (Z.of_nat (length got)) 0) ltac:(lia)).
        hide HD3. hide HEB3. ienterG. zstep. if_true. zstep. if_false. zstep. rewrite (nez_true (Z.of_nat (length got))) by lia. cbv iota. unhide HD3. unhide HEB3.
        apply evtF_done. apply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' RNG2 FP12 MI3 ST3 AG03 G3 OF1 RSTK RIMG RISH RTLS FR HD3 HEB3).
  Qed.
  End Sz3.
  #[using="fflagA GL FREAD FERROR FMT SNPRINTF"] Theorem read_bytes_proofA : ltac:(let t := eval cbv delta [read_bytes_proofA__stmt] in read_bytes_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC f Af D n EB lo foe dest junk ej. ltac2:(SecDiet.SzSec.closeP 'read_bytes_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RB.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_sfchk_fsegA__B3P.SfAuxB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Definition FMT_ERR_READING_A : Z := 0x22080.   (* [comment removed for export] *)
Definition FMT_TRUNC_PCAPNG_A : Z := 0x22300.  (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section RB.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  (* [comment removed for export] *)
  Definition cobjA_keep0__stmt : Prop := forall L RNG RNG' s' CL CL' FB' FL FL' m m' A n,
    cobjA RNG m FL CL A n -> GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' ->
    agrees_on (in_frame_sh FL) m m' -> 0 <= n -> cobjA RNG' m' FL CL A n.
  Section Sz1.
  Variables L RNG RNG' s' CL CL' FB' FL FL' m m' A n : ltac2:(SecDiet.SzSec.tyM 'cobjA_keep0__stmt "vvvvvvvvvvvvv" @L).
  #[using="tlsI FO fflagA GL"] Lemma cobjA_keep0__body : ltac2:(SecDiet.SzSec.bodyP 'cobjA_keep0__stmt "vvvvvvvvvvvvv").
  Proof.
    intros O G' ICL IFL AG Hn.
    destruct (Z.eq_dec n 0) as [->|NZ]; [| eapply (cobjA_keep _ _ _ GL); try eassumption; lia].
    destruct O as [LOC (A0 & A47 & _)]. split; [exact LOC|].
    destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)].
    - eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G'| apply in_or_app; left; apply ICL; exact Hb] | exact H1 | exact H2 | lia].
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G') as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr (IFL _ Hf)) as FRA.
      eapply frameA_aobj; [exact FRA| exact H1| exact H2| lia|].
      split; [lia|]. split; [lia|]. intros; lia.
  Qed.
  End Sz1.
  #[using="tlsI FO fflagA GL"] Lemma cobjA_keep0 : ltac:(let t := eval cbv delta [cobjA_keep0__stmt] in cobjA_keep0__stmt in exact t).
  Proof. intros L RNG RNG' s' CL CL' FB' FL FL' m m' A n. ltac2:(SecDiet.SzSec.closeP 'cobjA_keep0__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_mget_l : forall {St A} RNG (k : St -> Monad.M St A) s Q ms, implMG RNG (k s) s Q ms -> implMG RNG (mbind mget k) s Q ms.
  Proof. intros St A RNG k s Q ms HH. exact HH. Qed.

  Definition read_bytes_proofA__stmt : Prop := read_bytes_stmt HO FO sites GIOA TP.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC f Af D n EB lo foe dest junk ej : ltac2:(SecDiet.SzSec.tyM 'read_bytes_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL FREAD FERROR FMT SNPRINTF"] Lemma read_bytes_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'read_bytes_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR NF HinF HD -> -> -> -> -> Hn HDST OD HEB OE DISJ EB8.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    unfold READ_BYTES_STACK, PCAP_L1_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rng_sp_window RSTK sp RSPW.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    pose proof (proj1 OE) as EBL. pose proof (proj1 OD) as DL.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL) as (EBLO & EBHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G DL) as (DLO & DHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL ltac:(lia)) as EBBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G DL ltac:(lia)) as DBAND.
    unfold read_bytes, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims]. unfold READ_BYTES_ENTRY.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (HEBe : hidc (rw_cells asegs m EB [CB 256 ej])) by exact HEB.
    assert (HDe : hidc (rw_cells asegs m D [CB (Z.to_nat n) junk])) by exact HDST.
    clear HEB HDST.
    ienterG. carve_frame 64%nat ST. do 23 zstep.
  (* [comment removed for export] *)
  pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MU with munch ?W _ _ =>
    assert (FWS : Forall (client_ivA FL CL) W)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
    assert (G0 : GIOA L RNG s CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
    assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
      by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
          apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end
  end.
  assert (HEB1 : rw_cells asegs m1 EB [CB 256 ej])
    by (eapply agrees_rw_cells; [exact AGa | exact HEBe | intros a Ha; eapply clocA_keeps; [exact EBL|]; cbn [cells_size csize Nat.add] in Ha; lia]).
  assert (HD1 : rw_cells asegs m1 D [CB (Z.to_nat n) junk])
    by (eapply agrees_rw_cells; [exact AGa | exact HDe | intros a Ha; eapply clocA_keeps; [exact DL|]; cbn [cells_size csize Nat.add] in Ha; lia]).
  pose proof (cobjA_keep0 _ _ _ _ _ _ _ _ _ _ _ _ _ OD G0 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AGa) ltac:(lia)) as ODk.
  pose proof (cobjA_keep0 _ _ _ _ _ _ _ _ _ _ _ _ _ OE G0 (incl_refl _) (incl_refl _) (keeps_frame_sh _ _ _ _ _ AGa) ltac:(lia)) as OEk.
  clear MU WM FWS G'.
  name_sp sp (-64)%Z.
  apply evtF_done. eapply implMG_bind.
  { apply implMG_mget_l. rewrite HD.
    eapply FREAD with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (f := f) (Af := Af) (D := D) (n := n) (junk := junk);
      [ split; [exact G0|]; split; [rewrite Hsp; exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
        split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
        split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
      | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact HD1 | exact ODk ]. }
  intros got s' RNG1 ms' PO. cbv beta in PO.
  destruct PO as (FP1 & av & m2 & junk' & E & OF1 & MI1 & ST1 & AG1 & G1 & -> & GLn & GR & HD2).
  unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
  replace (ret_pc (Z_to_bv 64 571952)) with (Z_to_bv 64 571952) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
  assert (KEEP : forall A cs, rw_cells asegs m1 A cs -> (bv_unsigned sp + -64 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= bv_unsigned sp)%Z -> rw_cells asegs m2 A cs).
  { intros A cs HC HA HB. eapply agrees_rw_cells; [exact AG1 | exact HC | intros a Ha; split; [left; lia| lia]]. }
  apply KEEP in FR; [|lia|cbn [cells_size csize Nat.add]; lia].
  assert (HEB2 : rw_cells asegs m2 EB [CB 256 ej]).
  { eapply agrees_rw_cells; [exact AG1 | exact HEB1 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    split; [eapply clocA_keeps; [exact EBL| lia] | lia]. }
  clear KEEP HEB1 HD1 MI.
  assert (AG02 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m2).
  { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGa| intros a [K _]; exact K]|].
    eapply agrees_on_weaken; [exact AG1|]. intros a [K [Hd _]]. split; [|exact Hd]. destruct K as [K|K]; [left; lia| right; exact K]. }
  clear AGa AG1 G0.
  unfold zlength in *.
  (* [comment removed for export] *)
  assert (KSH : forall mx, agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m mx ->
                agrees_on (in_frame_sh FL) m mx).
  { intros mx AGx. eapply (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ [(D, D + n); (EB, EB + 256)]%Z _ _ _ G (incl_refl _)).
    - eapply agrees_on_weaken; [exact AGx|]. intros a [K O]. cbn [outside fst snd] in O. split; [exact K| tauto].
    - apply Forall_cons; [exact DBAND|]. apply Forall_cons; [exact EBBAND| apply Forall_nil]. }
  (* [comment removed for export] *)
  assert (EXIT : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (x2' x3' : word) (m3 : mem) (ps3 : PState H hptr) (RNG3 : footprint) (st : rb_status) (sv : Z),
    fp_le RNG RNG3 -> mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -64) ->
    agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
    GIOA L RNG3 ps3 CL FB FL m3 -> ps_outfile ps3 = ps_outfile s ->
    rng RNG3 lo (bv_unsigned sp - lo) ->
    rw_cells asegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
    match st with
    | RBS_Ok => sv = 1%Z /\ Z.of_nat (length got) = n /\ rw_cells asegs m3 EB [CB 256 ej]
    | RBS_Eof => sv = 0%Z /\ Z.of_nat (length got) = 0%Z /\ foe = false /\ rw_cells asegs m3 EB [CB 256 ej]
    | RBS_Err msg => exists junk'', sv = (-1)%Z /\ rw_cells asegs m3 EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''] /\ (Z.of_nat (length msg) < 256)%Z
                     /\ Forall (fun z => 0 < z < 256)%Z msg
    end ->
    evtF asegs RNG3 (POSTQ (st, got) ps3 RNG3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
               x2' x3' (Z_to_bv 64 sv) (Z_to_bv 64 Af) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x8bab0) fc None m3 (seg_rom asegs))).
  { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2' x3' m3 ps3 RNG3 st sv FP3 MI3 ST3 AG3 G3 OF3 RS3 FR3 HD3 HST.
    hide HD3. hide HST.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    do 11 zstep.
    release_frame FR3 ST3 (bv_unsigned sp).
    unhide HD3. unhide HST.
    apply evtF_done. subst POSTQ. unfold read_bytes_post. split; [exact FP3|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 sv), mm, junk' end.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF3|].
    split; [assumption|]. split; [assumption|]. split; [exact AG3|]. split; [exact G3|]. split; [exact HD3|].
    split; [exact GR|]. split; [unfold zlength; lia|].
    destruct st as [| |msg]; [destruct HST as (-> & E1 & X); auto| destruct HST as (-> & E1 & Ef & X); unfold zlength; auto| ].
    destruct HST as (j'' & -> & X & LM & OK). exists j''. auto. }
  (* [comment removed for export] *)
  assert (KSNP : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (x2' : word) (m3 : mem) (ps3 : PState H hptr) (RNG3 : footprint),
    fp_le RNG RNG3 -> mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -64) ->
    agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3 ->
    GIOA L RNG3 ps3 CL FB FL m3 -> ps_outfile ps3 = ps_outfile s ->
    rng RNG3 lo (al_top L - lo) -> rng_aimg RNG3 -> rng_aimg_sh RNG3 -> rng_atls RNG3 ->
    rw_cells asegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
    rw_cells asegs m3 EB [CB 256 ej] ->
    implMG RNG3 (mret (RBS_Err (Msg.trunc_pcapng n (Z.of_nat (length got))), got)) ps3 POSTQ
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' (Z_to_bv 64 EB) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
               x2' (Z_to_bv 64 (Z.of_nat (length got))) (Z_to_bv 64 1) (Z_to_bv 64 Af) (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x8ba90) fc None m3 (seg_rom asegs))).
  { intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x2' m3 ps3 RNG3 FP3 MI3 ST3 AG3 G3 OF3 RS3 RI3 RH3 RT3 FR3 HD3 HEB3.
    apply implMG_ret. hide HD3. hide HEB3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    do 7 zstep.
    assert (MSG : fmt_at m3 FMT_TRUNC_PCAPNG_A "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string)
      by (unfold FMT_TRUNC_PCAPNG_A; split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x22300 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                               MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
          split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
    pose proof (cobjA_keep0 _ _ _ _ _ _ _ _ _ _ _ _ _ OE G3 (incl_refl _) (incl_refl _) (KSH _ AG3) ltac:(lia)) as OE3.
    unhide HEB3.
    name_sp sp (-64)%Z.
    eapply evtF_cut.
    { eapply SNPRINTF with (L := L) (s := ps3) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (DST := EB) (n := 256%Z) (FMTA := FMT_TRUNC_PCAPNG_A)
                           (fs := "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string) (args := [AInt n; AInt (Z.of_nat (length got))]) (junk := ej);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
          split; [exact RS3|]; split; [exact RI3|]; split; [exact RH3| exact RT3]
        | reflexivity | reflexivity | reflexivity | lia | exact MSG | reflexivity | cbn; lia
        | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
        | exact HEB3 | exact OE3 ]. }
    cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 572076)) with (Z_to_bv 64 572076) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

    unfold STDIO_STACK in MU4.
    pose proof G3 as G3'. rewrite <- (app_nil_r CL) in G3'.
    assert (FW4 : Forall (own_ivA [] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(bv_unsigned sp + -64 - 16384, bv_unsigned sp + -64)]%Z) by own_ivs.
    assert (FX4 : Forall (cobj_iv FL CL) [(EB, EB + 256)]%Z) by cobj_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ FW4 FX4 G3' MU4 WM4 ltac:(lia)) as [G4 AG4x].
    rewrite app_nil_r in G4. cbn [app] in G4.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -64 - 16384, bv_unsigned sp + -64); (EB, EB + 256)]%Z a) m3 m4)
      by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (FR4 : rw_cells asegs m4 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply agrees_rw_cells; [exact AGS | exact FR3 | intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia]).
    unhide HD3.
    assert (HD4 : rw_cells asegs m4 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']).
    { eapply agrees_rw_cells; [exact AGS | exact HD3 |]. intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *.
      assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia. lia. }
    assert (AG4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m4).
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AG4x|]. intros a [K [_ NE]]. split; [exact K|]. cbn [outside fst snd]. tauto. }
    change (Z.to_nat 256) with 256%nat in HEB4.
    hide HD4. hide HEB4.
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU5. pose proof (wmono_refl asegs m4) as WM5.
    zstep. unhide HD4. unhide HEB4.
    eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RBS_Err _) (-1)%Z); [exact FP3 | exact MI4 | exact ST4 | exact AG4 | exact G4 | exact OF3 | eapply rng_sub'; [exact RS3| lia] | exact FR4 | exact HD4 |].
    eexists. split; [reflexivity|]. unfold Msg.trunc_pcapng, PCAP_ERRBUF_SIZE.
    pose proof (snprintf_length_le 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu"%string [AInt n; AInt (Z.of_nat (length got))] ltac:(lia)) as LS.
    replace (256 - length (Fmt.snprintf 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu" [AInt n; AInt (Z.of_nat (length got))]) - 1)%nat
      with (255 - length (Fmt.snprintf 256 "truncated pcapng dump file; tried to read %zu bytes, only got %zu" [AInt n; AInt (Z.of_nat (length got))]))%nat in HEB4 by lia.
    split; [exact HEB4|]. split; [lia|]. apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2]. }
  (* [comment removed for export] *)
  destruct (Z.eq_dec (Z.of_nat (length got)) n) as [LEQ|LNE].
  { rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb]. apply implMG_ret.
    assert (EQT : bv_eqb (Z_to_bv 64 (Z.of_nat (length got))) (Z_to_bv 64 n) = true) by (rewrite LEQ; unfold bv_eqb; apply Z.eqb_refl).
    hide HD2. hide HEB2.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. rewrite EQT. cbv iota. unhide HD2. unhide HEB2.
    eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RBS_Ok 1%Z); [exact FP1 | exact MI1 | exact ST1 | exact AG02 | exact G1 | exact OF1 | exact RSPW | exact FR | exact HD2 |].
    cbn. split; [reflexivity|]. split; [exact LEQ| exact HEB2]. }
  rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
  hide HD2. hide HEB2.
  pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
  ienterG. zstep. rewrite (eqb_lits_false (Z.of_nat (length got)) n ltac:(lia) ltac:(lia) LNE). cbv iota. do 3 zstep. unhide HD2. unhide HEB2.
  clear MU WM.
  name_sp sp (-64)%Z.
  apply evtF_done. eapply implMG_bind.
  { eapply FERROR with (L := L) (s := s') (CL := CL) (FB := FB) (FL := FL) (lo := lo) (f := f) (Af := Af); [| exact HinF | reflexivity].
    split; [exact G1|]. split; [rewrite Hsp; exact ST1|]. split; [lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
    split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
    split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
  intros e ps3 RNG2 ms3 PO. cbv beta in PO. destruct PO as (FP2 & av3 & m3 & E & MI3 & ST3 & AG3 & G3 & -> & -> & ERRNO).
  unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
  replace (ret_pc (Z_to_bv 64 571968)) with (Z_to_bv 64 571968) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  repeat match goal with HR : rng RNG1 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
  apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG3) in FR; [|lia].
  assert (HD3 : rw_cells asegs m3 D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk']).
  { eapply agrees_rw_cells; [exact AG3 | exact HD2 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia.
    eapply clocA_keeps; [exact DL| lia]. }
  assert (HEB3 : rw_cells asegs m3 EB [CB 256 ej]).
  { eapply agrees_rw_cells; [exact AG3 | exact HEB2 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. eapply clocA_keeps; [exact EBL| lia]. }
  assert (AG03 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m m3).
  { eapply agrees_on_trans; [exact AG02|]. eapply agrees_on_weaken; [exact AG3|]. intros a [K _]. destruct K as [K|K]; [left; lia| right; exact K]. }
  assert (FP12 : fp_le RNG RNG2) by (eapply fp_le_trans; [exact FP1| exact FP2]).
  clear HD2 HEB2 AG3 MI1 ST1 G1.
  destruct e.
  - (* [comment removed for export] *)
    cbv iota. destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
    destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 RTLS) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
    assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
    assert (MSG : fmt_at m3 FMT_ERR_READING_A "error reading dump file"%string)
      by (unfold FMT_ERR_READING_A; split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x22080 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                               MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
          split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
    pose proof (cobjA_keep0 _ _ _ _ _ _ _ _ _ _ _ _ _ OE G3 (incl_refl _) (incl_refl _) (KSH _ AG03) ltac:(lia)) as OE3.
    apply implMG_errno_ll. set (err := lc_errno (ps_libc s')) in *.
    hide HD3. hide HEB3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    cbn [Z.b2z]. ienterG. zstep. if_false. do 4 zstep. rewrite ETP.
    (* [comment removed for export] *)
    ub_null. zstep. ub_al 3%Z ltac:(pose proof A3W.ABase.TwB.ATPv_pg as PG; unfold ATP in *; clear - PG; Z.div_mod_to_equations; lia). zstep. if_false.
    ck TUNP 4%Z 0x8ba64%Z [11%Z; 12%Z].
    zstep. do 5 zstep.
    replace (sx32 (Z_to_bv 64 err)) with (Z_to_bv 64 (s32 err)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
    unhide HEB3. clear MU WM.
    name_sp sp (-64)%Z.
    apply evtF_done. eapply implMG_bind.
    { eapply FMT with (L := L) (s := s') (CL := CL) (FB := FB) (FL := FL) (lo := lo) (EB := EB) (FMTA := FMT_ERR_READING_A) (e := err) (fs := "error reading dump file"%string)
                      (args := []) (junk := ej);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [lia|]; split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | apply NF; unfold frames_read_bytes; cbn; tauto
        | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia
        | cbn [length firstn]; constructor
        | exact HEB3 | exact OE3 | exact EB8 ]. }
    intros r sF RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & -> & PO). destruct_exs PO.
    destruct PO as (-> & OF3 & LC3 & TL3 & MI4 & ST4 & AG4 & G4 & HEB4).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 572028)) with (Z_to_bv 64 572028) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    lazymatch type of FR with rw_cells _ _ ?A ?cs =>
      lazymatch type of AG4 with agrees_on _ _ ?mm =>
        assert (FR4 : rw_cells asegs mm A cs) by (eapply agrees_rw_cells; [exact AG4 | exact FR |]; intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]) end end.
    clear FR. unhide HD3.
    lazymatch type of AG4 with agrees_on _ _ ?mm =>
      assert (HD4 : rw_cells asegs mm D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'])
        by (eapply agrees_rw_cells; [exact AG4 | exact HD3 |]; intros a Ha; cbn [cells_size csize Nat.add] in Ha;
            assert (X : (Z.of_nat (length got) + Z.of_nat (Z.to_nat n - length got) = n)%Z) by lia;
            split; [eapply clocA_keeps; [exact DL| lia] | lia]);
      assert (AG04 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n) /\ ~ (EB <= a < EB + 256))%Z m mm)
        by (eapply agrees_on_trans; [exact AG03|]; eapply agrees_on_weaken; [exact AG4|]; intros a [K [_ NE]]; split; [|exact NE];
            destruct K as [K|K]; [left; lia| right; exact K]);
      pose proof (munch_refl ([] : list (Z * Z)) mm) as MU; pose proof (wmono_refl asegs mm) as WM
    end.
    hide HD4. hide HEB4.
    apply implMG_ret. do 2 zstep. unhide HD4. unhide HEB4.
    eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RBS_Err _) (-1)%Z);
      [eapply fp_le_trans; [exact FP12| exact FP3] | exact MI4 | exact ST4 | exact AG04 | exact G4 | congruence | eapply rng_sub'; [exact RSTK| lia] | exact FR4 | exact HD4 |].
    eexists. split; [reflexivity|]. split; [exact HEB4|]. split; [pose proof (fmt_errmsg_length "error reading dump file"%string [] err); lia|].
    apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor].
  - (* [comment removed for export] *)
    cbv iota. clear ERRNO.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    destruct foe.
    + (* [comment removed for export] *) cbn [negb andb]. rewrite Bool.andb_false_r.
      hide HD3. hide HEB3. cbn [Z.b2z]. ienterG. zstep. if_true. zstep. if_true. unhide HD3. unhide HEB3.
      apply evtF_done. apply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' RNG2 FP12 MI3 ST3 AG03 G3 OF1 RSTK RIMG RISH RTLS FR HD3 HEB3).
    + cbn [negb]. rewrite Bool.andb_true_r. cbn [Z.b2z].
      destruct (Nat.eq_dec (length got) 0) as [L0|L0].
      * (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_eq (Z.of_nat (length got)) 0) ltac:(lia)). apply implMG_ret.
        hide HD3. hide HEB3. zstep. if_true. zstep. if_false. zstep.
        replace (Z_to_bv 64 (Z.of_nat (length got))) with z64 by (rewrite L0; reflexivity). if_false. do 2 zstep. unhide HD3. unhide HEB3.
        eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RBS_Eof 0%Z); [exact FP12 | exact MI3 | exact ST3 | exact AG03 | exact G3 | exact OF1 | eapply rng_sub'; [exact RSTK| lia] | exact FR | exact HD3 |].
        cbn. split; [reflexivity|]. split; [lia|]. split; [reflexivity| exact HEB3].
      * (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq (Z.of_nat (length got)) 0) ltac:(lia)).
        hide HD3. hide HEB3. ienterG. zstep. if_true. zstep. if_false. zstep. rewrite (nez_true (Z.of_nat (length got))) by lia. cbv iota. unhide HD3. unhide HEB3.
        apply evtF_done. apply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' RNG2 FP12 MI3 ST3 AG03 G3 OF1 RSTK RIMG RISH RTLS FR HD3 HEB3).
  Qed.
  End Sz3.
  #[using="fflagA GL FREAD FERROR FMT SNPRINTF"] Theorem read_bytes_proofA : ltac:(let t := eval cbv delta [read_bytes_proofA__stmt] in read_bytes_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC f Af D n EB lo foe dest junk ej. ltac2:(SecDiet.SzSec.closeP 'read_bytes_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End RB.
End CANSEC1.
End TwB.
End F_ngrbA.
