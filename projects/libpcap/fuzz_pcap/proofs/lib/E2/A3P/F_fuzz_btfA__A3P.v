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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pcap_open2A__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_fuzz_btfA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pcap_open2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA.
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
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Lemma sx32_smallA : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. all: natfold_lits.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn. rewrite Z.mod_small by lia. lia.
Qed.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FuzzBtf.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FWRITE : fwrite_stmt_o HO GIOA.
  Hypothesis REMOVE : remove_stmt_o GIOA.
  Hypothesis PRINTF_R : printf_d_stmt_o GIOA FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o GIOA FMT_FAILED_OPEN pieces_failed_open.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PR := (prims HO FO sites).

  #[using="Type"] Lemma implMG_errno_l : forall {B} (k : Z -> Monad.M PSt B) (s : PSt) RNG Q ms,
    implMG RNG (k (lc_errno (ps_libc s))) s Q ms -> implMG RNG (mbind (s_get_errno (H:=H) (hptr:=hptr)) k) s Q ms.
  Proof. all: natfold_lits. intros. exact H0. Qed.

  (* [comment removed for export] *)
  Definition datA (RNG : footprint) (m : mem) (CL : list cblk) (D : Z) (data : list byte) : Prop :=
    bytes_at asegs m D data /\ ((data = [] /\ 0x10040 <= D /\ D <= 0x602fc0)%Z \/ cobjA RNG m [] CL D (Z.of_nat (length data))).

  Definition datA_keep__stmt : Prop := forall L RNG RNG' s' (CL : list cblk) FB' FLa FL' SP D data m m',
    datA RNG m CL D data -> agrees_on (client_keeps FLa CL SP) m m' -> GIOA L RNG' s' CL FB' FL' m' -> datA RNG' m' CL D data.
  Section Sz3.
  Variables L RNG RNG' s' CL FB' FLa FL' SP D data m m' : ltac2:(SecDiet.SzSec.tyM 'datA_keep__stmt "vvvvvvvvvvvvv" @L).
  #[using="tlsI FO fflagA GL"] Lemma datA_keep__body : ltac2:(SecDiet.SzSec.bodyP 'datA_keep__stmt "vvvvvvvvvvvvv").
  Proof. all: natfold_lits.
    intros [DAT [(-> & DB)|OBJ]] AG G'.
    - split; [| left; split; [reflexivity| exact DB]]. eapply agrees_bytes_at; [exact AG| exact DAT|]. intros a Ha. cbn [length] in Ha. lia.
    - pose proof (proj1 OBJ) as LOC.
      split.
      + eapply agrees_bytes_at; [exact AG| exact DAT|]. intros a Ha. destruct LOC as [(b & Hb & H1 & H2)|(fr & [] & _)].
        right; left. apply in_block_In. exists b. split; [exact Hb| lia].
      + right. destruct data as [|d0 data'].
        * (* [comment removed for export] *)
          destruct OBJ as [_ (A0 & A47 & _ & RN & RS & AR & BK)]. cbn [length Z.of_nat] in *.
          destruct LOC as [(b & Hb & H1 & H2)|(fr & [] & _)].
          split; [left; exists b; split; [exact Hb| lia]|].
          eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G'| apply in_or_app; left; exact Hb]| lia| lia| lia].
        * eapply (cobjA_keep FO GIOA fflagA GL); [exact OBJ| exact G'| apply incl_refl| intros x []| intros a _ Ha; inversion Ha| cbn [length]; lia].
  Qed.
  End Sz3.
  #[using="tlsI FO fflagA GL"] Lemma datA_keep : ltac:(let t := eval cbv delta [datA_keep__stmt] in datA_keep__stmt in exact t).
  Proof. all: natfold_lits. intros L RNG RNG' s' CL FB' FLa FL' SP D data m m'. ltac2:(SecDiet.SzSec.closeP 'datA_keep__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma datA_src : forall RNG m (CL : list cblk) FL D data, datA RNG m CL D data ->
    ((data = [] /\ 0x10040 <= D /\ D <= 0x602fc0)%Z \/ cobjA RNG m FL CL D (Z.of_nat (length data))).
  Proof. all: natfold_lits.
    intros RNG m CL FL D data [_ [E|[LOC OBJ]]]; [left; exact E| right]. split; [| exact OBJ].
    eapply clocA_incl; [exact LOC| apply incl_refl| intros x []].
  Qed.

  (* [comment removed for export] *)
  Definition btf_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (lo SPA Fb : Z) (nbuf ej : list byte) (hpc pkc : cell) (trC : list Z) (m0 : mem)
      : Z -> PSt -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 t3 t4 t5 t6 m' fra',
      ms' = MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 0x5e0894) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) r21 r22 (Z_to_bv 64 (Fb + 352))
                    (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
               F (Z_to_bv 64 (if r <? 0 then 0x84a94 else 0x84954)) fc None m' (seg_rom asegs)
      /\ hrngA L RNG' lo /\ GIOA L RNG' s' CL FB (FZFL Fb) m'
      /\ hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra' m'
      /\ cells_size fra' = 56%nat /\ ((0 <= r)%Z -> exists j1 j2, fra' = [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2])
      /\ rw_cells asegs m' (Fb + 352) [CB 4096 nbuf] /\ rw_cells asegs m' (Fb + 32) [CB 256 ej]
      /\ rw_cells asegs m' (Fb + 4608) [hpc] /\ rw_cells asegs m' (Fb + 4576) [pkc]
      /\ ucallerA depth_fuzz_one L m' sp s0 ra trC
      /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m0 m' /\ ((r < 0)%Z \/ r = 0%Z).

  #[using="Type"] Lemma btf_postA_back : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 RNG1 CL FB lo SPA Fb nbuf ej hpc pkc trC m0 m1 r s' RNG' ms',
    fp_le RNG0 RNG1 -> agrees_on (client_keeps [] CL (bv_unsigned sp)) m0 m1 ->
    btf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG1 CL FB lo SPA Fb nbuf ej hpc pkc trC m1 r s' RNG' ms' ->
    btf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 CL FB lo SPA Fb nbuf ej hpc pkc trC m0 r s' RNG' ms'.
  Proof. all: natfold_lits.
    intros until ms'. intros FP AG. unfold btf_postA. all: natfold_lits. generalize [CB (Z.to_nat 4096) nbuf] as NBc. generalize [CB 256%nat ej] as EJc. intros EJc NBc (FP' & PO). destruct_exs PO. destruct PO as (E & HR & G & HC & FS & FJ & FN & EB & HPc & PKc & UC & AG2 & RR).
    split; [intros b j Hb; apply FP', FP; exact Hb|].
    do 20 eexists. split; [exact E|]. repeat (split; [eassumption|]). split; [eapply agrees_on_trans; [exact AG| exact AG2]| exact RR].
  Qed.
  (* [comment removed for export] *)
  Definition fz_fopen_part__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (lo SPA Fb D : Z) (m : mem) (fra : list cell) (nbuf ej : list byte) (hpc pkc : cell)
      (data : list byte) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    datA RNG m CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (fo <- s_fopen HO TMPNAME true ;;
                match fo with
                | None => e <- s_get_errno ;; s_printf (pieces_failed_open e) ;;; mret (-2)%Z
                | Some fd => n <- s_fwrite HO fd (map bv_unsigned data) ;; s_fclose HO fd ;;;
                             (if negb (n =? zlength (map bv_unsigned data))%Z then mret (-3)%Z else mret 0%Z)
                end) s
      (btf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB lo SPA Fb nbuf ej hpc pkc trC m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e0894) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) (Z_to_bv 64 (Fb + 352))
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84910) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra nbuf ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_fopen_part__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO GL GH HAL EQB FOPEN FCLOSE FWRITE PRINTF_O"] Lemma fz_fopen_part__body : ltac2:(SecDiet.SzSec.bodyP 'fz_fopen_part__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof. all: natfold_lits.
 intros HP HR G HC FRAS FN NB EBc HPc HP8 PKc PK8 UC TR DAT DLEN.
    (* [comment removed for export] *)
    assert (FNsz : hidc ((Fb + 352 + Z.of_nat (cells_size [CB (Z.to_nat 4096) nbuf]) <= Fb + 8192)%Z)) by (unfold hidc; cbn [cells_size csize Nat.add]; lia).
    assert (EBsz : hidc ((Fb + 32 + Z.of_nat (cells_size [CB 256%nat ej]) <= Fb + 8192)%Z)) by (unfold hidc; cbn [cells_size csize Nat.add]; lia).
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    destruct HC as (MI & ST & STG & FRA & FRs & (k0 & FK0) & FLG & SA & SB & SC). unfold SHA, SHB, SHC in SA, SB, SC.
    pose proof TR as (_ & TRF & TRC & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    band_ind FBAND bF.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jf FRA']. clear FRA. rewrite FRAS in FRA'.
    pose proof (munch_refl [(SPA, SPA + 56)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HC1 : hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                      [CB 24 (firstn 24 jf); C8 (Z_to_bv 64 Fb); CB 24 (skipn 32 jf)] mm) end.
    { split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [assumption|]. split; [exists k0; assumption|].
      split; [assumption|]. split; [exact SA|]. split; [exact SB| exact SC]. }
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    assert (FW : Forall (own_ivA (FZFL Fb) ([] : list cblk) (bv_unsigned sp)) [(SPA, SPA + 56)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FW (Forall_nil _) G' MU WM ltac:(lia)) as [G1 AG1] end.
    rewrite app_nil_r in G1. cbn [app] in G1.
    assert (AG1' : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m0) by (eapply agrees_on_weaken; [exact AG1| intros a K0; split; [exact K0| exact I]]).
    assert (UC1 : ucallerA depth_fuzz_one L m0 sp s0 ra trC).
    { eapply ucaller_keep; [exact UC| exact TOP47|]. intros a Ha. apply (AG1' a); [lia| left; lia]. }
    pose proof (datA_keep _ _ _ _ _ _ _ _ _ _ _ _ _ DAT AG1' G1) as DAT1.
    clear G' FW G UC DAT AG1.
    do 4 zstep.
    pose proof (name_bytes _ _ _ _ _ _ FN NB) as NBY.
    pose proof (fz_unp_fname _ _ SB ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UFN.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RB : bytes_at asegs mm 0x211a0 ([Z_to_bv 8 119; Z_to_bv 8 98] ++ [Z_to_bv 8 0]))
        by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x211a0 [Z_to_bv 8 119; Z_to_bv 8 98; Z_to_bv 8 0] ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))) end.
    rewrite <- tmpname_Z.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply implMG_leaf.
      eapply FOPEN with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := (Fb + 352)%Z) (MODE := 0x211a0%Z) (name := tmpname)
                        (md := [Z_to_bv 8 119; Z_to_bv 8 98]) (wr := true) (trC := bv_unsigned ra :: trC);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G1| assumption| assumption| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | eapply (fz_ucaller fflagA); [exact UC1| exact HP| exact HC1| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_fuzz_one; lia]
        | rewrite unsigned_lit by lia; exact TRF
        | reflexivity | reflexivity | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia | exact tmpname_open_w
        | apply cobjA_robjA; [| rewrite tmpname_len; lia];
          eapply (fz_cobj FO GIOA fflagA GL); [exact G1| lia| rewrite tmpname_len; lia| rewrite tmpname_len; lia| eapply unpoisoned_sub; [exact UFN| lia| rewrite tmpname_len; lia]]
        | exact RB | right; split; reflexivity
        | eapply (gia_global_robjA _ _ _ GL); [exact G1 | unfold client_globals; repeat (first [left; reflexivity | right]) | cbn; lia | exact RIMG | exact RISH] ]. }
    intros fo s2' RNG2 ms2 [PO LF]. cbv beta iota in PO.
    destruct fo as [f|].
    - (* [comment removed for export] *)
      destruct PO as (FP2 & a0v & m2 & E & OF2 & MI2 & ST2 & AG2 & (Af & -> & G2)). rewrite ESPA in *. post_regs E.
      apply (fopen_leaf HO EQB) in LF as [fd LK].
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; left; reflexivity)) as ((FBAND2 & _ & FTOP2 & _) & A1 & _).
      cbn [cb_addr cb_size fst snd] in FBAND2, FTOP2, A1. unfold FILE_BLOCK in FBAND2, FTOP2. clear FBAND2.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC1 G1 HP eq_refl eq_refl AG2 MI2 ST2) as HC2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN AG2 ltac:(lia) FNsz) as FN2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc AG2 ltac:(lia) EBsz) as EBc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc2.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC1 TOP47 AG2 ltac:(lia)) as UC2.
      pose proof (datA_keep _ _ _ _ _ _ _ _ _ _ _ _ _ DAT1 AG2 G2) as DAT2.
      hr_next HR FP2 HR2.
      clear MI ST STG FRA' FRs FK0 FLG SA SB SC FN EBc HPc PKc MU WM RB NBY UFN.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      ienterG. zstep. if_false_by (eqz_false Af ltac:(lia)). do 6 zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FWRITE with (L := L) (s := s2') (CL := CL) (FB := (f, Af, FILE_BLOCK) :: FB) (FL := FZFL Fb) (f := f) (Af := Af) (SRC := D) (lo := lo) (src := data);
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact (proj1 DAT2) | eapply datA_src; exact DAT2
          | intros fs Hfs; rewrite LK in Hfs; injection Hfs as <-; cbn [f_wbuf fdopen_file]; unfold zlength; cbn [length Z.of_nat]; lia ]. }
      intros n s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & a0v & m3 & E & OF3 & MI3 & ST3 & AG3 & G3 & -> & Hn). rewrite ESPA in *. post_regs E.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC2 G2 HP eq_refl eq_refl AG3 MI3 ST3) as HC3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN2 AG3 ltac:(lia) FNsz) as FN3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc2 AG3 ltac:(lia) EBsz) as EBc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc3.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC2 TOP47 AG3 ltac:(lia)) as UC3.
      hr_next HR2 FP3 HR3.
      clear MI2 MU WM FN2 EBc2 HPc2 PKc2.
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      ienterG. do 3 zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FCLOSE with (L := L) (s := s3') (CL := CL) (F1 := []) (F2 := FB) (FL := FZFL Fb) (f := f) (Af := Af) (lo := lo) (trC := bv_unsigned ra :: trC);
          [ cbn [app]; eapply (hpureA_spo GIOA); [exact HP| exact HR3| exact G3| exact ST3| exact MI3| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | eapply (fz_ucaller fflagA); [exact UC3| exact HP| exact HC3| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_fuzz_one; lia]
          | rewrite unsigned_lit by lia; exact TRC
          | reflexivity
          | eapply (new_file_not_out HO FO GIOA fflagA GL HAL GH); [exact G1 | exact G3 | congruence] ]. }
      intros [] s4' RNG4 ms4 PO. cbv beta in PO. destruct PO as (FP4 & a0v & m4 & E & OF4 & MI4 & ST4 & AG4 & G4). rewrite ESPA in *. post_regs E. cbn [app] in G4.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC3 G3 HP eq_refl eq_refl AG4 MI4 ST4) as HC4.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN3 AG4 ltac:(lia) FNsz) as FN4.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc3 AG4 ltac:(lia) EBsz) as EBc4.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc3 AG4 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc4.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc3 AG4 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc4.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC3 TOP47 AG4 ltac:(lia)) as UC4.
      hr_next HR3 FP4 HR4.
      assert (AGK : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m4).
      { eapply agrees_on_trans; [exact AG1'|]. eapply agrees_on_trans; [eapply fz_ag_final; [exact AG2| lia]|].
        eapply agrees_on_trans; eapply fz_ag_final; first [exact AG3| exact AG4| lia]. }
      replace (zlength (map bv_unsigned data)) with (Z.of_nat (length data)) by (unfold zlength; rewrite length_map; reflexivity).
      clear MI3 MU WM FN3 EBc3 HPc3 PKc3.
      pose proof HC4 as (MI4' & _ & _ & FRA4 & _).
      pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      ienterG. zstep. zstep.
      assert (FPK : fp_le RNG RNG4) by (intros b j Hb; apply FP4, FP3, FP2; exact Hb).
      destruct (Z.eqb_spec n (Z.of_nat (length data))) as [En|Nn].
      + subst n. unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb].
        apply evtF_done. subst POSTQ. apply implMG_ret. apply evtF_done.
        (* [comment removed for export] *)
        unfold btf_postA. all: natfold_lits. revert FN4 EBc4. generalize [CB (Z.to_nat 4096) nbuf] as NBc. generalize [CB 256%nat ej] as EJc. intros EJc NBc FN4 EBc4.
        split; [exact FPK|]. do 20 eexists. split; [reflexivity|]. split; [exact HR4|]. split; [exact G4|]. split; [exact HC4|]. split; [reflexivity|].
        split; [intros _; eexists; eexists; reflexivity|]. split; [exact FN4|]. split; [exact EBc4|]. split; [exact HPc4|]. split; [exact PKc4|].
        split; [exact UC4|]. split; [exact AGK| right; reflexivity].
      + rewrite (eqb_lits_false n (Z.of_nat (length data)) ltac:(lia) ltac:(lia) ltac:(lia)). cbn [negb].
        apply evtF_done. subst POSTQ. apply implMG_ret. apply evtF_done.
        (* [comment removed for export] *)
        unfold btf_postA. all: natfold_lits. revert FN4 EBc4. generalize [CB (Z.to_nat 4096) nbuf] as NBc. generalize [CB 256%nat ej] as EJc. intros EJc NBc FN4 EBc4.
        split; [exact FPK|]. do 20 eexists. split; [reflexivity|]. split; [exact HR4|]. split; [exact G4|]. split; [exact HC4|]. split; [reflexivity|].
        split; [intros K0; lia|]. split; [exact FN4|]. split; [exact EBc4|]. split; [exact HPc4|]. split; [exact PKc4|].
        split; [exact UC4|]. split; [exact AGK| left; lia].
    - (* [comment removed for export] *)
      destruct PO as (FP2 & a0v & m2 & E & OF2 & MI2 & ST2 & AG2 & -> & G2 & EN & ER). rewrite ESPA in *. post_regs E.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC1 G1 HP eq_refl eq_refl AG2 MI2 ST2) as HC2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN AG2 ltac:(lia) FNsz) as FN2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc AG2 ltac:(lia) EBsz) as EBc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc2.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC1 TOP47 AG2 ltac:(lia)) as UC2.
      hr_next HR FP2 HR2.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G2 ltac:(assumption)) as (T0 & T47' & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      set (e := lc_errno (ps_libc s2')) in *.
      clear MI ST STG FRA' FRs FK0 FLG SA SB SC FN EBc HPc PKc MU WM RB NBY UFN LF.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      ienterG. zstep. if_true. zstep. do 3 zstep. rewrite ETP.
      ck TUNP 4%Z 0x84a30%Z [11%Z; 12%Z].
      zstep. rewrite (sx32_smallA e) by lia. do 3 zstep.
      apply evtF_done. subst POSTQ. apply implMG_errno_l. fold e. eapply implMG_bind.
      { eapply PRINTF_O with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (v := e);
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | reflexivity | reflexivity | exact ER ]. }
      intros [] s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & a0v & m3 & E & OF3 & MI3 & ST3 & AG3 & G3). rewrite ESPA in *. post_regs E.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC2 G2 HP eq_refl eq_refl AG3 MI3 ST3) as HC3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN2 AG3 ltac:(lia) FNsz) as FN3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc2 AG3 ltac:(lia) EBsz) as EBc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc3.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC2 TOP47 AG3 ltac:(lia)) as UC3.
      hr_next HR2 FP3 HR3.
      assert (AGK : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m3).
      { eapply agrees_on_trans; [exact AG1'|]. eapply agrees_on_trans; eapply fz_ag_final; first [exact AG2| exact AG3| lia]. }
      clear MI2 MU WM FN2 EBc2 HPc2 PKc2 EN TUNP.
      pose proof HC3 as (MI3' & _ & _ & FRA3 & _).
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      ienterG. zstep. zstep.
      apply evtF_done. subst POSTQ. apply implMG_ret. apply evtF_done.
      (* [comment removed for export] *)
      unfold btf_postA. all: natfold_lits. revert FN3 EBc3. generalize [CB (Z.to_nat 4096) nbuf] as NBc. generalize [CB 256%nat ej] as EJc. intros EJc NBc FN3 EBc3.
      split; [intros b j Hb; apply FP3, FP2; exact Hb|]. do 20 eexists. split; [reflexivity|]. split; [exact HR3|]. split; [exact G3|]. split; [exact HC3|]. split; [reflexivity|].
      split; [intros K0; lia|]. split; [exact FN3|]. split; [exact EBc3|]. split; [exact HPc3|]. split; [exact PKc3|].
      split; [exact UC3|]. split; [exact AGK| left; lia].
  Qed.
  End Sz6.
  #[using="FO GL GH HAL EQB FOPEN FCLOSE FWRITE PRINTF_O"] Lemma fz_fopen_part : ltac:(let t := eval cbv delta [fz_fopen_part__stmt] in fz_fopen_part__stmt in exact t).
  Proof. all: natfold_lits. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra nbuf ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_fopen_part__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M PSt B) (g : B -> Monad.M PSt C) (s : PSt) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. all: natfold_lits. intros. exact H0. Qed.

  #[using="Type"] Lemma eqz_false_neg1 : bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0) = false.
  Proof. all: natfold_lits. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition fz_btf__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (lo SPA Fb D : Z) (m : mem) (fra : list cell) (nbuf ej : list byte) (hpc pkc : cell)
      (data : list byte) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    datA RNG m CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (bufferToFile MOps PR TMPNAME (map bv_unsigned data)) s
      (btf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB lo SPA Fb nbuf ej hpc pkc trC m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e0894) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) (Z_to_bv 64 (Fb + 352))
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x848e4) fc None m (seg_rom asegs)).
  Section Sz9.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra nbuf ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_btf__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL GH HAL EQB FOPEN FCLOSE FWRITE REMOVE PRINTF_R PRINTF_O"] Lemma fz_btf__body : ltac2:(SecDiet.SzSec.bodyP 'fz_btf__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof. all: natfold_lits.
 intros HP HR G HC FRAS FN NB EBc HPc HP8 PKc PK8 UC TR DAT DLEN.
    (* [comment removed for export] *)
    assert (FNsz : hidc ((Fb + 352 + Z.of_nat (cells_size [CB (Z.to_nat 4096) nbuf]) <= Fb + 8192)%Z)) by (unfold hidc; cbn [cells_size csize Nat.add]; lia).
    assert (EBsz : hidc ((Fb + 32 + Z.of_nat (cells_size [CB 256%nat ej]) <= Fb + 8192)%Z)) by (unfold hidc; cbn [cells_size csize Nat.add]; lia).
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _ & _ & _ & _ & _ & _ & SB & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    pose proof (name_bytes _ _ _ _ _ _ FN NB) as NBY.
    pose proof (fz_unp_fname _ _ SB ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UFN.
    unfold bufferToFile. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_remove e_last_errno e_printf e_fopen_w e_fwrite e_fclose prims].
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. zstep. zstep.
    rewrite <- tmpname_Z.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply REMOVE with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := (Fb + 352)%Z) (name := tmpname);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | reflexivity | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia
        | eapply (fz_cobj FO GIOA fflagA GL); [exact G| lia| rewrite tmpname_len; lia| rewrite tmpname_len; lia| eapply unpoisoned_sub; [exact UFN| lia| rewrite tmpname_len; lia]]
        | exact tmpname_ok ]. }
    intros r s2' RNG2 ms2 PO. cbv beta in PO. destruct PO as (FP2 & a0v & m2 & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & Hr). rewrite ESPA in *. post_regs E.
    rewrite tmpname_Z.
    pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC G HP FRAS eq_refl AG2 MI2 ST2) as HC2.
    pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN AG2 ltac:(lia) FNsz) as FN2.
    pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc AG2 ltac:(lia) EBsz) as EBc2.
    pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc2.
    pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc2.
    pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC TOP47 AG2 ltac:(lia)) as UC2.
    pose proof (datA_keep _ _ _ _ _ _ _ _ _ _ _ _ _ DAT AG2 G2) as DAT2.
    hr_next HR FP2 HR2.
    assert (AGK2 : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m2) by (eapply fz_ag_final; [exact AG2| lia]).
    clear MI MU WM FN EBc HPc PKc NBY UFN SB UC DAT.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    destruct Hr as [-> | (-> & EN & ER)].
    - (* [comment removed for export] *)
      ienterG. zstep. if_true. apply evtF_done. subst POSTQ.
      cbn [Z.eqb negb]. apply implMG_retb. cbn [negb].
      eapply implMG_mono; [| intros r1 sx RNGx msx PO; eapply btf_postA_back with (RNG1 := RNG2) (m1 := m2); [exact FP2| exact AGK2| exact PO]].
      eapply fz_fopen_part; [exact HP| exact HR2| exact G2| exact HC2| exact FRAS| exact FN2| exact NB| exact EBc2| exact HPc2| exact HP8| exact PKc2| exact PK8
                            | exact UC2| exact TR| exact DAT2| exact DLEN].
    - (* [comment removed for export] *)
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G2 ltac:(assumption)) as (T0 & T47' & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      set (e := lc_errno (ps_libc s2')) in *.
      ienterG. zstep. if_false_by (eqz_false_neg1). zstep. do 3 zstep. rewrite ETP.
      ck TUNP 4%Z 0x84904%Z [11%Z; 12%Z].
      zstep. rewrite (sx32_smallA e) by lia. zstep. zstep.
      clear TUNP EN.
      destruct (Z.eqb_spec e 2) as [E2|NE2].
      + (* [comment removed for export] *)
        rewrite E2. unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
        apply evtF_done. subst POSTQ. cbn [Z.eqb negb]. apply implMG_errno_ll. cbv beta. fold e. rewrite E2. unfold ENOENT. cbn [Z.eqb negb].
        apply implMG_retb. cbn [negb].
        eapply implMG_mono; [| intros r1 sx RNGx msx PO; eapply btf_postA_back with (RNG1 := RNG2) (m1 := m2); [exact FP2| exact AGK2| exact PO]].
        eapply fz_fopen_part; [exact HP| exact HR2| exact G2| exact HC2| exact FRAS| exact FN2| exact NB| exact EBc2| exact HPc2| exact HP8| exact PKc2| exact PK8
                              | exact UC2| exact TR| exact DAT2| exact DLEN].
      + (* [comment removed for export] *)
        rewrite (eqb_lits_false e 2 ltac:(lia) ltac:(lia) ltac:(lia)). cbn [negb]. cbv iota.
        do 3 zstep.
        apply evtF_done. subst POSTQ. cbn [Z.eqb negb]. apply implMG_errno_ll. cbv beta. fold e.
        replace (negb (e =? ENOENT)%Z) with true by (unfold ENOENT; destruct (Z.eqb_spec e 2); [lia| reflexivity]).
        apply implMG_bind_assoc. cbv beta.
        eapply implMG_bind.
        { eapply PRINTF_R with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (v := e);
            [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
            | reflexivity | reflexivity | exact ER ]. }
        intros [] s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & a0v & m3 & E & OF3 & MI3 & ST3 & AG3 & G3). rewrite ESPA in *. post_regs E.
        pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC2 G2 HP FRAS eq_refl AG3 MI3 ST3) as HC3.
        pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN2 AG3 ltac:(lia) FNsz) as FN3.
        pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc2 AG3 ltac:(lia) EBsz) as EBc3.
        pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc3.
        pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc3.
        pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC2 TOP47 AG3 ltac:(lia)) as UC3.
        hr_next HR2 FP3 HR3.
        clear MI2 MU WM FN2 EBc2 HPc2 PKc2.
        pose proof HC3 as (MI3' & _).
        pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        apply implMG_retb. cbn [negb].
        ienterG. zstep.
        apply evtF_done. subst POSTQ. apply implMG_ret. apply evtF_done.
        (* [comment removed for export] *)
        unfold btf_postA. all: natfold_lits. revert FN3 EBc3. generalize [CB (Z.to_nat 4096) nbuf] as NBc. generalize [CB 256%nat ej] as EJc. intros EJc NBc FN3 EBc3.
        split; [intros b j Hb; apply FP3, FP2; exact Hb|]. do 20 eexists. split; [reflexivity|]. split; [exact HR3|]. split; [exact G3|]. split; [exact HC3|]. split; [exact FRAS|].
        split; [intros K0; lia|]. split; [exact FN3|]. split; [exact EBc3|]. split; [exact HPc3|]. split; [exact PKc3|].
        split; [exact UC3|]. split; [eapply agrees_on_trans; [exact AGK2| eapply fz_ag_final; [exact AG3| lia]]| left; lia].
  Qed.
  End Sz9.
  #[using="GL GH HAL EQB FOPEN FCLOSE FWRITE REMOVE PRINTF_R PRINTF_O"] Lemma fz_btf : ltac:(let t := eval cbv delta [fz_btf__stmt] in fz_btf__stmt in exact t).
  Proof. all: natfold_lits. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra nbuf ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_btf__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzBtf.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Lemma sx32_smallA : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. all: natfold_lits.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn. rewrite Z.mod_small by lia. lia.
Qed.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FuzzBtf.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FWRITE : fwrite_stmt_o HO GIOA.
  Hypothesis REMOVE : remove_stmt_o GIOA.
  Hypothesis PRINTF_R : printf_d_stmt_o GIOA FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o GIOA FMT_FAILED_OPEN pieces_failed_open.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PR := (prims HO FO sites).

  #[using="Type"] Lemma implMG_errno_l : forall {B} (k : Z -> Monad.M PSt B) (s : PSt) RNG Q ms,
    implMG RNG (k (lc_errno (ps_libc s))) s Q ms -> implMG RNG (mbind (s_get_errno (H:=H) (hptr:=hptr)) k) s Q ms.
  Proof. all: natfold_lits. intros. exact H0. Qed.

  (* [comment removed for export] *)
  Definition datA (RNG : footprint) (m : mem) (CL : list cblk) (D : Z) (data : list byte) : Prop :=
    bytes_at asegs m D data /\ ((data = [] /\ 0x10040 <= D /\ D <= 0x603fc0)%Z \/ cobjA RNG m [] CL D (Z.of_nat (length data))).

  Definition datA_keep__stmt : Prop := forall L RNG RNG' s' (CL : list cblk) FB' FLa FL' SP D data m m',
    datA RNG m CL D data -> agrees_on (client_keeps FLa CL SP) m m' -> GIOA L RNG' s' CL FB' FL' m' -> datA RNG' m' CL D data.
  Section Sz3.
  Variables L RNG RNG' s' CL FB' FLa FL' SP D data m m' : ltac2:(SecDiet.SzSec.tyM 'datA_keep__stmt "vvvvvvvvvvvvv" @L).
  #[using="tlsI FO fflagA GL"] Lemma datA_keep__body : ltac2:(SecDiet.SzSec.bodyP 'datA_keep__stmt "vvvvvvvvvvvvv").
  Proof. all: natfold_lits.
    intros [DAT [(-> & DB)|OBJ]] AG G'.
    - split; [| left; split; [reflexivity| exact DB]]. eapply agrees_bytes_at; [exact AG| exact DAT|]. intros a Ha. cbn [length] in Ha. lia.
    - pose proof (proj1 OBJ) as LOC.
      split.
      + eapply agrees_bytes_at; [exact AG| exact DAT|]. intros a Ha. destruct LOC as [(b & Hb & H1 & H2)|(fr & [] & _)].
        right; left. apply in_block_In. exists b. split; [exact Hb| lia].
      + right. destruct data as [|d0 data'].
        * (* [comment removed for export] *)
          destruct OBJ as [_ (A0 & A47 & _ & RN & RS & AR & BK)]. cbn [length Z.of_nat] in *.
          destruct LOC as [(b & Hb & H1 & H2)|(fr & [] & _)].
          split; [left; exists b; split; [exact Hb| lia]|].
          eapply blockA_aobj; [eapply (gl_block _ _ _ GL); [exact G'| apply in_or_app; left; exact Hb]| lia| lia| lia].
        * eapply (cobjA_keep FO GIOA fflagA GL); [exact OBJ| exact G'| apply incl_refl| intros x []| intros a _ Ha; inversion Ha| cbn [length]; lia].
  Qed.
  End Sz3.
  #[using="tlsI FO fflagA GL"] Lemma datA_keep : ltac:(let t := eval cbv delta [datA_keep__stmt] in datA_keep__stmt in exact t).
  Proof. all: natfold_lits. intros L RNG RNG' s' CL FB' FLa FL' SP D data m m'. ltac2:(SecDiet.SzSec.closeP 'datA_keep__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma datA_src : forall RNG m (CL : list cblk) FL D data, datA RNG m CL D data ->
    ((data = [] /\ 0x10040 <= D /\ D <= 0x603fc0)%Z \/ cobjA RNG m FL CL D (Z.of_nat (length data))).
  Proof. all: natfold_lits.
    intros RNG m CL FL D data [_ [E|[LOC OBJ]]]; [left; exact E| right]. split; [| exact OBJ].
    eapply clocA_incl; [exact LOC| apply incl_refl| intros x []].
  Qed.

  (* [comment removed for export] *)
  Definition btf_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (lo SPA Fb : Z) (nbuf ej : list byte) (hpc pkc : cell) (trC : list Z) (m0 : mem)
      : Z -> PSt -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 t3 t4 t5 t6 m' fra',
      ms' = MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 0x5e08fc) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) r21 r22 (Z_to_bv 64 (Fb + 352))
                    (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
               F (Z_to_bv 64 (if r <? 0 then 0x84acc else 0x849c8)) fc None m' (seg_rom asegs)
      /\ hrngA L RNG' lo /\ GIOA L RNG' s' CL FB (FZFL Fb) m'
      /\ hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra' m'
      /\ cells_size fra' = 56%nat /\ ((0 <= r)%Z -> exists j1 j2, fra' = [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2])
      /\ rw_cells asegs m' (Fb + 352) [CB 4096 nbuf] /\ rw_cells asegs m' (Fb + 32) [CB 256 ej]
      /\ rw_cells asegs m' (Fb + 4608) [hpc] /\ rw_cells asegs m' (Fb + 4576) [pkc]
      /\ ucallerA depth_fuzz_one L m' sp s0 ra trC
      /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m0 m' /\ ((r < 0)%Z \/ r = 0%Z).

  #[using="Type"] Lemma btf_postA_back : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 RNG1 CL FB lo SPA Fb nbuf ej hpc pkc trC m0 m1 r s' RNG' ms',
    fp_le RNG0 RNG1 -> agrees_on (client_keeps [] CL (bv_unsigned sp)) m0 m1 ->
    btf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG1 CL FB lo SPA Fb nbuf ej hpc pkc trC m1 r s' RNG' ms' ->
    btf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 CL FB lo SPA Fb nbuf ej hpc pkc trC m0 r s' RNG' ms'.
  Proof. all: natfold_lits.
    intros until ms'. intros FP AG. unfold btf_postA. all: natfold_lits. generalize [CB (Z.to_nat 4096) nbuf] as NBc. generalize [CB 256%nat ej] as EJc. intros EJc NBc (FP' & PO). destruct_exs PO. destruct PO as (E & HR & G & HC & FS & FJ & FN & EB & HPc & PKc & UC & AG2 & RR).
    split; [intros b j Hb; apply FP', FP; exact Hb|].
    do 20 eexists. split; [exact E|]. repeat (split; [eassumption|]). split; [eapply agrees_on_trans; [exact AG| exact AG2]| exact RR].
  Qed.
  (* [comment removed for export] *)
  Definition fz_fopen_part__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (lo SPA Fb D : Z) (m : mem) (fra : list cell) (nbuf ej : list byte) (hpc pkc : cell)
      (data : list byte) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    datA RNG m CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (fo <- s_fopen HO TMPNAME true ;;
                match fo with
                | None => e <- s_get_errno ;; s_printf (pieces_failed_open e) ;;; mret (-2)%Z
                | Some fd => n <- s_fwrite HO fd (map bv_unsigned data) ;; s_fclose HO fd ;;;
                             (if negb (n =? zlength (map bv_unsigned data))%Z then mret (-3)%Z else mret 0%Z)
                end) s
      (btf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB lo SPA Fb nbuf ej hpc pkc trC m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e08fc) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) (Z_to_bv 64 (Fb + 352))
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84984) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra nbuf ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_fopen_part__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="FO GL GH HAL EQB FOPEN FCLOSE FWRITE PRINTF_O"] Lemma fz_fopen_part__body : ltac2:(SecDiet.SzSec.bodyP 'fz_fopen_part__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof. all: natfold_lits.
 intros HP HR G HC FRAS FN NB EBc HPc HP8 PKc PK8 UC TR DAT DLEN.
    (* [comment removed for export] *)
    assert (FNsz : hidc ((Fb + 352 + Z.of_nat (cells_size [CB (Z.to_nat 4096) nbuf]) <= Fb + 8192)%Z)) by (unfold hidc; cbn [cells_size csize Nat.add]; lia).
    assert (EBsz : hidc ((Fb + 32 + Z.of_nat (cells_size [CB 256%nat ej]) <= Fb + 8192)%Z)) by (unfold hidc; cbn [cells_size csize Nat.add]; lia).
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    destruct HC as (MI & ST & STG & FRA & FRs & (k0 & FK0) & FLG & SA & SB & SC). unfold SHA, SHB, SHC in SA, SB, SC.
    pose proof TR as (_ & TRF & TRC & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    band_ind FBAND bF.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jf FRA']. clear FRA. rewrite FRAS in FRA'.
    pose proof (munch_refl [(SPA, SPA + 56)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HC1 : hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                      [CB 24 (firstn 24 jf); C8 (Z_to_bv 64 Fb); CB 24 (skipn 32 jf)] mm) end.
    { split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [assumption|]. split; [exists k0; assumption|].
      split; [assumption|]. split; [exact SA|]. split; [exact SB| exact SC]. }
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    assert (FW : Forall (own_ivA (FZFL Fb) ([] : list cblk) (bv_unsigned sp)) [(SPA, SPA + 56)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FW (Forall_nil _) G' MU WM ltac:(lia)) as [G1 AG1] end.
    rewrite app_nil_r in G1. cbn [app] in G1.
    assert (AG1' : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m0) by (eapply agrees_on_weaken; [exact AG1| intros a K0; split; [exact K0| exact I]]).
    assert (UC1 : ucallerA depth_fuzz_one L m0 sp s0 ra trC).
    { eapply ucaller_keep; [exact UC| exact TOP47|]. intros a Ha. apply (AG1' a); [lia| left; lia]. }
    pose proof (datA_keep _ _ _ _ _ _ _ _ _ _ _ _ _ DAT AG1' G1) as DAT1.
    clear G' FW G UC DAT AG1.
    do 4 zstep.
    pose proof (name_bytes _ _ _ _ _ _ FN NB) as NBY.
    pose proof (fz_unp_fname _ _ SB ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UFN.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RB : bytes_at asegs mm 0x211a0 ([Z_to_bv 8 119; Z_to_bv 8 98] ++ [Z_to_bv 8 0]))
        by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x211a0 [Z_to_bv 8 119; Z_to_bv 8 98; Z_to_bv 8 0] ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))) end.
    rewrite <- tmpname_Z.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply implMG_leaf.
      eapply FOPEN with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := (Fb + 352)%Z) (MODE := 0x211a0%Z) (name := tmpname)
                        (md := [Z_to_bv 8 119; Z_to_bv 8 98]) (wr := true) (trC := bv_unsigned ra :: trC);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G1| assumption| assumption| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | eapply (fz_ucaller fflagA); [exact UC1| exact HP| exact HC1| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_fuzz_one; lia]
        | rewrite unsigned_lit by lia; exact TRF
        | reflexivity | reflexivity | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia | exact tmpname_open_w
        | apply cobjA_robjA; [| rewrite tmpname_len; lia];
          eapply (fz_cobj FO GIOA fflagA GL); [exact G1| lia| rewrite tmpname_len; lia| rewrite tmpname_len; lia| eapply unpoisoned_sub; [exact UFN| lia| rewrite tmpname_len; lia]]
        | exact RB | right; split; reflexivity
        | eapply (gia_global_robjA _ _ _ GL); [exact G1 | unfold client_globals; repeat (first [left; reflexivity | right]) | cbn; lia | exact RIMG | exact RISH] ]. }
    intros fo s2' RNG2 ms2 [PO LF]. cbv beta iota in PO.
    destruct fo as [f|].
    - (* [comment removed for export] *)
      destruct PO as (FP2 & a0v & m2 & E & OF2 & MI2 & ST2 & AG2 & (Af & -> & G2)). rewrite ESPA in *. post_regs E.
      apply (fopen_leaf HO EQB) in LF as [fd LK].
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; left; reflexivity)) as ((FBAND2 & _ & FTOP2 & _) & A1 & _).
      cbn [cb_addr cb_size fst snd] in FBAND2, FTOP2, A1. unfold FILE_BLOCK in FBAND2, FTOP2. clear FBAND2.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC1 G1 HP eq_refl eq_refl AG2 MI2 ST2) as HC2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN AG2 ltac:(lia) FNsz) as FN2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc AG2 ltac:(lia) EBsz) as EBc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc2.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC1 TOP47 AG2 ltac:(lia)) as UC2.
      pose proof (datA_keep _ _ _ _ _ _ _ _ _ _ _ _ _ DAT1 AG2 G2) as DAT2.
      hr_next HR FP2 HR2.
      clear MI ST STG FRA' FRs FK0 FLG SA SB SC FN EBc HPc PKc MU WM RB NBY UFN.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      ienterG. zstep. if_false_by (eqz_false Af ltac:(lia)). do 6 zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FWRITE with (L := L) (s := s2') (CL := CL) (FB := (f, Af, FILE_BLOCK) :: FB) (FL := FZFL Fb) (f := f) (Af := Af) (SRC := D) (lo := lo) (src := data);
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact (proj1 DAT2) | eapply datA_src; exact DAT2
          | intros fs Hfs; rewrite LK in Hfs; injection Hfs as <-; cbn [f_wbuf fdopen_file]; unfold zlength; cbn [length Z.of_nat]; lia ]. }
      intros n s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & a0v & m3 & E & OF3 & MI3 & ST3 & AG3 & G3 & -> & Hn). rewrite ESPA in *. post_regs E.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC2 G2 HP eq_refl eq_refl AG3 MI3 ST3) as HC3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN2 AG3 ltac:(lia) FNsz) as FN3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc2 AG3 ltac:(lia) EBsz) as EBc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc3.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC2 TOP47 AG3 ltac:(lia)) as UC3.
      hr_next HR2 FP3 HR3.
      clear MI2 MU WM FN2 EBc2 HPc2 PKc2.
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      ienterG. do 3 zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FCLOSE with (L := L) (s := s3') (CL := CL) (F1 := []) (F2 := FB) (FL := FZFL Fb) (f := f) (Af := Af) (lo := lo) (trC := bv_unsigned ra :: trC);
          [ cbn [app]; eapply (hpureA_spo GIOA); [exact HP| exact HR3| exact G3| exact ST3| exact MI3| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | eapply (fz_ucaller fflagA); [exact UC3| exact HP| exact HC3| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_fuzz_one; lia]
          | rewrite unsigned_lit by lia; exact TRC
          | reflexivity
          | eapply (new_file_not_out HO FO GIOA fflagA GL HAL GH); [exact G1 | exact G3 | congruence] ]. }
      intros [] s4' RNG4 ms4 PO. cbv beta in PO. destruct PO as (FP4 & a0v & m4 & E & OF4 & MI4 & ST4 & AG4 & G4). rewrite ESPA in *. post_regs E. cbn [app] in G4.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC3 G3 HP eq_refl eq_refl AG4 MI4 ST4) as HC4.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN3 AG4 ltac:(lia) FNsz) as FN4.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc3 AG4 ltac:(lia) EBsz) as EBc4.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc3 AG4 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc4.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc3 AG4 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc4.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC3 TOP47 AG4 ltac:(lia)) as UC4.
      hr_next HR3 FP4 HR4.
      assert (AGK : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m4).
      { eapply agrees_on_trans; [exact AG1'|]. eapply agrees_on_trans; [eapply fz_ag_final; [exact AG2| lia]|].
        eapply agrees_on_trans; eapply fz_ag_final; first [exact AG3| exact AG4| lia]. }
      replace (zlength (map bv_unsigned data)) with (Z.of_nat (length data)) by (unfold zlength; rewrite length_map; reflexivity).
      clear MI3 MU WM FN3 EBc3 HPc3 PKc3.
      pose proof HC4 as (MI4' & _ & _ & FRA4 & _).
      pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      ienterG. zstep. zstep.
      assert (FPK : fp_le RNG RNG4) by (intros b j Hb; apply FP4, FP3, FP2; exact Hb).
      destruct (Z.eqb_spec n (Z.of_nat (length data))) as [En|Nn].
      + subst n. unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb].
        apply evtF_done. subst POSTQ. apply implMG_ret. apply evtF_done.
        (* [comment removed for export] *)
        unfold btf_postA. all: natfold_lits. revert FN4 EBc4. generalize [CB (Z.to_nat 4096) nbuf] as NBc. generalize [CB 256%nat ej] as EJc. intros EJc NBc FN4 EBc4.
        split; [exact FPK|]. do 20 eexists. split; [reflexivity|]. split; [exact HR4|]. split; [exact G4|]. split; [exact HC4|]. split; [reflexivity|].
        split; [intros _; eexists; eexists; reflexivity|]. split; [exact FN4|]. split; [exact EBc4|]. split; [exact HPc4|]. split; [exact PKc4|].
        split; [exact UC4|]. split; [exact AGK| right; reflexivity].
      + rewrite (eqb_lits_false n (Z.of_nat (length data)) ltac:(lia) ltac:(lia) ltac:(lia)). cbn [negb].
        apply evtF_done. subst POSTQ. apply implMG_ret. apply evtF_done.
        (* [comment removed for export] *)
        unfold btf_postA. all: natfold_lits. revert FN4 EBc4. generalize [CB (Z.to_nat 4096) nbuf] as NBc. generalize [CB 256%nat ej] as EJc. intros EJc NBc FN4 EBc4.
        split; [exact FPK|]. do 20 eexists. split; [reflexivity|]. split; [exact HR4|]. split; [exact G4|]. split; [exact HC4|]. split; [reflexivity|].
        split; [intros K0; lia|]. split; [exact FN4|]. split; [exact EBc4|]. split; [exact HPc4|]. split; [exact PKc4|].
        split; [exact UC4|]. split; [exact AGK| left; lia].
    - (* [comment removed for export] *)
      destruct PO as (FP2 & a0v & m2 & E & OF2 & MI2 & ST2 & AG2 & -> & G2 & EN & ER). rewrite ESPA in *. post_regs E.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC1 G1 HP eq_refl eq_refl AG2 MI2 ST2) as HC2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN AG2 ltac:(lia) FNsz) as FN2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc AG2 ltac:(lia) EBsz) as EBc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc2.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC1 TOP47 AG2 ltac:(lia)) as UC2.
      hr_next HR FP2 HR2.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G2 ltac:(assumption)) as (T0 & T47' & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      set (e := lc_errno (ps_libc s2')) in *.
      clear MI ST STG FRA' FRs FK0 FLG SA SB SC FN EBc HPc PKc MU WM RB NBY UFN LF.
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      pose proof HC2 as (_ & _ & _ & FRA2 & _).        (* [comment removed for export] *)
      ienterG. zstep. if_true. zstep. do 3 zstep. rewrite ETP.
      zstep.                                (* [comment removed for export] *)
      pose proof ATPv_pg as TPG. pose proof atp_lin as ((TPLO & _) & _).
      assert (ERN : (0 < ATP + -164 < 2^64)%Z) by (unfold ATP; atop_facts; lia).
      zstep. if_false_by (eqz_false (ATP + -164) ERN).
      zstep. replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
      zstep. if_false.
      ck TUNP 4%Z 0x84abc%Z [11%Z; 12%Z].
      zstep. rewrite (sx32_smallA e) by lia. do 3 zstep.
      apply evtF_done. subst POSTQ. apply implMG_errno_l. fold e. eapply implMG_bind.
      { eapply PRINTF_O with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (v := e);
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | reflexivity | reflexivity | exact ER ]. }
      intros [] s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & a0v & m3 & E & OF3 & MI3 & ST3 & AG3 & G3). rewrite ESPA in *. post_regs E.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC2 G2 HP eq_refl eq_refl AG3 MI3 ST3) as HC3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN2 AG3 ltac:(lia) FNsz) as FN3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc2 AG3 ltac:(lia) EBsz) as EBc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc3.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC2 TOP47 AG3 ltac:(lia)) as UC3.
      hr_next HR2 FP3 HR3.
      assert (AGK : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m3).
      { eapply agrees_on_trans; [exact AG1'|]. eapply agrees_on_trans; eapply fz_ag_final; first [exact AG2| exact AG3| lia]. }
      clear MI2 MU WM FN2 EBc2 HPc2 PKc2 EN TUNP.
      pose proof HC3 as (MI3' & _ & _ & FRA3 & _).
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      ienterG.                              (* [comment removed for export] *)
      apply evtF_done. subst POSTQ. apply implMG_ret. apply evtF_done.
      (* [comment removed for export] *)
      unfold btf_postA. all: natfold_lits. revert FN3 EBc3. generalize [CB (Z.to_nat 4096) nbuf] as NBc. generalize [CB 256%nat ej] as EJc. intros EJc NBc FN3 EBc3.
      split; [intros b j Hb; apply FP3, FP2; exact Hb|]. do 20 eexists. split; [reflexivity|]. split; [exact HR3|]. split; [exact G3|]. split; [exact HC3|]. split; [reflexivity|].
      split; [intros K0; lia|]. split; [exact FN3|]. split; [exact EBc3|]. split; [exact HPc3|]. split; [exact PKc3|].
      split; [exact UC3|]. split; [exact AGK| left; lia].
  Qed.
  End Sz6.
  #[using="FO GL GH HAL EQB FOPEN FCLOSE FWRITE PRINTF_O"] Lemma fz_fopen_part : ltac:(let t := eval cbv delta [fz_fopen_part__stmt] in fz_fopen_part__stmt in exact t).
  Proof. all: natfold_lits. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra nbuf ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_fopen_part__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M PSt B) (g : B -> Monad.M PSt C) (s : PSt) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. all: natfold_lits. intros. exact H0. Qed.

  #[using="Type"] Lemma eqz_false_neg1 : bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0) = false.
  Proof. all: natfold_lits. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition fz_btf__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (lo SPA Fb D : Z) (m : mem) (fra : list cell) (nbuf ej : list byte) (hpc pkc : cell)
      (data : list byte) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    datA RNG m CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (bufferToFile MOps PR TMPNAME (map bv_unsigned data)) s
      (btf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB lo SPA Fb nbuf ej hpc pkc trC m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e08fc) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) (Z_to_bv 64 (Fb + 352))
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8494c) fc None m (seg_rom asegs)).
  Section Sz9.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra nbuf ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_btf__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL GH HAL EQB FOPEN FCLOSE FWRITE REMOVE PRINTF_R PRINTF_O"] Lemma fz_btf__body : ltac2:(SecDiet.SzSec.bodyP 'fz_btf__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof. all: natfold_lits.
 intros HP HR G HC FRAS FN NB EBc HPc HP8 PKc PK8 UC TR DAT DLEN.
    (* [comment removed for export] *)
    assert (FNsz : hidc ((Fb + 352 + Z.of_nat (cells_size [CB (Z.to_nat 4096) nbuf]) <= Fb + 8192)%Z)) by (unfold hidc; cbn [cells_size csize Nat.add]; lia).
    assert (EBsz : hidc ((Fb + 32 + Z.of_nat (cells_size [CB 256%nat ej]) <= Fb + 8192)%Z)) by (unfold hidc; cbn [cells_size csize Nat.add]; lia).
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _ & _ & _ & _ & _ & _ & SB & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    pose proof (name_bytes _ _ _ _ _ _ FN NB) as NBY.
    pose proof (fz_unp_fname _ _ SB ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UFN.
    unfold bufferToFile. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_remove e_last_errno e_printf e_fopen_w e_fwrite e_fclose prims].
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. zstep. zstep.
    rewrite <- tmpname_Z.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply REMOVE with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := (Fb + 352)%Z) (name := tmpname);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | reflexivity | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia
        | eapply (fz_cobj FO GIOA fflagA GL); [exact G| lia| rewrite tmpname_len; lia| rewrite tmpname_len; lia| eapply unpoisoned_sub; [exact UFN| lia| rewrite tmpname_len; lia]]
        | exact tmpname_ok ]. }
    intros r s2' RNG2 ms2 PO. cbv beta in PO. destruct PO as (FP2 & a0v & m2 & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & Hr). rewrite ESPA in *. post_regs E.
    rewrite tmpname_Z.
    pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC G HP FRAS eq_refl AG2 MI2 ST2) as HC2.
    pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN AG2 ltac:(lia) FNsz) as FN2.
    pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc AG2 ltac:(lia) EBsz) as EBc2.
    pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc2.
    pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc2.
    pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC TOP47 AG2 ltac:(lia)) as UC2.
    pose proof (datA_keep _ _ _ _ _ _ _ _ _ _ _ _ _ DAT AG2 G2) as DAT2.
    hr_next HR FP2 HR2.
    assert (AGK2 : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m2) by (eapply fz_ag_final; [exact AG2| lia]).
    clear MI MU WM FN EBc HPc PKc NBY UFN SB UC DAT.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    destruct Hr as [-> | (-> & EN & ER)].
    - (* [comment removed for export] *)
      ienterG. zstep. if_true. apply evtF_done. subst POSTQ.
      cbn [Z.eqb negb]. apply implMG_retb. cbn [negb].
      eapply implMG_mono; [| intros r1 sx RNGx msx PO; eapply btf_postA_back with (RNG1 := RNG2) (m1 := m2); [exact FP2| exact AGK2| exact PO]].
      eapply fz_fopen_part; [exact HP| exact HR2| exact G2| exact HC2| exact FRAS| exact FN2| exact NB| exact EBc2| exact HPc2| exact HP8| exact PKc2| exact PK8
                            | exact UC2| exact TR| exact DAT2| exact DLEN].
    - (* [comment removed for export] *)
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G2 ltac:(assumption)) as (T0 & T47' & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      set (e := lc_errno (ps_libc s2')) in *.
      ienterG. zstep. if_false_by (eqz_false_neg1). zstep. do 3 zstep. rewrite ETP.
      (* [comment removed for export] *)
      pose proof ATPv_pg as TPG. pose proof atp_lin as ((TPLO & _) & _).
      assert (ERN : (0 < ATP + -164 < 2^64)%Z) by (unfold ATP; atop_facts; lia).
      zstep. if_false_by (eqz_false (ATP + -164) ERN).
      zstep. replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
      zstep. if_false.
      ck TUNP 4%Z 0x84978%Z [11%Z; 12%Z].
      zstep. rewrite (sx32_smallA e) by lia. zstep. zstep.
      clear TUNP EN.
      destruct (Z.eqb_spec e 2) as [E2|NE2].
      + (* [comment removed for export] *)
        rewrite E2. unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
        apply evtF_done. subst POSTQ. cbn [Z.eqb negb]. apply implMG_errno_ll. cbv beta. fold e. rewrite E2. unfold ENOENT. cbn [Z.eqb negb].
        apply implMG_retb. cbn [negb].
        eapply implMG_mono; [| intros r1 sx RNGx msx PO; eapply btf_postA_back with (RNG1 := RNG2) (m1 := m2); [exact FP2| exact AGK2| exact PO]].
        eapply fz_fopen_part; [exact HP| exact HR2| exact G2| exact HC2| exact FRAS| exact FN2| exact NB| exact EBc2| exact HPc2| exact HP8| exact PKc2| exact PK8
                              | exact UC2| exact TR| exact DAT2| exact DLEN].
      + (* [comment removed for export] *)
        rewrite (eqb_lits_false e 2 ltac:(lia) ltac:(lia) ltac:(lia)). cbn [negb]. cbv iota.
        do 4 zstep.                           (* [comment removed for export] *)
        apply evtF_done. subst POSTQ. cbn [Z.eqb negb]. apply implMG_errno_ll. cbv beta. fold e.
        replace (negb (e =? ENOENT)%Z) with true by (unfold ENOENT; destruct (Z.eqb_spec e 2); [lia| reflexivity]).
        apply implMG_bind_assoc. cbv beta.
        eapply implMG_bind.
        { eapply PRINTF_R with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (v := e);
            [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
            | reflexivity | reflexivity | exact ER ]. }
        intros [] s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & a0v & m3 & E & OF3 & MI3 & ST3 & AG3 & G3). rewrite ESPA in *. post_regs E.
        pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC2 G2 HP FRAS eq_refl AG3 MI3 ST3) as HC3.
        pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FN2 AG3 ltac:(lia) FNsz) as FN3.
        pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc2 AG3 ltac:(lia) EBsz) as EBc3.
        pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc3.
        pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc3.
        pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC2 TOP47 AG3 ltac:(lia)) as UC3.
        hr_next HR2 FP3 HR3.
        clear MI2 MU WM FN2 EBc2 HPc2 PKc2.
        pose proof HC3 as (MI3' & _).
        pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        apply implMG_retb. cbn [negb].
        ienterG.                              (* [comment removed for export] *)
        apply evtF_done. subst POSTQ. apply implMG_ret. apply evtF_done.
        (* [comment removed for export] *)
        unfold btf_postA. all: natfold_lits. revert FN3 EBc3. generalize [CB (Z.to_nat 4096) nbuf] as NBc. generalize [CB 256%nat ej] as EJc. intros EJc NBc FN3 EBc3.
        split; [intros b j Hb; apply FP3, FP2; exact Hb|]. do 20 eexists. split; [reflexivity|]. split; [exact HR3|]. split; [exact G3|]. split; [exact HC3|]. split; [exact FRAS|].
        split; [intros K0; lia|]. split; [exact FN3|]. split; [exact EBc3|]. split; [exact HPc3|]. split; [exact PKc3|].
        split; [exact UC3|]. split; [eapply agrees_on_trans; [exact AGK2| eapply fz_ag_final; [exact AG3| lia]]| left; lia].
  Qed.
  End Sz9.
  #[using="GL GH HAL EQB FOPEN FCLOSE FWRITE REMOVE PRINTF_R PRINTF_O"] Lemma fz_btf : ltac:(let t := eval cbv delta [fz_btf__stmt] in fz_btf__stmt in exact t).
  Proof. all: natfold_lits. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra nbuf ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_btf__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzBtf.
End CANSEC1.
End TwB.
End F_fuzz_btfA.

(* [comment removed for export] *)
Module F_fuzz_loopA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA.
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
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FuzzLoop.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis FOL : fo_leaf_laws FO.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis PNEXT : pcap_next_ex_stmt HO FO sites GIOA TP.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Notation PR := (prims HO FO sites).

  #[using="Type"] Lemma packet_loop_S : forall f ng (p : pcapT),
    packet_loop MOps PR (S f) ng p =
    mo_bind MOps (Pcap.pcap_next_ex MOps PR ng p) (fun x => let '(r, p) := x in
      if 0 <? r then
        mo_bind MOps (with_outfile MOps PR (fun out => e_fprintf PR out (pieces_packet_length (h_caplen (pc_header p)) (h_len (pc_header p)))))
                (fun _ => packet_loop MOps PR f ng p)
      else mo_ret MOps p).
  Proof. all: natfold_lits. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma with_outfile_lA : forall {A B} RNG (k : hptr -> Monad.M PSt A) (g : A -> Monad.M PSt B) (s : PSt) Q ms,
    (forall out, ps_outfile s = Some out -> implMG RNG (mbind (k out) g) s Q ms) ->
    implMG RNG (mo_bind MOps (with_outfile MOps PR k) g) s Q ms.
  Proof. all: natfold_lits.
    intros A B RNG k g s Q ms HK. unfold implMG in *. cbn. destruct (ps_outfile s) as [out|].
    - exact (HK out eq_refl).
    - cbn. apply evtS_done. exact I.
  Qed.

  #[using="Type"] Lemma PCAPR_hdrA : forall P (p : pcapT) PB FB m, PCAPR P p PB FB m ->
    rw_cells asegs m (P + 520) (hdr_cells (pc_header p)) /\ 0 <= h_caplen (pc_header p) < 2^32 /\ 0 <= h_len (pc_header p) < 2^32.
  Proof. all: natfold_lits.
    intros P p PB FB m (Af & Hin & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (pcap_cells_split4 _ _ _ _ (C8 (Z_to_bv 64 Af)) _ _ _ eq_refl CELLS) as (_ & _ & H3 & _).
    pose proof WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc & Hl & _). split; [exact H3|]. split; [exact Hc| exact Hl].
  Qed.
  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma PCAPR_unp : forall L RNG s CL PB FB FL m P (p : pcapT), GIOA L RNG s (CL ++ PB) FB FL m -> PCAPR P p PB FB m ->
    unpoisoned m P (P + psize p) /\ (P mod 16 = 0)%Z /\ (0 < P)%Z /\ (P + psize p <= ATOP)%Z /\ rng RNG P (psize p) /\ rng RNG (shad P) (nshad (psize p)).
  Proof. all: natfold_lits.
    intros L RNG s CL PB FB FL m P p G PC. pose proof (PCAPR_self_in _ _ _ _ _ PC) as HIN.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HIN)) as ((BAND & N0 & TOP & AL) & P0 & UNP & RB & RSH & AR).
    cbn [cb_addr cb_size fst snd] in *. repeat (split; [assumption|]). exact RSH.
  Qed.

  (* [comment removed for export] *)
  Definition fz_pkt__stmt : Prop := forall (A : Type) (K : Monad.M PSt A) (Q : A -> PSt -> footprint -> machine_state -> Prop)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL PB FB : list cblk) (lo SPA Fb P : Z) (m : mem) (j1 j2 nbuf : list byte) (pkc : cell)
      (p : pcapT) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s (CL ++ PB) FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
           [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] ->
    rw_cells asegs m (Fb + 4608) [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))] -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC ->
    PCAPR P p PB FB m ->
    (forall (s' : PSt) (RNG' : footprint) (m' : mem) (ra0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       fp_le RNG RNG' -> hrngA L RNG' lo -> GIOA L RNG' s' (CL ++ PB) FB (FZFL Fb) m' ->
       hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
              [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m' ->
       rw_cells asegs m' (Fb + 352) [CB 4096 nbuf] ->
       rw_cells asegs m' (Fb + 4608) [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))] -> rw_cells asegs m' (Fb + 4576) [pkc] ->
       ucallerA depth_fuzz_one L m' sp s0 ra trC ->
       PCAPR P p PB FB m' -> ps_outfile s' = ps_outfile s ->
       agrees_on (client_keeps [] CL (bv_unsigned sp)) m m' ->
       implMG RNG' K s' Q
         (MS (mkR ra0' (Z_to_bv 64 SPA) gp tp t0' t1' t2' sp (Z_to_bv 64 SPA) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 0x5e0894) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 P) (Z_to_bv 64 (Fb + 4576)) (Z_to_bv 64 (Fb + 352))
                  (Z_to_bv 64 (Fb + 4608)) (Z_to_bv 64 0x210e0) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3' t4' t5' t6')
             F (Z_to_bv 64 0x849d0) fc None m' (seg_rom asegs))) ->
    implMG RNG (mo_bind MOps (with_outfile MOps PR (fun out => e_fprintf PR out (pieces_packet_length (h_caplen (pc_header p)) (h_len (pc_header p)))))
                        (fun _ => K)) s Q
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e0894) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 P) (Z_to_bv 64 (Fb + 4576)) (Z_to_bv 64 (Fb + 352))
               (Z_to_bv 64 (Fb + 4608)) (Z_to_bv 64 0x210e0) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84990) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables A K Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL PB FB lo SPA Fb P m j1 j2 nbuf pkc p trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_pkt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @A).
  #[using="GL GH FPRINTF_DD"] Lemma fz_pkt__body : ltac2:(SecDiet.SzSec.bodyP 'fz_pkt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof. all: natfold_lits.
 intros HP HR G HC FN HPc PKc PK8 UC PC KONT.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    pose proof (PCAPR_unp _ _ _ _ _ _ _ _ _ _ G PC) as (PUNP & P16 & P0 & PTOP & PRNG & PSRNG). pose proof (psize_pos p) as PSZ.
    pose proof (PCAPR_hdrA _ _ _ _ _ PC) as (HDR & HCAP & HLEN). unfold hdr_cells in HDR. unfold PCAP_HDR_OFF in *.
    apply with_outfile_lA. intros out EO.
    pose proof (gh_outfile _ GH _ _ _ _ _ _ _ G) as OC. rewrite EO in OC. destruct OC as (Ao & AIN & OC). unfold OUTFILE_ADDR in OC.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. zstep. zstep.
    ck0 PUNP; ck_go.
    zstep.
    ck0 PUNP; ck_go.
    do 3 zstep.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply FPRINTF_DD with (L := L) (s := s) (CL := CL ++ PB) (FB := FB) (FL := FZFL Fb) (f := out) (Af := Ao) (lo := lo)
                             (v1 := h_caplen (pc_header p)) (v2 := h_len (pc_header p));
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | exact AIN | reflexivity | reflexivity | reflexivity | reflexivity | exact HCAP | exact HLEN ]. }
    intros [] s1' RNG1 ms1 PO. cbv beta in PO. destruct PO as (FP1 & a0v & m1 & E & OF1 & MI1 & ST1 & AG1 & G1).
    rewrite ESPA in *. post_regs E.
    assert (AGX : agrees_on (fun a => client_keeps (FZFL Fb) (CL ++ PB) SPA a /\ True) m m1) by (eapply agrees_on_weaken; [exact AG1| intros a [K0 _]; exact K0]).
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ (CL ++ PB) _ _ _ _ _ _ _ _ (fun _ => True) _ _ HC G HP eq_refl eq_refl AGX ltac:(intros; exact I) MI1 ST1) as HC1.
    pose proof (fz_local_keep (CL ++ PB) SPA Fb (fun _ => True) _ _ _ _ FN AGX ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros; exact I)) as FN1.
    pose proof (fz_local_keep (CL ++ PB) SPA Fb (fun _ => True) _ _ _ _ HPc AGX ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros; exact I)) as HPc1.
    pose proof (fz_uc_keep _ _ (CL ++ PB) SPA Fb (fun _ => True) _ _ _ _ _ _ UC TOP47 AGX ltac:(lia) ltac:(intros; exact I)) as UC1.
    assert (PC1 : PCAPR P p PB FB m1) by (eapply (PCAPR_agree _ _ _ _ _ _ _ AG1); [| exact PC]; intros a Ha; right; left; apply in_block_app; right; exact Ha).
    pose proof (fz_local_keep (CL ++ PB) SPA Fb (fun _ => True) _ _ _ _ PKc AGX ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia) ltac:(intros; exact I)) as PKc1.
    eapply KONT; [exact FP1 | eapply hrngA_le; [exact HR| exact FP1] | exact G1 | exact HC1 | exact FN1 | exact HPc1 | exact PKc1 | exact UC1 | exact PC1 | exact OF1 |].
    eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; apply in_block_app; left; exact Ha| intros fr0 []].
  Qed.
  End Sz5.
  #[using="GL GH FPRINTF_DD"] Lemma fz_pkt : ltac:(let t := eval cbv delta [fz_pkt__stmt] in fz_pkt__stmt in exact t).
  Proof. all: natfold_lits. intros A K Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL PB FB lo SPA Fb P m j1 j2 nbuf pkc p trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_pkt__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition lx_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (lo SPA Fb P : Z) (j1 j2 nbuf : list byte) (trC : list Z) (m0 : mem)
      : pcapT -> PSt -> footprint -> machine_state -> Prop :=
    fun p' s' RNG' ms' => fp_le RNG RNG' /\ exists ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r24 r25 t3 t4 t5 t6 m' PB',
      ms' = MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
                    r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 P) (Z_to_bv 64 (Fb + 4576)) (Z_to_bv 64 (Fb + 352))
                    r24 r25 (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
               F (Z_to_bv 64 0x84a48) fc None m' (seg_rom asegs)
      /\ hrngA L RNG' lo /\ GIOA L RNG' s' (CL ++ PB') FB (FZFL Fb) m' /\ PCAPR_closable P p' PB' FB m'
      /\ hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m'
      /\ rw_cells asegs m' (Fb + 352) [CB 4096 nbuf]
      /\ ucallerA depth_fuzz_one L m' sp s0 ra trC
      /\ ps_outfile s' <> Some (pc_rfile p')
      /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m0 m'.

  #[using="Type"] Lemma lx_postA_back : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 RNG1 CL FB lo SPA Fb P j1 j2 nbuf trC m0 m1 r s' RNG' ms',
    fp_le RNG0 RNG1 -> agrees_on (client_keeps [] CL (bv_unsigned sp)) m0 m1 ->
    lx_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG1 CL FB lo SPA Fb P j1 j2 nbuf trC m1 r s' RNG' ms' ->
    lx_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 CL FB lo SPA Fb P j1 j2 nbuf trC m0 r s' RNG' ms'.
  Proof. all: natfold_lits.
    intros until ms'. intros FP AG. unfold lx_postA. all: natfold_lits. generalize [CB (Z.to_nat 4096) nbuf] as NBc. intros NBc (FP' & PO). destruct_exs PO. destruct PO as (E & HR & G & PC & HC & FN & UC & NOF & AG2).
    split; [intros b j Hb; apply FP', FP; exact Hb|].
    do 21 eexists. split; [exact E|]. repeat (split; [eassumption|]). eapply agrees_on_trans; [exact AG| exact AG2].
  Qed.

  (* [comment removed for export] *)
  #[using="GL GH FOL FPRINTF_DD PNEXT"] Lemma fz_iter : forall (f ng : nat)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL PB FB : list cblk) (lo SPA Fb P : Z) (m : mem) (j1 j2 nbuf : list byte) (pkc : cell)
      (p : pcapT) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s (CL ++ PB) FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
           [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] ->
    rw_cells asegs m (Fb + 4608) [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))] -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    PCAPR P p PB FB m -> ps_outfile s <> Some (pc_rfile p) ->
    implMG RNG (mo_bind MOps (with_outfile MOps PR (fun out => e_fprintf PR out (pieces_packet_length (h_caplen (pc_header p)) (h_len (pc_header p)))))
                        (fun _ => packet_loop MOps PR f ng p)) s
      (lx_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB lo SPA Fb P j1 j2 nbuf trC m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e0894) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 P) (Z_to_bv 64 (Fb + 4576)) (Z_to_bv 64 (Fb + 352))
               (Z_to_bv 64 (Fb + 4608)) (Z_to_bv 64 0x210e0) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84990) fc None m (seg_rom asegs)).
  Proof. all: natfold_lits.
    induction f as [|f IH]; intros until t6; intros HP HR G HC FN HPc PKc PK8 UC TR PC NOF.
    all: eapply fz_pkt; [exact HP| exact HR| exact G| exact HC| exact FN| exact HPc| exact PKc| exact PK8| exact UC| exact PC|].
    all: intros s1' RNG1 m1 ra1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 FP1 HR1 G1 HC1 FN1 HPc1 PKc1 UC1 PC1 OF1 AG1.
    - (* [comment removed for export] *)
      apply implMG_unr.
    - rewrite packet_loop_S.
      pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR1.
      pose proof HC1 as (MI1 & ST1 & _ & _ & _ & _ & _ & _ & _ & SC1).
      pose proof TR as (_ & _ & _ & _ & _ & TRN & _).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
      assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
      pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G1) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
      destruct (fz_unp_locals _ _ SC1 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as [UPK UHP].
      pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
      ienterG. do 4 zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply implMG_leaf.
        eapply PNEXT with (L := L) (s := s1') (CLc := CL) (PB := PB) (FB := FB) (FL := FZFL Fb) (lo := lo) (P := P) (HP := (Fb + 4608)%Z) (PKT := (Fb + 4576)%Z)
                          (p := p) (fuel := ng) (hc := C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))) (pkc := pkc) (trC := bv_unsigned ra :: trC);
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR1| exact G1| exact ST1| exact MI1| unfold FUZZ_STACK, PCAP_L4_STACK; lia]
          | eapply (fz_ucaller fflagA); [exact UC1| exact HP| exact HC1| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_pcap_next_ex, depth_fuzz_one; lia]
          | rewrite unsigned_lit by lia; exact TRN
          | intros ff Hf [E|[]]; cbn in E; subst ff; unfold frames_pcap_next_ex in Hf; cbn in Hf; intuition discriminate
          | exact PC1 | reflexivity | reflexivity | reflexivity | exact HPc1 | reflexivity | exact PKc1 | exact PK8
          | eapply (fz_cobj FO GIOA fflagA GL); [exact G1| lia| lia| lia| exact UHP]
          | eapply (fz_cobj FO GIOA fflagA GL); [exact G1| lia| lia| lia| exact UPK]
          | right; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]. }
      intros [st p'] s2' RNG2 ms2 [PO LF]. cbv beta in PO. destruct PO as (FP2 & a0v & m2 & PB2 & pk2 & E & OF2 & MI2 & ST2 & AG2 & G2 & PC2 & PCC2 & -> & Hst & HPc2 & PKc2 & PK82).
      apply (pcap_next_ex_rfile HO FO sites FOL) in LF.
      rewrite ESPA in *. post_regs E.
      assert (NOF2 : ps_outfile s2' <> Some (pc_rfile p')) by (rewrite OF2, LF, OF1; exact NOF).
      pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _
                    HC1 G1 HP eq_refl eq_refl AG2 ltac:(intros a Ha; lia) MI2 ST2) as HC2.
      pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _ _ _ FN1 AG2 ltac:(lia)
                    ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia)) as FN2.
      pose proof (fz_uc_keep _ _ CL SPA Fb (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _ _ _ _ _ UC1 TOP47 AG2 ltac:(lia) ltac:(intros a Ha; lia)) as UC2.
      assert (AGK : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m2).
      { eapply agrees_on_trans; [exact AG1|]. eapply agrees_on_weaken; [exact AG2|]. cbv beta. intros a [Ha|[Ha|[Ha|Ha]]].
        - split; [left; lia| lia].
        - split; [right; left; exact Ha|].
          assert (NF : ~ in_frames (FZFL Fb) a) by (intros K0; apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G1 K0); apply in_block_app; left; apply in_block_app; left; exact Ha).
          assert (NR : ~ (Fb <= a < Fb + 8192)%Z) by (intros K0; apply NF; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia). lia.
        - inversion Ha.
        - inversion Ha. }
      hr_next HR1 FP2 HR2.
      clear MI1 MU WM HPc1 PKc1 UPK UHP SC1 FN1. 
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      destruct Hst as [-> | Hst].
      + (* [comment removed for export] *)
        ienterG. zstep. change (bv_lts z64 (Z_to_bv 64 1)) with true. cbv iota. cbn [Z.ltb Z.compare].
        apply evtF_done. subst POSTQ.
        eapply implMG_mono; [| intros r1 sx RNGx msx PO; eapply lx_postA_back with (RNG1 := RNG2) (m1 := m2); [intros b j Hb; apply FP2, FP1; exact Hb| exact AGK| exact PO]].
        eapply IH; [exact HP| exact HR2| exact G2| exact HC2| exact FN2| exact HPc2| exact PKc2| exact PK82| exact UC2
                   | exact TR | apply PC2; lia | exact NOF2].
      + (* [comment removed for export] *)
        assert (PCC : PCAPR_closable P p' PB2 FB m2) by (destruct Hst as [-> | ->]; [apply PCAPR_closable_of; apply PC2; lia | apply PCC2; reflexivity]).
        ienterG. zstep.
        replace (bv_lts z64 (Z_to_bv 64 st)) with false by (destruct Hst as [-> | ->]; reflexivity). cbv iota.
        replace (0 <? st)%Z with false by (destruct Hst as [-> | ->]; reflexivity).
        zstep.
        apply evtF_done. subst POSTQ. apply implMG_ret. apply evtF_done.
        (* [comment removed for export] *)
        unfold lx_postA. all: natfold_lits. revert FN2. generalize [CB (Z.to_nat 4096) nbuf] as NBc. intros NBc FN2.
        split; [intros b j Hb; apply FP2, FP1; exact Hb|].
        do 20 eexists. exists PB2. split; [reflexivity|]. split; [exact HR2|]. split; [exact G2|]. split; [exact PCC|]. split; [exact HC2|]. split; [exact FN2|].
        split; [exact UC2|]. split; [exact NOF2| exact AGK].
  Qed.

End FuzzLoop.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FuzzLoop.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis FOL : fo_leaf_laws FO.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis PNEXT : pcap_next_ex_stmt HO FO sites GIOA TP.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Notation PR := (prims HO FO sites).

  #[using="Type"] Lemma packet_loop_S : forall f ng (p : pcapT),
    packet_loop MOps PR (S f) ng p =
    mo_bind MOps (Pcap.pcap_next_ex MOps PR ng p) (fun x => let '(r, p) := x in
      if 0 <? r then
        mo_bind MOps (with_outfile MOps PR (fun out => e_fprintf PR out (pieces_packet_length (h_caplen (pc_header p)) (h_len (pc_header p)))))
                (fun _ => packet_loop MOps PR f ng p)
      else mo_ret MOps p).
  Proof. all: natfold_lits. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma with_outfile_lA : forall {A B} RNG (k : hptr -> Monad.M PSt A) (g : A -> Monad.M PSt B) (s : PSt) Q ms,
    (forall out, ps_outfile s = Some out -> implMG RNG (mbind (k out) g) s Q ms) ->
    implMG RNG (mo_bind MOps (with_outfile MOps PR k) g) s Q ms.
  Proof. all: natfold_lits.
    intros A B RNG k g s Q ms HK. unfold implMG in *. cbn. destruct (ps_outfile s) as [out|].
    - exact (HK out eq_refl).
    - cbn. apply evtS_done. exact I.
  Qed.

  #[using="Type"] Lemma PCAPR_hdrA : forall P (p : pcapT) PB FB m, PCAPR P p PB FB m ->
    rw_cells asegs m (P + 520) (hdr_cells (pc_header p)) /\ 0 <= h_caplen (pc_header p) < 2^32 /\ 0 <= h_len (pc_header p) < 2^32.
  Proof. all: natfold_lits.
    intros P p PB FB m (Af & Hin & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (pcap_cells_split4 _ _ _ _ (C8 (Z_to_bv 64 Af)) _ _ _ eq_refl CELLS) as (_ & _ & H3 & _).
    pose proof WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc & Hl & _). split; [exact H3|]. split; [exact Hc| exact Hl].
  Qed.
  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma PCAPR_unp : forall L RNG s CL PB FB FL m P (p : pcapT), GIOA L RNG s (CL ++ PB) FB FL m -> PCAPR P p PB FB m ->
    unpoisoned m P (P + psize p) /\ (P mod 16 = 0)%Z /\ (0 < P)%Z /\ (P + psize p <= ATOP)%Z /\ rng RNG P (psize p) /\ rng RNG (shad P) (nshad (psize p)).
  Proof. all: natfold_lits.
    intros L RNG s CL PB FB FL m P p G PC. pose proof (PCAPR_self_in _ _ _ _ _ PC) as HIN.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HIN)) as ((BAND & N0 & TOP & AL) & P0 & UNP & RB & RSH & AR).
    cbn [cb_addr cb_size fst snd] in *. repeat (split; [assumption|]). exact RSH.
  Qed.

  (* [comment removed for export] *)
  Definition fz_pkt__stmt : Prop := forall (A : Type) (K : Monad.M PSt A) (Q : A -> PSt -> footprint -> machine_state -> Prop)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL PB FB : list cblk) (lo SPA Fb P : Z) (m : mem) (j1 j2 nbuf : list byte) (pkc : cell)
      (p : pcapT) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s (CL ++ PB) FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
           [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] ->
    rw_cells asegs m (Fb + 4608) [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))] -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC ->
    PCAPR P p PB FB m ->
    (forall (s' : PSt) (RNG' : footprint) (m' : mem) (ra0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       fp_le RNG RNG' -> hrngA L RNG' lo -> GIOA L RNG' s' (CL ++ PB) FB (FZFL Fb) m' ->
       hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
              [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m' ->
       rw_cells asegs m' (Fb + 352) [CB 4096 nbuf] ->
       rw_cells asegs m' (Fb + 4608) [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))] -> rw_cells asegs m' (Fb + 4576) [pkc] ->
       ucallerA depth_fuzz_one L m' sp s0 ra trC ->
       PCAPR P p PB FB m' -> ps_outfile s' = ps_outfile s ->
       agrees_on (client_keeps [] CL (bv_unsigned sp)) m m' ->
       implMG RNG' K s' Q
         (MS (mkR ra0' (Z_to_bv 64 SPA) gp tp t0' t1' t2' sp (Z_to_bv 64 SPA) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 0x5e08fc) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 P) (Z_to_bv 64 (Fb + 4576)) (Z_to_bv 64 (Fb + 352))
                  (Z_to_bv 64 (Fb + 4608)) (Z_to_bv 64 0x210e0) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3' t4' t5' t6')
             F (Z_to_bv 64 0x84a50) fc None m' (seg_rom asegs))) ->
    implMG RNG (mo_bind MOps (with_outfile MOps PR (fun out => e_fprintf PR out (pieces_packet_length (h_caplen (pc_header p)) (h_len (pc_header p)))))
                        (fun _ => K)) s Q
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e08fc) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 P) (Z_to_bv 64 (Fb + 4576)) (Z_to_bv 64 (Fb + 352))
               (Z_to_bv 64 (Fb + 4608)) (Z_to_bv 64 0x210e0) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84a04) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables A K Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL PB FB lo SPA Fb P m j1 j2 nbuf pkc p trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_pkt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @A).
  #[using="GL GH FPRINTF_DD"] Lemma fz_pkt__body : ltac2:(SecDiet.SzSec.bodyP 'fz_pkt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof. all: natfold_lits.
 intros HP HR G HC FN HPc PKc PK8 UC PC KONT.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    pose proof (PCAPR_unp _ _ _ _ _ _ _ _ _ _ G PC) as (PUNP & P16 & P0 & PTOP & PRNG & PSRNG). pose proof (psize_pos p) as PSZ.
    pose proof (PCAPR_hdrA _ _ _ _ _ PC) as (HDR & HCAP & HLEN). unfold hdr_cells in HDR. unfold PCAP_HDR_OFF in *.
    apply with_outfile_lA. intros out EO.
    pose proof (gh_outfile _ GH _ _ _ _ _ _ _ G) as OC. rewrite EO in OC. destruct OC as (Ao & AIN & OC). unfold OUTFILE_ADDR in OC.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. zstep. ub_null.              (* [comment removed for export] *)
    zstep. ub_al 7%Z ltac:(al16 P16). zstep. if_false.
    zstep.
    ck0 PUNP; ck_go.
    zstep.
    ck0 PUNP; ck_go.
    do 3 zstep.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply FPRINTF_DD with (L := L) (s := s) (CL := CL ++ PB) (FB := FB) (FL := FZFL Fb) (f := out) (Af := Ao) (lo := lo)
                             (v1 := h_caplen (pc_header p)) (v2 := h_len (pc_header p));
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | exact AIN | reflexivity | reflexivity | reflexivity | reflexivity | exact HCAP | exact HLEN ]. }
    intros [] s1' RNG1 ms1 PO. cbv beta in PO. destruct PO as (FP1 & a0v & m1 & E & OF1 & MI1 & ST1 & AG1 & G1).
    rewrite ESPA in *. post_regs E.
    assert (AGX : agrees_on (fun a => client_keeps (FZFL Fb) (CL ++ PB) SPA a /\ True) m m1) by (eapply agrees_on_weaken; [exact AG1| intros a [K0 _]; exact K0]).
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ (CL ++ PB) _ _ _ _ _ _ _ _ (fun _ => True) _ _ HC G HP eq_refl eq_refl AGX ltac:(intros; exact I) MI1 ST1) as HC1.
    pose proof (fz_local_keep (CL ++ PB) SPA Fb (fun _ => True) _ _ _ _ FN AGX ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros; exact I)) as FN1.
    pose proof (fz_local_keep (CL ++ PB) SPA Fb (fun _ => True) _ _ _ _ HPc AGX ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros; exact I)) as HPc1.
    pose proof (fz_uc_keep _ _ (CL ++ PB) SPA Fb (fun _ => True) _ _ _ _ _ _ UC TOP47 AGX ltac:(lia) ltac:(intros; exact I)) as UC1.
    assert (PC1 : PCAPR P p PB FB m1) by (eapply (PCAPR_agree _ _ _ _ _ _ _ AG1); [| exact PC]; intros a Ha; right; left; apply in_block_app; right; exact Ha).
    pose proof (fz_local_keep (CL ++ PB) SPA Fb (fun _ => True) _ _ _ _ PKc AGX ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia) ltac:(intros; exact I)) as PKc1.
    eapply KONT; [exact FP1 | eapply hrngA_le; [exact HR| exact FP1] | exact G1 | exact HC1 | exact FN1 | exact HPc1 | exact PKc1 | exact UC1 | exact PC1 | exact OF1 |].
    eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; apply in_block_app; left; exact Ha| intros fr0 []].
  Qed.
  End Sz5.
  #[using="GL GH FPRINTF_DD"] Lemma fz_pkt : ltac:(let t := eval cbv delta [fz_pkt__stmt] in fz_pkt__stmt in exact t).
  Proof. all: natfold_lits. intros A K Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL PB FB lo SPA Fb P m j1 j2 nbuf pkc p trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_pkt__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition lx_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list cblk) (lo SPA Fb P : Z) (j1 j2 nbuf : list byte) (trC : list Z) (m0 : mem)
      : pcapT -> PSt -> footprint -> machine_state -> Prop :=
    fun p' s' RNG' ms' => fp_le RNG RNG' /\ exists ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r24 r25 t3 t4 t5 t6 m' PB',
      ms' = MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
                    r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 P) (Z_to_bv 64 (Fb + 4576)) (Z_to_bv 64 (Fb + 352))
                    r24 r25 (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
               F (Z_to_bv 64 0x84be8) fc None m' (seg_rom asegs)
      /\ hrngA L RNG' lo /\ GIOA L RNG' s' (CL ++ PB') FB (FZFL Fb) m' /\ PCAPR_closable P p' PB' FB m'
      /\ hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m'
      /\ rw_cells asegs m' (Fb + 352) [CB 4096 nbuf]
      /\ ucallerA depth_fuzz_one L m' sp s0 ra trC
      /\ ps_outfile s' <> Some (pc_rfile p')
      /\ agrees_on (client_keeps [] CL (bv_unsigned sp)) m0 m'.

  #[using="Type"] Lemma lx_postA_back : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 RNG1 CL FB lo SPA Fb P j1 j2 nbuf trC m0 m1 r s' RNG' ms',
    fp_le RNG0 RNG1 -> agrees_on (client_keeps [] CL (bv_unsigned sp)) m0 m1 ->
    lx_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG1 CL FB lo SPA Fb P j1 j2 nbuf trC m1 r s' RNG' ms' ->
    lx_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG0 CL FB lo SPA Fb P j1 j2 nbuf trC m0 r s' RNG' ms'.
  Proof. all: natfold_lits.
    intros until ms'. intros FP AG. unfold lx_postA. all: natfold_lits. generalize [CB (Z.to_nat 4096) nbuf] as NBc. intros NBc (FP' & PO). destruct_exs PO. destruct PO as (E & HR & G & PC & HC & FN & UC & NOF & AG2).
    split; [intros b j Hb; apply FP', FP; exact Hb|].
    do 21 eexists. split; [exact E|]. repeat (split; [eassumption|]). eapply agrees_on_trans; [exact AG| exact AG2].
  Qed.

  (* [comment removed for export] *)
  #[using="GL GH FOL FPRINTF_DD PNEXT"] Lemma fz_iter : forall (f ng : nat)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL PB FB : list cblk) (lo SPA Fb P : Z) (m : mem) (j1 j2 nbuf : list byte) (pkc : cell)
      (p : pcapT) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s (CL ++ PB) FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
           [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] ->
    rw_cells asegs m (Fb + 4608) [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))] -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    PCAPR P p PB FB m -> ps_outfile s <> Some (pc_rfile p) ->
    implMG RNG (mo_bind MOps (with_outfile MOps PR (fun out => e_fprintf PR out (pieces_packet_length (h_caplen (pc_header p)) (h_len (pc_header p)))))
                        (fun _ => packet_loop MOps PR f ng p)) s
      (lx_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB lo SPA Fb P j1 j2 nbuf trC m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e08fc) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 P) (Z_to_bv 64 (Fb + 4576)) (Z_to_bv 64 (Fb + 352))
               (Z_to_bv 64 (Fb + 4608)) (Z_to_bv 64 0x210e0) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84a04) fc None m (seg_rom asegs)).
  Proof. all: natfold_lits.
    induction f as [|f IH]; intros until t6; intros HP HR G HC FN HPc PKc PK8 UC TR PC NOF.
    all: eapply fz_pkt; [exact HP| exact HR| exact G| exact HC| exact FN| exact HPc| exact PKc| exact PK8| exact UC| exact PC|].
    all: intros s1' RNG1 m1 ra1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 FP1 HR1 G1 HC1 FN1 HPc1 PKc1 UC1 PC1 OF1 AG1.
    - (* [comment removed for export] *)
      apply implMG_unr.
    - rewrite packet_loop_S.
      pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR1.
      pose proof HC1 as (MI1 & ST1 & _ & _ & _ & _ & _ & _ & _ & SC1).
      pose proof TR as (_ & _ & _ & _ & _ & TRN & _).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
      assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
      pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G1) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
      destruct (fz_unp_locals _ _ SC1 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as [UPK UHP].
      pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
      ienterG. do 4 zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply implMG_leaf.
        eapply PNEXT with (L := L) (s := s1') (CLc := CL) (PB := PB) (FB := FB) (FL := FZFL Fb) (lo := lo) (P := P) (HP := (Fb + 4608)%Z) (PKT := (Fb + 4576)%Z)
                          (p := p) (fuel := ng) (hc := C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))) (pkc := pkc) (trC := bv_unsigned ra :: trC);
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR1| exact G1| exact ST1| exact MI1| unfold FUZZ_STACK, PCAP_L4_STACK; lia]
          | eapply (fz_ucaller fflagA); [exact UC1| exact HP| exact HC1| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_pcap_next_ex, depth_fuzz_one; lia]
          | rewrite unsigned_lit by lia; exact TRN
          | intros ff Hf [E|[]]; cbn in E; subst ff; unfold frames_pcap_next_ex in Hf; cbn in Hf; intuition discriminate
          | exact PC1 | reflexivity | reflexivity | reflexivity | exact HPc1 | reflexivity | exact PKc1 | exact PK8
          | eapply (fz_cobj FO GIOA fflagA GL); [exact G1| lia| lia| lia| exact UHP]
          | eapply (fz_cobj FO GIOA fflagA GL); [exact G1| lia| lia| lia| exact UPK]
          | right; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]. }
      intros [st p'] s2' RNG2 ms2 [PO LF]. cbv beta in PO. destruct PO as (FP2 & a0v & m2 & PB2 & pk2 & E & OF2 & MI2 & ST2 & AG2 & G2 & PC2 & PCC2 & -> & Hst & HPc2 & PKc2 & PK82).
      apply (pcap_next_ex_rfile HO FO sites FOL) in LF.
      rewrite ESPA in *. post_regs E.
      assert (NOF2 : ps_outfile s2' <> Some (pc_rfile p')) by (rewrite OF2, LF, OF1; exact NOF).
      pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _
                    HC1 G1 HP eq_refl eq_refl AG2 ltac:(intros a Ha; lia) MI2 ST2) as HC2.
      pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _ _ _ FN1 AG2 ltac:(lia)
                    ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia)) as FN2.
      pose proof (fz_uc_keep _ _ CL SPA Fb (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _ _ _ _ _ UC1 TOP47 AG2 ltac:(lia) ltac:(intros a Ha; lia)) as UC2.
      assert (AGK : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m2).
      { eapply agrees_on_trans; [exact AG1|]. eapply agrees_on_weaken; [exact AG2|]. cbv beta. intros a [Ha|[Ha|[Ha|Ha]]].
        - split; [left; lia| lia].
        - split; [right; left; exact Ha|].
          assert (NF : ~ in_frames (FZFL Fb) a) by (intros K0; apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G1 K0); apply in_block_app; left; apply in_block_app; left; exact Ha).
          assert (NR : ~ (Fb <= a < Fb + 8192)%Z) by (intros K0; apply NF; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia). lia.
        - inversion Ha.
        - inversion Ha. }
      hr_next HR1 FP2 HR2.
      clear MI1 MU WM HPc1 PKc1 UPK UHP SC1 FN1. 
      pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      destruct Hst as [-> | Hst].
      + (* [comment removed for export] *)
        ienterG. zstep. change (bv_lts z64 (Z_to_bv 64 1)) with true. cbv iota. cbn [Z.ltb Z.compare].
        apply evtF_done. subst POSTQ.
        eapply implMG_mono; [| intros r1 sx RNGx msx PO; eapply lx_postA_back with (RNG1 := RNG2) (m1 := m2); [intros b j Hb; apply FP2, FP1; exact Hb| exact AGK| exact PO]].
        eapply IH; [exact HP| exact HR2| exact G2| exact HC2| exact FN2| exact HPc2| exact PKc2| exact PK82| exact UC2
                   | exact TR | apply PC2; lia | exact NOF2].
      + (* [comment removed for export] *)
        assert (PCC : PCAPR_closable P p' PB2 FB m2) by (destruct Hst as [-> | ->]; [apply PCAPR_closable_of; apply PC2; lia | apply PCC2; reflexivity]).
        ienterG. zstep.
        replace (bv_lts z64 (Z_to_bv 64 st)) with false by (destruct Hst as [-> | ->]; reflexivity). cbv iota.
        replace (0 <? st)%Z with false by (destruct Hst as [-> | ->]; reflexivity).
        zstep.
        apply evtF_done. subst POSTQ. apply implMG_ret. apply evtF_done.
        (* [comment removed for export] *)
        unfold lx_postA. all: natfold_lits. revert FN2. generalize [CB (Z.to_nat 4096) nbuf] as NBc. intros NBc FN2.
        split; [intros b j Hb; apply FP2, FP1; exact Hb|].
        do 20 eexists. exists PB2. split; [reflexivity|]. split; [exact HR2|]. split; [exact G2|]. split; [exact PCC|]. split; [exact HC2|]. split; [exact FN2|].
        split; [exact UC2|]. split; [exact NOF2| exact AGK].
  Qed.

End FuzzLoop.
End CANSEC1.
End TwB.
End F_fuzz_loopA.

(* [comment removed for export] *)
Module F_fuzz_tailA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_exitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FuzzTail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x58388 0xf8.
  Hypothesis UNLINK : unlink_stmt_o GIOA.
  Hypothesis FOL : fo_leaf_laws FO.
  Hypothesis PSTATS : pcap_stats_stmt GIOA TP.
  Hypothesis PCLOSE : pcap_close_stmt HO FO sites GIOA TP.

  (* [comment removed for export] *)
  Definition fz_exitK__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (lo SPA Fb : Z) (m : mem) (fra : list cell)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    implMG RNG (fo_ret FO _ FF_FUZZ_ONE_INPUT tt) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) r21 r22 r23 (Z_to_bv 64 Fb) r25 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84a9c) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m fra ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_exitK__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FFREE7 SETSHF8"] Lemma fz_exitK__body : ltac2:(SecDiet.SzSec.bodyP 'fz_exitK__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HP HR G HC FRAS.
    destruct HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). destruct HR as (RSTK & RIMG & RISH & RTLS). unfold FUZZ_STACK, PCAP_L4_STACK in LOS.
    destruct HC as (MI & ST & STG & FRA & FRs & (k0 & FK0) & FLG & SA & SB & SC).
    eapply implMG_mono.
    - eapply (fz_exit FO GIOA fflagA GL FFREE7 SETSHF8 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m);
        first [ eassumption | reflexivity | lia ].
    - cbv beta. intros r s' RNG' ms' (-> & -> & PO). destruct_exs PO. destruct PO as (E & MI' & ST' & AG' & G' & _).
      split; [intros b j Hb; exact Hb|]. do 15 eexists. exists FB. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'| exact G'].
  Qed.
  End Sz1.
  #[using="GL FFREE7 SETSHF8"] Lemma fz_exitK : ltac:(let t := eval cbv delta [fz_exitK__stmt] in fz_exitK__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m fra ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_exitK__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
    try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

  (* [comment removed for export] *)
  Definition fz_unlink__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (lo SPA Fb : Z) (m : mem) (fra : list cell) (nbuf : list byte)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r25 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    implMG RNG (s_unlink (H:=H) (hptr:=hptr) TMPNAME ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) r21 r22 (Z_to_bv 64 (Fb + 352)) (Z_to_bv 64 Fb) r25 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84a94) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m fra nbuf ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r25 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_unlink__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FFREE7 SETSHF8 UNLINK"] Lemma fz_unlink__body : ltac2:(SecDiet.SzSec.bodyP 'fz_unlink__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HP HR G HC FRAS FN NB.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    pose proof (name_bytes _ _ _ _ _ _ FN NB) as NBY.
    assert (NOBJ : cobjA RNG m (FZFL Fb) CL (Fb + 352) (Z.of_nat (length tmpname) + 1)).
    { destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & SB & _).
      eapply (fz_cobj FO GIOA fflagA GL); [exact G| lia| rewrite tmpname_len; lia| rewrite tmpname_len; lia|].
      eapply unpoisoned_sub; [eapply fz_unp_fname; [exact SB| Z.div_mod_to_equations; lia| lia| lia]| lia| rewrite tmpname_len; lia]. }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. zstep. zstep.
    apply evtF_done. subst POSTQ. rewrite <- tmpname_Z. eapply implMG_bind.
    { eapply UNLINK with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := (Fb + 352)%Z) (name := tmpname);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | reflexivity | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia | exact NOBJ | exact tmpname_ok ]. }
    intros r s' RNG1 ms' PO. cbv beta in PO. destruct PO as (FP1 & a0v & m1 & E & OF1 & MI1 & ST1 & AG1 & G1 & -> & Hr).
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia). rewrite ESPA in *.
    post_regs E.
    assert (AGX : agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ True) m m1) by (eapply agrees_on_weaken; [exact AG1| intros a [K _]; exact K]).
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun _ => True) _ _ HC G HP FRAS eq_refl AGX ltac:(intros; exact I) MI1 ST1) as HC1.
    eapply implMG_mono.
    - eapply fz_exitK; [exact HP | eapply hrngA_le; [exact HR| exact FP1] | exact G1 | exact HC1 | exact FRAS].
    - intros u sx RNGx msx PO. eapply (fz_post_back GIOA) with (RNG1 := RNG1) (m1 := m1); [exact FP1| | exact PO].
      eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| intros fr0 []].
  Qed.
  End Sz2.
  #[using="GL FFREE7 SETSHF8 UNLINK"] Lemma fz_unlink : ltac:(let t := eval cbv delta [fz_unlink__stmt] in fz_unlink__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m fra nbuf ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r25 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_unlink__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[using="Type"] Lemma nez_true_neg1 : negb (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) = true.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition fz_tail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL PB FB : list (@cblock hptr)) (lo SPA Fb P : Z) (m : mem) (j1 j2 nbuf : list byte)
      (p : PcapTypes.pcap hptr hptr) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r24 r25 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s (CL ++ PB) FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
           [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    PCAPR_closable P p PB FB m -> ps_outfile s <> Some (pc_rfile p) ->
    implMG RNG ('(sr, p) <- Pcap.pcap_stats MOps p ;;
                (if sr =? 0 then with_outfile MOps (prims HO FO sites) (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
                Pcap.pcap_close MOps (prims HO FO sites) p ;;;
                s_unlink TMPNAME ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 P) (Z_to_bv 64 (Fb + 4576)) (Z_to_bv 64 (Fb + 352)) r24 r25 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84a48) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL PB FB lo SPA Fb P m j1 j2 nbuf p trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r24 r25 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FFREE7 SETSHF8 UNLINK PSTATS PCLOSE"] Lemma fz_tail__body : ltac2:(SecDiet.SzSec.bodyP 'fz_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HP HR G HC FN NB UC TR PC NOF.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _ & FRA & _).
    destruct TR as (_ & _ & _ & _ & _ & _ & TRS & TRC).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. do 4 zstep.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply implMG_leaf.
      eapply PSTATS with (L := L) (s := s) (CLc := CL) (PB := PB) (FB := FB) (FL := FZFL Fb) (lo := lo) (P := P) (p := p) (trC := bv_unsigned ra :: trC);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold PCAP_L1_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | eapply (fz_ucaller fflagA); [exact UC| exact HP| exact HC| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_pcap_stats, depth_fuzz_one; lia]
        | rewrite unsigned_lit by lia; exact TRS
        | intros f Hf [E|[]]; cbn in E; subst f; unfold frames_pcap_stats in Hf; cbn in Hf; intuition discriminate
        | exact PC | reflexivity ]. }
    intros [sr p'] s1' RNG1 ms1 [PO LF]. unfold pcap_post in PO. destruct PO as (FP1 & a0v & m1 & PB1 & FB1 & E & MI1 & ST1 & AG1 & G1 & (-> & -> & -> & -> & Esr & PC1)).
    apply pcap_stats_rfile in LF.
    cbn [fst snd] in Esr, PC1, E. subst sr. rewrite ESPA in *.
    post_regs E.
    assert (AGX : agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ True) m m1) by (eapply agrees_on_weaken; [exact AG1| intros a [K _]; exact K]).
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun _ => True) _ _ HC G HP eq_refl eq_refl AGX ltac:(intros; exact I) MI1 ST1) as HC1.
    pose proof (fz_local_keep CL SPA Fb (fun _ => True) _ _ _ _ FN AGX ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros; exact I)) as FN1.
    pose proof (fz_uc_keep _ _ CL SPA Fb (fun _ => True) _ _ _ _ _ _ UC TOP47 AGX ltac:(lia) ltac:(intros; exact I)) as UC1.
    hr_next HR FP1 HR1.
    clear MI MU WM. pose proof HC1 as (MI1' & _ & _ & FRA1 & _).
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    ienterG. zstep. zstep. if_true_by (nez_true_neg1). cbv beta iota. cbn [Z.eqb].
    apply evtF_done. subst POSTQ. apply implMG_retb.
    ienterG. zstep. zstep.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply PCLOSE with (L := L) (s := s) (CLc := CL) (PB := PB) (FB := FB) (FL := FZFL Fb) (lo := lo) (P := P) (p := p') (trC := bv_unsigned ra :: trC);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR1| exact G1| exact ST1| exact MI1| unfold FUZZ_STACK, PCAP_L4_STACK; lia]
        | eapply (fz_ucaller fflagA); [exact UC1| exact HP| exact HC1| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_pcap_close, depth_fuzz_one; lia]
        | rewrite unsigned_lit by lia; exact TRC
        | intros f Hf [E|[]]; cbn in E; subst f; unfold frames_pcap_close in Hf; cbn in Hf; intuition discriminate
        | exact PC1 | reflexivity | rewrite LF; exact NOF ]. }
    intros [] s2' RNG2 ms2 PO. unfold pcap_post in PO. destruct PO as (FP2 & a0v & m2 & PB2 & FB2 & E & MI2 & ST2 & AG2 & G2 & (OF2 & -> & _)).
    rewrite ESPA in *. post_regs E. rewrite app_nil_r in G2.
    assert (AGX2 : agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ True) m1 m2) by (eapply agrees_on_weaken; [exact AG2| intros a [K _]; exact K]).
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun _ => True) _ _ HC1 G1 HP eq_refl eq_refl AGX2 ltac:(intros; exact I) MI2 ST2) as HC2.
    pose proof (fz_local_keep CL SPA Fb (fun _ => True) _ _ _ _ FN1 AGX2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros; exact I)) as FN2.
    hr_next HR1 FP2 HR2.
    clear MI1 MI1' MU WM FRA1. pose proof HC2 as (MI2' & _).
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    ienterG. zstep.
    apply evtF_done. subst POSTQ.
    eapply implMG_mono.
    - eapply fz_unlink; [exact HP | exact HR2 | exact G2 | exact HC2 | reflexivity | exact FN2 | exact NB].
    - intros u sx RNGx msx PO. eapply (fz_post_back GIOA) with (RNG1 := RNG2) (m1 := m2); [intros b j Hb; apply FP2, FP1; exact Hb| | exact PO].
      eapply agrees_on_trans; (eapply client_keeps_weaken; [eassumption| lia| intros a Ha; exact Ha| intros fr0 []]).
  Qed.
  End Sz4.
  #[using="GL FFREE7 SETSHF8 UNLINK PSTATS PCLOSE"] Lemma fz_tail : ltac:(let t := eval cbv delta [fz_tail__stmt] in fz_tail__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL PB FB lo SPA Fb P m j1 j2 nbuf p trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r24 r25 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzTail.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_exitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FuzzTail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x583f0 0xf8.
  Hypothesis UNLINK : unlink_stmt_o GIOA.
  Hypothesis FOL : fo_leaf_laws FO.
  Hypothesis PSTATS : pcap_stats_stmt GIOA TP.
  Hypothesis PCLOSE : pcap_close_stmt HO FO sites GIOA TP.

  (* [comment removed for export] *)
  Definition fz_exitK__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (lo SPA Fb : Z) (m : mem) (fra : list cell)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    implMG RNG (fo_ret FO _ FF_FUZZ_ONE_INPUT tt) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) r21 r22 r23 (Z_to_bv 64 Fb) r25 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84ad4) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m fra ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_exitK__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FFREE7 SETSHF8"] Lemma fz_exitK__body : ltac2:(SecDiet.SzSec.bodyP 'fz_exitK__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HP HR G HC FRAS.
    destruct HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). destruct HR as (RSTK & RIMG & RISH & RTLS). unfold FUZZ_STACK, PCAP_L4_STACK in LOS.
    destruct HC as (MI & ST & STG & FRA & FRs & (k0 & FK0) & FLG & SA & SB & SC).
    eapply implMG_mono.
    - eapply (fz_exit FO GIOA fflagA GL FFREE7 SETSHF8 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m);
        first [ eassumption | reflexivity | lia ].
    - cbv beta. intros r s' RNG' ms' (-> & -> & PO). destruct_exs PO. destruct PO as (E & MI' & ST' & AG' & G' & _).
      split; [intros b j Hb; exact Hb|]. do 15 eexists. exists FB. split; [exact E|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'| exact G'].
  Qed.
  End Sz1.
  #[using="GL FFREE7 SETSHF8"] Lemma fz_exitK : ltac:(let t := eval cbv delta [fz_exitK__stmt] in fz_exitK__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m fra ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r23 r25 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_exitK__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
    try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

  (* [comment removed for export] *)
  Definition fz_unlink__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (lo SPA Fb : Z) (m : mem) (fra : list cell) (nbuf : list byte)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r25 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    implMG RNG (s_unlink (H:=H) (hptr:=hptr) TMPNAME ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) r21 r22 (Z_to_bv 64 (Fb + 352)) (Z_to_bv 64 Fb) r25 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84acc) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m fra nbuf ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r25 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_unlink__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FFREE7 SETSHF8 UNLINK"] Lemma fz_unlink__body : ltac2:(SecDiet.SzSec.bodyP 'fz_unlink__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HP HR G HC FRAS FN NB.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    pose proof (name_bytes _ _ _ _ _ _ FN NB) as NBY.
    assert (NOBJ : cobjA RNG m (FZFL Fb) CL (Fb + 352) (Z.of_nat (length tmpname) + 1)).
    { destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & SB & _).
      eapply (fz_cobj FO GIOA fflagA GL); [exact G| lia| rewrite tmpname_len; lia| rewrite tmpname_len; lia|].
      eapply unpoisoned_sub; [eapply fz_unp_fname; [exact SB| Z.div_mod_to_equations; lia| lia| lia]| lia| rewrite tmpname_len; lia]. }
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. zstep. zstep.
    apply evtF_done. subst POSTQ. rewrite <- tmpname_Z. eapply implMG_bind.
    { eapply UNLINK with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := (Fb + 352)%Z) (name := tmpname);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | reflexivity | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia | exact NOBJ | exact tmpname_ok ]. }
    intros r s' RNG1 ms' PO. cbv beta in PO. destruct PO as (FP1 & a0v & m1 & E & OF1 & MI1 & ST1 & AG1 & G1 & -> & Hr).
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia). rewrite ESPA in *.
    post_regs E.
    assert (AGX : agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ True) m m1) by (eapply agrees_on_weaken; [exact AG1| intros a [K _]; exact K]).
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun _ => True) _ _ HC G HP FRAS eq_refl AGX ltac:(intros; exact I) MI1 ST1) as HC1.
    eapply implMG_mono.
    - eapply fz_exitK; [exact HP | eapply hrngA_le; [exact HR| exact FP1] | exact G1 | exact HC1 | exact FRAS].
    - intros u sx RNGx msx PO. eapply (fz_post_back GIOA) with (RNG1 := RNG1) (m1 := m1); [exact FP1| | exact PO].
      eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| intros fr0 []].
  Qed.
  End Sz2.
  #[using="GL FFREE7 SETSHF8 UNLINK"] Lemma fz_unlink : ltac:(let t := eval cbv delta [fz_unlink__stmt] in fz_unlink__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m fra nbuf ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r22 r25 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_unlink__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  #[using="Type"] Lemma nez_true_neg1 : negb (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) = true.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition fz_tail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL PB FB : list (@cblock hptr)) (lo SPA Fb P : Z) (m : mem) (j1 j2 nbuf : list byte)
      (p : PcapTypes.pcap hptr hptr) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r24 r25 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s (CL ++ PB) FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
           [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    PCAPR_closable P p PB FB m -> ps_outfile s <> Some (pc_rfile p) ->
    implMG RNG ('(sr, p) <- Pcap.pcap_stats MOps p ;;
                (if sr =? 0 then with_outfile MOps (prims HO FO sites) (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
                Pcap.pcap_close MOps (prims HO FO sites) p ;;;
                s_unlink TMPNAME ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 P) (Z_to_bv 64 (Fb + 4576)) (Z_to_bv 64 (Fb + 352)) r24 r25 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84be8) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL PB FB lo SPA Fb P m j1 j2 nbuf p trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r24 r25 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FFREE7 SETSHF8 UNLINK PSTATS PCLOSE"] Lemma fz_tail__body : ltac2:(SecDiet.SzSec.bodyP 'fz_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HP HR G HC FN NB UC TR PC NOF.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _ & FRA & _).
    destruct TR as (_ & _ & _ & _ & _ & _ & TRS & TRC).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. do 4 zstep.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply implMG_leaf.
      eapply PSTATS with (L := L) (s := s) (CLc := CL) (PB := PB) (FB := FB) (FL := FZFL Fb) (lo := lo) (P := P) (p := p) (trC := bv_unsigned ra :: trC);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold PCAP_L1_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | eapply (fz_ucaller fflagA); [exact UC| exact HP| exact HC| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_pcap_stats, depth_fuzz_one; lia]
        | rewrite unsigned_lit by lia; exact TRS
        | intros f Hf [E|[]]; cbn in E; subst f; unfold frames_pcap_stats in Hf; cbn in Hf; intuition discriminate
        | exact PC | reflexivity ]. }
    intros [sr p'] s1' RNG1 ms1 [PO LF]. unfold pcap_post in PO. destruct PO as (FP1 & a0v & m1 & PB1 & FB1 & E & MI1 & ST1 & AG1 & G1 & (-> & -> & -> & -> & Esr & PC1)).
    apply pcap_stats_rfile in LF.
    cbn [fst snd] in Esr, PC1, E. subst sr. rewrite ESPA in *.
    post_regs E.
    assert (AGX : agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ True) m m1) by (eapply agrees_on_weaken; [exact AG1| intros a [K _]; exact K]).
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun _ => True) _ _ HC G HP eq_refl eq_refl AGX ltac:(intros; exact I) MI1 ST1) as HC1.
    pose proof (fz_local_keep CL SPA Fb (fun _ => True) _ _ _ _ FN AGX ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros; exact I)) as FN1.
    pose proof (fz_uc_keep _ _ CL SPA Fb (fun _ => True) _ _ _ _ _ _ UC TOP47 AGX ltac:(lia) ltac:(intros; exact I)) as UC1.
    hr_next HR FP1 HR1.
    clear MI MU WM. pose proof HC1 as (MI1' & _ & _ & FRA1 & _).
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    ienterG. zstep. zstep. if_true_by (nez_true_neg1). cbv beta iota. cbn [Z.eqb].
    apply evtF_done. subst POSTQ. apply implMG_retb.
    ienterG. zstep. zstep.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply PCLOSE with (L := L) (s := s) (CLc := CL) (PB := PB) (FB := FB) (FL := FZFL Fb) (lo := lo) (P := P) (p := p') (trC := bv_unsigned ra :: trC);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR1| exact G1| exact ST1| exact MI1| unfold FUZZ_STACK, PCAP_L4_STACK; lia]
        | eapply (fz_ucaller fflagA); [exact UC1| exact HP| exact HC1| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_pcap_close, depth_fuzz_one; lia]
        | rewrite unsigned_lit by lia; exact TRC
        | intros f Hf [E|[]]; cbn in E; subst f; unfold frames_pcap_close in Hf; cbn in Hf; intuition discriminate
        | exact PC1 | reflexivity | rewrite LF; exact NOF ]. }
    intros [] s2' RNG2 ms2 PO. unfold pcap_post in PO. destruct PO as (FP2 & a0v & m2 & PB2 & FB2 & E & MI2 & ST2 & AG2 & G2 & (OF2 & -> & _)).
    rewrite ESPA in *. post_regs E. rewrite app_nil_r in G2.
    assert (AGX2 : agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ True) m1 m2) by (eapply agrees_on_weaken; [exact AG2| intros a [K _]; exact K]).
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun _ => True) _ _ HC1 G1 HP eq_refl eq_refl AGX2 ltac:(intros; exact I) MI2 ST2) as HC2.
    pose proof (fz_local_keep CL SPA Fb (fun _ => True) _ _ _ _ FN1 AGX2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros; exact I)) as FN2.
    hr_next HR1 FP2 HR2.
    clear MI1 MI1' MU WM FRA1. pose proof HC2 as (MI2' & _).
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    ienterG. zstep.
    apply evtF_done. subst POSTQ.
    eapply implMG_mono.
    - eapply fz_unlink; [exact HP | exact HR2 | exact G2 | exact HC2 | reflexivity | exact FN2 | exact NB].
    - intros u sx RNGx msx PO. eapply (fz_post_back GIOA) with (RNG1 := RNG2) (m1 := m2); [intros b j Hb; apply FP2, FP1; exact Hb| | exact PO].
      eapply agrees_on_trans; (eapply client_keeps_weaken; [eassumption| lia| intros a Ha; exact Ha| intros fr0 []]).
  Qed.
  End Sz4.
  #[using="GL FFREE7 SETSHF8 UNLINK PSTATS PCLOSE"] Lemma fz_tail : ltac:(let t := eval cbv delta [fz_tail__stmt] in fz_tail__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL PB FB lo SPA Fb P m j1 j2 nbuf p trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r24 r25 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzTail.
End CANSEC1.
End TwB.
End F_fuzz_tailA.

(* [comment removed for export] *)
Module F_fuzz_openA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_pcap_open2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_tailA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_loopA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

(* [comment removed for export] *)
Lemma msg_cstr : forall msg, Forall (fun z => 0 < z < 256) msg -> cstr msg = msg.
Proof. induction msg as [|c msg IH]; intros HF; [reflexivity|]. inversion HF; subst. cbn. destruct (Z.eqb_spec c 0); [lia|]. f_equal. apply IH. assumption. Qed.
Lemma msg_unsigned : forall msg, Forall (fun z => 0 < z < 256) msg -> map bv_unsigned (map b8 msg) = msg.
Proof. induction msg as [|c msg IH]; intros HF; [reflexivity|]. inversion HF; subst. cbn [map]. f_equal; [unfold b8; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia | apply IH; assumption]. Qed.
Lemma msg_nonul : forall msg, Forall (fun z => 0 < z < 256) msg -> ~ In (Z_to_bv 8 0) (map b8 msg).
Proof.
  intros msg HF Hin. apply in_map_iff in Hin as (z & E & Hz). apply (proj1 (Forall_forall _ _) HF) in Hz.
  unfold b8 in E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap_small in E by (unfold bv_modulus; cbn; lia). lia.
Qed.
(* [comment removed for export] *)
Lemma neg_mod8_slack : forall E T, E mod 8 = 0 -> T <= E -> (- T) mod 8 <= E - T.
Proof.
  intros E T HE HT. replace (- T) with ((E - T) + (- (E / 8)) * 8) by (Z.div_mod_to_equations; lia).
  rewrite Z_mod_plus_full. apply Z.mod_le; lia.
Qed.
Lemma skipn_length_le : forall {A} k (l : list A) n, (n + k <= length l)%nat -> (n <= length (skipn k l))%nat.
Proof. intros A k l n Hl. rewrite length_skipn. lia. Qed.

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma name_bytes_slack : forall m A n (buf pre : list byte) k,
  rw_cells asegs m A [CB n buf] -> firstn k buf = pre ++ [Z_to_bv 8 0] -> bytes_at asegs m A (pre ++ Z_to_bv 8 0 :: skipn k buf).
Proof using .
  intros m A n buf pre k RC E. apply rw_cells_bytes_at in RC. cbn [cells_bytes cbytes] in RC. rewrite app_nil_r in RC.
  rewrite <- (firstn_skipn k buf), E, <- app_assoc in RC. exact RC.
Qed.
End CANSEC0.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FuzzOpen.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FOL : fo_leaf_laws FO.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x58388 0xf8.
  Hypothesis UNLINK : unlink_stmt_o GIOA.
  Hypothesis PSTATS : pcap_stats_stmt GIOA TP.
  Hypothesis PCLOSE : pcap_close_stmt HO FO sites GIOA TP.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO GIOA FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis PNEXT : pcap_next_ex_stmt HO FO sites GIOA TP.
  Hypothesis POPEN : pcap_open_offline_stmt HO FO sites GIOA TP.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Notation PR := (prims HO FO sites).

  (* [comment removed for export] *)
  Definition fz_pcap__stmt : Prop := forall (fu : nat)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (lo SPA Fb : Z) (m : mem) (j1 j2 nbuf ej : list byte) (hpc pkc : cell)
      (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
           [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    implMG RNG (po <- Pcap.pcap_open_offline MOps PR fu TMPNAME ;;
                match po with
                | inl errbuf =>
                    with_outfile MOps PR (fun out => s_fprintf HO out (pieces_couldnt_open (cstr errbuf))) ;;;
                    s_unlink TMPNAME ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt
                | inr p =>
                    p <- packet_loop MOps PR fu fu p ;;
                    '(sr, p) <- Pcap.pcap_stats MOps p ;;
                    (if sr =? 0 then with_outfile MOps PR (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
                    Pcap.pcap_close MOps PR p ;;;
                    s_unlink TMPNAME ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt
                end) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e0894) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) r21 r22 (Z_to_bv 64 (Fb + 352))
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84954) fc None m (seg_rom asegs)).
  Section Sz7.
  Variables fu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m j1 j2 nbuf ej hpc pkc trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_pcap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fu).
  Lemma fz_pcap__body : ltac2:(SecDiet.SzSec.bodyP 'fz_pcap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FFREE7 FOL FPRINTF_DD FPRINTF_S GH GL HAL PCLOSE PNEXT POPEN PSTATS SETSHF8 UNLINK.
 intros HP HR G HC FN NB EBc HPc HP8 PKc PK8 UC TR.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _ & _ & _ & _ & _ & SA & SB & SC).
    pose proof TR as (_ & _ & _ & TRO & TRN1 & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    pose proof (name_bytes_slack _ _ _ _ _ _ FN NB) as NBY.
    pose proof FN as FNc. destruct FNc as [[NWF _] _]. cbn in NWF. destruct NWF as [NLEN _].
    pose proof (skipn_length_le 25 nbuf 4071 ltac:(lia)) as SLK.
    (* [comment removed for export] *)
    assert (NLENZ : Z.of_nat (length nbuf) = 4096%Z) by (clear - NLEN; lia).
    assert (SLKZ : (4071 <= Z.of_nat (length (skipn 25 nbuf)))%Z) by (clear - SLK; lia).
    assert (NLENh : hidc (length nbuf = 4096%nat)) by exact NLEN. clear NLEN SLK.
    pose proof (fz_unp_fname _ _ SB ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UFN.
    pose proof (fz_unp_errbuf _ _ SA ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UEB.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. do 4 zstep.
    rewrite <- tmpname_Z.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply POPEN with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := (Fb + 352)%Z) (EB := (Fb + 32)%Z)
                        (name := tmpname) (slack := skipn 25 nbuf) (ej := ej) (fuel := fu) (trC := bv_unsigned ra :: trC);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold FUZZ_STACK, PCAP_L4_STACK; lia]
        | eapply (fz_ucaller fflagA); [exact UC| exact HP| exact HC| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_open_offline, depth_open_offline_wtp, depth_fuzz_one; lia]
        | rewrite unsigned_lit by lia; exact TRO
        | intros ff Hf [E|[]]; cbn in E; subst ff; unfold frames_open_offline, frames_open_offline_wtp in Hf; cbn in Hf; intuition discriminate
        | reflexivity | reflexivity
        | intros E; unfold PCAP_OPEN_OFFLINE_ENTRY, PCAP_OPEN_OFFLINE_WTP_ENTRY in E; lia
        | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia | exact tmpname_first | exact tmpname_open_r
        | rewrite tmpname_len, length_skipn, (NLENh : length nbuf = 4096%nat); etransitivity; [apply (neg_mod8_slack (Fb + 352 + 4096)); [Z.div_mod_to_equations; lia | lia] | lia]
        | eapply (fz_cobj FO GIOA fflagA GL); [exact G| lia| rewrite tmpname_len; lia| rewrite tmpname_len; lia| eapply unpoisoned_sub; [exact UFN| lia| rewrite tmpname_len; lia]]
        | right; exists (FF_FUZZ_ONE_INPUT, Fb, 8192%Z); split; [left; reflexivity|]; cbn [fb_addr fb_size fst snd]; rewrite tmpname_len, length_skipn, (NLENh : length nbuf = 4096%nat); lia
        | eapply rng_sub; [exact FRNG| lia| rewrite tmpname_len, length_skipn, (NLENh : length nbuf = 4096%nat); lia]
        | exact EBc
        | eapply (fz_cobj FO GIOA fflagA GL); [exact G| lia| lia| lia| exact UEB]
        | Z.div_mod_to_equations; lia
        | right; lia ]. }
    intros po s2' RNG2 ms2 PO. unfold open_result_post in PO.
    destruct PO as (FP2 & a0v & m2 & FB2 & E & OF2 & MI2 & ST2 & AG2 & PO). rewrite ESPA in *. post_regs E.
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun a => ~ (Fb + 32 <= a < Fb + 32 + 256))%Z _ _
                  HC G HP eq_refl eq_refl AG2 ltac:(intros a Ha; lia) MI2 ST2) as HC2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 32 <= a < Fb + 32 + 256))%Z _ _ _ _ FN AG2 ltac:(lia)
                  ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia)) as FN2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 32 <= a < Fb + 32 + 256))%Z _ _ _ _ HPc AG2 ltac:(lia)
                  ltac:(cbn [cells_size]; rewrite HP8; lia) ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite HP8 in Ha; lia)) as HPc2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 32 <= a < Fb + 32 + 256))%Z _ _ _ _ PKc AG2 ltac:(lia)
                  ltac:(cbn [cells_size]; rewrite PK8; lia) ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite PK8 in Ha; lia)) as PKc2.
    pose proof (fz_uc_keep _ _ CL SPA Fb (fun a => ~ (Fb + 32 <= a < Fb + 32 + 256))%Z _ _ _ _ _ _ UC TOP47 AG2 ltac:(lia) ltac:(intros a Ha; lia)) as UC2.
    assert (AGK : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m2).
    { eapply agrees_on_weaken; [exact AG2|]. cbv beta. intros a [Ha|[Ha|[Ha|Ha]]].
      - split; [left; lia| lia].
      - split; [right; left; exact Ha|].
        assert (NF : ~ in_frames (FZFL Fb) a) by (intros K0; apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G K0); apply in_block_app; left; exact Ha).
        assert (NR : ~ (Fb <= a < Fb + 8192)%Z) by (intros K0; apply NF; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia). lia.
      - inversion Ha.
      - inversion Ha. }
    hr_next HR FP2 HR2.
    clear MI MU WM EBc HPc PKc FN UFN UEB SA SB SC NBY UC.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    destruct po as [msg|p].
    - (* [comment removed for export] *)
      destruct PO as (junk' & -> & -> & G2 & HEB & LENM & RNGM).
      rewrite tmpname_Z. apply with_outfile_lA. intros out EO.
      pose proof (gh_outfile _ GH _ _ _ _ _ _ _ G2) as OC. rewrite EO in OC. destruct OC as (Ao & AIN & OC). unfold OUTFILE_ADDR in OC.
      rewrite (msg_cstr _ RNGM). rewrite <- (msg_unsigned _ RNGM).
      assert (HEBB : bytes_at asegs m2 (Fb + 32) (map b8 msg ++ Z_to_bv 8 0 :: junk')).
      { pose proof (rw_cells_bytes_at _ _ _ _ HEB) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r, <- app_assoc in X. exact X. }
      assert (JL : length junk' = (255 - length msg)%nat) by (destruct HEB as [[W _] _]; cbn in W; lia).
      pose proof HC2 as (_ & _ & _ & _ & _ & _ & _ & SA2 & _).
      pose proof (fz_unp_errbuf _ _ SA2 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UEB2.
      ienterG. zstep. if_true. do 5 zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FPRINTF_S with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := FZFL Fb) (f := out) (Af := Ao) (lo := lo) (P := (Fb + 32)%Z)
                              (str := map b8 msg) (slack := junk');
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | exact AIN | reflexivity | reflexivity | reflexivity | exact HEBB | apply msg_nonul; exact RNGM
          | rewrite length_map; lia
          | rewrite length_map, JL; etransitivity; [apply (neg_mod8_slack (Fb + 32 + 256)); [Z.div_mod_to_equations; lia | lia] | lia]
          | eapply (fz_cobj FO GIOA fflagA GL); [exact G2| lia| rewrite length_map; lia| rewrite length_map; lia| eapply unpoisoned_sub; [exact UEB2| lia| rewrite length_map; lia]]
          | rewrite JL; lia ]. }
      intros [] s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & a0v & m3 & E & OF3 & MI3 & ST3 & AG3 & G3). rewrite ESPA in *. post_regs E.
      assert (AGX3 : agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ True) m2 m3) by (eapply agrees_on_weaken; [exact AG3| intros a [K0 _]; exact K0]).
      pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun _ => True) _ _ HC2 G2 HP eq_refl eq_refl AGX3 ltac:(intros; exact I) MI3 ST3) as HC3.
      pose proof (fz_local_keep CL SPA Fb (fun _ => True) _ _ _ _ FN2 AGX3 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros; exact I)) as FN3.
      eapply implMG_mono.
      + eapply (fz_unlink FO GIOA fflagA GL FFREE7 SETSHF8 UNLINK); [exact HP | eapply hrngA_le; [exact HR2| exact FP3] | exact G3 | exact HC3 | reflexivity | exact FN3 | exact NB].
      + intros u sx RNGx msx PO. eapply (fz_post_back GIOA) with (RNG1 := RNG3) (m1 := m3); [intros b j Hb; apply FP3, FP2; exact Hb| | exact PO].
        eapply agrees_on_trans; [exact AGK|]. eapply client_keeps_weaken; [exact AG3| lia| intros a Ha; exact Ha| intros fr0 []].
    - (* [comment removed for export] *)
      destruct PO as (P & PB & -> & [FA ->] & G2 & PC2 & [ej2 HEB]).
      pose proof (PCAPR_unp FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ G2 PC2) as (PUNP & P16 & P0 & PTOP & PRNG & PSRNG). pose proof (psize_pos p) as PSZ.
      (* [comment removed for export] *)
      assert (NOF0 : ps_outfile s2' <> Some (pc_rfile p)) by (eapply (new_file_not_out HO FO GIOA fflagA GL HAL GH); [exact G | exact G2 | exact OF2]).
      pose proof HC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SC2).
      destruct (fz_unp_locals _ _ SC2 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as [UPK UHP].
      rewrite tmpname_Z.
      ienterG. zstep. if_false_by (eqz_false P ltac:(lia)). do 7 zstep.
      apply evtF_done. subst POSTQ. destruct fu as [|fu'].
      + (* [comment removed for export] *) apply implMG_unr.
      + rewrite (packet_loop_S HO FO sites). apply implMG_bind_assoc.
        eapply implMG_bind.
        { eapply implMG_leaf.
          eapply PNEXT with (L := L) (s := s2') (CLc := CL) (PB := PB) (FB := (pc_rfile p, FA, FILE_BLOCK) :: FB) (FL := FZFL Fb) (lo := lo) (P := P)
                            (HP := (Fb + 4608)%Z) (PKT := (Fb + 4576)%Z) (p := p) (fuel := S fu') (hc := hpc) (pkc := pkc) (trC := bv_unsigned ra :: trC);
            [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold FUZZ_STACK, PCAP_L4_STACK; lia]
            | eapply (fz_ucaller fflagA); [exact UC2| exact HP| exact HC2| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_pcap_next_ex, depth_fuzz_one; lia]
            | rewrite unsigned_lit by lia; exact TRN1
            | intros ff Hf [E|[]]; cbn in E; subst ff; unfold frames_pcap_next_ex in Hf; cbn in Hf; intuition discriminate
            | exact PC2 | reflexivity | reflexivity | reflexivity | exact HPc2 | exact HP8 | exact PKc2 | exact PK8
            | eapply (fz_cobj FO GIOA fflagA GL); [exact G2| lia| lia| lia| exact UHP]
            | eapply (fz_cobj FO GIOA fflagA GL); [exact G2| lia| lia| lia| exact UPK]
            | right; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]. }
        intros [st p'] s3' RNG3 ms3 [PO LF]. cbv beta in PO. destruct PO as (FP3 & a0v3 & m3 & PB3 & pk3 & E & OF3 & MI3 & ST3 & AG3 & G3 & PC3 & PCC3 & -> & Hst & HPc3 & PKc3 & PK83).
        apply (pcap_next_ex_rfile HO FO sites FOL) in LF.
        rewrite ESPA in *. post_regs E.
        assert (NOF3 : ps_outfile s3' <> Some (pc_rfile p')) by (rewrite OF3, LF; exact NOF0).
        pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _
                      HC2 G2 HP eq_refl eq_refl AG3 ltac:(intros a Ha; lia) MI3 ST3) as HC3.
        pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _ _ _ FN2 AG3 ltac:(lia)
                      ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia)) as FN3.
        pose proof (fz_uc_keep _ _ CL SPA Fb (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _ _ _ _ _ UC2 TOP47 AG3 ltac:(lia) ltac:(intros a Ha; lia)) as UC3.
        assert (AGK3 : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m3).
        { eapply agrees_on_trans; [exact AGK|]. eapply agrees_on_weaken; [exact AG3|]. cbv beta. intros a [Ha|[Ha|[Ha|Ha]]].
          - split; [left; lia| lia].
          - split; [right; left; exact Ha|].
            assert (NF : ~ in_frames (FZFL Fb) a) by (intros K0; apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G2 K0); apply in_block_app; left; apply in_block_app; left; exact Ha).
            assert (NR : ~ (Fb <= a < Fb + 8192)%Z) by (intros K0; apply NF; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia). lia.
          - inversion Ha.
          - inversion Ha. }
        hr_next HR2 FP3 HR3.
        clear MI2 MU WM HPc2 PKc2 UPK UHP SC2 FN2 PUNP HEB.
        pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        destruct Hst as [-> | Hst].
        * (* [comment removed for export] *)
          ienterG. zstep. change (bv_lts z64 (Z_to_bv 64 1)) with true. cbn [negb]. cbv iota. cbn [Z.ltb Z.compare]. zstep. zstep.
          apply evtF_done. subst POSTQ. eapply implMG_bind.
          { eapply (fz_iter HO FO sites GIOA TP fflagA GL GH FOL FPRINTF_DD PNEXT) with (CL := CL) (PB := PB3) (trC := trC);
              [exact HP| exact HR3| exact G3| exact HC3| exact FN3| exact HPc3| exact PKc3| exact PK83| exact UC3| exact TR| apply PC3; lia| exact NOF3]. }
          intros p4 s4' RNG4 ms4 PO. destruct PO as (FP4 & PO). destruct_exs PO.
          destruct PO as (-> & HR4 & G4 & PCC4 & HC4 & FN4 & UC4 & NOF4 & AG4).
          eapply implMG_mono.
          { eapply (fz_tail HO FO sites GIOA TP fflagA GL FFREE7 SETSHF8 UNLINK PSTATS PCLOSE) with (CL := CL) (trC := trC);
              [exact HP| exact HR4| exact G4| exact HC4| exact FN4| exact NB| exact UC4| exact TR| exact PCC4| exact NOF4]. }
          intros u sx RNGx msx PO.
          lazymatch type of AG4 with agrees_on _ _ ?mm => eapply (fz_post_back GIOA) with (RNG1 := RNG4) (m1 := mm); [intros b j Hb; apply FP4, FP3, FP2; exact Hb| | exact PO] end.
          eapply agrees_on_trans; [exact AGK3| exact AG4].
        * (* [comment removed for export] *)
          assert (PCC : PCAPR_closable P p' PB3 ((pc_rfile p, FA, FILE_BLOCK) :: FB) m3)
            by (destruct Hst as [-> | ->]; [apply PCAPR_closable_of; apply PC3; lia | apply PCC3; reflexivity]).
          ienterG. zstep.
          replace (bv_lts z64 (Z_to_bv 64 st)) with false by (destruct Hst as [-> | ->]; reflexivity). cbn [negb]. cbv iota.
          replace (0 <? st)%Z with false by (destruct Hst as [-> | ->]; reflexivity).
          apply evtF_done. subst POSTQ. apply implMG_retb.
          eapply implMG_mono.
          { eapply (fz_tail HO FO sites GIOA TP fflagA GL FFREE7 SETSHF8 UNLINK PSTATS PCLOSE) with (CL := CL) (trC := trC);
              [exact HP| exact HR3| exact G3| exact HC3| exact FN3| exact NB| exact UC3| exact TR| exact PCC| exact NOF3]. }
          intros u sx RNGx msx PO.
          eapply (fz_post_back GIOA) with (RNG1 := RNG3) (m1 := m3); [intros b j Hb; apply FP3, FP2; exact Hb| exact AGK3 | exact PO].
  Qed.
  End Sz7.
  Lemma fz_pcap : ltac:(let t := eval cbv delta [fz_pcap__stmt] in fz_pcap__stmt in exact t).
  Proof using FFREE7 FOL FPRINTF_DD FPRINTF_S GH GL HAL PCLOSE PNEXT POPEN PSTATS SETSHF8 UNLINK. intros fu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m j1 j2 nbuf ej hpc pkc trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_pcap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzOpen.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_pcap_open2A__A3P.F_pcap_open2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_tailA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_loopA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

(* [comment removed for export] *)
Lemma msg_cstr : forall msg, Forall (fun z => 0 < z < 256) msg -> cstr msg = msg.
Proof. induction msg as [|c msg IH]; intros HF; [reflexivity|]. inversion HF; subst. cbn. destruct (Z.eqb_spec c 0); [lia|]. f_equal. apply IH. assumption. Qed.
Lemma msg_unsigned : forall msg, Forall (fun z => 0 < z < 256) msg -> map bv_unsigned (map b8 msg) = msg.
Proof. induction msg as [|c msg IH]; intros HF; [reflexivity|]. inversion HF; subst. cbn [map]. f_equal; [unfold b8; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia | apply IH; assumption]. Qed.
Lemma msg_nonul : forall msg, Forall (fun z => 0 < z < 256) msg -> ~ In (Z_to_bv 8 0) (map b8 msg).
Proof.
  intros msg HF Hin. apply in_map_iff in Hin as (z & E & Hz). apply (proj1 (Forall_forall _ _) HF) in Hz.
  unfold b8 in E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned, !bv_wrap_small in E by (unfold bv_modulus; cbn; lia). lia.
Qed.
(* [comment removed for export] *)
Lemma neg_mod8_slack : forall E T, E mod 8 = 0 -> T <= E -> (- T) mod 8 <= E - T.
Proof.
  intros E T HE HT. replace (- T) with ((E - T) + (- (E / 8)) * 8) by (Z.div_mod_to_equations; lia).
  rewrite Z_mod_plus_full. apply Z.mod_le; lia.
Qed.
Lemma skipn_length_le : forall {A} k (l : list A) n, (n + k <= length l)%nat -> (n <= length (skipn k l))%nat.
Proof. intros A k l n Hl. rewrite length_skipn. lia. Qed.

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma name_bytes_slack : forall m A n (buf pre : list byte) k,
  rw_cells asegs m A [CB n buf] -> firstn k buf = pre ++ [Z_to_bv 8 0] -> bytes_at asegs m A (pre ++ Z_to_bv 8 0 :: skipn k buf).
Proof using .
  intros m A n buf pre k RC E. apply rw_cells_bytes_at in RC. cbn [cells_bytes cbytes] in RC. rewrite app_nil_r in RC.
  rewrite <- (firstn_skipn k buf), E, <- app_assoc in RC. exact RC.
Qed.
End CANSEC0.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FuzzOpen.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FOL : fo_leaf_laws FO.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x583f0 0xf8.
  Hypothesis UNLINK : unlink_stmt_o GIOA.
  Hypothesis PSTATS : pcap_stats_stmt GIOA TP.
  Hypothesis PCLOSE : pcap_close_stmt HO FO sites GIOA TP.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO GIOA FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis PNEXT : pcap_next_ex_stmt HO FO sites GIOA TP.
  Hypothesis POPEN : pcap_open_offline_stmt HO FO sites GIOA TP.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Notation PR := (prims HO FO sites).

  (* [comment removed for export] *)
  Definition fz_pcap__stmt : Prop := forall (fu : nat)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (lo SPA Fb : Z) (m : mem) (j1 j2 nbuf ej : list byte) (hpc pkc : cell)
      (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
           [CB 24 j1; C8 (Z_to_bv 64 Fb); CB 24 j2] m ->
    rw_cells asegs m (Fb + 352) [CB 4096 nbuf] -> firstn 25 nbuf = tmpname ++ [Z_to_bv 8 0] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    implMG RNG (po <- Pcap.pcap_open_offline MOps PR fu TMPNAME ;;
                match po with
                | inl errbuf =>
                    with_outfile MOps PR (fun out => s_fprintf HO out (pieces_couldnt_open (cstr errbuf))) ;;;
                    s_unlink TMPNAME ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt
                | inr p =>
                    p <- packet_loop MOps PR fu fu p ;;
                    '(sr, p) <- Pcap.pcap_stats MOps p ;;
                    (if sr =? 0 then with_outfile MOps PR (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
                    Pcap.pcap_close MOps PR p ;;;
                    s_unlink TMPNAME ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt
                end) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e08fc) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) r21 r22 (Z_to_bv 64 (Fb + 352))
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x849c8) fc None m (seg_rom asegs)).
  Section Sz7.
  Variables fu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m j1 j2 nbuf ej hpc pkc trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_pcap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fu).
  Lemma fz_pcap__body : ltac2:(SecDiet.SzSec.bodyP 'fz_pcap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FFREE7 FOL FPRINTF_DD FPRINTF_S GH GL HAL PCLOSE PNEXT POPEN PSTATS SETSHF8 UNLINK.
 intros HP HR G HC FN NB EBc HPc HP8 PKc PK8 UC TR.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _ & _ & _ & _ & _ & SA & SB & SC).
    pose proof TR as (_ & _ & _ & TRO & TRN1 & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    pose proof (name_bytes_slack _ _ _ _ _ _ FN NB) as NBY.
    pose proof FN as FNc. destruct FNc as [[NWF _] _]. cbn in NWF. destruct NWF as [NLEN _].
    pose proof (skipn_length_le 25 nbuf 4071 ltac:(lia)) as SLK.
    (* [comment removed for export] *)
    assert (NLENZ : Z.of_nat (length nbuf) = 4096%Z) by (clear - NLEN; lia).
    assert (SLKZ : (4071 <= Z.of_nat (length (skipn 25 nbuf)))%Z) by (clear - SLK; lia).
    assert (NLENh : hidc (length nbuf = 4096%nat)) by exact NLEN. clear NLEN SLK.
    pose proof (fz_unp_fname _ _ SB ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UFN.
    pose proof (fz_unp_errbuf _ _ SA ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UEB.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. do 4 zstep.
    rewrite <- tmpname_Z.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply POPEN with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := (Fb + 352)%Z) (EB := (Fb + 32)%Z)
                        (name := tmpname) (slack := skipn 25 nbuf) (ej := ej) (fuel := fu) (trC := bv_unsigned ra :: trC);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold FUZZ_STACK, PCAP_L4_STACK; lia]
        | eapply (fz_ucaller fflagA); [exact UC| exact HP| exact HC| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_open_offline, depth_open_offline_wtp, depth_fuzz_one; lia]
        | rewrite unsigned_lit by lia; exact TRO
        | intros ff Hf [E|[]]; cbn in E; subst ff; unfold frames_open_offline, frames_open_offline_wtp in Hf; cbn in Hf; intuition discriminate
        | reflexivity | reflexivity
        | intros E; unfold PCAP_OPEN_OFFLINE_ENTRY, PCAP_OPEN_OFFLINE_WTP_ENTRY in E; lia
        | exact NBY | exact tmpname_nonul | rewrite tmpname_len; lia | exact tmpname_first | exact tmpname_open_r
        | rewrite tmpname_len, length_skipn, (NLENh : length nbuf = 4096%nat); etransitivity; [apply (neg_mod8_slack (Fb + 352 + 4096)); [Z.div_mod_to_equations; lia | lia] | lia]
        | eapply (fz_cobj FO GIOA fflagA GL); [exact G| lia| rewrite tmpname_len; lia| rewrite tmpname_len; lia| eapply unpoisoned_sub; [exact UFN| lia| rewrite tmpname_len; lia]]
        | right; exists (FF_FUZZ_ONE_INPUT, Fb, 8192%Z); split; [left; reflexivity|]; cbn [fb_addr fb_size fst snd]; rewrite tmpname_len, length_skipn, (NLENh : length nbuf = 4096%nat); lia
        | eapply rng_sub; [exact FRNG| lia| rewrite tmpname_len, length_skipn, (NLENh : length nbuf = 4096%nat); lia]
        | exact EBc
        | eapply (fz_cobj FO GIOA fflagA GL); [exact G| lia| lia| lia| exact UEB]
        | Z.div_mod_to_equations; lia
        | right; lia ]. }
    intros po s2' RNG2 ms2 PO. unfold open_result_post in PO.
    destruct PO as (FP2 & a0v & m2 & FB2 & E & OF2 & MI2 & ST2 & AG2 & PO). rewrite ESPA in *. post_regs E.
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun a => ~ (Fb + 32 <= a < Fb + 32 + 256))%Z _ _
                  HC G HP eq_refl eq_refl AG2 ltac:(intros a Ha; lia) MI2 ST2) as HC2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 32 <= a < Fb + 32 + 256))%Z _ _ _ _ FN AG2 ltac:(lia)
                  ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia)) as FN2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 32 <= a < Fb + 32 + 256))%Z _ _ _ _ HPc AG2 ltac:(lia)
                  ltac:(cbn [cells_size]; rewrite HP8; lia) ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite HP8 in Ha; lia)) as HPc2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 32 <= a < Fb + 32 + 256))%Z _ _ _ _ PKc AG2 ltac:(lia)
                  ltac:(cbn [cells_size]; rewrite PK8; lia) ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite PK8 in Ha; lia)) as PKc2.
    pose proof (fz_uc_keep _ _ CL SPA Fb (fun a => ~ (Fb + 32 <= a < Fb + 32 + 256))%Z _ _ _ _ _ _ UC TOP47 AG2 ltac:(lia) ltac:(intros a Ha; lia)) as UC2.
    assert (AGK : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m2).
    { eapply agrees_on_weaken; [exact AG2|]. cbv beta. intros a [Ha|[Ha|[Ha|Ha]]].
      - split; [left; lia| lia].
      - split; [right; left; exact Ha|].
        assert (NF : ~ in_frames (FZFL Fb) a) by (intros K0; apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G K0); apply in_block_app; left; exact Ha).
        assert (NR : ~ (Fb <= a < Fb + 8192)%Z) by (intros K0; apply NF; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia). lia.
      - inversion Ha.
      - inversion Ha. }
    hr_next HR FP2 HR2.
    clear MI MU WM EBc HPc PKc FN UFN UEB SA SB SC NBY UC.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    destruct po as [msg|p].
    - (* [comment removed for export] *)
      destruct PO as (junk' & -> & -> & G2 & HEB & LENM & RNGM).
      rewrite tmpname_Z. apply with_outfile_lA. intros out EO.
      pose proof (gh_outfile _ GH _ _ _ _ _ _ _ G2) as OC. rewrite EO in OC. destruct OC as (Ao & AIN & OC). unfold OUTFILE_ADDR in OC.
      rewrite (msg_cstr _ RNGM). rewrite <- (msg_unsigned _ RNGM).
      assert (HEBB : bytes_at asegs m2 (Fb + 32) (map b8 msg ++ Z_to_bv 8 0 :: junk')).
      { pose proof (rw_cells_bytes_at _ _ _ _ HEB) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r, <- app_assoc in X. exact X. }
      assert (JL : length junk' = (255 - length msg)%nat) by (destruct HEB as [[W _] _]; cbn in W; lia).
      pose proof HC2 as (_ & _ & _ & _ & _ & _ & _ & SA2 & _).
      pose proof (fz_unp_errbuf _ _ SA2 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as UEB2.
      ienterG. zstep. if_true. do 5 zstep.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FPRINTF_S with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := FZFL Fb) (f := out) (Af := Ao) (lo := lo) (P := (Fb + 32)%Z)
                              (str := map b8 msg) (slack := junk');
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | exact AIN | reflexivity | reflexivity | reflexivity | exact HEBB | apply msg_nonul; exact RNGM
          | rewrite length_map; lia
          | rewrite length_map, JL; etransitivity; [apply (neg_mod8_slack (Fb + 32 + 256)); [Z.div_mod_to_equations; lia | lia] | lia]
          | eapply (fz_cobj FO GIOA fflagA GL); [exact G2| lia| rewrite length_map; lia| rewrite length_map; lia| eapply unpoisoned_sub; [exact UEB2| lia| rewrite length_map; lia]]
          | rewrite JL; lia ]. }
      intros [] s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & a0v & m3 & E & OF3 & MI3 & ST3 & AG3 & G3). rewrite ESPA in *. post_regs E.
      assert (AGX3 : agrees_on (fun a => client_keeps (FZFL Fb) CL SPA a /\ True) m2 m3) by (eapply agrees_on_weaken; [exact AG3| intros a [K0 _]; exact K0]).
      pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun _ => True) _ _ HC2 G2 HP eq_refl eq_refl AGX3 ltac:(intros; exact I) MI3 ST3) as HC3.
      pose proof (fz_local_keep CL SPA Fb (fun _ => True) _ _ _ _ FN2 AGX3 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros; exact I)) as FN3.
      (* [comment removed for export] *)
      try clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      ienterG. zstep. apply evtF_done. subst POSTQ.
      eapply implMG_mono.
      + eapply (fz_unlink FO GIOA fflagA GL FFREE7 SETSHF8 UNLINK); [exact HP | eapply hrngA_le; [exact HR2| exact FP3] | exact G3 | exact HC3 | reflexivity | exact FN3 | exact NB].
      + intros u sx RNGx msx PO. eapply (fz_post_back GIOA) with (RNG1 := RNG3) (m1 := m3); [intros b j Hb; apply FP3, FP2; exact Hb| | exact PO].
        eapply agrees_on_trans; [exact AGK|]. eapply client_keeps_weaken; [exact AG3| lia| intros a Ha; exact Ha| intros fr0 []].
    - (* [comment removed for export] *)
      destruct PO as (P & PB & -> & [FA ->] & G2 & PC2 & [ej2 HEB]).
      pose proof (PCAPR_unp FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ G2 PC2) as (PUNP & P16 & P0 & PTOP & PRNG & PSRNG). pose proof (psize_pos p) as PSZ.
      (* [comment removed for export] *)
      assert (NOF0 : ps_outfile s2' <> Some (pc_rfile p)) by (eapply (new_file_not_out HO FO GIOA fflagA GL HAL GH); [exact G | exact G2 | exact OF2]).
      pose proof HC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SC2).
      destruct (fz_unp_locals _ _ SC2 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)) as [UPK UHP].
      rewrite tmpname_Z.
      ienterG. zstep. if_false_by (eqz_false P ltac:(lia)). do 7 zstep.
      apply evtF_done. subst POSTQ. destruct fu as [|fu'].
      + (* [comment removed for export] *) apply implMG_unr.
      + rewrite (packet_loop_S HO FO sites). apply implMG_bind_assoc.
        eapply implMG_bind.
        { eapply implMG_leaf.
          eapply PNEXT with (L := L) (s := s2') (CLc := CL) (PB := PB) (FB := (pc_rfile p, FA, FILE_BLOCK) :: FB) (FL := FZFL Fb) (lo := lo) (P := P)
                            (HP := (Fb + 4608)%Z) (PKT := (Fb + 4576)%Z) (p := p) (fuel := S fu') (hc := hpc) (pkc := pkc) (trC := bv_unsigned ra :: trC);
            [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold FUZZ_STACK, PCAP_L4_STACK; lia]
            | eapply (fz_ucaller fflagA); [exact UC2| exact HP| exact HC2| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_pcap_next_ex, depth_fuzz_one; lia]
            | rewrite unsigned_lit by lia; exact TRN1
            | intros ff Hf [E|[]]; cbn in E; subst ff; unfold frames_pcap_next_ex in Hf; cbn in Hf; intuition discriminate
            | exact PC2 | reflexivity | reflexivity | reflexivity | exact HPc2 | exact HP8 | exact PKc2 | exact PK8
            | eapply (fz_cobj FO GIOA fflagA GL); [exact G2| lia| lia| lia| exact UHP]
            | eapply (fz_cobj FO GIOA fflagA GL); [exact G2| lia| lia| lia| exact UPK]
            | right; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]. }
        intros [st p'] s3' RNG3 ms3 [PO LF]. cbv beta in PO. destruct PO as (FP3 & a0v3 & m3 & PB3 & pk3 & E & OF3 & MI3 & ST3 & AG3 & G3 & PC3 & PCC3 & -> & Hst & HPc3 & PKc3 & PK83).
        apply (pcap_next_ex_rfile HO FO sites FOL) in LF.
        rewrite ESPA in *. post_regs E.
        assert (NOF3 : ps_outfile s3' <> Some (pc_rfile p')) by (rewrite OF3, LF; exact NOF0).
        pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _
                      HC2 G2 HP eq_refl eq_refl AG3 ltac:(intros a Ha; lia) MI3 ST3) as HC3.
        pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _ _ _ FN2 AG3 ltac:(lia)
                      ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia)) as FN3.
        pose proof (fz_uc_keep _ _ CL SPA Fb (fun a => ~ (Fb + 4608 <= a < Fb + 4608 + 8) /\ ~ (Fb + 4576 <= a < Fb + 4576 + 8))%Z _ _ _ _ _ _ UC2 TOP47 AG3 ltac:(lia) ltac:(intros a Ha; lia)) as UC3.
        assert (AGK3 : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m3).
        { eapply agrees_on_trans; [exact AGK|]. eapply agrees_on_weaken; [exact AG3|]. cbv beta. intros a [Ha|[Ha|[Ha|Ha]]].
          - split; [left; lia| lia].
          - split; [right; left; exact Ha|].
            assert (NF : ~ in_frames (FZFL Fb) a) by (intros K0; apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G2 K0); apply in_block_app; left; apply in_block_app; left; exact Ha).
            assert (NR : ~ (Fb <= a < Fb + 8192)%Z) by (intros K0; apply NF; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia). lia.
          - inversion Ha.
          - inversion Ha. }
        hr_next HR2 FP3 HR3.
        clear MI2 MU WM HPc2 PKc2 UPK UHP SC2 FN2 PUNP HEB.
        pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        destruct Hst as [-> | Hst].
        * (* [comment removed for export] *)
          ienterG. zstep. change (bv_lts z64 (Z_to_bv 64 1)) with true. cbn [negb]. cbv iota. cbn [Z.ltb Z.compare]. zstep. zstep.
          apply evtF_done. subst POSTQ. eapply implMG_bind.
          { eapply (fz_iter HO FO sites GIOA TP fflagA GL GH FOL FPRINTF_DD PNEXT) with (CL := CL) (PB := PB3) (trC := trC);
              [exact HP| exact HR3| exact G3| exact HC3| exact FN3| exact HPc3| exact PKc3| exact PK83| exact UC3| exact TR| apply PC3; lia| exact NOF3]. }
          intros p4 s4' RNG4 ms4 PO. destruct PO as (FP4 & PO). destruct_exs PO.
          destruct PO as (-> & HR4 & G4 & PCC4 & HC4 & FN4 & UC4 & NOF4 & AG4).
          eapply implMG_mono.
          { eapply (fz_tail HO FO sites GIOA TP fflagA GL FFREE7 SETSHF8 UNLINK PSTATS PCLOSE) with (CL := CL) (trC := trC);
              [exact HP| exact HR4| exact G4| exact HC4| exact FN4| exact NB| exact UC4| exact TR| exact PCC4| exact NOF4]. }
          intros u sx RNGx msx PO.
          lazymatch type of AG4 with agrees_on _ _ ?mm => eapply (fz_post_back GIOA) with (RNG1 := RNG4) (m1 := mm); [intros b j Hb; apply FP4, FP3, FP2; exact Hb| | exact PO] end.
          eapply agrees_on_trans; [exact AGK3| exact AG4].
        * (* [comment removed for export] *)
          assert (PCC : PCAPR_closable P p' PB3 ((pc_rfile p, FA, FILE_BLOCK) :: FB) m3)
            by (destruct Hst as [-> | ->]; [apply PCAPR_closable_of; apply PC3; lia | apply PCC3; reflexivity]).
          ienterG. zstep.
          replace (bv_lts z64 (Z_to_bv 64 st)) with false by (destruct Hst as [-> | ->]; reflexivity). cbn [negb]. cbv iota.
          replace (0 <? st)%Z with false by (destruct Hst as [-> | ->]; reflexivity).
          apply evtF_done. subst POSTQ. apply implMG_retb.
          eapply implMG_mono.
          { eapply (fz_tail HO FO sites GIOA TP fflagA GL FFREE7 SETSHF8 UNLINK PSTATS PCLOSE) with (CL := CL) (trC := trC);
              [exact HP| exact HR3| exact G3| exact HC3| exact FN3| exact NB| exact UC3| exact TR| exact PCC| exact NOF3]. }
          intros u sx RNGx msx PO.
          eapply (fz_post_back GIOA) with (RNG1 := RNG3) (m1 := m3); [intros b j Hb; apply FP3, FP2; exact Hb| exact AGK3 | exact PO].
  Qed.
  End Sz7.
  Lemma fz_pcap : ltac:(let t := eval cbv delta [fz_pcap__stmt] in fz_pcap__stmt in exact t).
  Proof using FFREE7 FOL FPRINTF_DD FPRINTF_S GH GL HAL PCLOSE PNEXT POPEN PSTATS SETSHF8 UNLINK. intros fu ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb m j1 j2 nbuf ej hpc pkc trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r21 r22 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_pcap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzOpen.
End CANSEC1.
End TwB.
End F_fuzz_openA.

(* [comment removed for export] *)
Module F_fuzz_bodyA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_tailA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_openA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_btfA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Definition tmplb : list byte := map b8 TEMPLATE.
Lemma tmplb_Z : map bv_unsigned tmplb = TEMPLATE.
Proof. vm_compute. reflexivity. Qed.
Lemma tmplb_nonul : ~ In (Z_to_bv 8 0) tmplb.
Proof. unfold tmplb, TEMPLATE. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
Definition template : list byte := map b8 TEMPLATE ++ [Z_to_bv 8 0].
Lemma template_len : length template = 30%nat.
Proof. reflexivity. Qed.
Section CANSEC0. Context {rc : runConstT}.
#[using="Type"] Lemma rodata_template : forall m, mem_inv asegs m -> bytes_at asegs m STR_TEMPLATE template.
Proof.
  intros m MI. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m STR_TEMPLATE template MI ltac:(vm_compute; reflexivity) ltac:(unfold STR_TEMPLATE; lia) ltac:(unfold STR_TEMPLATE, template, TEMPLATE; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ map app str String.list_ascii_of_string]; lia))).
Qed.
End CANSEC0.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FuzzBody.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOL : fo_leaf_laws FO.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x58388 0xf8.
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FWRITE : fwrite_stmt_o HO GIOA.
  Hypothesis REMOVE : remove_stmt_o GIOA.
  Hypothesis UNLINK : unlink_stmt_o GIOA.
  Hypothesis CLOSE : close_stmt_o GIOA.
  Hypothesis MKSTEMP : mkstemp_stmt_o GIOA.
  Hypothesis PRINTF_R : printf_d_stmt_o GIOA FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o GIOA FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO GIOA FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO FO sites GIOA TP.
  Hypothesis PNEXT : pcap_next_ex_stmt HO FO sites GIOA TP.
  Hypothesis PSTATS : pcap_stats_stmt GIOA TP.
  Hypothesis PCLOSE : pcap_close_stmt HO FO sites GIOA TP.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PR := (prims HO FO sites).

  (* [comment removed for export] *)
  Definition fuzz_bodyA (data : list Z) : Monad.M PSt unit :=
    '(filename, fd) <- s_mkstemp TEMPLATE ;;
    if (fd <? 0)%Z then fo_ret FO _ FF_FUZZ_ONE_INPUT tt else
    s_close fd ;;;
    r <- bufferToFile MOps PR filename data ;;
    if (r <? 0)%Z then s_unlink filename ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt else
    po <- Pcap.pcap_open_offline MOps PR (S (length data)) filename ;;
    match po with
    | inl errbuf =>
        with_outfile MOps PR (fun out => s_fprintf HO out (pieces_couldnt_open (cstr errbuf))) ;;;
        s_unlink filename ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt
    | inr p =>
        p <- packet_loop MOps PR (S (length data)) (S (length data)) p ;;
        '(sr, p) <- Pcap.pcap_stats MOps p ;;
        (if (sr =? 0)%Z then with_outfile MOps PR (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
        Pcap.pcap_close MOps PR p ;;;
        s_unlink filename ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt
    end.

  #[using="Type"] Lemma fuzz_unfoldA : forall data,
    LLVMFuzzerTestOneInput MOps PR data =
    fo_enter FO _ FF_FUZZ_ONE_INPUT
      (o0 <- (s <- mget ;; mret (ps_outfile s)) ;;
       o <- match o0 with
            | Some f => mret (Some f)
            | None => fo <- s_fopen HO DEVNULL true ;; mupd (set_outfile fo) ;;; mret fo
            end ;;
       match o with None => fo_ret FO _ FF_FUZZ_ONE_INPUT tt | Some _ => fuzz_bodyA data end).
  Proof. intros data. reflexivity. Qed.
  (* [comment removed for export] *)
  Definition fz_body__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (lo SPA Fb D : Z) (m : mem) (fra : list cell) (jn ej : list byte) (hpc pkc : cell)
      (data : list byte) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 30 jn] -> rw_cells asegs m (Fb + 382) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    datA RNG m CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (fuzz_bodyA (map bv_unsigned data)) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e0894) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) r23
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x848bc) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra jn ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_body__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL GH HAL EQB FOL FFREE7 SETSHF8 FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O FPRINTF_DD FPRINTF_S POPEN PNEXT PSTATS PCLOSE"] Lemma fz_body__body : ltac2:(SecDiet.SzSec.bodyP 'fz_body__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HP HR G HC FRAS FNT FNZ EBc HPc HP8 PKc PK8 UC TR DAT DLEN.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    destruct HC as (MI & ST & STG & FRA & FRs & (k0 & FK0) & FLG & SA & SB & SC). unfold SHA, SHB, SHC in SA, SB, SC.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    band_ind FBAND bF.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jf FRA']. clear FRA. rewrite FRAS in FRA'.
    pose proof (rodata_template m MI) as TMP.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
    assert (UFN : unpoisoned m (Fb + 352) (Fb + 352 + 4096)) by (eapply (fz_unp_fname m Fb); [exact SB| Z.div_mod_to_equations; lia| lia| lia]).
    assert (OSRC : mobjA RNG m STR_TEMPLATE 30)
      by (eapply (gia_global_mobjA _ _ _ GL); [exact G| unfold client_globals, STR_TEMPLATE; repeat (first [left; reflexivity | right]) | exact RIMG| exact RISH]).
    assert (ODST : mobjA RNG m (Fb + 352) 30).
    { apply aobjA_mobjA; [| lia].
      assert (CO : cobjA RNG m (FZFL Fb) CL (Fb + 352) 30)
        by (eapply (fz_cobj FO GIOA fflagA GL); [exact G| lia| lia| lia| eapply unpoisoned_sub; [exact UFN| lia| lia]]).
      exact (proj2 CO). }
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    pose proof (munch_refl [(SPA - 4096, SPA); (Fb, Fb + 8192)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold fuzz_bodyA.
    ienterG. do 6 zstep.
    (* [comment removed for export] *)
    clear ESPA. remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply asan_memcpy_specZ with (lo := lo) (Dst := (Fb + 352)%Z) (Src := STR_TEMPLATE) (n := 30%Z) (src := template) (junk := jn);
        [ reflexivity | reflexivity | reflexivity | assumption | rewrite Hspa; exact ST | rewrite Hspa; lia | lia | exact RT | exact TMP | reflexivity | lia
        | exact FNT | unfold STR_TEMPLATE; lia | exact OSRC | exact ODST | unfold STR_TEMPLATE; lia | lia | exact RIMG
        | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] ]. }
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (E & MU1 & WM1 & MI1 & ST1 & FNT1 & TMP1).
    subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    replace (ret_pc (Z_to_bv 64 542932)) with (Z_to_bv 64 542932) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch type of MU1 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU1 WM1 end.
    change (Z.to_nat 30) with 30%nat in FNT1.
    lazymatch type of MU with munch _ _ ?m1 =>
      assert (NBUF : rw_cells asegs m1 (Fb + 352) [CB 4096 (template ++ repeat (Z_to_bv 8 0) 4066)]);
      [ pose proof (rw_cells_merge asegs m1 (Fb + 352) [] [CB 30 template; CB 4066 (repeat (Z_to_bv 8 0) 4066)] []) as X |] end.
    { cbn [app cells_size csize cells_bytes cbytes Nat.add] in X. rewrite app_nil_r in X. apply X.
      apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact FNT1|]. cbn [cells_size csize Nat.add].
      replace (Fb + 352 + Z.of_nat 30)%Z with (Fb + 382)%Z by lia. exact FNZ. }
    clear FNT1 FNZ TMP1 OSRC ODST RT.
    assert (FW : Forall (own_ivA (FZFL Fb) ([] : list cblk) (bv_unsigned sp)) [(SPA - 4096, SPA); (Fb, Fb + 8192)]%Z) by own_ivs.
    lazymatch type of MU with munch _ _ ?mm =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FW (Forall_nil _) G' MU WM ltac:(lia)) as [G1 AG1] end.
    rewrite app_nil_r in G1. cbn [app] in G1.
    lazymatch type of MU with munch _ _ ?mm =>
      assert (AG1' : agrees_on (client_keeps [] CL (bv_unsigned sp)) m mm) by (eapply agrees_on_weaken; [exact AG1| intros a K0; split; [exact K0| exact I]]);
      assert (UC1 : ucallerA depth_fuzz_one L mm sp s0 ra trC)
        by (eapply ucaller_keep; [exact UC| exact TOP47|]; intros a Ha; apply (AG1' a); [lia| left; lia]);
      assert (HC1 : hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [CB 56 jf] mm)
        by (split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exists k0; assumption|];
            split; [assumption|]; split; [exact SA|]; split; [exact SB| exact SC])
    end.
    pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT AG1' G1) as DAT1.
    assert (ONAME : cobjA RNG x13 (FZFL Fb) CL (Fb + 352) (Z.of_nat 4096))
      by (eapply (fz_cobj FO GIOA fflagA GL); [exact G1| lia| lia| lia| exact UFN]).
    clear G' FW G UC DAT AG1 MI MU1 WM1.
    do 2 zstep.
    rewrite <- tmplb_Z.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply implMG_leaf.
      eapply MKSTEMP with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := (Fb + 352)%Z) (n := 4096%nat) (tmpl := tmplb)
                          (buf := template ++ repeat (Z_to_bv 8 0) 4066);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G1| assumption| assumption| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | reflexivity | exact NBUF | vm_compute; reflexivity | exact tmplb_nonul | reflexivity | cbn; lia | lia | exact ONAME ]. }
    intros [fn fd] s2' RNG2 ms2 [PO LF]. cbv beta in PO. cbn [fst snd] in PO.
    (* [comment removed for export] *)
    pose (N4096 := 4096%nat); change 4096%nat with N4096 in PO.
    destruct PO as (FP2 & a0v & m2 & buf' & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & Hfd & NBUF2 & NB2 & RNGf & LENf & SHAPE).
    repeat match goal with H : context [N4096] |- _ => unfold N4096 in H end. clear N4096.
    rewrite ESPA in *. post_regs E.
    rewrite tmplb_Z in LF. apply mkstemp_leaf in LF. subst fn.
    replace (length TMPNAME + 1)%nat with 25%nat in NB2 by reflexivity. change (map b8 TMPNAME) with tmpname in NB2.
    change (Z.of_nat 4096) with 4096%Z in AG2.
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun a => ~ (Fb + 352 <= a < Fb + 352 + 4096))%Z _ _
                  HC1 G1 HP eq_refl eq_refl AG2 ltac:(intros a Ha; lia) MI2 ST2) as HC2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 352 <= a < Fb + 352 + 4096))%Z _ _ _ _ EBc AG2 ltac:(lia)
                  ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia)) as EBc2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 352 <= a < Fb + 352 + 4096))%Z _ _ _ _ HPc AG2 ltac:(lia)
                  ltac:(cbn [cells_size]; rewrite HP8; lia) ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite HP8 in Ha; lia)) as HPc2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 352 <= a < Fb + 352 + 4096))%Z _ _ _ _ PKc AG2 ltac:(lia)
                  ltac:(cbn [cells_size]; rewrite PK8; lia) ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite PK8 in Ha; lia)) as PKc2.
    pose proof (fz_uc_keep _ _ CL SPA Fb (fun a => ~ (Fb + 352 <= a < Fb + 352 + 4096))%Z _ _ _ _ _ _ UC1 TOP47 AG2 ltac:(lia) ltac:(intros a Ha; lia)) as UC2.
    assert (AGC2 : agrees_on (client_keeps [] CL (bv_unsigned sp)) x13 m2).
    { eapply agrees_on_weaken; [exact AG2|]. cbv beta. intros a [Ha|[Ha|[Ha|Ha]]].
      - split; [left; lia| lia].
      - split; [right; left; exact Ha|].
        assert (NF : ~ in_frames (FZFL Fb) a) by (intros K0; apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G1 K0); apply in_block_app; left; exact Ha).
        assert (NR : ~ (Fb <= a < Fb + 8192)%Z) by (intros K0; apply NF; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia). lia.
      - inversion Ha.
      - inversion Ha. }
    pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT1 AGC2 G2) as DAT2.
    assert (AGK2 : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m2) by (eapply agrees_on_trans; [exact AG1'| exact AGC2]).
    hr_next HR FP2 HR2.
    clear STG FRs FK0 FLG SA SB SC EBc HPc PKc FRA' UFN MU WM MI1 ST1 NBUF ONAME.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    cbv beta iota.
    ienterG. zstep.
    destruct Hfd as [Efd|Hpos].
    - (* [comment removed for export] *)
      rewrite Efd. change (bv_lts (Z_to_bv 64 (-1)) z64) with true. cbn [Z.ltb Z.compare]. cbv iota.
      apply evtF_done. subst POSTQ.
      eapply implMG_mono.
      { eapply (fz_exitK FO GIOA fflagA GL FFREE7 SETSHF8); [exact HP| exact HR2| exact G2| exact HC2| reflexivity]. }
      intros u sx RNGx msx PO. eapply (fz_post_back GIOA) with (RNG1 := RNG2) (m1 := m2); [exact FP2| exact AGK2| exact PO].
    - (* [comment removed for export] *)
      rewrite bv_lts_zero_r, unsigned_lit by lia. replace (2 ^ 63 <=? fd)%Z with false by (symmetry; apply Z.leb_gt; lia).
      replace (fd <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      zstep. apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply CLOSE with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (fd := fd);
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | reflexivity | lia ]. }
      intros rclose s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & a0v & m3 & E & OF3 & MI3 & ST3 & AG3 & G3). rewrite ESPA in *. post_regs E.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC2 G2 HP eq_refl eq_refl AG3 MI3 ST3) as HC3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ NBUF2 AG3 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as FN3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc2 AG3 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as EBc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc3.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC2 TOP47 AG3 ltac:(lia)) as UC3.
      pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT2 AG3 G3) as DAT3.
      hr_next HR2 FP3 HR3.
      assert (AGK3 : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m3) by (eapply agrees_on_trans; [exact AGK2| eapply fz_ag_final; [exact AG3| lia]]).
      clear MI2 MU WM NBUF2 EBc2 HPc2 PKc2.
      eapply implMG_bind.
      { eapply (fz_btf HO FO sites GIOA TP fflagA GL GH HAL EQB FOPEN FCLOSE FWRITE REMOVE PRINTF_R PRINTF_O) with (trC := trC);
          [exact HP| exact HR3| exact G3| exact HC3| reflexivity| exact FN3| exact NB2| exact EBc3| exact HPc3| exact HP8| exact PKc3| exact PK8
          | exact UC3| exact TR| exact DAT3| exact DLEN]. }
      intros r s4' RNG4 ms4 PO.
      (* [comment removed for export] *)
      unfold btf_postA in PO. pose (NBc := [CB 4096%nat buf']); pose (EJc := [CB 256%nat ej]); change [CB 4096%nat buf'] with NBc in PO; change [CB 256%nat ej] with EJc in PO.
      destruct PO as (FP4 & PO). destruct_exs PO.
      destruct PO as (-> & HR4 & G4 & HC4 & FS4 & FJ4 & FN4 & EBc4 & HPc4 & PKc4 & UC4 & AG4 & Hr).
      assert (FPK : fp_le RNG RNG4) by (intros b j Hb; apply FP4, FP3, FP2; exact Hb).
      destruct Hr as [Hr | ->].
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.ltb_lt r 0) Hr).
        eapply implMG_mono.
        { eapply (fz_unlink FO GIOA fflagA GL FFREE7 SETSHF8 UNLINK); [exact HP | exact HR4 | exact G4 | exact HC4 | exact FS4 | exact FN4 | exact NB2]. }
        intros u sx RNGx msx PO.
        lazymatch type of AG4 with agrees_on _ _ ?mm => eapply (fz_post_back GIOA) with (RNG1 := RNG4) (m1 := mm); [exact FPK| | exact PO] end.
        eapply agrees_on_trans; [exact AGK3| exact AG4].
      + cbn [Z.ltb Z.compare]. destruct (FJ4 ltac:(lia)) as (j1 & j2 & ->).
        eapply implMG_mono.
        { eapply (fz_pcap HO FO sites GIOA TP fflagA GL GH HAL FOL FFREE7 SETSHF8 UNLINK PSTATS PCLOSE FPRINTF_DD FPRINTF_S PNEXT POPEN) with (trC := trC);
            [exact HP | exact HR4 | exact G4 | exact HC4 | exact FN4 | exact NB2 | exact EBc4 | exact HPc4 | exact HP8 | exact PKc4 | exact PK8 | exact UC4 | exact TR]. }
        intros u sx RNGx msx PO.
        lazymatch type of AG4 with agrees_on _ _ ?mm => eapply (fz_post_back GIOA) with (RNG1 := RNG4) (m1 := mm); [exact FPK| | exact PO] end.
        eapply agrees_on_trans; [exact AGK3| exact AG4].
  Qed.
  End Sz6.
  #[using="GL GH HAL EQB FOL FFREE7 SETSHF8 FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O FPRINTF_DD FPRINTF_S POPEN PNEXT PSTATS PCLOSE"] Lemma fz_body : ltac:(let t := eval cbv delta [fz_body__stmt] in fz_body__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra jn ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_body__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzBody.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_tailA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_openA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_btfA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Definition tmplb : list byte := map b8 TEMPLATE.
Lemma tmplb_Z : map bv_unsigned tmplb = TEMPLATE.
Proof. vm_compute. reflexivity. Qed.
Lemma tmplb_nonul : ~ In (Z_to_bv 8 0) tmplb.
Proof. unfold tmplb, TEMPLATE. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
Definition template : list byte := map b8 TEMPLATE ++ [Z_to_bv 8 0].
Lemma template_len : length template = 30%nat.
Proof. reflexivity. Qed.
Section CANSEC0. Context {rc : runConstT}.
#[using="Type"] Lemma rodata_template : forall m, mem_inv asegs m -> bytes_at asegs m STR_TEMPLATE template.
Proof.
  intros m MI. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m STR_TEMPLATE template MI ltac:(vm_compute; reflexivity) ltac:(unfold STR_TEMPLATE; lia) ltac:(unfold STR_TEMPLATE, template, TEMPLATE; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ map app str String.list_ascii_of_string]; lia))).
Qed.
End CANSEC0.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FuzzBody.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOL : fo_leaf_laws FO.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x583f0 0xf8.
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FWRITE : fwrite_stmt_o HO GIOA.
  Hypothesis REMOVE : remove_stmt_o GIOA.
  Hypothesis UNLINK : unlink_stmt_o GIOA.
  Hypothesis CLOSE : close_stmt_o GIOA.
  Hypothesis MKSTEMP : mkstemp_stmt_o GIOA.
  Hypothesis PRINTF_R : printf_d_stmt_o GIOA FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o GIOA FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO GIOA FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO FO sites GIOA TP.
  Hypothesis PNEXT : pcap_next_ex_stmt HO FO sites GIOA TP.
  Hypothesis PSTATS : pcap_stats_stmt GIOA TP.
  Hypothesis PCLOSE : pcap_close_stmt HO FO sites GIOA TP.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PR := (prims HO FO sites).

  (* [comment removed for export] *)
  Definition fuzz_bodyA (data : list Z) : Monad.M PSt unit :=
    '(filename, fd) <- s_mkstemp TEMPLATE ;;
    if (fd <? 0)%Z then fo_ret FO _ FF_FUZZ_ONE_INPUT tt else
    s_close fd ;;;
    r <- bufferToFile MOps PR filename data ;;
    if (r <? 0)%Z then s_unlink filename ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt else
    po <- Pcap.pcap_open_offline MOps PR (S (length data)) filename ;;
    match po with
    | inl errbuf =>
        with_outfile MOps PR (fun out => s_fprintf HO out (pieces_couldnt_open (cstr errbuf))) ;;;
        s_unlink filename ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt
    | inr p =>
        p <- packet_loop MOps PR (S (length data)) (S (length data)) p ;;
        '(sr, p) <- Pcap.pcap_stats MOps p ;;
        (if (sr =? 0)%Z then with_outfile MOps PR (fun out => s_fprintf HO out (pieces_number_of_packets 0)) else mret tt) ;;;
        Pcap.pcap_close MOps PR p ;;;
        s_unlink filename ;;; fo_ret FO _ FF_FUZZ_ONE_INPUT tt
    end.

  #[using="Type"] Lemma fuzz_unfoldA : forall data,
    LLVMFuzzerTestOneInput MOps PR data =
    fo_enter FO _ FF_FUZZ_ONE_INPUT
      (o0 <- (s <- mget ;; mret (ps_outfile s)) ;;
       o <- match o0 with
            | Some f => mret (Some f)
            | None => fo <- s_fopen HO DEVNULL true ;; mupd (set_outfile fo) ;;; mret fo
            end ;;
       match o with None => fo_ret FO _ FF_FUZZ_ONE_INPUT tt | Some _ => fuzz_bodyA data end).
  Proof. intros data. reflexivity. Qed.
  (* [comment removed for export] *)
  Definition fz_body__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (lo SPA Fb D : Z) (m : mem) (fra : list cell) (jn ej : list byte) (hpc pkc : cell)
      (data : list byte) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 30 jn] -> rw_cells asegs m (Fb + 382) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    datA RNG m CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (fuzz_bodyA (map bv_unsigned data)) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e08fc) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) r23
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84924) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra jn ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_body__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL GH HAL EQB FOL FFREE7 SETSHF8 FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O FPRINTF_DD FPRINTF_S POPEN PNEXT PSTATS PCLOSE"] Lemma fz_body__body : ltac2:(SecDiet.SzSec.bodyP 'fz_body__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HP HR G HC FRAS FNT FNZ EBc HPc HP8 PKc PK8 UC TR DAT DLEN.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    destruct HC as (MI & ST & STG & FRA & FRs & (k0 & FK0) & FLG & SA & SB & SC). unfold SHA, SHB, SHC in SA, SB, SC.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    band_ind FBAND bF.
    destruct (rw_cells_forget _ _ _ _ FRA) as [jf FRA']. clear FRA. rewrite FRAS in FRA'.
    pose proof (rodata_template m MI) as TMP.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT & _).
    assert (UFN : unpoisoned m (Fb + 352) (Fb + 352 + 4096)) by (eapply (fz_unp_fname m Fb); [exact SB| Z.div_mod_to_equations; lia| lia| lia]).
    assert (OSRC : mobjA RNG m STR_TEMPLATE 30)
      by (eapply (gia_global_mobjA _ _ _ GL); [exact G| unfold client_globals, STR_TEMPLATE; repeat (first [left; reflexivity | right]) | exact RIMG| exact RISH]).
    assert (ODST : mobjA RNG m (Fb + 352) 30).
    { apply aobjA_mobjA; [| lia].
      assert (CO : cobjA RNG m (FZFL Fb) CL (Fb + 352) 30)
        by (eapply (fz_cobj FO GIOA fflagA GL); [exact G| lia| lia| lia| eapply unpoisoned_sub; [exact UFN| lia| lia]]).
      exact (proj2 CO). }
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    pose proof (munch_refl [(SPA - 4096, SPA); (Fb, Fb + 8192)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold fuzz_bodyA.
    ienterG. do 6 zstep.
    (* [comment removed for export] *)
    clear ESPA. remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply asan_memcpy_specZ with (lo := lo) (Dst := (Fb + 352)%Z) (Src := STR_TEMPLATE) (n := 30%Z) (src := template) (junk := jn);
        [ reflexivity | reflexivity | reflexivity | assumption | rewrite Hspa; exact ST | rewrite Hspa; lia | lia | exact RT | exact TMP | reflexivity | lia
        | exact FNT | unfold STR_TEMPLATE; lia | exact OSRC | exact ODST | unfold STR_TEMPLATE; lia | lia | exact RIMG
        | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] ]. }
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (E & MU1 & WM1 & MI1 & ST1 & FNT1 & TMP1).
    subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    replace (ret_pc (Z_to_bv 64 543036)) with (Z_to_bv 64 543036) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch type of MU1 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU1 WM1 end.
    change (Z.to_nat 30) with 30%nat in FNT1.
    lazymatch type of MU with munch _ _ ?m1 =>
      assert (NBUF : rw_cells asegs m1 (Fb + 352) [CB 4096 (template ++ repeat (Z_to_bv 8 0) 4066)]);
      [ pose proof (rw_cells_merge asegs m1 (Fb + 352) [] [CB 30 template; CB 4066 (repeat (Z_to_bv 8 0) 4066)] []) as X |] end.
    { cbn [app cells_size csize cells_bytes cbytes Nat.add] in X. rewrite app_nil_r in X. apply X.
      apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact FNT1|]. cbn [cells_size csize Nat.add].
      replace (Fb + 352 + Z.of_nat 30)%Z with (Fb + 382)%Z by lia. exact FNZ. }
    clear FNT1 FNZ TMP1 OSRC ODST RT.
    assert (FW : Forall (own_ivA (FZFL Fb) ([] : list cblk) (bv_unsigned sp)) [(SPA - 4096, SPA); (Fb, Fb + 8192)]%Z) by own_ivs.
    lazymatch type of MU with munch _ _ ?mm =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FW (Forall_nil _) G' MU WM ltac:(lia)) as [G1 AG1] end.
    rewrite app_nil_r in G1. cbn [app] in G1.
    lazymatch type of MU with munch _ _ ?mm =>
      assert (AG1' : agrees_on (client_keeps [] CL (bv_unsigned sp)) m mm) by (eapply agrees_on_weaken; [exact AG1| intros a K0; split; [exact K0| exact I]]);
      assert (UC1 : ucallerA depth_fuzz_one L mm sp s0 ra trC)
        by (eapply ucaller_keep; [exact UC| exact TOP47|]; intros a Ha; apply (AG1' a); [lia| left; lia]);
      assert (HC1 : hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [CB 56 jf] mm)
        by (split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exists k0; assumption|];
            split; [assumption|]; split; [exact SA|]; split; [exact SB| exact SC])
    end.
    pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT AG1' G1) as DAT1.
    assert (ONAME : cobjA RNG x13 (FZFL Fb) CL (Fb + 352) (Z.of_nat 4096))
      by (eapply (fz_cobj FO GIOA fflagA GL); [exact G1| lia| lia| lia| exact UFN]).
    clear G' FW G UC DAT AG1 MI MU1 WM1.
    do 2 zstep.
    rewrite <- tmplb_Z.
    apply evtF_done. subst POSTQ. eapply implMG_bind.
    { eapply implMG_leaf.
      eapply MKSTEMP with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := (Fb + 352)%Z) (n := 4096%nat) (tmpl := tmplb)
                          (buf := template ++ repeat (Z_to_bv 8 0) 4066);
        [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G1| assumption| assumption| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
        | reflexivity | exact NBUF | vm_compute; reflexivity | exact tmplb_nonul | reflexivity | cbn; lia | lia | exact ONAME ]. }
    intros [fn fd] s2' RNG2 ms2 [PO LF]. cbv beta in PO. cbn [fst snd] in PO.
    (* [comment removed for export] *)
    pose (N4096 := 4096%nat); change 4096%nat with N4096 in PO.
    destruct PO as (FP2 & a0v & m2 & buf' & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & Hfd & NBUF2 & NB2 & RNGf & LENf & SHAPE).
    repeat match goal with H : context [N4096] |- _ => unfold N4096 in H end. clear N4096.
    rewrite ESPA in *. post_regs E.
    rewrite tmplb_Z in LF. apply mkstemp_leaf in LF. subst fn.
    replace (length TMPNAME + 1)%nat with 25%nat in NB2 by reflexivity. change (map b8 TMPNAME) with tmpname in NB2.
    change (Z.of_nat 4096) with 4096%Z in AG2.
    pose proof (hcoreA_keep FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ (fun a => ~ (Fb + 352 <= a < Fb + 352 + 4096))%Z _ _
                  HC1 G1 HP eq_refl eq_refl AG2 ltac:(intros a Ha; lia) MI2 ST2) as HC2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 352 <= a < Fb + 352 + 4096))%Z _ _ _ _ EBc AG2 ltac:(lia)
                  ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia)) as EBc2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 352 <= a < Fb + 352 + 4096))%Z _ _ _ _ HPc AG2 ltac:(lia)
                  ltac:(cbn [cells_size]; rewrite HP8; lia) ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite HP8 in Ha; lia)) as HPc2.
    pose proof (fz_local_keep CL SPA Fb (fun a => ~ (Fb + 352 <= a < Fb + 352 + 4096))%Z _ _ _ _ PKc AG2 ltac:(lia)
                  ltac:(cbn [cells_size]; rewrite PK8; lia) ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite PK8 in Ha; lia)) as PKc2.
    pose proof (fz_uc_keep _ _ CL SPA Fb (fun a => ~ (Fb + 352 <= a < Fb + 352 + 4096))%Z _ _ _ _ _ _ UC1 TOP47 AG2 ltac:(lia) ltac:(intros a Ha; lia)) as UC2.
    assert (AGC2 : agrees_on (client_keeps [] CL (bv_unsigned sp)) x13 m2).
    { eapply agrees_on_weaken; [exact AG2|]. cbv beta. intros a [Ha|[Ha|[Ha|Ha]]].
      - split; [left; lia| lia].
      - split; [right; left; exact Ha|].
        assert (NF : ~ in_frames (FZFL Fb) a) by (intros K0; apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G1 K0); apply in_block_app; left; exact Ha).
        assert (NR : ~ (Fb <= a < Fb + 8192)%Z) by (intros K0; apply NF; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia). lia.
      - inversion Ha.
      - inversion Ha. }
    pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT1 AGC2 G2) as DAT2.
    assert (AGK2 : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m2) by (eapply agrees_on_trans; [exact AG1'| exact AGC2]).
    hr_next HR FP2 HR2.
    clear STG FRs FK0 FLG SA SB SC EBc HPc PKc FRA' UFN MU WM MI1 ST1 NBUF ONAME.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    cbv beta iota.
    ienterG. zstep.
    destruct Hfd as [Efd|Hpos].
    - (* [comment removed for export] *)
      rewrite Efd. change (bv_lts (Z_to_bv 64 (-1)) z64) with true. cbn [Z.ltb Z.compare]. cbv iota.
      apply evtF_done. subst POSTQ.
      eapply implMG_mono.
      { eapply (fz_exitK FO GIOA fflagA GL FFREE7 SETSHF8); [exact HP| exact HR2| exact G2| exact HC2| reflexivity]. }
      intros u sx RNGx msx PO. eapply (fz_post_back GIOA) with (RNG1 := RNG2) (m1 := m2); [exact FP2| exact AGK2| exact PO].
    - (* [comment removed for export] *)
      rewrite bv_lts_zero_r, unsigned_lit by lia. replace (2 ^ 63 <=? fd)%Z with false by (symmetry; apply Z.leb_gt; lia).
      replace (fd <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      zstep. apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply CLOSE with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (fd := fd);
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR2| exact G2| exact ST2| exact MI2| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | reflexivity | lia ]. }
      intros rclose s3' RNG3 ms3 PO. cbv beta in PO. destruct PO as (FP3 & a0v & m3 & E & OF3 & MI3 & ST3 & AG3 & G3). rewrite ESPA in *. post_regs E.
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC2 G2 HP eq_refl eq_refl AG3 MI3 ST3) as HC3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ NBUF2 AG3 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as FN3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc2 AG3 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as EBc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc3.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc2 AG3 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc3.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC2 TOP47 AG3 ltac:(lia)) as UC3.
      pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT2 AG3 G3) as DAT3.
      hr_next HR2 FP3 HR3.
      assert (AGK3 : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m3) by (eapply agrees_on_trans; [exact AGK2| eapply fz_ag_final; [exact AG3| lia]]).
      clear MI2 MU WM NBUF2 EBc2 HPc2 PKc2.
      eapply implMG_bind.
      { eapply (fz_btf HO FO sites GIOA TP fflagA GL GH HAL EQB FOPEN FCLOSE FWRITE REMOVE PRINTF_R PRINTF_O) with (trC := trC);
          [exact HP| exact HR3| exact G3| exact HC3| reflexivity| exact FN3| exact NB2| exact EBc3| exact HPc3| exact HP8| exact PKc3| exact PK8
          | exact UC3| exact TR| exact DAT3| exact DLEN]. }
      intros r s4' RNG4 ms4 PO.
      (* [comment removed for export] *)
      unfold btf_postA in PO. pose (NBc := [CB 4096%nat buf']); pose (EJc := [CB 256%nat ej]); change [CB 4096%nat buf'] with NBc in PO; change [CB 256%nat ej] with EJc in PO.
      destruct PO as (FP4 & PO). destruct_exs PO.
      destruct PO as (-> & HR4 & G4 & HC4 & FS4 & FJ4 & FN4 & EBc4 & HPc4 & PKc4 & UC4 & AG4 & Hr).
      assert (FPK : fp_le RNG RNG4) by (intros b j Hb; apply FP4, FP3, FP2; exact Hb).
      destruct Hr as [Hr | ->].
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.ltb_lt r 0) Hr).
        eapply implMG_mono.
        { eapply (fz_unlink FO GIOA fflagA GL FFREE7 SETSHF8 UNLINK); [exact HP | exact HR4 | exact G4 | exact HC4 | exact FS4 | exact FN4 | exact NB2]. }
        intros u sx RNGx msx PO.
        lazymatch type of AG4 with agrees_on _ _ ?mm => eapply (fz_post_back GIOA) with (RNG1 := RNG4) (m1 := mm); [exact FPK| | exact PO] end.
        eapply agrees_on_trans; [exact AGK3| exact AG4].
      + cbn [Z.ltb Z.compare]. destruct (FJ4 ltac:(lia)) as (j1 & j2 & ->).
        eapply implMG_mono.
        { eapply (fz_pcap HO FO sites GIOA TP fflagA GL GH HAL FOL FFREE7 SETSHF8 UNLINK PSTATS PCLOSE FPRINTF_DD FPRINTF_S PNEXT POPEN) with (trC := trC);
            [exact HP | exact HR4 | exact G4 | exact HC4 | exact FN4 | exact NB2 | exact EBc4 | exact HPc4 | exact HP8 | exact PKc4 | exact PK8 | exact UC4 | exact TR]. }
        intros u sx RNGx msx PO.
        lazymatch type of AG4 with agrees_on _ _ ?mm => eapply (fz_post_back GIOA) with (RNG1 := RNG4) (m1 := mm); [exact FPK| | exact PO] end.
        eapply agrees_on_trans; [exact AGK3| exact AG4].
  Qed.
  End Sz6.
  #[using="GL GH HAL EQB FOL FFREE7 SETSHF8 FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O FPRINTF_DD FPRINTF_S POPEN PNEXT PSTATS PCLOSE"] Lemma fz_body : ltac:(let t := eval cbv delta [fz_body__stmt] in fz_body__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra jn ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_body__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzBody.
End CANSEC1.
End TwB.
End F_fuzz_bodyA.

(* [comment removed for export] *)
Module F_fuzz_outA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_tailA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_btfA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_bodyA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Definition devnull : list byte := map b8 DEVNULL.
Lemma devnull_Z : map bv_unsigned devnull = DEVNULL.
Proof. vm_compute. reflexivity. Qed.
Lemma devnull_nonul : ~ In (Z_to_bv 8 0) devnull.
Proof. unfold devnull, DEVNULL. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
Lemma devnull_len : length devnull = 9%nat.
Proof. reflexivity. Qed.
Lemma devnull_open_w : open_name_ok true devnull.
Proof. right. reflexivity. Qed.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FuzzOut.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis BODY : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (lo SPA Fb D : Z) (m : mem) (fra : list cell) (jn ej : list byte) (hpc pkc : cell)
      (data : list byte) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 30 jn] -> rw_cells asegs m (Fb + 382) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    datA RNG m CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (fuzz_bodyA HO FO sites (map bv_unsigned data)) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e0894) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) r23
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x848bc) fc None m (seg_rom asegs)).
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x58388 0xf8.
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PR := (prims HO FO sites).

  #[using="Type"] Lemma implMG_updret_l : forall {A B} RNG g (x : A) (k : A -> Monad.M PSt B) (s : PSt) Q ms,
    implMG RNG (k x) (g s) Q ms -> implMG RNG (mbind (mbind (mupd g) (fun _ => mret x)) k) s Q ms.
  Proof. intros. exact H0. Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma in_block_img : forall L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_block (CL ++ FB) a -> (AIMG_HI <= a)%Z.
  Proof.
    intros L RNG s CL FB FL m a G Hin. apply in_block_In in Hin as (b & Hb & Hr).
    destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G Hb) as ((BAND & _) & _). pose proof (ablk_lin _ _ BAND) as (IMG & _). lia.
  Qed.
  (* [comment removed for export] *)
  Definition fz_out__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (lo SPA Fb D : Z) (m : mem) (fra : list cell) (jn ej : list byte) (hpc pkc : cell)
      (data : list byte) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 30 jn] -> rw_cells asegs m (Fb + 382) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    datA RNG m CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (o <- match ps_outfile s with
                     | Some f => mret (Some f)
                     | None => fo <- s_fopen HO DEVNULL true ;; mupd (set_outfile fo) ;;; mret fo
                     end ;;
                match o with None => fo_ret FO _ FF_FUZZ_ONE_INPUT tt | Some _ => fuzz_bodyA HO FO sites (map bv_unsigned data) end) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) r23
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84894) fc None m (seg_rom asegs)).
  Section Sz7.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra jn ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL GH BODY FFREE7 SETSHF8 FOPEN"] Lemma fz_out__body : ltac2:(SecDiet.SzSec.bodyP 'fz_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HP HR G HC FRAS FNT FNZ EBc HPc HP8 PKc PK8 UC TR DAT DLEN.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _).
    pose proof TR as (TRF & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    band_ind FBAND bF.
    pose proof (gh_outfile _ GH _ _ _ _ _ _ _ G) as OC. unfold OUTFILE_ADDR in OC.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct (ps_outfile s) as [q|] eqn:EO.
    - (* [comment removed for export] *)
      destruct OC as (Ao & AIN & OC).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact AIN)) as ((_ & _ & ATOPo & _) & A1 & _).
      cbn [cb_addr cb_size fst snd] in A1, ATOPo. unfold FILE_BLOCK in ATOPo.
      apply implMG_retb.
      ienterG. zstep. zstep. zstep. if_true_by (nez_true Ao ltac:(lia)). apply evtF_done. subst POSTQ.
      eapply BODY; [exact HP| exact HR| exact G| exact HC| exact FRAS| exact FNT| exact FNZ| exact EBc| exact HPc| exact HP8| exact PKc| exact PK8| exact UC| exact TR| exact DAT| exact DLEN].
    - (* [comment removed for export] *)
      apply implMG_bind_assoc.
      ienterG. zstep. zstep. zstep. if_false. do 5 zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (RB1 : bytes_at asegs mm STR_DEVNULL (devnull ++ [Z_to_bv 8 0]))
          by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm STR_DEVNULL (devnull ++ [Z_to_bv 8 0]) ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(unfold STR_DEVNULL; lia) ltac:(unfold STR_DEVNULL; cbn; lia))));
        assert (RB2 : bytes_at asegs mm STR_W ([Z_to_bv 8 119] ++ [Z_to_bv 8 0]))
          by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm STR_W [Z_to_bv 8 119; Z_to_bv 8 0] ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(unfold STR_W; lia) ltac:(unfold STR_W; cbn; lia)))) end.
      rewrite <- devnull_Z.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FOPEN with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := STR_DEVNULL) (MODE := STR_W) (name := devnull)
                          (md := [Z_to_bv 8 119]) (wr := true) (trC := bv_unsigned ra :: trC);
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | eapply (fz_ucaller fflagA); [exact UC| exact HP| exact HC| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_fuzz_one; lia]
          | rewrite unsigned_lit by lia; exact TRF
          | reflexivity | reflexivity | exact RB1 | exact devnull_nonul | rewrite devnull_len; lia | exact devnull_open_w
          | eapply (gia_global_robjA _ _ _ GL); [exact G | unfold client_globals, STR_DEVNULL; repeat (first [left; reflexivity | right]) | unfold STR_DEVNULL; cbn; lia | exact RIMG | exact RISH]
          | exact RB2 | left; split; reflexivity
          | eapply (gia_global_robjA _ _ _ GL); [exact G | unfold client_globals, STR_W; repeat (first [left; reflexivity | right]) | unfold STR_W; cbn; lia | exact RIMG | exact RISH] ]. }
      intros fo s2' RNG2 ms2 PO. cbv beta in PO. destruct PO as (FP2 & a0v & m2 & E & OF2 & MI2 & ST2 & AG2 & PO). rewrite ESPA in *. post_regs E.
      assert (G2x : exists FB2, GIOA L RNG2 s2' CL FB2 (FZFL Fb) m2
                    /\ match fo with None => a0v = Z_to_bv 64 0 | Some f => exists Af, a0v = Z_to_bv 64 Af /\ In (f, Af, FILE_BLOCK) FB2 end).
      { destruct fo as [f|].
        - destruct PO as (Af & -> & G2). exists ((f, Af, FILE_BLOCK) :: FB). split; [exact G2|]. exists Af. split; [reflexivity| left; reflexivity].
        - destruct PO as (-> & G2 & _). exists FB. split; [exact G2| reflexivity]. }
      clear PO. destruct G2x as (FB2 & G2 & Hfo).
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC G HP FRAS eq_refl AG2 MI2 ST2) as HC2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FNT AG2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as FNT2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FNZ AG2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as FNZ2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc AG2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as EBc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc2.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC TOP47 AG2 ltac:(lia)) as UC2.
      pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT AG2 G2) as DAT2.
      pose proof (gh_outfile _ GH _ _ _ _ _ _ _ G2) as OC2. rewrite OF2, EO in OC2. unfold OUTFILE_ADDR in OC2.
      hr_next HR FP2 HR2.
      clear MI ST MU WM RB1 RB2 FNT FNZ EBc HPc PKc UC DAT OC.
      destruct HC2 as (MI2' & ST2' & STG2 & FRA2 & FRs2 & (k0 & FK02) & FLG2 & SA2 & SB2 & SC2). unfold SHA, SHB, SHC in SA2, SB2, SC2.
      destruct (rw_cells_forget _ _ _ _ FRA2) as [jf FRA2']. clear FRA2. rewrite FRAS in FRA2'.
      pose proof (munch_refl [(0x5e0c80, 0x5e0c88)]%Z m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      apply implMG_updret_l.
      ienterG. zstep.
      lazymatch type of MU with munch _ _ ?m3 =>
        assert (G3 : GIOA L RNG2 (set_outfile fo s2') CL FB2 (FZFL Fb) m3)
          by (eapply (gh_set_outfile _ GH _ _ _ _ _ _ _ _ fo G2); [rewrite OF2; exact EO| | exact MU| exact WM];
              destruct fo as [f|]; [destruct Hfo as (Af & -> & AIN); exists Af; split; [exact AIN| exact OC2] | rewrite Hfo in OC2; exact OC2]);
        assert (AGs : agrees_on (client_keeps [] CL (bv_unsigned sp)) m2 m3)
          by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [Ha|[Ha|[Ha|Ha]]]; cbn [outside fst snd];
              [ split; [lia| exact I]
              | pose proof (in_block_img _ _ _ _ _ _ _ a G2 ltac:(apply in_block_app; left; exact Ha)) as K0; unfold AIMG_HI in K0; split; [lia| exact I]
              | inversion Ha | inversion Ha ]);
        assert (UC3 : ucallerA depth_fuzz_one L m3 sp s0 ra trC)
          by (eapply ucaller_keep; [exact UC2| exact TOP47|]; intros a Ha; apply (AGs a); [lia| left; lia]);
        assert (HC3 : hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [CB 56 jf] m3)
          by (split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exists k0; assumption|];
              split; [assumption|]; split; [exact SA2|]; split; [exact SB2| exact SC2])
      end.
      pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT2 AGs G3) as DAT3.
      assert (AGK : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m0) by (eapply agrees_on_trans; [eapply fz_ag_final; [exact AG2| lia]| exact AGs]).
      clear G2 UC2 DAT2 MI2.
      zstep.
      destruct fo as [f|].
      + destruct Hfo as (Af & -> & AIN).
        pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 ltac:(apply in_or_app; right; exact AIN)) as ((_ & _ & ATOPo & _) & A1 & _).
        cbn [cb_addr cb_size fst snd] in A1, ATOPo. unfold FILE_BLOCK in ATOPo.
        if_false_by (eqz_false Af ltac:(lia)). apply evtF_done. subst POSTQ.
        eapply implMG_mono; [| intros r1 sx RNGx msx PO; eapply (fz_post_back GIOA) with (RNG1 := RNG2) (m1 := m0); [exact FP2| exact AGK| exact PO]].
        eapply BODY; [exact HP| exact HR2| exact G3| exact HC3| reflexivity| exact FNT2| exact FNZ2| exact EBc2| exact HPc2| exact HP8| exact PKc2| exact PK8| exact UC3| exact TR| exact DAT3| exact DLEN].
      + rewrite Hfo. if_true. apply evtF_done. subst POSTQ.
        eapply implMG_mono; [| intros r1 sx RNGx msx PO; eapply (fz_post_back GIOA) with (RNG1 := RNG2) (m1 := m0); [exact FP2| exact AGK| exact PO]].
        eapply (fz_exitK FO GIOA fflagA GL FFREE7 SETSHF8); [exact HP| exact HR2| exact G3| exact HC3| reflexivity].
  Qed.
  End Sz7.
  #[using="GL GH BODY FFREE7 SETSHF8 FOPEN"] Lemma fz_out : ltac:(let t := eval cbv delta [fz_out__stmt] in fz_out__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra jn ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_out__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzOut.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_tailA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_btfA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_bodyA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac post_regs E := unfold hpost_regs in E; destruct_exs E; lazymatch type of E with ?x = _ => subst x end;
  try (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
         replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) in * by (symmetry; apply ret_pc_even; [lia|reflexivity]) end).

Definition devnull : list byte := map b8 DEVNULL.
Lemma devnull_Z : map bv_unsigned devnull = DEVNULL.
Proof. vm_compute. reflexivity. Qed.
Lemma devnull_nonul : ~ In (Z_to_bv 8 0) devnull.
Proof. unfold devnull, DEVNULL. cbn. intros Hin. repeat (destruct Hin as [E|Hin]; [discriminate E|]). exact Hin. Qed.
Lemma devnull_len : length devnull = 9%nat.
Proof. reflexivity. Qed.
Lemma devnull_open_w : open_name_ok true devnull.
Proof. right. reflexivity. Qed.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FuzzOut.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis BODY : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (lo SPA Fb D : Z) (m : mem) (fra : list cell) (jn ej : list byte) (hpc pkc : cell)
      (data : list byte) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 30 jn] -> rw_cells asegs m (Fb + 382) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    datA RNG m CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (fuzz_bodyA HO FO sites (map bv_unsigned data)) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0x5e08fc) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) r23
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x84924) fc None m (seg_rom asegs)).
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x583f0 0xf8.
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PR := (prims HO FO sites).

  #[using="Type"] Lemma implMG_updret_l : forall {A B} RNG g (x : A) (k : A -> Monad.M PSt B) (s : PSt) Q ms,
    implMG RNG (k x) (g s) Q ms -> implMG RNG (mbind (mbind (mupd g) (fun _ => mret x)) k) s Q ms.
  Proof. intros. exact H0. Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma in_block_img : forall L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_block (CL ++ FB) a -> (AIMG_HI <= a)%Z.
  Proof.
    intros L RNG s CL FB FL m a G Hin. apply in_block_In in Hin as (b & Hb & Hr).
    destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G Hb) as ((BAND & _) & _). pose proof (ablk_lin _ _ BAND) as (IMG & _). lia.
  Qed.
  (* [comment removed for export] *)
  Definition fz_out__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (lo SPA Fb D : Z) (m : mem) (fra : list cell) (jn ej : list byte) (hpc pkc : cell)
      (data : list byte) (trC : list Z)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 t3 t4 t5 t6 : word),
    hpureA L sp tp lo SPA -> hrngA L RNG lo -> GIOA L RNG s CL FB (FZFL Fb) m ->
    hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m ->
    cells_size fra = 56%nat ->
    rw_cells asegs m (Fb + 352) [CB 30 jn] -> rw_cells asegs m (Fb + 382) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
    rw_cells asegs m (Fb + 32) [CB 256 ej] ->
    rw_cells asegs m (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
    ucallerA depth_fuzz_one L m sp s0 ra trC -> traces_fuzz_one TP L (bv_unsigned ra) trC ->
    datA RNG m CL D data -> (Z.of_nat (length data) < 2^26)%Z ->
    implMG RNG (o <- match ps_outfile s with
                     | Some f => mret (Some f)
                     | None => fo <- s_fopen HO DEVNULL true ;; mupd (set_outfile fo) ;;; mret fo
                     end ;;
                match o with None => fo_ret FO _ FF_FUZZ_ONE_INPUT tt | Some _ => fuzz_bodyA HO FO sites (map bv_unsigned data) end) s
      (fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) r23
               (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
          F (Z_to_bv 64 0x848fc) fc None m (seg_rom asegs)).
  Section Sz7.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra jn ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fz_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL GH BODY FFREE7 SETSHF8 FOPEN"] Lemma fz_out__body : ltac2:(SecDiet.SzSec.bodyP 'fz_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros HP HR G HC FRAS FNT FNZ EBc HPc HP8 PKc PK8 UC TR DAT DLEN.
    pose proof HP as (SPAB & SPA32 & LO & LOS & SPT & TOP47 & TPE & ALN). unfold FUZZ_STACK, PCAP_L4_STACK in LOS. hr_open HR.
    pose proof HC as (MI & ST & _).
    pose proof TR as (TRF & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (ESPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
    pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G) as (FBAND & FTOP & F64 & Fb0 & T47 & FRNG & FSRNG & SH1 & SH2).
    band_ind FBAND bF.
    pose proof (gh_outfile _ GH _ _ _ _ _ _ _ G) as OC. unfold OUTFILE_ADDR in OC.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct (ps_outfile s) as [q|] eqn:EO.
    - (* [comment removed for export] *)
      destruct OC as (Ao & AIN & OC).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact AIN)) as ((_ & _ & ATOPo & _) & A1 & _).
      cbn [cb_addr cb_size fst snd] in A1, ATOPo. unfold FILE_BLOCK in ATOPo.
      apply implMG_retb.
      ienterG. zstep. zstep. zstep. if_true_by (nez_true Ao ltac:(lia)). apply evtF_done. subst POSTQ.
      eapply BODY; [exact HP| exact HR| exact G| exact HC| exact FRAS| exact FNT| exact FNZ| exact EBc| exact HPc| exact HP8| exact PKc| exact PK8| exact UC| exact TR| exact DAT| exact DLEN].
    - (* [comment removed for export] *)
      apply implMG_bind_assoc.
      ienterG. zstep. zstep. zstep. if_false. do 5 zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (RB1 : bytes_at asegs mm STR_DEVNULL (devnull ++ [Z_to_bv 8 0]))
          by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm STR_DEVNULL (devnull ++ [Z_to_bv 8 0]) ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(unfold STR_DEVNULL; lia) ltac:(unfold STR_DEVNULL; cbn; lia))));
        assert (RB2 : bytes_at asegs mm STR_W ([Z_to_bv 8 119] ++ [Z_to_bv 8 0]))
          by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm STR_W [Z_to_bv 8 119; Z_to_bv 8 0] ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(unfold STR_W; lia) ltac:(unfold STR_W; cbn; lia)))) end.
      rewrite <- devnull_Z.
      apply evtF_done. subst POSTQ. eapply implMG_bind.
      { eapply FOPEN with (L := L) (s := s) (CL := CL) (FB := FB) (FL := FZFL Fb) (lo := lo) (NAME := STR_DEVNULL) (MODE := STR_W) (name := devnull)
                          (md := [Z_to_bv 8 119]) (wr := true) (trC := bv_unsigned ra :: trC);
          [ eapply (hpureA_spo GIOA); [exact HP| exact HR| exact G| exact ST| exact MI| unfold STDIO_STACK, FUZZ_STACK, PCAP_L4_STACK; lia]
          | eapply (fz_ucaller fflagA); [exact UC| exact HP| exact HC| reflexivity| reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_fuzz_one; lia]
          | rewrite unsigned_lit by lia; exact TRF
          | reflexivity | reflexivity | exact RB1 | exact devnull_nonul | rewrite devnull_len; lia | exact devnull_open_w
          | eapply (gia_global_robjA _ _ _ GL); [exact G | unfold client_globals, STR_DEVNULL; repeat (first [left; reflexivity | right]) | unfold STR_DEVNULL; cbn; lia | exact RIMG | exact RISH]
          | exact RB2 | left; split; reflexivity
          | eapply (gia_global_robjA _ _ _ GL); [exact G | unfold client_globals, STR_W; repeat (first [left; reflexivity | right]) | unfold STR_W; cbn; lia | exact RIMG | exact RISH] ]. }
      intros fo s2' RNG2 ms2 PO. cbv beta in PO. destruct PO as (FP2 & a0v & m2 & E & OF2 & MI2 & ST2 & AG2 & PO). rewrite ESPA in *. post_regs E.
      assert (G2x : exists FB2, GIOA L RNG2 s2' CL FB2 (FZFL Fb) m2
                    /\ match fo with None => a0v = Z_to_bv 64 0 | Some f => exists Af, a0v = Z_to_bv 64 Af /\ In (f, Af, FILE_BLOCK) FB2 end).
      { destruct fo as [f|].
        - destruct PO as (Af & -> & G2). exists ((f, Af, FILE_BLOCK) :: FB). split; [exact G2|]. exists Af. split; [reflexivity| left; reflexivity].
        - destruct PO as (-> & G2 & _). exists FB. split; [exact G2| reflexivity]. }
      clear PO. destruct G2x as (FB2 & G2 & Hfo).
      pose proof (hcoreA_keep0 FO GIOA fflagA GL _ _ _ _ CL _ _ _ _ _ _ _ _ _ _ HC G HP FRAS eq_refl AG2 MI2 ST2) as HC2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FNT AG2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as FNT2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ FNZ AG2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as FNZ2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ EBc AG2 ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as EBc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ HPc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite HP8; lia)) as HPc2.
      pose proof (fz_local_keep0 CL SPA Fb _ _ _ _ PKc AG2 ltac:(lia) ltac:(cbn [cells_size]; rewrite PK8; lia)) as PKc2.
      pose proof (fz_uc_keep0 _ _ CL SPA Fb _ _ _ _ _ _ UC TOP47 AG2 ltac:(lia)) as UC2.
      pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT AG2 G2) as DAT2.
      pose proof (gh_outfile _ GH _ _ _ _ _ _ _ G2) as OC2. rewrite OF2, EO in OC2. unfold OUTFILE_ADDR in OC2.
      hr_next HR FP2 HR2.
      clear MI ST MU WM RB1 RB2 FNT FNZ EBc HPc PKc UC DAT OC.
      destruct HC2 as (MI2' & ST2' & STG2 & FRA2 & FRs2 & (k0 & FK02) & FLG2 & SA2 & SB2 & SC2). unfold SHA, SHB, SHC in SA2, SB2, SC2.
      destruct (rw_cells_forget _ _ _ _ FRA2) as [jf FRA2']. clear FRA2. rewrite FRAS in FRA2'.
      pose proof (munch_refl [(0x5e1080, 0x5e1088)]%Z m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      apply implMG_updret_l.
      ienterG. zstep.
      lazymatch type of MU with munch _ _ ?m3 =>
        assert (G3 : GIOA L RNG2 (set_outfile fo s2') CL FB2 (FZFL Fb) m3)
          by (eapply (gh_set_outfile _ GH _ _ _ _ _ _ _ _ fo G2); [rewrite OF2; exact EO| | exact MU| exact WM];
              destruct fo as [f|]; [destruct Hfo as (Af & -> & AIN); exists Af; split; [exact AIN| exact OC2] | rewrite Hfo in OC2; exact OC2]);
        assert (AGs : agrees_on (client_keeps [] CL (bv_unsigned sp)) m2 m3)
          by (eapply agrees_on_of_munch; [exact MU | exact WM |]; intros a _ [Ha|[Ha|[Ha|Ha]]]; cbn [outside fst snd];
              [ split; [lia| exact I]
              | pose proof (in_block_img _ _ _ _ _ _ _ a G2 ltac:(apply in_block_app; left; exact Ha)) as K0; unfold AIMG_HI in K0; split; [lia| exact I]
              | inversion Ha | inversion Ha ]);
        assert (UC3 : ucallerA depth_fuzz_one L m3 sp s0 ra trC)
          by (eapply ucaller_keep; [exact UC2| exact TOP47|]; intros a Ha; apply (AGs a); [lia| left; lia]);
        assert (HC3 : hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [CB 56 jf] m3)
          by (split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exists k0; assumption|];
              split; [assumption|]; split; [exact SA2|]; split; [exact SB2| exact SC2])
      end.
      pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT2 AGs G3) as DAT3.
      assert (AGK : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m0) by (eapply agrees_on_trans; [eapply fz_ag_final; [exact AG2| lia]| exact AGs]).
      clear G2 UC2 DAT2 MI2.
      zstep.
      destruct fo as [f|].
      + destruct Hfo as (Af & -> & AIN).
        pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 ltac:(apply in_or_app; right; exact AIN)) as ((_ & _ & ATOPo & _) & A1 & _).
        cbn [cb_addr cb_size fst snd] in A1, ATOPo. unfold FILE_BLOCK in ATOPo.
        if_false_by (eqz_false Af ltac:(lia)). apply evtF_done. subst POSTQ.
        eapply implMG_mono; [| intros r1 sx RNGx msx PO; eapply (fz_post_back GIOA) with (RNG1 := RNG2) (m1 := m0); [exact FP2| exact AGK| exact PO]].
        eapply BODY; [exact HP| exact HR2| exact G3| exact HC3| reflexivity| exact FNT2| exact FNZ2| exact EBc2| exact HPc2| exact HP8| exact PKc2| exact PK8| exact UC3| exact TR| exact DAT3| exact DLEN].
      + rewrite Hfo. if_true. apply evtF_done. subst POSTQ.
        eapply implMG_mono; [| intros r1 sx RNGx msx PO; eapply (fz_post_back GIOA) with (RNG1 := RNG2) (m1 := m0); [exact FP2| exact AGK| exact PO]].
        eapply (fz_exitK FO GIOA fflagA GL FFREE7 SETSHF8); [exact HP| exact HR2| exact G3| exact HC3| reflexivity].
  Qed.
  End Sz7.
  #[using="GL GH BODY FFREE7 SETSHF8 FOPEN"] Lemma fz_out : ltac:(let t := eval cbv delta [fz_out__stmt] in fz_out__stmt in exact t).
  Proof. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB lo SPA Fb D m fra jn ej hpc pkc data trC ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fz_out__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzOut.
End CANSEC1.
End TwB.
End F_fuzz_outA.

(* [comment removed for export] *)
Module F_fuzz_topA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit2__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.LibcKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_btfA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_segA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac dm_plia := first [ atop_facts; once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); Z.div_mod_to_equations; lia_tiers
                            | Z.div_mod_to_equations; lia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

(* [comment removed for export] *)
Ltac norm_addr H P :=
  lazymatch type of H with
  | rw_cells _ _ (?b + Z.of_nat ?n)%Z _ =>
      lazymatch b with
      | (P + ?k0)%Z => let k := eval vm_compute in (k0 + Z.of_nat n)%Z in replace (b + Z.of_nat n)%Z with (P + k)%Z in H by lia
      | P => let k := eval vm_compute in (Z.of_nat n) in replace (P + Z.of_nat n)%Z with (P + k)%Z in H by lia
      end
  end.
Ltac cut_cells H k H1 P :=
  let H2 := fresh "TMP" in
  destruct (rw_cells_cut _ _ _ k H) as [H1 H2]; clear H; cbn [firstn skipn cells_size csize Nat.add] in H1, H2;
  norm_addr H2 P; rename H2 into H.

Lemma land_m32T : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

(* [comment removed for export] *)
Ltac peel1 H H1 P k' :=
  lazymatch type of H with
  | rw_cells ?sg ?mm ?A (?c :: ?rest) =>
      let H2 := fresh "TMP" in
      change (c :: rest) with ([c] ++ rest) in H;
      apply (proj1 (rw_cells_app sg mm A [c] rest)) in H as [H1 H2];
      replace (A + Z.of_nat (cells_size [c]))%Z with (P + k')%Z in H2 by (cbn [cells_size csize]; lia);
      rename H2 into H
  end.

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition fz_frame_cut__stmt : Prop := forall m Fb (j0 j1 j2 fl : word) (fjunk : list byte),
  rw_cells asegs m Fb [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (8192 - 32)) fjunk; C8 fl] ->
  exists ej jn jz pk hp,
    rw_cells asegs m Fb [C8 j0; C8 j1; C8 j2] /\ rw_cells asegs m (Fb + 32) [CB 256 ej]
    /\ rw_cells asegs m (Fb + 352) [CB 30 jn] /\ rw_cells asegs m (Fb + 382) [CB 4066 jz]
    /\ rw_cells asegs m (Fb + 4576) [CB 8 pk] /\ rw_cells asegs m (Fb + 4608) [CB 8 hp]
    /\ rw_cells asegs m (Fb + 8184) [C8 fl].
Section Sz2.
Variables m Fb j0 j1 j2 fl fjunk : ltac2:(SecDiet.SzSec.tyM 'fz_frame_cut__stmt "vvvvvvv" @m).
Lemma fz_frame_cut__body : ltac2:(SecDiet.SzSec.bodyP 'fz_frame_cut__stmt "vvvvvvv").
Proof using .
  intros FRC.
  apply (rw_cells_split_CB asegs _ _ [C8 j0; C8 j1; C8 j2] _ _ [C8 fl] [8; 256; 64; 30; Z.to_nat 4066; 128; 8; 24; 8; Z.to_nat 3568]%nat) in FRC; [|vm_compute; reflexivity].
  cbn [mk_CB_cells app] in FRC.
  (* [comment removed for export] *)
  repeat match type of FRC with context [CB _ ?t] =>
    lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in pose (j := t); change t with j in FRC; clearbody j end.
  (* [comment removed for export] *)
  pose (N4066 := (Z.to_nat 4066)); change (Z.to_nat 4066) with N4066 in FRC. pose (N3568 := (Z.to_nat 3568)); change (Z.to_nat 3568) with N3568 in FRC.
  replace Fb with (Fb + 0)%Z in FRC at 1 by lia.
  peel1 FRC K0 Fb 8%Z. peel1 FRC K1 Fb 16%Z. peel1 FRC K2 Fb 24%Z.
  peel1 FRC X0 Fb 32%Z. peel1 FRC EBc Fb 288%Z. peel1 FRC X1 Fb 352%Z. peel1 FRC FNT Fb 382%Z. peel1 FRC FNJ Fb 4448%Z.
  peel1 FRC X2 Fb 4576%Z. peel1 FRC PKc Fb 4584%Z. peel1 FRC X3 Fb 4608%Z. peel1 FRC HPc Fb 4616%Z. peel1 FRC X4 Fb 8184%Z.
  do 5 eexists. split; [| split; [exact EBc| split; [exact FNT| split; [exact FNJ| split; [exact PKc| split; [exact HPc| exact FRC]]]]]].
  replace (Fb + 0)%Z with Fb in K0 by lia.
  apply (proj2 (rw_cells_app asegs m Fb [C8 j0] [C8 j1; C8 j2])). split; [exact K0|].
  cbn [cells_size csize Nat.add]. replace (Fb + Z.of_nat 8)%Z with (Fb + 8)%Z by lia.
  apply (proj2 (rw_cells_app asegs m (Fb + 8) [C8 j1] [C8 j2])). split; [exact K1|].
  cbn [cells_size csize Nat.add]. replace (Fb + 8 + Z.of_nat 8)%Z with (Fb + 16)%Z by lia. exact K2.
Qed.
End Sz2.
Lemma fz_frame_cut : ltac:(let t := eval cbv delta [fz_frame_cut__stmt] in fz_frame_cut__stmt in exact t).
Proof using . intros m Fb j0 j1 j2 fl fjunk. ltac2:(SecDiet.SzSec.closeP 'fz_frame_cut__body "vvvvvvv"). Qed.
(* [comment removed for export] *)
Definition fz_shadow_cut__stmt : Prop := forall m S (sj : list byte),
  rw_cells asegs m S [CB 584 (repeat (Z_to_bv 8 0) 584); CB 440 sj] ->
  rw_cells asegs m S [CB 44 (repeat (Z_to_bv 8 0) 44)] /\ rw_cells asegs m (S + 44) [CB 512 (repeat (Z_to_bv 8 0) 512)]
  /\ rw_cells asegs m (S + 556) [CB 28 (repeat (Z_to_bv 8 0) 28)].
Section Sz3.
Variables m S sj : ltac2:(SecDiet.SzSec.tyM 'fz_shadow_cut__stmt "vvv" @m).
Lemma fz_shadow_cut__body : ltac2:(SecDiet.SzSec.bodyP 'fz_shadow_cut__stmt "vvv").
Proof using .
  intros SHC.
  apply (rw_cells_split_CB asegs _ _ [] _ _ [CB 440 sj] [44; 512; 28]%nat) in SHC; [|reflexivity].
  cbn [mk_CB_cells app] in SHC.
  change (firstn 44 (repeat (Z_to_bv 8 0) 584)) with (repeat (Z_to_bv 8 0) 44) in SHC.
  change (firstn 512 (skipn 44 (repeat (Z_to_bv 8 0) 584))) with (repeat (Z_to_bv 8 0) 512) in SHC.
  change (firstn 28 (skipn 512 (skipn 44 (repeat (Z_to_bv 8 0) 584)))) with (repeat (Z_to_bv 8 0) 28) in SHC.
  replace S with (S + 0)%Z in SHC at 1 by lia.
  peel1 SHC CA S 44%Z. peel1 SHC CB0 S 556%Z. peel1 SHC CC S 584%Z.
  replace (S + 0)%Z with S in CA by lia. split; [exact CA|]. split; [exact CB0| exact CC].
Qed.
End Sz3.
Lemma fz_shadow_cut : ltac:(let t := eval cbv delta [fz_shadow_cut__stmt] in fz_shadow_cut__stmt in exact t).
Proof using . intros m S sj. ltac2:(SecDiet.SzSec.closeP 'fz_shadow_cut__body "vvv"). Qed.
End CANSEC0.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FuzzTop.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER7 : fenter7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x58388 0xf8.
  Hypothesis SETSH00 : set_shadow_stmt 0x58268 0x00.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).

  Definition fz_top__stmt : Prop := forall (A : Type) (body : Monad.M PSt A) (Q : A -> PSt -> footprint -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (trC : list Z) (lo D : Z) (data : list byte),
    std_pre_o GIOA L RNG sp tp s CL FB [] lo FUZZ_STACK m ->
    ucallerA depth_fuzz_one L m sp s0 ra trC ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (Z.of_nat (length data)) -> datA RNG m CL D data ->
    (forall (SPA Fb : Z) (s' : PSt) (m' : mem) (fra : list cell) (jn ej : list byte) (hpc pkc : cell)
            (ra0 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 r18 r23 u3 u4 u5 u6 : word),
       hpureA L sp tp lo SPA -> GIOA L RNG s' CL FB (FZFL Fb) m' ->
       hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m' ->
       cells_size fra = 56%nat ->
       rw_cells asegs m' (Fb + 352) [CB 30 jn] -> rw_cells asegs m' (Fb + 382) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
       rw_cells asegs m' (Fb + 32) [CB 256 ej] ->
       rw_cells asegs m' (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m' (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
       ucallerA depth_fuzz_one L m' sp s0 ra trC -> datA RNG m' CL D data ->
       ps_outfile s' = ps_outfile s ->
       agrees_on (client_keeps [] CL (bv_unsigned sp)) m m' ->
       implMG RNG body s' Q
         (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp u0 u1 u2 sp (Z_to_bv 64 SPA) b0 b1 b2 b3 b4 b5 b6 b7
                  r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) r23
                  (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) u3 u4 u5 u6)
             F (Z_to_bv 64 0x84894) fc None m' (seg_rom asegs))) ->
    implMG RNG (fo_enter FO _ FF_FUZZ_ONE_INPUT body) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FUZZ_ONE_ENTRY) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables A body Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB trC lo D data : ltac2:(SecDiet.SzSec.tyM 'fz_top__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @A).
  Lemma fz_top__body : ltac2:(SecDiet.SzSec.bodyP 'fz_top__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FENTER7 GL SETSH00 SETSHF8.
 intros PRE UC -> -> DAT KONT.
    (nd_pre PRE 12%nat; intros G ST LO BU (SPT & TOP47) MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    unfold FUZZ_STACK, PCAP_L4_STACK in BU. unfold FUZZ_ONE_ENTRY.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    rng_sp_window RSTK sp RSPW.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    remember (bv_unsigned sp - 160 - (bv_unsigned sp - 160) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 191 <= SPA <= bv_unsigned sp - 160 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -160) - (bv_unsigned sp + -160) mod 32 = SPA)%Z)
      by (rewrite ESPA; dm_plia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 56%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    rewrite land_m32T by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -104)%Z.
    destruct (stk_split asegs _ lo (SPA + 56) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 56) 56 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 56) with 56%Z in STL, FRA. replace (SPA + 56 - 56)%Z with SPA in STL, FRA by lia.
    do 6 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 3 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FWS : Forall (client_ivA [] CL) [(bv_unsigned sp - 192, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s CL FB [] mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
      assert (AGa : agrees_on (client_keeps [] CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ [] []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FWS G'.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER7 _ spa) with (req := 4672%Z).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [dm_plia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { reflexivity. }
    { intros []. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk sjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ LSJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_FUZZ_ONE_INPUT) with 8192%Z in *.
    change (Z.to_nat (4672 / 8)) with 584%nat in *. change (Z.to_nat ((8192 - 4672) / 8)) with 440%nat in *.
    replace (ret_pc (Z_to_bv 64 542264)) with (Z_to_bv 64 542264) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G1) as ndP__; nd_pre ndP__ 9%nat; intros FBAND FTOP F64 _ T47 FRNG FSRNG SH1 SH2; nd_post).
    band_ind FBAND bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    assert (AGb : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
    assert (UCb : ucallerA depth_fuzz_one L m2 sp s0 ra trC)
      by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha; destruct (AGb a ltac:(lia) ltac:(left; lia)) as [E1 _]; exact E1).
    pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT AGb G1) as DATb.
    (* [comment removed for export] *)
    (nd_pre (fz_frame_cut _ _ _ _ _ _ _ FRC) 12%nat; intros ej jn jz pk hp FK EBc FNT FNJ PKc HPc FLG; nd_post). clear FRC.
    (* [comment removed for export] *)
    (nd_pre (fz_shadow_cut _ _ _ SHC) 3%nat; intros CA CB0 CC; nd_post). clear SHC.
    replace (Z.shiftr Fb 3 + 2147450880 + 44)%Z with (Z.shiftr Fb 3 + 2147450924)%Z in CB0 by lia.
    pose proof (munch_refl [(SPA - 4096, bv_unsigned sp); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G1) as (RT2 & _).
    pose proof (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G1) as GMS. unfold GOT_MEMSET in GMS.
    clear GOT SHB SUA GSU MI MU0 WM0 G0 AGa G UC DAT.
    ienterG.
    (* [comment removed for export] *)
    do 3 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    zstep.
    do 5 zstep.
    zstep. neg_lits.
    zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply fz_seg1 with (SH := (Z.shiftr Fb 3 + 2147450880)%Z); [assumption | lia | lia | eapply rng_sub'; [exact FSRNG| lia] | exact CA]. }
    cbv beta. intros ms' (m4 & -> & MU4 & WM4 & MI4 & CA4).
    lazymatch type of MU4 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU4 WM4 end.
    clear MU4 WM4 MI1.
    do 4 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RT4 : artcells mm)
        by (eapply artcells_munch; [exact RT2| exact MU| exact WM|]; repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]); apply Forall_nil) end.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply SETSHF8 with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450924)%Z) (n := 512%Z) (old := repeat (Z_to_bv 8 0) 512);
        [ exact MI4 | rewrite Hspa; exact ST1 | rewrite Hspa; unfold FAKE_STACK; lia | lia | exact RT4 | unfold GOT_MEMSET; exact GMS | reflexivity | reflexivity | lia | lia
        | exact CB0 | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]. }
    cbv beta. intros ms' PO. (nd_pre PO 8%nat; intros av m5 E MU5 WM5 MI5 ST5 CB5; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 542576)) with (Z_to_bv 64 542576) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unfold FAKE_STACK in MU5.
    lazymatch type of MU5 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU5 WM5 end.
    clear MU5 WM5 RT4 MI4.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply fz_seg2 with (SH := (Z.shiftr Fb 3 + 2147450880)%Z); [exact MI5 | lia | lia | eapply rng_sub; [exact FSRNG| lia| lia] | exact CC]. }
    cbv beta. intros ms' (m6 & -> & MU6 & WM6 & MI6 & CC6).
    lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end.
    clear MU6 WM6 MI5.
    eapply evtF_cut.
    { eapply fz_seg3 with (SH := (Z.shiftr Fb 3 + 2147450880)%Z);
        [exact MI6 | lia | lia | eapply rng_sub'; [exact FSRNG| lia] | eapply rng_sub; [exact FSRNG| lia| lia] | exact CA4 | exact CC6]. }
    cbv beta. intros ms' (m7 & -> & MU7 & WM7 & MI7 & CA7 & CC7).
    lazymatch type of MU7 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU7 WM7 end.
    clear MU7 WM7 MI6.
    do 3 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RT7 : artcells mm)
        by (eapply artcells_munch; [exact RT2| exact MU| exact WM|]; repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]); apply Forall_nil) end.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply SETSH00 with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450924)%Z) (n := 512%Z) (old := repeat (Z_to_bv 8 248) (Z.to_nat 512));
        [ exact MI7 | rewrite Hspa; eassumption | rewrite Hspa; unfold FAKE_STACK; lia | lia | exact RT7 | unfold GOT_MEMSET; exact GMS | reflexivity | reflexivity | lia | lia
        | exact CB5 | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]. }
    cbv beta. intros ms' PO. (nd_pre PO 8%nat; intros av8 m8 E MU8 WM8 MI8 ST8 CB8; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 542832)) with (Z_to_bv 64 542832) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unfold FAKE_STACK in MU8.
    lazymatch type of MU8 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU8 WM8 end.
    clear MU8 WM8 RT7 MI7.
    (* [comment removed for export] *)
    do 4 zstep.
    change (Z.to_nat 512) with 512%nat in CB8.
    pose proof G1 as G1'. rewrite <- (app_nil_r CL) in G1'.
    assert (FWo : Forall (own_ivA (FZFL Fb) ([] : list cblk) (bv_unsigned sp))
                   [(SPA - 4096, bv_unsigned sp); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FWo (Forall_nil _) G1' MU WM ltac:(lia)) as [G8 _];
      assert (RT8 : artcells mm)
        by (eapply artcells_munch; [exact RT2| exact MU| exact WM|]; repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]); apply Forall_nil)
    end.
    rewrite app_nil_r in G8. cbn [app] in G8.
    assert (ODST : mobjA RNG m8 (Fb + 382) 4066).
    { apply aobjA_mobjA; [| lia].
      assert (CO : cobjA RNG m8 (FZFL Fb) CL (Fb + 382) 4066)
        by (eapply (fz_cobj FO GIOA fflagA GL); [exact G8| lia| lia| lia|];
            eapply unpoisoned_sub; [eapply (fz_unp_fname m8 Fb); [exact CB8| dm_plia| lia| lia]| lia| lia]).
      exact (proj2 CO). }
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply asan_memset_specZ with (lo := lo) (Dst := (Fb + 382)%Z) (c := 0%Z) (n := 4066%Z) (junk := jz);
        [ reflexivity | reflexivity | reflexivity | lia | exact MI8 | rewrite Hspa; exact ST8 | rewrite Hspa; lia | lia | exact RT8 | lia
        | exact FNJ | exact ODST | lia | exact RIMG | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] ]. }
    cbv beta. intros ms' PO. destruct_exs PO. (nd_pre PO 6%nat; intros E MU9 WM9 MI9 ST9 FNZ9; nd_post).
    subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 542848)) with (Z_to_bv 64 542848) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch type of MU9 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU9 WM9 end.
    clear MU9 WM9 RT8 MI8 G8 ODST G1' FWo.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply fz_seg4 with (SH := (Z.shiftr Fb 3 + 2147450880)%Z); [exact MI9 | lia | lia | eapply rng_sub; [exact FSRNG| lia| lia] | exact CC7]. }
    cbv beta. intros ms' (m10 & -> & MU10 & WM10 & MI10 & CC10).
    lazymatch type of MU10 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU10 WM10 end.
    clear MU10 WM10 MI9.
    (* [comment removed for export] *)
    pose proof G1 as G1'. rewrite <- (app_nil_r CL) in G1'.
    assert (FWo : Forall (own_ivA (FZFL Fb) ([] : list cblk) (bv_unsigned sp))
                   [(SPA - 4096, bv_unsigned sp); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m10 _ [] _ FWo (Forall_nil _) G1' MU WM ltac:(lia)) as [G10 AG10].
    rewrite app_nil_r in G10. cbn [app] in G10.
    assert (AG10' : agrees_on (client_keeps [] CL (bv_unsigned sp)) m2 m10) by (eapply agrees_on_weaken; [exact AG10| intros a K0; split; [exact K0| exact I]]).
    assert (UC10 : ucallerA depth_fuzz_one L m10 sp s0 ra trC)
      by (eapply ucaller_keep; [exact UCb| exact TOP47|]; intros a Ha; apply (AG10' a); [lia| left; lia]).
    pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DATb AG10' G10) as DAT10.
    destruct (rw_cells_cut _ _ _ 1%nat FK) as [FK0 _]. cbn [firstn] in FK0.
    replace (Z.shiftr Fb 3 + 2147450880 + 556)%Z with (Z.shiftr Fb 3 + 2147451436)%Z in CC10 by lia.
    apply evtF_done. subst POSTQ.
    eapply KONT with (SPA := SPA) (Fb := Fb) (fra := [CB 48 (firstn 48 jA); C8 (Z_to_bv 64 Fb)]) (jn := jn) (ej := ej) (hpc := CB 8 hp) (pkc := CB 8 pk).
    - unfold hpureA, FUZZ_STACK, PCAP_L4_STACK. repeat (split; [first [assumption | lia]|]). exact ALN.
    - exact G10.
    - split; [exact MI10|]. split; [exact ST9|]. split; [exact STG|]. split; [exact FRA|]. split; [exact FR|]. split; [eexists; exact FK0|].
      split; [exact FLG|]. split; [exact CA7|]. split; [exact CB8| exact CC10].
    - reflexivity.
    - exact FNT.
    - exact FNZ9.
    - exact EBc.
    - exact HPc.
    - reflexivity.
    - exact PKc.
    - reflexivity.
    - exact UC10.
    - exact DAT10.
    - exact OF1.
    - eapply agrees_on_trans; [exact AGb| exact AG10'].
  Qed.
  End Sz4.
  Lemma fz_top : ltac:(let t := eval cbv delta [fz_top__stmt] in fz_top__stmt in exact t).
  Proof using FENTER7 GL SETSH00 SETSHF8. intros A body Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB trC lo D data. ltac2:(SecDiet.SzSec.closeP 'fz_top__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzTop.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit2__A3P.LibcKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_btfA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_segA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac dm_plia := first [ atop_facts; once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); Z.div_mod_to_equations; lia_tiers
                            | Z.div_mod_to_equations; lia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

(* [comment removed for export] *)
Ltac norm_addr H P :=
  lazymatch type of H with
  | rw_cells _ _ (?b + Z.of_nat ?n)%Z _ =>
      lazymatch b with
      | (P + ?k0)%Z => let k := eval vm_compute in (k0 + Z.of_nat n)%Z in replace (b + Z.of_nat n)%Z with (P + k)%Z in H by lia
      | P => let k := eval vm_compute in (Z.of_nat n) in replace (P + Z.of_nat n)%Z with (P + k)%Z in H by lia
      end
  end.
Ltac cut_cells H k H1 P :=
  let H2 := fresh "TMP" in
  destruct (rw_cells_cut _ _ _ k H) as [H1 H2]; clear H; cbn [firstn skipn cells_size csize Nat.add] in H1, H2;
  norm_addr H2 P; rename H2 into H.

Lemma land_m32T : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

(* [comment removed for export] *)
Ltac peel1 H H1 P k' :=
  lazymatch type of H with
  | rw_cells ?sg ?mm ?A (?c :: ?rest) =>
      let H2 := fresh "TMP" in
      change (c :: rest) with ([c] ++ rest) in H;
      apply (proj1 (rw_cells_app sg mm A [c] rest)) in H as [H1 H2];
      replace (A + Z.of_nat (cells_size [c]))%Z with (P + k')%Z in H2 by (cbn [cells_size csize]; lia);
      rename H2 into H
  end.

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition fz_frame_cut__stmt : Prop := forall m Fb (j0 j1 j2 fl : word) (fjunk : list byte),
  rw_cells asegs m Fb [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (8192 - 32)) fjunk; C8 fl] ->
  exists ej jn jz pk hp,
    rw_cells asegs m Fb [C8 j0; C8 j1; C8 j2] /\ rw_cells asegs m (Fb + 32) [CB 256 ej]
    /\ rw_cells asegs m (Fb + 352) [CB 30 jn] /\ rw_cells asegs m (Fb + 382) [CB 4066 jz]
    /\ rw_cells asegs m (Fb + 4576) [CB 8 pk] /\ rw_cells asegs m (Fb + 4608) [CB 8 hp]
    /\ rw_cells asegs m (Fb + 8184) [C8 fl].
Section Sz2.
Variables m Fb j0 j1 j2 fl fjunk : ltac2:(SecDiet.SzSec.tyM 'fz_frame_cut__stmt "vvvvvvv" @m).
Lemma fz_frame_cut__body : ltac2:(SecDiet.SzSec.bodyP 'fz_frame_cut__stmt "vvvvvvv").
Proof using .
  intros FRC.
  apply (rw_cells_split_CB asegs _ _ [C8 j0; C8 j1; C8 j2] _ _ [C8 fl] [8; 256; 64; 30; Z.to_nat 4066; 128; 8; 24; 8; Z.to_nat 3568]%nat) in FRC; [|vm_compute; reflexivity].
  cbn [mk_CB_cells app] in FRC.
  (* [comment removed for export] *)
  repeat match type of FRC with context [CB _ ?t] =>
    lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in pose (j := t); change t with j in FRC; clearbody j end.
  (* [comment removed for export] *)
  pose (N4066 := (Z.to_nat 4066)); change (Z.to_nat 4066) with N4066 in FRC. pose (N3568 := (Z.to_nat 3568)); change (Z.to_nat 3568) with N3568 in FRC.
  replace Fb with (Fb + 0)%Z in FRC at 1 by lia.
  peel1 FRC K0 Fb 8%Z. peel1 FRC K1 Fb 16%Z. peel1 FRC K2 Fb 24%Z.
  peel1 FRC X0 Fb 32%Z. peel1 FRC EBc Fb 288%Z. peel1 FRC X1 Fb 352%Z. peel1 FRC FNT Fb 382%Z. peel1 FRC FNJ Fb 4448%Z.
  peel1 FRC X2 Fb 4576%Z. peel1 FRC PKc Fb 4584%Z. peel1 FRC X3 Fb 4608%Z. peel1 FRC HPc Fb 4616%Z. peel1 FRC X4 Fb 8184%Z.
  do 5 eexists. split; [| split; [exact EBc| split; [exact FNT| split; [exact FNJ| split; [exact PKc| split; [exact HPc| exact FRC]]]]]].
  replace (Fb + 0)%Z with Fb in K0 by lia.
  apply (proj2 (rw_cells_app asegs m Fb [C8 j0] [C8 j1; C8 j2])). split; [exact K0|].
  cbn [cells_size csize Nat.add]. replace (Fb + Z.of_nat 8)%Z with (Fb + 8)%Z by lia.
  apply (proj2 (rw_cells_app asegs m (Fb + 8) [C8 j1] [C8 j2])). split; [exact K1|].
  cbn [cells_size csize Nat.add]. replace (Fb + 8 + Z.of_nat 8)%Z with (Fb + 16)%Z by lia. exact K2.
Qed.
End Sz2.
Lemma fz_frame_cut : ltac:(let t := eval cbv delta [fz_frame_cut__stmt] in fz_frame_cut__stmt in exact t).
Proof using . intros m Fb j0 j1 j2 fl fjunk. ltac2:(SecDiet.SzSec.closeP 'fz_frame_cut__body "vvvvvvv"). Qed.
(* [comment removed for export] *)
Definition fz_shadow_cut__stmt : Prop := forall m S (sj : list byte),
  rw_cells asegs m S [CB 584 (repeat (Z_to_bv 8 0) 584); CB 440 sj] ->
  rw_cells asegs m S [CB 44 (repeat (Z_to_bv 8 0) 44)] /\ rw_cells asegs m (S + 44) [CB 512 (repeat (Z_to_bv 8 0) 512)]
  /\ rw_cells asegs m (S + 556) [CB 28 (repeat (Z_to_bv 8 0) 28)].
Section Sz3.
Variables m S sj : ltac2:(SecDiet.SzSec.tyM 'fz_shadow_cut__stmt "vvv" @m).
Lemma fz_shadow_cut__body : ltac2:(SecDiet.SzSec.bodyP 'fz_shadow_cut__stmt "vvv").
Proof using .
  intros SHC.
  apply (rw_cells_split_CB asegs _ _ [] _ _ [CB 440 sj] [44; 512; 28]%nat) in SHC; [|reflexivity].
  cbn [mk_CB_cells app] in SHC.
  change (firstn 44 (repeat (Z_to_bv 8 0) 584)) with (repeat (Z_to_bv 8 0) 44) in SHC.
  change (firstn 512 (skipn 44 (repeat (Z_to_bv 8 0) 584))) with (repeat (Z_to_bv 8 0) 512) in SHC.
  change (firstn 28 (skipn 512 (skipn 44 (repeat (Z_to_bv 8 0) 584)))) with (repeat (Z_to_bv 8 0) 28) in SHC.
  replace S with (S + 0)%Z in SHC at 1 by lia.
  peel1 SHC CA S 44%Z. peel1 SHC CB0 S 556%Z. peel1 SHC CC S 584%Z.
  replace (S + 0)%Z with S in CA by lia. split; [exact CA|]. split; [exact CB0| exact CC].
Qed.
End Sz3.
Lemma fz_shadow_cut : ltac:(let t := eval cbv delta [fz_shadow_cut__stmt] in fz_shadow_cut__stmt in exact t).
Proof using . intros m S sj. ltac2:(SecDiet.SzSec.closeP 'fz_shadow_cut__body "vvv"). Qed.
End CANSEC0.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FuzzTop.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER7 : fenter7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x583f0 0xf8.
  Hypothesis SETSH00 : set_shadow_stmt 0x582d0 0x00.
  #[local] Notation PSt := (PState H hptr).
  #[local] Notation cblk := (@cblock hptr).

  Definition fz_top__stmt : Prop := forall (A : Type) (body : Monad.M PSt A) (Q : A -> PSt -> footprint -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PSt) (CL FB : list cblk) (trC : list Z) (lo D : Z) (data : list byte),
    std_pre_o GIOA L RNG sp tp s CL FB [] lo FUZZ_STACK m ->
    ucallerA depth_fuzz_one L m sp s0 ra trC ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (Z.of_nat (length data)) -> datA RNG m CL D data ->
    (forall (SPA Fb : Z) (s' : PSt) (m' : mem) (fra : list cell) (jn ej : list byte) (hpc pkc : cell)
            (ra0 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 r18 r23 u3 u4 u5 u6 : word),
       hpureA L sp tp lo SPA -> GIOA L RNG s' CL FB (FZFL Fb) m' ->
       hcoreA fflagA L sp lo SPA Fb [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] fra m' ->
       cells_size fra = 56%nat ->
       rw_cells asegs m' (Fb + 352) [CB 30 jn] -> rw_cells asegs m' (Fb + 382) [CB 4066 (repeat (Z_to_bv 8 0) 4066)] ->
       rw_cells asegs m' (Fb + 32) [CB 256 ej] ->
       rw_cells asegs m' (Fb + 4608) [hpc] -> csize hpc = 8%nat -> rw_cells asegs m' (Fb + 4576) [pkc] -> csize pkc = 8%nat ->
       ucallerA depth_fuzz_one L m' sp s0 ra trC -> datA RNG m' CL D data ->
       ps_outfile s' = ps_outfile s ->
       agrees_on (client_keeps [] CL (bv_unsigned sp)) m m' ->
       implMG RNG body s' Q
         (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp u0 u1 u2 sp (Z_to_bv 64 SPA) b0 b1 b2 b3 b4 b5 b6 b7
                  r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450924)) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 D) r23
                  (Z_to_bv 64 Fb) (Z_to_bv 64 0x1000) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) u3 u4 u5 u6)
             F (Z_to_bv 64 0x848fc) fc None m' (seg_rom asegs))) ->
    implMG RNG (fo_enter FO _ FF_FUZZ_ONE_INPUT body) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FUZZ_ONE_ENTRY) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables A body Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB trC lo D data : ltac2:(SecDiet.SzSec.tyM 'fz_top__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @A).
  Lemma fz_top__body : ltac2:(SecDiet.SzSec.bodyP 'fz_top__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FENTER7 GL SETSH00 SETSHF8.
 intros PRE UC -> -> DAT KONT.
    (nd_pre PRE 12%nat; intros G ST LO BU (SPT & TOP47) MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    unfold FUZZ_STACK, PCAP_L4_STACK in BU. unfold FUZZ_ONE_ENTRY.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    rng_sp_window RSTK sp RSPW.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    remember (bv_unsigned sp - 160 - (bv_unsigned sp - 160) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 191 <= SPA <= bv_unsigned sp - 160 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -160) - (bv_unsigned sp + -160) mod 32 = SPA)%Z)
      by (rewrite ESPA; dm_plia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 56%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    rewrite land_m32T by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -104)%Z.
    destruct (stk_split asegs _ lo (SPA + 56) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 56) 56 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 56) with 56%Z in STL, FRA. replace (SPA + 56 - 56)%Z with SPA in STL, FRA by lia.
    do 6 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 3 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FWS : Forall (client_ivA [] CL) [(bv_unsigned sp - 192, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s CL FB [] mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
      assert (AGa : agrees_on (client_keeps [] CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ [] []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FWS G'.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER7 _ spa) with (req := 4672%Z).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [dm_plia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { reflexivity. }
    { intros []. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk sjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ LSJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_FUZZ_ONE_INPUT) with 8192%Z in *.
    change (Z.to_nat (4672 / 8)) with 584%nat in *. change (Z.to_nat ((8192 - 4672) / 8)) with 440%nat in *.
    replace (ret_pc (Z_to_bv 64 542368)) with (Z_to_bv 64 542368) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (pose proof (fz_frame_facts FO GIOA fflagA GL _ _ _ _ _ _ _ G1) as ndP__; nd_pre ndP__ 9%nat; intros FBAND FTOP F64 _ T47 FRNG FSRNG SH1 SH2; nd_post).
    band_ind FBAND bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    assert (AGb : agrees_on (client_keeps [] CL (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
    assert (UCb : ucallerA depth_fuzz_one L m2 sp s0 ra trC)
      by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha; destruct (AGb a ltac:(lia) ltac:(left; lia)) as [E1 _]; exact E1).
    pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DAT AGb G1) as DATb.
    (* [comment removed for export] *)
    (nd_pre (fz_frame_cut _ _ _ _ _ _ _ FRC) 12%nat; intros ej jn jz pk hp FK EBc FNT FNJ PKc HPc FLG; nd_post). clear FRC.
    (* [comment removed for export] *)
    (nd_pre (fz_shadow_cut _ _ _ SHC) 3%nat; intros CA CB0 CC; nd_post). clear SHC.
    replace (Z.shiftr Fb 3 + 2147450880 + 44)%Z with (Z.shiftr Fb 3 + 2147450924)%Z in CB0 by lia.
    pose proof (munch_refl [(SPA - 4096, bv_unsigned sp); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G1) as (RT2 & _).
    pose proof (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G1) as GMS. unfold GOT_MEMSET in GMS.
    clear GOT SHB SUA GSU MI MU0 WM0 G0 AGa G UC DAT.
    ienterG.
    (* [comment removed for export] *)
    do 3 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    zstep.
    do 5 zstep.
    zstep. neg_lits.
    zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply fz_seg1 with (SH := (Z.shiftr Fb 3 + 2147450880)%Z); [assumption | lia | lia | eapply rng_sub'; [exact FSRNG| lia] | exact CA]. }
    cbv beta. intros ms' (m4 & -> & MU4 & WM4 & MI4 & CA4).
    lazymatch type of MU4 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU4 WM4 end.
    clear MU4 WM4 MI1.
    do 4 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RT4 : artcells mm)
        by (eapply artcells_munch; [exact RT2| exact MU| exact WM|]; repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]); apply Forall_nil) end.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply SETSHF8 with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450924)%Z) (n := 512%Z) (old := repeat (Z_to_bv 8 0) 512);
        [ exact MI4 | rewrite Hspa; exact ST1 | rewrite Hspa; unfold FAKE_STACK; lia | lia | exact RT4 | unfold GOT_MEMSET; exact GMS | reflexivity | reflexivity | lia | lia
        | exact CB0 | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]. }
    cbv beta. intros ms' PO. (nd_pre PO 8%nat; intros av m5 E MU5 WM5 MI5 ST5 CB5; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 542680)) with (Z_to_bv 64 542680) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unfold FAKE_STACK in MU5.
    lazymatch type of MU5 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU5 WM5 end.
    clear MU5 WM5 RT4 MI4.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply fz_seg2 with (SH := (Z.shiftr Fb 3 + 2147450880)%Z); [exact MI5 | lia | lia | eapply rng_sub; [exact FSRNG| lia| lia] | exact CC]. }
    cbv beta. intros ms' (m6 & -> & MU6 & WM6 & MI6 & CC6).
    lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end.
    clear MU6 WM6 MI5.
    eapply evtF_cut.
    { eapply fz_seg3 with (SH := (Z.shiftr Fb 3 + 2147450880)%Z);
        [exact MI6 | lia | lia | eapply rng_sub'; [exact FSRNG| lia] | eapply rng_sub; [exact FSRNG| lia| lia] | exact CA4 | exact CC6]. }
    cbv beta. intros ms' (m7 & -> & MU7 & WM7 & MI7 & CA7 & CC7).
    lazymatch type of MU7 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU7 WM7 end.
    clear MU7 WM7 MI6.
    do 3 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RT7 : artcells mm)
        by (eapply artcells_munch; [exact RT2| exact MU| exact WM|]; repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]); apply Forall_nil) end.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply SETSH00 with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450924)%Z) (n := 512%Z) (old := repeat (Z_to_bv 8 248) (Z.to_nat 512));
        [ exact MI7 | rewrite Hspa; eassumption | rewrite Hspa; unfold FAKE_STACK; lia | lia | exact RT7 | unfold GOT_MEMSET; exact GMS | reflexivity | reflexivity | lia | lia
        | exact CB5 | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]. }
    cbv beta. intros ms' PO. (nd_pre PO 8%nat; intros av8 m8 E MU8 WM8 MI8 ST8 CB8; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 542936)) with (Z_to_bv 64 542936) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unfold FAKE_STACK in MU8.
    lazymatch type of MU8 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU8 WM8 end.
    clear MU8 WM8 RT7 MI7.
    (* [comment removed for export] *)
    do 4 zstep.
    change (Z.to_nat 512) with 512%nat in CB8.
    pose proof G1 as G1'. rewrite <- (app_nil_r CL) in G1'.
    assert (FWo : Forall (own_ivA (FZFL Fb) ([] : list cblk) (bv_unsigned sp))
                   [(SPA - 4096, bv_unsigned sp); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FWo (Forall_nil _) G1' MU WM ltac:(lia)) as [G8 _];
      assert (RT8 : artcells mm)
        by (eapply artcells_munch; [exact RT2| exact MU| exact WM|]; repeat (apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia|]); apply Forall_nil)
    end.
    rewrite app_nil_r in G8. cbn [app] in G8.
    assert (ODST : mobjA RNG m8 (Fb + 382) 4066).
    { apply aobjA_mobjA; [| lia].
      assert (CO : cobjA RNG m8 (FZFL Fb) CL (Fb + 382) 4066)
        by (eapply (fz_cobj FO GIOA fflagA GL); [exact G8| lia| lia| lia|];
            eapply unpoisoned_sub; [eapply (fz_unp_fname m8 Fb); [exact CB8| dm_plia| lia| lia]| lia| lia]).
      exact (proj2 CO). }
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut.
    { eapply asan_memset_specZ with (lo := lo) (Dst := (Fb + 382)%Z) (c := 0%Z) (n := 4066%Z) (junk := jz);
        [ reflexivity | reflexivity | reflexivity | lia | exact MI8 | rewrite Hspa; exact ST8 | rewrite Hspa; lia | lia | exact RT8 | lia
        | exact FNJ | exact ODST | lia | exact RIMG | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] ]. }
    cbv beta. intros ms' PO. destruct_exs PO. (nd_pre PO 6%nat; intros E MU9 WM9 MI9 ST9 FNZ9; nd_post).
    subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 542952)) with (Z_to_bv 64 542952) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch type of MU9 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU9 WM9 end.
    clear MU9 WM9 RT8 MI8 G8 ODST G1' FWo.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply fz_seg4 with (SH := (Z.shiftr Fb 3 + 2147450880)%Z); [exact MI9 | lia | lia | eapply rng_sub; [exact FSRNG| lia| lia] | exact CC7]. }
    cbv beta. intros ms' (m10 & -> & MU10 & WM10 & MI10 & CC10).
    lazymatch type of MU10 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU10 WM10 end.
    clear MU10 WM10 MI9.
    (* [comment removed for export] *)
    pose proof G1 as G1'. rewrite <- (app_nil_r CL) in G1'.
    assert (FWo : Forall (own_ivA (FZFL Fb) ([] : list cblk) (bv_unsigned sp))
                   [(SPA - 4096, bv_unsigned sp); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m10 _ [] _ FWo (Forall_nil _) G1' MU WM ltac:(lia)) as [G10 AG10].
    rewrite app_nil_r in G10. cbn [app] in G10.
    assert (AG10' : agrees_on (client_keeps [] CL (bv_unsigned sp)) m2 m10) by (eapply agrees_on_weaken; [exact AG10| intros a K0; split; [exact K0| exact I]]).
    assert (UC10 : ucallerA depth_fuzz_one L m10 sp s0 ra trC)
      by (eapply ucaller_keep; [exact UCb| exact TOP47|]; intros a Ha; apply (AG10' a); [lia| left; lia]).
    pose proof (datA_keep FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ DATb AG10' G10) as DAT10.
    destruct (rw_cells_cut _ _ _ 1%nat FK) as [FK0 _]. cbn [firstn] in FK0.
    replace (Z.shiftr Fb 3 + 2147450880 + 556)%Z with (Z.shiftr Fb 3 + 2147451436)%Z in CC10 by lia.
    apply evtF_done. subst POSTQ.
    eapply KONT with (SPA := SPA) (Fb := Fb) (fra := [CB 48 (firstn 48 jA); C8 (Z_to_bv 64 Fb)]) (jn := jn) (ej := ej) (hpc := CB 8 hp) (pkc := CB 8 pk).
    - unfold hpureA, FUZZ_STACK, PCAP_L4_STACK. repeat (split; [first [assumption | lia]|]). exact ALN.
    - exact G10.
    - split; [exact MI10|]. split; [exact ST9|]. split; [exact STG|]. split; [exact FRA|]. split; [exact FR|]. split; [eexists; exact FK0|].
      split; [exact FLG|]. split; [exact CA7|]. split; [exact CB8| exact CC10].
    - reflexivity.
    - exact FNT.
    - exact FNZ9.
    - exact EBc.
    - exact HPc.
    - reflexivity.
    - exact PKc.
    - reflexivity.
    - exact UC10.
    - exact DAT10.
    - exact OF1.
    - eapply agrees_on_trans; [exact AGb| exact AG10'].
  Qed.
  End Sz4.
  Lemma fz_top : ltac:(let t := eval cbv delta [fz_top__stmt] in fz_top__stmt in exact t).
  Proof using FENTER7 GL SETSH00 SETSHF8. intros A body Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB trC lo D data. ltac2:(SecDiet.SzSec.closeP 'fz_top__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End FuzzTop.
End CANSEC1.
End TwB.
End F_fuzz_topA.

(* [comment removed for export] *)
Module F_fuzz_mainA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Fuzz_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_btfA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_bodyA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_outA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_topA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FuzzMain.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOL : fo_leaf_laws FO.
  Hypothesis FENTER7 : fenter7_stmt_o FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x58388 0xf8.
  Hypothesis SETSH00 : set_shadow_stmt 0x58268 0x00.
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FWRITE : fwrite_stmt_o HO GIOA.
  Hypothesis REMOVE : remove_stmt_o GIOA.
  Hypothesis UNLINK : unlink_stmt_o GIOA.
  Hypothesis CLOSE : close_stmt_o GIOA.
  Hypothesis MKSTEMP : mkstemp_stmt_o GIOA.
  Hypothesis PRINTF_R : printf_d_stmt_o GIOA FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o GIOA FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO GIOA FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO FO sites GIOA TP.
  Hypothesis PNEXT : pcap_next_ex_stmt HO FO sites GIOA TP.
  Hypothesis PSTATS : pcap_stats_stmt GIOA TP.
  Hypothesis PCLOSE : pcap_close_stmt HO FO sites GIOA TP.
  #[local] Notation PSt := (PState H hptr).

  #[using="Type"] Lemma implMG_getret_l : forall {A B} RNG (h : PSt -> A) (f : A -> Monad.M PSt B) s Q ms,
    implMG RNG (f (h s)) s Q ms -> implMG RNG (mbind (mbind mget (fun s => mret (h s))) f) s Q ms.
  Proof. intros. exact H0. Qed.

  (* [comment removed for export] *)
  Definition fuzz_one_proofA__stmt : Prop := fuzz_one_stmt HO FO sites GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB trC lo D data : ltac2:(SecDiet.SzSec.tyM 'fuzz_one_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL GH HAL EQB FOL FENTER7 FFREE7 SETSHF8 SETSH00 FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O FPRINTF_DD FPRINTF_S POPEN PNEXT PSTATS PCLOSE"] Lemma fuzz_one_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fuzz_one_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR Ea0 Ea1 DAT DOBJ DLEN.
    pose proof PRE as (G & ST & LO & BU & (SPT & TOP47) & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    unfold harness_call. rewrite (fuzz_unfoldA HO FO sites).
    eapply implMG_bind with (Q1 := fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m).
    - eapply (fz_top FO GIOA fflagA GL FENTER7 SETSHF8 SETSH00) with (trC := trC) (D := D) (data := data);
        [exact PRE | exact UC | exact Ea0 | exact Ea1 | split; [exact DAT| exact DOBJ] |].
      intros SPA Fb s1' m1 fra jn ej hpc pkc ra0 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 r18 r23 u3 u4 u5 u6 HP G1 HC FRAS FNT FNZ EBc HPc HP8 PKc PK8 UC1 DAT1 OF1 AG1.
      apply implMG_getret_l.
      eapply implMG_mono.
      + eapply (fz_out HO FO sites GIOA TP fflagA GL GH) with (trC := trC);
          [ intros; eapply (fz_body HO FO sites GIOA TP fflagA GL GH HAL EQB FOL FFREE7 SETSHF8 FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O
                              FPRINTF_DD FPRINTF_S POPEN PNEXT PSTATS PCLOSE); eassumption
          | exact FFREE7 | exact SETSHF8 | exact FOPEN
          | exact HP | split; [exact RSTK| split; [exact RIMG| split; [exact RISH| exact RTLS]]] | exact G1 | exact HC | exact FRAS | exact FNT | exact FNZ | exact EBc
          | exact HPc | exact HP8 | exact PKc | exact PK8 | exact UC1 | exact TR | exact DAT1 | exact DLEN ].
      + intros u sx RNGx msx PO. eapply (fz_post_back GIOA) with (RNG1 := RNG) (m1 := m1); [intros b j Hb; exact Hb| exact AG1| exact PO].
    - intros [] s' RNG' ms' (FP & PO). destruct_exs PO. destruct PO as (-> & MI' & ST' & AG' & G').
      apply implMG_ret. apply evtF_done. split; [exact FP|].
      do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'| reflexivity].
  Qed.
  End Sz2.
  #[using="fflagA GL GH HAL EQB FOL FENTER7 FFREE7 SETSHF8 SETSH00 FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O FPRINTF_DD FPRINTF_S POPEN PNEXT PSTATS PCLOSE"] Theorem fuzz_one_proofA : ltac:(let t := eval cbv delta [fuzz_one_proofA__stmt] in fuzz_one_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB trC lo D data. ltac2:(SecDiet.SzSec.closeP 'fuzz_one_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FuzzMain.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_fuzz_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_btfA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_bodyA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_outA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_btfA__A3P.F_fuzz_topA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FuzzMain.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GH : gia_harn_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  Hypothesis FOL : fo_leaf_laws FO.
  Hypothesis FENTER7 : fenter7_stmt_o FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETSHF8 : set_shadow_stmt 0x583f0 0xf8.
  Hypothesis SETSH00 : set_shadow_stmt 0x582d0 0x00.
  Hypothesis FOPEN : fopen_stmt_o HO GIOA TP.
  Hypothesis FCLOSE : fclose_stmt_o HO GIOA TP.
  Hypothesis FWRITE : fwrite_stmt_o HO GIOA.
  Hypothesis REMOVE : remove_stmt_o GIOA.
  Hypothesis UNLINK : unlink_stmt_o GIOA.
  Hypothesis CLOSE : close_stmt_o GIOA.
  Hypothesis MKSTEMP : mkstemp_stmt_o GIOA.
  Hypothesis PRINTF_R : printf_d_stmt_o GIOA FMT_FAILED_REMOVE pieces_failed_remove.
  Hypothesis PRINTF_O : printf_d_stmt_o GIOA FMT_FAILED_OPEN pieces_failed_open.
  Hypothesis FPRINTF_DD : fprintf_dd_stmt_o HO GIOA FMT_PACKET_LENGTH pieces_packet_length.
  Hypothesis FPRINTF_S : fprintf_s_stmt_o HO GIOA FMT_COULDNT_OPEN pieces_couldnt_open.
  Hypothesis POPEN : pcap_open_offline_stmt HO FO sites GIOA TP.
  Hypothesis PNEXT : pcap_next_ex_stmt HO FO sites GIOA TP.
  Hypothesis PSTATS : pcap_stats_stmt GIOA TP.
  Hypothesis PCLOSE : pcap_close_stmt HO FO sites GIOA TP.
  #[local] Notation PSt := (PState H hptr).

  #[using="Type"] Lemma implMG_getret_l : forall {A B} RNG (h : PSt -> A) (f : A -> Monad.M PSt B) s Q ms,
    implMG RNG (f (h s)) s Q ms -> implMG RNG (mbind (mbind mget (fun s => mret (h s))) f) s Q ms.
  Proof. intros. exact H0. Qed.

  (* [comment removed for export] *)
  Definition fuzz_one_proofA__stmt : Prop := fuzz_one_stmt HO FO sites GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB trC lo D data : ltac2:(SecDiet.SzSec.tyM 'fuzz_one_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL GH HAL EQB FOL FENTER7 FFREE7 SETSHF8 SETSH00 FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O FPRINTF_DD FPRINTF_S POPEN PNEXT PSTATS PCLOSE"] Lemma fuzz_one_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fuzz_one_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR Ea0 Ea1 DAT DOBJ DLEN.
    pose proof PRE as (G & ST & LO & BU & (SPT & TOP47) & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    unfold harness_call. rewrite (fuzz_unfoldA HO FO sites).
    eapply implMG_bind with (Q1 := fz_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL lo m).
    - eapply (fz_top FO GIOA fflagA GL FENTER7 SETSHF8 SETSH00) with (trC := trC) (D := D) (data := data);
        [exact PRE | exact UC | exact Ea0 | exact Ea1 | split; [exact DAT| exact DOBJ] |].
      intros SPA Fb s1' m1 fra jn ej hpc pkc ra0 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 r18 r23 u3 u4 u5 u6 HP G1 HC FRAS FNT FNZ EBc HPc HP8 PKc PK8 UC1 DAT1 OF1 AG1.
      apply implMG_getret_l.
      eapply implMG_mono.
      + eapply (fz_out HO FO sites GIOA TP fflagA GL GH) with (trC := trC);
          [ intros; eapply (fz_body HO FO sites GIOA TP fflagA GL GH HAL EQB FOL FFREE7 SETSHF8 FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O
                              FPRINTF_DD FPRINTF_S POPEN PNEXT PSTATS PCLOSE); eassumption
          | exact FFREE7 | exact SETSHF8 | exact FOPEN
          | exact HP | split; [exact RSTK| split; [exact RIMG| split; [exact RISH| exact RTLS]]] | exact G1 | exact HC | exact FRAS | exact FNT | exact FNZ | exact EBc
          | exact HPc | exact HP8 | exact PKc | exact PK8 | exact UC1 | exact TR | exact DAT1 | exact DLEN ].
      + intros u sx RNGx msx PO. eapply (fz_post_back GIOA) with (RNG1 := RNG) (m1 := m1); [intros b j Hb; exact Hb| exact AG1| exact PO].
    - intros [] s' RNG' ms' (FP & PO). destruct_exs PO. destruct PO as (-> & MI' & ST' & AG' & G').
      apply implMG_ret. apply evtF_done. split; [exact FP|].
      do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'| reflexivity].
  Qed.
  End Sz2.
  #[using="fflagA GL GH HAL EQB FOL FENTER7 FFREE7 SETSHF8 SETSH00 FOPEN FCLOSE FWRITE REMOVE UNLINK CLOSE MKSTEMP PRINTF_R PRINTF_O FPRINTF_DD FPRINTF_S POPEN PNEXT PSTATS PCLOSE"] Theorem fuzz_one_proofA : ltac:(let t := eval cbv delta [fuzz_one_proofA__stmt] in fuzz_one_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB trC lo D data. ltac2:(SecDiet.SzSec.closeP 'fuzz_one_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FuzzMain.
End CANSEC1.
End TwB.
End F_fuzz_mainA.
