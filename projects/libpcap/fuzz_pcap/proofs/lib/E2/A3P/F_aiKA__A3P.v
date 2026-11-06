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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_aiBA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require AccFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB AiAuxB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_aiKA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_aiBA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA_loop.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AccFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ck_dead_pc pc := fail.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K; lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_dead_pc pc then first [ exfalso; ck_lia | ck_arm OK n' ] else first [ ck_arm OK n' | exfalso; ck_lia ] | _ => first [ exfalso; ck_lia | ck_arm OK n' ] end
    end
  end.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= plia.
Local Ltac flia ::= first [ sassumption | plia | assumption ].
Local Ltac acc_hint ::= acc_hint_cheap.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.


Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.

Ltac msg_ok := vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]].
(* [comment removed for export] *)
Ltac fmt_at_tac MI ADDR str :=
  split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs _ ADDR (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string str) ++ [Z_to_bv 8 0])
                   MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
  split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]).

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section AIX.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL m.
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 16512 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.

  #[local] Abbreviation POSTQ := (add_interface_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Abbreviation AGP := (ai_AGP FL sp C1 C2 P B CUR EB p m).
  #[local] Abbreviation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  (* [comment removed for export] *)
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : (0 < P /\ P + 680 <= ATOP)%Z.
  Hypothesis B14 : (0 < B /\ B + pc_bufalloc p <= ATOP)%Z.
  Hypothesis LENB : (Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32)%Z.
  Hypothesis CURS : (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L)%Z.
  (* [comment removed for export] *)
  Hypothesis EBL : clocA FL (C1 ++ C2) EB 256.
  Hypothesis EBP : (EB + 256 <= P + 648 \/ P + 680 <= EB)%Z.
  Hypothesis EBB : (EB + 256 <= B \/ B + pc_bufalloc p <= EB)%Z.

  #[local] Abbreviation AIREST_F := (ai_REST_F GIOA L).
  Hypothesis EBO : cobjA RNG m FL (C1 ++ C2) EB 256 \/ (P + 216 = EB)%Z.

  Hypothesis UTS : (0 < ng_user_tsresol s < 2^64)%Z.
  Hypothesis IFW : Forall if_wf (ng_ifaces s).
  Hypothesis P2 : (P mod 16 = 0)%Z.
  Hypothesis B2 : (B mod 16 = 0)%Z.
  Hypothesis IDB0 : (0 <= idb_off)%Z.
  Hypothesis IDB4 : (idb_off mod 4 = 0)%Z.
  Hypothesis COFF : (cur_off c = idb_off + 8)%Z.
  Hypothesis CREM : (0 <= cur_remaining c)%Z.
  Hypothesis CEND : (cur_off c + cur_remaining c <= Z.of_nat (length (pc_bufdata p)))%Z.
  Hypothesis CBT : (0 <= cur_block_type c < 2^32)%Z.
  Hypothesis CUR8 : (CUR mod 8 = 0)%Z.
  Hypothesis APB : (P + 680 <= B \/ B + pc_bufalloc p <= P)%Z.
  Hypothesis EBP2 : (EB + 256 <= P + 48 \/ P + 60 <= EB)%Z.
  Hypothesis HPV : rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)))].

  #[local] Abbreviation ai_snap := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_snap idb_off p).
  #[local] Abbreviation ai_slot0 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot0 idb_off p).
  #[local] Abbreviation ai_result := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c).
  Hypothesis PFX : firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p).
  Hypothesis GRD : Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p).

  (* [comment removed for export] *)
  Definition ai_common__stmt : Prop := forall (ra' t0' t1' t2' x8 a0' a3' a4' a5' a6' a7' x20 x23 x24 x25 x27 t3' t4' t5' t6' : word) (m2 : mem) (RNG3 : footprint) (stG : PS)
        (sg : pcap_ng_sf) (q1 : hptr) (I' : Z) (js : list if_junk) (pad1 junk1 j0 j1 j2 : list byte),
      ng_user_tsresol sg = ng_user_tsresol s -> ng_max_blocksize sg = ng_max_blocksize s -> ng_ifaces sg = ng_ifaces s ->
      (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z -> (ng_ifcount sg <= ng_ifaces_size sg)%Z -> (1 <= ng_ifaces_size sg < 2^26)%Z ->
      length js = length (ng_ifaces s) ->
      fp_le RNG RNG3 ->
      mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -128) -> AGP m2 ->
      rw_cells asegs m2 (bv_unsigned sp + -128) [CB 8 j0; CB 8 j1; CB 8 j2] -> FRAME m2 ->
      rw_cells asegs m2 B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      rw_cells asegs m2 CUR (cursor_cells B c cpad) ->
      rw_cells asegs m2 EB [CB 256 ej] ->
      rw_cells asegs m2 (P + 648) (ng_cells sg I' pad1) ->
      rw_cells asegs m2 I' (ifs_cells (rev (ng_ifaces s)) js) ->
      rw_cells asegs m2 (I' + 40 * (ng_ifcount sg - 1)) [CB (Z.to_nat (40 * (ng_ifaces_size sg - (ng_ifcount sg - 1)))) junk1] ->
      GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m2 -> ps_outfile stG = ps_outfile st ->
      evtF asegs RNG3 (POSTQ (ai_result sg (Some q1) (process_idb_options (pc_swapped p) c (pc_bufdata p))) stG RNG3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' x8 (Z_to_bv 64 (P + 648)) a0' (Z_to_bv 64 (B + idb_off)) (Z_to_bv 64 CUR) a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 660)) (Z_to_bv 64 P) x20 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880)) x23 x24 x25 (Z_to_bv 64 EB) x27
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8c2e4) fc None m2 (seg_rom asegs)).
  Section Sz1.
  Variables ra' t0' t1' t2' x8 a0' a3' a4' a5' a6' a7' x20 x23 x24 x25 x27 t3' t4' t5' t6' m2 RNG3 stG sg q1 I' js pad1 junk1 j0 j1 j2 : ltac2:(SecDiet.SzSec.tyM 'ai_common__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ai_common__body : ltac2:(SecDiet.SzSec.bodyP 'ai_common__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej cpad G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 IDB4 COFF CREM CEND CBT CUR8 APB EBP2 HPV PFX GRD ra' t0' t1' t2' x8 a0' a3' a4' a5' a6' a7' x20 x23 x24 x25 x27 t3' t4' t5' t6' m2 RNG3 stG sg q1 I' js pad1 junk1 j0 j1 j2.
 intros U1 U2 U5 IC1 IC2 SZ LJS FP3 MI2 ST2 AG2 HD2 FR2 BUF2 CC2 HEB2 NG2 AR1 JK G2 OFG.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    (* [comment removed for export] *)
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA.ai_head FO GIOA fflagA GL sp L C1 C2 FB FL P B EB lo p LO BU GPL HinP HinB EBL _ _ _ _ _ _ G2 ltac:(lia)) as ((Q1 & Q4 & Q2) & IUNP & IRNG & IRSH & (bI & bIr & bIhi & bIlo & bIimg) & API & APIB & APIE).
    assert (HinB3 : In (pc_buffer p, B, pc_bufalloc p) (((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinB).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 HinB3) as ((BBAND & B3x & BTOP & _) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in BBAND, B3x, BTOP, B1, BUNP, BRNG, BRSH.
    band_ind BBAND bB.
    assert (HinP3 : In (pc_self p, P, PCAP_NG_SF_TOTAL) (((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinP).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 HinP3) as ((PBAND & P3x & PTOP & _) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in PBAND, P3x, PTOP, P1, PUNP, PRNG, PRSH. unfold PCAP_NG_SF_TOTAL in PBAND, P3x, PTOP, P1, PUNP, PRNG, PRSH.
    band_ind PBAND bP.
    pose proof (rng_fp_le _ _ _ _ FP3 RSTK) as RSTK3.
    destruct (gia_stack_sobjA FO GIOA fflagA GL _ _ _ _ _ _ _ lo (bv_unsigned sp) CUR 24 G2 LO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RSTK3) as (_ & _ & CUNP & CRNG & CRSH).
    replace (CUR - CUR mod 8)%Z with CUR in CRSH by lia. replace (24 + CUR mod 8)%Z with 24%Z in CRSH by lia.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK3| lia]).
    pose proof (rw_cells_bound _ _ _ _ AR1) as BA1. rewrite ifs_cells_size in BA1 by (rewrite length_rev; lia). rewrite length_rev in BA1.
    remember (I' + 40 * (ng_ifcount sg - 1))%Z as SA eqn:HSA.
    (* [comment removed for export] *)
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.split_at4 (pc_bufdata p) (Z.to_nat (idb_off + 4)) ltac:(lia)) as (pre0 & x0 & x1 & x2 & x3 & post0 & Ebuf & Lpre0).
    assert (GX : (0 <= x0 < 256 /\ 0 <= x1 < 256 /\ 0 <= x2 < 256 /\ 0 <= x3 < 256)%Z).
    { pose proof GRD as GRD'. rewrite Ebuf in GRD'. apply Forall_app in GRD' as [_ GB].
      pose proof (Forall_inv GB) as X0. pose proof (Forall_inv (Forall_inv_tail GB)) as X1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GB))) as X2.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GB)))) as X3. cbv beta in X0, X1, X2, X3. lia. }
    destruct GX as (X0 & X1 & X2 & X3).
    assert (SNAP : ai_snap = le4val x0 x1 x2 x3).
    { unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_snap. rewrite Ebuf. replace (idb_off + 4)%Z with (Z.of_nat (length pre0)) by lia. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_ai.get_le32_at. }
    assert (SNR : (0 <= ai_snap < 2^32)%Z) by (rewrite SNAP; unfold le4val; lia).
    pose proof PFX as PFX0. rewrite Ebuf in PFX0.
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pfx_decomp pre0 [x0; x1; x2; x3] post0 bs PFX0) as (bsr0 & Ebs & _). cbn [map] in Ebs.
    pose proof BUF2 as BX. rewrite Ebs in BX.
    pose proof (rw_cells_recell _ _ _ [CB (length pre0) (map b8 pre0); C4 (Z_to_bv 64 (le4val x0 x1 x2 x3)); CB (length bsr0) bsr0] BX
                  ltac:(cbn; rewrite length_map; repeat split; reflexivity) ltac:(cbn [cells_bytes cbytes app]; rewrite le4_lit by lia; rewrite !app_nil_r; cbn [app]; reflexivity)) as BX'.
    destruct (rw_cells_cut _ _ _ 1 BX') as [_ BX2]. destruct (rw_cells_cut _ _ _ 1 BX2) as [HSN _]. clear BX BX' BX2. cbn [firstn skipn cells_size csize Nat.add app] in HSN.
    lazymatch type of HSN with rw_cells _ _ ?A _ => replace A with (B + idb_off + 4)%Z in HSN by lia end.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [4%nat; 36%nat; Z.to_nat (40 * (ng_ifaces_size sg - ng_ifcount sg))] JK ltac:(cbn; lia)) as JK'. clear JK.
    cbn [mk_CB_cells app] in JK'.
    unfold ai_FRAME in FR2. unfold ng_cells in NG2. unfold cursor_cells in CC2.
    hide FR2. hide BUF2. hide HEB2. hide AR1.
    pose proof (munch_refl [(SA, SA + 4); (bv_unsigned sp + -128, bv_unsigned sp + -104)]%Z m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep.
  ck_join BUNP 4%Z 0x8c2f8%Z [10%Z; 13%Z].
  zstep.
  ck0 PUNP; ck_go.
  zstep.
  rewrite (sx32_s32 (le4val x0 x1 x2 x3)) by (unfold le4val; lia).
  ck0_at PUNP (P + 660)%Z; ck_go.
  zstep.
  rewrite (sx32_small (ng_ifcount sg)) by lia.
  do 4 zstep.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32)%Z with 4294967296%Z.
  zstep.
  rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.mulhu40 (ng_ifcount sg + -1)) by lia.
  zstep. replace (I' + (ng_ifcount sg + -1) * 40)%Z with SA by lia.
  ck IUNP 4%Z 0x8c348%Z [14%Z; 15%Z].
  zstep.
  zstep.
  ck0 CUNP; ck_go.
  do 2 zstep.
  zstep.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  (* [comment removed for export] *)
  assert (AGS23 : agrees_on (fun a => outside [(SA, SA + 4); (bv_unsigned sp + -128, bv_unsigned sp + -104)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
  unhide FR2. unhide BUF2. unhide HEB2. unhide AR1.
  transport FR2 m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport BUF2 m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha APIB HSA IC1 IC2 SZ Q2 BTOP B1 B3x LO BU; lia).
  assert (EBL3 : clocA FL ((q1, I', (40 * ng_ifaces_size sg)%Z) :: C1 ++ C2) EB 256) by (eapply clocA_incl; [exact EBL | apply incl_tl, incl_refl | apply incl_refl]).
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G2 EBL3) as (EBLO & EBHI).
  transport HEB2 m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha APIE HSA IC1 IC2 SZ Q2 EBHI EBLO LO BU; lia).
  transport AR1 m3 AGS23 ltac:(intros a Ha; rewrite ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [outside fst snd]; lia).
  assert (G3 : GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m3).
  { eapply (gl_client_frame _ _ _ GL); [exact G2 | exact MU | exact WM |].
    apply Forall_cons; [right; left; unfold iv_in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia|].
    apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
  assert (AG3 : AGP m3).
  { eapply agrees_on_trans; [exact AG2|]. eapply agrees_on_weaken; [exact AGS23|]. intros a [[Ha|[Ha|[Ha|Ha]]] _]; cbn [outside fst snd].
    - split; [lia| split; [lia| exact Logic.I]].
    - split; [| split; [| exact Logic.I]].
      + destruct (proj1 (in_block_In _ _) Ha) as (b' & Hin & Hr).
        pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G2) as BA. cbn [app blocks_apart] in BA. destruct BA as [FA _].
        pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl Hin))) as AP. unfold apart in AP. cbn [cb_addr cb_size fst snd] in AP. lia.
      + pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G2 ltac:(apply in_block_app; left; apply Exists_cons_tl; exact Ha)). lia.
    - split; [| split; [| exact Logic.I]].
      + intros Hr. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G2 Ha). apply in_block_app. left. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
      + pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G2 Ha). lia.
    - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G2 Ha) as SBD. split; [lia| split; [lia| exact Logic.I]]. }
  (* [comment removed for export] *)
  destruct (rw_cells_cut _ _ _ 2 JK') as [SL AR2]. clear JK'. cbn [firstn skipn cells_size csize Nat.add app] in SL, AR2.
  lazymatch type of AR2 with rw_cells _ _ ?A _ => replace A with (SA + 40)%Z in AR2 by lia end.
  lazymatch type of SL with rw_cells _ _ _ [_; CB 36 ?sjx] =>
    pose proof (rw_cells_recell _ _ _ [C4 (Z_to_bv 64 ai_snap); CB 36 sjx] SL ltac:(pose proof (proj1 (proj1 SL)) as WF; cbn in WF |- *; clear - WF; tauto)
                  ltac:(cbn [cells_bytes cbytes app]; rewrite SNAP, le4_lit, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_ai.le4_s32_lit by lia; reflexivity)) as SL3 end.
  clear SL.
  unfold process_idb_options.
  destruct (Z.eq_dec (cur_remaining c) 0) as [R0|R0].
  - (* [comment removed for export] *)
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ R0). cbv iota.
    do 3 zstep.
    rewrite R0. change (Z.to_nat (0 / 4 + 1)) with 1%nat. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_unfold. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_iter. rewrite R0. cbn [Z.eqb]. cbv iota.
    eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA.ai_tail with (opts := mkIdbOpts 1000000 0 false false false) (hd := [CB 8 j0; CB 8 j1; CB 8 j2]) (SA := SA) (js := js);
      eassumption || (try exact IC1; try exact HSA; try reflexivity; try (cbn [io_tsresol]; lia); try lia).
  - (* [comment removed for export] *)
    rewrite (eqb_lits_false (cur_remaining c) 0) by lia. cbv iota.
    clear MU WM AGS23.
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp + -104)]%Z m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    hide FR2. hide BUF2. hide HEB2. hide AR1. hide AR2. hide SL3. hide NG2. hide CC2.
    do 20 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
    replace (Z.land (P + 56) 7) with 0%Z in HD2 by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3)%Z with 8%Z; clear - P2; Z.div_mod_to_equations; lia).
    change (0 + 3)%Z with 3%Z in HD2.
    assert (AGS34 : agrees_on (fun a => outside [(bv_unsigned sp + -128, bv_unsigned sp + -104)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    unhide FR2. unhide BUF2. unhide HEB2. unhide AR1. unhide AR2. unhide SL3. unhide NG2. unhide CC2.
    transport FR2 m4 AGS34 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport BUF2 m4 AGS34 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport HEB2 m4 AGS34 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport AR1 m4 AGS34 ltac:(intros a Ha; rewrite ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [outside fst snd]; lia).
    transport AR2 m4 AGS34 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport SL3 m4 AGS34 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport NG2 m4 AGS34 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport CC2 m4 AGS34 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    assert (G4 : GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m4).
    { eapply (gl_client_frame _ _ _ GL); [exact G3 | exact MU | exact WM |]. apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
    assert (AG4 : AGP m4).
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS34|]. intros a [[Ha|[Ha|[Ha|Ha]]] _]; cbn [outside fst snd]; (split; [| exact Logic.I]).
      - lia.
      - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G2 ltac:(apply in_block_app; left; apply Exists_cons_tl; exact Ha)). lia.
      - pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G2 Ha). lia.
      - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G2 Ha) as SBD. lia. }
    replace (Z.to_nat (cur_remaining c / 4 + 1)) with (S (Z.to_nat (cur_remaining c / 4))) by (clear - CREM; Z.div_mod_to_equations; lia).
    lazymatch type of SL3 with rw_cells _ _ _ [_; CB 36 ?sjx] => lazymatch type of AR2 with rw_cells _ _ _ [CB _ ?tlx] =>
      pose proof (ai_iter FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej
                    G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV RNG3
                    stG sg q1 I' SA js pad1 sjx tlx FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG (Z.to_nat (cur_remaining c / 4))
                    (ai_loop FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej
                       G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV RNG3
                       stG sg q1 I' SA js pad1 sjx tlx FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG (Z.to_nat (cur_remaining c / 4)))) as IT
    end end.
    red in IT. unfold LREGS in IT.
    eapply IT with (io := mkIdbOpts 1000000 0 false false false) (c' := c) (buf' := pc_bufdata p) (bs3 := bs) (cpad3 := cpad).
    + split; [cbn [io_tsresol]; lia|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact AG4|]. split; [exact HD2|]. split; [exact FR2|].
      split; [exact NG2|]. split; [exact AR1|]. split; [exact SL3|]. split; [exact AR2|]. split; [exact G4|]. split; [exact BUF2|]. split; [exact PFX|].
      split; [reflexivity|]. split; [exact GRD|]. split; [exact CC2|]. split; [exact CREM|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [exact HEB2|].
      rewrite COFF. clear - IDB4. Z.div_mod_to_equations. lia.
    + clear - CREM. Z.div_mod_to_equations. lia.
    + lia.
  Qed.
  End Sz1.
  #[using="rc tlsI FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 IDB4 COFF CREM CEND CBT CUR8 APB EBP2 HPV PFX GRD"] Lemma ai_common : ltac:(let t := eval cbv delta [ai_common__stmt] in ai_common__stmt in exact t).
  Proof. intros ra' t0' t1' t2' x8 a0' a3' a4' a5' a6' a7' x20 x23 x24 x25 x27 t3' t4' t5' t6' m2 RNG3 stG sg q1 I' js pad1 junk1 j0 j1 j2. ltac2:(SecDiet.SzSec.closeP 'ai_common__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End AIX.
  End CANSEC1.
End F_aiKA.

(* [comment removed for export] *)
Module F_aiMA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_aiBA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiBA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiBA__A3P.F_aiEA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_aiKA__A3P.F_aiKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ck_branch :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif (match c with context [?x] => is_var x end) then first [ if_false | if_true ]
      else (let v := eval vm_compute in c in
            lazymatch v with true => first [ if_true | if_false ] | false => first [ if_false | if_true ] | _ => first [ if_false | if_true ] end)
  | _ => first [ if_false | if_true ]
  end.
Local Ltac ck_go ::= ck_steps 8%nat; ck_branch.
(* [comment removed for export] *)
Local Ltac ck_sh_small A1 A2 := first [ clear - A1 A2; sh_lia | sh_lia ].
Local Ltac ck0_at UNP P ::=
  ck_clear;
  lazymatch goal with
  | |- evtF _ ?RNG _ (MS _ _ _ _ _ ?m _) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
        let RD := fresh "RDsh" in let A1 := fresh "CKlo" in let A2 := fresh "CKhi" in
        assert (A1 : (lo <= P)%Z) by ck_lia;
        assert (A2 : (8 * (P / 8) + 8 <= hi)%Z) by ck_lia;
        pose proof (ck_full_rd m lo hi P UNP A1 A2) as RD;
        first [ let ACC := fresh "ACCsh" in
                match goal with
                | H : rng RNG (shad lo) ?len |- _ => pose proof (ck_acc RNG (shad lo) len P H ltac:(ck_sh_small A1 A2) ltac:(ck_sh_small A1 A2)) as ACC
                end
              | clear A1 A2; ck_fp_at lo P ];
        try clear A1 A2
    | unpoisoned ?m' _ _ => fail "ck0: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.
Ltac fmt_at_tac MI ADDR str :=
  split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs _ ADDR (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string str) ++ [Z_to_bv 8 0])
                   MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
  split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]).

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section AIThm.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : ~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI)%Z.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  Definition add_interface_proofA__stmt : Prop := add_interface_stmt HO FO sites GIOA TP.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG st C1 C2 FB FL trC P B I CUR EB lo idb_off p s i c bs ej pad cpad : ltac2:(SecDiet.SzSec.tyM 'add_interface_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma add_interface_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'add_interface_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr HO FO sites GIOA TP fflagA GL GPL MALLOC REALLOC RPC SNPRINTF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG st C1 C2 FB FL trC P B I CUR EB lo idb_off p s i c bs ej pad cpad.
 intros PRE UC TR NF HS HinP HinB APB -> -> -> -> HPV HNG HIF UTS WMB HBUF PFX LENB GRD HCUR CURS CUR8 IDB0 IDB4 COFF CREM CEND CBT HEB EBD.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    unfold ADD_INTERFACE_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
  (* [comment removed for export] *)
  assert (HinP' : In (pc_self p, P, PCAP_NG_SF_TOTAL) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
  { apply in_or_app. left. apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
  assert (HinB' : In (pc_buffer p, B, pc_bufalloc p) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
  { apply in_or_app. left. apply in_app_iff in HinB as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
  pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP') as ((PBAND & P3x & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
  pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinB') as ((BBAND & B3x & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
  cbn [cb_addr cb_size fst snd] in PBAND, P3x, PTOP, P2, P1, PUNP, PRNG, PRSH, BBAND, B3x, BTOP, B2, B1, BUNP, BRNG, BRSH.
  unfold PCAP_NG_SF_TOTAL in PBAND, P3x, PTOP, P1, PUNP, PRNG, PRSH, APB.
  assert (P14 : (0 < P /\ P + 680 <= ATOP)%Z) by (split; [exact P1| exact PTOP]).
  assert (B14 : (0 < B /\ B + pc_bufalloc p <= ATOP)%Z) by (split; [exact B1| exact BTOP]).
  band_ind PBAND bP.
  (* [comment removed for export] *)
  assert (EBF : clocA FL (C1 ++ C2) EB 256 /\ (EB + 256 <= P + 648 \/ P + 680 <= EB)%Z /\ (EB + 256 <= B \/ B + pc_bufalloc p <= EB)%Z /\ (EB + 256 <= P + 48 \/ P + 60 <= EB)%Z
                /\ (cobjA RNG m FL (C1 ++ C2) EB 256 \/ (P + 216 = EB)%Z)).
  { destruct EBD as [(OB & _ & EP & EBx)|EE].
    - unfold PCAP_NG_SF_TOTAL in EP. split; [exact (proj1 OB)|]. split; [lia|]. split; [exact EBx|]. split; [lia| left; exact OB].
    - split; [left; exists (pc_self p, P, PCAP_NG_SF_TOTAL); split; [exact HinP| cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia]|].
      split; [lia|]. split; [lia|]. split; [lia| right; exact EE]. }
  destruct EBF as (EBL & EBP & EBB & EBP2 & EBO). clear EBD.
  (* [comment removed for export] *)
  unfold ifaces_ok in HIF. rewrite HS in HIF.
  assert (IFC : (0 <= ng_ifcount s /\ ng_ifcount s <= ng_ifaces_size s /\ ng_ifaces_size s < 2^26 /\ ng_ifcount s = Z.of_nat (length (ng_ifaces s)))%Z /\ Forall if_wf (ng_ifaces s)).
  { destruct i as [q|]; [destruct HIF as (js & tail & LJS & AR0 & E1 & E2 & E3 & IFW0); split; [lia| exact IFW0]| destruct HIF as (-> & E0 & E1 & E2); rewrite E0, E1, E2; cbn; split; [lia| constructor]]. }
  destruct IFC as (IFC & IFW).
  (* [comment removed for export] *)
  unfold add_interface. unfold ng_of, ng_ifaces_ptr_of. rewrite HS.
  cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_realloc prims pc_bufdata pc_swapped set_ng set_priv].
  replace (u32 (ng_ifcount s + 1)) with (ng_ifcount s + 1)%Z by (unfold u32; symmetry; apply Z.mod_small; lia).
  replace (u32 (ng_ifaces_size s * 2) <? ng_ifaces_size s) with false by (unfold u32; rewrite Z.mod_small by lia; symmetry; apply Z.ltb_ge; lia).
  unfold ADD_INTERFACE_ENTRY.
  pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
  rng_sp_window RSTK sp RSPW.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold ng_cells in HNG. unfold cursor_cells in HCUR. unfold PCAP_PRIV_OFF in HPV, HNG.
  pose proof HPV as HPVm.
  hide HEB. hide HBUF. hide HCUR. hide HPVm.
  ienterG.
  unfold STDIO_STACK in BU. carve_frame 128%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 128 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB _ ?t] =>
    lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in pose (j := t); change t with j in FR; clearbody j end.
  do 14 zstep.
  do 6 zstep.
  ck0 PUNP; ck_go.
  do 2 zstep.
  ck0 PUNP; ck_go.
  zstep. rewrite (sx32_small (ng_ifcount s)) by lia.
  do 3 zstep.
  rewrite (bv_swrap32_small (ng_ifcount s + 1)) by lia.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mp end.
  assert (G0 : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL mp)
    by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]]).
  assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp - 128, bv_unsigned sp)]%Z a) m mp) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
  assert (ICL : incl (C1 ++ C2) (C1 ++ IBLK i I s ++ C2)) by (intros b Hb; apply in_app_iff in Hb as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]).
  assert (EBLg : clocA FL (C1 ++ IBLK i I s ++ C2) EB 256) by (eapply clocA_incl; [exact EBL | exact ICL | apply incl_refl]).
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G EBLg) as (EBLO & EBHI).
  assert (AGa : ai_AGP FL sp C1 C2 P B CUR EB p m mp).
  { eapply agrees_on_weaken; [exact AG0|]. intros a [[Ha|[Ha|[Ha|Ha]]] _]; cbn [outside fst snd]; (split; [| exact Logic.I]).
    - lia.
    - assert (Ha' : in_block ((C1 ++ IBLK i I s ++ C2) ++ FB) a) by (apply in_block_app; left; apply in_block_In; destruct (proj1 (in_block_In _ _) Ha) as (b' & Hin & Hr); exists b'; split; [apply ICL; exact Hin| exact Hr]).
      pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G Ha'). lia.
    - pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G Ha). lia.
    - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha) as SBD. lia. }
  unhide HEB. unhide HBUF. unhide HCUR.
  transport HEB mp AG0 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HBUF mp AG0 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HCUR mp AG0 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  clear MU WM.
  pose proof (munch_refl [(P + 660, P + 664)]%Z mp) as MU1. pose proof (wmono_refl asegs mp) as WM1.
  hide HEB. hide HBUF. hide HCUR. hide FR.
  zstep.
  zstep.
  ck0_at PUNP (P + 664)%Z; ck_go.
  zstep. rewrite (sx32_small (ng_ifaces_size s)) by lia.
  zstep.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (AGS1 : agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) mp m1) by (eapply agrees_on_of_munch; [exact MU1 | exact WM1 | intros a _ Ho; exact Ho]).
  assert (HinP'' : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ IBLK i I s ++ C2)) by (apply ICL; exact HinP).
  assert (G1 : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL m1).
  { eapply (gl_client_frame _ _ _ GL); [exact G0 | exact MU1 | exact WM1 |]. apply Forall_cons; [| apply Forall_nil]. right; left. unfold iv_in_block. apply Exists_exists.
    exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP'' |]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
  assert (AGa1 : ai_AGP FL sp C1 C2 P B CUR EB p m m1).
  { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_weaken; [exact AGS1|]. intros a (_ & Hn & _); cbn [outside fst snd]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. split; [lia| exact Logic.I]. }
  unhide HEB. unhide HBUF. unhide HCUR. unhide FR.
  transport HEB m1 AGS1 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HBUF m1 AGS1 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HCUR m1 AGS1 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport FR m1 AGS1 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  clear MU1 WM1.
  (* [comment removed for export] *)
  destruct (rw_cells_cut _ _ _ 3 FR) as [HD FRS]. clear FR. cbn [firstn skipn cells_size csize Nat.add] in HD, FRS.
  replace (bv_unsigned sp + -128 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FRS by lia.
  (* [comment removed for export] *)
  unhide HPVm.
  pose proof (ai_common FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej cpad
                G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 IDB4 COFF CREM CEND CBT CUR8 APB EBP2 HPVm PFX GRD) as KED0.
  (* [comment removed for export] *)
  assert (IBF : forall q, i = Some q -> (0 < I /\ I + 40 * ng_ifaces_size s <= ATOP /\ (P + 680 <= I \/ I + 40 * ng_ifaces_size s <= P) /\ (B + pc_bufalloc p <= I \/ I + 40 * ng_ifaces_size s <= B))%Z).
  { intros q ->. assert (HinI : In (q, I, (40 * ng_ifaces_size s)%Z) ((C1 ++ IBLK (Some q) I s ++ C2) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinI) as ((_ & _ & ITOP & _) & I1 & _). cbn [cb_addr cb_size fst snd] in ITOP, I1.
    assert (Gp : GIOA L RNG st ((q, I, (40 * ng_ifaces_size s)%Z) :: C1 ++ C2) FB FL m) by (eapply GPL; [exact G| cbn [IBLK app]; apply Permutation.Permutation_sym, Permutation.Permutation_middle]).
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ Gp) as BA. cbn [app blocks_apart] in BA. destruct BA as [FA _].
    pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl HinP))) as AP1. pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl HinB))) as AP2.
    unfold apart in AP1, AP2. cbn [cb_addr cb_size fst snd] in AP1, AP2. unfold PCAP_NG_SF_TOTAL in AP1. lia. }
  destruct (Z.lt_ge_cases (ng_ifaces_size s) (ng_ifcount s + 1)) as [GROW|NOGROW].
  2:{ (* [comment removed for export] *)
    replace (bv_ltu (Z_to_bv 64 (ng_ifaces_size s)) (Z_to_bv 64 (ng_ifcount s + 1))) with false by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [negb].
    rewrite (proj2 (Z.ltb_ge (ng_ifaces_size s) (ng_ifcount s + 1)) NOGROW).
    destruct i as [q|]; [| exfalso; destruct HIF as (_ & _ & E0 & E1); lia].
    destruct HIF as (js & tail & LJS & AR0 & E1 & E2 & E3 & IFW0). destruct (IBF q eq_refl) as (I1 & I4 & API & ABI).
    apply evtF_done.
    set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s) (ng_ifaces s)).
    lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s0' ?Q ?ms => change (implMG R (k a) s0' Q ms) end. cbv beta iota.
    lazymatch goal with |- implMG _ ?mdl _ _ _ =>
      replace mdl with (mret (St:=PS) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c SG (Some q) (process_idb_options (pc_swapped p) c (pc_bufdata p))))
        by (unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
            destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
    apply implMG_ret. subst POSTQ.
    (* [comment removed for export] *)
    apply (agrees_rw_cells _ _ _ _ _ AG0) in AR0; [| intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS1) in AR0; [| intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia].
    destruct (proj1 (rw_cells_app asegs m1 I _ _) AR0) as [AR1 JK]. clear AR0. rewrite ifs_cells_size in JK by (rewrite length_rev; lia). rewrite length_rev in JK.
    assert (G1p : GIOA L RNG st ((q, I, 40 * ng_ifaces_size s)%Z :: C1 ++ C2) FB FL m1) by (eapply GPL; [exact G1| cbn [IBLK app]; apply Permutation.Permutation_sym, Permutation.Permutation_middle]).
    eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 RNG st SG q I js pad tail jk jk0 jk1);
      [ reflexivity | reflexivity | reflexivity | cbn [SG ng_ifcount]; lia | cbn [SG ng_ifcount ng_ifaces_size]; lia | cbn [SG ng_ifaces_size]; lia | exact LJS | apply fp_le_refl
      | exact MI | exact ST | exact AGa1 | exact HD | exact FRS | exact HBUF | exact HCUR | exact HEB
      | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
      | exact AR1
      | cbn [SG ng_ifcount ng_ifaces_size]; replace (ng_ifcount s + 1 - 1)%Z with (ng_ifcount s) by lia;
        lazymatch type of JK with rw_cells _ _ ?A _ => replace (I + 40 * ng_ifcount s)%Z with A by lia end; exact JK
      | exact G1p | reflexivity ]. }
  (* [comment removed for export] *)
  replace (bv_ltu (Z_to_bv 64 (ng_ifaces_size s)) (Z_to_bv 64 (ng_ifcount s + 1))) with true by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [negb].
  rewrite (proj2 (Z.ltb_lt (ng_ifaces_size s) (ng_ifcount s + 1)) GROW).
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  zstep.
  destruct (Z.eq_dec (ng_ifaces_size s) 0) as [SZ0|SZ0].
  - (* [comment removed for export] *)
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ SZ0). cbv iota. rewrite (proj2 (Z.eqb_eq _ _) SZ0).
    destruct i as [q|]; [destruct HIF as (js & tail & LJS & AR0 & E1 & E2 & E3 & IFW0); exfalso; lia|]. destruct HIF as (I0 & IFN & IC0 & _).
    do 4 zstep.
    apply evtF_done.
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.implMG_bind_assoc.
    name_sp sp (-128)%Z.
    eapply implMG_bind.
    { eapply MALLOC with (L := L) (s := st) (CL := C1 ++ IBLK None I s ++ C2) (FB := FB) (FL := FL) (lo := lo) (n := 40%Z).
      - split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [exact LO|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
      - reflexivity.
      - lia.
      - eapply (unw_of_ucaller depth_add_interface) with (trC := []);
          [ eapply ucaller_data with (X := 0x8c2b0%Z);
              [ rewrite Hsp; rewrite unsigned_lit by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia); rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia
              | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold depth_add_interface; lia ]
          | unfold ACLIENT_LO, ACLIENT_HI, AMALLOC_PC; lia
          | rewrite Hsp; lia
          | rewrite unsigned_lit by lia; exact (proj1 TR)
          | exact RSTK ]. }
  intros r s2' RNG2 ms' PO. cbv beta in PO. destruct PO as (FP2 & av & m2 & E & OF2 & MI2 & ST2 & AG12 & PO).
  destruct r as [q'|]; [|destruct PO]. destruct PO as (A & junkA & -> & G2 & HBK).
  unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?X)] => replace (ret_pc (Z_to_bv 64 X)) with (Z_to_bv 64 X) by (symmetry; apply ret_pc_even; [lia|reflexivity]) end.
  cbn [IBLK app] in AG12, G2.
  (* [comment removed for export] *)
  assert (KST : forall A0 cs, rw_cells asegs m1 A0 cs -> (bv_unsigned sp + -128 <= A0)%Z -> rw_cells asegs m2 A0 cs)
    by (intros A0 cs HC HA; eapply agrees_rw_cells; [exact AG12| exact HC|]; intros a Ha; left; lia).
  assert (KPB : forall A0 cs (b : cblk), rw_cells asegs m1 A0 cs -> In b (C1 ++ C2) -> (cb_addr b <= A0)%Z -> (A0 + Z.of_nat (cells_size cs) <= cb_addr b + cb_size b)%Z -> rw_cells asegs m2 A0 cs)
    by (intros A0 cs b HC Hb H1 H3; eapply agrees_rw_cells; [exact AG12| exact HC|]; intros a Ha; right; left; apply in_block_In; exists b; split; [exact Hb| lia]).
  apply KST in HD; [|lia]. apply KST in FRS; [|lia]. apply KST in HCUR; [|lia].
  apply (KPB _ _ (pc_self p, P, PCAP_NG_SF_TOTAL)) in HPV; [| exact HinP | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia].
  apply (KPB _ _ (pc_self p, P, PCAP_NG_SF_TOTAL)) in HNG; [| exact HinP | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia].
  apply (KPB _ _ (pc_buffer p, B, pc_bufalloc p)) in HBUF; [| exact HinB | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; lia].
  apply (agrees_rw_cells _ _ _ _ _ AG12) in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact EBL| lia]].
  assert (AGa2 : ai_AGP FL sp C1 C2 P B CUR EB p m m2).
  { eapply agrees_on_trans; [exact AGa1|]. eapply agrees_on_weaken; [exact AG12|]. intros a (Hk & _).
    destruct Hk as [Ha|[Ha|[Ha|Ha]]]; [left; lia | right; left; exact Ha | right; right; left; exact Ha | right; right; right; exact Ha]. }
  clear KST KPB AG12.
  (* [comment removed for export] *)
  lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s0' ?Q ?ms => change (implMG R (k a) s0' Q ms) end. cbv beta iota.
  set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) 1 (ng_ifaces s)).
  lazymatch goal with |- implMG _ ?mdl _ _ _ =>
    replace mdl with (mret (St:=PS) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c SG (Some q') (process_idb_options (pc_swapped p) c (pc_bufdata p))))
      by (unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
          destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
  apply implMG_ret. subst POSTQ.
  clear PUNP PRNG PRSH BUNP BRNG BRSH.
  assert (HinP2 : In (pc_self p, P, PCAP_NG_SF_TOTAL) (((q', A, 40%Z) :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinP).
  pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 HinP2) as (_ & _ & PUNP & PRNG & PRSH & _).
  cbn [cb_addr cb_size fst snd] in PUNP, PRNG, PRSH. unfold PCAP_NG_SF_TOTAL in PUNP, PRNG, PRSH.
  pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 (or_introl eq_refl : In (q', A, 40%Z) (((q', A, 40%Z) :: C1 ++ C2) ++ FB))) as ((_ & _ & ATOPx & _) & A1 & _).
  cbn [cb_addr cb_size fst snd] in ATOPx, A1.
  pose proof (rng_fp_le _ _ _ _ FP2 RSPW) as RSPW2.
  pose proof (munch_refl [(P + 664, P + 668); (P + 672, P + 680)]%Z m2) as MU3. pose proof (wmono_refl asegs m2) as WM3.
  hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS. hide HPV. hide HBK.
  do 2 zstep. rewrite (eqb_lits_false A 0) by lia. cbv iota.
  ck0_at PUNP (P + 664)%Z; ck_go.
  do 2 zstep.
  ck0 PUNP; ck_go.
  do 3 zstep.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  assert (AGS23 : agrees_on (fun a => outside [(P + 664, P + 668); (P + 672, P + 680)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]).
  assert (G3 : GIOA L RNG2 s2' ((q', A, 40)%Z :: C1 ++ C2) FB FL m3).
  { eapply (gl_client_frame _ _ _ GL); [exact G2 | exact MU3 | exact WM3 |].
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; left; unfold iv_in_block; apply Exists_cons_tl; apply Exists_exists;
      exists (pc_self p, P, PCAP_NG_SF_TOTAL); (split; [exact HinP|]); cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia. }
  pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G2) as BA. cbn [app blocks_apart] in BA. destruct BA as [FA _].
  pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl HinP))) as APIP. unfold apart in APIP. cbn [cb_addr cb_size fst snd] in APIP. unfold PCAP_NG_SF_TOTAL in APIP.
  unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HBK.
  transport HD m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport FRS m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HBUF m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HCUR m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HEB m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HBK m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  assert (AGa3 : ai_AGP FL sp C1 C2 P B CUR EB p m m3).
  { eapply agrees_on_trans; [exact AGa2|]. eapply agrees_on_weaken; [exact AGS23|]. intros a (_ & Hn & _); cbn [outside fst snd]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. lia. }
  destruct (rw_cells_cut _ _ _ 0 HBK) as [AR1 _]. cbn [firstn] in AR1.
  replace (Z_to_bv 64 (ng_ifcount s)) with (Z_to_bv 64 (ng_ifcount SG - 1)) by (cbn [SG ng_ifcount]; f_equal; lia).
  eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 RNG2 s2' SG q' A [] pad junkA jk jk0 jk1);
    [ reflexivity | reflexivity | reflexivity | cbn [SG ng_ifcount]; rewrite IFN; cbn [length]; lia | cbn [SG ng_ifcount ng_ifaces_size]; lia | cbn [SG ng_ifaces_size]; lia | rewrite IFN; reflexivity | exact FP2
    | exact MI2 | exact ST2 | exact AGa3 | exact HD | exact FRS | exact HBUF | exact HCUR | exact HEB
    | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
    | rewrite IFN; cbn [rev ifs_cells]; exact AR1
    | cbn [SG ng_ifcount ng_ifaces_size]; replace (A + 40 * (ng_ifcount s + 1 - 1))%Z with A by lia; replace (Z.to_nat (40 * (1 - (ng_ifcount s + 1 - 1)))) with (Z.to_nat 40) by lia; exact HBK
    | exact G3 | exact OF2 ].
  - (* [comment removed for export] *)
    rewrite (eqb_lits_false (ng_ifaces_size s) 0) by lia. cbv iota. rewrite (proj2 (Z.eqb_neq _ _) SZ0). cbv iota.
    (* [comment removed for export] *)
    destruct (Z.lt_ge_cases (ng_ifcount s) (2 ^ 22)) as [IFC22|IFC22].
    2:{
        apply evtF_done.
        replace (ng_ifcount s <? 4194304) with false by (symmetry; apply Z.ltb_ge; exact IFC22). cbv beta iota delta [negb].
        lazymatch goal with |- implMG ?R _ ?s0' ?Q ?ms => change (implMG R (munr (A:=bool * cursor * pcapT * list Z)) s0' Q ms) end. apply implMG_unr. }
    replace (ng_ifcount s <? 4194304) with true by (symmetry; apply Z.ltb_lt; exact IFC22). cbv beta iota delta [negb].
    destruct i as [q|]; [| destruct HIF as (_ & _ & _ & E0); exfalso; lia].
    destruct HIF as (js & tail & LJS & AR0 & E1 & E2 & E3 & IFW0). destruct (IBF q eq_refl) as (I1 & I4 & API & ABI).
    assert (SZE : ng_ifaces_size s = ng_ifcount s) by lia.
    zstep.
    replace (bv_lts (Z_to_bv 64 (ng_ifaces_size s)) z64) with false by (symmetry; unfold bv_lts; rewrite signed_lit_small64 by lia; apply Z.ltb_ge; change (bv_signed z64) with 0%Z; lia). cbv iota.
    zstep.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
    zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32)%Z with 4294967296%Z.
    zstep. zstep.
    rewrite (Z.shiftr_div_pow2 (ng_ifaces_size s * 2 * 4294967296) 32) by lia. change (2 ^ 32)%Z with 4294967296%Z. rewrite Z.div_mul by lia.
    zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.mulhu40 (ng_ifaces_size s * 2)) by lia.
    zstep.
    replace (bv_ltu (Z_to_bv 64 (ng_ifaces_size s * 2 * 40)) (Z_to_bv 64 (ng_ifaces_size s * 2))) with false by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia).
    cbv beta iota delta [negb].
    (* [comment removed for export] *)
    apply (agrees_rw_cells _ _ _ _ _ AG0) in AR0; [| intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS1) in AR0; [| intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia].
    pose proof (proj1 (proj1 AR0)) as WFA. apply cells_wf_app in WFA as [WFI WFT]. cbn in WFT. destruct WFT as [LT _].
    assert (TL0 : tail = []) by (destruct tail; [reflexivity| cbn in LT; lia]). subst tail.
    assert (ARm : rw_cells asegs m1 I ([] ++ (ifs_cells (rev (ng_ifaces s)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) []]) ++ [])) by (cbn [app]; rewrite app_nil_r; exact AR0).
    apply rw_cells_merge in ARm. cbn [app] in ARm. rewrite cells_size_app, cells_bytes_app, ifs_cells_size in ARm by (rewrite length_rev; lia). rewrite length_rev in ARm.
    cbn [cells_size cells_bytes cbytes csize Nat.add app] in ARm. rewrite app_nil_r in ARm.
    replace (40 * length (ng_ifaces s) + (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s)) + 0))%nat with (Z.to_nat (40 * ng_ifaces_size s)) in ARm by lia.
    (* [comment removed for export] *)
    do 2 zstep.
    ck0 PUNP; ck_go.
    do 3 zstep.
    zstep.
    apply evtF_done.
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.implMG_bind_assoc.
    name_sp sp (-128)%Z.
    cbn [IBLK app] in G1.
    eapply implMG_bind.
    { eapply REALLOC with (L := L) (s := st) (C1 := C1) (C2 := C2) (FB := FB) (FL := FL) (q := q) (A := I) (sz := (40 * ng_ifaces_size s)%Z) (lo := lo) (n := (ng_ifaces_size s * 2 * 40)%Z).
      - split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [exact LO|].
        split; [rewrite Hsp; lazymatch goal with |- (lo + ?K <= _)%Z => let k := eval cbv in K in change K with k end; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
      - reflexivity.
      - reflexivity.
      - lia.
      - exact ARm.
      - eapply (unw_of_ucaller depth_add_interface) with (trC := []);
          [ eapply ucaller_data with (X := 0x8c7ec%Z);
              [ rewrite Hsp; rewrite unsigned_lit by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia); rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia
              | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold depth_add_interface; lia ]
          | exact RPC
          | rewrite Hsp; lia
          | rewrite unsigned_lit by lia; exact (proj2 TR)
          | exact RSTK ]. }
    intros r s2' RNG2 ms' PO. cbv beta in PO. destruct PO as (FP2 & av & m2 & E & OF2 & MI2 & ST2 & AG12 & PO).
    destruct r as [q'|]; [|destruct PO]. destruct PO as (A & junkA & -> & G2 & HBK).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?X)] => replace (ret_pc (Z_to_bv 64 X)) with (Z_to_bv 64 X) by (symmetry; apply ret_pc_even; [lia|reflexivity]) end.
    (* [comment removed for export] *)
    assert (KST : forall A0 cs, rw_cells asegs m1 A0 cs -> (bv_unsigned sp + -128 <= A0)%Z -> rw_cells asegs m2 A0 cs)
      by (intros A0 cs HC HA; eapply agrees_rw_cells; [exact AG12| exact HC|]; intros a Ha; left; lia).
    assert (KPB : forall A0 cs (b : cblk), rw_cells asegs m1 A0 cs -> In b (C1 ++ C2) -> (cb_addr b <= A0)%Z -> (A0 + Z.of_nat (cells_size cs) <= cb_addr b + cb_size b)%Z -> rw_cells asegs m2 A0 cs)
      by (intros A0 cs b HC Hb H1 H3; eapply agrees_rw_cells; [exact AG12| exact HC|]; intros a Ha; right; left; apply in_block_In; exists b; split; [exact Hb| lia]).
    apply KST in HD; [|lia]. apply KST in FRS; [|lia]. apply KST in HCUR; [|lia].
    apply (KPB _ _ (pc_self p, P, PCAP_NG_SF_TOTAL)) in HPV; [| exact HinP | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia].
    apply (KPB _ _ (pc_self p, P, PCAP_NG_SF_TOTAL)) in HNG; [| exact HinP | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia].
    apply (KPB _ _ (pc_buffer p, B, pc_bufalloc p)) in HBUF; [| exact HinB | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG12) in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact EBL| lia]].
    assert (AGa2 : ai_AGP FL sp C1 C2 P B CUR EB p m m2).
    { eapply agrees_on_trans; [exact AGa1|]. eapply agrees_on_weaken; [exact AG12|]. intros a (Hk & _).
      destruct Hk as [Ha|[Ha|[Ha|Ha]]]; [left; lia | right; left; exact Ha | right; right; left; exact Ha | right; right; right; exact Ha]. }
    clear KST KPB AG12 AR0 ARm.
    (* [comment removed for export] *)
    lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s0' ?Q ?ms => change (implMG R (k a) s0' Q ms) end. cbv beta iota.
    set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s * 2) (ng_ifaces s)).
    lazymatch goal with |- implMG _ ?mdl _ _ _ =>
      replace mdl with (mret (St:=PS) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c SG (Some q') (process_idb_options (pc_swapped p) c (pc_bufdata p))))
        by (unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
            destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
    apply implMG_ret. subst POSTQ.
    clear PUNP PRNG PRSH BUNP BRNG BRSH.
    assert (HinP2 : In (pc_self p, P, PCAP_NG_SF_TOTAL) (((q', A, (ng_ifaces_size s * 2 * 40)%Z) :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinP).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 HinP2) as (_ & _ & PUNP & PRNG & PRSH & _).
    cbn [cb_addr cb_size fst snd] in PUNP, PRNG, PRSH. unfold PCAP_NG_SF_TOTAL in PUNP, PRNG, PRSH.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 (or_introl eq_refl : In (q', A, (ng_ifaces_size s * 2 * 40)%Z) (((q', A, (ng_ifaces_size s * 2 * 40)%Z) :: C1 ++ C2) ++ FB))) as ((_ & _ & ATOPx & _) & A1 & _).
    cbn [cb_addr cb_size fst snd] in ATOPx, A1.
    pose proof (munch_refl [(P + 664, P + 668); (P + 672, P + 680)]%Z m2) as MU3. pose proof (wmono_refl asegs m2) as WM3.
    hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS. hide HPV. hide HBK.
    zstep. rewrite (eqb_lits_false A 0) by lia. cbv beta iota delta [negb].
    ck0_at PUNP (P + 664)%Z; ck_go.
    do 2 zstep.
    ck0 PUNP; ck_go.
    do 3 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    assert (AGS23 : agrees_on (fun a => outside [(P + 664, P + 668); (P + 672, P + 680)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]).
    assert (G3 : GIOA L RNG2 s2' ((q', A, ng_ifaces_size s * 2 * 40)%Z :: C1 ++ C2) FB FL m3).
    { eapply (gl_client_frame _ _ _ GL); [exact G2 | exact MU3 | exact WM3 |].
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; left; unfold iv_in_block; apply Exists_cons_tl; apply Exists_exists;
        exists (pc_self p, P, PCAP_NG_SF_TOTAL); (split; [exact HinP|]); cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia. }
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G2) as BA. cbn [app blocks_apart] in BA. destruct BA as [FA _].
    pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl HinP))) as APIP. unfold apart in APIP. cbn [cb_addr cb_size fst snd] in APIP. unfold PCAP_NG_SF_TOTAL in APIP.
    unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HBK.
    transport HD m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport FRS m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport HBUF m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha APB B3x; lia).
    transport HCUR m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport HEB m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha EBP; lia).
    rewrite !Z.min_l in HBK by lia.
    transport HBK m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha APIP E3; lia).
    assert (AGa3 : ai_AGP FL sp C1 C2 P B CUR EB p m m3).
    { eapply agrees_on_trans; [exact AGa2|]. eapply agrees_on_weaken; [exact AGS23|]. intros a (_ & Hn & _); cbn [outside fst snd]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. lia. }
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 1 HBK) as [AR1 JK]. cbn [firstn skipn cells_size csize Nat.add] in AR1, JK.
    pose proof (rw_cells_recell _ _ _ (ifs_cells (rev (ng_ifaces s)) js) AR1 WFI
                  ltac:(cbn [cells_bytes cbytes app]; rewrite app_nil_r; symmetry; apply firstn_all2; rewrite (cells_bytes_length _ WFI), ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as AR1'.
    replace (Z_to_bv 64 (ng_ifcount s)) with (Z_to_bv 64 (ng_ifcount SG - 1)) by (cbn [SG ng_ifcount]; f_equal; lia).
    eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 RNG2 s2' SG q' A js pad junkA jk jk0 jk1);
      [ reflexivity | reflexivity | reflexivity | cbn [SG ng_ifcount]; lia | cbn [SG ng_ifcount ng_ifaces_size]; lia | cbn [SG ng_ifaces_size]; lia | exact LJS | exact FP2
      | exact MI2 | exact ST2 | exact AGa3 | exact HD | exact FRS | exact HBUF | exact HCUR | exact HEB
      | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
      | exact AR1'
      | cbn [SG ng_ifcount ng_ifaces_size]; lazymatch type of JK with rw_cells _ _ ?AA [CB ?n _] => replace (A + 40 * (ng_ifcount s + 1 - 1))%Z with AA by lia; replace (Z.to_nat (40 * (ng_ifaces_size s * 2 - (ng_ifcount s + 1 - 1)))) with n by lia end; exact JK
      | replace (40 * ng_ifaces_size SG)%Z with (ng_ifaces_size s * 2 * 40)%Z by (cbn [SG ng_ifaces_size]; lia); exact G3 | exact OF2 ].
  Qed.
  End Sz1.
  #[using="fflagA GL GPL MALLOC REALLOC RPC SNPRINTF"] Theorem add_interface_proofA : ltac:(let t := eval cbv delta [add_interface_proofA__stmt] in add_interface_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG st C1 C2 FB FL trC P B I CUR EB lo idb_off p s i c bs ej pad cpad. ltac2:(SecDiet.SzSec.closeP 'add_interface_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AIThm.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB AiAuxB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiKA.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.AiAuxB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiKA. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ck_branch :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif (match c with context [?x] => is_var x end) then first [ if_false | if_true ]
      else (let v := eval vm_compute in c in
            lazymatch v with true => first [ if_true | if_false ] | false => first [ if_false | if_true ] | _ => first [ if_false | if_true ] end)
  | _ => first [ if_false | if_true ]
  end.
Local Ltac ck_go ::= ck_steps 8%nat; ck_branch.
(* [comment removed for export] *)
Local Ltac ck_sh_small A1 A2 := first [ clear - A1 A2; sh_lia | sh_lia ].
Local Ltac ck0_at UNP P ::=
  ck_clear;
  lazymatch goal with
  | |- evtF _ ?RNG _ (MS _ _ _ _ _ ?m _) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
        let RD := fresh "RDsh" in let A1 := fresh "CKlo" in let A2 := fresh "CKhi" in
        assert (A1 : (lo <= P)%Z) by ck_lia;
        assert (A2 : (8 * (P / 8) + 8 <= hi)%Z) by ck_lia;
        pose proof (ck_full_rd m lo hi P UNP A1 A2) as RD;
        first [ let ACC := fresh "ACCsh" in
                match goal with
                | H : rng RNG (shad lo) ?len |- _ => pose proof (ck_acc RNG (shad lo) len P H ltac:(ck_sh_small A1 A2) ltac:(ck_sh_small A1 A2)) as ACC
                end
              | clear A1 A2; ck_fp_at lo P ];
        try clear A1 A2
    | unpoisoned ?m' _ _ => fail "ck0: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)
Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.
Ltac fmt_at_tac MI ADDR str :=
  split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs _ ADDR (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string str) ++ [Z_to_bv 8 0])
                   MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
  split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]).

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section AIThm.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : ~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI)%Z.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  Definition add_interface_proofA__stmt : Prop := add_interface_stmt HO FO sites GIOA TP.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG st C1 C2 FB FL trC P B I CUR EB lo idb_off p s i c bs ej pad cpad : ltac2:(SecDiet.SzSec.tyM 'add_interface_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma add_interface_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'add_interface_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr HO FO sites GIOA TP fflagA GL GPL MALLOC REALLOC RPC SNPRINTF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG st C1 C2 FB FL trC P B I CUR EB lo idb_off p s i c bs ej pad cpad.
 intros PRE UC TR NF HS HinP HinB APB -> -> -> -> HPV HNG HIF UTS WMB HBUF PFX LENB GRD HCUR CURS CUR8 IDB0 IDB4 COFF CREM CEND CBT HEB EBD.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    unfold ADD_INTERFACE_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
  (* [comment removed for export] *)
  assert (HinP' : In (pc_self p, P, PCAP_NG_SF_TOTAL) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
  { apply in_or_app. left. apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
  assert (HinB' : In (pc_buffer p, B, pc_bufalloc p) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
  { apply in_or_app. left. apply in_app_iff in HinB as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
  pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP') as ((PBAND & P3x & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
  pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinB') as ((BBAND & B3x & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
  cbn [cb_addr cb_size fst snd] in PBAND, P3x, PTOP, P2, P1, PUNP, PRNG, PRSH, BBAND, B3x, BTOP, B2, B1, BUNP, BRNG, BRSH.
  unfold PCAP_NG_SF_TOTAL in PBAND, P3x, PTOP, P1, PUNP, PRNG, PRSH, APB.
  assert (P14 : (0 < P /\ P + 680 <= ATOP)%Z) by (split; [exact P1| exact PTOP]).
  assert (B14 : (0 < B /\ B + pc_bufalloc p <= ATOP)%Z) by (split; [exact B1| exact BTOP]).
  band_ind PBAND bP.
  (* [comment removed for export] *)
  assert (EBF : clocA FL (C1 ++ C2) EB 256 /\ (EB + 256 <= P + 648 \/ P + 680 <= EB)%Z /\ (EB + 256 <= B \/ B + pc_bufalloc p <= EB)%Z /\ (EB + 256 <= P + 48 \/ P + 60 <= EB)%Z
                /\ (cobjA RNG m FL (C1 ++ C2) EB 256 \/ (P + 216 = EB)%Z)).
  { destruct EBD as [(OB & _ & EP & EBx)|EE].
    - unfold PCAP_NG_SF_TOTAL in EP. split; [exact (proj1 OB)|]. split; [lia|]. split; [exact EBx|]. split; [lia| left; exact OB].
    - split; [left; exists (pc_self p, P, PCAP_NG_SF_TOTAL); split; [exact HinP| cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia]|].
      split; [lia|]. split; [lia|]. split; [lia| right; exact EE]. }
  destruct EBF as (EBL & EBP & EBB & EBP2 & EBO). clear EBD.
  (* [comment removed for export] *)
  unfold ifaces_ok in HIF. rewrite HS in HIF.
  assert (IFC : (0 <= ng_ifcount s /\ ng_ifcount s <= ng_ifaces_size s /\ ng_ifaces_size s < 2^26 /\ ng_ifcount s = Z.of_nat (length (ng_ifaces s)))%Z /\ Forall if_wf (ng_ifaces s)).
  { destruct i as [q|]; [destruct HIF as (js & tail & LJS & AR0 & E1 & E2 & E3 & IFW0); split; [lia| exact IFW0]| destruct HIF as (-> & E0 & E1 & E2); rewrite E0, E1, E2; cbn; split; [lia| constructor]]. }
  destruct IFC as (IFC & IFW).
  (* [comment removed for export] *)
  unfold add_interface. unfold ng_of, ng_ifaces_ptr_of. rewrite HS.
  cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_realloc prims pc_bufdata pc_swapped set_ng set_priv].
  replace (u32 (ng_ifcount s + 1)) with (ng_ifcount s + 1)%Z by (unfold u32; symmetry; apply Z.mod_small; lia).
  replace (u32 (ng_ifaces_size s * 2) <? ng_ifaces_size s) with false by (unfold u32; rewrite Z.mod_small by lia; symmetry; apply Z.ltb_ge; lia).
  unfold ADD_INTERFACE_ENTRY.
  pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
  rng_sp_window RSTK sp RSPW.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold ng_cells in HNG. unfold cursor_cells in HCUR. unfold PCAP_PRIV_OFF in HPV, HNG.
  pose proof HPV as HPVm.
  hide HEB. hide HBUF. hide HCUR. hide HPVm.
  ienterG.
  unfold STDIO_STACK in BU. carve_frame 144%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 144 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB _ ?t] =>
    lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in pose (j := t); change t with j in FR; clearbody j end.
  do 14 zstep.
  zstep. zstep. ub_al 7%Z ltac:(clear - P2; Z.div_mod_to_equations; lia). zstep. if_false.      (* [comment removed for export] *)
  do 5 zstep.
  ck0 PUNP; ck_go.
  zstep.
  ub_null.                                                                                   (* [comment removed for export] *)
  zstep. ub_al 7%Z ltac:(clear - P2; Z.div_mod_to_equations; lia). zstep. if_false.             (* [comment removed for export] *)
  zstep.
  ck0 PUNP; ck_go.
  zstep. rewrite (sx32_small (ng_ifcount s)) by lia.
  do 3 zstep.
  rewrite (bv_swrap32_small (ng_ifcount s + 1)) by lia.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mp end.
  assert (G0 : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL mp)
    by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]]).
  assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp - 144, bv_unsigned sp)]%Z a) m mp) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
  assert (ICL : incl (C1 ++ C2) (C1 ++ IBLK i I s ++ C2)) by (intros b Hb; apply in_app_iff in Hb as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]).
  assert (EBLg : clocA FL (C1 ++ IBLK i I s ++ C2) EB 256) by (eapply clocA_incl; [exact EBL | exact ICL | apply incl_refl]).
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G EBLg) as (EBLO & EBHI).
  assert (AGa : ai_AGP FL sp C1 C2 P B CUR EB p m mp).
  { eapply agrees_on_weaken; [exact AG0|]. intros a [[Ha|[Ha|[Ha|Ha]]] _]; cbn [outside fst snd]; (split; [| exact Logic.I]).
    - lia.
    - assert (Ha' : in_block ((C1 ++ IBLK i I s ++ C2) ++ FB) a) by (apply in_block_app; left; apply in_block_In; destruct (proj1 (in_block_In _ _) Ha) as (b' & Hin & Hr); exists b'; split; [apply ICL; exact Hin| exact Hr]).
      pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G Ha'). lia.
    - pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G Ha). lia.
    - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha) as SBD. lia. }
  unhide HEB. unhide HBUF. unhide HCUR.
  transport HEB mp AG0 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HBUF mp AG0 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HCUR mp AG0 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  clear MU WM.
  pose proof (munch_refl [(P + 660, P + 664)]%Z mp) as MU1. pose proof (wmono_refl asegs mp) as WM1.
  hide HEB. hide HBUF. hide HCUR. hide FR.
  zstep.
  zstep.
  ck0_at PUNP (P + 664)%Z; ck_go.
  zstep. rewrite (sx32_small (ng_ifaces_size s)) by lia.
  zstep.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (AGS1 : agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) mp m1) by (eapply agrees_on_of_munch; [exact MU1 | exact WM1 | intros a _ Ho; exact Ho]).
  assert (HinP'' : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ IBLK i I s ++ C2)) by (apply ICL; exact HinP).
  assert (G1 : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL m1).
  { eapply (gl_client_frame _ _ _ GL); [exact G0 | exact MU1 | exact WM1 |]. apply Forall_cons; [| apply Forall_nil]. right; left. unfold iv_in_block. apply Exists_exists.
    exists (pc_self p, P, PCAP_NG_SF_TOTAL). split; [exact HinP'' |]. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
  assert (AGa1 : ai_AGP FL sp C1 C2 P B CUR EB p m m1).
  { eapply agrees_on_trans; [exact AGa|]. eapply agrees_on_weaken; [exact AGS1|]. intros a (_ & Hn & _); cbn [outside fst snd]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. split; [lia| exact Logic.I]. }
  unhide HEB. unhide HBUF. unhide HCUR. unhide FR.
  transport HEB m1 AGS1 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HBUF m1 AGS1 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HCUR m1 AGS1 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport FR m1 AGS1 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  clear MU1 WM1.
  (* [comment removed for export] *)
  destruct (rw_cells_cut _ _ _ 5 FR) as [HD FRS]. clear FR. cbn [firstn skipn cells_size csize Nat.add] in HD, FRS.       (* [comment removed for export] *)
  replace (bv_unsigned sp + -144 + Z.of_nat 40)%Z with (bv_unsigned sp + -104)%Z in FRS by lia.
  (* [comment removed for export] *)
  unhide HPVm.
  pose proof (ai_common FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej cpad
                G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 IDB4 COFF CREM CEND CBT CUR8 APB EBP2 HPVm PFX GRD) as KED0.
  (* [comment removed for export] *)
  assert (IBF : forall q, i = Some q -> (0 < I /\ I + 40 * ng_ifaces_size s <= ATOP /\ (P + 680 <= I \/ I + 40 * ng_ifaces_size s <= P) /\ (B + pc_bufalloc p <= I \/ I + 40 * ng_ifaces_size s <= B))%Z).
  { intros q ->. assert (HinI : In (q, I, (40 * ng_ifaces_size s)%Z) ((C1 ++ IBLK (Some q) I s ++ C2) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinI) as ((_ & _ & ITOP & _) & I1 & _). cbn [cb_addr cb_size fst snd] in ITOP, I1.
    assert (Gp : GIOA L RNG st ((q, I, (40 * ng_ifaces_size s)%Z) :: C1 ++ C2) FB FL m) by (eapply GPL; [exact G| cbn [IBLK app]; apply Permutation.Permutation_sym, Permutation.Permutation_middle]).
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ Gp) as BA. cbn [app blocks_apart] in BA. destruct BA as [FA _].
    pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl HinP))) as AP1. pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl HinB))) as AP2.
    unfold apart in AP1, AP2. cbn [cb_addr cb_size fst snd] in AP1, AP2. unfold PCAP_NG_SF_TOTAL in AP1. lia. }
  destruct (Z.lt_ge_cases (ng_ifaces_size s) (ng_ifcount s + 1)) as [GROW|NOGROW].
  2:{ (* [comment removed for export] *)
    replace (bv_ltu (Z_to_bv 64 (ng_ifaces_size s)) (Z_to_bv 64 (ng_ifcount s + 1))) with false by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [negb].
    rewrite (proj2 (Z.ltb_ge (ng_ifaces_size s) (ng_ifcount s + 1)) NOGROW).
    destruct i as [q|]; [| exfalso; destruct HIF as (_ & _ & E0 & E1); lia].
    destruct HIF as (js & tail & LJS & AR0 & E1 & E2 & E3 & IFW0). destruct (IBF q eq_refl) as (I1 & I4 & API & ABI).
    apply evtF_done.
    set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s) (ng_ifaces s)).
    lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s0' ?Q ?ms => change (implMG R (k a) s0' Q ms) end. cbv beta iota.
    lazymatch goal with |- implMG _ ?mdl _ _ _ =>
      replace mdl with (mret (St:=PS) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c SG (Some q) (process_idb_options (pc_swapped p) c (pc_bufdata p))))
        by (unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
            destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
    apply implMG_ret. subst POSTQ.
    (* [comment removed for export] *)
    apply (agrees_rw_cells _ _ _ _ _ AG0) in AR0; [| intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS1) in AR0; [| intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia].
    destruct (proj1 (rw_cells_app asegs m1 I _ _) AR0) as [AR1 JK]. clear AR0. rewrite ifs_cells_size in JK by (rewrite length_rev; lia). rewrite length_rev in JK.
    assert (G1p : GIOA L RNG st ((q, I, 40 * ng_ifaces_size s)%Z :: C1 ++ C2) FB FL m1) by (eapply GPL; [exact G1| cbn [IBLK app]; apply Permutation.Permutation_sym, Permutation.Permutation_middle]).
    eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 RNG st SG q I js pad tail jk jk0 jk1 jk2 jk3);
      [ reflexivity | reflexivity | reflexivity | cbn [SG ng_ifcount]; lia | cbn [SG ng_ifcount ng_ifaces_size]; lia | cbn [SG ng_ifaces_size]; lia | exact LJS | apply fp_le_refl
      | exact MI | exact ST | exact AGa1 | exact HD | exact FRS | exact HBUF | exact HCUR | exact HEB
      | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
      | exact AR1
      | cbn [SG ng_ifcount ng_ifaces_size]; replace (ng_ifcount s + 1 - 1)%Z with (ng_ifcount s) by lia;
        lazymatch type of JK with rw_cells _ _ ?A _ => replace (I + 40 * ng_ifcount s)%Z with A by lia end; exact JK
      | exact G1p | reflexivity ]. }
  (* [comment removed for export] *)
  replace (bv_ltu (Z_to_bv 64 (ng_ifaces_size s)) (Z_to_bv 64 (ng_ifcount s + 1))) with true by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [negb].
  rewrite (proj2 (Z.ltb_lt (ng_ifaces_size s) (ng_ifcount s + 1)) GROW).
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  zstep.
  destruct (Z.eq_dec (ng_ifaces_size s) 0) as [SZ0|SZ0].
  - (* [comment removed for export] *)
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ SZ0). cbv iota. rewrite (proj2 (Z.eqb_eq _ _) SZ0).
    destruct i as [q|]; [destruct HIF as (js & tail & LJS & AR0 & E1 & E2 & E3 & IFW0); exfalso; lia|]. destruct HIF as (I0 & IFN & IC0 & _).
    do 4 zstep.
    apply evtF_done.
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB.implMG_bind_assoc.
    name_sp sp (-144)%Z.
    eapply implMG_bind.
    { eapply MALLOC with (L := L) (s := st) (CL := C1 ++ IBLK None I s ++ C2) (FB := FB) (FL := FL) (lo := lo) (n := 40%Z).
      - split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [exact LO|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
      - reflexivity.
      - lia.
      - eapply (unw_of_ucaller depth_add_interface) with (trC := []);
          [ eapply ucaller_data with (X := 0x8c3d4%Z);
              [ rewrite Hsp; rewrite unsigned_lit by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia); rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia
              | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold depth_add_interface; lia ]
          | unfold ACLIENT_LO, ACLIENT_HI, AMALLOC_PC; lia
          | rewrite Hsp; lia
          | rewrite unsigned_lit by lia; exact (proj1 TR)
          | exact RSTK ]. }
  intros r s2' RNG2 ms' PO. cbv beta in PO. destruct PO as (FP2 & av & m2 & E & OF2 & MI2 & ST2 & AG12 & PO).
  destruct r as [q'|]; [|destruct PO]. destruct PO as (A & junkA & -> & G2 & HBK).
  unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?X)] => replace (ret_pc (Z_to_bv 64 X)) with (Z_to_bv 64 X) by (symmetry; apply ret_pc_even; [lia|reflexivity]) end.
  cbn [IBLK app] in AG12, G2.
  (* [comment removed for export] *)
  assert (KST : forall A0 cs, rw_cells asegs m1 A0 cs -> (bv_unsigned sp + -144 <= A0)%Z -> rw_cells asegs m2 A0 cs)
    by (intros A0 cs HC HA; eapply agrees_rw_cells; [exact AG12| exact HC|]; intros a Ha; left; lia).
  assert (KPB : forall A0 cs (b : cblk), rw_cells asegs m1 A0 cs -> In b (C1 ++ C2) -> (cb_addr b <= A0)%Z -> (A0 + Z.of_nat (cells_size cs) <= cb_addr b + cb_size b)%Z -> rw_cells asegs m2 A0 cs)
    by (intros A0 cs b HC Hb H1 H3; eapply agrees_rw_cells; [exact AG12| exact HC|]; intros a Ha; right; left; apply in_block_In; exists b; split; [exact Hb| lia]).
  apply KST in HD; [|lia]. apply KST in FRS; [|lia]. apply KST in HCUR; [|lia].
  apply (KPB _ _ (pc_self p, P, PCAP_NG_SF_TOTAL)) in HPV; [| exact HinP | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia].
  apply (KPB _ _ (pc_self p, P, PCAP_NG_SF_TOTAL)) in HNG; [| exact HinP | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia].
  apply (KPB _ _ (pc_buffer p, B, pc_bufalloc p)) in HBUF; [| exact HinB | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; lia].
  apply (agrees_rw_cells _ _ _ _ _ AG12) in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact EBL| lia]].
  assert (AGa2 : ai_AGP FL sp C1 C2 P B CUR EB p m m2).
  { eapply agrees_on_trans; [exact AGa1|]. eapply agrees_on_weaken; [exact AG12|]. intros a (Hk & _).
    destruct Hk as [Ha|[Ha|[Ha|Ha]]]; [left; lia | right; left; exact Ha | right; right; left; exact Ha | right; right; right; exact Ha]. }
  clear KST KPB AG12.
  (* [comment removed for export] *)
  lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s0' ?Q ?ms => change (implMG R (k a) s0' Q ms) end. cbv beta iota.
  set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) 1 (ng_ifaces s)).
  lazymatch goal with |- implMG _ ?mdl _ _ _ =>
    replace mdl with (mret (St:=PS) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c SG (Some q') (process_idb_options (pc_swapped p) c (pc_bufdata p))))
      by (unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
          destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
  apply implMG_ret. subst POSTQ.
  clear PUNP PRNG PRSH BUNP BRNG BRSH.
  assert (HinP2 : In (pc_self p, P, PCAP_NG_SF_TOTAL) (((q', A, 40%Z) :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinP).
  pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 HinP2) as (_ & _ & PUNP & PRNG & PRSH & _).
  cbn [cb_addr cb_size fst snd] in PUNP, PRNG, PRSH. unfold PCAP_NG_SF_TOTAL in PUNP, PRNG, PRSH.
  pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 (or_introl eq_refl : In (q', A, 40%Z) (((q', A, 40%Z) :: C1 ++ C2) ++ FB))) as ((_ & _ & ATOPx & _) & A1 & _).
  cbn [cb_addr cb_size fst snd] in ATOPx, A1.
  pose proof (rng_fp_le _ _ _ _ FP2 RSPW) as RSPW2.
  pose proof (munch_refl [(P + 664, P + 668); (P + 672, P + 680)]%Z m2) as MU3. pose proof (wmono_refl asegs m2) as WM3.
  hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS. hide HPV. hide HBK.
  do 2 zstep. rewrite (eqb_lits_false A 0) by lia. cbv iota.
  ck0_at PUNP (P + 664)%Z; ck_go.
  do 2 zstep.
  ck0 PUNP; ck_go.
  do 3 zstep.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  assert (AGS23 : agrees_on (fun a => outside [(P + 664, P + 668); (P + 672, P + 680)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]).
  assert (G3 : GIOA L RNG2 s2' ((q', A, 40)%Z :: C1 ++ C2) FB FL m3).
  { eapply (gl_client_frame _ _ _ GL); [exact G2 | exact MU3 | exact WM3 |].
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; left; unfold iv_in_block; apply Exists_cons_tl; apply Exists_exists;
      exists (pc_self p, P, PCAP_NG_SF_TOTAL); (split; [exact HinP|]); cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia. }
  pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G2) as BA. cbn [app blocks_apart] in BA. destruct BA as [FA _].
  pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl HinP))) as APIP. unfold apart in APIP. cbn [cb_addr cb_size fst snd] in APIP. unfold PCAP_NG_SF_TOTAL in APIP.
  unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HBK.
  transport HD m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport FRS m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HBUF m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HCUR m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HEB m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport HBK m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  assert (AGa3 : ai_AGP FL sp C1 C2 P B CUR EB p m m3).
  { eapply agrees_on_trans; [exact AGa2|]. eapply agrees_on_weaken; [exact AGS23|]. intros a (_ & Hn & _); cbn [outside fst snd]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. lia. }
  destruct (rw_cells_cut _ _ _ 0 HBK) as [AR1 _]. cbn [firstn] in AR1.
  replace (Z_to_bv 64 (ng_ifcount s)) with (Z_to_bv 64 (ng_ifcount SG - 1)) by (cbn [SG ng_ifcount]; f_equal; lia).
  eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 RNG2 s2' SG q' A [] pad junkA jk jk0 jk1 jk2 jk3);
    [ reflexivity | reflexivity | reflexivity | cbn [SG ng_ifcount]; rewrite IFN; cbn [length]; lia | cbn [SG ng_ifcount ng_ifaces_size]; lia | cbn [SG ng_ifaces_size]; lia | rewrite IFN; reflexivity | exact FP2
    | exact MI2 | exact ST2 | exact AGa3 | exact HD | exact FRS | exact HBUF | exact HCUR | exact HEB
    | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
    | rewrite IFN; cbn [rev ifs_cells]; exact AR1
    | cbn [SG ng_ifcount ng_ifaces_size]; replace (A + 40 * (ng_ifcount s + 1 - 1))%Z with A by lia; replace (Z.to_nat (40 * (1 - (ng_ifcount s + 1 - 1)))) with (Z.to_nat 40) by lia; exact HBK
    | exact G3 | exact OF2 ].
  - (* [comment removed for export] *)
    rewrite (eqb_lits_false (ng_ifaces_size s) 0) by lia. cbv iota. rewrite (proj2 (Z.eqb_neq _ _) SZ0). cbv iota.
    (* [comment removed for export] *)
    destruct (Z.lt_ge_cases (ng_ifcount s) (2 ^ 22)) as [IFC22|IFC22].
    2:{
        apply evtF_done.
        replace (ng_ifcount s <? 4194304) with false by (symmetry; apply Z.ltb_ge; exact IFC22). cbv beta iota delta [negb].
        lazymatch goal with |- implMG ?R _ ?s0' ?Q ?ms => change (implMG R (munr (A:=bool * cursor * pcapT * list Z)) s0' Q ms) end. apply implMG_unr. }
    replace (ng_ifcount s <? 4194304) with true by (symmetry; apply Z.ltb_lt; exact IFC22). cbv beta iota delta [negb].
    destruct i as [q|]; [| destruct HIF as (_ & _ & _ & E0); exfalso; lia].
    destruct HIF as (js & tail & LJS & AR0 & E1 & E2 & E3 & IFW0). destruct (IBF q eq_refl) as (I1 & I4 & API & ABI).
    assert (SZE : ng_ifaces_size s = ng_ifcount s) by lia.
    zstep.
    replace (bv_lts (Z_to_bv 64 (ng_ifaces_size s)) z64) with false by (symmetry; unfold bv_lts; rewrite signed_lit_small64 by lia; apply Z.ltb_ge; change (bv_signed z64) with 0%Z; lia). cbv iota.
    zstep.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
    zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32)%Z with 4294967296%Z.
    zstep. zstep.
    rewrite (Z.shiftr_div_pow2 (ng_ifaces_size s * 2 * 4294967296) 32) by lia. change (2 ^ 32)%Z with 4294967296%Z. rewrite Z.div_mul by lia.
    zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.mulhu40 (ng_ifaces_size s * 2)) by lia.
    zstep.
    replace (bv_ltu (Z_to_bv 64 (ng_ifaces_size s * 2 * 40)) (Z_to_bv 64 (ng_ifaces_size s * 2))) with false by (unfold bv_ltu; rewrite !unsigned_lit by lia; symmetry; apply Z.ltb_ge; lia).
    cbv beta iota delta [negb].
    (* [comment removed for export] *)
    apply (agrees_rw_cells _ _ _ _ _ AG0) in AR0; [| intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS1) in AR0; [| intros a Ha; rewrite cells_size_app, ifs_cells_size in Ha by (rewrite length_rev; lia); rewrite length_rev in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia].
    pose proof (proj1 (proj1 AR0)) as WFA. apply cells_wf_app in WFA as [WFI WFT]. cbn in WFT. destruct WFT as [LT _].
    assert (TL0 : tail = []) by (destruct tail; [reflexivity| cbn in LT; lia]). subst tail.
    assert (ARm : rw_cells asegs m1 I ([] ++ (ifs_cells (rev (ng_ifaces s)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) []]) ++ [])) by (cbn [app]; rewrite app_nil_r; exact AR0).
    apply rw_cells_merge in ARm. cbn [app] in ARm. rewrite cells_size_app, cells_bytes_app, ifs_cells_size in ARm by (rewrite length_rev; lia). rewrite length_rev in ARm.
    cbn [cells_size cells_bytes cbytes csize Nat.add app] in ARm. rewrite app_nil_r in ARm.
    replace (40 * length (ng_ifaces s) + (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s)) + 0))%nat with (Z.to_nat (40 * ng_ifaces_size s)) in ARm by lia.
    (* [comment removed for export] *)
    do 2 zstep.
    ck0 PUNP; ck_go.
    do 3 zstep.
    zstep.
    apply evtF_done.
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB.implMG_bind_assoc.
    name_sp sp (-144)%Z.
    cbn [IBLK app] in G1.
    eapply implMG_bind.
    { eapply REALLOC with (L := L) (s := st) (C1 := C1) (C2 := C2) (FB := FB) (FL := FL) (q := q) (A := I) (sz := (40 * ng_ifaces_size s)%Z) (lo := lo) (n := (ng_ifaces_size s * 2 * 40)%Z).
      - split; [exact G1|]. split; [rewrite Hsp; exact ST|]. split; [exact LO|].
        split; [rewrite Hsp; lazymatch goal with |- (lo + ?K <= _)%Z => let k := eval cbv in K in change K with k end; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS].
      - reflexivity.
      - reflexivity.
      - lia.
      - exact ARm.
      - eapply (unw_of_ucaller depth_add_interface) with (trC := []);
          [ eapply ucaller_data with (X := 0x8c970%Z);
              [ rewrite Hsp; rewrite unsigned_lit by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia); rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia
              | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold depth_add_interface; lia ]
          | exact RPC
          | rewrite Hsp; lia
          | rewrite unsigned_lit by lia; exact (proj2 TR)
          | exact RSTK ]. }
    intros r s2' RNG2 ms' PO. cbv beta in PO. destruct PO as (FP2 & av & m2 & E & OF2 & MI2 & ST2 & AG12 & PO).
    destruct r as [q'|]; [|destruct PO]. destruct PO as (A & junkA & -> & G2 & HBK).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?X)] => replace (ret_pc (Z_to_bv 64 X)) with (Z_to_bv 64 X) by (symmetry; apply ret_pc_even; [lia|reflexivity]) end.
    (* [comment removed for export] *)
    assert (KST : forall A0 cs, rw_cells asegs m1 A0 cs -> (bv_unsigned sp + -144 <= A0)%Z -> rw_cells asegs m2 A0 cs)
      by (intros A0 cs HC HA; eapply agrees_rw_cells; [exact AG12| exact HC|]; intros a Ha; left; lia).
    assert (KPB : forall A0 cs (b : cblk), rw_cells asegs m1 A0 cs -> In b (C1 ++ C2) -> (cb_addr b <= A0)%Z -> (A0 + Z.of_nat (cells_size cs) <= cb_addr b + cb_size b)%Z -> rw_cells asegs m2 A0 cs)
      by (intros A0 cs b HC Hb H1 H3; eapply agrees_rw_cells; [exact AG12| exact HC|]; intros a Ha; right; left; apply in_block_In; exists b; split; [exact Hb| lia]).
    apply KST in HD; [|lia]. apply KST in FRS; [|lia]. apply KST in HCUR; [|lia].
    apply (KPB _ _ (pc_self p, P, PCAP_NG_SF_TOTAL)) in HPV; [| exact HinP | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia].
    apply (KPB _ _ (pc_self p, P, PCAP_NG_SF_TOTAL)) in HNG; [| exact HinP | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia].
    apply (KPB _ _ (pc_buffer p, B, pc_bufalloc p)) in HBUF; [| exact HinB | cbn [cb_addr fst snd]; lia | cbn [cells_size csize Nat.add cb_addr cb_size fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG12) in HEB; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; eapply clocA_keeps; [exact EBL| lia]].
    assert (AGa2 : ai_AGP FL sp C1 C2 P B CUR EB p m m2).
    { eapply agrees_on_trans; [exact AGa1|]. eapply agrees_on_weaken; [exact AG12|]. intros a (Hk & _).
      destruct Hk as [Ha|[Ha|[Ha|Ha]]]; [left; lia | right; left; exact Ha | right; right; left; exact Ha | right; right; right; exact Ha]. }
    clear KST KPB AG12 AR0 ARm.
    (* [comment removed for export] *)
    lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s0' ?Q ?ms => change (implMG R (k a) s0' Q ms) end. cbv beta iota.
    set (SG := mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s * 2) (ng_ifaces s)).
    lazymatch goal with |- implMG _ ?mdl _ _ _ =>
      replace mdl with (mret (St:=PS) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result idb_off p s c SG (Some q') (process_idb_options (pc_swapped p) c (pc_bufdata p))))
        by (unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_result, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_slot, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiB.ai_scale; subst SG; destruct (process_idb_options _ _ _) as [bb [mm|[oo cc]]]; [reflexivity|]; cbn;
            destruct (io_tsresol oo =? ng_user_tsresol s); [reflexivity|]; destruct (ng_user_tsresol s <? io_tsresol oo); destruct (io_is_binary oo); reflexivity) end.
    apply implMG_ret. subst POSTQ.
    clear PUNP PRNG PRSH BUNP BRNG BRSH.
    assert (HinP2 : In (pc_self p, P, PCAP_NG_SF_TOTAL) (((q', A, (ng_ifaces_size s * 2 * 40)%Z) :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinP).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 HinP2) as (_ & _ & PUNP & PRNG & PRSH & _).
    cbn [cb_addr cb_size fst snd] in PUNP, PRNG, PRSH. unfold PCAP_NG_SF_TOTAL in PUNP, PRNG, PRSH.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 (or_introl eq_refl : In (q', A, (ng_ifaces_size s * 2 * 40)%Z) (((q', A, (ng_ifaces_size s * 2 * 40)%Z) :: C1 ++ C2) ++ FB))) as ((_ & _ & ATOPx & _) & A1 & _).
    cbn [cb_addr cb_size fst snd] in ATOPx, A1.
    pose proof (munch_refl [(P + 664, P + 668); (P + 672, P + 680)]%Z m2) as MU3. pose proof (wmono_refl asegs m2) as WM3.
    hide HEB. hide HBUF. hide HCUR. hide HD. hide FRS. hide HPV. hide HBK.
    zstep. rewrite (eqb_lits_false A 0) by lia. cbv beta iota delta [negb].
    ck0_at PUNP (P + 664)%Z; ck_go.
    do 2 zstep.
    ck0 PUNP; ck_go.
    do 3 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    assert (AGS23 : agrees_on (fun a => outside [(P + 664, P + 668); (P + 672, P + 680)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU3 | exact WM3 | intros a _ Ho; exact Ho]).
    assert (G3 : GIOA L RNG2 s2' ((q', A, ng_ifaces_size s * 2 * 40)%Z :: C1 ++ C2) FB FL m3).
    { eapply (gl_client_frame _ _ _ GL); [exact G2 | exact MU3 | exact WM3 |].
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; left; unfold iv_in_block; apply Exists_cons_tl; apply Exists_exists;
        exists (pc_self p, P, PCAP_NG_SF_TOTAL); (split; [exact HinP|]); cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia. }
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G2) as BA. cbn [app blocks_apart] in BA. destruct BA as [FA _].
    pose proof (proj1 (Forall_forall _ _) FA _ (in_or_app _ _ _ (or_introl HinP))) as APIP. unfold apart in APIP. cbn [cb_addr cb_size fst snd] in APIP. unfold PCAP_NG_SF_TOTAL in APIP.
    unhide HEB. unhide HBUF. unhide HCUR. unhide HD. unhide FRS. unhide HBK.
    transport HD m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport FRS m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport HBUF m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha APB B3x; lia).
    transport HCUR m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport HEB m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha EBP; lia).
    rewrite !Z.min_l in HBK by lia.
    transport HBK m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha APIP E3; lia).
    assert (AGa3 : ai_AGP FL sp C1 C2 P B CUR EB p m m3).
    { eapply agrees_on_trans; [exact AGa2|]. eapply agrees_on_weaken; [exact AGS23|]. intros a (_ & Hn & _); cbn [outside fst snd]. unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Hn. lia. }
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 1 HBK) as [AR1 JK]. cbn [firstn skipn cells_size csize Nat.add] in AR1, JK.
    pose proof (rw_cells_recell _ _ _ (ifs_cells (rev (ng_ifaces s)) js) AR1 WFI
                  ltac:(cbn [cells_bytes cbytes app]; rewrite app_nil_r; symmetry; apply firstn_all2; rewrite (cells_bytes_length _ WFI), ifs_cells_size by (rewrite length_rev; lia); rewrite length_rev; lia)) as AR1'.
    replace (Z_to_bv 64 (ng_ifcount s)) with (Z_to_bv 64 (ng_ifcount SG - 1)) by (cbn [SG ng_ifcount]; f_equal; lia).
    eapply (KED0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 RNG2 s2' SG q' A js pad junkA jk jk0 jk1 jk2 jk3);
      [ reflexivity | reflexivity | reflexivity | cbn [SG ng_ifcount]; lia | cbn [SG ng_ifcount ng_ifaces_size]; lia | cbn [SG ng_ifaces_size]; lia | exact LJS | exact FP2
      | exact MI2 | exact ST2 | exact AGa3 | exact HD | exact FRS | exact HBUF | exact HCUR | exact HEB
      | unfold ng_cells; cbn [SG ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact HNG
      | exact AR1'
      | cbn [SG ng_ifcount ng_ifaces_size]; lazymatch type of JK with rw_cells _ _ ?AA [CB ?n _] => replace (A + 40 * (ng_ifcount s + 1 - 1))%Z with AA by lia; replace (Z.to_nat (40 * (ng_ifaces_size s * 2 - (ng_ifcount s + 1 - 1)))) with n by lia end; exact JK
      | replace (40 * ng_ifaces_size SG)%Z with (ng_ifaces_size s * 2 * 40)%Z by (cbn [SG ng_ifaces_size]; lia); exact G3 | exact OF2 ].
  Qed.
  End Sz1.
  #[using="fflagA GL GPL MALLOC REALLOC RPC SNPRINTF"] Theorem add_interface_proofA : ltac:(let t := eval cbv delta [add_interface_proofA__stmt] in add_interface_proofA__stmt in exact t).
  Proof. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG st C1 C2 FB FL trC P B I CUR EB lo idb_off p s i c bs ej pad cpad. ltac2:(SecDiet.SzSec.closeP 'add_interface_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AIThm.
End CANSEC1.
End TwB.
End F_aiMA.
