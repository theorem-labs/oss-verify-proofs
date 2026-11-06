(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Ox.F64_002.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require Import UbGuardB AiAuxB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiEA_body__B3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiEA_body__B3P.F_aiEA_loop. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
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
  Hypothesis BU : (lo + 16528 <= bv_unsigned sp)%Z.
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
        (sg : pcap_ng_sf) (q1 : hptr) (I' : Z) (js : list if_junk) (pad1 junk1 jj j0 j1 j2 j3 : list byte),
      ng_user_tsresol sg = ng_user_tsresol s -> ng_max_blocksize sg = ng_max_blocksize s -> ng_ifaces sg = ng_ifaces s ->
      (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z -> (ng_ifcount sg <= ng_ifaces_size sg)%Z -> (1 <= ng_ifaces_size sg < 2^26)%Z ->
      length js = length (ng_ifaces s) ->
      fp_le RNG RNG3 ->
      mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -144) -> AGP m2 ->
      rw_cells asegs m2 (bv_unsigned sp + -144) [CB 8 jj; CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] -> FRAME m2 ->     (* [comment removed for export] *)
      rw_cells asegs m2 B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
      rw_cells asegs m2 CUR (cursor_cells B c cpad) ->
      rw_cells asegs m2 EB [CB 256 ej] ->
      rw_cells asegs m2 (P + 648) (ng_cells sg I' pad1) ->
      rw_cells asegs m2 I' (ifs_cells (rev (ng_ifaces s)) js) ->
      rw_cells asegs m2 (I' + 40 * (ng_ifcount sg - 1)) [CB (Z.to_nat (40 * (ng_ifaces_size sg - (ng_ifcount sg - 1)))) junk1] ->
      GIOA L RNG3 stG ((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) FB FL m2 -> ps_outfile stG = ps_outfile st ->
      evtF asegs RNG3 (POSTQ (ai_result sg (Some q1) (process_idb_options (pc_swapped p) c (pc_bufdata p))) stG RNG3)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' x8 (Z_to_bv 64 (P + 648)) a0' (Z_to_bv 64 (B + idb_off)) (Z_to_bv 64 CUR) a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 660)) (Z_to_bv 64 P) x20 (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 660) 3 + 2147450880)) x23 x24 x25 (Z_to_bv 64 EB) x27
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8c408) fc None m2 (seg_rom asegs)).
  Section Sz1.
  Variables ra' t0' t1' t2' x8 a0' a3' a4' a5' a6' a7' x20 x23 x24 x25 x27 t3' t4' t5' t6' m2 RNG3 stG sg q1 I' js pad1 junk1 jj j0 j1 j2 j3 : ltac2:(SecDiet.SzSec.tyM 'ai_common__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ai_common__body : ltac2:(SecDiet.SzSec.bodyP 'ai_common__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej cpad G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 IDB4 COFF CREM CEND CBT CUR8 APB EBP2 HPV PFX GRD ra' t0' t1' t2' x8 a0' a3' a4' a5' a6' a7' x20 x23 x24 x25 x27 t3' t4' t5' t6' m2 RNG3 stG sg q1 I' js pad1 junk1 jj j0 j1 j2 j3.
 intros U1 U2 U5 IC1 IC2 SZ LJS FP3 MI2 ST2 AG2 HD2 FR2 BUF2 CC2 HEB2 NG2 AR1 JK G2 OFG.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    (* [comment removed for export] *)
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA.ai_head FO GIOA fflagA GL sp L C1 C2 FB FL P B EB lo p LO BU GPL HinP HinB EBL _ _ _ _ _ _ G2 ltac:(lia)) as ((Q1 & Q4 & Q2) & IUNP & IRNG & IRSH & (bI & bIr & bIhi & bIlo & bIimg) & API & APIB & APIE).
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
    pose proof (munch_refl [(SA, SA + 4); (bv_unsigned sp + -144, bv_unsigned sp + -104)]%Z m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. ub_al 3%Z ltac:(clear - B2 IDB4; Z.div_mod_to_equations; lia). zstep. if_false.
    zstep.
  ck_join BUNP 4%Z 0x8c424%Z [10%Z; 13%Z].
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
  assert (SAR : (I' <= SA /\ SA + 40 <= I' + 40 * ng_ifaces_size sg /\ SA mod 8 = 0)%Z) by (clear - HSA IC1 IC2 SZ Q2; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  zstep. ub_ltu.
  do 4 zstep. ub_xnull.
  ub_null.
  zstep. ub_al 7%Z ltac:(exact (proj2 (proj2 SAR))). zstep. if_false.
  ck IUNP 4%Z 0x8c494%Z [14%Z; 15%Z].
  zstep. ub_al 7%Z ltac:(exact CUR8).          (* [comment removed for export] *)
  zstep.
  zstep. if_false.
  zstep.
  ck0 CUNP; ck_go.
  zstep.                                       (* [comment removed for export] *)
  do 2 zstep.
  zstep.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  (* [comment removed for export] *)
  assert (AGS23 : agrees_on (fun a => outside [(SA, SA + 4); (bv_unsigned sp + -144, bv_unsigned sp + -104)]%Z a) m2 m3) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
  unhide FR2. unhide BUF2. unhide HEB2. unhide AR1.
  transport FR2 m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
  transport BUF2 m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha APIB SAR BTOP B1 B3x LO BU; lia).
  assert (EBL3 : clocA FL ((q1, I', (40 * ng_ifaces_size sg)%Z) :: C1 ++ C2) EB 256) by (eapply clocA_incl; [exact EBL | apply incl_tl, incl_refl | apply incl_refl]).
  pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G2 EBL3) as (EBLO & EBHI).
  transport HEB2 m3 AGS23 ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; clear - Ha APIE SAR EBHI EBLO LO BU; lia).
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
    eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA.ai_tail with (opts := mkIdbOpts 1000000 0 false false false) (SA := SA) (js := js);
      eassumption || (try exact IC1; try exact HSA; try reflexivity; try (cbn [io_tsresol]; lia); try lia).
  - (* [comment removed for export] *)
    rewrite (eqb_lits_false (cur_remaining c) 0) by lia. cbv iota.
    clear MU WM AGS23.
    pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp + -104)]%Z m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    hide FR2. hide BUF2. hide HEB2. hide AR1. hide AR2. hide SL3. hide NG2. hide CC2.
    do 21 zstep.                               (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
    replace (Z.land (P + 56) 7) with 0%Z in HD2 by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3)%Z with 8%Z; clear - P2; Z.div_mod_to_equations; lia).
    change (0 + 3)%Z with 3%Z in HD2.
    assert (AGS34 : agrees_on (fun a => outside [(bv_unsigned sp + -144, bv_unsigned sp + -104)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
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
                    stG sg q1 I' SA js pad1 sjx tlx FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG jj (Z.to_nat (cur_remaining c / 4))
                    (ai_loop FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej
                       G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 HPV RNG3
                       stG sg q1 I' SA js pad1 sjx tlx FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG jj (Z.to_nat (cur_remaining c / 4)))) as IT
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
  Proof. intros ra' t0' t1' t2' x8 a0' a3' a4' a5' a6' a7' x20 x23 x24 x25 x27 t3' t4' t5' t6' m2 RNG3 stG sg q1 I' js pad1 junk1 jj j0 j1 j2 j3. ltac2:(SecDiet.SzSec.closeP 'ai_common__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End AIX.
  End CANSEC1.
