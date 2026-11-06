(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require Import UbGuardB AiAuxB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.


Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.

(* [comment removed for export] *)
Lemma msg_ok_b : forall l : list Z, forallb (fun z => (0 <? z)%Z && (z <? 256)%Z) l = true -> Forall (fun z => 0 < z < 256)%Z l.
Proof. intros l H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. Qed.
Ltac msg_ok := first [ apply msg_ok_b; vm_compute; reflexivity
                     | vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]] ].
(* [comment removed for export] *)
Ltac fmt_at_tac MI ADDR str :=
  split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs _ ADDR (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string str) ++ [Z_to_bv 8 0])
                   MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
  split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]).

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AccFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= plia.
Local Ltac flia ::= first [ sassumption | plia | assumption ].
Local Ltac acc_hint ::= acc_hint_cheap.
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.sub _ (Z.mul (256)%Z (Z.div _ (128)%Z))) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (Z.sub _ (256)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section AIX.
  Context {H : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.CANSEC1.AIX.u0}} {hptr : Type@{OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.CANSEC1.AIX.u1}} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
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

  (* [comment removed for export] *)
  Variables (RNG3 : footprint) (stG : PS) (sg : pcap_ng_sf) (q1 : hptr) (I' SA : Z) (js : list if_junk) (pad1 sj tail3 : list byte).
  Hypothesis FP3 : fp_le RNG RNG3.
  Hypothesis U1 : ng_user_tsresol sg = ng_user_tsresol s.
  Hypothesis U2 : ng_max_blocksize sg = ng_max_blocksize s.
  Hypothesis U5 : ng_ifaces sg = ng_ifaces s.
  Hypothesis IC1 : (ng_ifcount sg = Z.of_nat (length (ng_ifaces s)) + 1)%Z.
  Hypothesis IC2 : (ng_ifcount sg <= ng_ifaces_size sg)%Z.
  Hypothesis SZ : (1 <= ng_ifaces_size sg < 2^26)%Z.
  Hypothesis LJS : length js = length (ng_ifaces s).
  Hypothesis HSA : (SA = I' + 40 * (ng_ifcount sg - 1))%Z.
  Hypothesis SNR : (0 <= ai_snap < 2^32)%Z.
  Hypothesis OFG : ps_outfile stG = ps_outfile st.

  (* [comment removed for export] *)
  Variable hj0 : list byte.
  (* [comment removed for export] *)
  #[local] Abbreviation ai_hd := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_hd P EB hj0).
  #[local] Abbreviation sgF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.sgF hptr idb_off p sg).
  #[local] Abbreviation pF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.pF hptr idb_off p sg q1).
  #[local] Abbreviation ai_result_inl := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_result_inl hptr idb_off p s c sg q1).
  #[local] Abbreviation AIM := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.AIM H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation LREGS := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LREGS sp gp tp P CUR).
  #[local] Abbreviation LOOPK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LOOPK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ITERK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ITERK H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop0 := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop0 H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop_step__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop_step__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_loop_step := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_loop_step rc tlsI H hptr FO GIOA fflagA GL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej LO BU SPT RSTK GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB UTS IFW IDB0 COFF CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0).
  #[local] Abbreviation loop_restf__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_restf__stmt H hptr GIOA L st C1 C2 FB FL P B CUR idb_off p s c RNG3 stG sg q1 I' SA js pad1 sj tail3).
  #[local] Abbreviation loop_restf := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_restf rc H hptr GIOA sp L st C1 C2 FB FL P B CUR EB lo idb_off p s c LO BU P14 B14 LENB CURS EBP EBB IDB0 COFF CREM CEND APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 U1 U2 IC1 IC2 SZ LJS HSA OFG).
  #[local] Abbreviation loop_facts__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.loop_facts__stmt H hptr GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m L st C1 C2 FB FL P B CUR EB lo idb_off p s c ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_disp__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_disp__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_body__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_body__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation ai_iter__stmt := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_iter__stmt H hptr GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B CUR EB lo idb_off p s c bs ej RNG3 stG sg q1 I' SA js pad1 sj tail3 hj0).
  #[local] Abbreviation swap_hdrA := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.swap_hdrA rc hptr sp L P B CUR EB lo idb_off p s c LO BU ALN P14 B14 LENB CURS EBP EBB P2 B2 IDB0 COFF CREM CEND CUR8 APB EBP2 js LJS).

  #[local] Abbreviation pio_body := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_body.
  #[local] Abbreviation pio_value := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_value.
  #[local] Abbreviation le8val := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.le8val.

  Section Sz6.
  Variables fuel t0' x25 x26 io c' sw pre post c0 c1 l0 l1 bsr cpad3 m5 D : ltac2:(SecDiet.SzSec.tyM 'ai_disp__stmt "vhvvvvvvvvvvvvvvvv" @fuel).
  Lemma ai_disp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_disp__stmt "vhvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m L RNG st C1 C2 FB FL P B I CUR EB lo idb_off p s i c bs ej G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 RNG3 stG sg q1 I' SA js pad1 sj tail3 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG hj0 fuel t0' x25 x26 io c' sw pre post c0 c1 l0 l1 bsr cpad3 m5 D.
    intros LK.
 intros code olen padded buf5 bs5 c2 AIM5 TSR SW FUEL GE4 FIT OFF0 OFF4 LEN4 HDd Lpre PFXr HC0 HC1 HL0 HL1 GRpost HB2.
    red in LK. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.LREGS in LK.
    assert (R2 : cur_remaining c2 = (cur_remaining c' - 4 - padded)%Z) by reflexivity.
    assert (FUEL2 : (cur_remaining c2 / 4 < Z.of_nat fuel)%Z) by (rewrite R2; clear - FUEL FIT HL0 HL1; subst padded olen; Z.div_mod_to_equations; lia).
    pose proof (AIM5 io TSR) as IV5.
    destruct IV5 as (_ & MI5 & ST5 & AG5 & HD5 & FR5 & NG5 & AR15 & SL5 & AR25 & G5 & BUF5 & PFX5 & LB5 & GR5 & CC5 & CR1 & CR2 & CR3 & CR4 & HEB5 & OFF5).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    assert (HCODE : (0 <= code < 65536)%Z) by (subst code; lia). assert (HOLEN : (0 <= olen < 65536)%Z) by (subst olen; lia).
    assert (HPAD : (olen <= padded <= olen + 3 /\ padded mod 4 = 0)%Z) by (subst padded; Z.div_mod_to_equations; lia).
    assert (Lpost : (cur_remaining c' - 4 <= Z.of_nat (length post))%Z) by (subst buf5; rewrite length_app in LEN4; cbn [length] in LEN4; lia).
    assert (RESTF5 : AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m5 stG c (pF buf5)).
    { eapply loop_restf; [exact G5 | exact NG5 | exact AR15 | exact SL5 | exact AR25 | exact BUF5 | exact PFX5 | exact LB5 | exact GR5 | exact CC5 | reflexivity]. }
    (* [comment removed for export] *)
    assert (HinB5 : In (pc_buffer p, B, pc_bufalloc p) (((q1, I', 40 * ng_ifaces_size sg)%Z :: C1 ++ C2) ++ FB)) by (apply in_or_app; left; right; exact HinB).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB5) as ((BBAND & B3 & BTOP & _) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in BBAND, B3, BTOP, B1, BUNP, BRNG, BRSH.
    band_ind BBAND bB.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact (rng_fp_le _ _ _ _ FP3 RSTK)| lia]).
    assert (LBS : length bs5 = Z.to_nat (pc_bufalloc p)) by (destruct BUF5 as [[WF _] _]; cbn in WF; lia).
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.pio_body.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiEA.ai_hd in HD5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    hide FR5. hide NG5. hide AR15. hide SL5. hide AR25. hide BUF5. hide CC5. hide HEB5.
    (* [comment removed for export] *)
    zstep. zstep.
    destruct (Z.eq_dec code 9) as [E9|NE9].
    { (* [comment removed for export] *)
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ E9). cbv iota.
      replace (code =? OPT_ENDOFOPT)%Z with false by (rewrite E9; reflexivity). replace (code =? IF_TSRESOL)%Z with true by (rewrite E9; reflexivity). cbv iota.
      zstep. zstep.
      destruct (Z.eq_dec olen 1) as [L1|L1].
      2:{ (* [comment removed for export] *)
        rewrite (eqb_lits_false olen 1) by lia. cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_neq olen 1) L1). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 3 zstep.
        assert (MSG : fmt_at m5 0x226c0 "Interface Description Block has if_tsresol option with length %u != 1"%string) by (fmt_at_tac MI5 0x226c0%Z "Interface Description Block has if_tsresol option with length %u != 1"%string).
        unhide FR5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB.ai_snp_b with (m3 := m5) (args := [AInt olen]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
          [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 ]. }
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ L1). cbn [negb]. cbv iota. rewrite (proj2 (Z.eqb_eq olen 1) L1). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      zstep.
      destruct (io_saw_tsresol io) eqn:SAWR.
      { cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 3 zstep.
        assert (MSG : fmt_at m5 0x22740 "Interface Description Block has more than one if_tsresol option"%string) by (fmt_at_tac MI5 0x22740%Z "Interface Description Block has more than one if_tsresol option"%string).
        unhide FR5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB.ai_mcp with (m3 := m5) (str := "Interface Description Block has more than one if_tsresol option"%string) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
          [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia | lia | vm_compute; reflexivity | msg_ok ]. }
      cbn [Z.b2z]. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      destruct post as [|v post']; [exfalso; cbn [length] in Lpost; clear - Lpost FIT HPAD L1; lia|].
      destruct bsr as [|bv0 bsr']; [cbn in PFXr; discriminate|]. cbn [firstn length map] in PFXr. injection PFXr as Ebv0 PFXr'. subst bv0.
      pose proof (Forall_inv GRpost) as Bv. cbv beta in Bv.
      assert (GU : get_u8 buf5 (cur_off c' + 4) = v).
      { subst buf5. replace (pre ++ c0 :: c1 :: l0 :: l1 :: v :: post') with ((pre ++ [c0; c1; l0; l1]) ++ v :: post') by (rewrite <- app_assoc; reflexivity).
        replace (cur_off c' + 4)%Z with (Z.of_nat (length (pre ++ [c0; c1; l0; l1]))) by (rewrite length_app; cbn [length]; lia). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_u8_at. }
      rewrite GU.
      pose proof (rw_cells_recell _ _ _ [CB 1 [b8 v]; CB (length bsr') bsr'] HB2 ltac:(cbn; auto) ltac:(reflexivity)) as HV.
      destruct (rw_cells_cut _ _ _ 1 HV) as [HV1 _]. clear HV. cbn [firstn] in HV1.
      assert (INB : (B <= D + 4 /\ D + 4 + 1 <= B + pc_bufalloc p)%Z) by (cbn [length] in Lpost; lia).
      eapply evtF_cut.
      { eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.TwB.tsres_ldA RNG3) with (v := v) (Bq := B) (alloc := pc_bufalloc p) (bB := bB) (A := (D + 4)%Z);
          [exact Bv | exact HV1 | exact MI5 | exact BUNP | lia | lia | lia | exact B2 | lia | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
      cbv beta. intros ms' (a3x & ->).
  rewrite (sxb_lit v) by lia.
  zstep. zstep.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_128 v) by lia.
      destruct (Z.lt_ge_cases v 128) as [VLO|VHI].
      + (* [comment removed for export] *)
        rewrite (Z.div_small v 128) by lia. replace (128 * 0 =? 0)%Z with true by reflexivity. cbv beta iota delta [negb]. replace (v - 256 * 0)%Z with v by lia.
        rewrite (Z.mod_small v 18446744073709551616), OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_255_mod, (Z.mod_small v 256) by lia.
        if_cases BRv; zify_cond BRv. { exfalso. plia_seed1 BRv. }
        zstep. zstep.
        destruct (Z.lt_ge_cases v 20) as [V20|V20].
        2:{ (* [comment removed for export] *)
          if_cases BR20; zify_cond BR20; rewrite ?unsigned_lit in BR20 by lia; [| exfalso; plia_seed1 BR20].
          rewrite (proj2 (Z.ltb_lt 19 v)) by lia. cbv iota. rewrite ai_result_inl.
          do 3 zstep.
          assert (MSG : fmt_at m5 0x22820 "Interface Description Block if_tsresol option resolution 10^-%u is too high"%string) by (fmt_at_tac MI5 0x22820%Z "Interface Description Block if_tsresol option resolution 10^-%u is too high"%string).
          unhide FR5. unhide HEB5.
          eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB.ai_snp_b with (m3 := m5) (args := [AInt v]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
            [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia
            | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_dec_high, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 ]. }
        if_cases BR20; zify_cond BR20; rewrite ?unsigned_lit in BR20 by lia; [exfalso; plia_seed1 BR20|].
        rewrite (proj2 (Z.ltb_ge 19 v)) by lia. cbv iota.
        assert (P19 : (0 < 10 ^ v <= 10 ^ 19)%Z) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
        change (10 ^ 19)%Z with 10000000000000000000%Z in P19.
        zstep.
        destruct (Z.eq_dec v 0) as [V0|V0].
        * (* [comment removed for export] *)
          rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ V0). cbv iota. rewrite V0. change (10 ^ 0)%Z with 1%Z.
          do 4 zstep.
          unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
          rewrite <- SW; eapply (LK _ _ _ _ _ _ _ _ (mkIdbOpts 1 (io_tsoffset io) false true (io_saw_tsoffset io)) c2 buf5 m5 bs5 cpad3); [apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
        * rewrite (eqb_lits_false v 0) by lia. cbv iota. zstep. zstep.
          eapply evtF_cut; [eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB.pow10A (Z.to_nat v - 1) v 1); lia |].
          cbv beta. intros ms' ->. rewrite Z.mul_1_l.
          do 2 zstep.
          unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
          rewrite <- SW; eapply (LK _ _ _ _ _ _ _ _ (mkIdbOpts (10 ^ v) (io_tsoffset io) false true (io_saw_tsoffset io)) c2 buf5 m5 bs5 cpad3); [apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
      + (* [comment removed for export] *)
        replace (v / 128)%Z with 1%Z by (Z.div_mod_to_equations; lia). replace (128 * 1 =? 0)%Z with false by reflexivity. cbv beta iota delta [negb].
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_127_hi v) by lia. replace (v - 256 * 1)%Z with (v - 256)%Z by lia.
        rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_255_mod. replace (((v - 256) mod 18446744073709551616) mod 256)%Z with v by (Z.div_mod_to_equations; lia).
        if_cases BRv; zify_cond BRv; [| exfalso; plia_seed1 BRv].
        zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.land_127_hi v) by lia.
        zstep. zstep.
        destruct (Z.lt_ge_cases 63 (v - 128)) as [V63|V63].
        { (* [comment removed for export] *)
          if_cases BR63; zify_cond BR63; rewrite ?unsigned_lit in BR63 by lia; [| exfalso; plia_seed1 BR63].
          rewrite (proj2 (Z.ltb_lt 63 (v - 128))) by lia. cbv iota. rewrite ai_result_inl.
          do 2 zstep.
          assert (MSG : fmt_at m5 0x227a0 "Interface Description Block if_tsresol option resolution 2^-%u is too high"%string) by (fmt_at_tac MI5 0x227a0%Z "Interface Description Block if_tsresol option resolution 2^-%u is too high"%string).
          unhide FR5. unhide HEB5.
          eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB.ai_snp_b with (m3 := m5) (args := [AInt (v - 128)]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
            [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia
            | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsresol_bin_high, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 ]. }
        if_cases BR63; zify_cond BR63; rewrite ?unsigned_lit in BR63 by lia; [exfalso; plia_seed1 BR63|].
        rewrite (proj2 (Z.ltb_ge 63 (v - 128))) by lia. cbv iota.
        assert (P63 : (0 < 2 ^ (v - 128) <= 2 ^ 63)%Z) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
        change (2 ^ 63)%Z with 9223372036854775808%Z in P63.
        zstep. zstep.
        rewrite (Z.mod_small (v - 128) 64), Z.shiftl_1_l by lia.
        zstep. zstep.
        unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
        rewrite <- SW; eapply (LK _ _ _ _ _ _ _ _ (mkIdbOpts (2 ^ (v - 128)) (io_tsoffset io) true true (io_saw_tsoffset io)) c2 buf5 m5 bs5 cpad3); [apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
    }
    (* [comment removed for export] *)
    rewrite (eqb_lits_false code 9) by lia. cbv iota.
    replace (code =? IF_TSRESOL)%Z with false by (symmetry; apply Z.eqb_neq; exact NE9).
    zstep. zstep.
    destruct (Z.eq_dec code 14) as [E14|NE14].
    { (* [comment removed for export] *)
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ E14). cbv beta iota delta [negb].
      replace (code =? OPT_ENDOFOPT)%Z with false by (rewrite E14; reflexivity). replace (code =? IF_TSOFFSET)%Z with true by (rewrite E14; reflexivity). cbv iota.
      zstep. zstep.
      destruct (Z.eq_dec olen 8) as [L8|L8].
      2:{ (* [comment removed for export] *)
        rewrite (eqb_lits_false olen 8) by lia. cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_neq olen 8) L8). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 3 zstep.
        assert (MSG : fmt_at m5 0x228a0 "Interface Description Block has if_tsoffset option with length %u != 8"%string) by (fmt_at_tac MI5 0x228a0%Z "Interface Description Block has if_tsoffset option with length %u != 8"%string).
        unhide FR5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB.ai_snp_b with (m3 := m5) (args := [AInt olen]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
          [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.tsoffset_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 ]. }
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ L8). cbv beta iota delta [negb]. rewrite (proj2 (Z.eqb_eq olen 8) L8). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      zstep.
      destruct (io_saw_tsoffset io) eqn:SAWO.
      { cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 4 zstep.
        assert (MSG : fmt_at m5 0x22920 "Interface Description Block has more than one if_tsoffset option"%string) by (fmt_at_tac MI5 0x22920%Z "Interface Description Block has more than one if_tsoffset option"%string).
        unhide FR5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB.ai_mcp with (m3 := m5) (str := "Interface Description Block has more than one if_tsoffset option"%string) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
          [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia | lia | vm_compute; reflexivity | msg_ok ]. }
      cbn [Z.b2z]. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
      (* [comment removed for export] *)
      destruct post as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 post']]]]]]]]; [ exfalso; cbn [length] in Lpost; clear - Lpost FIT HPAD L8; lia .. | ].
      destruct bsr as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 bsr']]]]]]]]; try (cbn in PFXr; discriminate).
      cbn [firstn length map] in PFXr. injection PFXr as E0 E1 E2 E3 E4 E5 E6 E7 PFXr'. subst b0 b1 b2 b3 b4 b5 b6 b7.
      assert (Bv : forall x, In x [v0; v1; v2; v3; v4; v5; v6; v7] -> (0 <= x < 256)%Z).
      { intros x Hx. apply (proj1 (Forall_forall _ _) GRpost). cbn in Hx |- *. clear - Hx. tauto. }
      pose proof (Bv v0 ltac:(cbn; clear; tauto)) as Bv0. pose proof (Bv v1 ltac:(cbn; clear; tauto)) as Bv1. pose proof (Bv v2 ltac:(cbn; clear; tauto)) as Bv2. pose proof (Bv v3 ltac:(cbn; clear; tauto)) as Bv3.
      pose proof (Bv v4 ltac:(cbn; clear; tauto)) as Bv4. pose proof (Bv v5 ltac:(cbn; clear; tauto)) as Bv5. pose proof (Bv v6 ltac:(cbn; clear; tauto)) as Bv6. pose proof (Bv v7 ltac:(cbn; clear; tauto)) as Bv7. clear Bv.
      assert (GU : get_le64 buf5 (cur_off c' + 4) = le8val v0 v1 v2 v3 v4 v5 v6 v7).
      { subst buf5. replace (pre ++ c0 :: c1 :: l0 :: l1 :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: post') with ((pre ++ [c0; c1; l0; l1]) ++ v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: post') by (rewrite <- app_assoc; reflexivity).
        replace (cur_off c' + 4)%Z with (Z.of_nat (length (pre ++ [c0; c1; l0; l1]))) by (rewrite length_app; cbn [length]; lia). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.get_le64_at. }
      rewrite GU.
      pose proof (rw_cells_recell _ _ _ [CB 8 (map b8 [v0; v1; v2; v3; v4; v5; v6; v7]); CB (length bsr') bsr'] HB2 ltac:(cbn; auto) ltac:(reflexivity)) as HV.
      destruct (rw_cells_cut _ _ _ 1 HV) as [HV8 _]. clear HV. cbn [firstn] in HV8.
      assert (INB : (B <= D + 4 /\ D + 4 + 8 <= B + pc_bufalloc p)%Z) by (cbn [length] in Lpost; lia).
      eapply evtF_cut.
      { eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiC2A.TwB.ldu64ckA RNG3) with (A := (D + 4)%Z) (u0 := v0) (u1 := v1) (u2 := v2) (u3 := v3) (u4 := v4) (u5 := v5) (u6 := v6) (u7 := v7) (Bq := B) (alloc := pc_bufalloc p) (bB := bB);
          [exact Bv0 | exact Bv1 | exact Bv2 | exact Bv3 | exact Bv4 | exact Bv5 | exact Bv6 | exact Bv7 | exact HV8 | exact MI5 | exact BUNP | lia | lia | lia | exact B2 | lia
          | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
      cbv beta. intros ms' (a0x & a3x & a4x & a5x & s0x & ->).
      (* [comment removed for export] *)
      zstep.
      destruct sw.
      + cbn [Z.b2z]. rewrite (eqb_lits_false 1 0) by lia. cbv beta iota delta [negb].
        destruct (rw_cells_cut _ _ _ 3 HD5) as [_ HD24]. cbn [firstn skipn cells_size csize Nat.add] in HD24.     (* [comment removed for export] *)
        destruct (rw_cells_cut _ _ _ 1 HD24) as [HD16 _]. clear HD24. cbn [firstn skipn] in HD16.
        replace (bv_unsigned sp + -144 + Z.of_nat 24)%Z with (bv_unsigned sp + -144 + 24)%Z in HD16 by lia.
        eapply evtF_cut.
        { eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_aiCA.TwB.bswap64A with (SPF := (bv_unsigned sp + -144)%Z) (u0 := v0) (u1 := v1) (u2 := v2) (u3 := v3) (u4 := v4) (u5 := v5) (u6 := v6) (u7 := v7);
            [exact MI5 | reflexivity | lia | lia | eapply rng_sub'; [exact RSPW | lia] | exact HD16 | exact Bv0 | exact Bv1 | exact Bv2 | exact Bv3 | exact Bv4 | exact Bv5 | exact Bv6 | exact Bv7]. }
        cbv beta. intros ms' (a0y & a3y & a4y & a5y & s0y & s3y & ->).
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.bswap64_bytes v0 v1 v2 v3 v4 v5 v6 v7) by lia. rewrite <- (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.Z_to_bv64_s64 (le8val v7 v6 v5 v4 v3 v2 v1 v0)).
        replace (process_idb_options_loop fuel true) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
        unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
        eapply (LK _ _ _ _ _ _ _ _ (mkIdbOpts (io_tsresol io) (s64 (le8val v7 v6 v5 v4 v3 v2 v1 v0)) (io_is_binary io) (io_saw_tsresol io) true) c2 buf5 m5 bs5 cpad3); [apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
      + cbn [Z.b2z]. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq 0 0 eq_refl). cbv beta iota delta [negb].
        rewrite <- (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE.Z_to_bv64_s64 (le8val v0 v1 v2 v3 v4 v5 v6 v7)).
        replace (process_idb_options_loop fuel false) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
        unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
        eapply (LK _ _ _ _ _ _ _ _ (mkIdbOpts (io_tsresol io) (s64 (le8val v0 v1 v2 v3 v4 v5 v6 v7)) (io_is_binary io) (io_saw_tsresol io) true) c2 buf5 m5 bs5 cpad3); [apply AIM5; cbn [io_tsresol]; lia | exact FUEL2].
    }
    (* [comment removed for export] *)
    rewrite (eqb_lits_false code 14) by lia. cbv beta iota delta [negb].
    replace (code =? IF_TSOFFSET)%Z with false by (symmetry; apply Z.eqb_neq; exact NE14).
    zstep.
    destruct (Z.eq_dec code 0) as [E0|NE0].
    + rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ E0). cbv iota. replace (code =? OPT_ENDOFOPT)%Z with true by (rewrite E0; reflexivity). cbv iota.
      (* [comment removed for export] *)
      zstep.
      destruct (Z.eq_dec olen 0) as [L0|L0].
      * rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.eqb_lits_eq _ _ L0). cbv iota. rewrite (proj2 (Z.eqb_eq olen 0) L0). cbv beta iota delta [negb].
        unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_aiBA.ai_tail with (SA := SA) (js := js) (c' := c2) (opts := io); eassumption || (try exact IC1; try exact HSA; try reflexivity; try lia).
      * rewrite (eqb_lits_false olen 0) by lia. cbv iota. rewrite (proj2 (Z.eqb_neq olen 0) L0). cbv beta iota delta [negb]. rewrite ai_result_inl.
        do 3 zstep.
        assert (MSG : fmt_at m5 0x22640 "Interface Description Block has opt_endofopt option with length %u != 0"%string) by (fmt_at_tac MI5 0x22640%Z "Interface Description Block has opt_endofopt option with length %u != 0"%string).
        unhide FR5. unhide HEB5.
        eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_aiAA.TwB.ai_snp_b with (m3 := m5) (args := [AInt olen]) (h0 := C8 (Z_to_bv 64 3)) (h2 := C8 (Z_to_bv 64 65280)); try eassumption;
          [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | cbn; lia
          | intros; cbn [length firstn]; apply Forall2_cons; [reflexivity| apply Forall2_nil] | unfold Msg.endofopt_len, PCAP_ERRBUF_SIZE; reflexivity | vm_compute; reflexivity | apply args_ok_ints1 ].
    + (* [comment removed for export] *)
      rewrite (eqb_lits_false code 0) by lia. cbv iota. replace (code =? OPT_ENDOFOPT)%Z with false by (symmetry; apply Z.eqb_neq; exact NE0). cbv iota.
      replace (process_idb_options_loop fuel sw) with (process_idb_options_loop fuel (pc_swapped p)) by (rewrite SW; reflexivity).
      unhide FR5. unhide NG5. unhide AR15. unhide SL5. unhide AR25. unhide BUF5. unhide CC5. unhide HEB5.
      eapply (LK _ _ _ _ _ _ _ _ io c2 buf5 m5 bs5 cpad3); [apply AIM5; exact TSR | exact FUEL2].
  Qed.
  End Sz6.
  #[using="rc tlsI FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO UTS IFW P2 B2 IDB0 COFF CREM CEND CBT CUR8 APB EBP2 FP3 U1 U2 U5 IC1 IC2 SZ LJS HSA SNR OFG"] Lemma ai_disp : ltac:(let t := eval hnf in ai_disp__stmt in exact t).
  Proof. intros fuel LK t0' x25 x26 io c' sw pre post c0 c1 l0 l1 bsr cpad3 m5 D. ltac2:(SecDiet.SzSec.closeP 'ai_disp__body "vhvvvvvvvvvvvvvvvv"). Qed.
  End AIX.
  End CANSEC1.
