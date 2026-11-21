(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Lemma reach_cases : forall m, reach m ->
  m = HEAD \/ m = DICTID \/ m = DICT \/ m = TYPE \/ m = TYPEDO \/ m = STORED \/ m = COPY_ \/ m = COPY \/
  m = TABLE \/ m = LENLENS \/ m = CODELENS \/ m = LEN_ \/ m = LEN \/ m = LENEXT \/ m = DIST \/ m = DISTEXT \/
  m = MATCH \/ m = LIT \/ m = CHECK \/ m = LENGTH \/ m = DONE \/ m = BAD \/ m = MEM.
Proof. intros m H. unfold reach in H. cbv [HEAD DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM] in *. lia. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KDISPB cx ly B := (KDISP cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation KBADB cx ly B := (KBADMODE cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation KLLD cx ly := (KLEAVE_LD cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh).
  Notation KLV cx ly := (KLEAVE cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh).
  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation ARM cx ly Lb X := (arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Lemma kbadmode_of_kdisp : forall cx ly B, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KDISPB cx ly B -> KBADB cx ly B.
  Proof.
    intros cx ly B CTX PLEN KD. unfold KBADMODE. intros until m. intros SI ME ARR VIS HID.
    pose proof (proj1 SI : IDefs.RNG cx st lf cf) as RN0.
    inf_arm_open_rn.
    zrunb [0x8e5ec].
    eapply (KD (bad_of (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) lf cf wf fo);
      [exact SI| exact ME| exact ARR| unfold bad_of; change BAD with 16209; inf_vis_close| inf_hid_close].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder of KDISP at 1.4 (InfBBase's inf_locals no longer holds it) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Lemma kleave_ld_of_kleave : forall cx ly, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> KLLD cx ly.
  Proof.
    intros cx ly CTX PLEN KL. unfold KLEAVE_LD, LEAVE_MS, L_LEAVE_LD. intros until m. intros SI ARR CINN VIS HID.
    inf_arm_open.
    zrunb [0x93758].
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - cin)) by (f_equal; lia).
    eapply (KL (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
      [exact SI| exact ARR| exact VISf| exact HID].
  Qed.

  Section Step.
  Hypothesis PAYR : Forall (fun c => 0 <= c < 256) payload.
  Definition arms_ok (cx : ictx) (ly : ilay) : Prop :=
       ARM cx ly 0x8e648 HEAD
    /\ ARM cx ly 0x8ec8c DICTID
    /\ ARM cx ly 0x8f090 DICT
    /\ ARM cx ly 0x8f134 TYPE
    /\ ARM cx ly 0x8f144 TYPEDO
    /\ ARM cx ly 0x8ed88 STORED
    /\ ARM cx ly 0x8f340 COPY_
    /\ ARM cx ly 0x8f35c COPY
    /\ ARM cx ly 0x8ee1c TABLE
    /\ ARM cx ly 0x8e700 LENLENS
    /\ ARM cx ly 0x8f8d8 CODELENS
    /\ ARM cx ly 0x91730 LEN_
    /\ ARM cx ly 0x9174c LEN
    /\ ARM cx ly 0x8e74c LENEXT
    /\ ARM cx ly 0x91d9c DIST
    /\ ARM cx ly 0x8e72c DISTEXT
    /\ ARM cx ly 0x92318 MATCH
    /\ ARM cx ly 0x8ec00 LIT
    /\ ARM cx ly 0x8eea4 CHECK
    /\ ARM cx ly 0x90a4c LENGTH.

  Lemma kall_of_kdisp : forall cx ly B, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> KDISPB cx ly B -> KALLB cx ly B.
  Proof.
    intros cx ly B CTX PLEN KL KD. unfold KALL. split; [exact KD|]. split; [apply kbadmode_of_kdisp; assumption|].
    split; [apply kleave_ld_of_kleave; assumption| exact KL].
  Qed.

  Lemma kdisp_mono : forall cx ly B B', B' <= B -> KDISPB cx ly B -> KDISPB cx ly B'.
  Proof. intros cx ly B B' HB KD. unfold KDISP. intros until m. intros SI ME. apply KD; [exact SI| lia]. Qed.

  Definition KDISP_P (P : Z -> Prop) (cx : ictx) (ly : ilay) (B : Z) : Prop :=
    forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word) (x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
      P (t_mode st) ->
      sinv cx st lf cf -> meas cx st < B -> inf_arr_ok cx wf fo ->
      inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
      inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
      evtF bsegs RNG POST (DISP_MS cx ly gp tp FR fc st x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Definition modesA (m : Z) : Prop :=
    m = HEAD \/ m = DICTID \/ m = DICT \/ m = TYPE \/ m = TYPEDO \/ m = STORED \/ m = COPY_ \/ m = COPY \/ m = TABLE \/ m = LENLENS \/ m = CODELENS.
  Definition modesB (m : Z) : Prop :=
    m = LEN_ \/ m = LEN \/ m = LENEXT \/ m = DIST \/ m = DISTEXT \/ m = MATCH \/ m = LIT \/ m = CHECK \/ m = LENGTH \/ m = DONE \/ m = BAD \/ m = MEM.
  End Step.
End S.
End CANSEC1.
