(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_iface_gotA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfpcap_chkA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfchk_failA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA.
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

(* [comment removed for export] *)
Ltac err_recheck UNP P OK :=
  zstep;
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of UNP with unpoisoned mm ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd mm lo hi P 4 UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P; pose proof (sval_range b) as SR end end;
  zstep; zstep;
  cbv beta delta [mkR];
  lazymatch goal with |- evtF ?segs ?RNGx ?Q (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    eapply (evtF_cut segs RNGx (fun ms' => ck_post [10%Z; 11%Z] (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv mm ro) R)) end;
  [ ck_arm OK 16%nat
  | let ms' := fresh "ms'" in let H := fresh "Hck" in
    intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; ck_clear ].

(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (555520%Z, 555372%Z) => idtac | (555520%Z, 555520%Z) => idtac | (555520%Z, 556984%Z) => idtac | (555584%Z, 555276%Z) => idtac | (555584%Z, 555584%Z) => idtac | (555584%Z, 557004%Z) => idtac | (556228%Z, 556228%Z) => idtac | (556228%Z, 557200%Z) => idtac | (556864%Z, 556536%Z) => idtac | (556864%Z, 556648%Z) => idtac | (556864%Z, 556800%Z) => idtac | (556864%Z, 556864%Z) => idtac | (556864%Z, 557512%Z) => idtac | (556864%Z, 558192%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; lazymatch goal with |- ?q _ => tryif is_var q then unfold q else idtac end; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
(* [comment removed for export] *)
Local Ltac cjq_fold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQc" in pose (QQ := Q); change Q with QQ end).
Local Ltac ck_join_at UNP P N OK RS ::=
  ck_clear; cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd m lo hi P N UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P;
      pose proof (sval_range b) as SR;
      eapply (evtF_cut segs RNG (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv m ro) R));
      [ cjq_fold; ck_arm OK 16%nat
      | let ms' := fresh "ms'" in let H := fresh "Hck" in
        intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; clear RD CK SR; ck_clear; try clear b ]
    | unpoisoned ?m' _ _ => fail "ck_join: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Section CANSEC1. Context {rc : runConstT}.
Section FailSeq.
  Variables (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (RNG : footprint) (SPA ERR EB Fb : Z) (j1 j3 : list byte) (c24 c32 : word).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis UNP : unpoisoned m ERR (ERR + 4).
  Hypothesis RSH : rng RNG (shad (ERR - ERR mod 8)) (nshad (4 + ERR mod 8)).
  Hypothesis RER : rng RNG ERR 4.
  Hypothesis RSP : rng RNG SPA 88.
  Hypothesis ERR4 : (ERR mod 4 = 0)%Z.
  Hypothesis ERLO : (0x603000 <= ERR)%Z.
  Hypothesis ERHI : (ERR + 4 <= SPA)%Z.
  Hypothesis SPAHI : (SPA + 88 <= 2^47)%Z.
  Hypothesis FRA : rw_cells asegs m SPA [CB 24 j1; C8 c24; C8 c32; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                                         C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 EB); CB 16 j3; C8 (Z_to_bv 64 Fb)].
  Hypothesis HE : rw_cells asegs m ERR [C4 z64].

  Local Notation fail_post x19 x20 :=
    (fun ms' : machine_state => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 0) (Z_to_bv 64 1) a2 a3 a4 (Z_to_bv 64 Fb) a6 a7
                      s2 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x87a50) fc None m' (seg_rom asegs)
        /\ munch [(ERR, ERR + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' ERR [C4 (Z_to_bv 64 1)]).

  Local Ltac seq_start := pose proof (munch_refl [(ERR, ERR + 4)]%Z m) as MU; pose proof (wmono_refl asegs m) as WM.
  Local Ltac seq_end := apply evtF_done; eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; assumption.

  #[using="EB j1 j3 c24 c32 MI UNP RSH RER RSP ERR4 ERLO ERHI SPAHI FRA HE"] Lemma fail_seq_A : forall s4 : word,
    evtF asegs RNG (fail_post (Z_to_bv 64 ERR) s4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87900) fc None m (seg_rom asegs)).
  Proof.
    intros s4. seq_start.
    zstep. ck_join_at UNP ERR 4%Z 0x87a40%Z [10%Z; 11%Z].
    do 4 zstep. seq_end.
  Qed.

  #[using="EB j1 j3 c24 c32 MI UNP RSH RER RSP ERR4 ERLO ERHI SPAHI FRA HE"] Lemma fail_seq_B : forall s4 : word,
    evtF asegs RNG (fail_post (Z_to_bv 64 ERR) s4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87a34) fc None m (seg_rom asegs)).
  Proof.
    intros s4. seq_start.
    zstep. ck_join_at UNP ERR 4%Z 0x87a40%Z [10%Z; 11%Z].
    do 4 zstep. seq_end.
  Qed.

  #[using="EB j1 j3 c24 c32 MI UNP RSH RER RSP ERR4 ERLO ERHI SPAHI FRA HE"] Lemma fail_seq_C : forall s4 : word,
    evtF asegs RNG (fail_post (Z_to_bv 64 ERR) s4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ERR) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87cb4) fc None m (seg_rom asegs)).
  Proof.
    intros s4. seq_start.
    err_recheck UNP ERR 0x87cc4%Z.
    do 4 zstep. seq_end.
  Qed.

  #[using="EB j1 j3 c24 c32 MI UNP RSH RER RSP ERR4 ERLO ERHI SPAHI FRA HE"] Lemma fail_seq_D : forall s3 : word,
    evtF asegs RNG (fail_post s3 (Z_to_bv 64 ERR))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 ERR) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8795c) fc None m (seg_rom asegs)).
  Proof.
    intros s3. seq_start.
    err_recheck UNP ERR 0x87a00%Z.
    do 4 zstep. seq_end.
  Qed.

  #[using="EB j1 j3 c24 c32 MI UNP RSH RER RSP ERR4 ERLO ERHI SPAHI FRA HE"] Lemma fail_seq_E : forall s3 : word,
    evtF asegs RNG (fail_post s3 (Z_to_bv 64 ERR))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 ERR) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x879f0) fc None m (seg_rom asegs)).
  Proof.
    intros s3. seq_start.
    err_recheck UNP ERR 0x87a00%Z.
    do 4 zstep. seq_end.
  Qed.
End FailSeq.

Section ChkFail.
  Context {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  (* [comment removed for export] *)
  Definition chk_fail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r26 r27 t3 t4 t5 t6 : word)
      (j1 j3 : list byte) (c24 c32 : word) (fcs : list cell) (k0 k1 k2 : word) (msg : list Z) (junk3 : list byte) (pcX : Z),
    chk_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    ((pcX = 0x87900 \/ pcX = 0x87a34 \/ pcX = 0x87cb4)%Z /\ r19 = Z_to_bv 64 ERR) \/ ((pcX = 0x8795c \/ pcX = 0x879f0)%Z /\ r20 = Z_to_bv 64 ERR) ->
    rw_cells asegs mm SPA [CB 24 j1; C8 c24; C8 c32; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                           C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 EB); CB 16 j3; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))]) -> cells_size fcs = 96%nat ->
    rw_cells asegs mm ERR [C4 z64] ->
    rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    implMG RNGx (fo_ret FO _ FF_CHECK_HEADER (CH_Err msg)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 r19 r20 r21 r22 r23 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 pcX) fc None mm (seg_rom asegs)).
  Section Sz6.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r26 r27 t3 t4 t5 t6 j1 j3 c24 c32 fcs k0 k1 k2 msg junk3 pcX : ltac2:(SecDiet.SzSec.tyM 'chk_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_fail__body : ltac2:(SecDiet.SzSec.bodyP 'chk_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET.
    intros CTX INV PCX FRA FRC Hfcs HE HEB LEN3 RNG3.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU. unfold chk_shadow in SHC.
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rw_cells_merge asegs _ _ [C8 k0; C8 k1; C8 k2] fcs [C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] FRC) as FRCm.
    rewrite Hfcs in FRCm. cbn [app] in FRCm. clear FRC.
    (* [comment removed for export] *)
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]. pose proof (Forall_inv FAll) as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll. change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR.
    pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _). band_ind FBAND' bF.
    assert (ICL : incl CL (CL ++ [])) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL ((FF_CHECK_HEADER, Fb, 128%Z) :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND| apply Forall_cons; [exact EBBAND| apply Forall_nil]]).
    band_ind ERBAND bE.
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL (incl_refl _)) ltac:(lia)) as (kM & kMr & kM1 & kM2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2).
    cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    apply (rng_fp_le _ _ _ _ FP) in RSTK.
    assert (RSPA : rng RNGx SPA 88) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AG FXB) as AGsh.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OERR G ICL IFL AGsh ltac:(lia)) as (_ & _ & _ & ERUNP & ERRNG & ERRSH & _).
    assert (FX : Forall (cobj_iv FL CL) [(ERR, ERR + 4)]%Z) by cobj_ivs.
    pose proof (munch_refl [(ERR, ERR + 4)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF.
    assert (SEQ : evtF asegs RNGx (fun ms' => exists m',
        ms' = MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 0) (Z_to_bv 64 1) a2 a3 a4 (Z_to_bv 64 Fb) a6 a7
                      r18 r19 r20 r21 r22 r23 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x87a50) fc None m' (seg_rom asegs)
        /\ munch [(ERR, ERR + 4)]%Z mm m' /\ wmono asegs mm m' /\ mem_inv asegs m' /\ rw_cells asegs m' ERR [C4 (Z_to_bv 64 1)])
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 r19 r20 r21 r22 r23 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 pcX) fc None mm (seg_rom asegs))).
    { destruct PCX as [([->|[->| ->]] & ->)|([->| ->] & ->)].
      - eapply fail_seq_A; eassumption || lia.
      - eapply fail_seq_B; eassumption || lia.
      - eapply fail_seq_C; eassumption || lia.
      - eapply fail_seq_D; eassumption || lia.
      - eapply fail_seq_E; eassumption || lia. }
    call SEQ.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m4 _) =>
      destruct (own_writes _ _ _ GL L RNGx sx CL [] FB FL [(FF_CHECK_HEADER, Fb, 128%Z)] mm m4 [] [(ERR, ERR + 4)]%Z (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G4 AG4];
      assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m4)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG4|]; intros a (K & (N1 & _)); split; [exact K|]; split; [exact N1| exact I])
    end.
    apply evtF_done.
    lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?m4 _) =>
      eapply (chk_exit FO GIOA TP fflagA GL FRET) with (fcs := [CB 96 (cells_bytes fcs)]) (r := CH_Err msg) (PB := []) (mm := m4);
        [ exact CTX | | eassumption | reflexivity | exact FRCm | reflexivity | eassumption | ] end.
    - unfold chk_inv, chk_shadow. split; [exact FP|]. split; [exact G4|]. split; [exact OF|]. repeat (split; [assumption|]). assumption.
    - cbn [chk_result]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists junk3; assumption|]. split; [exact LEN3| exact RNG3].
  Qed.
  End Sz6.
  Lemma chk_fail : ltac:(let t := eval cbv delta [chk_fail__stmt] in chk_fail__stmt in exact t).
  Proof using GL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r26 r27 t3 t4 t5 t6 j1 j3 c24 c32 fcs k0 k1 k2 msg junk3 pcX. ltac2:(SecDiet.SzSec.closeP 'chk_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkFail.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA.TwB.
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

(* [comment removed for export] *)
Ltac err_recheck UNP P OK :=
  zstep;
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of UNP with unpoisoned mm ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd mm lo hi P 4 UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P; pose proof (sval_range b) as SR end end;
  zstep; zstep;
  cbv beta delta [mkR];
  lazymatch goal with |- evtF ?segs ?RNGx ?Q (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    eapply (evtF_cut segs RNGx (fun ms' => ck_post [10%Z; 11%Z] (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv mm ro) R)) end;
  [ ck_arm OK 16%nat
  | let ms' := fresh "ms'" in let H := fresh "Hck" in
    intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; ck_clear ].

(* [comment removed for export] *)
Local Ltac ck_live OK pc := lazymatch constr:((OK, pc)) with (555480%Z, 555332%Z) => idtac | (555480%Z, 555480%Z) => idtac | (555480%Z, 556944%Z) => idtac | (555544%Z, 555236%Z) => idtac | (555544%Z, 555544%Z) => idtac | (555544%Z, 556964%Z) => idtac | (556188%Z, 556188%Z) => idtac | (556188%Z, 557160%Z) => idtac | (556824%Z, 556496%Z) => idtac | (556824%Z, 556608%Z) => idtac | (556824%Z, 556760%Z) => idtac | (556824%Z, 556824%Z) => idtac | (556824%Z, 557472%Z) => idtac | (556824%Z, 558152%Z) => idtac end.
Local Ltac ck_arm OK n ::=
  lazymatch n with
  | O => fail "ck_join: step budget exhausted before reaching the join point" OK
  | S ?n' =>
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 OK) _ _ _ _) =>
        apply evtF_done; lazymatch goal with |- ?q _ => tryif is_var q then unfold q else idtac end; cbn [ck_post]; repeat eexists; simp_regs;
        first [ reflexivity | fail 1 "ck_join: a register outside the clobber list changed before" OK ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; rewrite ?sxb_sval; ck_arm OK n'
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "Kck" in
        if_cases K; ck_zify K;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif ck_live OK pc then first [ ck_arm OK n' | exfalso; ck_lia ] else first [ exfalso; ck_lia | ck_arm OK n' ]
        | _ => first [ exfalso; ck_lia | ck_arm OK n' ]
        end
    end
  end.
(* [comment removed for export] *)
Local Ltac cjq_fold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQc" in pose (QQ := Q); change Q with QQ end).
Local Ltac ck_join_at UNP P N OK RS ::=
  ck_clear; cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
      let b := fresh "shb" in let RD := fresh "RDsh" in let CK := fresh "CKsh" in let SR := fresh "SRsh" in
      destruct (ck_part_rd m lo hi P N UNP ltac:(ck_lia) ltac:(ck_lia) ltac:(lia) ltac:(ck_lia)) as (b & RD & CK);
      ck_fp_at lo P;
      pose proof (sval_range b) as SR;
      eapply (evtF_cut segs RNG (fun ms' => ck_post RS (fun R' => ms' = MS R' F (Z_to_bv 64 OK) fc rv m ro) R));
      [ cjq_fold; ck_arm OK 16%nat
      | let ms' := fresh "ms'" in let H := fresh "Hck" in
        intros ms' H; cbn [ck_post] in H; destruct_exs H; subst ms'; simp_regs; clear RD CK SR; ck_clear; try clear b ]
    | unpoisoned ?m' _ _ => fail "ck_join: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Section CANSEC1. Context {rc : runConstT}.
Section FailSeq.
  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (RNG : footprint) (SPA ERR EB Fb : Z) (j1 j3 : list byte) (c24 c32 : word).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis UNP : unpoisoned m ERR (ERR + 4).
  Hypothesis RSH : rng RNG (shad (ERR - ERR mod 8)) (nshad (4 + ERR mod 8)).
  Hypothesis RER : rng RNG ERR 4.
  Hypothesis RSP : rng RNG SPA 88.
  Hypothesis ERR4 : (ERR mod 4 = 0)%Z.
  Hypothesis ERLO : (0x604000 <= ERR)%Z.
  Hypothesis ERHI : (ERR + 4 <= SPA)%Z.
  Hypothesis SPAHI : (SPA + 88 <= 2^47)%Z.
  Hypothesis FRA : rw_cells asegs m SPA [CB 24 j1; C8 c24; C8 c32; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                                         C8 (Z_to_bv 64 EB); C8 (Z_to_bv 64 ERR); CB 16 j3; C8 (Z_to_bv 64 Fb)].
  Hypothesis HE : rw_cells asegs m ERR [C4 z64].

  Local Notation fail_post x19 :=
    (fun ms' : machine_state => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 0) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 ERR) x19 s4 s5 s6 s7 (Z_to_bv 64 Fb) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x87f24) fc None m' (seg_rom asegs)
        /\ munch [(ERR, ERR + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' ERR [C4 (Z_to_bv 64 1)]).

  Local Ltac seq_start := pose proof (munch_refl [(ERR, ERR + 4)]%Z m) as MU; pose proof (wmono_refl asegs m) as WM.
  Local Ltac seq_end := apply evtF_done; eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; assumption.

  #[using="EB j1 j3 c24 c32 MI UNP RSH RER RSP ERR4 ERLO ERHI SPAHI FRA HE"] Lemma fail_seq_A : forall s3 : word,
    evtF asegs RNG (fail_post s3)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ERR) s3 s4 s5 s6 s7 (Z_to_bv 64 Fb) s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87dc4) fc None m (seg_rom asegs)).
  Proof.
    intros s3. seq_start.
    zstep. ck_join_at UNP ERR 4%Z 0x87f18%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="EB j1 j3 c24 c32 MI UNP RSH RER RSP ERR4 ERLO ERHI SPAHI FRA HE"] Lemma fail_seq_B : forall s3 : word,
    evtF asegs RNG (fail_post s3)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ERR) s3 s4 s5 s6 s7 (Z_to_bv 64 Fb) s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87f0c) fc None m (seg_rom asegs)).
  Proof.
    intros s3. seq_start.
    zstep. ck_join_at UNP ERR 4%Z 0x87f18%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="EB j1 j3 c24 c32 MI UNP RSH RER RSP ERR4 ERLO ERHI SPAHI FRA HE"] Lemma fail_seq_C : forall s3 : word,
    evtF asegs RNG (fail_post s3)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ERR) s3 s4 s5 s6 s7 (Z_to_bv 64 Fb) s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88194) fc None m (seg_rom asegs)).
  Proof.
    intros s3. seq_start.
    zstep. ck_join_at UNP ERR 4%Z 0x87f18%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  #[using="EB j1 j3 c24 c32 MI UNP RSH RER RSP ERR4 ERLO ERHI SPAHI FRA HE"] Lemma fail_seq_D : forall s3 : word,
    evtF asegs RNG (fail_post s3)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ERR) s3 s4 s5 s6 s7 (Z_to_bv 64 Fb) s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87e34) fc None m (seg_rom asegs)).
  Proof.
    intros s3. seq_start.
    zstep. ck_join_at UNP ERR 4%Z 0x87f18%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.

  (* [comment removed for export] *)
  #[using="EB j1 j3 c24 c32 MI UNP RSH RER RSP ERR4 ERLO ERHI SPAHI FRA HE"] Lemma fail_seq_E : forall s2 s8 : word,
    evtF asegs RNG (fail_post (Z_to_bv 64 Fb))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 Fb) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x87ec4) fc None m (seg_rom asegs)).
  Proof.
    intros s2 s8. seq_start.
    do 2 zstep.
    zstep. ck_join_at UNP ERR 4%Z 0x87f18%Z [10%Z; 11%Z].
    do 3 zstep. seq_end.
  Qed.
End FailSeq.

Section ChkFail.
  Context {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.

  (* [comment removed for export] *)
  Definition chk_fail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r24 r27 t3 t4 t5 t6 : word)
      (j1 j3 : list byte) (c24 c32 : word) (fcs : list cell) (k0 k1 k2 : word) (msg : list Z) (junk3 : list byte) (pcX : Z),
    chk_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
    chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic o m RNGx sx [] mm ->
    ((pcX = 0x87dc4 \/ pcX = 0x87f0c \/ pcX = 0x88194 \/ pcX = 0x87e34)%Z /\ r18 = Z_to_bv 64 ERR /\ r24 = Z_to_bv 64 Fb) \/ (pcX = 0x87ec4%Z /\ r19 = Z_to_bv 64 Fb) ->
    rw_cells asegs mm SPA [CB 24 j1; C8 c24; C8 c32; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                           C8 (Z_to_bv 64 EB); C8 (Z_to_bv 64 ERR); CB 16 j3; C8 (Z_to_bv 64 Fb)] ->
    rw_cells asegs mm Fb ([C8 k0; C8 k1; C8 k2] ++ fcs ++ [C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))]) -> cells_size fcs = 96%nat ->
    rw_cells asegs mm ERR [C4 z64] ->
    rw_cells asegs mm EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk3] ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    implMG RNGx (fo_ret FO _ FF_CHECK_HEADER (CH_Err msg)) sx
      (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 r19 r20 r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 pcX) fc None mm (seg_rom asegs)).
  Section Sz6.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r24 r27 t3 t4 t5 t6 j1 j3 c24 c32 fcs k0 k1 k2 msg junk3 pcX : ltac2:(SecDiet.SzSec.tyM 'chk_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_fail__body : ltac2:(SecDiet.SzSec.bodyP 'chk_fail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FRET.
 intros CTX INV PCX FRA FRC Hfcs HE HEB LEN3 RNG3.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU. unfold chk_shadow in SHC.
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rw_cells_merge asegs _ _ [C8 k0; C8 k1; C8 k2] fcs [C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] FRC) as FRCm.
    rewrite Hfcs in FRCm. cbn [app] in FRCm. clear FRC.
    (* [comment removed for export] *)
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]. pose proof (Forall_inv FAll) as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll. change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR.
    pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _). band_ind FBAND' bF.
    assert (ICL : incl CL (CL ++ [])) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL ((FF_CHECK_HEADER, Fb, 128%Z) :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND| apply Forall_cons; [exact EBBAND| apply Forall_nil]]).
    band_ind ERBAND bE.
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL (incl_refl _)) ltac:(lia)) as (kM & kMr & kM1 & kM2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2).
    cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    apply (rng_fp_le _ _ _ _ FP) in RSTK.
    assert (RSPA : rng RNGx SPA 88) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AG FXB) as AGsh.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OERR G ICL IFL AGsh ltac:(lia)) as (_ & _ & _ & ERUNP & ERRNG & ERRSH & _).
    assert (FX : Forall (cobj_iv FL CL) [(ERR, ERR + 4)]%Z) by cobj_ivs.
    pose proof (munch_refl [(ERR, ERR + 4)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF.
    assert (SEQ : evtF asegs RNGx (fun ms' => exists m',
        ms' = MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 0) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 ERR) r19 r20 r21 r22 r23 (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x87f24) fc None m' (seg_rom asegs)
        /\ munch [(ERR, ERR + 4)]%Z mm m' /\ wmono asegs mm m' /\ mem_inv asegs m' /\ rw_cells asegs m' ERR [C4 (Z_to_bv 64 1)])
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 r19 r20 r21 r22 r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 pcX) fc None mm (seg_rom asegs))).
    { destruct PCX as [([->|[->|[->| ->]]] & -> & ->)|(-> & ->)].
      - eapply fail_seq_A; eassumption || lia.
      - eapply fail_seq_B; eassumption || lia.
      - eapply fail_seq_C; eassumption || lia.
      - eapply fail_seq_D; eassumption || lia.
      - eapply fail_seq_E; eassumption || lia. }
    call SEQ.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m4 _) =>
      destruct (own_writes _ _ _ GL L RNGx sx CL [] FB FL [(FF_CHECK_HEADER, Fb, 128%Z)] mm m4 [] [(ERR, ERR + 4)]%Z (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G4 AG4];
      assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m4)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG4|]; intros a (K & (N1 & _)); split; [exact K|]; split; [exact N1| exact I])
    end.
    apply evtF_done.
    lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?m4 _) =>
      eapply (chk_exit FO GIOA TP fflagA GL FRET) with (fcs := [CB 96 (cells_bytes fcs)]) (r := CH_Err msg) (PB := []) (mm := m4);
        [ exact CTX | | eassumption | reflexivity | exact FRCm | reflexivity | eassumption | ] end.
    - unfold chk_inv, chk_shadow. split; [exact FP|]. split; [exact G4|]. split; [exact OF|]. repeat (split; [assumption|]). assumption.
    - cbn [chk_result]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists junk3; assumption|]. split; [exact LEN3| exact RNG3].
  Qed.
  End Sz6.
  Lemma chk_fail : ltac:(let t := eval cbv delta [chk_fail__stmt] in chk_fail__stmt in exact t).
  Proof using GL FRET. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m o RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r19 r20 r21 r22 r23 r24 r27 t3 t4 t5 t6 j1 j3 c24 c32 fcs k0 k1 k2 msg junk3 pcX. ltac2:(SecDiet.SzSec.closeP 'chk_fail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkFail.
End CANSEC1.
End TwB.
End F_sfchk_failA.

(* [comment removed for export] *)
Module F_sfchk_fillA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_gotA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfHandleA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfHandleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_sfchk_fsegA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
(* [comment removed for export] *)
Local Ltac oiv_lo_base k := lazymatch goal with |- (?lo0 <= ?lo)%Z /\ _ => d_split lo0 ltac:(fun X0 _ _ => d_split lo ltac:(fun X _ _ => constr_eq X0 X; k)) end.
Local Ltac oiv_orig :=
  first [ left; cbn [fst snd]; lia
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; lia ].
Local Ltac own_iv1 ::=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; oiv_lo_base ltac:(lia)
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; oiv_lo_base ltac:(lia)
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; oiv_lo_base ltac:(lia)
        | oiv_orig ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac seg_side1 := lazymatch goal with |- (_ <= _ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac | _ => eassumption end.
Ltac open_pcells := repeat match goal with HH : rw_cells _ _ _ (pcells _ _ _ _ _ _ _ _ _ _ _ _ _ _) |- _ => unfold pcells in HH end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section ChkFill.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis GOTL : gia_got_law GIOA.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.

  Definition chk_fill__stmt : Prop := chk_fill_stmt HO FO sites GIOA TP fflagA.
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 t3 t4 t5 t6 j1 j3 pre mid post ej k0 k1 k2 q P maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw : ltac2:(SecDiet.SzSec.tyM 'chk_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FRET GPL GOTL LT2DLT ADJSNAP MALLOC"] Lemma chk_fill__body : ltac2:(SecDiet.SzSec.bodyP 'chk_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros CTX INV MI3 Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 Z2 Z3 FRA FRC CELLS0 HE HEB.
    chk_setup GL CTX INV.
    assert (MIB : (2^31 <= mi < 2^32)%Z) by (unfold TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in MI3; lia).
    (* [comment removed for export] *)
    assert (HinPB : In (q, P, PCAP_SF_TOTAL) [(q, P, PCAP_SF_TOTAL)]) by (left; reflexivity).
    assert (HinP : In (q, P, PCAP_SF_TOTAL) ((CL ++ [(q, P, PCAP_SF_TOTAL)]) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; exact HinPB).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as ((PBAND & _ & PTOP & P16) & P0 & PUNP & PRNG & PRSH & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PUNP, PRNG, PRSH. unfold PCAP_SF_TOTAL in PBAND, PTOP, PUNP, PRNG, PRSH.
    band_ind PBAND bP.
    destruct (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G HinP (or_introl eq_refl) ltac:(cbn [cb_size snd]; unfold PCAP_SF_TOTAL; lia)) as (kPF & kPFr & kPF1 & kPF2).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kPF1, kPF2. unfold PCAP_SF_TOTAL in kPF1, kPF2.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; unfold PCAP_SF_TOTAL; lia)) as (kMP & kMPr & kMP1 & kMP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; unfold PCAP_SF_TOTAL; lia)) as (kEP & kEPr & kEP1 & kEP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) (incl_refl _) IFL) HinPB ltac:(lia) ltac:(cbn [cb_size snd]; unfold PCAP_SF_TOTAL; lia)) as (kBP & kBPr & kBP1 & kBP2).
    cbn [cb_addr cb_size fst snd] in kMP1, kMP2, kEP1, kEP2, kBP1, kBP2. unfold PCAP_SF_TOTAL in kMP1, kMP2, kEP1, kEP2, kBP1, kBP2.
    assert (PBK : pblk_ok RNGx SPA P Fb bP kPF).
    { unfold pblk_ok. split; [exact PRNG|]. split; [exact PRSH|]. split; [eapply rng_sub'; [exact RSPA| lia]|]. split; [exact FRNG|]. split; [exact RIMG|].
      atop_facts. repeat (split; [first [assumption | lia]|]). first [assumption | lia]. }
    assert (SPALO : (17594333495296 <= SPA)%Z) by (atop_facts; lia).
    assert (HOK : hdrf_ok mi maj min n0 n1 n2 n3 l0 l1 l2 l3) by (unfold hdrf_ok; repeat (split; [assumption|]); assumption).
    apply blank_recell in CELLS0. rename CELLS0 into CELLS.
    (* [comment removed for export] *)
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as (RT0 & _).
    pose proof (gia_global_unp FO GIOA fflagA GL _ _ _ _ _ _ _ 0x22000%Z 28%Z G ltac:(unfold client_globals; repeat (first [left; reflexivity | right]))) as LTUNP.
    pose proof (GOTL _ _ _ _ _ _ _ G) as GOT. unfold GOT_PCAP_ADDR in GOT.
    (* [comment removed for export] *)
    unfold chk_fill_model. cbn [e_fret prims]. rewrite (land_ffff l0 l1 l2 l3) by lia.
    unfold PCAP_TSTAMP_PRECISION_MICRO. cbn [Z.eqb mo_bind mo_ret MOps e_malloc e_free prims].
    set (lt := linktype_to_dlt (l0 + 256 * l1)). set (snap := pcapint_adjust_snapshot lt (le4val n0 n1 n2 n3)).
    pose proof (linktype_to_dlt_range (l0 + 256 * l1) ltac:(lia)) as LTR. fold lt in LTR.
    pose proof (adjust_snapshot_range lt (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as SNR. fold snap in SNR. unfold INT_MAX in SNR.
    set (EXT := s32 (Z.land (le4val l0 l1 l2 l3) 4294901760)).
    set (POSTQ := check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR [mg0; mg1; mg2; mg3] f m (ps_outfile s)).
    pose proof (munch_refl [(bv_unsigned sp - 57344, bv_unsigned sp); (P, P + 664)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF.
    (* [comment removed for export] *)
    call fill_seg1; [eassumption .. | ]. open_pcells.
    (* [comment removed for export] *)
    assert (FWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv)%Z [(bv_unsigned sp - 57344, bv_unsigned sp); (P, P + 664)]%Z)
      by (repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; lia|]); apply Forall_nil).
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (LT2DLT _ spa) with (lo := lo) (lt := (l0 + 256 * l1)%Z);
        [ assumption | rewrite Hspa; exact ST | rewrite Hspa; lia | lia | exact (LibcKit.artcells_munch _ _ _ RT0 MU WM FWI) | exact LTUNP
        | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH | reflexivity | lia ]
      | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. destruct PO as (-> & MUc & WMc & MIc & STc & ->).
    rewrite Hspa in *.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
    try clear ST. rename STc into ST.
    replace (ret_pc (Z_to_bv 64 555960)) with (Z_to_bv 64 555960) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    fold lt. clear Hspa. subst spa.
    (* [comment removed for export] *)
    call fill_seg2; [eassumption .. | ]. open_pcells.
    (* [comment removed for export] *)
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (ADJSNAP _ spa) with (lo := lo) (lt := lt) (snaplen := le4val n0 n1 n2 n3);
        [ assumption | rewrite Hspa; exact ST | reflexivity | lia | reflexivity | unfold le4val; lia ]
      | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. destruct PO as (-> & MUc & WMc & MIc & STc & ->).
    rewrite Hspa in *.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end; clear MUc WMc.
    try clear ST. rename STc into ST.
    replace (ret_pc (Z_to_bv 64 556044)) with (Z_to_bv 64 556044) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    fold snap. clear Hspa. subst spa.
    (* [comment removed for export] *)
    call fill_seg3; [eassumption .. | ]. open_pcells.
    call fill_seg4; [eassumption .. | ]. open_pcells.
    call fill_segL; [eassumption .. | ]. open_pcells.
    call fill_segH; [seg_side1 .. | ]; [lia .. | ]. open_pcells.
    destruct (fill_hs_ss_range mi lt snap SNR) as (SSR & HSR).
    (* [comment removed for export] *)
    call fill_segB; [seg_side1 .. | ]; [lia .. | ]. open_pcells.
    lazymatch goal with HH : rw_cells asegs _ SPA _ |- _ => rename HH into FRA1 end.
    lazymatch goal with HH : rw_cells asegs _ P _ |- _ => rename HH into CELLS end.
    (* [comment removed for export] *)
    set (HS := fst (fill_hs_ss mi lt snap)) in *. set (SS := snd (fill_hs_ss mi lt snap)) in *.
    set (BS := (if 2048 <? SS then 2048 else SS)%Z) in *.
    assert (BSR : (1 <= BS <= 2048)%Z) by (subst BS; destruct (Z.ltb_spec 2048 SS); lia).
    replace (chk_sf_model MOps (prims HO FO sites) q f 0 mi sw maj min lt EXT snap
               (if (maj =? 2)%Z then if (min <? 3)%Z then SWAPPED else if (min =? 3)%Z then MAYBE_SWAPPED else NOT_SWAPPED
                else if (maj =? 543)%Z then SWAPPED else NOT_SWAPPED)
               (if (mi =? NSEC_TCPDUMP_MAGIC)%Z then SF_SCALE_DOWN else SF_PASS_THROUGH))
      with (chk_buf_model MOps (prims HO FO sites) q f 0 sw maj min lt EXT HS SS (fill_lensw maj min) (fill_scale mi))
      by (unfold chk_sf_model, HS, SS, fill_hs_ss, fill_lensw, fill_scale; destruct (mi =? KUZNETZOV_TCPDUMP_MAGIC)%Z; reflexivity).
    unfold chk_buf_model. fold BS. cbn [e_malloc e_fret e_free prims mo_bind mo_ret MOps].
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] [(q, P, PCAP_SF_TOTAL)] (bv_unsigned sp))
                   [(bv_unsigned sp - 57344, bv_unsigned sp); (P, P + 664)]%Z) by (unfold PCAP_SF_TOTAL; own_ivs).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mx _ [] _ FW (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGm5 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mx)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I]);
      assert (UC5 : ucallerA (depth_check_header false) L mx sp s0 ra trC)
        by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha;
            destruct (AGm5 a ltac:(lia) ltac:(split; [left; lia| cbn [outside fst snd]; lia])) as [E1 _]; congruence)
    end.
    pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FR eq_refl) as BRA.
    cbn [firstn cells_size csize Nat.add] in BS0, BRA.
    replace (bv_unsigned sp + -104 + Z.of_nat 88)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
    replace (bv_unsigned sp + -104 + Z.of_nat 96)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (MALLOC _ spa) with (L := L) (s := sx) (CL := CL ++ [(q, P, PCAP_SF_TOTAL)]) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (n := BS);
        [ split; [exact G5|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold MALLOC_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | reflexivity | lia
        | eapply (unw_of_ucaller (pred (depth_check_header false)));
            [ eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x87ecc%Z UC5); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_pcap_check_header; cbn; lia]
            | unfold ACLIENT_LO, ACLIENT_HI, AMALLOC_PC; lia
            | rewrite Hspa; lia
            | rewrite unsigned_lit by lia; unfold traces_check_header, traces_pcap_check_header in TR; destruct TR as (_ & _ & _ & _ & _ & T6 & _); exact T6
            | exact RSTK ] ]. }
    intros r s2' RNG2 ms' PO. cbv beta in PO. destruct PO as (FP2 & av & m6 & E & OF6 & MI6 & ST6 & AG6 & PO).
    destruct r as [qb|]; [|destruct PO]. destruct PO as (B & bjunk & -> & G6 & BUF).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 556748)) with (Z_to_bv 64 556748) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [app] in AG6.
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    pose proof (pblk_ok_fp_le _ _ _ _ _ _ _ FP2 PBK) as PBK2.
    lazymatch type of AG6 with agrees_on _ ?m5 _ =>
      assert (KST : forall A cs, rw_cells asegs m5 A cs -> (SPA <= A)%Z -> rw_cells asegs m6 A cs)
        by (intros A cs HC HA; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha; left; lia);
      assert (KFR : forall A cs, rw_cells asegs m5 A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 128)%Z -> rw_cells asegs m6 A cs)
        by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha;
            right; right; left; apply in_frames_In; exists (FF_CHECK_HEADER, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]);
      assert (KOB : forall A n cs, rw_cells asegs m5 A cs -> clocA FL CL A n -> Z.of_nat (cells_size cs) = n -> rw_cells asegs m6 A cs)
        by (intros A n cs HC LOC HSz; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha;
            eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia])
    end.
    apply KST in FR; [|lia]. apply KST in FRA1; [|lia].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in CELLS;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; left; apply in_block_app; right; apply in_block_In; exists (q, P, PCAP_SF_TOTAL);
        split; [left; reflexivity| cbn [cb_addr cb_size fst snd]; unfold PCAP_SF_TOTAL; lia]].
    apply (agrees_stk _ _ _ _ _ AG6) in STG; [|intros a Ha; left; lia].
    apply KFR in FRC; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in SHC;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; right; right; apply in_frame_sh_In; exists (FF_CHECK_HEADER, Fb, 128%Z);
        split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]].
    apply (KOB _ 4%Z) in HE; [|exact (proj1 OERR)|reflexivity].
    apply (KOB _ 256%Z) in HEB; [|exact (proj1 OEB)|reflexivity].
    apply (KOB _ 4%Z) in MGc; [|exact (proj1 OMG)|reflexivity].
    clear KST KFR KOB.
    (* [comment removed for export] *)
    assert (G6' : GIOA L RNG2 s2' (CL ++ [(q, P, PCAP_SF_TOTAL); (qb, B, BS)]) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) m6).
    { eapply GPL; [exact G6|]. replace (CL ++ [(q, P, PCAP_SF_TOTAL); (qb, B, BS)]) with ((CL ++ [(q, P, PCAP_SF_TOTAL)]) ++ [(qb, B, BS)])
        by (rewrite <- app_assoc; reflexivity). apply Permutation.Permutation_cons_append. }
    assert (HinP6 : In (q, P, PCAP_SF_TOTAL) ((CL ++ [(q, P, PCAP_SF_TOTAL); (qb, B, BS)]) ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB6 : In (qb, B, BS) ((CL ++ [(q, P, PCAP_SF_TOTAL); (qb, B, BS)]) ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G6' HinP6) as (_ & _ & PUNP6 & _).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G6' HinB6) as ((_ & _ & BTOP & _) & B0 & _).
    cbn [cb_addr cb_size fst snd] in PUNP6, BTOP, B0. unfold PCAP_SF_TOTAL in PUNP6.
    pose proof (GOTL _ _ _ _ _ _ _ G6') as GOT6. unfold GOT_PCAP_ADDR in GOT6.
    assert (BR : (0 < B < 2^64)%Z) by (atop_facts; lia).
    assert (APB : exists k, (0 <= k <= 1 /\ P + 664 <= B + k * 18446744073709551616 /\ B + BS <= P + (1 - k) * 18446744073709551616)%Z).
    { pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G6') as BA.
      apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & BA & _).
      cbn [blocks_apart] in BA. destruct BA as (F1 & _). pose proof (Forall_inv F1) as A12.
      unfold apart, cb_addr, cb_size, PCAP_SF_TOTAL in A12; cbn [fst snd] in A12. atop_facts.
      destruct A12 as [D|D]; [exists 0%Z | exists 1%Z]; lia. }
    destruct APB as (kPB & kPBr & kPB1 & kPB2).
    pose proof (munch_refl [(P, P + 664)]%Z m6) as MU6. pose proof (wmono_refl asegs m6) as WM6.
    (* [comment removed for export] *)
    apply implMG_from_evtF.
    call fill_segE; [seg_side1 .. | ]; [lia .. | ]. open_pcells.
    lazymatch goal with HH : rw_cells asegs _ P _ |- _ => rename HH into CELLS7 end.
    (* [comment removed for export] *)
    assert (FW7 : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] [(q, P, PCAP_SF_TOTAL); (qb, B, BS)] (bv_unsigned sp)) [(P, P + 664)]%Z)
      by (unfold PCAP_SF_TOTAL; own_ivs).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m7 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m7 _ [] _ FW7 (Forall_nil _) G6' MU6 WM6 ltac:(lia)) as [G7 AG7];
      assert (AGm7 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m7)
        by (eapply agrees_on_trans; [exact AGm5|]; eapply agrees_on_trans;
            [ eapply (keeps_callee0 (CL ++ [(q, P, PCAP_SF_TOTAL)]) (FF_CHECK_HEADER, Fb, 128%Z) FL _ _ CL (bv_unsigned sp) SPA); [exact ICL| lia| exact AG6]
            | eapply agrees_on_weaken; [exact AG7|]; intros a (K & _); split; [exact K| exact I] ])
    end.
    apply evtF_done. subst POSTQ.
    pose proof (s32_range (Z.land (le4val l0 l1 l2 l3) 4294901760)) as EXR. fold EXT in EXR.
    lazymatch goal with |- implMG _ (fo_ret _ _ _ (CH_Ok ?pp)) _ _ (MS _ _ _ _ _ ?m7 _) =>
      eapply (chk_exit FO GIOA TP fflagA GL FRET) with (mm := m7) (PB := [(q, P, PCAP_SF_TOTAL); (qb, B, BS)]) (r := CH_Ok pp)
             (fcs := [CB 8 pre; C4 (Z_to_bv 64 (mi + (2^64 - 2^32))); C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid;
                      C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3)); CB 64 post]);
        [ exact CTX | | exact FRA1 | reflexivity | exact FRC | reflexivity | exact HE | ] end.
    - unfold chk_inv, chk_shadow. split; [eapply fp_le_trans; [exact FP| exact FP2]|]. split; [exact G7|]. split; [congruence|].
      repeat (split; [assumption|]). assumption.
    - cbn [chk_result]. exists P. split; [reflexivity|]. split; [| split; [reflexivity| exists ej; exact HEB]].
      exists z8, z8, z8. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists B, 0%Z, blank_junk, [], bjunk.
      destruct (rw_cells_cut _ _ _ 33 CELLS7) as [CP CQ]. cbn [firstn skipn cells_size csize Nat.add] in CP, CQ.
      split; [unfold pcap_blocks, psize, is_ng; cbn [pc_priv pc_self pc_buffer pc_bufalloc]; reflexivity|].
      split. { unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, PK, blank_junk.
               cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_next_pcap pk_cleanup_sf
                    pc_priv pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                    pc_tstamp_precision pc_header h_sec h_usec h_caplen h_len hdr0].
               exact CP. }
      split. { unfold priv_cells, PCAP_PRIV_OFF. cbn [pc_priv sf_cells sf_hdrsize sf_lengths_swapped sf_scale_type].
               replace (P + 648)%Z with (P + Z.of_nat 648)%Z by lia. exact CQ. }
      split; [exact BUF|]. split; [reflexivity|]. split; [reflexivity|].
      unfold pcap_wf. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                            pc_linktype pc_linktype_ext pc_header pc_priv h_caplen h_len hdr0 sf_hdrsize length Z.of_nat].
      unfold INT_MAX. repeat split; try lia.
  Qed.
  End Sz1.
  #[using="GL FRET GPL GOTL LT2DLT ADJSNAP MALLOC"] Lemma chk_fill : ltac:(let t := eval cbv delta [chk_fill__stmt] in chk_fill__stmt in exact t).
  Proof. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 t3 t4 t5 t6 j1 j3 pre mid post ej k0 k1 k2 q P maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw. ltac2:(SecDiet.SzSec.closeP 'chk_fill__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkFill.
End CANSEC1.
End F_sfchk_fillA.

(* [comment removed for export] *)
Module F_sfchk_hdrA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_failA.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section ChkHdr.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis OPEN_COMMON : open_offline_common_stmt HO FO sites GIOA TP.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis CHK_FILL : chk_fill_stmt HO FO sites GIOA TP fflagA.

  Definition chk_hdr__stmt : Prop := chk_hdr_stmt HO FO sites GIOA TP fflagA.
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r19 t3 t4 t5 t6 j1 j3 pre mid post ej k0 k1 k2 maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw : ltac2:(SecDiet.SzSec.tyM 'chk_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_hdr__body : ltac2:(SecDiet.SzSec.bodyP 'chk_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CHK_FILL FRET GL GPL OPEN_COMMON SNPRINTF.
    intros CTX INV MI3 Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 FRA FRC1 HD FRC2 HE HEB.
    chk_setup GL CTX INV.
    assert (MIB : (2^31 <= mi < 2^32)%Z) by (unfold TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in MI3; lia).
    (* [comment removed for export] *)
    pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HD FRC2 ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC.
    cbn [app] in FRC. clear FRC1 HD FRC2.
    (* [comment removed for export] *)
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND'| apply Forall_cons; [exact EBBAND'| apply Forall_nil]]).
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AG FXB) as AGsh.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G ICL IFL AGsh ltac:(lia)) as OEBm.
    assert (OEB' : cobjA RNGx mm ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) (CL ++ []) EB 256)
      by (split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEBm) ICL IFL)| exact (proj2 OEBm)]).
    assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(bv_unsigned sp - 57344, bv_unsigned sp)]%Z) by own_ivs.
    assert (FX : Forall (cobj_iv FL CL) [(EB, EB + 256)]%Z) by cobj_ivs.
    unfold chk_rest2. cbn [e_fret prims].
    set (POSTQ := check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR [mg0; mg1; mg2; mg3] f m (ps_outfile s)).
    (* [comment removed for export] *)
    assert (KSNP : forall (ra5 t0' t1' t2' a3' a4' a5' a6' a7' r18' r22' r26' t3' t4' t5' t6' : word) (FMTA : Z) (fs : string) (args : list farg),
      (ra5 = Z_to_bv 64 0x87900 \/ ra5 = Z_to_bv 64 0x87a34) ->
      fmt_at mm FMTA fs -> fmt_ok fs args = true -> (length args <= 2)%nat ->
      Forall2 (farg_word true L RNGx ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) (CL ++ []) SPA EB 256 mm) args (firstn (length args) [a3'; a4']) ->
      (length (Fmt.snprintf 256 fs args) <= 255)%nat -> items_okb (fmt fs) = true -> Forall arg_ok args ->
      evtF asegs RNGx (fun ms' => implMG RNGx (fo_ret FO _ FF_CHECK_HEADER (CH_Err (Fmt.snprintf 256 fs args))) sx POSTQ ms')
        (MS (mkR ra5 (Z_to_bv 64 SPA) gp tp t0' t1' t2' sp (Z_to_bv 64 SPA) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 r18' (Z_to_bv 64 ERR) (Z_to_bv 64 ERR) (Z_to_bv 64 (mi + (2^64 - 2^32))) r22' (Z_to_bv 64 (Fb + 32))
                 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r26' (Z_to_bv 64 2147450880) t3' t4' t5' t6')
            F (Z_to_bv 64 SNPRINTF_ENTRY) fc None mm (seg_rom asegs))).
    { intros ra5 t0' t1' t2' a3' a4' a5' a6' a7' r18' r22' r26' t3' t4' t5' t6' FMTA fs args Hra FMT5 FOK LA FWA LEN IOK AOK.
      pose proof (munch_refl [(bv_unsigned sp - 57344, bv_unsigned sp); (EB, EB + 256)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      eapply evtF_cut;
        [ eapply SNPRINTF with (L := L) (s := sx) (CL := CL ++ []) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (DST := EB) (n := 256%Z)
                               (FMTA := FMTA) (fs := fs) (args := args) (junk := ej);
          [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | lia
          | rewrite Hspa; replace (firstn (length args) [a3'; a4'; a5']) with (firstn (length args) [a3'; a4'])
              by (clear - LA; destruct args as [|? [|? [|? ?]]]; cbn in LA |- *; first [reflexivity | lia]); exact FWA
          | exact HEB | exact OEB' ]
        | ].
      cbv beta; intros ms' PO; destruct PO as (vav5 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
      unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
      unfold STDIO_STACK in MU6.
      lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end; clear MU6 WM6.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m6 _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m6 _ _ _ FW FX G MU WM ltac:(lia)) as [G6 AG6];
        assert (AGm6 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m6)
          by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG6|]; intros a (K & (_ & QN & _)); split; [exact K|]; split; [exact QN| exact I])
      end.
      change (Z.to_nat 256) with 256%nat in HEB6.
      replace (256 - length (Fmt.snprintf 256 fs args) - 1)%nat with (255 - length (Fmt.snprintf 256 fs args))%nat in HEB6 by lia.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m6 _) =>
        assert (INV6 : chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNGx sx [] m6)
          by (unfold chk_inv, chk_shadow; split; [exact FP|]; split; [exact G6|]; split; [exact OF|]; repeat (split; [assumption|]); assumption) end.
      apply evtF_done. subst POSTQ.
      destruct Hra as [-> | ->].
      1: replace (ret_pc (Z_to_bv 64 0x87900)) with (Z_to_bv 64 0x87900) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      2: replace (ret_pc (Z_to_bv 64 0x87a34)) with (Z_to_bv 64 0x87a34) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      all: lazymatch goal with |- implMG _ _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?m6 _) =>
        eapply (chk_fail FO GIOA TP fflagA GL FRET) with (mm := m6) (pcX := pc) (msg := Fmt.snprintf 256 fs args)
               (fcs := [CB 8 pre; C4 (Z_to_bv 64 (mi + (2^64 - 2^32))); C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid;
                        C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3)); CB 64 post]);
          [ exact CTX | exact INV6 | left; split; [first [left; reflexivity | right; left; reflexivity] | reflexivity]
          | exact FRA | exact FRC | reflexivity | exact HE | exact HEB6 | lia | apply snprintf_ok; [exact IOK| exact AOK] ] end. }
    (* [comment removed for export] *)
    assert (KVER : forall (a0' a1' : word),
      evtF asegs RNGx (fun ms' => implMG RNGx (fo_ret FO _ FF_CHECK_HEADER (CH_Err (Msg.unsupported_pcap_version maj min))) sx POSTQ ms')
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0' a1' a2 (Z_to_bv 64 maj) a4 a5 a6 a7 r18 (Z_to_bv 64 ERR)
                 (Z_to_bv 64 ERR) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 (Fb + 36)) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x87a1c) fc None mm (seg_rom asegs))).
    { intros a0' a1'.
      assert (MSG : fmt_at mm 0x21c40 "unsupported pcap savefile version %u.%u"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x21c40 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "unsupported pcap savefile version %u.%u"%string) ++ [Z_to_bv 8 0])
                                MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      zstep. rewrite ?zx16_lit by lia.
      do 4 zstep.
      zstep.
      unfold Msg.unsupported_pcap_version, PCAP_ERRBUF_SIZE.
      eapply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [AInt maj; AInt min]); [right; reflexivity | exact MSG | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
      { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
      pose proof (snprintf_length_le 256 "unsupported pcap savefile version %u.%u"%string [AInt maj; AInt min] ltac:(lia)) as LS. lia. }
    (* [comment removed for export] *)
    assert (KOK : forall (a0' a1' : word),
      evtF asegs RNGx (fun ms' => implMG RNGx
                   (if negb (Z.land (le4val l0 l1 l2 l3) 67043328 =? 0)
                    then fo_ret FO _ FF_CHECK_HEADER (CH_Err (Msg.reserved_not_zero (Z.land (le4val l0 l1 l2 l3) 67043328)))
                    else mo_bind MOps (pcapint_open_offline_common MOps (prims HO FO sites) PCAP_SF_TOTAL)
                           (fun r => match r with
                                     | inl m0 => fo_ret FO _ FF_CHECK_HEADER (CH_Err m0)
                                     | inr self => chk_fill_model MOps (prims HO FO sites) self f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)
                                     end)) sx POSTQ ms')
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0' a1' a2 (Z_to_bv 64 maj) a4 a5 a6 a7 r18 (Z_to_bv 64 ERR)
                 (Z_to_bv 64 ERR) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 (Fb + 36)) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x878d8) fc None mm (seg_rom asegs))).
    { intros a0' a1'. rewrite (reserved_val l0 l1 l2 l3) by lia.
      zstep. rewrite (sx32_lit l0 l1 l2 l3) by lia. do 2 zstep.
      rewrite (reserved_wordA l0 l1 l2 l3) by lia.
      zstep.
      destruct (Z.eq_dec ((l2 + 256 * (l3 mod 4)) * 65536) 0) as [RZ|RZ].
      2:{ (* [comment removed for export] *)
        replace ((l2 + 256 * (l3 mod 4)) * 65536 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact RZ). cbn [negb].
        if_cases KR; [zify_cond KR; exfalso; lia|].
        assert (MSG : fmt_at mm 0x21ca0 "savefile linktype reserved field not zero (0x%08x)"%string)
          by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x21ca0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "savefile linktype reserved field not zero (0x%08x)"%string) ++ [Z_to_bv 8 0])
                                  MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
              split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
        do 5 zstep.
        zstep.
        unfold Msg.reserved_not_zero, PCAP_ERRBUF_SIZE.
        eapply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [AInt ((l2 + 256 * (l3 mod 4)) * 65536)]); [left; reflexivity | exact MSG | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints1].
        { cbn [length firstn]. constructor; [reflexivity| constructor]. }
        pose proof (snprintf_length_le 256 "savefile linktype reserved field not zero (0x%08x)"%string [AInt ((l2 + 256 * (l3 mod 4)) * 65536)] ltac:(lia)) as LS. lia. }
      (* [comment removed for export] *)
      replace ((l2 + 256 * (l3 mod 4)) * 65536 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact RZ). cbn [negb].
      rewrite RZ. if_true.
      do 4 zstep.
      zstep.
      (* [comment removed for export] *)
      pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FR eq_refl) as BRA.
      cbn [firstn cells_size csize Nat.add] in BS0, BRA.
      replace (bv_unsigned sp + -104 + Z.of_nat 88)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
      replace (bv_unsigned sp + -104 + Z.of_nat 96)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
      assert (UC3 : ucallerA (depth_check_header false) L mm sp s0 ra trC).
      { eapply ucaller_keep; [exact UC| lia|]. intros a Ha.
        destruct (AG a ltac:(lia) ltac:(split; [left; lia| cbn [outside fst snd]; lia])) as [E1 _]. congruence. }
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      apply evtF_done. eapply implMG_bind.
      { eapply (OPEN_COMMON _ spa) with (L := L) (s := sx) (CL := CL ++ []) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (EB := EB) (total := PCAP_SF_TOTAL) (ej := ej);
          [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold PCAP_L1B_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x87b4c%Z UC3); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_open_offline_common, depth_check_header, depth_pcap_check_header; lia]
          | rewrite unsigned_lit by lia; unfold traces_check_header, traces_pcap_check_header in TR; destruct TR as (_ & T2 & _); exact T2
          | unfold frames_open_offline_common; apply nofr_cons; [eapply nofr_sub; [exact NF| intros ff Hf; cbn in Hf |- *; clear - Hf; intuition]| cbn; clear; intuition congruence]
          | reflexivity | reflexivity | reflexivity | left; reflexivity | exact HEB | exact OEB' | exact EB8 ]. }
      intros r s1' RNG1 ms' PO. unfold open_common_post in PO. destruct PO as (FP1 & av & m1 & E & OF1 & MI1 & ST1 & AG1 & PO).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
      replace (ret_pc (Z_to_bv 64 555852)) with (Z_to_bv 64 555852) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in AG1.
      (* [comment removed for export] *)
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
      assert (KST : forall A cs, rw_cells asegs mm A cs -> (SPA <= A)%Z -> rw_cells asegs m1 A cs).
      { intros A cs HC HA. eapply agrees_rw_cells; [exact AG1| exact HC|]. intros a Ha. split; [left; lia| lia]. }
      assert (KFR : forall A cs, rw_cells asegs mm A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 128)%Z -> rw_cells asegs m1 A cs).
      { intros A cs HC H1 H3. eapply agrees_rw_cells; [exact AG1| exact HC|]. intros a Ha. split; [|lia].
        right; right; left. apply in_frames_In. exists (FF_CHECK_HEADER, Fb, 128%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
      assert (KOB : forall A n cs, rw_cells asegs mm A cs -> clocA FL CL A n -> Z.of_nat (cells_size cs) = n ->
                     (A + n <= EB \/ EB + 256 <= A)%Z -> rw_cells asegs m1 A cs).
      { intros A n cs HC LOC HS HD. eapply agrees_rw_cells; [exact AG1| exact HC|]. intros a Ha. split; [|lia].
        eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]. }
      apply KST in FR; [|lia]. apply KST in FRA; [|lia].
      apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; split; [left; lia| lia]].
      apply KFR in FRC; [|lia|cbn [cells_size csize Nat.add]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AG1) in SHC;
        [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [|lia]; right; right; right; apply in_frame_sh_In; exists (FF_CHECK_HEADER, Fb, 128%Z);
          split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]].
      apply (KOB _ 4%Z) in HE; [|exact (proj1 OERR)|reflexivity|lia].
      apply (KOB _ 4%Z) in MGc; [|exact (proj1 OMG)|reflexivity|lia].
      assert (AGm1 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m1).
      { eapply agrees_on_trans; [exact AG|]. eapply (keeps_callee FO GIOA fflagA GL); [exact G| exact ICL| | | exact AG1|].
        - lia. - lia. - intros a _ QO _. cbn [outside fst snd] in QO. lia. }
      assert (INV1 : forall PB1, GIOA L RNG1 s1' (CL ++ PB1) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) m1 ->
                chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG1 s1' PB1 m1).
      { intros PB1 GX. unfold chk_inv, chk_shadow. split; [eapply fp_le_trans; [exact FP| exact FP1]|]. split; [exact GX|]. split; [congruence|].
        repeat (split; [assumption|]). assumption. }
      clear KST KFR KOB.
      destruct r as [msg|q].
      - (* [comment removed for export] *)
        destruct PO as (junk1 & -> & G1 & HEB1 & LEN1 & MSG1).
        apply implMG_from_evtF. zstep. if_true.
        apply evtF_done. subst POSTQ.
        eapply (chk_fail FO GIOA TP fflagA GL FRET) with (mm := m1) (pcX := 0x87cb4%Z) (msg := msg)
               (fcs := [CB 8 pre; C4 (Z_to_bv 64 (mi + (2^64 - 2^32))); C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid;
                        C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3)); CB 64 post]);
          [ exact CTX | apply INV1; exact G1 | left; split; [right; right; reflexivity | reflexivity]
          | exact FRA | exact FRC | reflexivity | exact HE | exact HEB1 | exact LEN1 | exact MSG1 ].
      - (* [comment removed for export] *)
        destruct PO as (P & -> & G1 & CELLS & HEB1).
        destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 ltac:(left; reflexivity)) as ((_ & _ & PTOP & _) & P0 & _).
        cbn [cb_addr cb_size fst snd] in PTOP, P0.
        assert (PR : (0 < P < 2^64)%Z) by (atop_facts; unfold PCAP_SF_TOTAL in PTOP; lia).
        apply implMG_from_evtF. zstep. if_false_by (eqz_false P PR).
        apply evtF_done. subst POSTQ.
        eapply (CHK_FILL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m RNG1 s1' m1)
          with (q := q) (P := P) (mi := mi) (sw := sw) (maj := maj) (min := min) (n0 := n0) (n1 := n1) (n2 := n2) (n3 := n3) (l0 := l0) (l1 := l1) (l2 := l2) (l3 := l3);
          [ exact CTX
          | apply INV1; eapply GPL; [exact G1|]; rewrite app_nil_r; apply Permutation.Permutation_cons_append
          | exact MI3 | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia
          | clear - RZ L2 L3; Z.div_mod_to_equations; lia | clear - RZ L2 L3; Z.div_mod_to_equations; lia
          | exact FRA | exact FRC | exact CELLS | exact HE | exact HEB1 ]. }
    (* [comment removed for export] *)
    apply implMG_from_evtF.
    zstep. rewrite ?zx16_lit by lia.
    do 2 zstep.
    if_cases K543; zify_cond K543.
    - zstep. rewrite ?zx16_lit by lia. do 2 zstep.
      if_cases KM0; zify_cond KM0.
      + (* [comment removed for export] *)
        replace (negb ((maj =? 2) && (min <=? 4) || (maj =? 543) && (min =? 0)))%Z with false
          by (symmetry; destruct (Z.eqb_spec maj 2), (Z.leb_spec min 4), (Z.eqb_spec maj 543), (Z.eqb_spec min 0); cbn; first [reflexivity | lia]).
        eapply KOK.
      + replace (negb ((maj =? 2) && (min <=? 4) || (maj =? 543) && (min =? 0)))%Z with true
          by (symmetry; destruct (Z.eqb_spec maj 2), (Z.leb_spec min 4), (Z.eqb_spec maj 543), (Z.eqb_spec min 0); cbn; first [reflexivity | lia]).
        eapply KVER.
    - do 3 zstep.
      if_cases K2; zify_cond K2.
      + replace (negb ((maj =? 2) && (min <=? 4) || (maj =? 543) && (min =? 0)))%Z with true
          by (symmetry; destruct (Z.eqb_spec maj 2), (Z.leb_spec min 4), (Z.eqb_spec maj 543), (Z.eqb_spec min 0); cbn; first [reflexivity | lia]).
        eapply KVER.
      + zstep. rewrite ?zx16_lit by lia. do 2 zstep.
        if_cases K5; zify_cond K5.
        * replace (negb ((maj =? 2) && (min <=? 4) || (maj =? 543) && (min =? 0)))%Z with true
          by (symmetry; destruct (Z.eqb_spec maj 2), (Z.leb_spec min 4), (Z.eqb_spec maj 543), (Z.eqb_spec min 0); cbn; first [reflexivity | lia]).
        eapply KVER.
        * replace (negb ((maj =? 2) && (min <=? 4) || (maj =? 543) && (min =? 0)))%Z with false
          by (symmetry; destruct (Z.eqb_spec maj 2), (Z.leb_spec min 4), (Z.eqb_spec maj 543), (Z.eqb_spec min 0); cbn; first [reflexivity | lia]).
        eapply KOK.
  Qed.
  End Sz1.
  Lemma chk_hdr : ltac:(let t := eval cbv delta [chk_hdr__stmt] in chk_hdr__stmt in exact t).
  Proof using CHK_FILL FRET GL GPL OPEN_COMMON SNPRINTF. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r19 t3 t4 t5 t6 j1 j3 pre mid post ej k0 k1 k2 maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw. ltac2:(SecDiet.SzSec.closeP 'chk_hdr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkHdr.
End CANSEC1.

(* [comment removed for export] *)

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_failA.TwB.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section ChkHdr.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis OPEN_COMMON : open_offline_common_stmt HO FO sites GIOA TP.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis CHK_FILL : chk_fill_stmt HO FO sites GIOA TP fflagA.

  Definition chk_hdr__stmt : Prop := chk_hdr_stmt HO FO sites GIOA TP fflagA.
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r24 t3 t4 t5 t6 j1 j3 pre mid post ej k0 k1 k2 maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw : ltac2:(SecDiet.SzSec.tyM 'chk_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma chk_hdr__body : ltac2:(SecDiet.SzSec.bodyP 'chk_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CHK_FILL FRET GL GPL OPEN_COMMON SNPRINTF.
 intros CTX INV MI3 Bmaj Bmin N0 N1 N2 N3 L0 L1 L2 L3 FRA FRC1 HD FRC2 HE HEB.
    chk_setup GL CTX INV.
    assert (MIB : (2^31 <= mi < 2^32)%Z) by (unfold TCPDUMP_MAGIC, KUZNETZOV_TCPDUMP_MAGIC, NSEC_TCPDUMP_MAGIC in MI3; lia).
    (* [comment removed for export] *)
    pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HD FRC2 ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC.
    cbn [app] in FRC. clear FRC1 HD FRC2.
    (* [comment removed for export] *)
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND'| apply Forall_cons; [exact EBBAND'| apply Forall_nil]]).
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AG FXB) as AGsh.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G ICL IFL AGsh ltac:(lia)) as OEBm.
    assert (OEB' : cobjA RNGx mm ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) (CL ++ []) EB 256)
      by (split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEBm) ICL IFL)| exact (proj2 OEBm)]).
    assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(bv_unsigned sp - 57344, bv_unsigned sp)]%Z) by own_ivs.
    assert (FX : Forall (cobj_iv FL CL) [(EB, EB + 256)]%Z) by cobj_ivs.
    unfold chk_rest2. cbn [e_fret prims].
    set (POSTQ := check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR [mg0; mg1; mg2; mg3] f m (ps_outfile s)).
    (* [comment removed for export] *)
    assert (KSNP : forall (ra5 t0' t1' t2' a3' a4' a5' a6' a7' r20' r22' t3' t4' t5' t6' : word) (FMTA : Z) (fs : string) (args : list farg),
      (ra5 = Z_to_bv 64 0x87dc4 \/ ra5 = Z_to_bv 64 0x87f0c) ->
      fmt_at mm FMTA fs -> fmt_ok fs args = true -> (length args <= 2)%nat ->
      Forall2 (farg_word true L RNGx ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) (CL ++ []) SPA EB 256 mm) args (firstn (length args) [a3'; a4']) ->
      (length (Fmt.snprintf 256 fs args) <= 255)%nat -> items_okb (fmt fs) = true -> Forall arg_ok args ->
      evtF asegs RNGx (fun ms' => implMG RNGx (fo_ret FO _ FF_CHECK_HEADER (CH_Err (Fmt.snprintf 256 fs args))) sx POSTQ ms')
        (MS (mkR ra5 (Z_to_bv 64 SPA) gp tp t0' t1' t2' sp (Z_to_bv 64 SPA) (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 (Z_to_bv 64 ERR) (Z_to_bv 64 Fb) r20' (Z_to_bv 64 (mi + (2^64 - 2^32))) r22' (Z_to_bv 64 (Fb + 32))
                 (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3' t4' t5' t6')
            F (Z_to_bv 64 SNPRINTF_ENTRY) fc None mm (seg_rom asegs))).
    { intros ra5 t0' t1' t2' a3' a4' a5' a6' a7' r20' r22' t3' t4' t5' t6' FMTA fs args Hra FMT5 FOK LA FWA LEN IOK AOK.
      pose proof (munch_refl [(bv_unsigned sp - 57344, bv_unsigned sp); (EB, EB + 256)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      eapply evtF_cut;
        [ eapply SNPRINTF with (L := L) (s := sx) (CL := CL ++ []) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (DST := EB) (n := 256%Z)
                               (FMTA := FMTA) (fs := fs) (args := args) (junk := ej);
          [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | lia
          | rewrite Hspa; replace (firstn (length args) [a3'; a4'; a5']) with (firstn (length args) [a3'; a4'])
              by (clear - LA; destruct args as [|? [|? [|? ?]]]; cbn in LA |- *; first [reflexivity | lia]); exact FWA
          | exact HEB | exact OEB' ]
        | ].
      cbv beta; intros ms' PO; destruct PO as (vav5 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
      unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
      unfold STDIO_STACK in MU6.
      lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end; clear MU6 WM6.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m6 _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m6 _ _ _ FW FX G MU WM ltac:(lia)) as [G6 AG6];
        assert (AGm6 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m6)
          by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG6|]; intros a (K & (_ & QN & _)); split; [exact K|]; split; [exact QN| exact I])
      end.
      change (Z.to_nat 256) with 256%nat in HEB6.
      replace (256 - length (Fmt.snprintf 256 fs args) - 1)%nat with (255 - length (Fmt.snprintf 256 fs args))%nat in HEB6 by lia.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m6 _) =>
        assert (INV6 : chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNGx sx [] m6)
          by (unfold chk_inv, chk_shadow; split; [exact FP|]; split; [exact G6|]; split; [exact OF|]; repeat (split; [assumption|]); assumption) end.
      apply evtF_done. subst POSTQ.
      destruct Hra as [-> | ->].
      1: replace (ret_pc (Z_to_bv 64 0x87dc4)) with (Z_to_bv 64 0x87dc4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      2: replace (ret_pc (Z_to_bv 64 0x87f0c)) with (Z_to_bv 64 0x87f0c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      all: lazymatch goal with |- implMG _ _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?m6 _) =>
        eapply (chk_fail FO GIOA TP fflagA GL FRET) with (mm := m6) (pcX := pc) (msg := Fmt.snprintf 256 fs args)
               (fcs := [CB 8 pre; C4 (Z_to_bv 64 (mi + (2^64 - 2^32))); C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid;
                        C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3)); CB 64 post]);
          [ exact CTX | exact INV6 | left; split; [first [left; reflexivity | right; left; reflexivity] | split; reflexivity]
          | exact FRA | exact FRC | reflexivity | exact HE | exact HEB6 | lia | apply snprintf_ok; [exact IOK| exact AOK] ] end. }
    (* [comment removed for export] *)
    assert (KVER : forall (a0' a1' : word),
      evtF asegs RNGx (fun ms' => implMG RNGx (fo_ret FO _ FF_CHECK_HEADER (CH_Err (Msg.unsupported_pcap_version maj min))) sx POSTQ ms')
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0' a1' a2 (Z_to_bv 64 maj) a4 a5 a6 a7 (Z_to_bv 64 ERR) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 (Fb + 36)) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x87ef4) fc None mm (seg_rom asegs))).
    { intros a0' a1'.
      assert (MSG : fmt_at mm 0x21c40 "unsupported pcap savefile version %u.%u"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x21c40 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "unsupported pcap savefile version %u.%u"%string) ++ [Z_to_bv 8 0])
                                MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      zstep. rewrite ?zx16_lit by lia.
      do 4 zstep.
      zstep.
      unfold Msg.unsupported_pcap_version, PCAP_ERRBUF_SIZE.
      eapply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [AInt maj; AInt min]); [right; reflexivity | exact MSG | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
      { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
      pose proof (snprintf_length_le 256 "unsupported pcap savefile version %u.%u"%string [AInt maj; AInt min] ltac:(lia)) as LS. lia. }
    (* [comment removed for export] *)
    assert (KOK : forall (a0' a1' : word),
      evtF asegs RNGx (fun ms' => implMG RNGx
                   (if negb (Z.land (le4val l0 l1 l2 l3) 67043328 =? 0)
                    then fo_ret FO _ FF_CHECK_HEADER (CH_Err (Msg.reserved_not_zero (Z.land (le4val l0 l1 l2 l3) 67043328)))
                    else mo_bind MOps (pcapint_open_offline_common MOps (prims HO FO sites) PCAP_SF_TOTAL)
                           (fun r => match r with
                                     | inl m0 => fo_ret FO _ FF_CHECK_HEADER (CH_Err m0)
                                     | inr self => chk_fill_model MOps (prims HO FO sites) self f 0 mi sw maj min (le4val n0 n1 n2 n3) (le4val l0 l1 l2 l3)
                                     end)) sx POSTQ ms')
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0' a1' a2 (Z_to_bv 64 maj) a4 a5 a6 a7 (Z_to_bv 64 ERR) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 (Fb + 36)) (Z_to_bv 64 (mi + (2^64 - 2^32))) (Z_to_bv 64 FA) (Z_to_bv 64 (Fb + 32)) (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x87da0) fc None mm (seg_rom asegs))).
    { intros a0' a1'. rewrite (reserved_val l0 l1 l2 l3) by lia.
      zstep. do 2 zstep.   (* [comment removed for export] *)
      rewrite (zx32_lit (le4val l0 l1 l2 l3)) by (unfold le4val; lia). rewrite (unsigned_lit (le4val l0 l1 l2 l3)) by (unfold le4val; lia). rewrite (reserved_val l0 l1 l2 l3) by lia.
      zstep.
      destruct (Z.eq_dec ((l2 + 256 * (l3 mod 4)) * 65536) 0) as [RZ|RZ].
      2:{ (* [comment removed for export] *)
        replace ((l2 + 256 * (l3 mod 4)) * 65536 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact RZ). cbn [negb].
        if_cases KR; [zify_cond KR; exfalso; lia|].
        assert (MSG : fmt_at mm 0x21ca0 "savefile linktype reserved field not zero (0x%08x)"%string)
          by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x21ca0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "savefile linktype reserved field not zero (0x%08x)"%string) ++ [Z_to_bv 8 0])
                                  MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
              split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
        do 4 zstep.   (* [comment removed for export] *)
        zstep.
        unfold Msg.reserved_not_zero, PCAP_ERRBUF_SIZE.
        eapply (KSNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [AInt ((l2 + 256 * (l3 mod 4)) * 65536)]); [left; reflexivity | exact MSG | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints1].
        { cbn [length firstn]. constructor; [reflexivity| constructor]. }
        pose proof (snprintf_length_le 256 "savefile linktype reserved field not zero (0x%08x)"%string [AInt ((l2 + 256 * (l3 mod 4)) * 65536)] ltac:(lia)) as LS. lia. }
      (* [comment removed for export] *)
      replace ((l2 + 256 * (l3 mod 4)) * 65536 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact RZ). cbn [negb].
      rewrite RZ. if_true.
      do 3 zstep.
      zstep.
      (* [comment removed for export] *)
      pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FR eq_refl) as BRA.
      cbn [firstn cells_size csize Nat.add] in BS0, BRA.
      replace (bv_unsigned sp + -104 + Z.of_nat 88)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
      replace (bv_unsigned sp + -104 + Z.of_nat 96)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
      assert (UC3 : ucallerA (depth_check_header false) L mm sp s0 ra trC).
      { eapply ucaller_keep; [exact UC| lia|]. intros a Ha.
        destruct (AG a ltac:(lia) ltac:(split; [left; lia| cbn [outside fst snd]; lia])) as [E1 _]. congruence. }
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      apply evtF_done. eapply implMG_bind.
      { eapply (OPEN_COMMON _ spa) with (L := L) (s := sx) (CL := CL ++ []) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (EB := EB) (total := PCAP_SF_TOTAL) (ej := ej);
          [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold PCAP_L1B_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x8801c%Z UC3); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_open_offline_common, depth_check_header, depth_pcap_check_header; lia]
          | rewrite unsigned_lit by lia; unfold traces_check_header, traces_pcap_check_header in TR; destruct TR as (_ & T2 & _); exact T2
          | unfold frames_open_offline_common; apply nofr_cons; [eapply nofr_sub; [exact NF| intros ff Hf; cbn in Hf |- *; clear - Hf; intuition]| cbn; clear; intuition congruence]
          | rewrite Hspa; lia   (* [comment removed for export] *)
          | reflexivity | reflexivity | reflexivity | left; reflexivity | exact HEB | exact OEB' | exact EB8 ]. }
      intros r s1' RNG1 ms' PO. unfold open_common_post in PO. destruct PO as (FP1 & av & m1 & E & OF1 & MI1 & ST1 & AG1 & PO).
      unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
      replace (ret_pc (Z_to_bv 64 557084)) with (Z_to_bv 64 557084) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in AG1.
      (* [comment removed for export] *)
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP1) in HR end.
      assert (KST : forall A cs, rw_cells asegs mm A cs -> (SPA <= A)%Z -> rw_cells asegs m1 A cs).
      { intros A cs HC HA. eapply agrees_rw_cells; [exact AG1| exact HC|]. intros a Ha. split; [left; lia| lia]. }
      assert (KFR : forall A cs, rw_cells asegs mm A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 128)%Z -> rw_cells asegs m1 A cs).
      { intros A cs HC H1 H3. eapply agrees_rw_cells; [exact AG1| exact HC|]. intros a Ha. split; [|lia].
        right; right; left. apply in_frames_In. exists (FF_CHECK_HEADER, Fb, 128%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
      assert (KOB : forall A n cs, rw_cells asegs mm A cs -> clocA FL CL A n -> Z.of_nat (cells_size cs) = n ->
                     (A + n <= EB \/ EB + 256 <= A)%Z -> rw_cells asegs m1 A cs).
      { intros A n cs HC LOC HS HD. eapply agrees_rw_cells; [exact AG1| exact HC|]. intros a Ha. split; [|lia].
        eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]. }
      apply KST in FR; [|lia]. apply KST in FRA; [|lia].
      apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; split; [left; lia| lia]].
      apply KFR in FRC; [|lia|cbn [cells_size csize Nat.add]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AG1) in SHC;
        [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [|lia]; right; right; right; apply in_frame_sh_In; exists (FF_CHECK_HEADER, Fb, 128%Z);
          split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]].
      apply (KOB _ 4%Z) in HE; [|exact (proj1 OERR)|reflexivity|lia].
      apply (KOB _ 4%Z) in MGc; [|exact (proj1 OMG)|reflexivity|lia].
      assert (AGm1 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m1).
      { eapply agrees_on_trans; [exact AG|]. eapply (keeps_callee FO GIOA fflagA GL); [exact G| exact ICL| | | exact AG1|].
        - lia. - lia. - intros a _ QO _. cbn [outside fst snd] in QO. lia. }
      assert (INV1 : forall PB1, GIOA L RNG1 s1' (CL ++ PB1) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) m1 ->
                chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG1 s1' PB1 m1).
      { intros PB1 GX. unfold chk_inv, chk_shadow. split; [eapply fp_le_trans; [exact FP| exact FP1]|]. split; [exact GX|]. split; [congruence|].
        repeat (split; [assumption|]). assumption. }
      clear KST KFR KOB.
      destruct r as [msg|q].
      - (* [comment removed for export] *)
        destruct PO as (junk1 & -> & G1 & HEB1 & LEN1 & MSG1).
        apply implMG_from_evtF. zstep. if_true.
        apply evtF_done. subst POSTQ.
        eapply (chk_fail FO GIOA TP fflagA GL FRET) with (mm := m1) (pcX := 0x88194%Z) (msg := msg)
               (fcs := [CB 8 pre; C4 (Z_to_bv 64 (mi + (2^64 - 2^32))); C2 (Z_to_bv 64 maj); C2 (Z_to_bv 64 min); CB 8 mid;
                        C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3)); CB 64 post]);
          [ exact CTX | apply INV1; exact G1 | left; split; [right; right; left; reflexivity | split; reflexivity]
          | exact FRA | exact FRC | reflexivity | exact HE | exact HEB1 | exact LEN1 | exact MSG1 ].
      - (* [comment removed for export] *)
        destruct PO as (P & -> & G1 & CELLS & HEB1).
        destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G1 ltac:(left; reflexivity)) as ((_ & _ & PTOP & _) & P0 & _).
        cbn [cb_addr cb_size fst snd] in PTOP, P0.
        assert (PR : (0 < P < 2^64)%Z) by (atop_facts; unfold PCAP_SF_TOTAL in PTOP; lia).
        apply implMG_from_evtF. zstep. if_false_by (eqz_false P PR).
        apply evtF_done. subst POSTQ.
        eapply (CHK_FILL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m RNG1 s1' m1)
          with (q := q) (P := P) (mi := mi) (sw := sw) (maj := maj) (min := min) (n0 := n0) (n1 := n1) (n2 := n2) (n3 := n3) (l0 := l0) (l1 := l1) (l2 := l2) (l3 := l3);
          [ exact CTX
          | apply INV1; eapply GPL; [exact G1|]; rewrite app_nil_r; apply Permutation.Permutation_cons_append
          | exact MI3 | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia
          | clear - RZ L2 L3; Z.div_mod_to_equations; lia | clear - RZ L2 L3; Z.div_mod_to_equations; lia
          | exact FRA | exact FRC | exact CELLS | exact HE | exact HEB1 ]. }
    (* [comment removed for export] *)
    apply implMG_from_evtF.
    zstep. rewrite ?zx16_lit by lia.
    do 4 zstep.   (* [comment removed for export] *)
    if_cases K543; zify_cond K543.
    - zstep. rewrite ?zx16_lit by lia. zstep.
      if_cases KM0; zify_cond KM0.
      + (* [comment removed for export] *)
        replace (negb ((maj =? 2) && (min <=? 4) || (maj =? 543) && (min =? 0)))%Z with false
          by (symmetry; destruct (Z.eqb_spec maj 2), (Z.leb_spec min 4), (Z.eqb_spec maj 543), (Z.eqb_spec min 0); cbn; first [reflexivity | lia]).
        eapply KOK.
      + replace (negb ((maj =? 2) && (min <=? 4) || (maj =? 543) && (min =? 0)))%Z with true
          by (symmetry; destruct (Z.eqb_spec maj 2), (Z.leb_spec min 4), (Z.eqb_spec maj 543), (Z.eqb_spec min 0); cbn; first [reflexivity | lia]).
        eapply KVER.
    - do 2 zstep.
      if_cases K2; zify_cond K2.
      + replace (negb ((maj =? 2) && (min <=? 4) || (maj =? 543) && (min =? 0)))%Z with true
          by (symmetry; destruct (Z.eqb_spec maj 2), (Z.leb_spec min 4), (Z.eqb_spec maj 543), (Z.eqb_spec min 0); cbn; first [reflexivity | lia]).
        eapply KVER.
      + zstep. rewrite ?zx16_lit by lia. do 2 zstep.
        if_cases K5; zify_cond K5.
        * replace (negb ((maj =? 2) && (min <=? 4) || (maj =? 543) && (min =? 0)))%Z with true
          by (symmetry; destruct (Z.eqb_spec maj 2), (Z.leb_spec min 4), (Z.eqb_spec maj 543), (Z.eqb_spec min 0); cbn; first [reflexivity | lia]).
        eapply KVER.
        * replace (negb ((maj =? 2) && (min <=? 4) || (maj =? 543) && (min =? 0)))%Z with false
          by (symmetry; destruct (Z.eqb_spec maj 2), (Z.leb_spec min 4), (Z.eqb_spec maj 543), (Z.eqb_spec min 0); cbn; first [reflexivity | lia]).
        eapply KOK.
  Qed.
  End Sz1.
  Lemma chk_hdr : ltac:(let t := eval cbv delta [chk_hdr__stmt] in chk_hdr__stmt in exact t).
  Proof using CHK_FILL FRET GL GPL OPEN_COMMON SNPRINTF. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r24 t3 t4 t5 t6 j1 j3 pre mid post ej k0 k1 k2 maj min n0 n1 n2 n3 l0 l1 l2 l3 mi sw. ltac2:(SecDiet.SzSec.closeP 'chk_hdr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkHdr.
End CANSEC1.
End TwB.
End F_sfchk_hdrA.

(* [comment removed for export] *)
Module F_sfchk_tailA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_sfchk_swapA.
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
(* [comment removed for export] *)
Local Ltac oiv_lo_base k := lazymatch goal with |- (?lo0 <= ?lo)%Z /\ _ => d_split lo0 ltac:(fun X0 _ _ => d_split lo ltac:(fun X _ _ => constr_eq X0 X; k)) end.
Local Ltac oiv_orig :=
  first [ left; cbn [fst snd]; lia
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; lia ].
Local Ltac own_iv1 ::=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; oiv_lo_base ltac:(lia)
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; oiv_lo_base ltac:(lia)
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; oiv_lo_base ltac:(lia)
        | oiv_orig ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section ChkTail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis CHK_HDR : chk_hdr_stmt HO FO sites GIOA TP fflagA.

  (* [comment removed for export] *)
  Definition chk_short_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
           (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem)
           (RNGx : footprint) (sx : PState H hptr) (mm : mem)
           (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r19 r21 r23 r26 t3 t4 t5 t6 : word)
           (j1 j3 fj ej : list byte) (k0 k1 k2 c24 c32 : word) (n : Z),
      chk_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
      chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic (ps_outfile s) m RNGx sx [] mm ->
      (0 <= n <= 20)%Z -> n <> 20%Z ->
      rw_cells asegs mm SPA [CB 24 j1; C8 c24; C8 c32; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                             C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 EB); CB 16 j3; C8 (Z_to_bv 64 Fb)] ->
      rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 96 fj; C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] ->
      rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 ej] ->
      implMG RNGx (mbind (read_fail_msg MOps (prims HO FO sites) f (Msg.trunc_file_header 24 n))
                         (fun m0 => e_fret (prims HO FO sites) FF_CHECK_HEADER (CH_Err m0))) sx
        (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 r18 r19 (Z_to_bv 64 ERR)
                 r21 (Z_to_bv 64 FA) r23 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r26 (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x87920) fc None mm (seg_rom asegs)).
  Hypothesis CHK_SHORT : chk_short_stmt.

  Definition chk_tail__stmt : Prop := chk_tail_stmt HO FO sites GIOA TP fflagA.
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a7 r18 r23 r26 t3 t4 t5 t6 j1 j2 j3 fjunk ej k0 k1 k2 mi sw : ltac2:(SecDiet.SzSec.tyM 'chk_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FREAD CHK_HDR CHK_SHORT"] Lemma chk_tail__body : ltac2:(SecDiet.SzSec.bodyP 'chk_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros CTX INV MI3 LJ FRA FRC HE HEB.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU. unfold chk_shadow in SHC.
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    (* [comment removed for export] *)
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]. pose proof (Forall_inv FAll) as FRM. pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll. change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR.
    pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _). band_ind FBAND' bF.
    assert (ICL : incl CL (CL ++ [])) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL ((FF_CHECK_HEADER, Fb, 128%Z) :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL) ltac:(lia)) as MGBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    pose proof MGBAND as MGBAND'. pose proof ERBAND as ERBAND'. pose proof EBBAND as EBBAND'.
    band_ind MGBAND bM. band_ind ERBAND bE. band_ind EBBAND bB.
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL (incl_refl _)) ltac:(lia)) as (kM & kMr & kM1 & kM2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2).
    cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    apply (rng_fp_le _ _ _ _ FP) in RSTK. apply (rng_fp_le _ _ _ _ FP) in RIMG. apply (rng_fp_le _ _ _ _ FP) in RISH. apply (rng_fp_le _ _ _ _ FP) in RTLS.
    assert (RSPW : rng RNGx lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (RSPA : rng RNGx SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    (* [comment removed for export] *)
    unfold chk_rest. cbn [mo_bind mo_ret MOps e_fread prims].
    apply (rw_cells_split_CB asegs _ _ [_; _; _] 96 _ [_] [8; 4; 20; 64]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    do 3 zstep.
    do 2 zstep.
    do 6 zstep.
    zstep.
    replace (ret_pc (Z_to_bv 64 555044)) with (Z_to_bv 64 555044) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mx _ [] _ FW (Forall_nil _) G MU WM ltac:(lia)) as [G3 AG3] end.
    assert (AGm : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m1).
    { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & _). split; [exact K| exact I]. }
    pose proof (unp_of_sh_bytes _ _ _ 4%nat 3%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPH.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPH. change (8 * Z.of_nat 3)%Z with 24%Z in UNPH.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    destruct (rw_cells_cut _ _ _ 5 FRC) as [FRC1 FRC']. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FRC1, FRC'.
    destruct (rw_cells_cut _ _ _ 1 FRC') as [FRD FRC2]. clear FRC'. cbn [firstn skipn cells_size csize Nat.add] in FRD, FRC2.
    replace (Fb + Z.of_nat 36)%Z with (Fb + 36)%Z in * by lia. replace (Fb + 36 + Z.of_nat 20)%Z with (Fb + 56)%Z in * by lia.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SitePcapHdrRest 36%Z G3 (or_introl eq_refl) eq_refl).
      replace (Fb + 36 + 0)%Z with (Fb + 36)%Z by lia.
      eapply (FREAD _ spa);
        [ split; [exact G3|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact FRD
        | split; [right; exists (FF_CHECK_HEADER, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia|
                               eapply unpoisoned_sub; [exact UNPH| lia| lia]] ]. }
    intros got s2' RNG2 ms' PO. cbv beta in PO.
    destruct PO as (FP2 & av & m2 & junk' & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & GOTL & GOTR & HD2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 555044)) with (Z_to_bv 64 555044) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [app] in G2, AG2.
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    assert (KST : forall A cs, rw_cells asegs m1 A cs -> (SPA <= A)%Z -> rw_cells asegs m2 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AG2| exact HC|]. intros a Ha. split; [left; lia| lia]. }
    assert (KFR : forall A cs, rw_cells asegs m1 A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 36 \/ Fb + 56 <= A)%Z ->
                   (A + Z.of_nat (cells_size cs) <= Fb + 128)%Z -> rw_cells asegs m2 A cs).
    { intros A cs HC H1 H2 H3. eapply agrees_rw_cells; [exact AG2| exact HC|]. intros a Ha. split; [|lia].
      right; right; left. apply in_frames_In. exists (FF_CHECK_HEADER, Fb, 128%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
    assert (KOB : forall A n cs, rw_cells asegs m1 A cs -> clocA FL CL A n -> Z.of_nat (cells_size cs) = n ->
                   (A + n <= Fb \/ Fb + 128 <= A)%Z -> rw_cells asegs m2 A cs).
    { intros A n cs HC LOC HS HD. eapply agrees_rw_cells; [exact AG2| exact HC|]. intros a Ha. split; [|lia].
      eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]. }
    apply KST in FR; [|lia]. apply KST in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG2) in STG; [|intros a Ha; split; [left; lia| lia]].
    apply KFR in FRC1; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KFR in FRC2; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG2) in SHC;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [|lia]; right; right; right; apply in_frame_sh_In; exists (FF_CHECK_HEADER, Fb, 128%Z);
        split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]].
    apply (KOB _ 4%Z) in HE; [|exact (proj1 OERR)|reflexivity|lia].
    apply (KOB _ 256%Z) in HEB; [|exact (proj1 OEB)|reflexivity|lia].
    apply (KOB _ 4%Z) in MGc; [|exact (proj1 OMG)|reflexivity|lia].
    assert (AGm2 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m2).
    { eapply agrees_on_trans; [exact AGm|]. eapply (keeps_callee FO GIOA fflagA GL); [exact G3| exact ICL| | | exact AG2|].
      - lia. - lia. - intros a _ _ N. cbn [fb_addr fb_size fst snd] in N. lia. }
    clear KST KFR KOB AG2 AGm AG AG3 UNPH FRM3.
    assert (INV2 : forall mx, GIOA L RNG2 s2' (CL ++ []) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) mx -> mem_inv asegs mx -> stk asegs mx lo SPA ->
              stk asegs mx (SPA + 88) (bv_unsigned sp + -104) ->
              rw_cells asegs mx (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mx ->
              rw_cells asegs mx MG [C1 (b8 mg0); C1 (b8 mg1); C1 (b8 mg2); C1 (b8 mg3)] ->
              rw_cells asegs mx (Z.shiftr Fb 3 + 2147450880) chk_shadow ->
              chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG2 s2' [] mx).
    { intros mx X1 X2 X3 X4 X5 X6 X7 X8. unfold chk_inv. split; [eapply fp_le_trans; [exact FP| exact FP2]|]. split; [exact X1|]. split; [congruence|].
      repeat (split; [assumption|]). assumption. }
    unfold zlength in *.
    destruct (Z.eq_dec (Z.of_nat (length got)) 20) as [L20|L20].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) L20). cbn [negb].
      pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HD2 FRC2 ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) as FRCx.
      cbn [app] in FRCx.
      lazymatch type of FRCx with rw_cells _ _ _ [?h0; ?h1; ?h2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
        pose proof (rw_cells_merge asegs _ _ [h0; h1; h2] [c3; c4; c5; c6; c7] [c8] FRCx) as FRCm end.
      cbn [app] in FRCm.
      lazymatch type of FRCm with rw_cells _ _ _ [_; _; _; CB ?n _; _] => replace n with 96%nat in FRCm by (cbn [cells_size csize]; lia) end.
      ienterG. zstep. rewrite (eqb_lits_false (Z.of_nat (length got)) 20) by lia. cbn [negb]. cbv iota.
      apply evtF_done. subst POSTQ0 POSTQ.
      eapply (CHK_SHORT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m RNG2 s2' m2);
        [exact CTX | apply INV2; assumption | lia | exact L20 | exact FRA | exact FRCm | exact HE | exact HEB]. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) L20). cbn [negb].
    assert (L20n : length got = 20%nat) by lia.
    destruct got as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|g8 [|g9 [|g10 [|g11 [|g12 [|g13 [|g14 [|g15 [|g16 [|g17 [|g18 [|g19 [|gx gr]]]]]]]]]]]]]]]]]]]]]; try (exfalso; cbn in L20n; lia).
    clear L20n L20 GOTL.
    pose proof GOTR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    assert (LJ' : length junk' = 0%nat) by (destruct HD2 as [[WF _] _]; cbn in WF; lia).
    destruct junk' as [|jx jr]; [|discriminate LJ']. clear LJ'.
    (* [comment removed for export] *)
    assert (HD5 : rw_cells asegs m2 (Fb + 36)
              [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3)); CB 8 (map b8 [g4; g5; g6; g7; g8; g9; g10; g11]);
               C4 (Z_to_bv 64 (le4val g12 g13 g14 g15)); C4 (Z_to_bv 64 (le4val g16 g17 g18 g19))]).
    { eapply rw_cells_recell; [exact HD2 | cbn; repeat split; reflexivity |].
      cbn [cells_bytes cbytes]. rewrite (le2_lit g0 g1), (le2_lit g2 g3), (le4_lit g12 g13 g14 g15), (le4_lit g16 g17 g18 g19) by lia. reflexivity. }
    clear HD2.
    unfold get_le16, get_le32, zslice, zfirstn, zskipn.
    change (Z.to_nat 2) with 2%nat. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. change (Z.to_nat 12) with 12%nat. change (Z.to_nat 16) with 16%nat.
    cbn [firstn skipn].
    assert (FW2 : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(Fb, Fb + 128)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 128)]%Z m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    ienterG. zstep. if_false.
    destruct sw; cbn [negb Z.b2z] in *.
    - (* [comment removed for export] *)
      zstep. if_false.
      replace (Fb + 36)%Z with (Fb + 32 + 4)%Z in HD5 by lia.
      assert (RH : rng RNG2 (Fb + 32) 24) by (eapply rng_sub; [exact FRNG| lia| lia]).
      call (swap_blockA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RNG2 (Fb + 32)%Z g0 g1 g2 g3 g12 g13 g14 g15 g16 g17 g18 g19).
      1: assumption. 1-14: lia. 1: exact HD5.
      replace (Fb + 32 + 4)%Z with (Fb + 36)%Z in POST by lia.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mx _ [] _ FW2 (Forall_nil _) G2 MU2 WM2 ltac:(lia)) as [G4 AG4];
        assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mx)
          by (eapply agrees_on_trans; [exact AGm2|]; eapply agrees_on_weaken; [exact AG4|]; intros a (K & _); split; [exact K| exact I])
      end.
      rewrite (bswap16_bytes g0 g1), (bswap16_bytes g2 g3), (bswap32_bytes g12 g13 g14 g15), (bswap32_bytes g16 g17 g18 g19) by lia.
      rewrite !le_of_bytes_2, !le_of_bytes_4.
      replace (g15 + 256 * g14 + 65536 * g13 + 16777216 * g12)%Z with (le4val g15 g14 g13 g12) by reflexivity.
      replace (g19 + 256 * g18 + 65536 * g17 + 16777216 * g16)%Z with (le4val g19 g18 g17 g16) by reflexivity.
      apply evtF_done. subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (CHK_HDR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m RNG2 s2' mx)
          with (sw := true) (mi := mi) (maj := (g1 + 256 * g0)%Z) (min := (g3 + 256 * g2)%Z) (n0 := g15) (n1 := g14) (n2 := g13) (n3 := g12)
               (l0 := g19) (l1 := g18) (l2 := g17) (l3 := g16);
          [exact CTX | apply INV2; assumption | exact MI3 | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia
          | exact FRA | exact FRC1 | exact POST | exact FRC2 | exact HE | exact HEB] end.
    - (* [comment removed for export] *)
      zstep. if_true.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mx _ [] _ FW2 (Forall_nil _) G2 MU2 WM2 ltac:(lia)) as [G4 AG4];
        assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mx)
          by (eapply agrees_on_trans; [exact AGm2|]; eapply agrees_on_weaken; [exact AG4|]; intros a (K & _); split; [exact K| exact I])
      end.
      cbv iota. rewrite !le_of_bytes_2, !le_of_bytes_4.
      replace (g12 + 256 * g13 + 65536 * g14 + 16777216 * g15)%Z with (le4val g12 g13 g14 g15) by reflexivity.
      replace (g16 + 256 * g17 + 65536 * g18 + 16777216 * g19)%Z with (le4val g16 g17 g18 g19) by reflexivity.
      apply evtF_done. subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (CHK_HDR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m RNG2 s2' mx)
          with (sw := false) (mi := mi) (maj := (g0 + 256 * g1)%Z) (min := (g2 + 256 * g3)%Z) (n0 := g12) (n1 := g13) (n2 := g14) (n3 := g15)
               (l0 := g16) (l1 := g17) (l2 := g18) (l3 := g19);
          [exact CTX | apply INV2; assumption | exact MI3 | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia
          | exact FRA | exact FRC1 | exact HD5 | exact FRC2 | exact HE | exact HEB] end.
  Qed.
  End Sz1.
  #[using="GL FREAD CHK_HDR CHK_SHORT"] Lemma chk_tail : ltac:(let t := eval cbv delta [chk_tail__stmt] in chk_tail__stmt in exact t).
  Proof. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a7 r18 r23 r26 t3 t4 t5 t6 j1 j2 j3 fjunk ej k0 k1 k2 mi sw. ltac2:(SecDiet.SzSec.closeP 'chk_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkTail.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_sfchk_swapA.TwB.
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
(* [comment removed for export] *)
Local Ltac oiv_lo_base k := lazymatch goal with |- (?lo0 <= ?lo)%Z /\ _ => d_split lo0 ltac:(fun X0 _ _ => d_split lo ltac:(fun X _ _ => constr_eq X0 X; k)) end.
Local Ltac oiv_orig :=
  first [ left; cbn [fst snd]; lia
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; lia ].
Local Ltac own_iv1 ::=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; oiv_lo_base ltac:(lia)
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; oiv_lo_base ltac:(lia)
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; oiv_lo_base ltac:(lia)
        | oiv_orig ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section ChkTail.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis CHK_HDR : chk_hdr_stmt HO FO sites GIOA TP fflagA.

  (* [comment removed for export] *)
  Definition chk_short_stmt : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
           (lo MG FA EB ERR SPA Fb : Z) (f : hptr) (magic : list Z) (m : mem)
           (RNGx : footprint) (sx : PState H hptr) (mm : mem)
           (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r23 r24 t3 t4 t5 t6 : word)
           (j1 j3 fj ej : list byte) (k0 k1 k2 c24 c32 : word) (n : Z),
      chk_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f magic m ->
      chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb magic (ps_outfile s) m RNGx sx [] mm ->
      (0 <= n <= 20)%Z -> n <> 20%Z ->
      rw_cells asegs mm SPA [CB 24 j1; C8 c24; C8 c32; C8 (Z_to_bv 64 (Z.shiftr ERR 3 + 2147450880));
                             C8 (Z_to_bv 64 EB); C8 (Z_to_bv 64 ERR); CB 16 j3; C8 (Z_to_bv 64 Fb)] ->
      rw_cells asegs mm Fb [C8 k0; C8 k1; C8 k2; CB 96 fj; C8 (Z_to_bv 64 (fflagA L FF_CHECK_HEADER Fb))] ->
      rw_cells asegs mm ERR [C4 z64] -> rw_cells asegs mm EB [CB 256 ej] ->
      implMG RNGx (mbind (read_fail_msg MOps (prims HO FO sites) f (Msg.trunc_file_header 24 n))
                         (fun m0 => e_fret (prims HO FO sites) FF_CHECK_HEADER (CH_Err m0))) sx
        (check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 r18 (Z_to_bv 64 Fb) r20
                 r21 (Z_to_bv 64 FA) r23 r24 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0x87de4) fc None mm (seg_rom asegs)).
  Hypothesis CHK_SHORT : chk_short_stmt.

  Definition chk_tail__stmt : Prop := chk_tail_stmt HO FO sites GIOA TP fflagA.
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a6 a7 r19 r20 r23 t3 t4 t5 t6 j1 j2 j3 fjunk ej k0 k1 k2 mi sw : ltac2:(SecDiet.SzSec.tyM 'chk_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FREAD CHK_HDR CHK_SHORT"] Lemma chk_tail__body : ltac2:(SecDiet.SzSec.bodyP 'chk_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX INV MI3 LJ FRA FRC HE HEB.
    pose proof CTX as (LO & BU & (SPT & TOP47) & TPE & ALN & (RSTK & RIMG & RISH & RTLS) & UC & TR & NF & HinF & MGR & MGL & OMG & OERR & DME & OEB & DEE & DEM & ERR4 & EB8 & SPAB & SPA32).
    pose proof INV as (FP & G & OF & MI & ST & STG & FR & AG & MGc & SHC).
    unfold PCAP_L2_STACK in BU. unfold chk_shadow in SHC.
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. cbn [map] in MGc.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    (* [comment removed for export] *)
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll FND]. pose proof (Forall_inv FAll) as FRM. pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll. change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR.
    pose proof (ablk_lin _ _ FBAND') as (_ & Fb0 & _ & _). band_ind FBAND' bF.
    assert (ICL : incl CL (CL ++ [])) by (apply incl_appl, incl_refl).
    assert (IFL : incl FL ((FF_CHECK_HEADER, Fb, 128%Z) :: FL)) by (apply incl_tl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL IFL) ltac:(lia)) as MGBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL IFL) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL IFL) ltac:(lia)) as EBBAND.
    pose proof MGBAND as MGBAND'. pose proof ERBAND as ERBAND'. pose proof EBBAND as EBBAND'.
    band_ind MGBAND bM. band_ind ERBAND bE. band_ind EBBAND bB.
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OMG) ICL (incl_refl _)) ltac:(lia)) as (kM & kMr & kM1 & kM2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OERR) ICL (incl_refl _)) ltac:(lia)) as (kE & kEr & kE1 & kE2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OEB) ICL (incl_refl _)) ltac:(lia)) as (kB & kBr & kB1 & kB2).
    cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    apply (rng_fp_le _ _ _ _ FP) in RSTK. apply (rng_fp_le _ _ _ _ FP) in RIMG. apply (rng_fp_le _ _ _ _ FP) in RISH. apply (rng_fp_le _ _ _ _ FP) in RTLS.
    assert (RSPW : rng RNGx lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (RSPA : rng RNGx SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    (* [comment removed for export] *)
    unfold chk_rest. cbn [mo_bind mo_ret MOps e_fread prims].
    apply (rw_cells_split_CB asegs _ _ [_; _; _] 96 _ [_] [8; 4; 20; 64]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    ienterG.
    do 3 zstep.
    do 2 zstep.
    do 6 zstep.
    zstep.
    replace (ret_pc (Z_to_bv 64 556264)) with (Z_to_bv 64 556264) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.   (* [comment removed for export] *)
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m1 _ [] _ FW (Forall_nil _) G MU WM ltac:(lia)) as [G3 AG3].
    assert (AGm : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m1).
    { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & _). split; [exact K| exact I]. }
    pose proof (unp_of_sh_bytes _ _ _ 4%nat 3%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPH.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPH. change (8 * Z.of_nat 3)%Z with 24%Z in UNPH.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    destruct (rw_cells_cut _ _ _ 5 FRC) as [FRC1 FRC']. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FRC1, FRC'.
    destruct (rw_cells_cut _ _ _ 1 FRC') as [FRD FRC2]. clear FRC'. cbn [firstn skipn cells_size csize Nat.add] in FRD, FRC2.
    replace (Fb + Z.of_nat 36)%Z with (Fb + 36)%Z in * by lia. replace (Fb + 36 + Z.of_nat 20)%Z with (Fb + 56)%Z in * by lia.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SitePcapHdrRest 36%Z G3 (or_introl eq_refl) eq_refl).
      replace (Fb + 36 + 0)%Z with (Fb + 36)%Z by lia.
      eapply (FREAD _ spa);
        [ split; [exact G3|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact FRD
        | split; [right; exists (FF_CHECK_HEADER, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia|
                               eapply unpoisoned_sub; [exact UNPH| lia| lia]] ]. }
    intros got s2' RNG2 ms' PO. cbv beta in PO.
    destruct PO as (FP2 & av & m2 & junk' & E & OF2 & MI2 & ST2 & AG2 & G2 & -> & GOTL & GOTR & HD2).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 556264)) with (Z_to_bv 64 556264) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [app] in G2, AG2.
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    assert (KST : forall A cs, rw_cells asegs m1 A cs -> (SPA <= A)%Z -> rw_cells asegs m2 A cs).
    { intros A cs HC HA. eapply agrees_rw_cells; [exact AG2| exact HC|]. intros a Ha. split; [left; lia| lia]. }
    assert (KFR : forall A cs, rw_cells asegs m1 A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 36 \/ Fb + 56 <= A)%Z ->
                   (A + Z.of_nat (cells_size cs) <= Fb + 128)%Z -> rw_cells asegs m2 A cs).
    { intros A cs HC H1 H2 H3. eapply agrees_rw_cells; [exact AG2| exact HC|]. intros a Ha. split; [|lia].
      right; right; left. apply in_frames_In. exists (FF_CHECK_HEADER, Fb, 128%Z). split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]. }
    assert (KOB : forall A n cs, rw_cells asegs m1 A cs -> clocA FL CL A n -> Z.of_nat (cells_size cs) = n ->
                   (A + n <= Fb \/ Fb + 128 <= A)%Z -> rw_cells asegs m2 A cs).
    { intros A n cs HC LOC HS HD. eapply agrees_rw_cells; [exact AG2| exact HC|]. intros a Ha. split; [|lia].
      eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]. }
    apply KST in FR; [|lia]. apply KST in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG2) in STG; [|intros a Ha; split; [left; lia| lia]].
    apply KFR in FRC1; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KFR in FRC2; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG2) in SHC;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [|lia]; right; right; right; apply in_frame_sh_In; exists (FF_CHECK_HEADER, Fb, 128%Z);
        split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]].
    apply (KOB _ 4%Z) in HE; [|exact (proj1 OERR)|reflexivity|lia].
    apply (KOB _ 256%Z) in HEB; [|exact (proj1 OEB)|reflexivity|lia].
    apply (KOB _ 4%Z) in MGc; [|exact (proj1 OMG)|reflexivity|lia].
    assert (AGm2 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m2).
    { eapply agrees_on_trans; [exact AGm|]. eapply (keeps_callee FO GIOA fflagA GL); [exact G3| exact ICL| | | exact AG2|].
      - lia. - lia. - intros a _ _ N. cbn [fb_addr fb_size fst snd] in N. lia. }
    clear KST KFR KOB AG2 AGm AG AG3 UNPH FRM3.
    assert (INV2 : forall mx, GIOA L RNG2 s2' (CL ++ []) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) mx -> mem_inv asegs mx -> stk asegs mx lo SPA ->
              stk asegs mx (SPA + 88) (bv_unsigned sp + -104) ->
              rw_cells asegs mx (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mx ->
              rw_cells asegs mx MG [C1 (b8 mg0); C1 (b8 mg1); C1 (b8 mg2); C1 (b8 mg3)] ->
              rw_cells asegs mx (Z.shiftr Fb 3 + 2147450880) chk_shadow ->
              chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG2 s2' [] mx).
    { intros mx X1 X2 X3 X4 X5 X6 X7 X8. unfold chk_inv. split; [eapply fp_le_trans; [exact FP| exact FP2]|]. split; [exact X1|]. split; [congruence|].
      repeat (split; [assumption|]). assumption. }
    unfold zlength in *.
    destruct (Z.eq_dec (Z.of_nat (length got)) 20) as [L20|L20].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) L20). cbn [negb].
      pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HD2 FRC2 ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) as FRCx.
      cbn [app] in FRCx.
      lazymatch type of FRCx with rw_cells _ _ _ [?h0; ?h1; ?h2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
        pose proof (rw_cells_merge asegs _ _ [h0; h1; h2] [c3; c4; c5; c6; c7] [c8] FRCx) as FRCm end.
      cbn [app] in FRCm.
      lazymatch type of FRCm with rw_cells _ _ _ [_; _; _; CB ?n _; _] => replace n with 96%nat in FRCm by (cbn [cells_size csize]; lia) end.
      ienterG. zstep. rewrite (eqb_lits_false (Z.of_nat (length got)) 20) by lia. cbn [negb]. cbv iota.
      apply evtF_done. subst POSTQ0 POSTQ.
      eapply (CHK_SHORT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m RNG2 s2' m2);
        [exact CTX | apply INV2; assumption | lia | exact L20 | exact FRA | exact FRCm | exact HE | exact HEB]. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) L20). cbn [negb].
    assert (L20n : length got = 20%nat) by lia.
    destruct got as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|g8 [|g9 [|g10 [|g11 [|g12 [|g13 [|g14 [|g15 [|g16 [|g17 [|g18 [|g19 [|gx gr]]]]]]]]]]]]]]]]]]]]]; try (exfalso; cbn in L20n; lia).
    clear L20n L20 GOTL.
    pose proof GOTR as GR'. do 20 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    assert (LJ' : length junk' = 0%nat) by (destruct HD2 as [[WF _] _]; cbn in WF; lia).
    destruct junk' as [|jx jr]; [|discriminate LJ']. clear LJ'.
    (* [comment removed for export] *)
    assert (HD5 : rw_cells asegs m2 (Fb + 36)
              [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3)); CB 8 (map b8 [g4; g5; g6; g7; g8; g9; g10; g11]);
               C4 (Z_to_bv 64 (le4val g12 g13 g14 g15)); C4 (Z_to_bv 64 (le4val g16 g17 g18 g19))]).
    { eapply rw_cells_recell; [exact HD2 | cbn; repeat split; reflexivity |].
      cbn [cells_bytes cbytes]. rewrite (le2_lit g0 g1), (le2_lit g2 g3), (le4_lit g12 g13 g14 g15), (le4_lit g16 g17 g18 g19) by lia. reflexivity. }
    clear HD2.
    unfold get_le16, get_le32, zslice, zfirstn, zskipn.
    change (Z.to_nat 2) with 2%nat. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. change (Z.to_nat 12) with 12%nat. change (Z.to_nat 16) with 16%nat.
    cbn [firstn skipn].
    assert (FW2 : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(Fb, Fb + 128)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 128)]%Z m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    ienterG. zstep. if_false.
    destruct sw; cbn [negb Z.b2z] in *.
    - (* [comment removed for export] *)
      zstep. if_false.
      replace (Fb + 36)%Z with (Fb + 32 + 4)%Z in HD5 by lia.
      assert (RH : rng RNG2 (Fb + 32) 24) by (eapply rng_sub; [exact FRNG| lia| lia]).
      call (swap_blockA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RNG2 (Fb + 32)%Z g0 g1 g2 g3 g12 g13 g14 g15 g16 g17 g18 g19).
      1: assumption. 1-14: lia. 1: exact HD5.
      replace (Fb + 32 + 4)%Z with (Fb + 36)%Z in POST by lia.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mx _ [] _ FW2 (Forall_nil _) G2 MU2 WM2 ltac:(lia)) as [G4 AG4];
        assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mx)
          by (eapply agrees_on_trans; [exact AGm2|]; eapply agrees_on_weaken; [exact AG4|]; intros a (K & _); split; [exact K| exact I])
      end.
      rewrite (bswap16_bytes g0 g1), (bswap16_bytes g2 g3), (bswap32_bytes g12 g13 g14 g15), (bswap32_bytes g16 g17 g18 g19) by lia.
      rewrite !le_of_bytes_2, !le_of_bytes_4.
      replace (g15 + 256 * g14 + 65536 * g13 + 16777216 * g12)%Z with (le4val g15 g14 g13 g12) by reflexivity.
      replace (g19 + 256 * g18 + 65536 * g17 + 16777216 * g16)%Z with (le4val g19 g18 g17 g16) by reflexivity.
      apply evtF_done. subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (CHK_HDR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m RNG2 s2' mx)
          with (sw := true) (mi := mi) (maj := (g1 + 256 * g0)%Z) (min := (g3 + 256 * g2)%Z) (n0 := g15) (n1 := g14) (n2 := g13) (n3 := g12)
               (l0 := g19) (l1 := g18) (l2 := g17) (l3 := g16);
          [exact CTX | apply INV2; assumption | exact MI3 | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia
          | exact FRA | exact FRC1 | exact POST | exact FRC2 | exact HE | exact HEB] end.
    - (* [comment removed for export] *)
      zstep. if_true.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mx _ [] _ FW2 (Forall_nil _) G2 MU2 WM2 ltac:(lia)) as [G4 AG4];
        assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mx)
          by (eapply agrees_on_trans; [exact AGm2|]; eapply agrees_on_weaken; [exact AG4|]; intros a (K & _); split; [exact K| exact I])
      end.
      cbv iota. rewrite !le_of_bytes_2, !le_of_bytes_4.
      replace (g12 + 256 * g13 + 65536 * g14 + 16777216 * g15)%Z with (le4val g12 g13 g14 g15) by reflexivity.
      replace (g16 + 256 * g17 + 65536 * g18 + 16777216 * g19)%Z with (le4val g16 g17 g18 g19) by reflexivity.
      apply evtF_done. subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (CHK_HDR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m RNG2 s2' mx)
          with (sw := false) (mi := mi) (maj := (g0 + 256 * g1)%Z) (min := (g2 + 256 * g3)%Z) (n0 := g12) (n1 := g13) (n2 := g14) (n3 := g15)
               (l0 := g16) (l1 := g17) (l2 := g18) (l3 := g19);
          [exact CTX | apply INV2; assumption | exact MI3 | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia
          | exact FRA | exact FRC1 | exact HD5 | exact FRC2 | exact HE | exact HEB] end.
  Qed.
  End Sz1.
  #[using="GL FREAD CHK_HDR CHK_SHORT"] Lemma chk_tail : ltac:(let t := eval cbv delta [chk_tail__stmt] in chk_tail__stmt in exact t).
  Proof. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a0 a1 a2 a3 a6 a7 r19 r20 r23 t3 t4 t5 t6 j1 j2 j3 fjunk ej k0 k1 k2 mi sw. ltac2:(SecDiet.SzSec.closeP 'chk_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkTail.
End CANSEC1.
End TwB.
End F_sfchk_tailA.

(* [comment removed for export] *)
Module F_sfchk_shortA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_tailA.
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
Section ChkShort.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  Definition chk_short__stmt : Prop := chk_short_stmt HO FO sites GIOA TP fflagA.
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r19 r21 r23 r26 t3 t4 t5 t6 j1 j3 fj ej k0 k1 k2 c24 c32 n : ltac2:(SecDiet.SzSec.tyM 'chk_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FRET FERROR FMT SNPRINTF"] Lemma chk_short__body : ltac2:(SecDiet.SzSec.bodyP 'chk_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros CTX INV NR N20 FRA FRC HE HEB.
    chk_setup GL CTX INV.
    set (POSTQ := check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR [mg0; mg1; mg2; mg3] f m (ps_outfile s)).
    unfold read_fail_msg. cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    apply implMG_bind_assoc.
    apply implMG_from_evtF. do 3 zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := CL ++ []) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (f := f) (Af := FA);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. destruct PO as (FP3 & av & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 555308)) with (Z_to_bv 64 555308) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [app] in AG3, G3.
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    assert (KST : forall A cs, rw_cells asegs mm A cs -> (SPA <= A)%Z -> rw_cells asegs m3 A cs)
      by (intros A cs HC HA; eapply agrees_rw_cells; [exact AG3| exact HC|]; intros a Ha; left; lia).
    assert (KFR : forall A cs, rw_cells asegs mm A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 128)%Z -> rw_cells asegs m3 A cs)
      by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG3| exact HC|]; intros a Ha;
          right; right; left; apply in_frames_In; exists (FF_CHECK_HEADER, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    assert (KOB : forall A k cs, rw_cells asegs mm A cs -> clocA FL CL A k -> Z.of_nat (cells_size cs) = k -> rw_cells asegs m3 A cs)
      by (intros A k cs HC LOC HSz; eapply agrees_rw_cells; [exact AG3| exact HC|]; intros a Ha;
          eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]).
    apply KST in FR; [|lia]. apply KST in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG3) in STG; [|intros a Ha; left; lia].
    apply KFR in FRC; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in SHC;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; right; right; apply in_frame_sh_In; exists (FF_CHECK_HEADER, Fb, 128%Z);
        split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]].
    apply (KOB _ 4%Z) in HE; [|exact (proj1 OERR)|reflexivity].
    apply (KOB _ 256%Z) in HEB; [|exact (proj1 OEB)|reflexivity].
    apply (KOB _ 4%Z) in MGc; [|exact (proj1 OMG)|reflexivity].
    assert (AGm3 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m3).
    { eapply agrees_on_trans; [exact AG|]. eapply (keeps_callee0 (CL ++ []) (FF_CHECK_HEADER, Fb, 128%Z) FL _ _ CL (bv_unsigned sp) SPA); [exact ICL| lia| exact AG3]. }
    clear KST KFR KOB.
    (* [comment removed for export] *)
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND'| apply Forall_cons; [exact EBBAND'| apply Forall_nil]]).
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AGm3 FXB) as AGsh.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G3 ICL IFL AGsh ltac:(lia)) as OEBm.
    assert (OEB' : cobjA RNG3 m3 ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) (CL ++ []) EB 256)
      by (split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEBm) ICL IFL)| exact (proj2 OEBm)]).
    assert (INV3 : forall RNGy sy my, fp_le RNG3 RNGy -> GIOA L RNGy sy (CL ++ []) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) my -> ps_outfile sy = ps_outfile s ->
              mem_inv asegs my -> stk asegs my lo SPA -> stk asegs my (SPA + 88) (bv_unsigned sp + -104) ->
              rw_cells asegs my (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m my ->
              rw_cells asegs my MG [C1 (b8 mg0); C1 (b8 mg1); C1 (b8 mg2); C1 (b8 mg3)] ->
              rw_cells asegs my (Z.shiftr Fb 3 + 2147450880) chk_shadow ->
              chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNGy sy [] my).
    { intros RNGy sy my X0 X1 X1' X2 X3 X4 X5 X6 X7 X8. unfold chk_inv. split; [eapply fp_le_trans; [exact FP|]; eapply fp_le_trans; [exact FP3| exact X0]|].
      split; [exact X1|]. split; [exact X1'|]. repeat (split; [assumption|]). assumption. }
    destruct r.
    - (* [comment removed for export] *)
      destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
      unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
      apply implMG_errno_ll. set (e := lc_errno (ps_libc sx)) in *.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 RTLS) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m3 0x21b80 "error reading dump file"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21b80 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      apply implMG_from_evtF. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      ck TUNP 4%Z 0x87944%Z [11%Z; 12%Z].
      zstep.
      do 4 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      apply evtF_done. eapply implMG_bind.
      { eapply (FMT _ spa) with (L := L) (s := sx) (CL := CL ++ []) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (EB := EB)
                               (FMTA := 0x21b80%Z) (e := e) (fs := "error reading dump file"%string) (args := []) (junk := ej);
          [ split; [exact G3|]; rewrite Hspa; split; [exact ST3|]; split; [lia|]; split; [unfold PCAP_L1_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | cbn [map fb_fn fst]; intros [X|X]; [discriminate X|];
            exact (NF FF_FMT_ERRMSG ltac:(unfold frames_check_header, frames_pcap_check_header; right; left; reflexivity) X)
          | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor
          | exact HEB | exact OEB' | exact EB8 ]. }
      intros r4 s4' RNG4 ms4 PO. cbv beta in PO. destruct PO as (FP4 & -> & PO). destruct_exs PO.
      destruct PO as (-> & OF4 & LC4 & TL4 & MI4 & ST4 & AG4 & G4 & HEB4).
      rewrite Hspa in *. clear Hspa. subst spa.
      replace (ret_pc (Z_to_bv 64 555356)) with (Z_to_bv 64 555356) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in AG4, G4.
      lazymatch type of AG4 with agrees_on _ _ ?m4 =>
        assert (KST : forall A cs, rw_cells asegs m3 A cs -> (SPA <= A)%Z -> rw_cells asegs m4 A cs)
          by (intros A cs HC HA; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [left; lia| lia]);
        assert (KFR : forall A cs, rw_cells asegs m3 A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 128)%Z -> rw_cells asegs m4 A cs)
          by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
              right; right; left; apply in_frames_In; exists (FF_CHECK_HEADER, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]);
        assert (KOB : forall A k cs, rw_cells asegs m3 A cs -> clocA FL CL A k -> Z.of_nat (cells_size cs) = k ->
                       (A + k <= EB \/ EB + 256 <= A)%Z -> rw_cells asegs m4 A cs)
          by (intros A k cs HC LOC HSz HD; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
              eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]);
        assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m4)
          by (eapply agrees_on_trans; [exact AGm3|]; eapply (keeps_callee FO GIOA fflagA GL); [exact G3| exact ICL| | | exact AG4|];
              [lia| lia| intros a _ QO _; cbn [outside fst snd] in QO; lia])
      end.
      apply KST in FR; [|lia]. apply KST in FRA; [|lia].
      apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| lia]].
      apply KFR in FRC; [|lia|cbn [cells_size csize Nat.add]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AG4) in SHC;
        [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [|lia]; right; right; right; apply in_frame_sh_In; exists (FF_CHECK_HEADER, Fb, 128%Z);
          split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]].
      apply (KOB _ 4%Z) in HE; [|exact (proj1 OERR)|reflexivity|lia].
      apply (KOB _ 4%Z) in MGc; [|exact (proj1 OMG)|reflexivity|lia].
      subst POSTQ.
      eapply (chk_fail FO GIOA TP fflagA GL FRET) with (pcX := 0x8795c%Z) (msg := fmt_errmsg "error reading dump file" [] e) (fcs := [CB 96 fj]);
        [ exact CTX
        | apply (INV3 RNG4 s4'); [exact FP4| exact G4| congruence| assumption| assumption| assumption| assumption| exact AGm4| assumption| assumption]
        | right; split; [left; reflexivity| reflexivity]
        | exact FRA | exact FRC | reflexivity | exact HE | exact HEB4
        | pose proof (fmt_errmsg_length "error reading dump file" [] e); lia
        | apply fmt_errmsg_ok; [vm_compute; reflexivity| apply args_ok_nil] ].
    - (* [comment removed for export] *)
      apply implMG_retb.
      assert (MSG : fmt_at m3 0x21bc0 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21bc0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %zu file header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(bv_unsigned sp - 57344, bv_unsigned sp)]%Z) by own_ivs.
      assert (FX : Forall (cobj_iv FL CL) [(EB, EB + 256)]%Z) by cobj_ivs.
      pose proof (munch_refl [(bv_unsigned sp - 57344, bv_unsigned sp); (EB, EB + 256)]%Z m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      apply implMG_from_evtF. zstep. if_true.
      do 6 zstep. zstep.
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      eapply evtF_cut;
        [ eapply SNPRINTF with (L := L) (s := sx) (CL := CL ++ []) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (DST := EB) (n := 256%Z)
                               (FMTA := 0x21bc0%Z) (fs := "truncated dump file; tried to read %zu file header bytes, only got %zu"%string)
                               (args := [AInt 24; AInt n]) (junk := ej);
          [ split; [exact G3|]; rewrite Hspa; split; [exact ST3|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | reflexivity | reflexivity | reflexivity | lia | exact MSG | vm_compute; reflexivity | cbn; lia
          | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
          | exact HEB | exact OEB' ]
        | ].
      cbv beta; intros ms' PO; destruct PO as (vav5 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
      unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
      unfold STDIO_STACK in MU6.
      lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end; clear MU6 WM6.
      replace (ret_pc (Z_to_bv 64 555504)) with (Z_to_bv 64 555504) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m6 _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m6 _ _ _ FW FX G3 MU WM ltac:(lia)) as [G6 AG6];
        assert (AGm6 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m6)
          by (eapply agrees_on_trans; [exact AGm3|]; eapply agrees_on_weaken; [exact AG6|]; intros a (K & (_ & QN & _)); split; [exact K|]; split; [exact QN| exact I])
      end.
      change (Z.to_nat 256) with 256%nat in HEB6.
      set (msg := Fmt.snprintf 256 "truncated dump file; tried to read %zu file header bytes, only got %zu" [AInt 24; AInt n]) in *.
      pose proof (snprintf_length_le 256 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 24; AInt n] ltac:(lia)) as LS. fold msg in LS.
      replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB6 by lia.
      apply evtF_done. subst POSTQ. unfold Msg.trunc_file_header, PCAP_ERRBUF_SIZE. fold msg.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?m6 _) =>
        eapply (chk_fail FO GIOA TP fflagA GL FRET) with (mm := m6) (pcX := 0x879f0%Z) (msg := msg) (fcs := [CB 96 fj]);
          [ exact CTX
          | apply (INV3 RNG3 sx); [apply fp_le_refl| exact G6| exact OF| assumption| assumption| assumption| assumption| exact AGm6| assumption| assumption]
          | right; split; [right; reflexivity| reflexivity]
          | exact FRA | exact FRC | reflexivity | exact HE | exact HEB6 | lia
          | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ] end.
  Qed.
  End Sz3.
  #[using="GL FRET FERROR FMT SNPRINTF"] Lemma chk_short : ltac:(let t := eval cbv delta [chk_short__stmt] in chk_short__stmt in exact t).
  Proof. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r19 r21 r23 r26 t3 t4 t5 t6 j1 j3 fj ej k0 k1 k2 c24 c32 n. ltac2:(SecDiet.SzSec.closeP 'chk_short__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkShort.
End CANSEC1.

(* [comment removed for export] *)

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_tailA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Section ChkShort.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  Definition chk_short__stmt : Prop := chk_short_stmt HO FO sites GIOA TP fflagA.
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r23 r24 t3 t4 t5 t6 j1 j3 fj ej k0 k1 k2 c24 c32 n : ltac2:(SecDiet.SzSec.tyM 'chk_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="GL FRET FERROR FMT SNPRINTF"] Lemma chk_short__body : ltac2:(SecDiet.SzSec.bodyP 'chk_short__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros CTX INV NR N20 FRA FRC HE HEB.
    chk_setup GL CTX INV.
    set (POSTQ := check_header_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR [mg0; mg1; mg2; mg3] f m (ps_outfile s)).
    unfold read_fail_msg. cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    apply implMG_bind_assoc.
    apply implMG_from_evtF. do 3 zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := CL ++ []) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (f := f) (Af := FA);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. destruct PO as (FP3 & av & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 556528)) with (Z_to_bv 64 556528) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [app] in AG3, G3.
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    assert (KST : forall A cs, rw_cells asegs mm A cs -> (SPA <= A)%Z -> rw_cells asegs m3 A cs)
      by (intros A cs HC HA; eapply agrees_rw_cells; [exact AG3| exact HC|]; intros a Ha; left; lia).
    assert (KFR : forall A cs, rw_cells asegs mm A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 128)%Z -> rw_cells asegs m3 A cs)
      by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG3| exact HC|]; intros a Ha;
          right; right; left; apply in_frames_In; exists (FF_CHECK_HEADER, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    assert (KOB : forall A k cs, rw_cells asegs mm A cs -> clocA FL CL A k -> Z.of_nat (cells_size cs) = k -> rw_cells asegs m3 A cs)
      by (intros A k cs HC LOC HSz; eapply agrees_rw_cells; [exact AG3| exact HC|]; intros a Ha;
          eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]).
    apply KST in FR; [|lia]. apply KST in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG3) in STG; [|intros a Ha; left; lia].
    apply KFR in FRC; [|lia|cbn [cells_size csize Nat.add]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in SHC;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; right; right; apply in_frame_sh_In; exists (FF_CHECK_HEADER, Fb, 128%Z);
        split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]].
    apply (KOB _ 4%Z) in HE; [|exact (proj1 OERR)|reflexivity].
    apply (KOB _ 256%Z) in HEB; [|exact (proj1 OEB)|reflexivity].
    apply (KOB _ 4%Z) in MGc; [|exact (proj1 OMG)|reflexivity].
    assert (AGm3 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m3).
    { eapply agrees_on_trans; [exact AG|]. eapply (keeps_callee0 (CL ++ []) (FF_CHECK_HEADER, Fb, 128%Z) FL _ _ CL (bv_unsigned sp) SPA); [exact ICL| lia| exact AG3]. }
    clear KST KFR KOB.
    (* [comment removed for export] *)
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND'| apply Forall_cons; [exact EBBAND'| apply Forall_nil]]).
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G IFL AGm3 FXB) as AGsh.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G3 ICL IFL AGsh ltac:(lia)) as OEBm.
    assert (OEB' : cobjA RNG3 m3 ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) (CL ++ []) EB 256)
      by (split; [exact (clocA_incl _ _ _ _ _ _ (proj1 OEBm) ICL IFL)| exact (proj2 OEBm)]).
    assert (INV3 : forall RNGy sy my, fp_le RNG3 RNGy -> GIOA L RNGy sy (CL ++ []) FB ((FF_CHECK_HEADER, Fb, 128%Z) :: FL) my -> ps_outfile sy = ps_outfile s ->
              mem_inv asegs my -> stk asegs my lo SPA -> stk asegs my (SPA + 88) (bv_unsigned sp + -104) ->
              rw_cells asegs my (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
              agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m my ->
              rw_cells asegs my MG [C1 (b8 mg0); C1 (b8 mg1); C1 (b8 mg2); C1 (b8 mg3)] ->
              rw_cells asegs my (Z.shiftr Fb 3 + 2147450880) chk_shadow ->
              chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNGy sy [] my).
    { intros RNGy sy my X0 X1 X1' X2 X3 X4 X5 X6 X7 X8. unfold chk_inv. split; [eapply fp_le_trans; [exact FP|]; eapply fp_le_trans; [exact FP3| exact X0]|].
      split; [exact X1|]. split; [exact X1'|]. repeat (split; [assumption|]). assumption. }
    destruct r.
    - (* [comment removed for export] *)
      destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
      unfold errmsg_for_errno. cbn [mo_bind mo_ret MOps e_last_errno e_fenter e_fret prims].
      apply implMG_errno_ll. set (e := lc_errno (ps_libc sx)) in *.
      destruct (gl_tls _ _ _ GL _ _ _ _ _ _ _ G3 RTLS) as (T0 & T47 & TUNP & TRNG & (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) & _).
      assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
      assert (MSG : fmt_at m3 0x21b80 "error reading dump file"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21b80 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      apply implMG_from_evtF. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      zstep.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      pose proof ATPv_pg as TPG. pose proof atp_lin as ((TPLO & _) & _).
      assert (XX : (0 < ATP + -164 < 2 ^ 64)%Z) by (unfold ATP; atop_facts; lia).
      zstep. if_false_by (eqz_false (ATP + -164) XX).
      zstep. replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
      zstep. if_false.
      zstep.   (* [comment removed for export] *)
      ck TUNP 4%Z 0x87e1c%Z [11%Z; 12%Z].
      zstep.
      do 4 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      apply evtF_done. eapply implMG_bind.
      { eapply (FMT _ spa) with (L := L) (s := sx) (CL := CL ++ []) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (EB := EB)
                               (FMTA := 0x21b80%Z) (e := e) (fs := "error reading dump file"%string) (args := []) (junk := ej);
          [ split; [exact G3|]; rewrite Hspa; split; [exact ST3|]; split; [lia|]; split; [unfold PCAP_L1_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | cbn [map fb_fn fst]; intros [X|X]; [discriminate X|];
            exact (NF FF_FMT_ERRMSG ltac:(unfold frames_check_header, frames_pcap_check_header; right; left; reflexivity) X)
          | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia | constructor
          | exact HEB | exact OEB' | exact EB8 ]. }
      intros r4 s4' RNG4 ms4 PO. cbv beta in PO. destruct PO as (FP4 & -> & PO). destruct_exs PO.
      destruct PO as (-> & OF4 & LC4 & TL4 & MI4 & ST4 & AG4 & G4 & HEB4).
      rewrite Hspa in *. clear Hspa. subst spa.
      replace (ret_pc (Z_to_bv 64 556596)) with (Z_to_bv 64 556596) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in AG4, G4.
      lazymatch type of AG4 with agrees_on _ _ ?m4 =>
        assert (KST : forall A cs, rw_cells asegs m3 A cs -> (SPA <= A)%Z -> rw_cells asegs m4 A cs)
          by (intros A cs HC HA; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [left; lia| lia]);
        assert (KFR : forall A cs, rw_cells asegs m3 A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 128)%Z -> rw_cells asegs m4 A cs)
          by (intros A cs HC H1 H3; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
              right; right; left; apply in_frames_In; exists (FF_CHECK_HEADER, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]);
        assert (KOB : forall A k cs, rw_cells asegs m3 A cs -> clocA FL CL A k -> Z.of_nat (cells_size cs) = k ->
                       (A + k <= EB \/ EB + 256 <= A)%Z -> rw_cells asegs m4 A cs)
          by (intros A k cs HC LOC HSz HD; eapply agrees_rw_cells; [exact AG4| exact HC|]; intros a Ha; split; [|lia];
              eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]);
        assert (AGm4 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m4)
          by (eapply agrees_on_trans; [exact AGm3|]; eapply (keeps_callee FO GIOA fflagA GL); [exact G3| exact ICL| | | exact AG4|];
              [lia| lia| intros a _ QO _; cbn [outside fst snd] in QO; lia])
      end.
      apply KST in FR; [|lia]. apply KST in FRA; [|lia].
      apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| lia]].
      apply KFR in FRC; [|lia|cbn [cells_size csize Nat.add]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AG4) in SHC;
        [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [|lia]; right; right; right; apply in_frame_sh_In; exists (FF_CHECK_HEADER, Fb, 128%Z);
          split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]].
      apply (KOB _ 4%Z) in HE; [|exact (proj1 OERR)|reflexivity|lia].
      apply (KOB _ 4%Z) in MGc; [|exact (proj1 OMG)|reflexivity|lia].
      subst POSTQ.
      eapply (chk_fail FO GIOA TP fflagA GL FRET) with (pcX := 0x87e34%Z) (msg := fmt_errmsg "error reading dump file" [] e) (fcs := [CB 96 fj]);
        [ exact CTX
        | apply (INV3 RNG4 s4'); [exact FP4| exact G4| congruence| assumption| assumption| assumption| assumption| exact AGm4| assumption| assumption]
        | left; split; [right; right; right; reflexivity| split; reflexivity]
        | exact FRA | exact FRC | reflexivity | exact HE | exact HEB4
        | pose proof (fmt_errmsg_length "error reading dump file" [] e); lia
        | apply fmt_errmsg_ok; [vm_compute; reflexivity| apply args_ok_nil] ].
    - (* [comment removed for export] *)
      apply implMG_retb.
      assert (MSG : fmt_at m3 0x21bc0 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21bc0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %zu file header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(bv_unsigned sp - 57344, bv_unsigned sp)]%Z) by own_ivs.
      assert (FX : Forall (cobj_iv FL CL) [(EB, EB + 256)]%Z) by cobj_ivs.
      pose proof (munch_refl [(bv_unsigned sp - 57344, bv_unsigned sp); (EB, EB + 256)]%Z m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      apply implMG_from_evtF. zstep. if_true.
      do 6 zstep. zstep.
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      eapply evtF_cut;
        [ eapply SNPRINTF with (L := L) (s := sx) (CL := CL ++ []) (FB := FB) (FL := (FF_CHECK_HEADER, Fb, 128%Z) :: FL) (lo := lo) (DST := EB) (n := 256%Z)
                               (FMTA := 0x21bc0%Z) (fs := "truncated dump file; tried to read %zu file header bytes, only got %zu"%string)
                               (args := [AInt 24; AInt n]) (junk := ej);
          [ split; [exact G3|]; rewrite Hspa; split; [exact ST3|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | reflexivity | reflexivity | reflexivity | lia | exact MSG | vm_compute; reflexivity | cbn; lia
          | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
          | exact HEB | exact OEB' ]
        | ].
      cbv beta; intros ms' PO; destruct PO as (vav5 & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
      unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
      unfold STDIO_STACK in MU6.
      lazymatch type of MU6 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU6 WM6 end; clear MU6 WM6.
      replace (ret_pc (Z_to_bv 64 556740)) with (Z_to_bv 64 556740) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m6 _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m6 _ _ _ FW FX G3 MU WM ltac:(lia)) as [G6 AG6];
        assert (AGm6 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m m6)
          by (eapply agrees_on_trans; [exact AGm3|]; eapply agrees_on_weaken; [exact AG6|]; intros a (K & (_ & QN & _)); split; [exact K|]; split; [exact QN| exact I])
      end.
      change (Z.to_nat 256) with 256%nat in HEB6.
      set (msg := Fmt.snprintf 256 "truncated dump file; tried to read %zu file header bytes, only got %zu" [AInt 24; AInt n]) in *.
      pose proof (snprintf_length_le 256 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 24; AInt n] ltac:(lia)) as LS. fold msg in LS.
      replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB6 by lia.
      apply evtF_done. subst POSTQ. unfold Msg.trunc_file_header, PCAP_ERRBUF_SIZE. fold msg.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?m6 _) =>
        eapply (chk_fail FO GIOA TP fflagA GL FRET) with (mm := m6) (pcX := 0x87ec4%Z) (msg := msg) (fcs := [CB 96 fj]);
          [ exact CTX
          | apply (INV3 RNG3 sx); [apply fp_le_refl| exact G6| exact OF| assumption| assumption| assumption| assumption| exact AGm6| assumption| assumption]
          | right; split; reflexivity
          | exact FRA | exact FRC | reflexivity | exact HE | exact HEB6 | lia
          | apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] ] end.
  Qed.
  End Sz3.
  #[using="GL FRET FERROR FMT SNPRINTF"] Lemma chk_short : ltac:(let t := eval cbv delta [chk_short__stmt] in chk_short__stmt in exact t).
  Proof. red. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f magic m RNGx sx mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r20 r21 r23 r24 t3 t4 t5 t6 j1 j3 fj ej k0 k1 k2 c24 c32 n. ltac2:(SecDiet.SzSec.closeP 'chk_short__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkShort.
End CANSEC1.
End TwB.
End F_sfchk_shortA.

(* [comment removed for export] *)
Module F_sfnp_psegA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

(* [comment removed for export] *)
Definition np_shadow_f8 : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 18446744073709551608); C1 (Z_to_bv 8 18446744073709551608); C1 (Z_to_bv 8 18446744073709551608);
   C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602);
   C1 (Z_to_bv 8 18446744073709551602)].

Section CANSEC1. Context {rc : runConstT}.
Section NpSeg.
  Variables (gp tp s0 s2 s6 s7 s8 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).

  Definition np_poison_seq__stmt : Prop := forall (m : mem) (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s9 s11 t3 t4 t5 t6 : word) (SPA Fb bF : Z)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 j0 j1 j2 flagw : word) (fj : list byte),
    mem_inv asegs m ->
    rw_cells asegs m SPA [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14] ->
    rw_cells asegs m Fb [C8 j0; C8 j1; C8 j2; CB (Z.to_nat 8160) fj; C8 flagw] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) (repeat (C1 (Z_to_bv 8 0)) 12) ->
    rng RNG SPA 120 -> rng RNG Fb 8192 -> rng RNG (Z.shiftr Fb 3 + 2147450880) 1024 ->
    (0 < Fb)%Z -> (Fb + 8192 <= 2147446784 + bF * 140737479966720)%Z -> (17594333495296 * bF <= Fb)%Z -> (0 <= bF <= 1)%Z ->
    (2147450880 <= Z.shiftr Fb 3 + 2147450880)%Z -> (Z.shiftr Fb 3 + 2147450880 + 1024 <= 17594333495296)%Z ->
    (Fb + 8192 <= SPA)%Z -> (17594333495296 <= SPA)%Z -> (SPA + 120 <= 2^47)%Z ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR (Z_to_bv 64 0x882c0) (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)) (Z_to_bv 64 512)
                      (Z_to_bv 64 557448) (Z_to_bv 64 18446744073709551602) (Z_to_bv 64 18446744073709551608) a5 a6 a7
                      s2 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) s4 (Z_to_bv 64 Fb) s6 s7 s8 (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x58388) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 120); (Fb, Fb + 24); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450892)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SPA [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9;
                                  C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 w11; C8 w12; C8 w13; C8 (Z_to_bv 64 Fb)]
        /\ rw_cells asegs m' Fb [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 115235); C8 (Z_to_bv 64 557448); CB (Z.to_nat 8160) fj; C8 flagw]
        /\ rw_cells asegs m' (Z.shiftr Fb 3 + 2147450880) np_shadow_f8)
      (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 Fb) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x88204) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables m ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s9 s11 t3 t4 t5 t6 SPA Fb bF w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 j0 j1 j2 flagw fj : ltac2:(SecDiet.SzSec.tyM 'np_poison_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma np_poison_seq__body : ltac2:(SecDiet.SzSec.bodyP 'np_poison_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros MI FRW FRC SH12 RSPA FRNG FSRNG Fb0 bFhi bFlo bFr SLO SHI FSP SPALO SPAHI.
    qfold.
    cbn [repeat] in SH12.
    pose proof (munch_refl [(SPA, SPA + 120); (Fb, Fb + 24); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450892)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    do 2 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    zstep.
    do 9 zstep. neg_lits.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    do 4 zstep.
    zstep_sh0. do 3 zstep.
    do 4 zstep.
    zstep.
    do 2 zstep.
    zstep.
    apply evtF_done. eexists. split; [reflexivity|].
    unfold np_shadow_f8. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz1.
  #[using="Type"] Lemma np_poison_seq : ltac:(let t := eval cbv delta [np_poison_seq__stmt] in np_poison_seq__stmt in exact t).
  Proof. intros m ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s9 s11 t3 t4 t5 t6 SPA Fb bF w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 j0 j1 j2 flagw fj. ltac2:(SecDiet.SzSec.closeP 'np_poison_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  Definition np_f3_seq__stmt : Prop := forall (m : mem) (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s10 s11 t3 t4 t5 t6 : word) (P Fb : Z),
    mem_inv asegs m ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147451404) (repeat (C1 (Z_to_bv 8 0)) 16) ->
    rng RNG (Z.shiftr Fb 3 + 2147450880) 1024 ->
    (2147450880 <= Z.shiftr Fb 3 + 2147450880)%Z -> (Z.shiftr Fb 3 + 2147450880 + 1024 <= 17594333495296)%Z ->
    (0 < P)%Z -> (P + 664 <= 2^47)%Z ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 48)) (Z_to_bv 64 18446744073709551603) a2 a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x88308) fc None m' (seg_rom asegs)
        /\ munch [(Z.shiftr Fb 3 + 2147451404, Z.shiftr Fb 3 + 2147451420)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x882c0) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables m ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s10 s11 t3 t4 t5 t6 P Fb : ltac2:(SecDiet.SzSec.tyM 'np_f3_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma np_f3_seq__body : ltac2:(SecDiet.SzSec.bodyP 'np_f3_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros MI SH16 FSRNG SLO SHI P0 PHI.
    qfold.
    cbn [repeat] in SH16.
    pose proof (munch_refl [(Z.shiftr Fb 3 + 2147451404, Z.shiftr Fb 3 + 2147451420)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    zstep. neg_lits. zstep.
    do 16 zstep.
    apply evtF_done. eexists. split; [reflexivity|].
    repeat (split; [assumption|]). assumption.
  Qed.
  End Sz2.
  #[using="Type"] Lemma np_f3_seq : ltac:(let t := eval cbv delta [np_f3_seq__stmt] in np_f3_seq__stmt in exact t).
  Proof. intros m ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s10 s11 t3 t4 t5 t6 P Fb. ltac2:(SecDiet.SzSec.closeP 'np_f3_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  Definition np_s1_seq__stmt : Prop := forall (m : mem) (ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s11 t3 t4 t5 t6 : word) (P Fb bP : Z),
    mem_inv asegs m ->
    unpoisoned m P (P + 664) -> rng RNG P 664 -> rng RNG (shad P) (nshad 664) ->
    rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + 648))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) np_shadow_f8 ->
    rng RNG (Z.shiftr Fb 3 + 2147450880) 1024 ->
    (P mod 16 = 0)%Z -> (0 < P)%Z -> (P + 664 <= 2147446784 + bP * 140737479966720)%Z -> (17594333495296 * bP <= P)%Z -> (0 <= bP <= 1)%Z -> (6303744 <= P)%Z ->
    (2147450880 <= Z.shiftr Fb 3 + 2147450880)%Z -> (Z.shiftr Fb 3 + 2147450880 + 1024 <= 17594333495296)%Z ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 48)) z64 a2 a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 648)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x88328) fc None m' (seg_rom asegs)
        /\ munch [(Z.shiftr Fb 3 + 2147450884, Z.shiftr Fb 3 + 2147450887)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (Z.shiftr Fb 3 + 2147450880) np_shadow)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 48)) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x88308) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables m ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s11 t3 t4 t5 t6 P Fb bP : ltac2:(SecDiet.SzSec.tyM 'np_s1_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma np_s1_seq__body : ltac2:(SecDiet.SzSec.bodyP 'np_s1_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros MI PUNP PRNG PRSH C48 SH12 FSRNG P16 P0 bPhi bPlo bPr bPimg SLO SHI.
    qfold.
    unfold np_shadow_f8 in SH12.
    pose proof (munch_refl [(Z.shiftr Fb 3 + 2147450884, Z.shiftr Fb 3 + 2147450887)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    ck0 PUNP; ck_go.
    zstep.
    do 3 zstep.
    apply evtF_done. eexists. split; [reflexivity|].
    unfold np_shadow. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz3.
  #[using="Type"] Lemma np_s1_seq : ltac:(let t := eval cbv delta [np_s1_seq__stmt] in np_s1_seq__stmt in exact t).
  Proof. intros m ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s11 t3 t4 t5 t6 P Fb bP. ltac2:(SecDiet.SzSec.closeP 'np_s1_seq__body "vvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpSeg.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac qfold := try (lazymatch goal with |- evtF ?s ?r ?Q ?st => let QQ := fresh "QQ" in pose (QQ := Q); change Q with QQ end).
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.

(* [comment removed for export] *)
Definition np_shadow_f8 : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 18446744073709551608); C1 (Z_to_bv 8 18446744073709551608); C1 (Z_to_bv 8 18446744073709551608);
   C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 18446744073709551602);
   C1 (Z_to_bv 8 18446744073709551602)].

Section CANSEC1. Context {rc : runConstT}.
Section NpSeg.
  Variables (gp tp s0 s2 s6 s7 s8 : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint).

  Definition np_poison_seq__stmt : Prop := forall (m : mem) (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s9 s11 t3 t4 t5 t6 : word) (SPA Fb bF : Z)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 j0 j1 j2 flagw : word) (fj : list byte),
    mem_inv asegs m ->
    rw_cells asegs m SPA [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w8; C8 w7; C8 w10; C8 w9; C8 w11; C8 w12; C8 w13; C8 w14] ->
    rw_cells asegs m Fb [C8 j0; C8 j1; C8 j2; CB (Z.to_nat 8160) fj; C8 flagw] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) (repeat (C1 (Z_to_bv 8 0)) 12) ->
    rng RNG SPA 120 -> rng RNG Fb 8192 -> rng RNG (Z.shiftr Fb 3 + 2147450880) 1024 ->
    (0 < Fb)%Z -> (Fb + 8192 <= 2147446784 + bF * 140737479966720)%Z -> (17594333495296 * bF <= Fb)%Z -> (0 <= bF <= 1)%Z ->
    (2147450880 <= Z.shiftr Fb 3 + 2147450880)%Z -> (Z.shiftr Fb 3 + 2147450880 + 1024 <= 17594333495296)%Z ->
    (Fb + 8192 <= SPA)%Z -> (17594333495296 <= SPA)%Z -> (SPA + 120 <= 2^47)%Z ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR (Z_to_bv 64 0x886d8) (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)) (Z_to_bv 64 512)
                      (Z_to_bv 64 558496) (Z_to_bv 64 18446744073709551602) (Z_to_bv 64 18446744073709551608) a5 a6 a7
                      s2 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) s4 (Z_to_bv 64 Fb) s6 s7 s8 (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x583f0) fc None m' (seg_rom asegs)
        /\ munch [(SPA, SPA + 120); (Fb, Fb + 24); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450892)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' SPA [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w8; C8 w7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                                  C8 w9; C8 w11; C8 w12; C8 w13; C8 (Z_to_bv 64 Fb)]
        /\ rw_cells asegs m' Fb [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 115227); C8 (Z_to_bv 64 558496); CB (Z.to_nat 8160) fj; C8 flagw]
        /\ rw_cells asegs m' (Z.shiftr Fb 3 + 2147450880) np_shadow_f8)
      (MS (mkR ra (Z_to_bv 64 SPA) gp tp t0 t1 t2 s0 (Z_to_bv 64 SPA) (Z_to_bv 64 Fb) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 2147450880) s9 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8861c) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables m ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s9 s11 t3 t4 t5 t6 SPA Fb bF w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 j0 j1 j2 flagw fj : ltac2:(SecDiet.SzSec.tyM 'np_poison_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma np_poison_seq__body : ltac2:(SecDiet.SzSec.bodyP 'np_poison_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI FRW FRC SH12 RSPA FRNG FSRNG Fb0 bFhi bFlo bFr SLO SHI FSP SPALO SPAHI.
 qfold.
    cbn [repeat] in SH12.
    pose proof (munch_refl [(SPA, SPA + 120); (Fb, Fb + 24); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450892)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    do 2 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    zstep.
    do 9 zstep. neg_lits.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    do 4 zstep.
    zstep_sh0. do 3 zstep.
    do 4 zstep.
    zstep.
    do 2 zstep.
    zstep.
    apply evtF_done. eexists. split; [reflexivity|].
    unfold np_shadow_f8. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz1.
  #[using="Type"] Lemma np_poison_seq : ltac:(let t := eval cbv delta [np_poison_seq__stmt] in np_poison_seq__stmt in exact t).
  Proof. intros m ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s9 s11 t3 t4 t5 t6 SPA Fb bF w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 j0 j1 j2 flagw fj. ltac2:(SecDiet.SzSec.closeP 'np_poison_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  Definition np_f3_seq__stmt : Prop := forall (m : mem) (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s10 s11 t3 t4 t5 t6 : word) (P Fb : Z),
    mem_inv asegs m ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147451404) (repeat (C1 (Z_to_bv 8 0)) 16) ->
    rng RNG (Z.shiftr Fb 3 + 2147450880) 1024 ->
    (2147450880 <= Z.shiftr Fb 3 + 2147450880)%Z -> (Z.shiftr Fb 3 + 2147450880 + 1024 <= 17594333495296)%Z ->
    (0 < P)%Z -> (P + 664 <= 2^47)%Z -> (P mod 16 = 0)%Z ->   (* [comment removed for export] *)
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 48)) a1 a2 a3 a4 a5 a6 a7   (* [comment removed for export] *)
                      s2 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) s5 s6 s7 s8 s10 s9 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8872c) fc None m' (seg_rom asegs)
        /\ munch [(Z.shiftr Fb 3 + 2147451404, Z.shiftr Fb 3 + 2147451420)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) s5 s6 s7 s8 s10 s9 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x886d8) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables m ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s10 s11 t3 t4 t5 t6 P Fb : ltac2:(SecDiet.SzSec.tyM 'np_f3_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma np_f3_seq__body : ltac2:(SecDiet.SzSec.bodyP 'np_f3_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI SH16 FSRNG SLO SHI P0 PHI P16.
 qfold.
    cbn [repeat] in SH16.
    pose proof (munch_refl [(Z.shiftr Fb 3 + 2147451404, Z.shiftr Fb 3 + 2147451420)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    zstep. neg_lits.
    do 16 zstep.
    ub_null.
    zstep. ub_al 7%Z ltac:(al16 P16). zstep. if_false.
    zstep.
    apply evtF_done. eexists. split; [reflexivity|].
    repeat (split; [assumption|]). assumption.
  Qed.
  End Sz2.
  #[using="Type"] Lemma np_f3_seq : ltac:(let t := eval cbv delta [np_f3_seq__stmt] in np_f3_seq__stmt in exact t).
  Proof. intros m ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s10 s11 t3 t4 t5 t6 P Fb. ltac2:(SecDiet.SzSec.closeP 'np_f3_seq__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  Definition np_s1_seq__stmt : Prop := forall (m : mem) (ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s11 t3 t4 t5 t6 : word) (P Fb bP : Z),
    mem_inv asegs m ->
    unpoisoned m P (P + 664) -> rng RNG P 664 -> rng RNG (shad P) (nshad 664) ->
    rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 (P + 648))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) np_shadow_f8 ->
    rng RNG (Z.shiftr Fb 3 + 2147450880) 1024 ->
    (P mod 16 = 0)%Z -> (0 < P)%Z -> (P + 664 <= 2147446784 + bP * 140737479966720)%Z -> (17594333495296 * bP <= P)%Z -> (0 <= bP <= 1)%Z -> (6307840 <= P)%Z ->
    (2147450880 <= Z.shiftr Fb 3 + 2147450880)%Z -> (Z.shiftr Fb 3 + 2147450880 + 1024 <= 17594333495296)%Z ->
    evtF asegs RNG (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 48)) z64 a2 a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) s5 s6 s7 s8 (Z_to_bv 64 2147450880) s9 (Z_to_bv 64 (P + 648)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8874c) fc None m' (seg_rom asegs)
        /\ munch [(Z.shiftr Fb 3 + 2147450884, Z.shiftr Fb 3 + 2147450887)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (Z.shiftr Fb 3 + 2147450880) np_shadow)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 48)) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) s5 s6 s7 s8 (Z_to_bv 64 2147450880) s9 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8872c) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables m ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s11 t3 t4 t5 t6 P Fb bP : ltac2:(SecDiet.SzSec.tyM 'np_s1_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvv" @m).
  #[using="Type"] Lemma np_s1_seq__body : ltac2:(SecDiet.SzSec.bodyP 'np_s1_seq__stmt "vvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros MI PUNP PRNG PRSH C48 SH12 FSRNG P16 P0 bPhi bPlo bPr bPimg SLO SHI.
 qfold.
    unfold np_shadow_f8 in SH12.
    pose proof (munch_refl [(Z.shiftr Fb 3 + 2147450884, Z.shiftr Fb 3 + 2147450887)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    ck0 PUNP; ck_go.
    zstep.
    do 3 zstep.
    apply evtF_done. eexists. split; [reflexivity|].
    unfold np_shadow. repeat (split; [assumption|]). assumption.
  Qed.
  End Sz3.
  #[using="Type"] Lemma np_s1_seq : ltac:(let t := eval cbv delta [np_s1_seq__stmt] in np_s1_seq__stmt in exact t).
  Proof. intros m ra sp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s5 s9 s11 t3 t4 t5 t6 P Fb bP. ltac2:(SecDiet.SzSec.closeP 'np_s1_seq__body "vvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpSeg.
End CANSEC1.
End TwB.
End F_sfnp_psegA.

(* [comment removed for export] *)
Module F_sfpcap_chk_allA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad PcapTypes Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_gotA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfpcap_chkA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_fillA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_hdrA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_tailA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_shortA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfpcap_chkA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section ChkAll.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis GOTL : gia_got_law GIOA.
  Hypothesis FENTER1 : fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis OPEN_COMMON : open_offline_common_stmt HO FO sites GIOA TP.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.

  #[using="fflagA GL GPL GOTL FENTER1 FRET FREAD FERROR FMT SNPRINTF OPEN_COMMON LT2DLT ADJSNAP MALLOC"] Theorem pcap_check_header_allA : pcap_check_header_stmt HO FO sites GIOA TP.
  Proof.
    eapply pcap_check_header_proofA; [exact GL | exact FENTER1 | exact FRET |].
    eapply chk_tail; [exact GL | exact FREAD | | ].
    - eapply chk_hdr; [exact GL | exact FRET | exact SNPRINTF | exact OPEN_COMMON | exact GPL |].
      eapply chk_fill; [exact GL | exact FRET | exact GPL | exact GOTL | exact LT2DLT | exact ADJSNAP | exact MALLOC].
    - eapply chk_short; [exact GL | exact FRET | exact FERROR | exact FMT | exact SNPRINTF].
  Qed.
End ChkAll.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_sfchk_fsegA__B3P.F_sfchk_fillA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_hdrA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_tailA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfchk_shortA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfpcap_chkA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section ChkAll.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis GOTL : gia_got_law GIOA.
  Hypothesis FENTER1 : fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis OPEN_COMMON : open_offline_common_stmt HO FO sites GIOA TP.
  Hypothesis LT2DLT : linktype_to_dlt_stmt.
  Hypothesis ADJSNAP : adjust_snapshot_stmt.
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.

  #[using="fflagA GL GPL GOTL FENTER1 FRET FREAD FERROR FMT SNPRINTF OPEN_COMMON LT2DLT ADJSNAP MALLOC"] Theorem pcap_check_header_allA : pcap_check_header_stmt HO FO sites GIOA TP.
  Proof.
    eapply pcap_check_header_proofA; [exact GL | exact FENTER1 | exact FRET |].
    eapply chk_tail; [exact GL | exact FREAD | | ].
    - eapply chk_hdr; [exact GL | exact FRET | exact SNPRINTF | exact OPEN_COMMON | exact GPL |].
      eapply chk_fill; [exact GL | exact FRET | exact GPL | exact GOTL | exact LT2DLT | exact ADJSNAP | exact MALLOC].
    - eapply chk_short; [exact GL | exact FRET | exact FERROR | exact FMT | exact SNPRINTF].
  Qed.
End ChkAll.
End CANSEC1.
End TwB.
End F_sfpcap_chk_allA.
