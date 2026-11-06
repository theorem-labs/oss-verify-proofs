(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32A : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

(* [comment removed for export] *)
Local Ltac nlb_hyp A :=
  repeat match goal with
  | H : rw_cells _ _ A ?cs |- _ =>
      match cs with context [C1 (Z_to_bv 8 ?z)] =>
        is_Zlit z; let z' := eval vm_compute in (Z.modulo z 256) in
        tryif constr_eq z z' then fail else
        replace (Z_to_bv 8 z) with (Z_to_bv 8 z') in H by (apply (proj2 (bv_eq _ _ _)); reflexivity)
      end
  end.
Local Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store; try nlb_hyp A
      | _ => idtac
      end
  | _ => idtac
  end.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section OfflineRead.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER1 : fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis NP_PCAP : pcap_next_packet_stmt HO FO sites GIOA TP.
  Hypothesis NP_NG : pcap_ng_next_packet_stmt HO FO sites GIOA TP.
  Hypothesis ONESHOT : oneshot_stmt.

  Lemma next_packet_op_any : forall ng, next_packet_op_stmt_for HO FO sites GIOA TP ng.
  Proof using NP_NG NP_PCAP. intros [|]; [exact NP_NG | exact NP_PCAP]. Qed.

  (* [comment removed for export] *)
  Definition or_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb st : Z) (m : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r25 r26 r27 t3 t4 t5 t6 : word)
      (jS1 jS2 fj : list byte) (k0 k1 k2 : word) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z -> (-2147483648 <= st < 2147483648)%Z ->
    GIOA L RNG s (CLc ++ PB) FB ((FF_OFFLINE_READ, Fb, 128%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 88) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA [CB 24 jS1; C8 (Z_to_bv 64 Fb); CB 56 jS2] ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 96 fj; C8 (Z_to_bv 64 (fflagA L FF_OFFLINE_READ Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_OFFLINE_READ x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 st) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m' /\ agrees_on (fun a => in_block (CLc ++ PB) a) m m'
           /\ GIOA L RNG s' (CLc ++ PB) FB FL m' /\ ps_outfile s' = ps_outfile s)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 (Z_to_bv 64 st) r21 r22 r23 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r25 r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x85580) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb st m ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r25 r26 r27 t3 t4 t5 t6 jS1 jS2 fj k0 k1 k2 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 A x : ltac2:(SecDiet.SzSec.tyM 'or_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma or_epi__body : ltac2:(SecDiet.SzSec.bodyP 'or_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FRET GL.
 intros SPAB SPA32 LO LOS SPT TOP47 SX G MI ST STG FRA FR FRC SHC RSTK.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).   (* [comment removed for export] *)
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (SWR : forall z, (-2147483648 <= z < 2147483648)%Z -> bv_swrap 32 (z mod 18446744073709551616 + 0) = z).
    { intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z. Z.div_mod_to_equations. lia. }
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND FTOP F64 _ FRNG FSRNG _ _; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 128 3) with 16%Z in FSRNG.
    (pose proof (ablk_lin _ _ FBAND) as ndP__; nd_pre ndP__ 4%nat; intros _ Fb0 _ _; nd_post). band_ind FBAND bF.
    (nd_pre (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) 6%nat; intros _ FLR FLB FLT _ (kF & kFr & kF1 & kF2); nd_post). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    assert (FW : Forall (own_ivA [(FF_OFFLINE_READ, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    do 4 zstep.
    do 3 zstep.
    zstep. zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    burst_begin [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z [Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 4 zstep. zstep_sh0. do 11 zstep.
    burst_end MUb WMb.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block (CLc ++ PB) a) m mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha;
            exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a Ha));
      pose proof (munch_refl [(fflagA L FF_OFFLINE_READ Fb, fflagA L FF_OFFLINE_READ Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 17 zstep.
    rewrite (SWR st) by lia.
    release_frame FRA ST (SPA + 88)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CLc (bv_unsigned sp) G5 MU2 WM2 (incl_appl _ (incl_refl _)) ltac:(lia)) as [AG6 AGP6].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split. { eapply agrees_on_trans; [exact AGP5| exact AGP6]. }
    split; [exact G6| exact OF3].
  Qed.
  End Sz3.
  Lemma or_epi : ltac:(let t := eval cbv delta [or_epi__stmt] in or_epi__stmt in exact t).
  Proof using FRET GL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CLc PB FB FL lo SPA Fb st m ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r21 r22 r23 r25 r26 r27 t3 t4 t5 t6 jS1 jS2 fj k0 k1 k2 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 A x. ltac2:(SecDiet.SzSec.closeP 'or_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition offline_read_proofA__stmt : Prop := offline_read_stmt HO FO sites GIOA TP.
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P U PKT p fuel pd pkc : ltac2:(SecDiet.SzSec.tyM 'offline_read_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma offline_read_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'offline_read_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FENTER1 FRET GL NP_NG NP_PCAP ONESHOT.
 intros PRE UC TR NF PC -> -> -> -> HU HPK Hpk OU OPK D1 AU AK.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| unfold PCAP_L3_STACK in BU; lia]).   (* [comment removed for export] *)
    pose proof (PCAPR_self_in _ _ _ _ _ PC) as HinP.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 3%nat; intros (PBAND & P3 & PTOP & P2) P1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    pose proof (psize_pos p) as PS. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (UL : clocA FL (CLc ++ PB) U 24) by (eapply clocA_incl; [exact (proj1 OU)| apply incl_appl; apply incl_refl| apply incl_refl]).
    assert (PKL : clocA FL (CLc ++ PB) PKT 8) by (eapply clocA_incl; [exact (proj1 OPK)| apply incl_appl; apply incl_refl| apply incl_refl]).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G UL) as (ULO & UHI). pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G PKL) as (PKLO & PKHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G UL ltac:(lia)) as UBAND. pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G PKL ltac:(lia)) as PKBAND.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (proj1 OU) HinP ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kUP kUPr kUP1 kUP2; nd_post).
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (proj1 OPK) HinP ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kKP kKPr kKP1 kKP2; nd_post).
    cbn [cb_addr cb_size fst snd] in kUP1, kUP2, kKP1, kKP2.
    pose proof UBAND as UBAND'. pose proof PKBAND as PKBAND'. band_ind UBAND bU. band_ind PKBAND bK.
    band_ind PBAND bP.
    destruct (rw_cells_forget _ _ _ _ HPK) as [pkj HPc]. clear HPK. cbn [cells_size] in HPc. rewrite Hpk in HPc. change (8 + 0)%nat with 8%nat in HPc.
    unfold pcapint_offline_read_1. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]. unfold PCAP_OFFLINE_READ_ENTRY.
    remember (bv_unsigned sp - 192 - (bv_unsigned sp - 192) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -192) - (bv_unsigned sp + -192) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| unfold PCAP_L3_STACK in BU; lia]).   (* [comment removed for export] *)
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 88%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    rewrite land_m32A by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -104)%Z.
    destruct (stk_split asegs _ lo (SPA + 88) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 88) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 88) with 88%Z in STL, FRA. replace (SPA + 88 - 88)%Z with SPA in STL, FRA by lia.
    zstep.
    do 3 zstep.
    do 4 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 2 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW0 : Forall (pcap_iv FL PB) [(bv_unsigned sp - 208, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ PB) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW0]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FW0.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER1 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { apply NF. left. reflexivity. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_OFFLINE_READ) with 128%Z in *.
    change (Z.to_nat (128 - 32)) with 96%nat in *. change (Z.to_nat (128 / 8)) with 16%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 545920)) with (Z_to_bv 64 545920) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND' FTOP' F64 _ FRNG FSRNG _ FSWR; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HU; [|intros a Ha; eapply clocA_keeps; [exact UL| exact Ha]].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HPc; [|intros a Ha; eapply clocA_keeps; [exact PKL| exact Ha]].
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 UL ltac:(lia)) 4%nat; intros kU kUr kU1 kU2; nd_post).
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 PKL ltac:(lia)) 4%nat; intros kK kKr kK1 kK2; nd_post).
    cbn [fb_addr fb_size fst snd] in kU1, kU2, kK1, kK2.
    assert (AGb : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; apply in_block_app; left; exact Ha| apply incl_refl]. }
    assert (PC2 : PCAPR P p PB FB m2).
    { eapply PCAPR_agree; [exact AG1| intros a Ha; right; left; apply in_block_app; right; exact Ha|].
      eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU0| exact WM0| intros a _ Ho; exact Ho]| | exact PC].
      intros a Ha. pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)).
      cbn [outside]. lia. }
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    do 2 zstep. if_true_by (nez_true Fb ltac:(lia)).
    burst_begin [(SPA, SPA + 88); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z [SPA; Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 2 zstep.
    do 5 zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    do 4 zstep.
    zstep. neg_lits.
    zstep_sh0. do 3 zstep.
    zstep. neg_lits.
    do 7 zstep.
    burst_end MUb WMb.
    zstep.
    zstep. if_true.
    do 4 zstep.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_OFFLINE_READ, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G1 MU WM ltac:(lia)) as [G2 AG2];
      assert (PC3 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM| intros a _ Ho; exact Ho]| exact (pb_outside _ _ _ GL _ _ _ _ _ _ _ _ _ _ [] _ FW (Forall_nil _) G1) | exact PC2])
    end.
    (pose proof PC3 as ndP__; nd_pre ndP__ 3%nat; intros Af HinF (B & Ib & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
    (pose proof WF as ndP__; nd_pre ndP__ 13%nat; intros W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 W11 W12 W13; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 6%nat; intros _ _ PUNP PRNG PRSH _; nd_post).
    cbn [cb_addr cb_size fst snd] in PUNP, PRNG, PRSH.
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    hide BUF. hide PRIV. hide IFS. hide CE. hide CH. hide CO.
    unfold pc_pre, PCAP_PRIV_OFF in CA. rewrite W5 in CA.
    rewrite W5. cbn [Z.eqb negb].
    (* [comment removed for export] *)
    ck0 PUNP; ck_go.
    zstep.
    zstep. if_true.
    (* [comment removed for export] *)
    do 7 zstep.
    do 8 zstep.
    ck0_at PUNP (P + 8)%Z; ck_go.
    do 4 zstep.
    zstep.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 (np_entry p))) with (Z_to_bv 64 (np_entry p))
      by (unfold np_entry, PK; cbn [pk_next_ng pk_next_pcap]; destruct (is_ng p); (symmetry; apply ret_pc_even; [lia|reflexivity])).
    clear G2 AG2 PC3.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G1 MU WM ltac:(lia)) as [G3 AG3];
      assert (PC4 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM| intros a _ Ho; exact Ho]| exact (pb_outside _ _ _ GL _ _ _ _ _ _ _ _ _ _ [] _ FW (Forall_nil _) G1) | exact PC2]);
      assert (AGc : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply agrees_on_trans; [exact AGb|]; eapply agrees_on_weaken; [exact AG3|]; intros a Ha; split; [exact Ha| exact I]);
      assert (UC3 : ucallerA depth_offline_read L mm sp s0 ra trC)
        by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha;
            destruct (AGb a ltac:(lia) ltac:(left; lia)) as [E1 _]; destruct (AG3 a ltac:(lia) ltac:(split; [left; lia| exact I])) as [E2 _]; congruence)
    end.
    pose proof (keeps_frame_sh _ _ _ _ _ AGc) as AGsh.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OU G3 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as OU3.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OPK G3 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as OPK3.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FR eq_refl) as BRA.
    cbn [firstn cells_size csize Nat.add] in BS0, BRA.
    replace (bv_unsigned sp + -104 + Z.of_nat 88)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
    replace (bv_unsigned sp + -104 + Z.of_nat 96)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
    pose proof (unp_of_sh_bytes _ _ _ 4%nat 1%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPD.
    pose proof (unp_of_sh_bytes _ _ _ 8%nat 3%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPH.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPD. change (8 * Z.of_nat 1)%Z with 8%Z in UNPD.
    change (8 * Z.of_nat 8)%Z with 64%Z in UNPH. change (8 * Z.of_nat 3)%Z with 24%Z in UNPH.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs _ _ [_; _; _] 96 _ [_] [8; 8; 24; 24; 32]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [FRC1 FRC']. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FRC1, FRC'.
    destruct (rw_cells_cut _ _ _ 1 FRC') as [FRD FRC'']. clear FRC'. cbn [firstn skipn cells_size csize Nat.add] in FRD, FRC''.
    destruct (rw_cells_cut _ _ _ 1 FRC'') as [FRM FRC']. clear FRC''. cbn [firstn skipn cells_size csize Nat.add] in FRM, FRC'.
    destruct (rw_cells_cut _ _ _ 1 FRC') as [FRH FRC2]. clear FRC'. cbn [firstn skipn cells_size csize Nat.add] in FRH, FRC2.
    replace (Fb + Z.of_nat 32)%Z with (Fb + 32)%Z in * by lia. replace (Fb + 32 + Z.of_nat 8)%Z with (Fb + 40)%Z in * by lia.
    replace (Fb + 40 + Z.of_nat 24)%Z with (Fb + 64)%Z in * by lia. replace (Fb + 64 + Z.of_nat 24)%Z with (Fb + 88)%Z in * by lia.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    assert (FRIN : forall a, (Fb <= a < Fb + 128)%Z -> in_frames ((FF_OFFLINE_READ, Fb, 128%Z) :: FL) a)
      by (intros a Ha; apply in_frames_In; exists (FF_OFFLINE_READ, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    apply evtF_done. eapply implMG_bind.
    { eapply (next_packet_op_any (is_ng p) _ spa);
        [ split; [exact G3|]; rewrite Hspa; split; [eassumption|]; split; [lia|]; split; [unfold PCAP_L2_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x85650%Z UC3); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
              | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_next_packet_op, depth_offline_read, depth_pcap_ng_next_packet, depth_pcap_next_packet; destruct (is_ng p); lia]
        | rewrite unsigned_lit by lia; unfold traces_next_packet_op; (nd_pre TR 3%nat; intros T1 T2 _; nd_post); destruct (is_ng p); assumption
        | unfold frames_next_packet_op; apply nofr_cons; [eapply nofr_sub; [exact NF| destruct (is_ng p); intros f Hf; cbn in Hf |- *; clear - Hf; intuition]
                                                         | destruct (is_ng p); cbn; clear; intuition congruence]
        | exact PC4 | reflexivity | rewrite Hspa; lia | reflexivity | reflexivity | reflexivity
        | exact FRH | reflexivity | exact FRD | reflexivity
        | split; [right; exists (FF_OFFLINE_READ, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPH]
        | split; [right; exists (FF_OFFLINE_READ, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPD]
        | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]. }
    intros [[st h] p'] s2' RNG2 ms' PO. unfold next_packet_post in PO. destruct PO as (FP2 & PO). destruct_exs PO.
    (nd_pre PO 9%nat; intros E OF2 MI2 ST2 AG4 G4 PC5 PCC5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros Hst HH1 HH0 HD1 Hdw; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 546384)) with (Z_to_bv 64 546384) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [app] in G4, AG4.
    rename x0 into m6. rename x1 into PB1. rename x2 into dw.
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FR; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRA; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]].
    apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRC1; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; apply FRIN; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRM; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; apply FRIN; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRC2; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; apply FRIN; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in SHC;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; right; apply in_frame_sh_In; exists (FF_OFFLINE_READ, Fb, 128%Z);
          split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in HU;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [eapply clocA_keeps; [eapply clocA_incl; [exact (proj1 OU)| apply incl_refl| apply incl_tl; apply incl_refl]| lia]| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in HPc;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [eapply clocA_keeps; [eapply clocA_incl; [exact (proj1 OPK)| apply incl_refl| apply incl_tl; apply incl_refl]| lia]| lia]].
    destruct (rw_cells_forget _ _ _ _ HD1) as [dwj HD]. clear HD1. cbn [cells_size] in HD. rewrite Hdw in HD. change (8 + 0)%nat with 8%nat in HD. clear dw Hdw.
    (* [comment removed for export] *)
    assert (AGd : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m6).
    { eapply agrees_on_trans; [exact AGc|]. eapply agrees_on_weaken; [exact AG4|]. intros a K.
      destruct (keeps_not_own_frame _ _ _ GL _ _ _ _ _ _ _ (FF_OFFLINE_READ, Fb, 128%Z) CLc (bv_unsigned sp) a G3 (incl_appl _ (incl_refl _)) ltac:(lia) K) as [NF1 _].
      cbn [fb_addr fb_size fst snd] in NF1.
      split; [| lia]. destruct K as [K|[K|[K|K]]]; [left; lia| right; left; exact K| right; right; left; apply in_frames_cons; exact K
                                                  | right; right; right; apply in_frame_sh_cons; exact K]. }
    clear MU WM FW.
    destruct Hst as [-> | [-> | ->]].
    3:{ (* [comment removed for export] *)
      (nd_pre (HH0 ltac:(lia)) 3%nat; intros hcs' Hsz HDR0; nd_post). clear HH0 HH1.
      destruct (rw_cells_forget _ _ _ _ HDR0) as [hj HDR]. clear HDR0. rewrite Hsz in HDR.
      cbn [Z.ltb Z.eqb].
      ienterG. zstep. if_true. do 2 zstep. apply evtF_done. subst POSTQ1.
      (* [comment removed for export] *)
      pose proof (rw_cells_merge asegs _ _ [] [_; _; _] _ FRA) as FRA1. cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA1.
      lazymatch type of FRA1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
        pose proof (rw_cells_merge asegs _ _ [c0; c1] rest [] ltac:(rewrite app_nil_r; exact FRA1)) as FRA2 end.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA2. clear FRA1.
      (* [comment removed for export] *)
      pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HD (rw_cells_uncut _ _ _ _ _ FRM (rw_cells_uncut _ _ _ _ _ HDR FRC2
                    ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia))
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC.
      cbn [app] in FRC.
      lazymatch type of FRC with rw_cells _ _ _ [?h0; ?h1; ?h2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
        pose proof (rw_cells_merge asegs _ _ [h0; h1; h2] [c3; c4; c5; c6; c7] [c8] FRC) as FRCm end.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRCm.
      eapply implMG_mono.
      { eapply (or_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG2 s2' CLc PB1 FB FL lo SPA Fb (-1)%Z);
          [lia| exact SPA32| lia| lia| lia| lia| lia| exact G4| assumption| exact ST2| exact STG| exact FRA2| exact FR| exact FRCm| exact SHC| exact RSTK]. }
      intros r s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 6%nat; intros MI7 ST7 AG7 AGP7 G7 OF7; nd_post).
      subst POSTQ0 POSTQ. cbv beta iota.
      split; [exact FP2|].
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 (-1)), mm, PB1, (CB 8 pkj) end.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [congruence|]. split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGd|]; intros a (K & _); exact K|].
               eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
      split; [exact G7|].
      split; [intros X; exfalso; lia|].
      split. { intros _. eapply PCAPR_closable_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| exact (PCC5 eq_refl)]. }
      split; [reflexivity|]. split; [right; right; reflexivity|].
      split. { eapply agrees_rw_cells; [exact AG7| exact HU|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OU)| exact Ha]. }
      split; [| reflexivity]. eapply agrees_rw_cells; [exact AG7| exact HPc|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OPK)| exact Ha]. }
    2:{ (* [comment removed for export] *)
      (nd_pre (HH0 ltac:(lia)) 3%nat; intros hcs' Hsz HDR0; nd_post). clear HH0 HH1.
      destruct (rw_cells_forget _ _ _ _ HDR0) as [hj HDR]. clear HDR0. rewrite Hsz in HDR.
      cbn [Z.ltb Z.eqb].
      ienterG. zstep. if_false. zstep. if_true. apply evtF_done. subst POSTQ1.
      (* [comment removed for export] *)
      pose proof (rw_cells_merge asegs _ _ [] [_; _; _] _ FRA) as FRA1. cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA1.
      lazymatch type of FRA1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
        pose proof (rw_cells_merge asegs _ _ [c0; c1] rest [] ltac:(rewrite app_nil_r; exact FRA1)) as FRA2 end.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA2. clear FRA1.
      pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HD (rw_cells_uncut _ _ _ _ _ FRM (rw_cells_uncut _ _ _ _ _ HDR FRC2
                    ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia))
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC.
      cbn [app] in FRC.
      lazymatch type of FRC with rw_cells _ _ _ [?h0; ?h1; ?h2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
        pose proof (rw_cells_merge asegs _ _ [h0; h1; h2] [c3; c4; c5; c6; c7] [c8] FRC) as FRCm end.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRCm.
      eapply implMG_mono.
      { eapply (or_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG2 s2' CLc PB1 FB FL lo SPA Fb 0%Z);
          [lia| exact SPA32| lia| lia| lia| lia| lia| exact G4| assumption| exact ST2| exact STG| exact FRA2| exact FR| exact FRCm| exact SHC| exact RSTK]. }
      intros r s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 6%nat; intros MI7 ST7 AG7 AGP7 G7 OF7; nd_post).
      subst POSTQ0 POSTQ. cbv beta iota.
      split; [exact FP2|].
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, PB1, (CB 8 pkj) end.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [congruence|]. split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGd|]; intros a (K & _); exact K|].
               eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
      split; [exact G7|].
      split. { intros _. eapply PCAPR_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| exact (PC5 ltac:(lia))]. }
      split; [intros X; exfalso; lia|].
      split; [reflexivity|]. split; [right; left; reflexivity|].
      split. { eapply agrees_rw_cells; [exact AG7| exact HU|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OU)| exact Ha]. }
      split; [| reflexivity]. eapply agrees_rw_cells; [exact AG7| exact HPc|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OPK)| exact Ha]. }
    (* [comment removed for export] *)
    specialize (PC5 ltac:(lia)). clear PCC5.
    (pose proof PC5 as ndP__; nd_pre ndP__ 3%nat; intros Af1 HinF1 (B1 & I1 & jq & pad1 & bs1 & EPB1 & CELLS1 & PRIV1 & BUF1 & PFX1 & IFS1 & WF1); nd_post).
    pose proof (PCAPR_self_in _ _ _ _ _ PC5) as HinP1.
    assert (HinP1' : In (pc_self p', P, psize p') ((CLc ++ PB1) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; exact HinP1).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 HinP1') as PBLK.
    (pose proof PBLK as ndP__; nd_pre ndP__ 6%nat; intros (PBAND1 & _ & PTOP1 & _) _ PUNP1 PRNG1 PRSH1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in PBAND1, PTOP1, PUNP1, PRNG1, PRSH1.
    pose proof (psize_pos p') as PS1. band_ind PBAND1 bQ.
    (nd_pre (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G4 HinP1' (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kB kBr kB1 kB2; nd_post).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kB1, kB2.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G4 (clocA_incl _ _ _ _ _ _ (proj1 OU) (incl_refl _) (incl_tl _ (incl_refl _))) HinP1 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kUQ kUQr kUQ1 kUQ2; nd_post).
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G4 (clocA_incl _ _ _ _ _ _ (proj1 OPK) (incl_refl _) (incl_tl _ (incl_refl _))) HinP1 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kKQ kKQr kKQ1 kKQ2; nd_post).
    cbn [cb_addr cb_size fst snd] in kUQ1, kUQ2, kKQ1, kKQ2.
    disj_ind D1 kD.
    apply pcap_cells_split4 in CELLS1 as (CA1 & CE1 & CH1 & CO1); [|reflexivity].
    unfold pc_pre, PCAP_PRIV_OFF in CA1.
    (nd_pre (HH1 eq_refl) 3%nat; intros HDR Hcap Hlen; nd_post). clear HH0 HH1.
    apply hdr_cells_to_3 in HDR. apply hdr_cells_to_3 in CH1. unfold hdr3 in HDR, CH1.
    hide BUF1. hide PRIV1. hide IFS1. hide CE1. hide CO1.
    unfold PCAP_HDR_OFF in HU.
    cbn [Z.ltb Z.eqb].
    ienterG.
    zstep. if_false. zstep. if_false.
    zstep.
    ck0_at PUNP1 (P + 208)%Z; ck_go.
    do 2 zstep. if_true.
    do 4 zstep.
    zstep.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 (pk_oneshot PK))) with (Z_to_bv 64 (pk_oneshot PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G4) as (RT4 & _).
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OU G4 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) (keeps_frame_sh _ _ _ _ _ AGd) ltac:(lia)) as OU6.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OPK G4 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) (keeps_frame_sh _ _ _ _ _ AGd) ltac:(lia)) as OPK6.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G4) as [FAll6 _]. pose proof (Forall_inv FAll6) as FRM6. clear FAll6.
    pose proof (unp_of_sh_bytes _ _ _ 8%nat 3%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPH6.
    change (8 * Z.of_nat 8)%Z with 64%Z in UNPH6. change (8 * Z.of_nat 3)%Z with 24%Z in UNPH6.
    assert (OSRC : aobjA RNG2 m6 (Fb + 64) 24)
      by (eapply frameA_aobj; [exact FRM6| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPH6]).
    assert (OHD : aobjA RNG2 m6 (P + 520) 24)
      by (eapply blockA_aobj; [exact PBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia]).
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    pose proof (munch_refl [(bv_unsigned spa - 8224, bv_unsigned spa); (P + 520, P + 544); (PKT, PKT + 8)]%Z m6) as MU2. pose proof (wmono_refl asegs m6) as WM2.
    unfold oneshot_stmt, ONESHOT_STACK in ONESHOT. change (32 + 8192)%Z with 8224%Z in ONESHOT.
    call (ONESHOT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo U (P + 520)%Z PKT (Fb + 64)%Z pd _ _ _ _ _ _ (CB 8 pkj));
      [ reflexivity | reflexivity | exact HU | exact HDR | exact CH1 | exact HPc | reflexivity
      | lia | lia | lia | lia | lia
      | assumption | rewrite Hspa; exact ST2 | lia | lia
      | exact RT4 | exact (proj2 OU6) | exact OSRC | exact OHD | exact (proj2 OPK6)
      | lia | lia | lia | lia | exact AU | exact AK | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | .. ].
    all: try solve [eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH | exact RTLS].
    rewrite Hspa in *. clear Hspa. subst spa.
    do 3 zstep. if_true.
    (* [comment removed for export] *)
    assert (FW8 : Forall (own_ivA [(FF_OFFLINE_READ, Fb, 128%Z)] PB1 SPA) [(SPA - 8224, SPA); (P + 520, P + 544)]%Z)
      by (rewrite EPB1; unfold pcap_blocks; own_ivs).
    assert (FX8 : Forall (cobj_iv FL CLc) [(PKT, PKT + 8)]%Z) by cobj_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW8 FX8 G4 MU2 WM2 ltac:(lia)) as [G8 AG8];
      assert (AG2 : agrees_on (fun a => outside [(SPA - 8224, SPA); (P + 520, P + 544); (PKT, PKT + 8)]%Z a) m6 mm)
        by (eapply agrees_on_of_munch; [exact MU2 | exact WM2 | intros a _ Ho; exact Ho])
    end.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G4 EPB1) as [APB1 API1].
    (pose proof WF1 as ndP__; nd_pre ndP__ 4%nat; intros _ _ W3' _; nd_post).
    assert (HinB1 : In (pc_buffer p', B1, pc_bufalloc p') PB1) by (rewrite EPB1; right; left; reflexivity).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB1)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & BTOP1 & _) B01 _; nd_post).
    cbn [cb_addr cb_size fst snd] in BTOP1, B01.
    unhide CE1; unhide CO1; unhide BUF1; unhide PRIV1; unhide IFS1.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (pcap_aux_agree p' P B1 I1 pad1 bs1 m6 mm _ AG2) as (BUF' & PRIV' & IFS'); [ | | | lia | exact BUF1 | exact PRIV1 | exact IFS1 |]
    end.
    { intros a Ha. cbn [outside].
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G4 (clocA_incl _ _ _ _ _ _ (proj1 OPK) (incl_refl _) (incl_tl _ (incl_refl _))) HinB1 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kq kqr kq1 kq2; nd_post).
      cbn [cb_addr cb_size fst snd] in kq1, kq2. lia. }
    { intros a Ha. cbn [outside]. unfold PCAP_PRIV_OFF in Ha. lia. }
    { intros sg q Hq a Ha. cbn [outside]. destruct (API1 sg q Hq) as [X1 X2].
      assert (HinI1 : In (q, I1, (40 * ng_ifaces_size sg)%Z) PB1) by (rewrite EPB1; unfold pcap_blocks; rewrite Hq; right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 ltac:(apply in_or_app; left; apply in_or_app; right; exact HinI1)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & ITOP1 & _) I01 _; nd_post).
      cbn [cb_addr cb_size fst snd] in ITOP1, I01.
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G4 (clocA_incl _ _ _ _ _ _ (proj1 OPK) (incl_refl _) (incl_tl _ (incl_refl _))) HinI1 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kq kqr kq1 kq2; nd_post).
      cbn [cb_addr cb_size fst snd] in kq1, kq2. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CE' : rw_cells asegs mm (P + 216) [CB 304 (pj_g jq)])
        by (eapply agrees_rw_cells; [exact AG2 | exact CE1 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
      assert (CO' : rw_cells asegs mm (P + 544) (pc_ops p' (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jq))
        by (eapply agrees_rw_cells; [exact AG2 | exact CO1 | intros a Ha; cbn [outside cells_size csize Nat.add pc_ops] in *; lia]);
      lazymatch goal with HPC : rw_cells _ mm (P + 520)%Z _ |- _ =>
        pose proof (pcap_cells_join4 mm P p' B1 (C8 (Z_to_bv 64 Af1)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jq _ h
                      eq_refl CA1 CE' eq_refl (hdr_cells_of_3 _ _ h HPC) CO') as J end
    end.
    assert (PC8 : PCAPR P (set_header h p') PB1 FB _)
      by (eapply PCAPR_intro_set_header; [exact HinF1 | exact EPB1 | exact J | exact PRIV' | exact BUF' | exact PFX1 | exact IFS' | exact WF1 | exact Hcap | exact Hlen]).
    (* [comment removed for export] *)
    lazymatch goal with HSRC : rw_cells _ _ (Fb + 64)%Z [C8 _; C8 _; C8 _] |- _ =>
      pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HD (rw_cells_uncut _ _ _ _ _ FRM (rw_cells_uncut _ _ _ _ _ HSRC FRC2
                    ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia))
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC end.
    cbn [app] in FRC.
    lazymatch type of FRC with rw_cells _ _ _ [?h0; ?h1; ?h2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10] =>
      pose proof (rw_cells_merge asegs _ _ [h0; h1; h2] [c3; c4; c5; c6; c7; c8; c9] [c10] FRC) as FRCm end.
    cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRCm.
    pose proof (rw_cells_merge asegs _ _ [] [_; _; _] _ FRA) as FRA1. cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA1.
    lazymatch type of FRA1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
      pose proof (rw_cells_merge asegs _ _ [c0; c1] rest [] ltac:(rewrite app_nil_r; exact FRA1)) as FRA2 end.
    cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA2. clear FRA1.
    apply evtF_done. subst POSTQ1.
    eapply implMG_mono.
    { eapply (or_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG2 s2' CLc PB1 FB FL lo SPA Fb 1%Z);
        [lia| exact SPA32| lia| lia| lia| lia| lia| exact G8| assumption| eassumption| exact STG| exact FRA2| exact FR| exact FRCm| exact SHC| exact RSTK]. }
    intros r s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 6%nat; intros MI7 ST7 AG7 AGP7 G7 OF7; nd_post).
    subst POSTQ0 POSTQ. cbv beta iota.
    split; [exact FP2|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
      lazymatch goal with HPK : rw_cells _ _ PKT [?c] |- _ => exists (Z_to_bv 64 1), mm, PB1, c end end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [assumption|]. split; [assumption|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGd|]; intros a (K & _); exact K|].
             eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG8|]; intros a (K & NK); split;
                                        [destruct K as [K|K]; [left; lia| right; exact K] | cbn [outside]; split; [exact NK| exact I]]|].
             eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
    split; [exact G7|].
    split. { intros _. eapply PCAPR_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| exact PC8]. }
    split; [intros X; exfalso; lia|].
    split; [reflexivity|]. split; [left; reflexivity|].
    split. { unfold PCAP_HDR_OFF. lazymatch goal with HUU : rw_cells _ _ U _ |- _ => eapply agrees_rw_cells; [exact AG7| exact HUU|] end.
             intros a Ha. eapply clocA_keeps; [exact (proj1 OU)| exact Ha]. }
    split; [| reflexivity].
    lazymatch goal with HPK : rw_cells _ _ PKT _ |- _ => eapply agrees_rw_cells; [exact AG7| exact HPK|] end.
    intros a Ha. eapply clocA_keeps; [exact (proj1 OPK)| exact Ha].
  Qed.
  End Sz4.
  Theorem offline_read_proofA : ltac:(let t := eval cbv delta [offline_read_proofA__stmt] in offline_read_proofA__stmt in exact t).
  Proof using FENTER1 FRET GL NP_NG NP_PCAP ONESHOT. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P U PKT p fuel pd pkc. ltac2:(SecDiet.SzSec.closeP 'offline_read_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End OfflineRead.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
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
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32A : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

(* [comment removed for export] *)
Local Ltac nlb_hyp A :=
  repeat match goal with
  | H : rw_cells _ _ A ?cs |- _ =>
      match cs with context [C1 (Z_to_bv 8 ?z)] =>
        is_Zlit z; let z' := eval vm_compute in (Z.modulo z 256) in
        tryif constr_eq z z' then fail else
        replace (Z_to_bv 8 z) with (Z_to_bv 8 z') in H by (apply (proj2 (bv_eq _ _ _)); reflexivity)
      end
  end.
Local Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store; try nlb_hyp A
      | _ => idtac
      end
  | _ => idtac
  end.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section OfflineRead.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER1 : fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis NP_PCAP : pcap_next_packet_stmt HO FO sites GIOA TP.
  Hypothesis NP_NG : pcap_ng_next_packet_stmt HO FO sites GIOA TP.
  Hypothesis ONESHOT : oneshot_stmt.

  Lemma next_packet_op_any : forall ng, next_packet_op_stmt_for HO FO sites GIOA TP ng.
  Proof using NP_NG NP_PCAP. intros [|]; [exact NP_NG | exact NP_PCAP]. Qed.

  (* [comment removed for export] *)
  Lemma or_epi : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb st : Z) (m : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 r25 r26 r27 t3 t4 t5 t6 : word)
      (jS1 jS2 fj : list byte) (k0 k1 k2 : word) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z -> (-2147483648 <= st < 2147483648)%Z ->
    GIOA L RNG s (CLc ++ PB) FB ((FF_OFFLINE_READ, Fb, 128%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 88) (bv_unsigned sp + -104) ->
    rw_cells asegs m SPA [CB 24 jS1; C8 (Z_to_bv 64 Fb); CB 56 jS2] ->
    rw_cells asegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 96 fj; C8 (Z_to_bv 64 (fflagA L FF_OFFLINE_READ Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_OFFLINE_READ x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 st) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m' /\ agrees_on (fun a => in_block (CLc ++ PB) a) m m'
           /\ GIOA L RNG s' (CLc ++ PB) FB FL m' /\ ps_outfile s' = ps_outfile s)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 r20 r21 r22 r23 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) r25 r26 r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8564c) fc None m (seg_rom asegs)).      (* [comment removed for export] *)
  Proof using FRET GL.
    intros until x. intros SPAB SPA32 LO LOS SPT TOP47 SX G MI ST STG FRA FR FRC SHC RSTK.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).   (* [comment removed for export] *)
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (SWR : forall z, (-2147483648 <= z < 2147483648)%Z -> bv_swrap 32 (z mod 18446744073709551616 + 0) = z).
    { intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z. Z.div_mod_to_equations. lia. }
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND FTOP F64 _ FRNG FSRNG _ _; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 128 3) with 16%Z in FSRNG.
    (pose proof (ablk_lin _ _ FBAND) as ndP__; nd_pre ndP__ 4%nat; intros _ Fb0 _ _; nd_post). band_ind FBAND bF.
    (nd_pre (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) 6%nat; intros _ FLR FLB FLT _ (kF & kFr & kF1 & kF2); nd_post). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    assert (FW : Forall (own_ivA [(FF_OFFLINE_READ, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    zstep. neg_lits.
    do 4 zstep.
    do 3 zstep.
    zstep. zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    burst_begin [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z [Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 4 zstep. zstep_sh0. do 11 zstep.
    burst_end MUb WMb.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block (CLc ++ PB) a) m mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha;
            exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PB) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a Ha));
      pose proof (munch_refl [(fflagA L FF_OFFLINE_READ Fb, fflagA L FF_OFFLINE_READ Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 17 zstep.
    rewrite (SWR st) by lia.
    release_frame FRA ST (SPA + 88)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CLc (bv_unsigned sp) G5 MU2 WM2 (incl_appl _ (incl_refl _)) ltac:(lia)) as [AG6 AGP6].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split. { eapply agrees_on_trans; [exact AGP5| exact AGP6]. }
    split; [exact G6| exact OF3].
  Qed.

  Theorem offline_read_proofA : offline_read_stmt HO FO sites GIOA TP.
  Proof using FENTER1 FRET GL NP_NG NP_PCAP ONESHOT.
    red. intros until pkc. intros PRE UC TR NF PC -> -> -> -> HU HPK Hpk OU OPK D1 AU AK.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| unfold PCAP_L3_STACK in BU; lia]).   (* [comment removed for export] *)
    pose proof (PCAPR_self_in _ _ _ _ _ PC) as HinP.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 3%nat; intros (PBAND & P3 & PTOP & P2) P1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    pose proof (psize_pos p) as PS. unfold PCAP_L3_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (UL : clocA FL (CLc ++ PB) U 24) by (eapply clocA_incl; [exact (proj1 OU)| apply incl_appl; apply incl_refl| apply incl_refl]).
    assert (PKL : clocA FL (CLc ++ PB) PKT 8) by (eapply clocA_incl; [exact (proj1 OPK)| apply incl_appl; apply incl_refl| apply incl_refl]).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G UL) as (ULO & UHI). pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G PKL) as (PKLO & PKHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G UL ltac:(lia)) as UBAND. pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G PKL ltac:(lia)) as PKBAND.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (proj1 OU) HinP ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kUP kUPr kUP1 kUP2; nd_post).
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (proj1 OPK) HinP ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kKP kKPr kKP1 kKP2; nd_post).
    cbn [cb_addr cb_size fst snd] in kUP1, kUP2, kKP1, kKP2.
    pose proof UBAND as UBAND'. pose proof PKBAND as PKBAND'. band_ind UBAND bU. band_ind PKBAND bK.
    band_ind PBAND bP.
    destruct (rw_cells_forget _ _ _ _ HPK) as [pkj HPc]. clear HPK. cbn [cells_size] in HPc. rewrite Hpk in HPc. change (8 + 0)%nat with 8%nat in HPc.
    unfold pcapint_offline_read_1. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]. unfold PCAP_OFFLINE_READ_ENTRY.
    remember (bv_unsigned sp - 192 - (bv_unsigned sp - 192) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -192) - (bv_unsigned sp + -192) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| unfold PCAP_L3_STACK in BU; lia]).   (* [comment removed for export] *)
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 88%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    rewrite land_m32A by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -104)%Z.
    destruct (stk_split asegs _ lo (SPA + 88) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 88) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 88) with 88%Z in STL, FRA. replace (SPA + 88 - 88)%Z with SPA in STL, FRA by lia.
    zstep.
    do 3 zstep.
    do 4 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 2 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW0 : Forall (pcap_iv FL PB) [(bv_unsigned sp - 208, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ PB) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW0]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FW0.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER1 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { apply NF. left. reflexivity. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_OFFLINE_READ) with 128%Z in *.
    change (Z.to_nat (128 - 32)) with 96%nat in *. change (Z.to_nat (128 / 8)) with 16%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 546124)) with (Z_to_bv 64 546124) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND' FTOP' F64 _ FRNG FSRNG _ FSWR; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HU; [|intros a Ha; eapply clocA_keeps; [exact UL| exact Ha]].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HPc; [|intros a Ha; eapply clocA_keeps; [exact PKL| exact Ha]].
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 UL ltac:(lia)) 4%nat; intros kU kUr kU1 kU2; nd_post).
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 PKL ltac:(lia)) 4%nat; intros kK kKr kK1 kK2; nd_post).
    cbn [fb_addr fb_size fst snd] in kU1, kU2, kK1, kK2.
    assert (AGb : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; apply in_block_app; left; exact Ha| apply incl_refl]. }
    assert (PC2 : PCAPR P p PB FB m2).
    { eapply PCAPR_agree; [exact AG1| intros a Ha; right; left; apply in_block_app; right; exact Ha|].
      eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU0| exact WM0| intros a _ Ho; exact Ho]| | exact PC].
      intros a Ha. pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)).
      cbn [outside]. lia. }
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    do 2 zstep. if_true_by (nez_true Fb ltac:(lia)).
    burst_begin [(SPA, SPA + 88); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z [SPA; Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    (* [comment removed for export] *)
    zstep.
    do 4 zstep.
    do 3 zstep.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    do 4 zstep.
    zstep. neg_lits.
    zstep_sh0. do 3 zstep.
    zstep. neg_lits.
    do 5 zstep.
    burst_end MUb WMb.
    zstep.
    zstep. if_true.
    do 4 zstep.
    (* [comment removed for export] *)
    ub_null.
    zstep. ub_al 7%Z ltac:(al16 P2). zstep. if_false.
    zstep.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_OFFLINE_READ, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G1 MU WM ltac:(lia)) as [G2 AG2];
      assert (PC3 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM| intros a _ Ho; exact Ho]| exact (pb_outside _ _ _ GL _ _ _ _ _ _ _ _ _ _ [] _ FW (Forall_nil _) G1) | exact PC2])
    end.
    (pose proof PC3 as ndP__; nd_pre ndP__ 3%nat; intros Af HinF (B & Ib & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
    (pose proof WF as ndP__; nd_pre ndP__ 13%nat; intros W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 W11 W12 W13; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 6%nat; intros _ _ PUNP PRNG PRSH _; nd_post).
    cbn [cb_addr cb_size fst snd] in PUNP, PRNG, PRSH.
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    hide BUF. hide PRIV. hide IFS. hide CE. hide CH. hide CO.
    unfold pc_pre, PCAP_PRIV_OFF in CA. rewrite W5 in CA.
    rewrite W5. cbn [Z.eqb negb].
    (* [comment removed for export] *)
    ck0 PUNP; ck_go.
    zstep.
    zstep. if_true.
    (* [comment removed for export] *)
    do 7 zstep.
    do 8 zstep.
    ck0_at PUNP (P + 8)%Z; ck_go.
    do 4 zstep.
    zstep.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 (np_entry p))) with (Z_to_bv 64 (np_entry p))
      by (unfold np_entry, PK; cbn [pk_next_ng pk_next_pcap]; destruct (is_ng p); (symmetry; apply ret_pc_even; [lia|reflexivity])).
    clear G2 AG2 PC3.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB _) FW) (Forall_nil _) G1 MU WM ltac:(lia)) as [G3 AG3];
      assert (PC4 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM| intros a _ Ho; exact Ho]| exact (pb_outside _ _ _ GL _ _ _ _ _ _ _ _ _ _ [] _ FW (Forall_nil _) G1) | exact PC2]);
      assert (AGc : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply agrees_on_trans; [exact AGb|]; eapply agrees_on_weaken; [exact AG3|]; intros a Ha; split; [exact Ha| exact I]);
      assert (UC3 : ucallerA depth_offline_read L mm sp s0 ra trC)
        by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha;
            destruct (AGb a ltac:(lia) ltac:(left; lia)) as [E1 _]; destruct (AG3 a ltac:(lia) ltac:(split; [left; lia| exact I])) as [E2 _]; congruence)
    end.
    pose proof (keeps_frame_sh _ _ _ _ _ AGc) as AGsh.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OU G3 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as OU3.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OPK G3 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as OPK3.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 12%nat _ FR eq_refl) as BRA.
    cbn [firstn cells_size csize Nat.add] in BS0, BRA.
    replace (bv_unsigned sp + -104 + Z.of_nat 88)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
    replace (bv_unsigned sp + -104 + Z.of_nat 96)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
    pose proof (unp_of_sh_bytes _ _ _ 4%nat 1%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPD.
    pose proof (unp_of_sh_bytes _ _ _ 8%nat 3%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPH.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPD. change (8 * Z.of_nat 1)%Z with 8%Z in UNPD.
    change (8 * Z.of_nat 8)%Z with 64%Z in UNPH. change (8 * Z.of_nat 3)%Z with 24%Z in UNPH.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs _ _ [_; _; _] 96 _ [_] [8; 8; 24; 24; 32]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [FRC1 FRC']. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FRC1, FRC'.
    destruct (rw_cells_cut _ _ _ 1 FRC') as [FRD FRC'']. clear FRC'. cbn [firstn skipn cells_size csize Nat.add] in FRD, FRC''.
    destruct (rw_cells_cut _ _ _ 1 FRC'') as [FRM FRC']. clear FRC''. cbn [firstn skipn cells_size csize Nat.add] in FRM, FRC'.
    destruct (rw_cells_cut _ _ _ 1 FRC') as [FRH FRC2]. clear FRC'. cbn [firstn skipn cells_size csize Nat.add] in FRH, FRC2.
    replace (Fb + Z.of_nat 32)%Z with (Fb + 32)%Z in * by lia. replace (Fb + 32 + Z.of_nat 8)%Z with (Fb + 40)%Z in * by lia.
    replace (Fb + 40 + Z.of_nat 24)%Z with (Fb + 64)%Z in * by lia. replace (Fb + 64 + Z.of_nat 24)%Z with (Fb + 88)%Z in * by lia.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    assert (FRIN : forall a, (Fb <= a < Fb + 128)%Z -> in_frames ((FF_OFFLINE_READ, Fb, 128%Z) :: FL) a)
      by (intros a Ha; apply in_frames_In; exists (FF_OFFLINE_READ, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    apply evtF_done. eapply implMG_bind.
    { eapply (next_packet_op_any (is_ng p) _ spa);
        [ split; [exact G3|]; rewrite Hspa; split; [eassumption|]; split; [lia|]; split; [unfold PCAP_L2_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x8571c%Z UC3); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
              | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_next_packet_op, depth_offline_read, depth_pcap_ng_next_packet, depth_pcap_next_packet; destruct (is_ng p); lia]
        | rewrite unsigned_lit by lia; unfold traces_next_packet_op; (nd_pre TR 3%nat; intros T1 T2 _; nd_post); destruct (is_ng p); assumption
        | unfold frames_next_packet_op; apply nofr_cons; [eapply nofr_sub; [exact NF| destruct (is_ng p); intros f Hf; cbn in Hf |- *; clear - Hf; intuition]
                                                         | destruct (is_ng p); cbn; clear; intuition congruence]
        | exact PC4 | reflexivity | rewrite Hspa; lia | reflexivity | reflexivity | reflexivity
        | exact FRH | reflexivity | exact FRD | reflexivity
        | split; [right; exists (FF_OFFLINE_READ, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPH]
        | split; [right; exists (FF_OFFLINE_READ, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPD]
        | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]. }
    intros [[st h] p'] s2' RNG2 ms' PO. unfold next_packet_post in PO. destruct PO as (FP2 & PO). destruct_exs PO.
    (nd_pre PO 9%nat; intros E OF2 MI2 ST2 AG4 G4 PC5 PCC5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros Hst HH1 HH0 HD1 Hdw; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 546588)) with (Z_to_bv 64 546588) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [app] in G4, AG4.
    rename x0 into m6. rename x1 into PB1. rename x2 into dw.
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FR; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRA; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]].
    apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRC1; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; apply FRIN; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRM; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; apply FRIN; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRC2; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; apply FRIN; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in SHC;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; right; apply in_frame_sh_In; exists (FF_OFFLINE_READ, Fb, 128%Z);
          split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in HU;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [eapply clocA_keeps; [eapply clocA_incl; [exact (proj1 OU)| apply incl_refl| apply incl_tl; apply incl_refl]| lia]| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in HPc;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [eapply clocA_keeps; [eapply clocA_incl; [exact (proj1 OPK)| apply incl_refl| apply incl_tl; apply incl_refl]| lia]| lia]].
    destruct (rw_cells_forget _ _ _ _ HD1) as [dwj HD]. clear HD1. cbn [cells_size] in HD. rewrite Hdw in HD. change (8 + 0)%nat with 8%nat in HD. clear dw Hdw.
    (* [comment removed for export] *)
    assert (AGd : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m6).
    { eapply agrees_on_trans; [exact AGc|]. eapply agrees_on_weaken; [exact AG4|]. intros a K.
      destruct (keeps_not_own_frame _ _ _ GL _ _ _ _ _ _ _ (FF_OFFLINE_READ, Fb, 128%Z) CLc (bv_unsigned sp) a G3 (incl_appl _ (incl_refl _)) ltac:(lia) K) as [NF1 _].
      cbn [fb_addr fb_size fst snd] in NF1.
      split; [| lia]. destruct K as [K|[K|[K|K]]]; [left; lia| right; left; exact K| right; right; left; apply in_frames_cons; exact K
                                                  | right; right; right; apply in_frame_sh_cons; exact K]. }
    clear MU WM FW.
    destruct Hst as [-> | [-> | ->]].
    3:{ (* [comment removed for export] *)
      (nd_pre (HH0 ltac:(lia)) 3%nat; intros hcs' Hsz HDR0; nd_post). clear HH0 HH1.
      destruct (rw_cells_forget _ _ _ _ HDR0) as [hj HDR]. clear HDR0. rewrite Hsz in HDR.
      cbn [Z.ltb Z.eqb].
      ienterG. zstep. if_true. apply evtF_done. subst POSTQ1.      (* [comment removed for export] *)
      (* [comment removed for export] *)
      pose proof (rw_cells_merge asegs _ _ [] [_; _; _] _ FRA) as FRA1. cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA1.
      lazymatch type of FRA1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
        pose proof (rw_cells_merge asegs _ _ [c0; c1] rest [] ltac:(rewrite app_nil_r; exact FRA1)) as FRA2 end.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA2. clear FRA1.
      (* [comment removed for export] *)
      pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HD (rw_cells_uncut _ _ _ _ _ FRM (rw_cells_uncut _ _ _ _ _ HDR FRC2
                    ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia))
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC.
      cbn [app] in FRC.
      lazymatch type of FRC with rw_cells _ _ _ [?h0; ?h1; ?h2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
        pose proof (rw_cells_merge asegs _ _ [h0; h1; h2] [c3; c4; c5; c6; c7] [c8] FRC) as FRCm end.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRCm.
      eapply implMG_mono.
      { eapply (or_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG2 s2' CLc PB1 FB FL lo SPA Fb (-1)%Z);
          [lia| exact SPA32| lia| lia| lia| lia| lia| exact G4| assumption| exact ST2| exact STG| exact FRA2| exact FR| exact FRCm| exact SHC| exact RSTK]. }
      intros r s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 6%nat; intros MI7 ST7 AG7 AGP7 G7 OF7; nd_post).
      subst POSTQ0 POSTQ. cbv beta iota.
      split; [exact FP2|].
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 (-1)), mm, PB1, (CB 8 pkj) end.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [congruence|]. split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGd|]; intros a (K & _); exact K|].
               eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
      split; [exact G7|].
      split; [intros X; exfalso; lia|].
      split. { intros _. eapply PCAPR_closable_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| exact (PCC5 eq_refl)]. }
      split; [reflexivity|]. split; [right; right; reflexivity|].
      split. { eapply agrees_rw_cells; [exact AG7| exact HU|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OU)| exact Ha]. }
      split; [| reflexivity]. eapply agrees_rw_cells; [exact AG7| exact HPc|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OPK)| exact Ha]. }
    2:{ (* [comment removed for export] *)
      (nd_pre (HH0 ltac:(lia)) 3%nat; intros hcs' Hsz HDR0; nd_post). clear HH0 HH1.
      destruct (rw_cells_forget _ _ _ _ HDR0) as [hj HDR]. clear HDR0. rewrite Hsz in HDR.
      cbn [Z.ltb Z.eqb].
      ienterG. zstep. if_false. zstep. if_true. do 2 zstep. apply evtF_done. subst POSTQ1.      (* [comment removed for export] *)
      (* [comment removed for export] *)
      pose proof (rw_cells_merge asegs _ _ [] [_; _; _] _ FRA) as FRA1. cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA1.
      lazymatch type of FRA1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
        pose proof (rw_cells_merge asegs _ _ [c0; c1] rest [] ltac:(rewrite app_nil_r; exact FRA1)) as FRA2 end.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA2. clear FRA1.
      pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HD (rw_cells_uncut _ _ _ _ _ FRM (rw_cells_uncut _ _ _ _ _ HDR FRC2
                    ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia))
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC.
      cbn [app] in FRC.
      lazymatch type of FRC with rw_cells _ _ _ [?h0; ?h1; ?h2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
        pose proof (rw_cells_merge asegs _ _ [h0; h1; h2] [c3; c4; c5; c6; c7] [c8] FRC) as FRCm end.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRCm.
      eapply implMG_mono.
      { eapply (or_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG2 s2' CLc PB1 FB FL lo SPA Fb 0%Z);
          [lia| exact SPA32| lia| lia| lia| lia| lia| exact G4| assumption| exact ST2| exact STG| exact FRA2| exact FR| exact FRCm| exact SHC| exact RSTK]. }
      intros r s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 6%nat; intros MI7 ST7 AG7 AGP7 G7 OF7; nd_post).
      subst POSTQ0 POSTQ. cbv beta iota.
      split; [exact FP2|].
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, PB1, (CB 8 pkj) end.
      split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
      split; [congruence|]. split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGd|]; intros a (K & _); exact K|].
               eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
      split; [exact G7|].
      split. { intros _. eapply PCAPR_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| exact (PC5 ltac:(lia))]. }
      split; [intros X; exfalso; lia|].
      split; [reflexivity|]. split; [right; left; reflexivity|].
      split. { eapply agrees_rw_cells; [exact AG7| exact HU|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OU)| exact Ha]. }
      split; [| reflexivity]. eapply agrees_rw_cells; [exact AG7| exact HPc|]. intros a Ha. eapply clocA_keeps; [exact (proj1 OPK)| exact Ha]. }
    (* [comment removed for export] *)
    specialize (PC5 ltac:(lia)). clear PCC5.
    (pose proof PC5 as ndP__; nd_pre ndP__ 3%nat; intros Af1 HinF1 (B1 & I1 & jq & pad1 & bs1 & EPB1 & CELLS1 & PRIV1 & BUF1 & PFX1 & IFS1 & WF1); nd_post).
    pose proof (PCAPR_self_in _ _ _ _ _ PC5) as HinP1.
    assert (HinP1' : In (pc_self p', P, psize p') ((CLc ++ PB1) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; exact HinP1).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 HinP1') as PBLK.
    (pose proof PBLK as ndP__; nd_pre ndP__ 6%nat; intros (PBAND1 & _ & PTOP1 & _) _ PUNP1 PRNG1 PRSH1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in PBAND1, PTOP1, PUNP1, PRNG1, PRSH1.
    pose proof (psize_pos p') as PS1. band_ind PBAND1 bQ.
    (nd_pre (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ G4 HinP1' (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kB kBr kB1 kB2; nd_post).
    cbn [cb_addr cb_size fb_addr fb_size fst snd] in kB1, kB2.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G4 (clocA_incl _ _ _ _ _ _ (proj1 OU) (incl_refl _) (incl_tl _ (incl_refl _))) HinP1 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kUQ kUQr kUQ1 kUQ2; nd_post).
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G4 (clocA_incl _ _ _ _ _ _ (proj1 OPK) (incl_refl _) (incl_tl _ (incl_refl _))) HinP1 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kKQ kKQr kKQ1 kKQ2; nd_post).
    cbn [cb_addr cb_size fst snd] in kUQ1, kUQ2, kKQ1, kKQ2.
    disj_ind D1 kD.
    apply pcap_cells_split4 in CELLS1 as (CA1 & CE1 & CH1 & CO1); [|reflexivity].
    unfold pc_pre, PCAP_PRIV_OFF in CA1.
    (nd_pre (HH1 eq_refl) 3%nat; intros HDR Hcap Hlen; nd_post). clear HH0 HH1.
    apply hdr_cells_to_3 in HDR. apply hdr_cells_to_3 in CH1. unfold hdr3 in HDR, CH1.
    hide BUF1. hide PRIV1. hide IFS1. hide CE1. hide CO1.
    unfold PCAP_HDR_OFF in HU.
    cbn [Z.ltb Z.eqb].
    ienterG.
    zstep. if_false. zstep. if_false.
    zstep.
    ck0_at PUNP1 (P + 208)%Z; ck_go.
    do 2 zstep. if_true.
    do 4 zstep.
    zstep.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 (pk_oneshot PK))) with (Z_to_bv 64 (pk_oneshot PK)) by (symmetry; apply ret_pc_even; [cbn; lia|reflexivity]).
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G4) as (RT4 & _).
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OU G4 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) (keeps_frame_sh _ _ _ _ _ AGd) ltac:(lia)) as OU6.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OPK G4 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) (keeps_frame_sh _ _ _ _ _ AGd) ltac:(lia)) as OPK6.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G4) as [FAll6 _]. pose proof (Forall_inv FAll6) as FRM6. clear FAll6.
    pose proof (unp_of_sh_bytes _ _ _ 8%nat 3%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPH6.
    change (8 * Z.of_nat 8)%Z with 64%Z in UNPH6. change (8 * Z.of_nat 3)%Z with 24%Z in UNPH6.
    assert (OSRC : aobjA RNG2 m6 (Fb + 64) 24)
      by (eapply frameA_aobj; [exact FRM6| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPH6]).
    assert (OHD : aobjA RNG2 m6 (P + 520) 24)
      by (eapply blockA_aobj; [exact PBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia]).
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    pose proof (munch_refl [(bv_unsigned spa - 8224, bv_unsigned spa); (P + 520, P + 544); (PKT, PKT + 8)]%Z m6) as MU2. pose proof (wmono_refl asegs m6) as WM2.
    unfold oneshot_stmt, ONESHOT_STACK in ONESHOT. change (32 + 8192)%Z with 8224%Z in ONESHOT.
    call (ONESHOT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo U (P + 520)%Z PKT (Fb + 64)%Z pd _ _ _ _ _ _ (CB 8 pkj));
      [ reflexivity | reflexivity | exact HU | exact HDR | exact CH1 | exact HPc | reflexivity
      | lia | lia | lia | lia | lia
      | assumption | rewrite Hspa; exact ST2 | lia | lia
      | exact RT4 | exact (proj2 OU6) | exact OSRC | exact OHD | exact (proj2 OPK6)
      | lia | lia | lia | lia | exact AU | exact AK | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | .. ].
    all: try solve [eapply rng_sub'; [exact RSTK| lia] | exact RIMG | exact RISH | exact RTLS].
    rewrite Hspa in *. clear Hspa. subst spa.
    do 2 zstep. if_false.                 (* [comment removed for export] *)
    do 3 zstep. if_true.
    (* [comment removed for export] *)
    assert (FW8 : Forall (own_ivA [(FF_OFFLINE_READ, Fb, 128%Z)] PB1 SPA) [(SPA - 8224, SPA); (P + 520, P + 544)]%Z)
      by (rewrite EPB1; unfold pcap_blocks; own_ivs).
    assert (FX8 : Forall (cobj_iv FL CLc) [(PKT, PKT + 8)]%Z) by cobj_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW8 FX8 G4 MU2 WM2 ltac:(lia)) as [G8 AG8];
      assert (AG2 : agrees_on (fun a => outside [(SPA - 8224, SPA); (P + 520, P + 544); (PKT, PKT + 8)]%Z a) m6 mm)
        by (eapply agrees_on_of_munch; [exact MU2 | exact WM2 | intros a _ Ho; exact Ho])
    end.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G4 EPB1) as [APB1 API1].
    (pose proof WF1 as ndP__; nd_pre ndP__ 4%nat; intros _ _ W3' _; nd_post).
    assert (HinB1 : In (pc_buffer p', B1, pc_bufalloc p') PB1) by (rewrite EPB1; right; left; reflexivity).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 ltac:(apply in_or_app; left; apply in_or_app; right; exact HinB1)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & BTOP1 & _) B01 _; nd_post).
    cbn [cb_addr cb_size fst snd] in BTOP1, B01.
    unhide CE1; unhide CO1; unhide BUF1; unhide PRIV1; unhide IFS1.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (pcap_aux_agree p' P B1 I1 pad1 bs1 m6 mm _ AG2) as (BUF' & PRIV' & IFS'); [ | | | lia | exact BUF1 | exact PRIV1 | exact IFS1 |]
    end.
    { intros a Ha. cbn [outside].
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G4 (clocA_incl _ _ _ _ _ _ (proj1 OPK) (incl_refl _) (incl_tl _ (incl_refl _))) HinB1 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kq kqr kq1 kq2; nd_post).
      cbn [cb_addr cb_size fst snd] in kq1, kq2. lia. }
    { intros a Ha. cbn [outside]. unfold PCAP_PRIV_OFF in Ha. lia. }
    { intros sg q Hq a Ha. cbn [outside]. destruct (API1 sg q Hq) as [X1 X2].
      assert (HinI1 : In (q, I1, (40 * ng_ifaces_size sg)%Z) PB1) by (rewrite EPB1; unfold pcap_blocks; rewrite Hq; right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 ltac:(apply in_or_app; left; apply in_or_app; right; exact HinI1)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & ITOP1 & _) I01 _; nd_post).
      cbn [cb_addr cb_size fst snd] in ITOP1, I01.
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G4 (clocA_incl _ _ _ _ _ _ (proj1 OPK) (incl_refl _) (incl_tl _ (incl_refl _))) HinI1 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kq kqr kq1 kq2; nd_post).
      cbn [cb_addr cb_size fst snd] in kq1, kq2. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CE' : rw_cells asegs mm (P + 216) [CB 304 (pj_g jq)])
        by (eapply agrees_rw_cells; [exact AG2 | exact CE1 | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
      assert (CO' : rw_cells asegs mm (P + 544) (pc_ops p' (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jq))
        by (eapply agrees_rw_cells; [exact AG2 | exact CO1 | intros a Ha; cbn [outside cells_size csize Nat.add pc_ops] in *; lia]);
      lazymatch goal with HPC : rw_cells _ mm (P + 520)%Z _ |- _ =>
        pose proof (pcap_cells_join4 mm P p' B1 (C8 (Z_to_bv 64 Af1)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jq _ h
                      eq_refl CA1 CE' eq_refl (hdr_cells_of_3 _ _ h HPC) CO') as J end
    end.
    assert (PC8 : PCAPR P (set_header h p') PB1 FB _)
      by (eapply PCAPR_intro_set_header; [exact HinF1 | exact EPB1 | exact J | exact PRIV' | exact BUF' | exact PFX1 | exact IFS' | exact WF1 | exact Hcap | exact Hlen]).
    (* [comment removed for export] *)
    lazymatch goal with HSRC : rw_cells _ _ (Fb + 64)%Z [C8 _; C8 _; C8 _] |- _ =>
      pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HD (rw_cells_uncut _ _ _ _ _ FRM (rw_cells_uncut _ _ _ _ _ HSRC FRC2
                    ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia))
                    ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC end.
    cbn [app] in FRC.
    lazymatch type of FRC with rw_cells _ _ _ [?h0; ?h1; ?h2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10] =>
      pose proof (rw_cells_merge asegs _ _ [h0; h1; h2] [c3; c4; c5; c6; c7; c8; c9] [c10] FRC) as FRCm end.
    cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRCm.
    pose proof (rw_cells_merge asegs _ _ [] [_; _; _] _ FRA) as FRA1. cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA1.
    lazymatch type of FRA1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
      pose proof (rw_cells_merge asegs _ _ [c0; c1] rest [] ltac:(rewrite app_nil_r; exact FRA1)) as FRA2 end.
    cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRA2. clear FRA1.
    apply evtF_done. subst POSTQ1.
    eapply implMG_mono.
    { eapply (or_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG2 s2' CLc PB1 FB FL lo SPA Fb 1%Z);
        [lia| exact SPA32| lia| lia| lia| lia| lia| exact G8| assumption| eassumption| exact STG| exact FRA2| exact FR| exact FRCm| exact SHC| exact RSTK]. }
    intros r s3' RNG3 ms3 (-> & -> & PO). destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 6%nat; intros MI7 ST7 AG7 AGP7 G7 OF7; nd_post).
    subst POSTQ0 POSTQ. cbv beta iota.
    split; [exact FP2|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
      lazymatch goal with HPK : rw_cells _ _ PKT [?c] |- _ => exists (Z_to_bv 64 1), mm, PB1, c end end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [assumption|]. split; [assumption|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGd|]; intros a (K & _); exact K|].
             eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG8|]; intros a (K & NK); split;
                                        [destruct K as [K|K]; [left; lia| right; exact K] | cbn [outside]; split; [exact NK| exact I]]|].
             eapply agrees_on_weaken; [exact AG7|]. intros a (K & _); exact K. }
    split; [exact G7|].
    split. { intros _. eapply PCAPR_agree; [exact AGP7| intros a Ha; apply in_block_app; right; exact Ha| exact PC8]. }
    split; [intros X; exfalso; lia|].
    split; [reflexivity|]. split; [left; reflexivity|].
    split. { unfold PCAP_HDR_OFF. lazymatch goal with HUU : rw_cells _ _ U _ |- _ => eapply agrees_rw_cells; [exact AG7| exact HUU|] end.
             intros a Ha. eapply clocA_keeps; [exact (proj1 OU)| exact Ha]. }
    split; [| reflexivity].
    lazymatch goal with HPK : rw_cells _ _ PKT _ |- _ => eapply agrees_rw_cells; [exact AG7| exact HPK|] end.
    intros a Ha. eapply clocA_keeps; [exact (proj1 OPK)| exact Ha].
  Qed.
End OfflineRead.
End CANSEC1.
End TwB.
