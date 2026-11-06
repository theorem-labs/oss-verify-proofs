(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase AMalloc_iface RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strerror__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_vsnprintf_top. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_mkstemp__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_fmtA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA StdioLawsA Stdio_glueA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.Printf_snsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vfprintf_sn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vsnprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_vsnprintf_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_mkstemp__A3S.I_snprintf_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_fmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.Printf_pitems OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueSn.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  (* [comment removed for export] *)
  Lemma items_ok_eqA : forall its args, Pcap_ifaceA.items_ok its args = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok its args.
  Proof using Type. pin_using tt.
    induction its as [|[l|c|b] its IH]; intros args; cbn; [reflexivity| | |reflexivity].
    - rewrite IH. reflexivity.
    - destruct args as [|a args]; [reflexivity|]. rewrite IH. destruct c, a; reflexivity.
  Qed.

  Lemma zb_unsigned : forall (bs : list byte), zb (map bv_unsigned bs) = bs.
  Proof using Type. pin_using tt. induction bs as [|b bs IH]; cbn; [reflexivity|]. unfold zb in *. cbn. rewrite definitions.Z_to_bv_bv_unsigned, IH. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition slocA_below__stmt : Prop := forall L RNG (s : PS) CL FB FL m tls P n k,
    GIOA L RNG s CL FB FL m -> slocA tls FL CL P n k -> 0 <= n -> 0 <= k -> P + n + k <= ATOP.
  Section Sz3.
  Variables L RNG s CL FB FL m tls P n k : ltac2:(SecDiet.SzSec.tyM 'slocA_below__stmt "vvvvvvvvvvv" @L).
  Lemma slocA_below__body : ltac2:(SecDiet.SzSec.bodyP 'slocA_below__stmt "vvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOC Hn Hk.
    pose proof (@ATOP_lo rc) as AL.
    destruct LOC as [CR | [(g & HG & G1 & G2 & G3 & G4) | (_ & T1 & T2)]].
    - destruct (clocA_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G CR ltac:(lia)) as (_ & X & _). lia.
    - lia.
    - pose proof (@ATPv_hi rc tlsI) as TH. unfold ATP in *. lia.
  Qed.
  End Sz3.
  Lemma slocA_below : ltac:(let t := eval cbv delta [slocA_below__stmt] in slocA_below__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m tls P n k. ltac2:(SecDiet.SzSec.closeP 'slocA_below__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition farg_str_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m SP D dn lo (w : word) cs,
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo + 8 <= SP -> 0 <= dn ->
    farg_word true L RNG FL CL SP D dn m (AStr cs) w ->
    arg_ok lo 0 D dn RNG m lo SP lo w (PA_s cs)
    /\ (forall sp : word, bv_unsigned sp = SP -> pword_ok RNG lo sp m (AStr cs) w)
    /\ pword_sep [(D, D + dn)] (AStr cs) w.
  Section Sz4.
  Variables L RNG s CL FB FL m SP D dn lo w cs : ltac2:(SecDiet.SzSec.tyM 'farg_str_factsA__stmt "vvvvvvvvvvvvv" @L).
  Lemma farg_str_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'farg_str_factsA__stmt "vvvvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOA LSP Hdn FW.
    cbn in FW. destruct FW as (P & bs & slack & -> & BY & NZ & -> & LB & PAD & DD & LOC & MOB & RG).
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof (pad8_range (P + Z.of_nat (length bs) + 1)) as PR. unfold pad8 in PR.
    set (pd := (- (P + Z.of_nat (length bs) + 1)) mod 8) in *.
    pose proof (slocA_below _ _ _ _ _ _ _ _ _ _ _ G LOC ltac:(lia) ltac:(lia)) as BEL.
    pose proof (@ATOP_hi rc) as AH.
    pose proof MOB as (P0 & P47 & _).
    assert (EP : bv_unsigned (Z_to_bv 64 P : word) = P) by (apply unsigned_lit; lia).
    assert (SOS : sobj RNG m P (P + (Z.of_nat (length bs) + 1))) by (apply mobjA_sobj; [exact MOB | lia]).
    assert (NZF : Forall (fun b : byte => bv_unsigned b <> 0) bs).
    { apply Forall_forall. intros b Hb E. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|].
      rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b), E. reflexivity. }
    split; [| split].
    - cbn [arg_ok]. rewrite EP. exists (firstn (Z.to_nat pd) slack).
      assert (LS : length (firstn (Z.to_nat pd) slack) = Z.to_nat pd) by (rewrite length_firstn; lia).
      unfold zlength. rewrite length_map, LS.
      split. { rewrite zb_unsigned. rewrite <- (firstn_skipn (Z.to_nat pd) slack) in BY.
               change (bs ++ Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack ++ skipn (Z.to_nat pd) slack)
                 with (bs ++ (Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack) ++ skipn (Z.to_nat pd) slack) in BY.
               rewrite app_assoc in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split. { apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
               pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
               pose proof (proj1 (Forall_forall _ _) NZF b Hb) as Nb. cbv beta in Nb. lia. }
      split; [lia|]. split; [lia|]. split; [left; lia|]. split; [left; lia|]. split; [lia|]. split; [left; lia|]. split; [lia|].
      split; [eapply rng_sub'; [exact RG | lia]|].
      replace (P + Z.of_nat (length bs) + 1) with (P + (Z.of_nat (length bs) + 1)) by lia. exact SOS.
    - intros sp ESP. cbn [pword_ok]. rewrite EP, zb_unsigned. unfold pstrL.
      split. { change (bs ++ Z_to_bv 8 0 :: slack) with (bs ++ [Z_to_bv 8 0] ++ slack) in BY. rewrite app_assoc in BY.
               apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split; [exact NZF|]. split; [left; lia|]. split; [lia|]. split; [exact SOS|]. eapply rng_sub'; [exact RG | lia].
    - cbn [pword_sep]. rewrite EP, zb_unsigned. cbn [disjoint_from]. split; [lia | exact I].
  Qed.
  End Sz4.
  Lemma farg_str_factsA : ltac:(let t := eval cbv delta [farg_str_factsA__stmt] in farg_str_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m SP D dn lo w cs. ltac2:(SecDiet.SzSec.closeP 'farg_str_factsA__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fargs_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m SP D dn lo,
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo + 8 <= SP -> 0 <= dn ->
    forall its args ws, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok its args = true ->
    Forall2 (farg_word true L RNG FL CL SP D dn m) args ws ->
    args_ok lo 0 D dn RNG m lo SP lo ws (to_pargs its args)
    /\ (forall sp : word, bv_unsigned sp = SP -> Forall2 (pword_ok RNG lo sp m) args ws)
    /\ Forall2 (pword_sep [(D, D + dn)]) args ws.
  Section Sz5.
  Variables L RNG s CL FB FL m SP D dn lo : ltac2:(SecDiet.SzSec.tyM 'fargs_factsA__stmt "vvvvvvvvvvv" @L).
  Lemma fargs_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'fargs_factsA__stmt "vvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOA LSP Hdn.
    induction its as [|[l|c|b] its IH]; intros args ws OK FW.
    - cbn in OK. destruct args; [|discriminate]. inversion FW; subst. cbn. split; [exact I|]. split; [intros; constructor | constructor].
    - cbn in OK |- *. apply andb_prop in OK as [_ OK]. apply IH; assumption.
    - cbn in OK |- *. destruct args as [|a args]; [discriminate|]. apply andb_prop in OK as [OKc OK].
      inversion FW as [|a' w args' ws' FA FW']; subst. destruct (IH args ws' OK FW') as (I1 & I2 & I3).
      cbn [args_ok].
      destruct c; destruct a as [v|sv]; try discriminate OKc; cbn [conv_parg].
      + split; [split; [cbn in FA |- *; subst w; exact (s32_facts v) | exact I1]|]. split; [intros sp E; constructor; [exact I | exact (I2 sp E)] | constructor; [exact I | exact I3]].
      + split; [split; [cbn in FA |- *; subst w; exact (u32_facts v) | exact I1]|]. split; [intros sp E; constructor; [exact I | exact (I2 sp E)] | constructor; [exact I | exact I3]].
      + split; [split; [cbn in FA |- *; subst w; exact (u32_facts v) | exact I1]|]. split; [intros sp E; constructor; [exact I | exact (I2 sp E)] | constructor; [exact I | exact I3]].
      + destruct (farg_str_factsA _ _ _ _ _ _ _ _ _ _ _ _ _ G LOA LSP Hdn FA) as (S1 & S2 & S3).
        split; [split; [exact S1 | exact I1]|]. split; [intros sp E; constructor; [exact (S2 sp E) | exact (I2 sp E)] | constructor; [exact S3 | exact I3]].
      + split; [split; [cbn in FA |- *; subst w; exact (u64_facts v) | exact I1]|]. split; [intros sp E; constructor; [exact I | exact (I2 sp E)] | constructor; [exact I | exact I3]].
    - cbn in OK. discriminate.
  Qed.
  End Sz5.
  Lemma fargs_factsA : ltac:(let t := eval cbv delta [fargs_factsA__stmt] in fargs_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m SP D dn lo. ltac2:(SecDiet.SzSec.closeP 'fargs_factsA__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma stdio_stack_bigA : SNPRINTF_I_DEPTH <= STDIO_STACK.
  Proof using Type. pin_using tt. unfold SNPRINTF_I_DEPTH, STDIO_STACK. lia. Qed.

  Definition vsnprintf_proofA__stmt : Prop := vsnprintf_spec_stmt GIOA.
  Section Sz7.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo DST n FMTA AP fs ws junk : ltac2:(SecDiet.SzSec.tyM 'vsnprintf_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv" @ra).
  Lemma vsnprintf_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'vsnprintf_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros args PRE -> -> -> -> HN FAT FOK LWS L4 FW APC SPAP APHI APD DSTC CR.
    pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ PRE) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct FAT as (FBY & FLO & FHI & FGL).
    unfold fmt_ok in FOK. apply andb_prop in FOK as [IOK FLEN]. rewrite items_ok_eqA in IOK. apply Z.ltb_lt in FLEN.
    pose proof (fmt_output_bound fs args IOK) as OB. rewrite str_length in OB.
    assert (FLn : fargs_len args <= Z.of_nat (length args) * (80 + 2^24)).
    { clear -FW. revert ws FW. induction args as [|a args IH]; intros ws FW; [cbn; Lia.lia|].
      inversion FW as [|a' w args' ws' FA FW']; subst.
      assert (Ha : farg_len a <= 2^24). { destruct a as [z|cs]; cbn; [Lia.lia|]. cbn in FA. destruct FA as (P & bs & slack & _ & _ & _ & -> & LB & _).
                                         unfold zlength. rewrite length_map. Lia.lia. }
      specialize (IH ws' FW'). cbn [fargs_len length]. Lia.lia. }
    assert (FL4 : fargs_len args <= 4 * (80 + 2^24)) by (clear -FLn L4; pose proof (fargs_len_nonneg args); Lia.nia).
    destruct (cobjA_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ DST n lo G CR ltac:(lia) LOA) as (D0 & DLO & D3 & D47 & SOD & RGD & IESD & _).
    (* [comment removed for export] *)
    destruct (stk_split _ _ _ (bv_unsigned sp - 16384) _ ST ltac:(lia)) as [ST1 ST2].
    set (lo' := bv_unsigned sp - 16384) in *.
    assert (LOA' : ATOP + 4096 <= lo') by (subst lo'; lia).
    destruct (fargs_factsA _ _ _ _ _ _ _ (bv_unsigned sp) DST n lo' G LOA' ltac:(subst lo'; lia) ltac:(lia) (fmt fs) args ws IOK FW) as (AOK & PWS & PSEPW).
    specialize (PWS sp eq_refl).
    set (its := pitems fs args ws).
    assert (LSTR : (length (str fs) <= length (str fs))%nat) by Lia.lia.
    assert (IOK' : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux (length (str fs)) (str fs)) args = true) by exact IOK.
    pose proof (str_range fs) as SRG. apply Forall_app in SRG. destruct SRG as [SRG _].
    pose proof (pitems_render _ _ _ ws LSTR IOK' LWS) as EF. fold (pitems fs args ws) in EF. fold its in EF.
    pose proof (pitems_ok _ _ _ ws LSTR IOK' SRG) as OKI. fold (pitems fs args ws) in OKI. fold its in OKI.
    pose proof (pitems_words RNG lo' sp m _ _ _ _ LSTR IOK' PWS) as PWI. fold (pitems fs args ws) in PWI. fold its in PWI.
    pose proof (pitems_sep [(DST, DST + n)] _ _ _ _ LSTR IOK' PSEPW) as PSI. fold (pitems fs args ws) in PSI. fold its in PSI.
    pose proof (fmt_nonzero _ _ _ LSTR IOK') as FNZ.
    pose proof (gia_global_mobjA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G FGL RIMG RIMGSH) as MOF.
    pose proof (rw_cells_bound _ _ _ _ APC) as APB. rewrite cells_size_map_C8 in APB.
    pose proof (str_length fs) as SLEN.
    assert (KLO' : KHIGH <= lo') by (subst lo'; unfold KHIGH in *; lia).
    eapply evtF_mono.
    { eapply (vsnprintf_i_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST n FMTA AP lo'
                (str fs ++ [0]) ws (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)) canary (zb (str fs)) its)
        with (jd := junk).
      - exact HN.
      - apply str_range.
      - apply (fmt_pass1 fs args IOK). rewrite str_length. unfold INT_MAX. lia.
      - apply fmt_bridge; [exact IOK|]. unfold INT_MAX. lia.
      - unfold VSNPRINTF_I_DEPTH. subst lo'. lia.
      - unfold GLOBALS_TOP. subst lo'. lia.
      - lia.
      - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app, str_length. change (zlength [0]) with 1. lia.
      - unfold zlength. lia.
      - split; [lia|]. split; [lia|]. split; [right; lia|]. left. subst lo'. lia.
      - exact KLO'.
      - exact IESD.
      - subst lo'. eapply rng_sub'; [exact RSTK | lia].
      - exact RIMG.
      - unfold zlength. eapply rng_sub'; [exact RSTKF | lia].
      - exact RGD.
      - exact (gs_rng0 _ GSL _ _ _ _ _ _ _ G).
      - apply zb_app.
      - unfold zb. apply Forall_map. apply Forall_forall. intros c Hc.
        pose proof (proj1 (Forall_forall _ _) SRG c Hc) as Rc. pose proof (proj1 (Forall_forall _ _) FNZ c Hc) as Nc. cbv beta in Rc, Nc.
        rewrite b8_unsigned by lia. exact Nc.
      - symmetry. exact EF.
      - exact OKI.
      - reflexivity. - reflexivity. - reflexivity. - reflexivity.
      - exact DSTC.
      - rewrite <- str_bytes. exact FBY.
      - apply va_area_of_cells. exact APC.
      - exact AOK.
      - exact ST2.
      - exact SSP.
      - exact MI.
      - exact I.
      - exact ENV.
      - exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G).
      - apply (gs_stack _ GSL _ _ _ _ _ _ _ lo' (bv_unsigned sp) G); subst lo'; lia.
      - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app, str_length. change (zlength [0]) with 1.
        apply mobjA_sobj; [exact MOF | lia].
      - apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; lia | lia].
      - exact SOD.
      - eapply pargs_okL_of_words; [exact PWI | exact APC | lia | lia | eapply rng_sub'; [exact RSTKF | lia]].
      - eapply pargs_sep_of_words; [exact PWI | exact PSI | cbn [disjoint_from]; split; [lia | exact I] | lia | lia]. }
    cbv beta. intros ms' PO. unfold vsnprintf_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & jd' & m' & -> & MU & WM & MI' & ST' & SSP' & DST' & Hr).
    set (out := Fmt.snprintf n fs args) in *.
    change (firstn (Z.to_nat (n - 1)) (List.concat (fmt_pieces (fmt fs) args))) with out in DST'.
    pose proof (rw_CB_length _ _ _ _ DST') as LJ. rewrite length_app, zb_length in LJ. cbn [length] in LJ.
    exists (Z_to_bv 64 (zlength (fmt_output (fmt fs) args))), m', (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')).
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; subst lo'; lia] | exact ST' | subst lo'; lia ]. }
    split; [reflexivity|].
    apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat n) _ [] [length out + 1; Z.to_nat n - length out - 1]%nat) in DST'; [| cbn; lia].
    cbn [mk_CB_cells app] in DST'.
    replace (firstn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')) with (map b8 out ++ [Z_to_bv 8 0]) in DST'.
    2:{ rewrite firstn_app, zb_length, (firstn_all2 (zb out)) by (rewrite zb_length; lia).
        replace (length out + 1 - length out)%nat with 1%nat by lia. reflexivity. }
    rewrite (firstn_all2 (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd'))) in DST' by (rewrite length_skipn, length_app, zb_length; cbn [length]; lia).
    exact DST'.
  Qed.
  End Sz7.
  Theorem vsnprintf_proofA : ltac:(let t := eval cbv delta [vsnprintf_proofA__stmt] in vsnprintf_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo DST n FMTA AP fs args ws junk. ltac2:(SecDiet.SzSec.closeP 'vsnprintf_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma args_ok_more : forall Fp FS B BS RNG m lo sp ap ws more pargs,
    args_ok Fp FS B BS RNG m lo sp ap ws pargs -> args_ok Fp FS B BS RNG m lo sp ap (ws ++ more) pargs.
  Proof using Type. pin_using tt.
    intros Fp FS B BS RNG m lo sp ap ws more pargs. revert ws.
    induction pargs as [|a pargs IH]; intros ws AOK; [destruct (ws ++ more); exact I|].
    destruct ws as [|w ws]; [destruct AOK|]. cbn in AOK |- *. destruct AOK as [H1 H2]. split; [exact H1 | apply IH; exact H2].
  Qed.

  Definition snprintf_proofA__stmt : Prop := snprintf_spec_stmt GIOA.
  Section Sz9.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo DST n FMTA fs junk : ltac2:(SecDiet.SzSec.tyM 'snprintf_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv" @ra).
  Lemma snprintf_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'snprintf_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros args PRE -> -> -> HN FAT FOK L3 FW DSTC CR.
    pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ PRE) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct FAT as (FBY & FLO & FHI & FGL).
    unfold fmt_ok in FOK. apply andb_prop in FOK as [IOK FLEN]. rewrite items_ok_eqA in IOK. apply Z.ltb_lt in FLEN.
    pose proof (fmt_output_bound fs args IOK) as OB. rewrite str_length in OB.
    set (ws := firstn (length args) [a3; a4; a5]) in *.
    assert (LWS : length ws = length args) by (subst ws; rewrite length_firstn; cbn [length]; Lia.lia).
    assert (FLn : fargs_len args <= Z.of_nat (length args) * (80 + 2^24)).
    { clear -FW. revert FW. generalize ws. induction args as [|a args IH]; intros ws0 FW; [cbn; Lia.lia|].
      inversion FW as [|a' w args' ws' FA FW']; subst.
      assert (Ha : farg_len a <= 2^24). { destruct a as [z|cs]; cbn; [Lia.lia|]. cbn in FA. destruct FA as (P & bs & slack & _ & _ & _ & -> & LB & _).
                                         unfold zlength. rewrite length_map. Lia.lia. }
      specialize (IH ws' FW'). cbn [fargs_len length]. Lia.lia. }
    assert (FL4 : fargs_len args <= 3 * (80 + 2^24)) by (clear -FLn L3; pose proof (fargs_len_nonneg args); Lia.nia).
    destruct (cobjA_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ DST n lo G CR ltac:(lia) LOA) as (D0 & DLO & D3 & D47 & SOD & RGD & IESD & _).
    destruct (stk_split _ _ _ (bv_unsigned sp - 16384) _ ST ltac:(lia)) as [ST1 ST2].
    set (lo' := bv_unsigned sp - 16384) in *.
    assert (LOA' : ATOP + 4096 <= lo') by (subst lo'; lia).
    destruct (fargs_factsA _ _ _ _ _ _ _ (bv_unsigned sp) DST n lo' G LOA' ltac:(subst lo'; lia) ltac:(lia) (fmt fs) args ws IOK FW) as (AOK & PWS & PSEPW).
    specialize (PWS sp eq_refl).
    set (its := pitems fs args ws).
    assert (LSTR : (length (str fs) <= length (str fs))%nat) by Lia.lia.
    assert (IOK' : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux (length (str fs)) (str fs)) args = true) by exact IOK.
    pose proof (str_range fs) as SRG. apply Forall_app in SRG. destruct SRG as [SRG _].
    pose proof (pitems_render _ _ _ ws LSTR IOK' LWS) as EF. fold (pitems fs args ws) in EF. fold its in EF.
    pose proof (pitems_ok _ _ _ ws LSTR IOK' SRG) as OKI. fold (pitems fs args ws) in OKI. fold its in OKI.
    pose proof (pitems_words RNG lo' sp m _ _ _ _ LSTR IOK' PWS) as PWI. fold (pitems fs args ws) in PWI. fold its in PWI.
    pose proof (pitems_sep [(DST, DST + n)] _ _ _ _ LSTR IOK' PSEPW) as PSI. fold (pitems fs args ws) in PSI. fold its in PSI.
    pose proof (fmt_nonzero _ _ _ LSTR IOK') as FNZ.
    pose proof (gia_global_mobjA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G FGL RIMG RIMGSH) as MOF.
    pose proof (str_length fs) as SLEN.
    assert (KLO' : KHIGH <= lo') by (subst lo'; unfold KHIGH in *; lia).
    (* [comment removed for export] *)
    assert (EWS : ws ++ (skipn (length args) [a3; a4; a5] ++ [a6; a7]) = [a3; a4; a5; a6; a7]).
    { subst ws. rewrite app_assoc, firstn_skipn. reflexivity. }
    apply (args_ok_more _ _ _ _ _ _ _ _ _ _ (skipn (length args) [a3; a4; a5] ++ [a6; a7])) in AOK. rewrite EWS in AOK.
    apply (pwords_ok_more _ _ _ _ _ _ (skipn (length args) [a3; a4; a5] ++ [a6; a7])) in PWI. rewrite EWS in PWI.
    eapply evtF_mono.
    { eapply (snprintf_i_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST n FMTA lo'
                (str fs ++ [0]) a3 a4 a5 a6 a7 (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)) canary (zb (str fs)) its)
        with (jd := junk).
      - exact HN.
      - apply str_range.
      - apply (fmt_pass1 fs args IOK). rewrite str_length. unfold INT_MAX. lia.
      - apply fmt_bridge; [exact IOK|]. unfold INT_MAX. lia.
      - unfold SNPRINTF_I_DEPTH. subst lo'. lia.
      - unfold GLOBALS_TOP. subst lo'. lia.
      - lia.
      - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app, str_length. change (zlength [0]) with 1. lia.
      - split; [lia|]. split; [lia|]. split; [right; lia|]. left. subst lo'. lia.
      - exact KLO'.
      - exact IESD.
      - subst lo'. eapply rng_sub'; [exact RSTK | lia].
      - exact RIMG.
      - exact RGD.
      - exact (gs_rng0 _ GSL _ _ _ _ _ _ _ G).
      - apply zb_app.
      - unfold zb. apply Forall_map. apply Forall_forall. intros c Hc.
        pose proof (proj1 (Forall_forall _ _) SRG c Hc) as Rc. pose proof (proj1 (Forall_forall _ _) FNZ c Hc) as Nc. cbv beta in Rc, Nc.
        rewrite b8_unsigned by lia. exact Nc.
      - symmetry. exact EF.
      - exact OKI.
      - reflexivity. - reflexivity. - reflexivity.
      - exact DSTC.
      - rewrite <- str_bytes. exact FBY.
      - exact AOK.
      - exact ST2.
      - exact SSP.
      - exact MI.
      - exact I.
      - exact ENV.
      - exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G).
      - apply (gs_stack _ GSL _ _ _ _ _ _ _ lo' (bv_unsigned sp) G); subst lo'; lia.
      - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app, str_length. change (zlength [0]) with 1.
        apply mobjA_sobj; [exact MOF | lia].
      - apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; lia | lia].
      - exact SOD.
      - exact PWI.
      - exact PSI. }
    cbv beta. intros ms' PO. unfold vsnprintf_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & jd' & m' & -> & MU & WM & MI' & ST' & SSP' & DST' & Hr).
    set (out := Fmt.snprintf n fs args) in *.
    change (firstn (Z.to_nat (n - 1)) (List.concat (fmt_pieces (fmt fs) args))) with out in DST'.
    pose proof (rw_CB_length _ _ _ _ DST') as LJ. rewrite length_app, zb_length in LJ. cbn [length] in LJ.
    exists (Z_to_bv 64 (zlength (fmt_output (fmt fs) args))), m', (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')).
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; subst lo'; lia] | exact ST' | subst lo'; lia ]. }
    split; [reflexivity|].
    apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat n) _ [] [length out + 1; Z.to_nat n - length out - 1]%nat) in DST'; [| cbn; lia].
    cbn [mk_CB_cells app] in DST'.
    replace (firstn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')) with (map b8 out ++ [Z_to_bv 8 0]) in DST'.
    2:{ rewrite firstn_app, zb_length, (firstn_all2 (zb out)) by (rewrite zb_length; lia).
        replace (length out + 1 - length out)%nat with 1%nat by lia. reflexivity. }
    rewrite (firstn_all2 (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd'))) in DST' by (rewrite length_skipn, length_app, zb_length; cbn [length]; lia).
    exact DST'.
  Qed.
  End Sz9.
  Theorem snprintf_proofA : ltac:(let t := eval cbv delta [snprintf_proofA__stmt] in snprintf_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo DST n FMTA fs args junk. ltac2:(SecDiet.SzSec.closeP 'snprintf_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv"). Qed.
End GlueSn.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.Printf_snsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vfprintf_sn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vsnprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_vsnprintf_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_mkstemp__A3S.I_snprintf_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_fmtA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.Printf_pitems.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueSn.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  (* [comment removed for export] *)
  Lemma items_ok_eqA : forall its args, A3P.Pcap_ifaceA.TwB.items_ok its args = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok its args.
  Proof using Type. pin_using tt.
    induction its as [|[l|c|b] its IH]; intros args; cbn; [reflexivity| | |reflexivity].
    - rewrite IH. reflexivity.
    - destruct args as [|a args]; [reflexivity|]. rewrite IH. destruct c, a; reflexivity.
  Qed.

  Lemma zb_unsigned : forall (bs : list byte), zb (map bv_unsigned bs) = bs.
  Proof using Type. pin_using tt. induction bs as [|b bs IH]; cbn; [reflexivity|]. unfold zb in *. cbn. rewrite definitions.Z_to_bv_bv_unsigned, IH. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition slocA_below__stmt : Prop := forall L RNG (s : PS) CL FB FL m tls P n k,
    GIOA L RNG s CL FB FL m -> slocA tls FL CL P n k -> 0 <= n -> 0 <= k -> P + n + k <= ATOP.
  Section Sz3.
  Variables L RNG s CL FB FL m tls P n k : ltac2:(SecDiet.SzSec.tyM 'slocA_below__stmt "vvvvvvvvvvv" @L).
  Lemma slocA_below__body : ltac2:(SecDiet.SzSec.bodyP 'slocA_below__stmt "vvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOC Hn Hk.
    pose proof (@ATOP_lo rc) as AL.
    destruct LOC as [CR | [(g & HG & G1 & G2 & G3 & G4) | (_ & T1 & T2)]].
    - destruct (clocA_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G CR ltac:(lia)) as (_ & X & _). lia.
    - lia.
    - pose proof (@ATPv_hi rc tlsI) as TH. unfold ATP in *. lia.
  Qed.
  End Sz3.
  Lemma slocA_below : ltac:(let t := eval cbv delta [slocA_below__stmt] in slocA_below__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m tls P n k. ltac2:(SecDiet.SzSec.closeP 'slocA_below__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition farg_str_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m SP D dn lo (w : word) cs,
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo + 8 <= SP -> 0 <= dn ->
    farg_word true L RNG FL CL SP D dn m (AStr cs) w ->
    arg_ok lo 0 D dn RNG m lo SP lo w (PA_s cs)
    /\ (forall sp : word, bv_unsigned sp = SP -> pword_ok RNG lo sp m (AStr cs) w)
    /\ pword_sep [(D, D + dn)] (AStr cs) w.
  Section Sz4.
  Variables L RNG s CL FB FL m SP D dn lo w cs : ltac2:(SecDiet.SzSec.tyM 'farg_str_factsA__stmt "vvvvvvvvvvvvv" @L).
  Lemma farg_str_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'farg_str_factsA__stmt "vvvvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOA LSP Hdn FW.
    cbn in FW. destruct FW as (P & bs & slack & -> & BY & NZ & -> & LB & PAD & DD & LOC & MOB & RG).
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof (pad8_range (P + Z.of_nat (length bs) + 1)) as PR. unfold pad8 in PR.
    set (pd := (- (P + Z.of_nat (length bs) + 1)) mod 8) in *.
    pose proof (slocA_below _ _ _ _ _ _ _ _ _ _ _ G LOC ltac:(lia) ltac:(lia)) as BEL.
    pose proof (@ATOP_hi rc) as AH.
    pose proof MOB as (P0 & P47 & _).
    assert (EP : bv_unsigned (Z_to_bv 64 P : word) = P) by (apply unsigned_lit; lia).
    assert (SOS : sobj RNG m P (P + (Z.of_nat (length bs) + 1))) by (apply mobjA_sobj; [exact MOB | lia]).
    assert (NZF : Forall (fun b : byte => bv_unsigned b <> 0) bs).
    { apply Forall_forall. intros b Hb E. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|].
      rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b), E. reflexivity. }
    split; [| split].
    - cbn [arg_ok]. rewrite EP. exists (firstn (Z.to_nat pd) slack).
      assert (LS : length (firstn (Z.to_nat pd) slack) = Z.to_nat pd) by (rewrite length_firstn; lia).
      unfold zlength. rewrite length_map, LS.
      split. { rewrite zb_unsigned. rewrite <- (firstn_skipn (Z.to_nat pd) slack) in BY.
               change (bs ++ Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack ++ skipn (Z.to_nat pd) slack)
                 with (bs ++ (Z_to_bv 8 0 :: firstn (Z.to_nat pd) slack) ++ skipn (Z.to_nat pd) slack) in BY.
               rewrite app_assoc in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split. { apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & Hb).
               pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
               pose proof (proj1 (Forall_forall _ _) NZF b Hb) as Nb. cbv beta in Nb. lia. }
      split; [lia|]. split; [lia|]. split; [left; lia|]. split; [left; lia|]. split; [lia|]. split; [left; lia|]. split; [lia|].
      split; [eapply rng_sub'; [exact RG | lia]|].
      replace (P + Z.of_nat (length bs) + 1) with (P + (Z.of_nat (length bs) + 1)) by lia. exact SOS.
    - intros sp ESP. cbn [pword_ok]. rewrite EP, zb_unsigned. unfold pstrL.
      split. { change (bs ++ Z_to_bv 8 0 :: slack) with (bs ++ [Z_to_bv 8 0] ++ slack) in BY. rewrite app_assoc in BY.
               apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. exact (proj1 BY). }
      split; [exact NZF|]. split; [left; lia|]. split; [lia|]. split; [exact SOS|]. eapply rng_sub'; [exact RG | lia].
    - cbn [pword_sep]. rewrite EP, zb_unsigned. cbn [disjoint_from]. split; [lia | exact I].
  Qed.
  End Sz4.
  Lemma farg_str_factsA : ltac:(let t := eval cbv delta [farg_str_factsA__stmt] in farg_str_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m SP D dn lo w cs. ltac2:(SecDiet.SzSec.closeP 'farg_str_factsA__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fargs_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m SP D dn lo,
    GIOA L RNG s CL FB FL m -> ATOP + 4096 <= lo -> lo + 8 <= SP -> 0 <= dn ->
    forall its args ws, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok its args = true ->
    Forall2 (farg_word true L RNG FL CL SP D dn m) args ws ->
    args_ok lo 0 D dn RNG m lo SP lo ws (to_pargs its args)
    /\ (forall sp : word, bv_unsigned sp = SP -> Forall2 (pword_ok RNG lo sp m) args ws)
    /\ Forall2 (pword_sep [(D, D + dn)]) args ws.
  Section Sz5.
  Variables L RNG s CL FB FL m SP D dn lo : ltac2:(SecDiet.SzSec.tyM 'fargs_factsA__stmt "vvvvvvvvvvv" @L).
  Lemma fargs_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'fargs_factsA__stmt "vvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOA LSP Hdn.
    induction its as [|[l|c|b] its IH]; intros args ws OK FW.
    - cbn in OK. destruct args; [|discriminate]. inversion FW; subst. cbn. split; [exact I|]. split; [intros; constructor | constructor].
    - cbn in OK |- *. apply andb_prop in OK as [_ OK]. apply IH; assumption.
    - cbn in OK |- *. destruct args as [|a args]; [discriminate|]. apply andb_prop in OK as [OKc OK].
      inversion FW as [|a' w args' ws' FA FW']; subst. destruct (IH args ws' OK FW') as (I1 & I2 & I3).
      cbn [args_ok].
      destruct c; destruct a as [v|sv]; try discriminate OKc; cbn [conv_parg].
      + split; [split; [cbn in FA |- *; subst w; exact (s32_facts v) | exact I1]|]. split; [intros sp E; constructor; [exact I | exact (I2 sp E)] | constructor; [exact I | exact I3]].
      + split; [split; [cbn in FA |- *; subst w; exact (u32_facts v) | exact I1]|]. split; [intros sp E; constructor; [exact I | exact (I2 sp E)] | constructor; [exact I | exact I3]].
      + split; [split; [cbn in FA |- *; subst w; exact (u32_facts v) | exact I1]|]. split; [intros sp E; constructor; [exact I | exact (I2 sp E)] | constructor; [exact I | exact I3]].
      + destruct (farg_str_factsA _ _ _ _ _ _ _ _ _ _ _ _ _ G LOA LSP Hdn FA) as (S1 & S2 & S3).
        split; [split; [exact S1 | exact I1]|]. split; [intros sp E; constructor; [exact (S2 sp E) | exact (I2 sp E)] | constructor; [exact S3 | exact I3]].
      + split; [split; [cbn in FA |- *; subst w; exact (u64_facts v) | exact I1]|]. split; [intros sp E; constructor; [exact I | exact (I2 sp E)] | constructor; [exact I | exact I3]].
    - cbn in OK. discriminate.
  Qed.
  End Sz5.
  Lemma fargs_factsA : ltac:(let t := eval cbv delta [fargs_factsA__stmt] in fargs_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m SP D dn lo. ltac2:(SecDiet.SzSec.closeP 'fargs_factsA__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma stdio_stack_bigA : SNPRINTF_I_DEPTH <= STDIO_STACK.
  Proof using Type. pin_using tt. unfold SNPRINTF_I_DEPTH, STDIO_STACK. lia. Qed.

  Definition vsnprintf_proofA__stmt : Prop := vsnprintf_spec_stmt GIOA.
  Section Sz7.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo DST n FMTA AP fs ws junk : ltac2:(SecDiet.SzSec.tyM 'vsnprintf_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv" @ra).
  Lemma vsnprintf_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'vsnprintf_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros args PRE -> -> -> -> HN FAT FOK LWS L4 FW APC SPAP APHI APD DSTC CR.
    pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ PRE) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct FAT as (FBY & FLO & FHI & FGL).
    unfold fmt_ok in FOK. apply andb_prop in FOK as [IOK FLEN]. rewrite items_ok_eqA in IOK. apply Z.ltb_lt in FLEN.
    pose proof (fmt_output_bound fs args IOK) as OB. rewrite str_length in OB.
    assert (FLn : fargs_len args <= Z.of_nat (length args) * (80 + 2^24)).
    { clear -FW. revert ws FW. induction args as [|a args IH]; intros ws FW; [cbn; Lia.lia|].
      inversion FW as [|a' w args' ws' FA FW']; subst.
      assert (Ha : farg_len a <= 2^24). { destruct a as [z|cs]; cbn; [Lia.lia|]. cbn in FA. destruct FA as (P & bs & slack & _ & _ & _ & -> & LB & _).
                                         unfold zlength. rewrite length_map. Lia.lia. }
      specialize (IH ws' FW'). cbn [fargs_len length]. Lia.lia. }
    assert (FL4 : fargs_len args <= 4 * (80 + 2^24)) by (clear -FLn L4; pose proof (fargs_len_nonneg args); Lia.nia).
    destruct (cobjA_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ DST n lo G CR ltac:(lia) LOA) as (D0 & DLO & D3 & D47 & SOD & RGD & IESD & _).
    (* [comment removed for export] *)
    destruct (stk_split _ _ _ (bv_unsigned sp - 16384) _ ST ltac:(lia)) as [ST1 ST2].
    set (lo' := bv_unsigned sp - 16384) in *.
    assert (LOA' : ATOP + 4096 <= lo') by (subst lo'; lia).
    destruct (fargs_factsA _ _ _ _ _ _ _ (bv_unsigned sp) DST n lo' G LOA' ltac:(subst lo'; lia) ltac:(lia) (fmt fs) args ws IOK FW) as (AOK & PWS & PSEPW).
    specialize (PWS sp eq_refl).
    set (its := pitems fs args ws).
    assert (LSTR : (length (str fs) <= length (str fs))%nat) by Lia.lia.
    assert (IOK' : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux (length (str fs)) (str fs)) args = true) by exact IOK.
    pose proof (str_range fs) as SRG. apply Forall_app in SRG. destruct SRG as [SRG _].
    pose proof (pitems_render _ _ _ ws LSTR IOK' LWS) as EF. fold (pitems fs args ws) in EF. fold its in EF.
    pose proof (pitems_ok _ _ _ ws LSTR IOK' SRG) as OKI. fold (pitems fs args ws) in OKI. fold its in OKI.
    pose proof (pitems_words RNG lo' sp m _ _ _ _ LSTR IOK' PWS) as PWI. fold (pitems fs args ws) in PWI. fold its in PWI.
    pose proof (pitems_sep [(DST, DST + n)] _ _ _ _ LSTR IOK' PSEPW) as PSI. fold (pitems fs args ws) in PSI. fold its in PSI.
    pose proof (fmt_nonzero _ _ _ LSTR IOK') as FNZ.
    pose proof (gia_global_mobjA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G FGL RIMG RIMGSH) as MOF.
    pose proof (rw_cells_bound _ _ _ _ APC) as APB. rewrite cells_size_map_C8 in APB.
    pose proof (str_length fs) as SLEN.
    assert (KLO' : KHIGH <= lo') by (subst lo'; unfold KHIGH in *; lia).
    eapply evtF_mono.
    { eapply (vsnprintf_i_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST n FMTA AP lo'
                (str fs ++ [0]) ws (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)) canary (zb (str fs)) its)
        with (jd := junk).
      - exact HN.
      - apply str_range.
      - apply (fmt_pass1 fs args IOK). rewrite str_length. unfold INT_MAX. lia.
      - apply fmt_bridge; [exact IOK|]. unfold INT_MAX. lia.
      - unfold VSNPRINTF_I_DEPTH. subst lo'. lia.
      - unfold GLOBALS_TOP. subst lo'. lia.
      - lia.
      - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app, str_length. change (zlength [0]) with 1. lia.
      - unfold zlength. lia.
      - split; [lia|]. split; [lia|]. split; [right; lia|]. left. subst lo'. lia.
      - exact KLO'.
      - exact IESD.
      - subst lo'. eapply rng_sub'; [exact RSTK | lia].
      - exact RIMG.
      - unfold zlength. eapply rng_sub'; [exact RSTKF | lia].
      - exact RGD.
      - exact (gs_rng0 _ GSL _ _ _ _ _ _ _ G).
      - apply zb_app.
      - unfold zb. apply Forall_map. apply Forall_forall. intros c Hc.
        pose proof (proj1 (Forall_forall _ _) SRG c Hc) as Rc. pose proof (proj1 (Forall_forall _ _) FNZ c Hc) as Nc. cbv beta in Rc, Nc.
        rewrite b8_unsigned by lia. exact Nc.
      - symmetry. exact EF.
      - exact OKI.
      - reflexivity. - reflexivity. - reflexivity. - reflexivity.
      - exact DSTC.
      - rewrite <- str_bytes. exact FBY.
      - apply va_area_of_cells. exact APC.
      - exact AOK.
      - exact ST2.
      - exact SSP.
      - exact MI.
      - exact I.
      - exact ENV.
      - exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G).
      - apply (gs_stack _ GSL _ _ _ _ _ _ _ lo' (bv_unsigned sp) G); subst lo'; lia.
      - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app, str_length. change (zlength [0]) with 1.
        apply mobjA_sobj; [exact MOF | lia].
      - apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; lia | lia].
      - exact SOD.
      - eapply pargs_okL_of_words; [exact PWI | exact APC | lia | lia | eapply rng_sub'; [exact RSTKF | lia]].
      - eapply pargs_sep_of_words; [exact PWI | exact PSI | cbn [disjoint_from]; split; [lia | exact I] | lia | lia]. }
    cbv beta. intros ms' PO. unfold vsnprintf_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & jd' & m' & -> & MU & WM & MI' & ST' & SSP' & DST' & Hr).
    set (out := Fmt.snprintf n fs args) in *.
    change (firstn (Z.to_nat (n - 1)) (List.concat (fmt_pieces (fmt fs) args))) with out in DST'.
    pose proof (rw_CB_length _ _ _ _ DST') as LJ. rewrite length_app, zb_length in LJ. cbn [length] in LJ.
    exists (Z_to_bv 64 (zlength (fmt_output (fmt fs) args))), m', (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')).
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; subst lo'; lia] | exact ST' | subst lo'; lia ]. }
    split; [reflexivity|].
    apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat n) _ [] [length out + 1; Z.to_nat n - length out - 1]%nat) in DST'; [| cbn; lia].
    cbn [mk_CB_cells app] in DST'.
    replace (firstn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')) with (map b8 out ++ [Z_to_bv 8 0]) in DST'.
    2:{ rewrite firstn_app, zb_length, (firstn_all2 (zb out)) by (rewrite zb_length; lia).
        replace (length out + 1 - length out)%nat with 1%nat by lia. reflexivity. }
    rewrite (firstn_all2 (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd'))) in DST' by (rewrite length_skipn, length_app, zb_length; cbn [length]; lia).
    exact DST'.
  Qed.
  End Sz7.
  Theorem vsnprintf_proofA : ltac:(let t := eval cbv delta [vsnprintf_proofA__stmt] in vsnprintf_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo DST n FMTA AP fs args ws junk. ltac2:(SecDiet.SzSec.closeP 'vsnprintf_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma args_ok_more : forall Fp FS B BS RNG m lo sp ap ws more pargs,
    args_ok Fp FS B BS RNG m lo sp ap ws pargs -> args_ok Fp FS B BS RNG m lo sp ap (ws ++ more) pargs.
  Proof using Type. pin_using tt.
    intros Fp FS B BS RNG m lo sp ap ws more pargs. revert ws.
    induction pargs as [|a pargs IH]; intros ws AOK; [destruct (ws ++ more); exact I|].
    destruct ws as [|w ws]; [destruct AOK|]. cbn in AOK |- *. destruct AOK as [H1 H2]. split; [exact H1 | apply IH; exact H2].
  Qed.

  Definition snprintf_proofA__stmt : Prop := snprintf_spec_stmt GIOA.
  Section Sz9.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo DST n FMTA fs junk : ltac2:(SecDiet.SzSec.tyM 'snprintf_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv" @ra).
  Lemma snprintf_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'snprintf_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros args PRE -> -> -> HN FAT FOK L3 FW DSTC CR.
    pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ PRE) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct FAT as (FBY & FLO & FHI & FGL).
    unfold fmt_ok in FOK. apply andb_prop in FOK as [IOK FLEN]. rewrite items_ok_eqA in IOK. apply Z.ltb_lt in FLEN.
    pose proof (fmt_output_bound fs args IOK) as OB. rewrite str_length in OB.
    set (ws := firstn (length args) [a3; a4; a5]) in *.
    assert (LWS : length ws = length args) by (subst ws; rewrite length_firstn; cbn [length]; Lia.lia).
    assert (FLn : fargs_len args <= Z.of_nat (length args) * (80 + 2^24)).
    { clear -FW. revert FW. generalize ws. induction args as [|a args IH]; intros ws0 FW; [cbn; Lia.lia|].
      inversion FW as [|a' w args' ws' FA FW']; subst.
      assert (Ha : farg_len a <= 2^24). { destruct a as [z|cs]; cbn; [Lia.lia|]. cbn in FA. destruct FA as (P & bs & slack & _ & _ & _ & -> & LB & _).
                                         unfold zlength. rewrite length_map. Lia.lia. }
      specialize (IH ws' FW'). cbn [fargs_len length]. Lia.lia. }
    assert (FL4 : fargs_len args <= 3 * (80 + 2^24)) by (clear -FLn L3; pose proof (fargs_len_nonneg args); Lia.nia).
    destruct (cobjA_factsA FO GIOA fflagA GL _ _ _ _ _ _ _ DST n lo G CR ltac:(lia) LOA) as (D0 & DLO & D3 & D47 & SOD & RGD & IESD & _).
    destruct (stk_split _ _ _ (bv_unsigned sp - 16384) _ ST ltac:(lia)) as [ST1 ST2].
    set (lo' := bv_unsigned sp - 16384) in *.
    assert (LOA' : ATOP + 4096 <= lo') by (subst lo'; lia).
    destruct (fargs_factsA _ _ _ _ _ _ _ (bv_unsigned sp) DST n lo' G LOA' ltac:(subst lo'; lia) ltac:(lia) (fmt fs) args ws IOK FW) as (AOK & PWS & PSEPW).
    specialize (PWS sp eq_refl).
    set (its := pitems fs args ws).
    assert (LSTR : (length (str fs) <= length (str fs))%nat) by Lia.lia.
    assert (IOK' : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.items_ok (parse_fmt_aux (length (str fs)) (str fs)) args = true) by exact IOK.
    pose proof (str_range fs) as SRG. apply Forall_app in SRG. destruct SRG as [SRG _].
    pose proof (pitems_render _ _ _ ws LSTR IOK' LWS) as EF. fold (pitems fs args ws) in EF. fold its in EF.
    pose proof (pitems_ok _ _ _ ws LSTR IOK' SRG) as OKI. fold (pitems fs args ws) in OKI. fold its in OKI.
    pose proof (pitems_words RNG lo' sp m _ _ _ _ LSTR IOK' PWS) as PWI. fold (pitems fs args ws) in PWI. fold its in PWI.
    pose proof (pitems_sep [(DST, DST + n)] _ _ _ _ LSTR IOK' PSEPW) as PSI. fold (pitems fs args ws) in PSI. fold its in PSI.
    pose proof (fmt_nonzero _ _ _ LSTR IOK') as FNZ.
    pose proof (gia_global_mobjA FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ G FGL RIMG RIMGSH) as MOF.
    pose proof (str_length fs) as SLEN.
    assert (KLO' : KHIGH <= lo') by (subst lo'; unfold KHIGH in *; lia).
    (* [comment removed for export] *)
    assert (EWS : ws ++ (skipn (length args) [a3; a4; a5] ++ [a6; a7]) = [a3; a4; a5; a6; a7]).
    { subst ws. rewrite app_assoc, firstn_skipn. reflexivity. }
    apply (args_ok_more _ _ _ _ _ _ _ _ _ _ (skipn (length args) [a3; a4; a5] ++ [a6; a7])) in AOK. rewrite EWS in AOK.
    apply (pwords_ok_more _ _ _ _ _ _ (skipn (length args) [a3; a4; a5] ++ [a6; a7])) in PWI. rewrite EWS in PWI.
    eapply evtF_mono.
    { eapply (snprintf_i_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST n FMTA lo'
                (str fs ++ [0]) a3 a4 a5 a6 a7 (to_pargs (fmt fs) args) (fmt_pieces (fmt fs) args) (zlength (fmt_output (fmt fs) args)) canary (zb (str fs)) its)
        with (jd := junk).
      - exact HN.
      - apply str_range.
      - apply (fmt_pass1 fs args IOK). rewrite str_length. unfold INT_MAX. lia.
      - apply fmt_bridge; [exact IOK|]. unfold INT_MAX. lia.
      - unfold SNPRINTF_I_DEPTH. subst lo'. lia.
      - unfold GLOBALS_TOP. subst lo'. lia.
      - lia.
      - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app, str_length. change (zlength [0]) with 1. lia.
      - split; [lia|]. split; [lia|]. split; [right; lia|]. left. subst lo'. lia.
      - exact KLO'.
      - exact IESD.
      - subst lo'. eapply rng_sub'; [exact RSTK | lia].
      - exact RIMG.
      - exact RGD.
      - exact (gs_rng0 _ GSL _ _ _ _ _ _ _ G).
      - apply zb_app.
      - unfold zb. apply Forall_map. apply Forall_forall. intros c Hc.
        pose proof (proj1 (Forall_forall _ _) SRG c Hc) as Rc. pose proof (proj1 (Forall_forall _ _) FNZ c Hc) as Nc. cbv beta in Rc, Nc.
        rewrite b8_unsigned by lia. exact Nc.
      - symmetry. exact EF.
      - exact OKI.
      - reflexivity. - reflexivity. - reflexivity.
      - exact DSTC.
      - rewrite <- str_bytes. exact FBY.
      - exact AOK.
      - exact ST2.
      - exact SSP.
      - exact MI.
      - exact I.
      - exact ENV.
      - exact (gs_ckpf _ GSL _ _ _ _ _ _ _ G).
      - apply (gs_stack _ GSL _ _ _ _ _ _ _ lo' (bv_unsigned sp) G); subst lo'; lia.
      - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_fmt.zlength_app, str_length. change (zlength [0]) with 1.
        apply mobjA_sobj; [exact MOF | lia].
      - apply (gs_rodata _ GSL _ _ _ _ _ _ _ 68460 68469 G RIMG RIMGSH); [left; lia | lia].
      - exact SOD.
      - exact PWI.
      - exact PSI. }
    cbv beta. intros ms' PO. unfold vsnprintf_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & jd' & m' & -> & MU & WM & MI' & ST' & SSP' & DST' & Hr).
    set (out := Fmt.snprintf n fs args) in *.
    change (firstn (Z.to_nat (n - 1)) (List.concat (fmt_pieces (fmt fs) args))) with out in DST'.
    pose proof (rw_CB_length _ _ _ _ DST') as LJ. rewrite length_app, zb_length in LJ. cbn [length] in LJ.
    exists (Z_to_bv 64 (zlength (fmt_output (fmt fs) args))), m', (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')).
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; subst lo'; lia] | exact ST' | subst lo'; lia ]. }
    split; [reflexivity|].
    apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat n) _ [] [length out + 1; Z.to_nat n - length out - 1]%nat) in DST'; [| cbn; lia].
    cbn [mk_CB_cells app] in DST'.
    replace (firstn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd')) with (map b8 out ++ [Z_to_bv 8 0]) in DST'.
    2:{ rewrite firstn_app, zb_length, (firstn_all2 (zb out)) by (rewrite zb_length; lia).
        replace (length out + 1 - length out)%nat with 1%nat by lia. reflexivity. }
    rewrite (firstn_all2 (skipn (length out + 1) (zb out ++ Z_to_bv 8 0 :: jd'))) in DST' by (rewrite length_skipn, length_app, zb_length; cbn [length]; lia).
    exact DST'.
  Qed.
  End Sz9.
  Theorem snprintf_proofA : ltac:(let t := eval cbv delta [snprintf_proofA__stmt] in snprintf_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo DST n FMTA fs args junk. ltac2:(SecDiet.SzSec.closeP 'snprintf_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvkv"). Qed.
End GlueSn.
End TwB.
