(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StrerrorTable StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.     (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
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
(* [comment removed for export] *)
Local Ltac dm_plia := first [ atop_facts; once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); Z.div_mod_to_equations; lia_tiers
                            | Z.div_mod_to_equations; lia ].
(* [comment removed for export] *)
Local Ltac plia_comp := first [ once ltac2:(LiaRel.lr_prune_sub ()); lia_tiers | once ltac2:(LiaRel.lr_prune_hub 5); lia_tiers
                              | once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers ].
Local Ltac transport_call_munch_tac ::= unfold sub_fp; cbn [outside]; intros; first [ plia_comp | slia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Lemma land_m32F : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FmtErrmsg.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis VSNPRINTF : vsnprintf_spec_stmt GIOA.
  Hypothesis STRLEN : strlen_stmt GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis STRERROR : pcap_strerror_stmt GIOA.

  Lemma aobjA_sub : forall RNG (m : mem) A n A' n', aobjA RNG m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> aobjA RNG m A' n'.
  Proof using .
    intros RNG m A n A' n' (H0 & H1 & H2 & H3 & H4 & H5 & H6) HA HB Hn.
    split; [lia|]. split; [lia|]. split; [eapply unpoisoned_sub; [exact H2| lia| lia]|]. split; [eapply rng_sub; [exact H3| lia| lia]|].
    split.
    { eapply rng_sub; [exact H4| |]; rewrite ?shad_div, ?nshad_div; unfold ASHOFF; dm_plia. }
    split; [eapply arenaA_sub; [exact H5| lia| lia]| eapply ablk_sub; [exact H6| lia| lia]].
  Qed.
  Lemma cobjA_sub : forall RNG (m : mem) FL (CL : list (@cblock hptr)) A n A' n', cobjA RNG m FL CL A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> cobjA RNG m FL CL A' n'.
  Proof using .
    intros RNG m FL CL A n A' n' [LOC OBJ] HA HB Hn. split; [| eapply aobjA_sub; eassumption].
    destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]; [left; exists b | right; exists fr]; (split; [assumption|]; split; lia).
  Qed.

  Lemma robjA_sub : forall RNG (m : mem) FL (CL : list (@cblock hptr)) A n n', robjA RNG m FL CL A n -> 0 <= n' <= n -> robjA RNG m FL CL A n'.
  Proof using .
    intros RNG m FL CL A n n' [LOC OBJ] Hn. split; [| eapply mobjA_sub; [exact OBJ| lia| lia| lia]].
    destruct LOC as [[(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]|(g & Hg & G1 & G2 & G3)].
    - left; left. exists b. split; [exact Hb|]. split; [exact H1| lia].
    - left; right. exists fr. split; [exact Hf|]. split; [exact H1| lia].
    - right. exists g. split; [exact Hg|]. split; [exact G1|]. split; [lia| exact G3].
  Qed.

  (* [comment removed for export] *)
  Definition farg_word_keepx__stmt : Prop := forall L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn (m m' : mem) a w,
    farg_word false L RNG FL CL SP D dn m a w ->
    GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' -> fp_le RNG RNG' ->
    agrees_on (fun x => client_keeps FL CL SPk x /\ outside [(D, D + dn)%Z] x) m m' -> agrees_on (in_frame_sh FL) m m' ->
    mem_inv asegs m -> mem_inv asegs m' -> rng_aimg RNG' -> rng_aimg_sh RNG' -> rng_atls RNG' ->
    farg_word false L RNG' FL' CL' SP' D dn m' a w.
  Section Sz5.
  Variables L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn m m' a w : ltac2:(SecDiet.SzSec.tyM 'farg_word_keepx__stmt "vvvvvvvvvvvvvvvvvv" @L).
  Lemma farg_word_keepx__body : ltac2:(SecDiet.SzSec.bodyP 'farg_word_keepx__stmt "vvvvvvvvvvvvvvvvvv").
  Proof using GL.
    intros FW G' ICL IFL FP AG AGS MI MI' RI RS RT.
    destruct a as [z|cs]; cbn [farg_word] in *; [exact FW|].
    (nd_pre FW 4%nat; intros P bs slack ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 3%nat; intros HB NN ndR3__; nd_post; destruct ndR3__ as (-> & ndR4__); nd_pre ndR4__ 6%nat; intros LEN SLK DIS LOC OBJ RNGS; nd_post).
    exists P, bs, slack. split; [reflexivity|].
    pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
    split.
    { destruct LOC as [LC|[(g & Hg & G1 & G2 & G3 & G4)|(T0 & _)]]; [| | discriminate T0].
      - eapply agrees_bytes_at; [exact AG | exact HB |]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
        split; [eapply clocA_keeps; [exact LC| lia]| cbn [outside]; lia].
      - pose proof (client_globals_lo g Hg) as (GLO & _). eapply ro_bytes_at_any; [exact MI | exact MI' | exact HB | lia |].
        rewrite length_app. cbn [length]. lia. }
    split; [exact NN|]. split; [reflexivity|]. split; [exact LEN|]. split; [exact SLK|]. split; [exact DIS|].
    split.
    { destruct LOC as [LC|[GC|(T0 & _)]]; [left; eapply clocA_incl; eassumption | right; left; exact GC | discriminate T0]. }
    split; [| eapply rng_fp_le; eassumption].
    eapply (slocA_mobjA_keep _ _ _ GL); [exact LOC | exact OBJ | exact G' | exact ICL | exact IFL | exact AGS | exact RI | exact RS | exact RT | lia | lia].
  Qed.
  End Sz5.
  Lemma farg_word_keepx : ltac:(let t := eval cbv delta [farg_word_keepx__stmt] in farg_word_keepx__stmt in exact t).
  Proof using GL. intros L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn m m' a w. ltac2:(SecDiet.SzSec.closeP 'farg_word_keepx__body "vvvvvvvvvvvvvvvvvv"). Qed.

  Lemma farg_words_keepx : forall L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn (m m' : mem) args ws,
    Forall2 (farg_word false L RNG FL CL SP D dn m) args ws ->
    GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' -> fp_le RNG RNG' ->
    agrees_on (fun x => client_keeps FL CL SPk x /\ outside [(D, D + dn)%Z] x) m m' -> agrees_on (in_frame_sh FL) m m' ->
    mem_inv asegs m -> mem_inv asegs m' -> rng_aimg RNG' -> rng_aimg_sh RNG' -> rng_atls RNG' ->
    Forall2 (farg_word false L RNG' FL' CL' SP' D dn m') args ws.
  Proof using GL.
    intros L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn m m' args ws FW G' ICL IFL FP AG AGS MI MI' RI RS RT.
    induction FW; constructor; [eapply farg_word_keepx; eassumption| assumption].
  Qed.
  (* [comment removed for export] *)
  Lemma farg_word_tls : forall L RNG FL (CL : list (@cblock hptr)) SP D dn (m : mem) a w, farg_word false L RNG FL CL SP D dn m a w -> farg_word true L RNG FL CL SP D dn m a w.
  Proof using .
    intros L RNG FL CL SP D dn m a w FW. destruct a as [z|cs]; cbn [farg_word] in *; [exact FW|].
    (nd_pre FW 13%nat; intros P bs slack E HB NN E2 LEN SLK DIS LOC OBJ RNGS; nd_post).
    exists P, bs, slack. repeat (split; [assumption|]). split; [|split; assumption].
    destruct LOC as [LC|[GC|(T0 & _)]]; [left; exact LC| right; left; exact GC| discriminate T0].
  Qed.
  Lemma farg_words_tls : forall L RNG FL (CL : list (@cblock hptr)) SP D dn (m : mem) args ws,
    Forall2 (farg_word false L RNG FL CL SP D dn m) args ws -> Forall2 (farg_word true L RNG FL CL SP D dn m) args ws.
  Proof using . intros L RNG FL CL SP D dn m args ws FW. induction FW; constructor; [apply farg_word_tls; assumption| assumption]. Qed.

  (* [comment removed for export] *)
  Definition tls_farg__stmt : Prop := forall L RNG s (CL FB : list (@cblock hptr)) FL (m : mem) e rest D dn SP,
    GIOA L RNG s CL FB FL m -> rng_atls RNG ->
    rw_cells asegs m (ATP + PCAP_TLS_ERRBUF) [CB (length (Fmt.strerror e) + 1) (map b8 (Fmt.strerror e) ++ [Z_to_bv 8 0]); CB (255 - length (Fmt.strerror e)) rest] ->
    (D + dn <= ATP + -200 \/ ATP + -200 + 504 <= D)%Z ->
    farg_word true L RNG FL CL SP D dn m (AStr (Fmt.strerror e)) (Z_to_bv 64 (ATP + PCAP_TLS_ERRBUF)).
  Section Sz9.
  Variables L RNG s CL FB FL m e rest D dn SP : ltac2:(SecDiet.SzSec.tyM 'tls_farg__stmt "vvvvvvvvvvvv" @L).
  Lemma tls_farg__body : ltac2:(SecDiet.SzSec.bodyP 'tls_farg__stmt "vvvvvvvvvvvv").
  Proof using GL.
    intros G RT TLS DIS.
 cbn [farg_word].
    pose proof (strerror_len e) as SEL. set (se := Fmt.strerror e) in *.
    assert (LR : length rest = (255 - length se)%nat) by (destruct TLS as [[WFc _] _]; cbn [cells_wf cell_wf csize] in WFc; lia).
    exists (ATP + PCAP_TLS_ERRBUF)%Z, (map b8 se), rest.
    split; [reflexivity|].
    split. { pose proof (rw_cells_bytes_at _ _ _ _ TLS) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r, <- app_assoc in X. exact X. }
    split; [apply map_b8_no_nul; subst se; apply strerror_ok|].
    split; [symmetry; apply map_unsigned_b8; subst se; apply strerror_ok|].
    rewrite length_map, LR. unfold PCAP_TLS_ERRBUF.
    split; [lia|]. split; [clear - SEL; dm_plia|].
    split; [lia|].
    split; [right; right; split; [reflexivity| lia]|].
    split; [eapply mobjA_sub; [eapply (gl_tls _ _ _ GL); [exact G| exact RT]| lia| lia| lia]|].
    eapply rng_sub'; [exact RT| unfold ATP; lia].
  Qed.
  End Sz9.
  Lemma tls_farg : ltac:(let t := eval cbv delta [tls_farg__stmt] in tls_farg__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m e rest D dn SP. ltac2:(SecDiet.SzSec.closeP 'tls_farg__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fm_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r25 s10 s11 t3 t4 t5 t6 : word)
      (v0 v1 v2 v3 k0 k1 k2 fptr apw : word) (fj1 fj2 : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 159 <= SPA <= bv_unsigned sp - 128)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z ->
    GIOA L RNG s CL FB ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 8) (bv_unsigned sp + -120) ->
    rw_cells asegs m SPA [C8 fptr] ->
    rw_cells asegs m (bv_unsigned sp + -120) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m (bv_unsigned sp + -32) [C8 v0; C8 v1; C8 v2; C8 v3] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 8 fj1; C8 apw; CB 16 fj2; C8 (Z_to_bv 64 (fflagA L FF_FMT_ERRMSG Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_FMT_ERRMSG x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIOA L RNG s' CL FB FL m' /\ ps_outfile s' = ps_outfile s /\ ps_libc s' = ps_libc s /\ ps_tls s' = ps_tls s)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -32)) r9 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 r20 r21 r22 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r25 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x86138) fc None m (seg_rom asegs)).
  Section Sz10.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F fc L RNG s CL FB FL lo SPA Fb m ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r25 s10 s11 t3 t4 t5 t6 v0 v1 v2 v3 k0 k1 k2 fptr apw fj1 fj2 b0 b1 b2 b3 b4 b5 b6 b7 A x : ltac2:(SecDiet.SzSec.tyM 'fm_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fm_epi__body : ltac2:(SecDiet.SzSec.bodyP 'fm_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FRET GL.
 intros SPAB SPA32 LO LOS SPT TOP47 G MI ST STG FRA FRs FRv FRC SHC RSTK.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND FTOP F64 _ FRNG FSRNG _ _; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 64 3) with 8%Z in FSRNG.
    (pose proof (ablk_lin _ _ FBAND) as ndP__; nd_pre ndP__ 4%nat; intros _ Fb0 _ _; nd_post). band_ind FBAND bF.
    (nd_pre (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) 6%nat; intros _ FLR FLB FLT _ (kF & kFr & kF1 & kF2); nd_post). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; dm_plia).
    assert (FW : Forall (own_ivA [(FF_FMT_ERRMSG, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    pose proof (munch_refl [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    burst_begin [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z [Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    zstep. neg_lits.
    zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    do 4 zstep. zstep_sh0. do 3 zstep.
    burst_end MUb WMb.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FW (Forall_nil _) G' MU WM ltac:(lia)) as [G5 AG5];
      pose proof (munch_refl [(fflagA L FF_FMT_ERRMSG Fb, fflagA L FF_FMT_ERRMSG Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    rewrite app_nil_r in G5.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 14 zstep.
    release_frame FRA ST (SPA + 8)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    pose proof (rw_cells_uncut _ _ _ _ _ FRs FRv ltac:(cbn; lia)) as FR. cbn [app] in FR. clear FRs FRv.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CL (bv_unsigned sp) G5 MU2 WM2 (incl_refl _) ltac:(lia)) as [AG6 _].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 15 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split; [exact G6|]. split; [exact OF3|]. split; [exact LC3| exact TL3].
  Qed.
  End Sz10.
  Lemma fm_epi : ltac:(let t := eval cbv delta [fm_epi__stmt] in fm_epi__stmt in exact t).
  Proof using FRET GL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F fc L RNG s CL FB FL lo SPA Fb m ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r25 s10 s11 t3 t4 t5 t6 v0 v1 v2 v3 k0 k1 k2 fptr apw fj1 fj2 b0 b1 b2 b3 b4 b5 b6 b7 A x. ltac2:(SecDiet.SzSec.closeP 'fm_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fmt_errmsg_proofA__stmt : Prop := fmt_errmsg_stmt FO GIOA.
  Section Sz11.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo EB FMTA e fs args junk : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fmt_errmsg_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FENTER0 FRET GL SNPRINTF STRERROR STRLEN VSNPRINTF.
 intros PRE NF -> -> -> HE -> FMT5 FOK LA FW HEB OEB E8.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    unfold PCAP_L1_STACK in BU.
    pose proof (farg_words_ok _ _ _ _ _ _ _ _ _ _ _ FW) as AOK.
    pose proof (fmt_ok_items_okb _ _ FOK) as IOK.
    set (out := Fmt.snprintf 256 fs args). set (len := length out).
    pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LENB. fold out len in LENB.
    pose proof (snprintf_ok 256 fs args IOK AOK) as OUTOK. fold out in OUTOK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rng_sp_window RSTK sp RSPW.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    pose proof (proj1 OEB) as EBL.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL ltac:(lia)) as EBBAND. pose proof EBBAND as EBBAND'. band_ind EBBAND bE.
    remember (bv_unsigned sp - 128 - (bv_unsigned sp - 128) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 159 <= SPA <= bv_unsigned sp - 128 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -128) - (bv_unsigned sp + -128) mod 32 = SPA)%Z)
      by (rewrite ESPA; dm_plia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    assert (MIe : hidc (mem_inv asegs m)) by exact MI.
    unfold PCAP_FMT_ERRMSG_ENTRY.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 120%nat ST. carve_frame 8%nat ST.
    zstep.
    do 11 zstep.
    zstep.
    zstep.
    rewrite land_m32F by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -120)%Z.
    destruct (stk_split asegs _ lo (SPA + 8) (bv_unsigned sp + -120) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 8) 8 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 8) with 8%Z in STL, FRA. replace (SPA + 8 - 8)%Z with SPA in STL, FRA by lia.
    do 5 zstep.
    do 4 zstep.
    zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    do 4 zstep.
    zstep. if_false.
    do 2 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FWS : Forall (client_ivA FL CL) [(bv_unsigned sp - 160, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp - 160, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho])
    end.
    rename MU into MU0. rename WM into WM0. clear FWS G'.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER0 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [dm_plia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { exact NF. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_FMT_ERRMSG) with 64%Z in *.
    change (Z.to_nat (64 - 32)) with 32%nat in *. change (Z.to_nat (64 / 8)) with 8%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 548868)) with (Z_to_bv 64 548868) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND' FTOP' F64 _ FRNG FSRNG _ FSWR; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HEB; [|intros a Ha; eapply clocA_keeps; [exact EBL| exact Ha]].
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 EBL ltac:(lia)) 4%nat; intros kE kEr kE1 kE2; nd_post).
    cbn [fb_addr fb_size fst snd] in kE1, kE2.
    assert (AGb : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; dm_plia).
    pose proof (munch_refl [(bv_unsigned sp - 28672, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8); (EB, EB + 256)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    burst_begin [(SPA, SPA + 8); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z [SPA; Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 11 zstep.
    zstep. neg_lits.
    zstep.
    do 4 zstep.
    zstep. neg_lits.
    zstep_sh0.
    do 3 zstep.
    do 2 zstep.
    burst_end MUb WMb.
    do 4 zstep.
    zstep.
    (* [comment removed for export] *)
    clear GOT SHB SUA GSU.
    pose proof G1 as G1'. rewrite <- (app_nil_r CL) in G1'.
    assert (FWo : Forall (own_ivA [(FF_FMT_ERRMSG, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 28672, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    assert (FX : Forall (cobj_iv FL CL) [(EB, EB + 256)]%Z) by cobj_ivs.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(EB, EB + 256)]%Z) by (apply Forall_cons; [exact EBBAND'| apply Forall_nil]).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWo FX G1' MU WM ltac:(lia)) as [G2 AG2];
      assert (AGsh : agrees_on (in_frame_sh FL) m mm)
        by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG2 FXB));
      assert (AGx : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m mm)
        by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb| intros x [Hx _]; exact Hx]| exact AG2])
    end.
    rewrite app_nil_r in G2.
    unfold hidc in MIe.
    assert (FMT0 : fmt_at m0 FMTA fs) by (eapply fmt_at_keep; [exact FMT5 | exact MIe | exact MI1]).
    assert (FW0 : Forall2 (farg_word true L RNG ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL SPA EB 256 m0) args (firstn (length args) [a4])).
    { apply farg_words_tls. eapply farg_words_keepx; [exact FW | exact G2 | apply incl_refl | apply incl_tl; apply incl_refl | apply fp_le_refl
                                                     | exact AGx | exact AGsh | exact MIe | exact MI1 | exact RIMG | exact RISH | exact RTLS]. }
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G2 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as OEB2.
    assert (OEB3 : cobjA RNG m0 ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL EB 256)
      by (split; [eapply clocA_incl; [exact (proj1 OEB2)| apply incl_refl| apply incl_tl; apply incl_refl]| exact (proj2 OEB2)]).
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 11 FR) as [FRs FRv]. cbn [firstn skipn cells_size csize Nat.add] in FRs, FRv.
    replace (bv_unsigned sp + -120 + Z.of_nat 88)%Z with (bv_unsigned sp + -32)%Z in FRv by lia.
    destruct args as [|x1 [|x2 args2]]; [ | | cbn [length] in LA; exfalso; lia].
    all: cbn [length firstn] in FW0.
    1: destruct (rw_cells_cut _ _ _ 0 FRv) as [AP0 _]; cbn [firstn skipn cells_size csize Nat.add] in AP0.
    2: destruct (rw_cells_cut _ _ _ 1 FRv) as [AP0 _]; cbn [firstn skipn cells_size csize Nat.add] in AP0.
    all: remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    all: assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    all: lazymatch type of FW0 with Forall2 _ ?xargs ?xws => eapply evtF_cut;
           [ eapply VSNPRINTF with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_FMT_ERRMSG, Fb, 64%Z) :: FL) (lo := lo) (DST := EB) (n := 256%Z)
                                   (FMTA := FMTA) (AP := (bv_unsigned sp + -32)%Z) (fs := fs) (args := xargs) (ws := xws) (junk := junk);
             [ split; [exact G2|]; rewrite Hspa; split; [exact ST1|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
               split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
               split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
             | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact FMT0 | exact FOK
             | reflexivity | cbn [length]; lia | rewrite Hspa; exact FW0
             | first [exact AP0 | cbn [map]; exact AP0] | rewrite Hspa; lia | cbn [length]; lia | cbn [length]; lia | exact HEB | exact OEB3 ]
           | ] end.
    all: cbv beta; intros ms' PO; (nd_pre PO 9%nat; intros vav mv vjk E MU1 WM1 MIv STv ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into HD1);
         unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
    all: replace (ret_pc (Z_to_bv 64 549040)) with (Z_to_bv 64 549040) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unfold STDIO_STACK in MU1; clear G2 AG2 AGsh AGx FW0 FMT0 OEB2 OEB3 AP0.
    all: transport_after_call asegs m0 mv MU1 WM1; clear MU1 WM1 MI1.
    all: change (Z.to_nat 256) with 256%nat in HD1; fold out in HD1; fold len in HD1.
    all: assert (LJ1 : length vjk = (255 - len)%nat)
           by (destruct HD1 as [[WFc _] _]; cbn [cells_wf cell_wf csize] in WFc; rewrite length_app, length_map in WFc; cbn [length] in WFc; lia).
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWo FX G1' MU WM ltac:(lia)) as [G3 AG3];
           assert (AGsh : agrees_on (in_frame_sh FL) m mm)
             by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG3 FXB))
         end.
    all: rewrite app_nil_r in G3.
    all: pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G3 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as OEB2.
    all: assert (OEB3 : cobjA RNG mv ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL EB 256)
           by (split; [eapply clocA_incl; [exact (proj1 OEB2)| apply incl_refl| apply incl_tl; apply incl_refl]| exact (proj2 OEB2)]).
    all: do 2 zstep.
    all: remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    all: assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    all: eapply evtF_cut;
           [ eapply STRLEN with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_FMT_ERRMSG, Fb, 64%Z) :: FL) (lo := lo) (P := EB) (bs := map b8 out) (slack := vjk);
             [ split; [exact G3|]; rewrite Hspa; split; [exact STv|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
               split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
               split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
             | reflexivity
             | pose proof (rw_cells_bytes_at _ _ _ _ HD1) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r, <- app_assoc in X; exact X
             | apply map_b8_no_nul; exact OUTOK
             | rewrite length_map; fold len; lia
             | rewrite length_map, LJ1; fold len; clear - E8 LENB; dm_plia
             | rewrite length_map; fold len; eapply robjA_sub; [apply cobjA_robjA; [exact OEB3| lia]| lia]
             | rewrite length_map, LJ1; fold len; replace (Z.of_nat len + 1 + Z.of_nat (255 - len))%Z with 256%Z by lia; destruct OEB3 as [_ (_ & _ & _ & R & _)]; exact R ]
           | ].
    all: cbv beta; intros ms' PO; (nd_pre PO 8%nat; intros vav2 mw E MU2 WM2 MIw STw ndR1__; nd_post; revert ndR1__; intros ->);
         unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
    all: replace (ret_pc (Z_to_bv 64 549048)) with (Z_to_bv 64 549048) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unfold STDIO_STACK in MU2; clear G3 AG3 AGsh OEB2 OEB3.
    all: transport_after_call asegs mv mw MU2 WM2; clear MU2 WM2 MIv.
    all: rewrite length_map; fold len.
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWo FX G1' MU WM ltac:(lia)) as [G4 AG4];
           assert (AGsh : agrees_on (in_frame_sh FL) m mm)
             by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG4 FXB));
           assert (AGx : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m mm)
             by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb| intros aa [Haa _]; exact Haa]| exact AG4])
         end.
    all: rewrite app_nil_r in G4.
    all: do 2 zstep.
    all: if_cases Kr; zify_cond Kr.
    (* [comment removed for export] *)
    1,3: apply evtF_done; eapply implMG_mono;
           [ eapply fm_epi with (L := L) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (SPA := SPA) (Fb := Fb);
             [ lia | exact SPA32 | lia | lia | lia | lia | exact G4 | assumption | exact STw | exact STG | exact FRA | exact FRs | exact FRv | exact FRC | exact SHC | exact RSTK ]
           | ].
    1,2: cbv beta; intros r s5' RNG5 ms5 PO; (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); rename ndR2__ into PO); destruct_exs PO;
         (destruct PO as (-> & ndR1__); nd_pre ndR1__ 7%nat; intros MI5 ST5 AG5 G5 OF5 LC5 TL5; nd_post).
    1,2: subst POSTQ0 POSTQ; cbv beta; split; [apply fp_le_refl|]; split; [reflexivity|].
    1,2: do 15 eexists; lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end; exists vjk.
    1,2: split; [reflexivity|]; split; [congruence|]; split; [congruence|]; split; [congruence|];
         split; [exact MI5|]; split; [exact ST5|].
    1,2: split; [eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGx| intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]
                                        | eapply agrees_on_weaken; [exact AG5| intros a [K _]; exact K]]|].
    1,2: split; [exact G5|].
    1,2: unfold fmt_errmsg, PCAP_ERRBUF_SIZE; fold out; unfold zlength; fold len;
         replace (256 <? Z.of_nat len + 3) with true by (symmetry; apply Z.ltb_lt; lia);
         replace (255 - length out)%nat with (256 - len - 1)%nat by (subst len; lia);
         eapply agrees_rw_cells; [exact AG5 | exact HD1 |]; intros a Ha; eapply clocA_keeps; [exact EBL|];
         cbn [cells_size csize Nat.add] in Ha; lia.
    (* [comment removed for export] *)
    all: assert (L2 : (2 <= length vjk)%nat) by lia.
    all: destruct vjk as [|jb0 [|jb1 jrest]]; try (exfalso; cbn [length] in L2; lia); cbn [length] in LJ1.
    all: assert (HD5 : rw_cells asegs mw EB [CB len (map b8 out); CB 1 [Z_to_bv 8 0]; CB 1 [jb0]; CB 1 [jb1]; CB (253 - len) jrest])
           by (eapply rw_cells_recell; [exact HD1 | cbn; rewrite length_map; repeat split; try reflexivity; lia | cbn [cells_bytes cbytes]; rewrite <- !app_assoc, !app_nil_r; reflexivity]);
         clear HD1.
    all: destruct (rw_cells_cut _ _ _ 1 HD5) as [HDo HDr]; clear HD5; cbn [firstn skipn cells_size csize Nat.add] in HDo, HDr; rewrite Nat.add_0_r in HDr.
    all: destruct (rw_cells_cut _ _ _ 3 HDr) as [HD3 HDrest]; clear HDr; cbn [firstn skipn cells_size csize Nat.add] in HD3, HDrest.
    all: pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G4 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as (_ & (_ & _ & EUNP & ERNG & ERSH & _)).
    all: replace (EB - EB mod 8)%Z with EB in ERSH by lia; replace (256 + EB mod 8)%Z with 256%Z in ERSH by lia.
    all: zstep.
    all: remember (EB + Z.of_nat len)%Z as Q eqn:HQ in *.
    all: replace (Q + Z.of_nat 3)%Z with (Q + 3)%Z in HDrest by lia.
    all: assert (RQ : rng RNG Q 3) by (eapply rng_sub'; [exact ERNG| lia]).
    all: ck0 EUNP; ck_go.
    all: do 3 zstep.
    all: ck0 EUNP; ck_go.
    all: do 3 zstep.
    all: ck0 EUNP; ck_go.
    all: do 4 zstep.
    all: zstep.
    (* [comment removed for export] *)
    all: clear G4 AG4 AGsh AGx.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWo FX G1' MU WM ltac:(lia)) as [G6 AG6];
           assert (AGsh6 : agrees_on (in_frame_sh FL) m mm)
             by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG6 FXB));
           assert (AGx6 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(EB, EB + 256)%Z] a) m mm)
             by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb| intros aa [Haa _]; exact Haa]| exact AG6])
         end.
    all: rewrite app_nil_r in G6.
    all: assert (EBL' : clocA ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL EB 256) by (eapply clocA_incl; [exact EBL| apply incl_refl| apply incl_tl; apply incl_refl]).
    all: remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    all: assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    all: eapply evtF_cut;
           [ eapply STRERROR with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_FMT_ERRMSG, Fb, 64%Z) :: FL) (lo := lo) (e := e);
             [ split; [exact G6|]; rewrite Hspa; split; [exact STw|]; split; [lia|]; split; [unfold PCAP_L0_STACK; lia|]; split; [lia|];
               split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
               split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
             | reflexivity | exact HE ]
           | ].
    all: cbv beta; intros ms' PO; destruct_exs PO; (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MI7 ST7 AG7 G7 TLS7; nd_post); rewrite Hspa in *; clear Hspa; subst spa.
    all: replace (ret_pc (Z_to_bv 64 549152)) with (Z_to_bv 64 549152) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG7) in FRs; [|lia]; apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG7) in FRv; [|lia];
         apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG7) in FRA; [|lia].
    all: apply (agrees_stk _ _ _ _ _ AG7) in STG; [|intros a Ha; left; lia].
    all: assert (FRIN : forall a, (Fb <= a < Fb + 64)%Z -> in_frames ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) a)
           by (intros a Ha; apply in_frames_In; exists (FF_FMT_ERRMSG, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    all: assert (SHIN : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> in_frame_sh ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) a)
           by (intros a Ha; apply in_frame_sh_In; exists (FF_FMT_ERRMSG, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 64 3) with 8%Z; lia]).
    all: apply (keeps_rw_cells_frame _ _ _ _ _ _ _ AG7) in FRC; [|intros a Ha; apply FRIN; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (keeps_rw_cells_frame_sh _ _ _ _ _ _ _ AG7) in SHC; [|intros a Ha; apply SHIN; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG7) in HDo; [|intros a Ha; eapply clocA_keeps; [exact EBL'|]; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG7) in HD3; [|intros a Ha; eapply clocA_keeps; [exact EBL'|]; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG7) in HDrest; [|intros a Ha; eapply clocA_keeps; [exact EBL'|]; cbn [cells_size csize Nat.add] in Ha; lia].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           assert (AGx7 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(EB, EB + 256)%Z] a) m mm)
             by (eapply agrees_on_trans; [exact AGx6|]; eapply agrees_on_weaken; [exact AG7|]; intros a [K _];
                 destruct K as [K|[K|[K|K]]]; [left; lia | right; left; exact K | right; right; left; apply in_frames_cons; exact K
                                              | right; right; right; apply in_frame_sh_cons; exact K]);
           assert (AGsh7 : agrees_on (in_frame_sh FL) m mm)
             by (eapply agrees_on_trans; [exact AGsh6|]; eapply agrees_on_weaken; [exact AG7|]; intros a K; right; right; right; apply in_frame_sh_cons; exact K)
         end.
    (* [comment removed for export] *)
    all: pose proof (strerror_len e) as SEL; set (se := Fmt.strerror e) in *.
    all: lazymatch type of TLS7 with rw_cells _ _ _ [_; CB _ ?r] => rename r into rest end.
    all: assert (LR : length rest = (255 - length se)%nat) by (destruct TLS7 as [[WFc _] _]; cbn [cells_wf cell_wf csize] in WFc; lia).
    all: clear MU WM G6 AG6 AGsh6 AGx6.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           pose proof (munch_refl [(bv_unsigned sp - 28672, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8); (EB, EB + 256)]%Z mm) as MU;
           pose proof (wmono_refl asegs mm) as WM;
           assert (MSG : fmt_at mm 0x217a0 "%s"%string)
             by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x217a0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "%s"%string) ++ [Z_to_bv 8 0])
                                     MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
                 split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]))
         end.
    all: pose proof G7 as G7'; rewrite <- (app_nil_r CL) in G7'.
    all: do 5 zstep.
    all: zstep.
    (* [comment removed for export] *)
    all: destruct (rw_cells_cut _ _ _ 2 HD3) as [HC2 HZ]; clear HD3; cbn [firstn skipn cells_size csize Nat.add] in HC2, HZ.
    all: pose proof (rw_cells_uncut _ _ _ _ _ HZ HDrest ltac:(cbn; lia)) as HDST0; clear HZ HDrest.
    all: lazymatch type of HDST0 with rw_cells _ ?mm _ _ =>
           pose proof (rw_cells_merge asegs mm _ [] _ [] ltac:(rewrite app_nil_r; exact HDST0)) as HDST end; clear HDST0;
         cbn [app cells_size csize cells_bytes cbytes Nat.add] in HDST.
    all: replace (Q + Z.of_nat 2)%Z with (Q + 2)%Z in HDST by lia.
    all: replace (S (253 - len + 0)) with (Z.to_nat (254 - Z.of_nat len)) in HDST by lia.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           assert (FWS : Forall2 (farg_word true L RNG ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL SPA (Q + 2) (254 - Z.of_nat len) mm) [AStr se] [Z_to_bv 64 (ATP + PCAP_TLS_ERRBUF)])
             by (constructor; [| constructor]; eapply tls_farg; [exact G7 | exact RTLS | exact TLS7 |];
                 destruct (clocA_apart_tls _ _ _ GL _ _ _ _ _ _ _ _ _ G7 EBL' ltac:(lia)) as [T|T]; [left; lia | right; lia]);
           pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G7 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh7 ltac:(lia)) as OEB7;
           assert (ODST : cobjA RNG mm ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL (Q + 2) (254 - Z.of_nat len))
             by (eapply cobjA_sub; [split; [exact EBL'| exact (proj2 OEB7)] | lia | lia | lia])
         end.
    all: remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    all: assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    all: eapply evtF_cut;
           [ eapply SNPRINTF with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_FMT_ERRMSG, Fb, 64%Z) :: FL) (lo := lo) (DST := (Q + 2)%Z) (n := (254 - Z.of_nat len)%Z)
                                  (FMTA := 0x217a0%Z) (fs := "%s"%string) (args := [AStr se]) (junk := (Z_to_bv 8 0 :: jrest ++ []));
             [ split; [exact G7|]; rewrite Hspa; split; [exact ST7|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
               split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
               split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
             | reflexivity | first [reflexivity | f_equal; lia] | reflexivity | lia | exact MSG | reflexivity | cbn; lia
             | cbn [length firstn]; rewrite Hspa; exact FWS | exact HDST | exact ODST ]
           | ].
    all: cbv beta; intros ms' PO; (nd_pre PO 9%nat; intros vav5 m9 junk5 E MU5 WM5 MI9 ST9 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into HD2);
         unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
    all: replace (ret_pc (Z_to_bv 64 549176)) with (Z_to_bv 64 549176) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unfold STDIO_STACK in MU5; clear FWS MSG OEB7 ODST HDST.
    all: lazymatch type of MU5 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU5 WM5 end; clear MU5 WM5 MI7.
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWo FX G7' MU WM ltac:(lia)) as [G9 AG9] end.
    all: rewrite app_nil_r in G9.
    all: apply evtF_done; eapply implMG_mono;
           [ eapply fm_epi with (L := L) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (SPA := SPA) (Fb := Fb);
             [ lia | exact SPA32 | lia | lia | lia | lia | exact G9 | assumption | exact ST9 | exact STG | exact FRA | exact FRs | exact FRv | exact FRC | exact SHC | exact RSTK ]
           | ].
    all: cbv beta; intros r s5' RNG5 ms5 PO; (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); rename ndR2__ into PO); destruct_exs PO;
         (destruct PO as (-> & ndR1__); nd_pre ndR1__ 7%nat; intros MI5 ST5 AG5 G5 OF5 LC5 TL5; nd_post).
    all: subst POSTQ0 POSTQ; cbv beta; split; [apply fp_le_refl|]; split; [reflexivity|].
    all: do 15 eexists; lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end; exists junk5.
    all: split; [reflexivity|]; split; [congruence|]; split; [congruence|]; split; [congruence|];
         split; [exact MI5|]; split; [exact ST5|].
    all: split; [eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGx7| intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]|];
                 eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG9| intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]
                                         | eapply agrees_on_weaken; [exact AG5| intros a [K _]; exact K]]|].
    all: split; [exact G5|].
    (* [comment removed for export] *)
    all: set (out2 := Fmt.snprintf (254 - Z.of_nat len) "%s" [AStr se]) in *.
    all: pose proof (snprintf_length_le (254 - Z.of_nat len) "%s" [AStr se] ltac:(lia)) as L2B; fold out2 in L2B.
    all: assert (LJ5 : length junk5 = (253 - len - length out2)%nat)
           by (destruct HD2 as [[WFc _] _]; cbn [cells_wf cell_wf csize] in WFc; rewrite length_app, length_map in WFc; cbn [length] in WFc; lia).
    all: lazymatch goal with |- context [fmt_errmsg ?ff ?ar ?ee] =>
           assert (EFM : fmt_errmsg ff ar ee = out ++ [58; 32]%Z ++ out2)
             by (unfold fmt_errmsg, PCAP_ERRBUF_SIZE; fold out; unfold zlength;
                 replace (256 <? Z.of_nat (length out) + 3) with false by (symmetry; apply Z.ltb_ge; subst len; lia);
                 unfold strerror_r; fold se; unfold zlength; replace (Z.of_nat (length se) <? 256) with true by (symmetry; apply Z.ltb_lt; lia); cbn [snd];
                 replace (256 - Z.of_nat (length out) - 2)%Z with (254 - Z.of_nat len)%Z by (subst len; lia); reflexivity)
         end.
    all: rewrite EFM; rewrite !length_app; cbn [length].
    all: assert (EBK : forall a, (EB <= a < EB + 256)%Z -> client_keeps FL CL (bv_unsigned sp) a) by (intros a Ha; eapply clocA_keeps; [exact EBL| exact Ha]).
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in HDo; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in HC2; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in HD2; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; lia].
    all: pose proof (rw_cells_uncut _ _ _ _ _ HDo HC2 ltac:(cbn; lia)) as J1.
    all: pose proof (rw_cells_uncut _ _ _ _ _ J1 HD2 ltac:(cbn; lia)) as J2.
    all: eapply rw_cells_recell; [exact J2 | | ].
    2,4: cbn [cells_bytes cbytes app map]; rewrite !map_app; cbn [map app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
    all: cbn [cells_wf cell_wf csize]; rewrite !length_app, !length_map, !length_app; cbn [length]; repeat split; lia.
  Qed.
  End Sz11.
  Theorem fmt_errmsg_proofA : ltac:(let t := eval cbv delta [fmt_errmsg_proofA__stmt] in fmt_errmsg_proofA__stmt in exact t).
  Proof using FENTER0 FRET GL SNPRINTF STRERROR STRLEN VSNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo EB FMTA e fs args junk. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FmtErrmsg.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StrerrorTable OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.     (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
(* [comment removed for export] *)
Local Ltac dm_plia := first [ atop_facts; once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); Z.div_mod_to_equations; lia_tiers
                            | Z.div_mod_to_equations; lia ].
(* [comment removed for export] *)
Local Ltac plia_comp := first [ once ltac2:(LiaRel.lr_prune_sub ()); lia_tiers | once ltac2:(LiaRel.lr_prune_hub 5); lia_tiers
                              | once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers ].
Local Ltac transport_call_munch_tac ::= unfold sub_fp; cbn [outside]; intros; first [ plia_comp | slia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Lemma land_m32F : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FmtErrmsg.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis VSNPRINTF : vsnprintf_spec_stmt GIOA.
  Hypothesis STRLEN : strlen_stmt GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis STRERROR : pcap_strerror_stmt GIOA.

  Lemma aobjA_sub : forall RNG (m : mem) A n A' n', aobjA RNG m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> aobjA RNG m A' n'.
  Proof using .
    intros RNG m A n A' n' (H0 & H1 & H2 & H3 & H4 & H5 & H6) HA HB Hn.
    split; [lia|]. split; [lia|]. split; [eapply unpoisoned_sub; [exact H2| lia| lia]|]. split; [eapply rng_sub; [exact H3| lia| lia]|].
    split.
    { eapply rng_sub; [exact H4| |]; rewrite ?shad_div, ?nshad_div; unfold ASHOFF; dm_plia. }
    split; [eapply arenaA_sub; [exact H5| lia| lia]| eapply ablk_sub; [exact H6| lia| lia]].
  Qed.
  Lemma cobjA_sub : forall RNG (m : mem) FL (CL : list (@cblock hptr)) A n A' n', cobjA RNG m FL CL A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> cobjA RNG m FL CL A' n'.
  Proof using .
    intros RNG m FL CL A n A' n' [LOC OBJ] HA HB Hn. split; [| eapply aobjA_sub; eassumption].
    destruct LOC as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]; [left; exists b | right; exists fr]; (split; [assumption|]; split; lia).
  Qed.

  Lemma robjA_sub : forall RNG (m : mem) FL (CL : list (@cblock hptr)) A n n', robjA RNG m FL CL A n -> 0 <= n' <= n -> robjA RNG m FL CL A n'.
  Proof using .
    intros RNG m FL CL A n n' [LOC OBJ] Hn. split; [| eapply mobjA_sub; [exact OBJ| lia| lia| lia]].
    destruct LOC as [[(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]|(g & Hg & G1 & G2 & G3)].
    - left; left. exists b. split; [exact Hb|]. split; [exact H1| lia].
    - left; right. exists fr. split; [exact Hf|]. split; [exact H1| lia].
    - right. exists g. split; [exact Hg|]. split; [exact G1|]. split; [lia| exact G3].
  Qed.

  (* [comment removed for export] *)
  Definition farg_word_keepx__stmt : Prop := forall L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn (m m' : mem) a w,
    farg_word false L RNG FL CL SP D dn m a w ->
    GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' -> fp_le RNG RNG' ->
    agrees_on (fun x => client_keeps FL CL SPk x /\ outside [(D, D + dn)%Z] x) m m' -> agrees_on (in_frame_sh FL) m m' ->
    mem_inv asegs m -> mem_inv asegs m' -> rng_aimg RNG' -> rng_aimg_sh RNG' -> rng_atls RNG' ->
    farg_word false L RNG' FL' CL' SP' D dn m' a w.
  Section Sz5.
  Variables L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn m m' a w : ltac2:(SecDiet.SzSec.tyM 'farg_word_keepx__stmt "vvvvvvvvvvvvvvvvvv" @L).
  Lemma farg_word_keepx__body : ltac2:(SecDiet.SzSec.bodyP 'farg_word_keepx__stmt "vvvvvvvvvvvvvvvvvv").
  Proof using GL.
    intros FW G' ICL IFL FP AG AGS MI MI' RI RS RT.
    destruct a as [z|cs]; cbn [farg_word] in *; [exact FW|].
    (nd_pre FW 4%nat; intros P bs slack ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 3%nat; intros HB NN ndR3__; nd_post; destruct ndR3__ as (-> & ndR4__); nd_pre ndR4__ 6%nat; intros LEN SLK DIS LOC OBJ RNGS; nd_post).
    exists P, bs, slack. split; [reflexivity|].
    pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
    split.
    { destruct LOC as [LC|[(g & Hg & G1 & G2 & G3 & G4)|(T0 & _)]]; [| | discriminate T0].
      - eapply agrees_bytes_at; [exact AG | exact HB |]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
        split; [eapply clocA_keeps; [exact LC| lia]| cbn [outside]; lia].
      - pose proof (client_globals_lo g Hg) as (GLO & _). eapply ro_bytes_at_any; [exact MI | exact MI' | exact HB | lia |].
        rewrite length_app. cbn [length]. lia. }
    split; [exact NN|]. split; [reflexivity|]. split; [exact LEN|]. split; [exact SLK|]. split; [exact DIS|].
    split.
    { destruct LOC as [LC|[GC|(T0 & _)]]; [left; eapply clocA_incl; eassumption | right; left; exact GC | discriminate T0]. }
    split; [| eapply rng_fp_le; eassumption].
    eapply (slocA_mobjA_keep _ _ _ GL); [exact LOC | exact OBJ | exact G' | exact ICL | exact IFL | exact AGS | exact RI | exact RS | exact RT | lia | lia].
  Qed.
  End Sz5.
  Lemma farg_word_keepx : ltac:(let t := eval cbv delta [farg_word_keepx__stmt] in farg_word_keepx__stmt in exact t).
  Proof using GL. intros L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn m m' a w. ltac2:(SecDiet.SzSec.closeP 'farg_word_keepx__body "vvvvvvvvvvvvvvvvvv"). Qed.

  Lemma farg_words_keepx : forall L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn (m m' : mem) args ws,
    Forall2 (farg_word false L RNG FL CL SP D dn m) args ws ->
    GIOA L RNG' s' CL' FB' FL' m' -> incl CL CL' -> incl FL FL' -> fp_le RNG RNG' ->
    agrees_on (fun x => client_keeps FL CL SPk x /\ outside [(D, D + dn)%Z] x) m m' -> agrees_on (in_frame_sh FL) m m' ->
    mem_inv asegs m -> mem_inv asegs m' -> rng_aimg RNG' -> rng_aimg_sh RNG' -> rng_atls RNG' ->
    Forall2 (farg_word false L RNG' FL' CL' SP' D dn m') args ws.
  Proof using GL.
    intros L RNG RNG' s' CL CL' FB' FL FL' SPk SP SP' D dn m m' args ws FW G' ICL IFL FP AG AGS MI MI' RI RS RT.
    induction FW; constructor; [eapply farg_word_keepx; eassumption| assumption].
  Qed.
  (* [comment removed for export] *)
  Lemma farg_word_tls : forall L RNG FL (CL : list (@cblock hptr)) SP D dn (m : mem) a w, farg_word false L RNG FL CL SP D dn m a w -> farg_word true L RNG FL CL SP D dn m a w.
  Proof using .
    intros L RNG FL CL SP D dn m a w FW. destruct a as [z|cs]; cbn [farg_word] in *; [exact FW|].
    (nd_pre FW 13%nat; intros P bs slack E HB NN E2 LEN SLK DIS LOC OBJ RNGS; nd_post).
    exists P, bs, slack. repeat (split; [assumption|]). split; [|split; assumption].
    destruct LOC as [LC|[GC|(T0 & _)]]; [left; exact LC| right; left; exact GC| discriminate T0].
  Qed.
  Lemma farg_words_tls : forall L RNG FL (CL : list (@cblock hptr)) SP D dn (m : mem) args ws,
    Forall2 (farg_word false L RNG FL CL SP D dn m) args ws -> Forall2 (farg_word true L RNG FL CL SP D dn m) args ws.
  Proof using . intros L RNG FL CL SP D dn m args ws FW. induction FW; constructor; [apply farg_word_tls; assumption| assumption]. Qed.

  (* [comment removed for export] *)
  Definition tls_farg__stmt : Prop := forall L RNG s (CL FB : list (@cblock hptr)) FL (m : mem) e rest D dn SP,
    GIOA L RNG s CL FB FL m -> rng_atls RNG ->
    rw_cells asegs m (ATP + PCAP_TLS_ERRBUF) [CB (length (Fmt.strerror e) + 1) (map b8 (Fmt.strerror e) ++ [Z_to_bv 8 0]); CB (255 - length (Fmt.strerror e)) rest] ->
    (D + dn <= ATP + -200 \/ ATP + -200 + 504 <= D)%Z ->
    farg_word true L RNG FL CL SP D dn m (AStr (Fmt.strerror e)) (Z_to_bv 64 (ATP + PCAP_TLS_ERRBUF)).
  Section Sz9.
  Variables L RNG s CL FB FL m e rest D dn SP : ltac2:(SecDiet.SzSec.tyM 'tls_farg__stmt "vvvvvvvvvvvv" @L).
  Lemma tls_farg__body : ltac2:(SecDiet.SzSec.bodyP 'tls_farg__stmt "vvvvvvvvvvvv").
  Proof using GL.
    intros G RT TLS DIS.
 cbn [farg_word].
    pose proof (strerror_len e) as SEL. set (se := Fmt.strerror e) in *.
    assert (LR : length rest = (255 - length se)%nat) by (destruct TLS as [[WFc _] _]; cbn [cells_wf cell_wf csize] in WFc; lia).
    exists (ATP + PCAP_TLS_ERRBUF)%Z, (map b8 se), rest.
    split; [reflexivity|].
    split. { pose proof (rw_cells_bytes_at _ _ _ _ TLS) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r, <- app_assoc in X. exact X. }
    split; [apply map_b8_no_nul; subst se; apply strerror_ok|].
    split; [symmetry; apply map_unsigned_b8; subst se; apply strerror_ok|].
    rewrite length_map, LR. unfold PCAP_TLS_ERRBUF.
    split; [lia|]. split; [clear - SEL; dm_plia|].
    split; [lia|].
    split; [right; right; split; [reflexivity| lia]|].
    split; [eapply mobjA_sub; [eapply (gl_tls _ _ _ GL); [exact G| exact RT]| lia| lia| lia]|].
    eapply rng_sub'; [exact RT| unfold ATP; lia].
  Qed.
  End Sz9.
  Lemma tls_farg : ltac:(let t := eval cbv delta [tls_farg__stmt] in tls_farg__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m e rest D dn SP. ltac2:(SecDiet.SzSec.closeP 'tls_farg__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fm_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r25 s10 s11 t3 t4 t5 t6 : word)
      (v0 v1 v2 v3 k0 k1 k2 fptr apw : word) (fj1 fj2 : list byte) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 159 <= SPA <= bv_unsigned sp - 128)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z ->
    GIOA L RNG s CL FB ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 8) (bv_unsigned sp + -120) ->
    rw_cells asegs m SPA [C8 fptr] ->
    rw_cells asegs m (bv_unsigned sp + -120) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m (bv_unsigned sp + -32) [C8 v0; C8 v1; C8 v2; C8 v3] ->
    rw_cells asegs m Fb [C8 k0; C8 k1; C8 k2; CB 8 fj1; C8 apw; CB 16 fj2; C8 (Z_to_bv 64 (fflagA L FF_FMT_ERRMSG Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_FMT_ERRMSG x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIOA L RNG s' CL FB FL m' /\ ps_outfile s' = ps_outfile s /\ ps_libc s' = ps_libc s /\ ps_tls s' = ps_tls s)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -32)) r9 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 r20 r21 r22 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 Fb) r25 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x862e0) fc None m (seg_rom asegs)).
  Section Sz10.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F fc L RNG s CL FB FL lo SPA Fb m ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r25 s10 s11 t3 t4 t5 t6 v0 v1 v2 v3 k0 k1 k2 fptr apw fj1 fj2 b0 b1 b2 b3 b4 b5 b6 b7 A x : ltac2:(SecDiet.SzSec.tyM 'fm_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fm_epi__body : ltac2:(SecDiet.SzSec.bodyP 'fm_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FRET GL.
 intros SPAB SPA32 LO LOS SPT TOP47 G MI ST STG FRA FRs FRv FRC SHC RSTK.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND FTOP F64 _ FRNG FSRNG _ _; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 64 3) with 8%Z in FSRNG.
    (pose proof (ablk_lin _ _ FBAND) as ndP__; nd_pre ndP__ 4%nat; intros _ Fb0 _ _; nd_post). band_ind FBAND bF.
    (nd_pre (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) 6%nat; intros _ FLR FLB FLT _ (kF & kFr & kF1 & kF2); nd_post). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; dm_plia).
    assert (FW : Forall (own_ivA [(FF_FMT_ERRMSG, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    pose proof (munch_refl [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    burst_begin [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z [Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    zstep. neg_lits.
    zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    do 4 zstep. zstep_sh0. do 3 zstep.
    burst_end MUb WMb.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FW (Forall_nil _) G' MU WM ltac:(lia)) as [G5 AG5];
      pose proof (munch_refl [(fflagA L FF_FMT_ERRMSG Fb, fflagA L FF_FMT_ERRMSG Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    rewrite app_nil_r in G5.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 14 zstep.
    release_frame FRA ST (SPA + 8)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    pose proof (rw_cells_uncut _ _ _ _ _ FRs FRv ltac:(cbn; lia)) as FR. cbn [app] in FR. clear FRs FRv.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CL (bv_unsigned sp) G5 MU2 WM2 (incl_refl _) ltac:(lia)) as [AG6 _].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 15 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split; [exact G6|]. split; [exact OF3|]. split; [exact LC3| exact TL3].
  Qed.
  End Sz10.
  Lemma fm_epi : ltac:(let t := eval cbv delta [fm_epi__stmt] in fm_epi__stmt in exact t).
  Proof using FRET GL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F fc L RNG s CL FB FL lo SPA Fb m ra0 t0 t1 t2 r9 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r25 s10 s11 t3 t4 t5 t6 v0 v1 v2 v3 k0 k1 k2 fptr apw fj1 fj2 b0 b1 b2 b3 b4 b5 b6 b7 A x. ltac2:(SecDiet.SzSec.closeP 'fm_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fmt_errmsg_proofA__stmt : Prop := fmt_errmsg_stmt FO GIOA.
  Section Sz11.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo EB FMTA e fs args junk : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fmt_errmsg_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FENTER0 FRET GL SNPRINTF STRERROR STRLEN VSNPRINTF.
 intros PRE NF -> -> -> HE -> FMT5 FOK LA FW HEB OEB E8.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    unfold PCAP_L1_STACK in BU.
    pose proof (farg_words_ok _ _ _ _ _ _ _ _ _ _ _ FW) as AOK.
    pose proof (fmt_ok_items_okb _ _ FOK) as IOK.
    set (out := Fmt.snprintf 256 fs args). set (len := length out).
    pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LENB. fold out len in LENB.
    pose proof (snprintf_ok 256 fs args IOK AOK) as OUTOK. fold out in OUTOK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rng_sp_window RSTK sp RSPW.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    pose proof (proj1 OEB) as EBL.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL ltac:(lia)) as EBBAND. pose proof EBBAND as EBBAND'. band_ind EBBAND bE.
    remember (bv_unsigned sp - 128 - (bv_unsigned sp - 128) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 159 <= SPA <= bv_unsigned sp - 128 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -128) - (bv_unsigned sp + -128) mod 32 = SPA)%Z)
      by (rewrite ESPA; dm_plia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    assert (MIe : hidc (mem_inv asegs m)) by exact MI.
    unfold PCAP_FMT_ERRMSG_ENTRY.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 120%nat ST. carve_frame 8%nat ST.
    zstep.
    do 11 zstep.
    zstep.
    zstep.
    rewrite land_m32F by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -120)%Z.
    destruct (stk_split asegs _ lo (SPA + 8) (bv_unsigned sp + -120) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 8) 8 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 8) with 8%Z in STL, FRA. replace (SPA + 8 - 8)%Z with SPA in STL, FRA by lia.
    do 5 zstep.
    do 4 zstep.
    zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    do 4 zstep.
    zstep. if_false.
    do 2 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FWS : Forall (client_ivA FL CL) [(bv_unsigned sp - 160, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (AG0 : agrees_on (fun a => outside [(bv_unsigned sp - 160, bv_unsigned sp)]%Z a) m mm)
        by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho])
    end.
    rename MU into MU0. rename WM into WM0. clear FWS G'.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER0 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [dm_plia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { exact NF. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_FMT_ERRMSG) with 64%Z in *.
    change (Z.to_nat (64 - 32)) with 32%nat in *. change (Z.to_nat (64 / 8)) with 8%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 549252)) with (Z_to_bv 64 549252) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND' FTOP' F64 _ FRNG FSRNG _ FSWR; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 64 3) with 8%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HEB; [|intros a Ha; eapply clocA_keeps; [exact EBL| exact Ha]].
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 EBL ltac:(lia)) 4%nat; intros kE kEr kE1 kE2; nd_post).
    cbn [fb_addr fb_size fst snd] in kE1, kE2.
    assert (AGb : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; dm_plia).
    pose proof (munch_refl [(bv_unsigned sp - 28672, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8); (EB, EB + 256)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    burst_begin [(SPA, SPA + 8); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z [SPA; Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 11 zstep.
    zstep. neg_lits.
    zstep.
    do 4 zstep.
    zstep. neg_lits.
    zstep_sh0.
    do 3 zstep.
    do 2 zstep.
    burst_end MUb WMb.
    do 4 zstep.
    zstep.
    (* [comment removed for export] *)
    clear GOT SHB SUA GSU.
    pose proof G1 as G1'. rewrite <- (app_nil_r CL) in G1'.
    assert (FWo : Forall (own_ivA [(FF_FMT_ERRMSG, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 28672, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    assert (FX : Forall (cobj_iv FL CL) [(EB, EB + 256)]%Z) by cobj_ivs.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(EB, EB + 256)]%Z) by (apply Forall_cons; [exact EBBAND'| apply Forall_nil]).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWo FX G1' MU WM ltac:(lia)) as [G2 AG2];
      assert (AGsh : agrees_on (in_frame_sh FL) m mm)
        by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG2 FXB));
      assert (AGx : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m mm)
        by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb| intros x [Hx _]; exact Hx]| exact AG2])
    end.
    rewrite app_nil_r in G2.
    unfold hidc in MIe.
    assert (FMT0 : fmt_at m0 FMTA fs) by (eapply fmt_at_keep; [exact FMT5 | exact MIe | exact MI1]).
    assert (FW0 : Forall2 (farg_word true L RNG ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL SPA EB 256 m0) args (firstn (length args) [a4])).
    { apply farg_words_tls. eapply farg_words_keepx; [exact FW | exact G2 | apply incl_refl | apply incl_tl; apply incl_refl | apply fp_le_refl
                                                     | exact AGx | exact AGsh | exact MIe | exact MI1 | exact RIMG | exact RISH | exact RTLS]. }
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G2 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as OEB2.
    assert (OEB3 : cobjA RNG m0 ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL EB 256)
      by (split; [eapply clocA_incl; [exact (proj1 OEB2)| apply incl_refl| apply incl_tl; apply incl_refl]| exact (proj2 OEB2)]).
    (* [comment removed for export] *)
    destruct (rw_cells_cut _ _ _ 11 FR) as [FRs FRv]. cbn [firstn skipn cells_size csize Nat.add] in FRs, FRv.
    replace (bv_unsigned sp + -120 + Z.of_nat 88)%Z with (bv_unsigned sp + -32)%Z in FRv by lia.
    destruct args as [|x1 [|x2 args2]]; [ | | cbn [length] in LA; exfalso; lia].
    all: cbn [length firstn] in FW0.
    1: destruct (rw_cells_cut _ _ _ 0 FRv) as [AP0 _]; cbn [firstn skipn cells_size csize Nat.add] in AP0.
    2: destruct (rw_cells_cut _ _ _ 1 FRv) as [AP0 _]; cbn [firstn skipn cells_size csize Nat.add] in AP0.
    all: remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    all: assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    all: lazymatch type of FW0 with Forall2 _ ?xargs ?xws => eapply evtF_cut;
           [ eapply VSNPRINTF with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_FMT_ERRMSG, Fb, 64%Z) :: FL) (lo := lo) (DST := EB) (n := 256%Z)
                                   (FMTA := FMTA) (AP := (bv_unsigned sp + -32)%Z) (fs := fs) (args := xargs) (ws := xws) (junk := junk);
             [ split; [exact G2|]; rewrite Hspa; split; [exact ST1|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
               split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
               split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
             | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact FMT0 | exact FOK
             | reflexivity | cbn [length]; lia | rewrite Hspa; exact FW0
             | first [exact AP0 | cbn [map]; exact AP0] | rewrite Hspa; lia | cbn [length]; lia | cbn [length]; lia | exact HEB | exact OEB3 ]
           | ] end.
    all: cbv beta; intros ms' PO; (nd_pre PO 9%nat; intros vav mv vjk E MU1 WM1 MIv STv ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into HD1);
         unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
    all: replace (ret_pc (Z_to_bv 64 549424)) with (Z_to_bv 64 549424) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unfold STDIO_STACK in MU1; clear G2 AG2 AGsh AGx FW0 FMT0 OEB2 OEB3 AP0.
    all: transport_after_call asegs m0 mv MU1 WM1; clear MU1 WM1 MI1.
    all: change (Z.to_nat 256) with 256%nat in HD1; fold out in HD1; fold len in HD1.
    all: assert (LJ1 : length vjk = (255 - len)%nat)
           by (destruct HD1 as [[WFc _] _]; cbn [cells_wf cell_wf csize] in WFc; rewrite length_app, length_map in WFc; cbn [length] in WFc; lia).
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWo FX G1' MU WM ltac:(lia)) as [G3 AG3];
           assert (AGsh : agrees_on (in_frame_sh FL) m mm)
             by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG3 FXB))
         end.
    all: rewrite app_nil_r in G3.
    all: pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G3 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as OEB2.
    all: assert (OEB3 : cobjA RNG mv ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL EB 256)
           by (split; [eapply clocA_incl; [exact (proj1 OEB2)| apply incl_refl| apply incl_tl; apply incl_refl]| exact (proj2 OEB2)]).
    all: do 2 zstep.
    all: remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    all: assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    all: eapply evtF_cut;
           [ eapply STRLEN with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_FMT_ERRMSG, Fb, 64%Z) :: FL) (lo := lo) (P := EB) (bs := map b8 out) (slack := vjk);
             [ split; [exact G3|]; rewrite Hspa; split; [exact STv|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
               split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
               split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
             | reflexivity
             | pose proof (rw_cells_bytes_at _ _ _ _ HD1) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r, <- app_assoc in X; exact X
             | apply map_b8_no_nul; exact OUTOK
             | rewrite length_map; fold len; lia
             | rewrite length_map, LJ1; fold len; clear - E8 LENB; dm_plia
             | rewrite length_map; fold len; eapply robjA_sub; [apply cobjA_robjA; [exact OEB3| lia]| lia]
             | rewrite length_map, LJ1; fold len; replace (Z.of_nat len + 1 + Z.of_nat (255 - len))%Z with 256%Z by lia; destruct OEB3 as [_ (_ & _ & _ & R & _)]; exact R ]
           | ].
    all: cbv beta; intros ms' PO; (nd_pre PO 8%nat; intros vav2 mw E MU2 WM2 MIw STw ndR1__; nd_post; revert ndR1__; intros ->);
         unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
    all: replace (ret_pc (Z_to_bv 64 549432)) with (Z_to_bv 64 549432) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unfold STDIO_STACK in MU2; clear G3 AG3 AGsh OEB2 OEB3.
    all: transport_after_call asegs mv mw MU2 WM2; clear MU2 WM2 MIv.
    all: rewrite length_map; fold len.
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWo FX G1' MU WM ltac:(lia)) as [G4 AG4];
           assert (AGsh : agrees_on (in_frame_sh FL) m mm)
             by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG4 FXB));
           assert (AGx : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m mm)
             by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb| intros aa [Haa _]; exact Haa]| exact AG4])
         end.
    all: rewrite app_nil_r in G4.
    all: do 2 zstep.
    all: if_cases Kr; zify_cond Kr.
    (* [comment removed for export] *)
    1,3: apply evtF_done; eapply implMG_mono;
           [ eapply fm_epi with (L := L) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (SPA := SPA) (Fb := Fb);
             [ lia | exact SPA32 | lia | lia | lia | lia | exact G4 | assumption | exact STw | exact STG | exact FRA | exact FRs | exact FRv | exact FRC | exact SHC | exact RSTK ]
           | ].
    1,2: cbv beta; intros r s5' RNG5 ms5 PO; (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); rename ndR2__ into PO); destruct_exs PO;
         (destruct PO as (-> & ndR1__); nd_pre ndR1__ 7%nat; intros MI5 ST5 AG5 G5 OF5 LC5 TL5; nd_post).
    1,2: subst POSTQ0 POSTQ; cbv beta; split; [apply fp_le_refl|]; split; [reflexivity|].
    1,2: do 15 eexists; lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end; exists vjk.
    1,2: split; [reflexivity|]; split; [congruence|]; split; [congruence|]; split; [congruence|];
         split; [exact MI5|]; split; [exact ST5|].
    1,2: split; [eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGx| intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]
                                        | eapply agrees_on_weaken; [exact AG5| intros a [K _]; exact K]]|].
    1,2: split; [exact G5|].
    1,2: unfold fmt_errmsg, PCAP_ERRBUF_SIZE; fold out; unfold zlength; fold len;
         replace (256 <? Z.of_nat len + 3) with true by (symmetry; apply Z.ltb_lt; lia);
         replace (255 - length out)%nat with (256 - len - 1)%nat by (subst len; lia);
         eapply agrees_rw_cells; [exact AG5 | exact HD1 |]; intros a Ha; eapply clocA_keeps; [exact EBL|];
         cbn [cells_size csize Nat.add] in Ha; lia.
    (* [comment removed for export] *)
    all: assert (L2 : (2 <= length vjk)%nat) by lia.
    all: destruct vjk as [|jb0 [|jb1 jrest]]; try (exfalso; cbn [length] in L2; lia); cbn [length] in LJ1.
    all: assert (HD5 : rw_cells asegs mw EB [CB len (map b8 out); CB 1 [Z_to_bv 8 0]; CB 1 [jb0]; CB 1 [jb1]; CB (253 - len) jrest])
           by (eapply rw_cells_recell; [exact HD1 | cbn; rewrite length_map; repeat split; try reflexivity; lia | cbn [cells_bytes cbytes]; rewrite <- !app_assoc, !app_nil_r; reflexivity]);
         clear HD1.
    all: destruct (rw_cells_cut _ _ _ 1 HD5) as [HDo HDr]; clear HD5; cbn [firstn skipn cells_size csize Nat.add] in HDo, HDr; rewrite Nat.add_0_r in HDr.
    all: destruct (rw_cells_cut _ _ _ 3 HDr) as [HD3 HDrest]; clear HDr; cbn [firstn skipn cells_size csize Nat.add] in HD3, HDrest.
    all: pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G4 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as (_ & (_ & _ & EUNP & ERNG & ERSH & _)).
    all: replace (EB - EB mod 8)%Z with EB in ERSH by lia; replace (256 + EB mod 8)%Z with 256%Z in ERSH by lia.
    (* [comment removed for export] *)
    all: do 2 zstep; ub_ltu.
    all: do 4 zstep; ub_xnull.
    all: zstep; ub_null_here.
    all: do 2 zstep; ub_m1.
    all: remember (EB + Z.of_nat len)%Z as Q eqn:HQ in *.
    all: replace (Q + Z.of_nat 3)%Z with (Q + 3)%Z in HDrest by lia.
    all: assert (RQ : rng RNG Q 3) by (eapply rng_sub'; [exact ERNG| lia]).
    all: ck0 EUNP; ck_go.
    all: do 5 zstep; ub_m1.           (* [comment removed for export] *)
    all: ck0 EUNP; ck_go.
    all: do 3 zstep.
    all: ck0 EUNP; ck_go.
    all: do 4 zstep.
    all: zstep.
    (* [comment removed for export] *)
    all: clear G4 AG4 AGsh AGx.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWo FX G1' MU WM ltac:(lia)) as [G6 AG6];
           assert (AGsh6 : agrees_on (in_frame_sh FL) m mm)
             by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG6 FXB));
           assert (AGx6 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(EB, EB + 256)%Z] a) m mm)
             by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb| intros aa [Haa _]; exact Haa]| exact AG6])
         end.
    all: rewrite app_nil_r in G6.
    all: assert (EBL' : clocA ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL EB 256) by (eapply clocA_incl; [exact EBL| apply incl_refl| apply incl_tl; apply incl_refl]).
    all: remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    all: assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    all: eapply evtF_cut;
           [ eapply STRERROR with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_FMT_ERRMSG, Fb, 64%Z) :: FL) (lo := lo) (e := e);
             [ split; [exact G6|]; rewrite Hspa; split; [exact STw|]; split; [lia|]; split; [unfold PCAP_L0_STACK; lia|]; split; [lia|];
               split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
               split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
             | reflexivity | exact HE ]
           | ].
    all: cbv beta; intros ms' PO; destruct_exs PO; (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MI7 ST7 AG7 G7 TLS7; nd_post); rewrite Hspa in *; clear Hspa; subst spa.
    all: replace (ret_pc (Z_to_bv 64 549576)) with (Z_to_bv 64 549576) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG7) in FRs; [|lia]; apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG7) in FRv; [|lia];
         apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG7) in FRA; [|lia].
    all: apply (agrees_stk _ _ _ _ _ AG7) in STG; [|intros a Ha; left; lia].
    all: assert (FRIN : forall a, (Fb <= a < Fb + 64)%Z -> in_frames ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) a)
           by (intros a Ha; apply in_frames_In; exists (FF_FMT_ERRMSG, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    all: assert (SHIN : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> in_frame_sh ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) a)
           by (intros a Ha; apply in_frame_sh_In; exists (FF_FMT_ERRMSG, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 64 3) with 8%Z; lia]).
    all: apply (keeps_rw_cells_frame _ _ _ _ _ _ _ AG7) in FRC; [|intros a Ha; apply FRIN; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (keeps_rw_cells_frame_sh _ _ _ _ _ _ _ AG7) in SHC; [|intros a Ha; apply SHIN; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG7) in HDo; [|intros a Ha; eapply clocA_keeps; [exact EBL'|]; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG7) in HD3; [|intros a Ha; eapply clocA_keeps; [exact EBL'|]; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG7) in HDrest; [|intros a Ha; eapply clocA_keeps; [exact EBL'|]; cbn [cells_size csize Nat.add] in Ha; lia].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           assert (AGx7 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(EB, EB + 256)%Z] a) m mm)
             by (eapply agrees_on_trans; [exact AGx6|]; eapply agrees_on_weaken; [exact AG7|]; intros a [K _];
                 destruct K as [K|[K|[K|K]]]; [left; lia | right; left; exact K | right; right; left; apply in_frames_cons; exact K
                                              | right; right; right; apply in_frame_sh_cons; exact K]);
           assert (AGsh7 : agrees_on (in_frame_sh FL) m mm)
             by (eapply agrees_on_trans; [exact AGsh6|]; eapply agrees_on_weaken; [exact AG7|]; intros a K; right; right; right; apply in_frame_sh_cons; exact K)
         end.
    (* [comment removed for export] *)
    all: pose proof (strerror_len e) as SEL; set (se := Fmt.strerror e) in *.
    all: lazymatch type of TLS7 with rw_cells _ _ _ [_; CB _ ?r] => rename r into rest end.
    all: assert (LR : length rest = (255 - length se)%nat) by (destruct TLS7 as [[WFc _] _]; cbn [cells_wf cell_wf csize] in WFc; lia).
    all: clear MU WM G6 AG6 AGsh6 AGx6.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           pose proof (munch_refl [(bv_unsigned sp - 28672, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8); (EB, EB + 256)]%Z mm) as MU;
           pose proof (wmono_refl asegs mm) as WM;
           assert (MSG : fmt_at mm 0x217a0 "%s"%string)
             by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x217a0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "%s"%string) ++ [Z_to_bv 8 0])
                                     MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
                 split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]))
         end.
    all: pose proof G7 as G7'; rewrite <- (app_nil_r CL) in G7'.
    all: do 5 zstep.
    all: zstep.
    (* [comment removed for export] *)
    all: destruct (rw_cells_cut _ _ _ 2 HD3) as [HC2 HZ]; clear HD3; cbn [firstn skipn cells_size csize Nat.add] in HC2, HZ.
    all: pose proof (rw_cells_uncut _ _ _ _ _ HZ HDrest ltac:(cbn; lia)) as HDST0; clear HZ HDrest.
    all: lazymatch type of HDST0 with rw_cells _ ?mm _ _ =>
           pose proof (rw_cells_merge asegs mm _ [] _ [] ltac:(rewrite app_nil_r; exact HDST0)) as HDST end; clear HDST0;
         cbn [app cells_size csize cells_bytes cbytes Nat.add] in HDST.
    all: replace (Q + Z.of_nat 2)%Z with (Q + 2)%Z in HDST by lia.
    all: replace (S (253 - len + 0)) with (Z.to_nat (254 - Z.of_nat len)) in HDST by lia.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           assert (FWS : Forall2 (farg_word true L RNG ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL SPA (Q + 2) (254 - Z.of_nat len) mm) [AStr se] [Z_to_bv 64 (ATP + PCAP_TLS_ERRBUF)])
             by (constructor; [| constructor]; eapply tls_farg; [exact G7 | exact RTLS | exact TLS7 |];
                 destruct (clocA_apart_tls _ _ _ GL _ _ _ _ _ _ _ _ _ G7 EBL' ltac:(lia)) as [T|T]; [left; lia | right; lia]);
           pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G7 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh7 ltac:(lia)) as OEB7;
           assert (ODST : cobjA RNG mm ((FF_FMT_ERRMSG, Fb, 64%Z) :: FL) CL (Q + 2) (254 - Z.of_nat len))
             by (eapply cobjA_sub; [split; [exact EBL'| exact (proj2 OEB7)] | lia | lia | lia])
         end.
    all: remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    all: assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    all: eapply evtF_cut;
           [ eapply SNPRINTF with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_FMT_ERRMSG, Fb, 64%Z) :: FL) (lo := lo) (DST := (Q + 2)%Z) (n := (254 - Z.of_nat len)%Z)
                                  (FMTA := 0x217a0%Z) (fs := "%s"%string) (args := [AStr se]) (junk := (Z_to_bv 8 0 :: jrest ++ []));
             [ split; [exact G7|]; rewrite Hspa; split; [exact ST7|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
               split; [assumption|]; split; [exact TPE|]; split; [dm_plia|];
               split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
             | reflexivity | first [reflexivity | f_equal; lia] | reflexivity | lia | exact MSG | reflexivity | cbn; lia
             | cbn [length firstn]; rewrite Hspa; exact FWS | exact HDST | exact ODST ]
           | ].
    all: cbv beta; intros ms' PO; (nd_pre PO 9%nat; intros vav5 m9 junk5 E MU5 WM5 MI9 ST9 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into HD2);
         unfold hpost_regs in E; destruct_exs E; subst ms'; rewrite Hspa in *; clear Hspa; subst spa.
    all: replace (ret_pc (Z_to_bv 64 549600)) with (Z_to_bv 64 549600) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    all: unfold STDIO_STACK in MU5; clear FWS MSG OEB7 ODST HDST.
    all: lazymatch type of MU5 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU5 WM5 end; clear MU5 WM5 MI7.
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWo FX G7' MU WM ltac:(lia)) as [G9 AG9] end.
    all: rewrite app_nil_r in G9.
    all: apply evtF_done; eapply implMG_mono;
           [ eapply fm_epi with (L := L) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (SPA := SPA) (Fb := Fb);
             [ lia | exact SPA32 | lia | lia | lia | lia | exact G9 | assumption | exact ST9 | exact STG | exact FRA | exact FRs | exact FRv | exact FRC | exact SHC | exact RSTK ]
           | ].
    all: cbv beta; intros r s5' RNG5 ms5 PO; (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); rename ndR2__ into PO); destruct_exs PO;
         (destruct PO as (-> & ndR1__); nd_pre ndR1__ 7%nat; intros MI5 ST5 AG5 G5 OF5 LC5 TL5; nd_post).
    all: subst POSTQ0 POSTQ; cbv beta; split; [apply fp_le_refl|]; split; [reflexivity|].
    all: do 15 eexists; lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end; exists junk5.
    all: split; [reflexivity|]; split; [congruence|]; split; [congruence|]; split; [congruence|];
         split; [exact MI5|]; split; [exact ST5|].
    all: split; [eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGx7| intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]|];
                 eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG9| intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]
                                         | eapply agrees_on_weaken; [exact AG5| intros a [K _]; exact K]]|].
    all: split; [exact G5|].
    (* [comment removed for export] *)
    all: set (out2 := Fmt.snprintf (254 - Z.of_nat len) "%s" [AStr se]) in *.
    all: pose proof (snprintf_length_le (254 - Z.of_nat len) "%s" [AStr se] ltac:(lia)) as L2B; fold out2 in L2B.
    all: assert (LJ5 : length junk5 = (253 - len - length out2)%nat)
           by (destruct HD2 as [[WFc _] _]; cbn [cells_wf cell_wf csize] in WFc; rewrite length_app, length_map in WFc; cbn [length] in WFc; lia).
    all: lazymatch goal with |- context [fmt_errmsg ?ff ?ar ?ee] =>
           assert (EFM : fmt_errmsg ff ar ee = out ++ [58; 32]%Z ++ out2)
             by (unfold fmt_errmsg, PCAP_ERRBUF_SIZE; fold out; unfold zlength;
                 replace (256 <? Z.of_nat (length out) + 3) with false by (symmetry; apply Z.ltb_ge; subst len; lia);
                 unfold strerror_r; fold se; unfold zlength; replace (Z.of_nat (length se) <? 256) with true by (symmetry; apply Z.ltb_lt; lia); cbn [snd];
                 replace (256 - Z.of_nat (length out) - 2)%Z with (254 - Z.of_nat len)%Z by (subst len; lia); reflexivity)
         end.
    all: rewrite EFM; rewrite !length_app; cbn [length].
    all: assert (EBK : forall a, (EB <= a < EB + 256)%Z -> client_keeps FL CL (bv_unsigned sp) a) by (intros a Ha; eapply clocA_keeps; [exact EBL| exact Ha]).
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in HDo; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in HC2; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; lia].
    all: apply (agrees_rw_cells _ _ _ _ _ AG5) in HD2; [| intros a Ha; apply EBK; cbn [cells_size csize Nat.add] in Ha; lia].
    all: pose proof (rw_cells_uncut _ _ _ _ _ HDo HC2 ltac:(cbn; lia)) as J1.
    all: pose proof (rw_cells_uncut _ _ _ _ _ J1 HD2 ltac:(cbn; lia)) as J2.
    all: eapply rw_cells_recell; [exact J2 | | ].
    2,4: cbn [cells_bytes cbytes app map]; rewrite !map_app; cbn [map app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
    all: cbn [cells_wf cell_wf csize]; rewrite !length_app, !length_map, !length_app; cbn [length]; repeat split; lia.
  Qed.
  End Sz11.
  Theorem fmt_errmsg_proofA : ltac:(let t := eval cbv delta [fmt_errmsg_proofA__stmt] in fmt_errmsg_proofA__stmt in exact t).
  Proof using FENTER0 FRET GL SNPRINTF STRERROR STRLEN VSNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo EB FMTA e fs args junk. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FmtErrmsg.
End CANSEC1.
End TwB.
