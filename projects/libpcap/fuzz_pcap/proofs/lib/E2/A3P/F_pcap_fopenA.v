(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_gotA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
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
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Tactic Notation "xf1" constr(AG) hyp(HH) tactic3(loc) :=
  apply (agrees_rw_cells _ _ _ _ _ AG) in HH;
  [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add] in Ha; loc].
Tactic Notation "xf2" constr(AG) hyp(HH) tactic3(loc) :=
  apply (agrees_rw_cells _ _ _ _ _ AG) in HH;
  [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [loc| lia]].
Tactic Notation "xf3" constr(AG) hyp(HH) tactic3(loc) :=
  apply (agrees_rw_cells _ _ _ _ _ AG) in HH;
  [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [loc| split; lia]].

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
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells ?s ?m ?A1 ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    let J := fresh "J" in
    pose proof (rw_cells_uncut m A1 cs1 cs2 A2 H1 H2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J;
    clear H1 H2; cbn [app] in J; rename J into H1
  end end.

Lemma land_m32F : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Open Scope bv_scope.
Definition fmt_errmsg_length__stmt : Prop := forall f args e, (length (fmt_errmsg f args e) <= 255)%nat.
Section Sz2.
Variables f args e : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_length__stmt "vvv" @f).
Lemma fmt_errmsg_length__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_length__stmt "vvv").
Proof using .
 unfold fmt_errmsg, snprintf, snprintf_out, PCAP_ERRBUF_SIZE, zlength.
  set (mm := firstn (Z.to_nat (256 - 1)) (fmt_output (fmt f) args)).
  assert (Hm : (length mm <= 255)%nat) by (subst mm; rewrite length_firstn; apply Nat.le_min_l).
  destruct (256 <? Z.of_nat (length mm) + 3)%Z eqn:E; [exact Hm|].
  apply Z.ltb_ge in E. rewrite !length_app, length_firstn. cbn [length str String.list_ascii_of_string map].
  unfold str. cbn [String.list_ascii_of_string map length]. lia.
Qed.
End Sz2.
Lemma fmt_errmsg_length : ltac:(let t := eval cbv delta [fmt_errmsg_length__stmt] in fmt_errmsg_length__stmt in exact t).
Proof. intros f args e. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_length__body "vvv"). Qed.
Lemma snprintf_length : forall n f a, (length (Fmt.snprintf n f a) <= Z.to_nat (n - 1))%nat.
Proof. intros. unfold Fmt.snprintf, snprintf_out. apply firstn_le_length. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section FopenOffline.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GOTL : gia_got_law GIOA.
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FILENO : fileno_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis CHK_PCAP : pcap_check_header_stmt HO FO sites GIOA TP.
  Hypothesis CHK_NG : pcap_ng_check_header_stmt HO FO sites GIOA TP.
  Lemma chk_any : forall ng, check_header_stmt_for HO FO sites GIOA TP ng.
  Proof using CHK_NG CHK_PCAP. intros [|]; [exact CHK_NG | exact CHK_PCAP]. Qed.

  Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof using . intros B C f g s RNG Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  Definition callee_ag__stmt : Prop := forall L RNG s (CLg FB : list (@cblock hptr)) FL m0 Fb SPA SP (CL CLk : list (@cblock hptr)) (X : Z -> Prop) EB (mA mB : mem),
    GIOA L RNG s CLg FB ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) m0 -> incl CL CLg -> (forall a, in_block CL a -> in_block CLk a) ->
    (ATOP <= SP)%Z -> (SPA <= SP)%Z ->
    agrees_on (fun a => client_keeps ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CLk SPA a /\ X a) mA mB ->
    (forall a, ~ (Fb <= a < Fb + 64)%Z -> ~ (EB <= a < EB + 256)%Z -> X a) ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside [(EB, EB + 256)%Z] a) mA mB.
  Section Sz6.
  Variables L RNG s CLg FB FL m0 Fb SPA SP CL CLk X EB mA mB : ltac2:(SecDiet.SzSec.tyM 'callee_ag__stmt "vvvvvvvvvvvvvvvv" @L).
  Lemma callee_ag__body : ltac2:(SecDiet.SzSec.bodyP 'callee_ag__stmt "vvvvvvvvvvvvvvvv").
  Proof using GL.
    intros G IC IB HSP HSPA AG HX.
 eapply agrees_on_weaken; [exact AG|]. intros a [K [NE _]].
    destruct (keeps_not_own_frame _ _ _ GL _ _ _ _ _ _ _ (FF_FOPEN_OFFLINE, Fb, 64%Z) CL SP a G IC HSP K) as [NF1 _].
    cbn [fb_addr fb_size fst snd] in NF1.
    split; [| apply HX; assumption].
    destruct K as [K|[K|[K|K]]]; [left; lia| right; left; apply IB; exact K| right; right; left; apply in_frames_cons; exact K
                                 | right; right; right; apply in_frame_sh_cons; exact K].
  Qed.
  End Sz6.
  Lemma callee_ag : ltac:(let t := eval cbv delta [callee_ag__stmt] in callee_ag__stmt in exact t).
  Proof using GL. intros L RNG s CLg FB FL m0 Fb SPA SP CL CLk X EB mA mB. ltac2:(SecDiet.SzSec.closeP 'callee_ag__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fo_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 s11 t3 t4 t5 t6 : word)
      (k0 : word) (fra : list cell) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 159 <= SPA <= bv_unsigned sp - 128)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z ->
    GIOA L RNG s CL FB ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 32) (bv_unsigned sp + -96) ->
    rw_cells asegs m SPA fra -> cells_size fra = 32%nat ->
    rw_cells asegs m (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0] ->
    rw_cells asegs m (Fb + 56) [C8 (Z_to_bv 64 (fflagA L FF_FOPEN_OFFLINE Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_FOPEN_OFFLINE x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIOA L RNG s' CL FB FL m' /\ ps_outfile s' = ps_outfile s /\ ps_libc s' = ps_libc s /\ ps_tls s' = ps_tls s)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 r20 r21 r22 r23 (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8527c) fc None m (seg_rom asegs)).
  Section Sz7.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 F fc L RNG s CL FB FL lo SPA Fb m ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 s11 t3 t4 t5 t6 k0 fra b0 b1 b2 b3 b4 b5 b6 b7 A x : ltac2:(SecDiet.SzSec.tyM 'fo_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fo_epi__body : ltac2:(SecDiet.SzSec.bodyP 'fo_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FRET GL.
 intros SPAB SPA32 LO LOS SPT TOP47 G MI ST STG FRA FRAS FRs FK0 FLG SHC RSTK.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND FTOP F64 _ FRNG FSRNG _ _; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 64 3) with 8%Z in FSRNG.
    (pose proof (ablk_lin _ _ FBAND) as ndP__; nd_pre ndP__ 4%nat; intros _ Fb0 _ _; nd_post). band_ind FBAND bF.
    (nd_pre (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) 6%nat; intros _ FLR FLB FLT _ (kF & kFr & kF1 & kF2); nd_post). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    assert (FW : Forall (own_ivA [(FF_FOPEN_OFFLINE, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    pose proof (munch_refl [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    burst_begin [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z [Fb; (Fb + 56)%Z; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    zstep. neg_lits.
    do 2 zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    do 4 zstep. zstep_sh0. do 3 zstep.
    burst_end MUb WMb.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FW (Forall_nil _) G' MU WM ltac:(lia)) as [G5 AG5];
      pose proof (munch_refl [(fflagA L FF_FOPEN_OFFLINE Fb, fflagA L FF_FOPEN_OFFLINE Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    rewrite app_nil_r in G5.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 15 zstep.
    release_frame FRA ST (SPA + 32)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    release_frame FRs ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CL (bv_unsigned sp) G5 MU2 WM2 (incl_refl _) ltac:(lia)) as [AG6 _].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split; [exact G6|]. split; [exact OF3|]. split; [exact LC3| exact TL3].
  Qed.
  End Sz7.
  Lemma fo_epi : ltac:(let t := eval cbv delta [fo_epi__stmt] in fo_epi__stmt in exact t).
  Proof using FRET GL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 F fc L RNG s CL FB FL lo SPA Fb m ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 s11 t3 t4 t5 t6 k0 fra b0 b1 b2 b3 b4 b5 b6 b7 A x. ltac2:(SecDiet.SzSec.closeP 'fo_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fopen_offline_proofA__stmt : Prop := fopen_offline_stmt HO FO sites GIOA TP.
  Section Sz8.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo FA EB f ej fuel : ltac2:(SecDiet.SzSec.tyM 'fopen_offline_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fopen_offline_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_offline_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CHK_NG CHK_PCAP FENTER0 FERROR FILENO FMT FREAD FRET GL GOTL SNPRINTF.
 intros PRE UC TR NF HinF -> -> -> HEB OEB E8.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    unfold PCAP_L3_STACK in BU. (nd_pre TR 3%nat; intros TRC TRM TRN; nd_post).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rng_sp_window RSTK sp RSPW.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as ndP__; nd_pre ndP__ 3%nat; intros (FABAND & _ & FATOP & _) FA1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in FABAND, FATOP, FA1. unfold FILE_BLOCK in FABAND, FATOP. pose proof (ablk_lin _ _ FABAND) as (FAIMG & _). unfold AIMG_HI in FAIMG. clear FABAND.
    pose proof (proj1 OEB) as EBL.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL ltac:(lia)) as EBBAND. pose proof EBBAND as EBBAND'. band_ind EBBAND bE.
    remember (bv_unsigned sp - 128 - (bv_unsigned sp - 128) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 159 <= SPA <= bv_unsigned sp - 128 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -128) - (bv_unsigned sp + -128) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    assert (MIe : hidc (mem_inv asegs m)) by exact MI.
    assert (HEBe : hidc (rw_cells asegs m EB [CB 256 ej])) by exact HEB.
    unfold pcap_fopen_offline_with_tstamp_precision, read_fail_msg, errmsg_for_errno.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_fread e_ferror e_fileno e_last_errno prims]. unfold PCAP_FOPEN_OFFLINE_WTP_ENTRY.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 96%nat ST. carve_frame 32%nat ST.
    zstep.
    do 12 zstep.
    zstep.
    zstep.
    rewrite land_m32F by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -96)%Z.
    destruct (stk_split asegs _ lo (SPA + 32) (bv_unsigned sp + -96) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 32) 32 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 32) with 32%Z in STL, FRA. replace (SPA + 32 - 32)%Z with SPA in STL, FRA by lia.
    do 5 zstep.
    do 2 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 2 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FWS : Forall (client_ivA FL CL) [(bv_unsigned sp - 160, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FWS G'.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER0 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { apply NF. unfold frames_fopen_offline. cbn. first [ clear; tauto | tauto ]. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_FOPEN_OFFLINE) with 64%Z in *.
    change (Z.to_nat (64 - 32)) with 32%nat in *. change (Z.to_nat (64 / 8)) with 8%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 544512)) with (Z_to_bv 64 544512) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
    assert (UCb : ucallerA depth_fopen_offline L m2 sp s0 ra trC)
      by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha; destruct (AGb a ltac:(lia) ltac:(left; lia)) as [E1 _]; exact E1).
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    burst_begin [(SPA, SPA + 32); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z [SPA; Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 4 zstep.
    zstep. neg_lits.
    zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    do 2 zstep.
    do 4 zstep.
    zstep. neg_lits.
    zstep_sh0.
    do 3 zstep.
    zstep.
    burst_end MUb WMb.
    zstep. if_false_by (eqz_false FA ltac:(lia)).
    do 5 zstep.
    zstep.
    (* [comment removed for export] *)
    clear GOT SHB SUA GSU.
    pose proof G1 as G1'. rewrite <- (app_nil_r CL) in G1'.
    assert (FWo : Forall (own_ivA [(FF_FOPEN_OFFLINE, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 160, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FWo (Forall_nil _) G1' MU WM ltac:(lia)) as [G2 AG2];
      assert (AGx : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m mm)
        by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb| intros x [Hx _]; exact Hx]|];
            eapply agrees_on_weaken; [exact AG2|]; intros x [Hx _]; split; [exact Hx| exact I]);
      assert (UC2 : ucallerA depth_fopen_offline L mm sp s0 ra trC)
        by (eapply ucaller_keep; [exact UCb| lia|]; intros a Ha; destruct (AG2 a ltac:(lia) ltac:(split; [left; lia| exact I])) as [E1 _]; exact E1)
    end.
    rewrite app_nil_r in G2.
    assert (FRIN : forall a, (Fb <= a < Fb + 64)%Z -> in_frames ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) a)
      by (intros a Ha; apply in_frames_In; exists (FF_FOPEN_OFFLINE, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    assert (SHIN : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> in_frame_sh ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) a)
      by (intros a Ha; apply in_frame_sh_In; exists (FF_FOPEN_OFFLINE, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 64 3) with 8%Z; lia]).
    assert (EBL' : clocA ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CL EB 256) by (eapply clocA_incl; [exact EBL| apply incl_refl| apply incl_tl; apply incl_refl]).
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [_] [8; 4; 12; 4; 4]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
    cbn [app] in G2.
    destruct (rw_cells_cut _ _ _ 1 FRC) as [FK0 T1]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FK0, T1.
    destruct (rw_cells_cut _ _ _ 3 T1) as [_ T2]. clear T1. cbn [firstn skipn cells_size csize Nat.add] in T2.
    destruct (rw_cells_cut _ _ _ 1 T2) as [MGc T3]. clear T2. cbn [firstn skipn cells_size csize Nat.add] in MGc, T3.
    destruct (rw_cells_cut _ _ _ 1 T3) as [_ T4]. clear T3. cbn [firstn skipn cells_size csize Nat.add] in T4.
    destruct (rw_cells_cut _ _ _ 1 T4) as [ERRc T5]. clear T4. cbn [firstn skipn cells_size csize Nat.add] in ERRc, T5.
    destruct (rw_cells_cut _ _ _ 1 T5) as [_ FLG]. clear T5. cbn [firstn skipn cells_size csize Nat.add] in FLG.
    replace (Fb + Z.of_nat 8 + Z.of_nat 24)%Z with (Fb + 32)%Z in * by lia.
    replace (Fb + 32 + Z.of_nat 4 + Z.of_nat 12)%Z with (Fb + 48)%Z in * by lia.
    replace (Fb + 48 + Z.of_nat 4 + Z.of_nat 4)%Z with (Fb + 56)%Z in * by lia.
    (* [comment removed for export] *)
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G2) as [FAll2 _]. pose proof (Forall_inv FAll2) as FRM2. clear FAll2.
    pose proof (unp_of_sh_part _ _ _ 4%nat 0%nat 4 SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPM.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPM. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SiteMagic 32 G2 (or_introl eq_refl) eq_refl).
      replace (Fb + 32 + 0)%Z with (Fb + 32)%Z by lia.
      eapply FREAD with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := FA) (D := (Fb + 32)%Z) (n := 4%Z);
        [ split; [exact G2|]; rewrite Hspa; split; [exact ST1|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact MGc
        | split; [right; exists (FF_FOPEN_OFFLINE, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM2| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPM] ]. }
    intros got s2' RNG2 ms' PO. cbv beta in PO.
    (nd_pre PO 11%nat; intros FP2 av m4 junk' E OF2 MI2 ST2 AG3 G3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 3%nat; intros GLN GR MG2; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 544692)) with (Z_to_bv 64 544692) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    xf2 AG3 FR (left; lia). xf2 AG3 FRA (left; lia).
    xf2 AG3 FK0 (right; right; left; apply FRIN; lia). xf2 AG3 ERRc (right; right; left; apply FRIN; lia). xf2 AG3 FLG (right; right; left; apply FRIN; lia).
    xf2 AG3 SHC (right; right; right; apply SHIN; lia).
    xf2 AG3 HEB (eapply clocA_keeps; [exact EBL'| lia]).
    apply (agrees_stk _ _ _ _ _ AG3) in STG; [|intros a Ha; split; [left; lia| lia]].
    assert (AGx3 : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m m4).
    { eapply agrees_on_trans; [exact AGx|]. eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA); [exact G2| apply incl_refl| intros a K; exact K| lia| lia| exact AG3|].
      intros a NFr NEb. lia. }
    assert (UC3 : ucallerA depth_fopen_offline L m4 sp s0 ra trC)
      by (eapply ucaller_keep; [exact UC2| lia|]; intros a Ha; destruct (AG3 a ltac:(lia) ltac:(split; [left; lia| lia])) as [E1 _]; exact E1).
    clear MGc UNPM FRM2 G2 AG2 G1' AGx UC2 MI1 ST1 AG3 MU WM FSWR FWo.
    (* [comment removed for export] *)
    assert (FAIL : forall (RNGf : footprint) (mf : mem) (psf : PState H hptr) (msgf : list Z) (junk3 : list byte) (fraf : list cell) (k0f : word) (b0f b1f b2f b3f b4f b5f b6f b7f : byte)
                          (ra' t0f t1f t2f a0f a1f a2f a3f a4f a5f a6f a7f r19 r20 r21 r22 r23 t3f t4f t5f t6f : word),
      fp_le RNG2 RNGf -> mem_inv asegs mf -> stk asegs mf lo SPA -> stk asegs mf (SPA + 32) (bv_unsigned sp + -96) ->
      agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m mf ->
      GIOA L RNGf psf CL FB ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) mf ->
      rw_cells asegs mf SPA fraf -> cells_size fraf = 32%nat ->
      rw_cells asegs mf (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs mf Fb [C8 k0f] -> rw_cells asegs mf (Fb + 56) [C8 (Z_to_bv 64 (fflagA L FF_FOPEN_OFFLINE Fb))] ->
      rw_cells asegs mf (Z.shiftr Fb 3 + 2147450880) [C1 b0f; C1 b1f; C1 b2f; C1 b3f; C1 b4f; C1 b5f; C1 b6f; C1 b7f] ->
      rw_cells asegs mf EB [CB (length msgf + 1) (map b8 msgf ++ [Z_to_bv 8 0]); CB (255 - length msgf) junk3] -> Z.of_nat (length msgf) < 256 ->
      Forall (fun z => 0 < z < 256)%Z msgf -> ps_outfile psf = ps_outfile s ->
      implMG RNGf (fo_ret FO _ FF_FOPEN_OFFLINE (inl msgf)) psf POSTQ
        (MS (mkR ra' (Z_to_bv 64 SPA) gp tp t0f t1f t2f sp (Z_to_bv 64 SPA) a0f a1f a2f a3f a4f a5f a6f a7f
                 (Z_to_bv 64 Fb) r19 r20 r21 r22 r23 (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3f t4f t5f t6f)
            F (Z_to_bv 64 0x85278) fc None mf (seg_rom asegs))).
    { intros RNGf mf psf msgf junk3 fraf k0f b0f b1f b2f b3f b4f b5f b6f b7f ra' t0f t1f t2f a0f a1f a2f a3f a4f a5f a6f a7f r19 r20 r21 r22 r23 t3f t4f t5f t6f
             FPf MIf STf STGf AGf Gf FRAf FRASf FRf FKf FLGf SHCf HEBf LENf RNGMf OFf.
      clear FR FRA FK0 ERRc FLG SHC HEB STG MG2 MI2 ST2 G3 UC3 AGx3.
      pose proof (munch_refl ([] : list (Z * Z)) mf) as MUf. pose proof (wmono_refl asegs mf) as WMf.
      ienterG. zstep.
      apply evtF_done. eapply implMG_mono;
        [ eapply fo_epi with (L := L) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (SPA := SPA) (Fb := Fb);
          [ lia | exact SPA32 | lia | lia | lia | lia | exact Gf | exact MIf | exact STf | exact STGf | exact FRAf | exact FRASf | exact FRf | exact FKf | exact FLGf | exact SHCf
          | eapply rng_fp_le; [exact FPf| exact RSTK] ]
        | ].
      cbv beta. intros r s5' RNG5 ms5 PO. (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); rename ndR2__ into PO). destruct_exs PO.
      (destruct PO as (-> & ndR1__); nd_pre ndR1__ 7%nat; intros MI5 ST5 AG5 G5 OF5 LC5 TL5; nd_post).
      repeat match goal with Q := _ : _ -> _ -> footprint -> machine_state -> Prop |- _ => subst Q end. unfold open_result_post.
      split; [eapply fp_le_trans; [exact FP2| exact FPf]|].
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [congruence|].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGf| intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]
                                      | eapply agrees_on_weaken; [exact AG5| intros a [K _]; exact K]]. }
      exists junk3. split; [reflexivity|]. split; [reflexivity|]. split; [exact G5|].
      split; [eapply agrees_rw_cells; [exact AG5 | exact HEBf |]; intros a Ha; eapply clocA_keeps; [exact EBL|]; cbn [cells_size csize Nat.add] in Ha; lia |].
      split; [exact LENf| exact RNGMf]. }
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(EB, EB + 256)]%Z) by (apply Forall_cons; [exact EBBAND'| apply Forall_nil]).
    unfold zlength in *.
    destruct (Z.eq_dec (Z.of_nat (length got)) 4) as [L4|L4].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) L4). cbn [negb].
      apply implMG_bind_assoc.
      clear MG2 ERRc.
      pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      ienterG. zstep. rewrite (eqb_lits_false (Z.of_nat (length got)) 4) by lia. cbn [negb]. cbv iota.
      do 2 zstep. zstep.
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      apply evtF_done. eapply implMG_bind.
      { eapply FERROR with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := FA);
          [ split; [exact G3|]; rewrite Hspa; split; [exact ST2|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | exact HinF | reflexivity ]. }
      intros r ps3 RNG3 ms3 PO; cbv beta in PO; (nd_pre PO 9%nat; intros FP3 av3 m5 E MI3 ST3 AG4 G4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); rename ndR3__ into ERRNO).
      unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hspa in *; clear Hspa; subst spa.
      replace (ret_pc (Z_to_bv 64 545260)) with (Z_to_bv 64 545260) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      xf1 AG4 FR (left; lia). xf1 AG4 FRA (left; lia).
      xf1 AG4 FK0 (right; right; left; apply FRIN; lia). xf1 AG4 FLG (right; right; left; apply FRIN; lia).
      xf1 AG4 SHC (right; right; right; apply SHIN; lia).
      xf1 AG4 HEB (eapply clocA_keeps; [exact EBL'| lia]).
      apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; left; lia].
      assert (AGx4 : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m m5).
      { eapply agrees_on_trans; [exact AGx3|].
        eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA) (X := fun _ => True); [exact G3| apply incl_refl| intros a K; exact K| lia| lia| | intros; exact I].
        eapply agrees_on_weaken; [exact AG4| intros a [K _]; exact K]. }
      pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 (incl_tl _ (incl_refl _)) AGx4 FXB) as AGsh4.
      pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G4 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh4 ltac:(lia)) as OEB4.
      assert (OEB4' : cobjA RNG3 m5 ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CL EB 256)
        by (split; [exact EBL'| exact (proj2 OEB4)]).
      clear MI2 ST2 G3 AGx3 UC3 AG4 MU WM AGsh4 OEB4.
      destruct r.
      - (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
        (nd_pre (gl_tls _ _ _ GL _ _ _ _ _ _ _ G4 RTLS) 6%nat; intros T0 T47 TUNP TRNG (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) _; nd_post).
        assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
        assert (MSG : fmt_at m5 0x21380 "error reading dump file"%string)
          by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x21380 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
              split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
        apply implMG_errno_ll. set (e := lc_errno (ps_libc s2')) in *.
        pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
        cbn [Z.b2z]. ienterG. zstep. if_false.
        zstep. do 3 zstep. rewrite ETP.
        ck TUNP 4%Z 0x85204%Z [11%Z; 12%Z].
        zstep.
        do 4 zstep. zstep.
        replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
        remember (Z_to_bv 64 SPA) as spa eqn:Espa.
        assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
        apply evtF_done. eapply implMG_bind.
        { eapply FMT with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (EB := EB) (FMTA := 0x21380%Z) (e := e)
                          (fs := "error reading dump file"%string) (args := []) (junk := ej);
            [ split; [exact G4|]; rewrite Hspa; split; [exact ST3|]; split; [lia|]; split; [unfold PCAP_L1_STACK; lia|]; split; [lia|];
              split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
              split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
            | cbn [map]; intros [E|K]; [cbn in E; discriminate E| exact (NF FF_FMT_ERRMSG ltac:(unfold frames_fopen_offline; cbn; first [ clear; tauto | tauto ]) K)]
            | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia
            | cbn [length firstn]; constructor
            | exact HEB | exact OEB4' | exact E8 ]. }
        intros r sF RNG5 ms5 PO. cbv beta in PO. (nd_pre PO 2%nat; intros FP5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into PO). destruct_exs PO.
        (destruct PO as (-> & ndR1__); nd_pre ndR1__ 8%nat; intros OF5 LC5 TL5 MI5 ST5 AG5 G5 HEB5; nd_post).
        rewrite Hspa in *. clear Hspa. subst spa.
        replace (ret_pc (Z_to_bv 64 545308)) with (Z_to_bv 64 545308) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        repeat match goal with HR : rng RNG3 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP5) in HR end.
        xf2 AG5 FR (left; lia). xf2 AG5 FRA (left; lia).
        xf2 AG5 FK0 (right; right; left; apply FRIN; lia). xf2 AG5 FLG (right; right; left; apply FRIN; lia).
        xf2 AG5 SHC (right; right; right; apply SHIN; lia).
        apply (agrees_stk _ _ _ _ _ AG5) in STG; [|intros a Ha; split; [left; lia| lia]].
        lazymatch type of AG5 with agrees_on _ _ ?mm => pose proof (munch_refl ([] : list (Z * Z)) mm) as MU5; pose proof (wmono_refl asegs mm) as WM5 end.
        clear MU WM MI3 ST3 HEB EN2 TUNP TA7.
        ienterG. zstep.
        apply evtF_done. eapply FAIL with (msgf := fmt_errmsg "error reading dump file" [] e);
          [ eapply fp_le_trans; [exact FP3| exact FP5] | exact MI5 | exact ST5 | exact STG
          | eapply agrees_on_trans; [exact AGx4|]; eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA);
              [exact G4| apply incl_refl| intros a K; exact K| lia| lia| exact AG5| intros a NFr NEb; exact NEb]
          | exact G5 | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC | exact HEB5
          | pose proof (fmt_errmsg_length "error reading dump file"%string [] e); lia
          | apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor] | congruence ].
      - (* [comment removed for export] *)
        apply implMG_retb.
        assert (MSG : fmt_at m5 0x213c0 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string)
          by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x213c0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %zu file header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                   MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
              split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
        pose proof (munch_refl [(SPA - 16384, SPA); (EB, EB + 256)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
        cbn [Z.b2z]. ienterG. zstep. if_true.
        do 6 zstep. zstep.
        remember (Z_to_bv 64 SPA) as spa eqn:Espa.
        assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
        eapply evtF_cut.
        { eapply SNPRINTF with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (DST := EB) (n := 256%Z) (FMTA := 0x213c0%Z)
                               (fs := "truncated dump file; tried to read %zu file header bytes, only got %zu"%string) (args := [AInt 4; AInt (Z.of_nat (length got))]) (junk := ej);
            [ split; [exact G4|]; rewrite Hspa; split; [exact ST3|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
              split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
              split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
            | reflexivity | reflexivity | reflexivity | lia | exact MSG | vm_compute; reflexivity | cbn; lia
            | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
            | exact HEB | exact OEB4' ]. }
        cbv beta. intros ms' PO. (nd_pre PO 9%nat; intros av6 m6 junk6 E MU6 WM6 MI6 ST6 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into HEB6).
        unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
        replace (ret_pc (Z_to_bv 64 545400)) with (Z_to_bv 64 545400) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        unfold STDIO_STACK in MU6.
        pose proof G4 as G4'. rewrite <- (app_nil_r CL) in G4'.
        assert (FWs : Forall (own_ivA [(FF_FOPEN_OFFLINE, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA - 16384, SPA)]%Z) by own_ivs.
        assert (FXs : Forall (cobj_iv FL CL) [(EB, EB + 256)]%Z) by cobj_ivs.
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m6 _ _ _ FWs FXs G4' MU6 WM6 ltac:(lia)) as [G6 AG6].
        rewrite app_nil_r in G6.
        clear HEB.
        transport_after_call asegs m5 m6 MU6 WM6.
        change (Z.to_nat 256) with 256%nat in HEB6.
        lazymatch type of HEB6 with context [(256 - length ?X - 1)%nat] => replace (256 - length X - 1)%nat with (255 - length X)%nat in HEB6 by lia end.
        cbn [app] in G6.
        apply evtF_done. eapply FAIL with (msgf := Msg.trunc_file_header 4 (Z.of_nat (length got)));
          [ exact FP3 | exact MI6 | exact ST6 | exact STG
          | eapply agrees_on_trans; [exact AGx4| exact AG6]
          | exact G6 | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC | exact HEB6
          | pose proof (snprintf_length 256 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 4; AInt (Z.of_nat (length got))]) as LS;
            change (Z.to_nat (256 - 1)) with 255%nat in LS; unfold Msg.trunc_file_header, PCAP_ERRBUF_SIZE; lia
          | unfold Msg.trunc_file_header; apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] | congruence ]. }
    (* [comment removed for export] *)
    assert (FOUND : forall (RNGf : footprint) (mf : mem) (psf : PState H hptr) (P : Z) (PB : list (@cblock hptr)) (p : pcap hptr hptr) (e3 : list byte)
                           (fraf : list cell) (k0f : word) (b0f b1f b2f b3f b4f b5f b6f b7f : byte)
                           (ra' t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f r19 r21 r22 r23 t3f t4f t5f t6f : word),
      pc_rfile p = f -> fp_le RNG2 RNGf -> mem_inv asegs mf -> stk asegs mf lo SPA -> stk asegs mf (SPA + 32) (bv_unsigned sp + -96) ->
      agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m mf ->
      GIOA L RNGf psf (CL ++ PB) FB ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) mf -> pre_PCAPR (hptr:=hptr) P p PB mf ->
      rw_cells asegs mf SPA fraf -> cells_size fraf = 32%nat ->
      rw_cells asegs mf (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs mf Fb [C8 k0f] -> rw_cells asegs mf (Fb + 56) [C8 (Z_to_bv 64 (fflagA L FF_FOPEN_OFFLINE Fb))] ->
      rw_cells asegs mf (Z.shiftr Fb 3 + 2147450880) [C1 b0f; C1 b1f; C1 b2f; C1 b3f; C1 b4f; C1 b5f; C1 b6f; C1 b7f] ->
      rw_cells asegs mf EB [CB 256 e3] -> ps_outfile psf = ps_outfile s ->
      implMG RNGf (mbind (s_fileno HO f) (fun _ => fo_ret FO _ FF_FOPEN_OFFLINE (inr p))) psf POSTQ
        (MS (mkR ra' (Z_to_bv 64 SPA) gp tp t0f t1f t2f sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) a1f a2f a3f a4f a5f a6f a7f
                 (Z_to_bv 64 Fb) r19 (Z_to_bv 64 FA) r21 r22 r23 (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3f t4f t5f t6f)
            F (Z_to_bv 64 0x84fd8) fc None mf (seg_rom asegs))).
    { intros RNGf mf psf P PB p e3 fraf k0f b0f b1f b2f b3f b4f b5f b6f b7f ra' t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f r19 r21 r22 r23 t3f t4f t5f t6f
             RFf FPf MIf STf STGf AGf Gf PPCf FRAf FRASf FRf FKf FLGf SHCf HEBf OFf.
      clear FR FRA FK0 ERRc FLG SHC HEB STG MG2 MI2 ST2 G3 UC3 AGx3 FAIL.
      (nd_pre PPCf 7%nat; intros rf st os Lrf Lst Los (B & Ib & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
      assert (HinP : In (pc_self p, P, psize p) ((CL ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ Gf HinP) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOPb & P2) P1 PUNP PRNG PRSH PAR; nd_post).
      cbn [cb_addr cb_size fst snd] in PBAND, P3, PTOPb, P2, P1, PUNP, PRNG, PRSH, PAR. band_ind PBAND bP.
      pose proof (psize_pos p) as PS.
      repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FPf) in HR end.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
      hide PRIV. hide BUF. hide IFS. hide HEBf.
      assert (FWP : Forall (own_ivA [(FF_FOPEN_OFFLINE, Fb, 64%Z)] PB (bv_unsigned sp)) [(P, P + 648)]%Z).
      { apply Forall_cons; [|apply Forall_nil]. right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      pose proof (munch_refl [(P, P + 648)]%Z mf) as MUf. pose proof (wmono_refl asegs mf) as WMf.
      (* [comment removed for export] *)
      cut_cells CELLS 1%nat X0 P. cut_cells CELLS 9%nat X1 P. cut_cells CELLS 1%nat X2 P. cut_cells CELLS 1%nat X3 P.
      cut_cells CELLS 5%nat X4 P. cut_cells CELLS 1%nat X5 P. cut_cells CELLS 3%nat X6 P. cut_cells CELLS 1%nat X7 P.
      cut_cells CELLS 6%nat X8 P. cut_cells CELLS 1%nat X9 P. cut_cells CELLS 1%nat X10 P. cut_cells CELLS 1%nat X11 P.
      cut_cells CELLS 1%nat X12 P. rename CELLS into X13.
      (nd_pre (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (pc_self p, P, psize p) (FF_FOPEN_OFFLINE, Fb, 64%Z) Gf HinP (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kP kPr kP1 kP2; nd_post).
      cbn [cb_addr cb_size fb_addr fb_size fst snd] in kP1, kP2.
      ienterG.
      zstep.
      ck0 PUNP; ck_go.
      do 2 zstep.
      ck0 PUNP; ck_go.
      do 3 zstep.
      zstep.
      (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FWP (Forall_nil _) Gf MUf WMf ltac:(lia)) as [G5 AG5];
        assert (AGo5 : agrees_on (fun a => outside [(P, P + 648)]%Z a) mf mm) by (eapply agrees_on_of_munch; [exact MUf | exact WMf | intros a _ Ho; exact Ho])
      end.
      cbn [app] in G5.
      assert (HinPa : forall a, (P <= a < P + 648)%Z -> in_block (CL ++ PB) a).
      { intros a Ha. apply in_block_app. right. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      apply evtF_done. eapply implMG_bind.
      { eapply FILENO with (L := L) (s := psf) (CL := CL ++ PB) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := FA);
          [ split; [exact G5|]; rewrite Hspa; split; [exact STf|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | exact HinF | reflexivity ]. }
      intros fd ps5 RNG5 ms5 PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP5 av5 m7 E MI5 ST5 AG6 G6 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); rename ndR3__ into Hfd).
      unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hspa in *. clear Hspa. subst spa.
      replace (ret_pc (Z_to_bv 64 544788)) with (Z_to_bv 64 544788) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat match goal with HR : rng RNGf _ _ |- _ => apply (rng_fp_le _ _ _ _ FP5) in HR end.
      xf1 AG6 FRf (left; lia). xf1 AG6 FRAf (left; rewrite FRASf in *; lia).
      xf1 AG6 FKf (right; right; left; apply FRIN; lia). xf1 AG6 FLGf (right; right; left; apply FRIN; lia).
      xf1 AG6 SHCf (right; right; right; apply SHIN; lia).
      apply (agrees_stk _ _ _ _ _ AG6) in STGf; [|intros a Ha; left; lia].
      xf1 AG6 X0 (right; left; apply HinPa; lia). xf1 AG6 X1 (right; left; apply HinPa; lia). xf1 AG6 X2 (right; left; apply HinPa; lia).
      xf1 AG6 X3 (right; left; apply HinPa; lia). xf1 AG6 X4 (right; left; apply HinPa; lia). xf1 AG6 X5 (right; left; apply HinPa; lia).
      xf1 AG6 X6 (right; left; apply HinPa; lia). xf1 AG6 X7 (right; left; apply HinPa; lia). xf1 AG6 X8 (right; left; apply HinPa; lia).
      xf1 AG6 X9 (right; left; apply HinPa; lia). xf1 AG6 X10 (right; left; apply HinPa; lia). xf1 AG6 X11 (right; left; apply HinPa; lia).
      xf1 AG6 X12 (right; left; apply HinPa; lia). xf1 AG6 X13 (right; left; apply HinPa; lia).
      clear PUNP MIf STf MUf WMf.
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G6 HinP) as ndP__; nd_pre ndP__ 4%nat; intros _ _ PUNP _; nd_post). cbn [cb_addr cb_size fst snd] in PUNP.
      pose proof (GOTL _ _ _ _ _ _ _ G6) as GOT. unfold GOT_PCAP_ADDR, GOT_INSTALL_BPF, GOT_BREAKLOOP, PK in GOT. cbn [pk_oneshot pk_cleanup_sf] in GOT.
      pose proof (munch_refl [(P, P + 648)]%Z m7) as MU7. pose proof (wmono_refl asegs m7) as WM7.
      ienterG.
      do 2 zstep.
      ck0 PUNP; ck_go.
      do 2 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 2 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 3 zstep.
      ck0 PUNP; ck_go.
      do 3 zstep.
      (* [comment removed for export] *)
      merge_all X3. merge_all X5. merge_all X7. merge_all X9.
      join_cells X0 X1. join_cells X0 X2. join_cells X0 X3. join_cells X0 X4. join_cells X0 X5. join_cells X0 X6. join_cells X0 X7.
      join_cells X0 X8. join_cells X0 X9. join_cells X0 X10. join_cells X0 X11. join_cells X0 X12. join_cells X0 X13.
      rename X0 into CELLS.
      unhide PRIV. unhide BUF. unhide IFS. unhide HEBf.
      pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ Gf EPB) as [APB API].
      (pose proof WF as ndP__; nd_pre ndP__ 4%nat; intros _ _ W3 _; nd_post).
      assert (HinPB : In (pc_self p, P, psize p) PB) by (rewrite EPB; left; reflexivity).
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ Gf EBL' HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kq kqr kq1 kq2; nd_post).
      cbn [cb_addr cb_size fst snd] in kq1, kq2.
      assert (EBL2 : clocA ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (CL ++ PB) EB 256) by (eapply clocA_incl; [exact EBL'| apply incl_appl; apply incl_refl| apply incl_refl]).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FWP (Forall_nil _) G6 MU7 WM7 ltac:(lia)) as [G8 AG8];
        assert (AGo8 : agrees_on (fun a => outside [(P, P + 648)]%Z a) m7 mm) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]);
        assert (AGX : agrees_on (fun a => in_block (CL ++ PB) a /\ ~ (P <= a < P + 648))%Z mf mm)
          by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGo5|]; intros a [_ Hn]; cbn [outside]; split; [exact Hn| exact I]|];
              eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG6|]; intros a [Ha _]; right; left; exact Ha|];
              eapply agrees_on_weaken; [exact AGo8|]; intros a [_ Hn]; cbn [outside]; split; [exact Hn| exact I]);
        assert (HEB8 : rw_cells asegs mm EB [CB 256 e3])
          by (eapply agrees_rw_cells; [exact AGo8|
                eapply agrees_rw_cells; [exact AG6| eapply agrees_rw_cells; [exact AGo5| exact HEBf| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]
                                        | intros a Ha; eapply clocA_keeps; [exact EBL2| cbn [cells_size csize Nat.add] in Ha; lia]]
                | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
        destruct (pcap_aux_agree p P B Ib pad bs mf mm _ AGX) as (BUF' & PRIV' & IFS'); [ | | | lia | exact BUF | exact PRIV | exact IFS |]
      end.
      { intros a Ha. split; [apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| lia]. }
      { intros a Ha. unfold PCAP_PRIV_OFF in Ha. split; [apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| lia]. }
      { intros sg q Hq a Ha. destruct (API sg q Hq) as [X1' X2'].
        split; [apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; rewrite Hq; do 2 apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| lia]. }
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (PC8 : PCAPR P p PB FB mm) end.
      { exists FA. split; [rewrite RFf; exact HinF|]. exists B, Ib. eexists (mkPJ _ _ _ _ _ _ _ _ _ _ _). exists pad, bs.
        split; [exact EPB|].
        split; [unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF, PK; cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_stats pk_oneshot]; exact CELLS|].
        split; [exact PRIV'|]. split; [exact BUF'|]. split; [exact PFX|]. split; [exact IFS'| exact WF]. }
      cbn [app] in G8.
      apply evtF_done. eapply implMG_mono;
        [ eapply fo_epi with (L := L) (CL := CL ++ PB) (FB := FB) (FL := FL) (lo := lo) (SPA := SPA) (Fb := Fb);
          [ lia | exact SPA32 | lia | lia | lia | lia | exact G8 | assumption | exact ST5 | exact STGf | exact FRAf | exact FRASf | exact FRf | exact FKf | exact FLGf | exact SHCf
          | exact RSTK ]
        | ].
      cbv beta. intros r s9' RNG9 ms9 PO. (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); rename ndR2__ into PO). destruct_exs PO.
      (destruct PO as (-> & ndR1__); nd_pre ndR1__ 7%nat; intros MI9 ST9 AG9 G9 OF9 LC9 TL9; nd_post).
      repeat match goal with Q := _ : _ -> _ -> footprint -> machine_state -> Prop |- _ => subst Q end. unfold open_result_post.
      split; [eapply fp_le_trans; [exact FP2|]; eapply fp_le_trans; [exact FPf| exact FP5]|].
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 P), mm, FB end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [congruence|].
      split; [assumption|]. split; [assumption|].
      split.
      { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGf| intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]|].
        eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5| intros a [K _]; split; [exact K| exact I]]|].
        eapply agrees_on_trans; [eapply agrees_on_weaken; [eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA) (X := fun _ => True) (CL := CL) (CLk := CL ++ PB);
                                    [exact Gf| apply incl_appl; apply incl_refl| intros a K; apply in_block_app; left; exact K| lia| lia
                                    | eapply agrees_on_weaken; [exact AG6| intros a [K _]; exact K] | intros; exact I]
                                 | intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]|].
        eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG8| intros a [K _]; split; [exact K| exact I]]|].
        eapply agrees_on_weaken; [exact AG9|]. intros a [K _].
        destruct K as [K|[K|[K|K]]]; [left; exact K| right; left; apply in_block_app; left; exact K| right; right; left; exact K| right; right; right; exact K]. }
      exists P, PB. split; [reflexivity|]. split; [split; [reflexivity| exact RFf]|].
      split; [exact G9|].
      split; [eapply PCAPR_agree; [exact AG9| intros a Ha; right; left; apply in_block_app; right; exact Ha| exact PC8]|].
      exists e3. eapply agrees_rw_cells; [exact AG9| exact HEB8|]. intros a Ha.
      eapply clocA_keeps; [eapply clocA_incl; [exact EBL| apply incl_appl; apply incl_refl| apply incl_refl]|]. cbn [cells_size csize Nat.add] in Ha; lia. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) L4). cbn [negb].
    destruct (rw_cells_cut _ _ _ 1 MG2) as [MG _]. clear MG2. cbn [firstn] in MG.
    replace (length got) with 4%nat in MG by lia.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    pose proof (unp_of_sh_part _ _ _ 4%nat 0%nat 4 SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPM.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPM. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPM.
    pose proof (unp_of_sh_part _ _ _ 6%nat 0%nat 4 SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPE.
    change (8 * Z.of_nat 6)%Z with 48%Z in UNPE. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPE.
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 (incl_tl _ (incl_refl _)) AGx3 FXB) as AGsh3.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G3 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh3 ltac:(lia)) as OEB3.
    assert (OEB3' : cobjA RNG2 m4 ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CL EB 256) by (split; [exact EBL'| exact (proj2 OEB3)]).
    pose proof (rw_cells_nth_C8 _ _ _ 10%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BRA.
    cbn [firstn cells_size csize Nat.add] in BS0, BRA.
    replace (bv_unsigned sp + -96 + Z.of_nat 80)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
    replace (bv_unsigned sp + -96 + Z.of_nat 88)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
    assert (FRINc : forall A n, (Fb <= A)%Z -> (A + n <= Fb + 64)%Z -> clocA ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CL A n)
      by (intros A n H1 H2; right; exists (FF_FOPEN_OFFLINE, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    ienterG. zstep. rewrite L4. if_false. do 6 zstep. zstep.
    (* [comment removed for export] *)
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (chk_any false) with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (MG := (Fb + 32)%Z) (FA := FA)
                                  (EB := EB) (ERR := (Fb + 48)%Z) (f := f) (magic := got) (ej := ej) (fuel := O) (trC := bv_unsigned ra :: trC);
        [ split; [exact G3|]; rewrite Hspa; split; [exact ST2|]; split; [lia|]; split; [unfold PCAP_L2_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x84fd4%Z UC3); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
              | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_fopen_offline, depth_pcap_check_header; lia]
        | rewrite unsigned_lit by lia; exact TRC
        | unfold frames_check_header; apply nofr_cons; [eapply nofr_sub; [exact NF| unfold frames_fopen_offline, frames_pcap_check_header; intros ff Hf; cbn in Hf |- *; clear - Hf; intuition]
                                                       | cbn; clear; intuition congruence]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | exact MG | exact GR | lia | exact HEB | exact ERRc | reflexivity
        | split; [apply FRINc; lia|]; eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPM]
        | split; [apply FRINc; lia|]; eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPE]
        | lia | exact OEB3' | lia | lia | Z.div_mod_to_equations; lia | exact E8 ]. }
    intros r1 ps3 RNG3 ms3 PO; unfold check_header_post in PO;
      (nd_pre PO 12%nat; intros FP3 av3 m5 errw E OF3 MI3 ST3 AG4 MG3 ERR3 REST; nd_post).
    unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hspa in *; clear Hspa; subst spa.
    replace (ret_pc (Z_to_bv 64 544724)) with (Z_to_bv 64 544724) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    xf3 AG4 FR (left; lia). xf3 AG4 FRA (left; lia).
    xf3 AG4 FK0 (right; right; left; apply FRIN; lia). xf3 AG4 FLG (right; right; left; apply FRIN; lia).
    xf3 AG4 SHC (right; right; right; apply SHIN; lia).
    apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| split; lia]].
    assert (AGx4 : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m m5).
    { eapply agrees_on_trans; [exact AGx3|]. eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA); [exact G3| apply incl_refl| intros a K; exact K| lia| lia| exact AG4|].
      intros a NFr NEb. split; [exact NEb| lia]. }
    assert (UC4 : ucallerA depth_fopen_offline L m5 sp s0 ra trC)
      by (eapply ucaller_keep; [exact UC3| lia|]; intros a Ha; destruct (AG4 a ltac:(lia) ltac:(split; [left; lia| split; lia])) as [E1 _]; exact E1).
    clear MG ERRc HEB UNPM UNPE FRM3 AGsh3 OEB3 OEB3' BS0 BRA MI2 ST2 MU WM UC3 AGx3 AG4 G3.
    assert (FP23 : fp_le RNG2 RNG3) by exact FP3.
    destruct r1 as [|msg|p].
    - (* [comment removed for export] *)
      (destruct REST as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros G4 [e3 HEB3]; nd_post).
      destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G4) as [FAll4 _]. pose proof (Forall_inv FAll4) as FRM4. clear FAll4.
      pose proof (unp_of_sh_part _ _ _ 4%nat 0%nat 4 SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPM.
      change (8 * Z.of_nat 4)%Z with 32%Z in UNPM. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPM.
      pose proof (unp_of_sh_part _ _ _ 6%nat 0%nat 4 SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPE.
      change (8 * Z.of_nat 6)%Z with 48%Z in UNPE. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPE.
      pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G4 (incl_tl _ (incl_refl _)) AGx4 FXB) as AGsh4.
      pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G4 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh4 ltac:(lia)) as OEB4.
      assert (OEB4' : cobjA RNG3 m5 ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CL EB 256) by (split; [exact EBL'| exact (proj2 OEB4)]).
      pose proof (rw_cells_nth_C8 _ _ _ 10%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BRA.
      cbn [firstn cells_size csize Nat.add] in BS0, BRA.
      replace (bv_unsigned sp + -96 + Z.of_nat 80)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
      replace (bv_unsigned sp + -96 + Z.of_nat 88)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
      pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
      ienterG. zstep. if_true.
      zstep.
      replace (sx32 z64) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
      zstep. if_false.
      do 5 zstep. zstep.
      (* [comment removed for export] *)
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      apply evtF_done. eapply implMG_bind.
      { eapply (chk_any true) with (L := L) (s := ps3) (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (MG := (Fb + 32)%Z) (FA := FA)
                                   (EB := EB) (ERR := (Fb + 48)%Z) (f := f) (magic := got) (ej := e3) (fuel := fuel) (trC := bv_unsigned ra :: trC);
          [ split; [exact G4|]; rewrite Hspa; split; [exact ST3|]; split; [lia|]; split; [unfold PCAP_L2_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x85240%Z UC4); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_fopen_offline, depth_pcap_ng_check_header; lia]
          | rewrite unsigned_lit by lia; exact TRN
          | unfold frames_check_header; apply nofr_cons; [eapply nofr_sub; [exact NF| unfold frames_fopen_offline, frames_pcap_ng_check_header; intros ff Hf; cbn in Hf |- *; clear - Hf; intuition]
                                                         | cbn; clear; intuition congruence]
          | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | exact MG3 | exact GR | lia | exact HEB3 | exact ERR3 | reflexivity
          | split; [apply FRINc; lia|]; eapply frameA_aobj; [exact FRM4| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPM]
          | split; [apply FRINc; lia|]; eapply frameA_aobj; [exact FRM4| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPE]
          | lia | exact OEB4' | lia | lia | Z.div_mod_to_equations; lia | exact E8 ]. }
      intros r2 ps5 RNG5 ms5 PO; unfold check_header_post in PO;
        (nd_pre PO 12%nat; intros FP5 av5 m6 errw5 E OF5 MI5 ST5 AG5 MG5 ERR5 REST5; nd_post).
      unfold hpost_regs in E; destruct_exs E; subst ms5; rewrite Hspa in *; clear Hspa; subst spa.
      replace (ret_pc (Z_to_bv 64 545344)) with (Z_to_bv 64 545344) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat match goal with HR : rng RNG3 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP5) in HR end.
      xf3 AG5 FR (left; lia). xf3 AG5 FRA (left; lia).
      xf3 AG5 FK0 (right; right; left; apply FRIN; lia). xf3 AG5 FLG (right; right; left; apply FRIN; lia).
      xf3 AG5 SHC (right; right; right; apply SHIN; lia).
      apply (agrees_stk _ _ _ _ _ AG5) in STG; [|intros a Ha; split; [left; lia| split; lia]].
      assert (AGx5 : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m m6).
      { eapply agrees_on_trans; [exact AGx4|]. eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA); [exact G4| apply incl_refl| intros a K; exact K| lia| lia| exact AG5|].
        intros a NFr NEb. split; [exact NEb| lia]. }
      assert (FP25 : fp_le RNG2 RNG5) by (eapply fp_le_trans; [exact FP3| exact FP5]).
      clear MG3 HEB3 UNPM UNPE FRM4 AGsh4 OEB4 OEB4' BS0 BRA MI3 ST3 MU WM UC4 AGx4 AG5 ERR3.
      destruct r2 as [|msg|p].
      + (* [comment removed for export] *)
        (destruct REST5 as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros G5 [e5 HEB5]; nd_post).
        apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [20; 236]%nat) in HEB5; [|reflexivity]. cbn [mk_CB_cells app] in HEB5.
        destruct (rw_cells_cut _ _ _ 1 HEB5) as [EB1 EB2]. clear HEB5. cbn [firstn skipn cells_size csize Nat.add] in EB1, EB2.
        replace (EB + Z.of_nat 20)%Z with (EB + 20)%Z in EB2 by lia.
        set (UFF := [Z_to_bv 8 117; Z_to_bv 8 110; Z_to_bv 8 107; Z_to_bv 8 110; Z_to_bv 8 111; Z_to_bv 8 119; Z_to_bv 8 110; Z_to_bv 8 32; Z_to_bv 8 102; Z_to_bv 8 105;
                     Z_to_bv 8 108; Z_to_bv 8 101; Z_to_bv 8 32; Z_to_bv 8 102; Z_to_bv 8 111; Z_to_bv 8 114; Z_to_bv 8 109; Z_to_bv 8 97; Z_to_bv 8 116; Z_to_bv 8 0]).
        assert (MSGB : bytes_at asegs m6 0x21440 UFF)
          by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m6 0x21440 UFF MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))).
        assert (EUFF : map b8 Msg.unknown_file_format ++ [Z_to_bv 8 0] = UFF) by (vm_compute; reflexivity).
        pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G5) as (RT5 & _).
        pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G5 (incl_tl _ (incl_refl _)) AGx5 FXB) as AGsh5.
        pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G5 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh5 ltac:(lia)) as OEB5.
        pose proof (munch_refl [(SPA - 2224, SPA); (EB, EB + 20)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
        ienterG. zstep. if_false.
        zstep. replace (sx32 z64) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
        zstep. if_false.
        do 4 zstep. zstep. zstep.
        remember (Z_to_bv 64 SPA) as spa eqn:Espa.
        assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
        eapply evtF_cut.
        { eapply (asan_memcpy_specZ RNG5 _ spa) with (lo := lo) (Dst := EB) (Src := 0x21440%Z) (n := 20%Z) (src := UFF) (junk := firstn 20 e5);
            [ reflexivity | reflexivity | reflexivity | exact MI5 | rewrite Hspa; exact ST5 | rewrite Hspa; lia | lia | exact RT5 | exact MSGB | reflexivity | lia | exact EB1 | lia
            | eapply (gia_global_mobjA _ _ _ GL); [exact G5 | unfold client_globals; repeat (first [left; reflexivity | right]) | exact RIMG | exact RISH]
            | eapply mobjA_sub; [apply aobjA_mobjA; [exact (proj2 OEB5)| lia]| lia| lia| lia]
            | first [lia | atop_facts; lia] | lia | exact RIMG | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] ]. }
        cbv beta. intros ms' PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 6%nat; intros MU7 WM7 MI7 ST7 HD7 SRC7; nd_post).
        rewrite Hspa in *. clear Hspa. subst spa.
        replace (ret_pc (Z_to_bv 64 545244)) with (Z_to_bv 64 545244) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        pose proof G5 as G5'. rewrite <- (app_nil_r CL) in G5'.
        assert (FWs : Forall (own_ivA [(FF_FOPEN_OFFLINE, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA - 2224, SPA)]%Z) by own_ivs.
        assert (FXs : Forall (cobj_iv FL CL) [(EB, EB + 20)]%Z).
        { apply Forall_cons; [|apply Forall_nil]. split; [cbn [fst snd]| cbn [fst snd]; lia]. replace (EB + 20 - EB)%Z with 20%Z by lia.
          destruct EBL as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]; [left; exists b| right; exists fr]; (split; [assumption|]; split; lia). }
        lazymatch type of MU7 with munch _ _ ?mm =>
          destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWs FXs G5' MU7 WM7 ltac:(lia)) as [G7 AG7] end.
        rewrite app_nil_r in G7. cbn [app] in G7.
        lazymatch type of MU7 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU7 WM7 end.
        change (Z.to_nat 20) with 20%nat in HD7.
        pose proof (rw_cells_uncut _ _ _ _ _ HD7 EB2 ltac:(reflexivity)) as HEB7. rewrite <- EUFF in HEB7. cbn [app] in HEB7.
        zstep.
        apply evtF_done. eapply FAIL with (msgf := Msg.unknown_file_format) (junk3 := firstn 236 (skipn 20 e5));
          [ exact FP25 | exact MI7 | exact ST7 | exact STG
          | eapply agrees_on_trans; [exact AGx5|]; eapply agrees_on_weaken; [exact AG7|]; intros a [K N]; split; [exact K|]; cbn [outside] in *; split; [lia| exact I]
          | exact G7 | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC | exact HEB7
          | vm_compute; reflexivity | vm_compute; repeat constructor | congruence ].
      + (* [comment removed for export] *)
        (nd_pre REST5 2%nat; intros junk5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); nd_pre ndR3__ 4%nat; intros G5 HEB5 LEN5 RNGM5; nd_post).
        pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
        ienterG. zstep. if_false.
        zstep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
        zstep. if_true.
        apply evtF_done. eapply FAIL with (msgf := msg);
          [ exact FP25 | exact MI5 | exact ST5 | exact STG | exact AGx5 | exact G5 | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC | exact HEB5
          | exact LEN5 | exact RNGM5 | congruence ].
      + (* [comment removed for export] *)
        (nd_pre REST5 3%nat; intros P PB ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros G5 PPC RF [e5 HEB5]; nd_post).
        (pose proof PPC as ndP__; nd_pre ndP__ 7%nat; intros rf0 st0 os0 _ _ _ (B0 & I0 & jq0 & pad0 & bs0 & EPB0 & _); nd_post).
        (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 ltac:(apply in_or_app; left; apply in_or_app; right; rewrite EPB0; left; reflexivity)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & PT0 & _) P0 _; nd_post).
        cbn [cb_addr cb_size fst snd] in P0, PT0. pose proof (psize_pos p) as PS0.
        pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
        ienterG. zstep. if_true_by (nez_true P ltac:(lia)).
        apply evtF_done. eapply FOUND with (P := P) (PB := PB) (e3 := e5);
          [ exact RF | exact FP25 | exact MI5 | exact ST5 | exact STG | exact AGx5 | exact G5 | exact PPC | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC
          | exact HEB5 | congruence ].
    - (* [comment removed for export] *)
      (nd_pre REST 2%nat; intros junk4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); nd_pre ndR3__ 4%nat; intros G4 HEB4 LEN4 RNGM4; nd_post).
      pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
      ienterG. zstep. if_true.
      zstep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
      zstep. if_true.
      apply evtF_done. eapply FAIL with (msgf := msg);
        [ exact FP23 | exact MI3 | exact ST3 | exact STG | exact AGx4 | exact G4 | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC | exact HEB4
        | exact LEN4 | exact RNGM4 | congruence ].
    - (* [comment removed for export] *)
      (nd_pre REST 3%nat; intros P PB ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros G4 PPC RF [e4 HEB4]; nd_post).
      (pose proof PPC as ndP__; nd_pre ndP__ 7%nat; intros rf0 st0 os0 _ _ _ (B0 & I0 & jq0 & pad0 & bs0 & EPB0 & _); nd_post).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 ltac:(apply in_or_app; left; apply in_or_app; right; rewrite EPB0; left; reflexivity)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & PT0 & _) P0 _; nd_post).
      cbn [cb_addr cb_size fst snd] in P0, PT0. pose proof (psize_pos p) as PS0.
      pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
      ienterG. zstep. if_false_by (eqz_false P ltac:(lia)).
      apply evtF_done. eapply FOUND with (P := P) (PB := PB) (e3 := e4);
        [ exact RF | exact FP23 | exact MI3 | exact ST3 | exact STG | exact AGx4 | exact G4 | exact PPC | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC
        | exact HEB4 | congruence ].
  Qed.
  End Sz8.
  Theorem fopen_offline_proofA : ltac:(let t := eval cbv delta [fopen_offline_proofA__stmt] in fopen_offline_proofA__stmt in exact t).
  Proof using CHK_NG CHK_PCAP FENTER0 FERROR FILENO FMT FREAD FRET GL GOTL SNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo FA EB f ej fuel. ltac2:(SecDiet.SzSec.closeP 'fopen_offline_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FopenOffline.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
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
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

(* [comment removed for export] *)
Tactic Notation "xf1" constr(AG) hyp(HH) tactic3(loc) :=
  apply (agrees_rw_cells _ _ _ _ _ AG) in HH;
  [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add] in Ha; loc].
Tactic Notation "xf2" constr(AG) hyp(HH) tactic3(loc) :=
  apply (agrees_rw_cells _ _ _ _ _ AG) in HH;
  [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [loc| lia]].
Tactic Notation "xf3" constr(AG) hyp(HH) tactic3(loc) :=
  apply (agrees_rw_cells _ _ _ _ _ AG) in HH;
  [| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [loc| split; lia]].

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
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells ?s ?m ?A1 ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    let J := fresh "J" in
    pose proof (rw_cells_uncut m A1 cs1 cs2 A2 H1 H2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J;
    clear H1 H2; cbn [app] in J; rename J into H1
  end end.

Lemma land_m32F : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Open Scope bv_scope.
Definition fmt_errmsg_length__stmt : Prop := forall f args e, (length (fmt_errmsg f args e) <= 255)%nat.
Section Sz2.
Variables f args e : ltac2:(SecDiet.SzSec.tyM 'fmt_errmsg_length__stmt "vvv" @f).
Lemma fmt_errmsg_length__body : ltac2:(SecDiet.SzSec.bodyP 'fmt_errmsg_length__stmt "vvv").
Proof using .
 unfold fmt_errmsg, snprintf, snprintf_out, PCAP_ERRBUF_SIZE, zlength.
  set (mm := firstn (Z.to_nat (256 - 1)) (fmt_output (fmt f) args)).
  assert (Hm : (length mm <= 255)%nat) by (subst mm; rewrite length_firstn; apply Nat.le_min_l).
  destruct (256 <? Z.of_nat (length mm) + 3)%Z eqn:E; [exact Hm|].
  apply Z.ltb_ge in E. rewrite !length_app, length_firstn. cbn [length str String.list_ascii_of_string map].
  unfold str. cbn [String.list_ascii_of_string map length]. lia.
Qed.
End Sz2.
Lemma fmt_errmsg_length : ltac:(let t := eval cbv delta [fmt_errmsg_length__stmt] in fmt_errmsg_length__stmt in exact t).
Proof. intros f args e. ltac2:(SecDiet.SzSec.closeP 'fmt_errmsg_length__body "vvv"). Qed.
Lemma snprintf_length : forall n f a, (length (Fmt.snprintf n f a) <= Z.to_nat (n - 1))%nat.
Proof. intros. unfold Fmt.snprintf, snprintf_out. apply firstn_le_length. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section FopenOffline.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GOTL : gia_got_law GIOA.
  Hypothesis FENTER0 : fenter_stmt_o FO GIOA fflagA 0 STACK_MALLOC_0.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FILENO : fileno_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis CHK_PCAP : pcap_check_header_stmt HO FO sites GIOA TP.
  Hypothesis CHK_NG : pcap_ng_check_header_stmt HO FO sites GIOA TP.
  Lemma chk_any : forall ng, check_header_stmt_for HO FO sites GIOA TP ng.
  Proof using CHK_NG CHK_PCAP. intros [|]; [exact CHK_NG | exact CHK_PCAP]. Qed.

  Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof using . intros B C f g s RNG Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  Definition callee_ag__stmt : Prop := forall L RNG s (CLg FB : list (@cblock hptr)) FL m0 Fb SPA SP (CL CLk : list (@cblock hptr)) (X : Z -> Prop) EB (mA mB : mem),
    GIOA L RNG s CLg FB ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) m0 -> incl CL CLg -> (forall a, in_block CL a -> in_block CLk a) ->
    (ATOP <= SP)%Z -> (SPA <= SP)%Z ->
    agrees_on (fun a => client_keeps ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CLk SPA a /\ X a) mA mB ->
    (forall a, ~ (Fb <= a < Fb + 64)%Z -> ~ (EB <= a < EB + 256)%Z -> X a) ->
    agrees_on (fun a => client_keeps FL CL SP a /\ outside [(EB, EB + 256)%Z] a) mA mB.
  Section Sz6.
  Variables L RNG s CLg FB FL m0 Fb SPA SP CL CLk X EB mA mB : ltac2:(SecDiet.SzSec.tyM 'callee_ag__stmt "vvvvvvvvvvvvvvvv" @L).
  Lemma callee_ag__body : ltac2:(SecDiet.SzSec.bodyP 'callee_ag__stmt "vvvvvvvvvvvvvvvv").
  Proof using GL.
    intros G IC IB HSP HSPA AG HX.
 eapply agrees_on_weaken; [exact AG|]. intros a [K [NE _]].
    destruct (keeps_not_own_frame _ _ _ GL _ _ _ _ _ _ _ (FF_FOPEN_OFFLINE, Fb, 64%Z) CL SP a G IC HSP K) as [NF1 _].
    cbn [fb_addr fb_size fst snd] in NF1.
    split; [| apply HX; assumption].
    destruct K as [K|[K|[K|K]]]; [left; lia| right; left; apply IB; exact K| right; right; left; apply in_frames_cons; exact K
                                 | right; right; right; apply in_frame_sh_cons; exact K].
  Qed.
  End Sz6.
  Lemma callee_ag : ltac:(let t := eval cbv delta [callee_ag__stmt] in callee_ag__stmt in exact t).
  Proof using GL. intros L RNG s CLg FB FL m0 Fb SPA SP CL CLk X EB mA mB. ltac2:(SecDiet.SzSec.closeP 'callee_ag__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fo_epi__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (s : PState H hptr) (CL FB : list (@cblock hptr)) (FL : list fblock) (lo SPA Fb : Z) (m : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 s11 t3 t4 t5 t6 : word)
      (k0 : word) (fra : list cell) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
      (A : Type) (x : A),
    (bv_unsigned sp - 159 <= SPA <= bv_unsigned sp - 128)%Z -> (SPA mod 32 = 0)%Z -> (ATOP + 4096 <= lo)%Z -> (lo <= SPA)%Z ->
    (bv_unsigned sp + 16 < al_top L)%Z -> (al_top L <= 2^47)%Z ->
    GIOA L RNG s CL FB ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) m -> mem_inv asegs m ->
    stk asegs m lo SPA -> stk asegs m (SPA + 32) (bv_unsigned sp + -96) ->
    rw_cells asegs m SPA fra -> cells_size fra = 32%nat ->
    rw_cells asegs m (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m Fb [C8 k0] ->
    rw_cells asegs m (Fb + 56) [C8 (Z_to_bv 64 (fflagA L FF_FOPEN_OFFLINE Fb))] ->
    rw_cells asegs m (Z.shiftr Fb 3 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
    rng RNG lo (al_top L - lo) ->
    implMG RNG (fo_ret FO _ FF_FOPEN_OFFLINE x) s
      (fun r s' RNG' ms' => r = x /\ RNG' = RNG /\ exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIOA L RNG s' CL FB FL m' /\ ps_outfile s' = ps_outfile s /\ ps_libc s' = ps_libc s /\ ps_tls s' = ps_tls s)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 Fb) r19 r20 r21 r22 r23 (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x85344) fc None m (seg_rom asegs)).
  Section Sz7.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 F fc L RNG s CL FB FL lo SPA Fb m ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 s11 t3 t4 t5 t6 k0 fra b0 b1 b2 b3 b4 b5 b6 b7 A x : ltac2:(SecDiet.SzSec.tyM 'fo_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fo_epi__body : ltac2:(SecDiet.SzSec.bodyP 'fo_epi__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FRET GL.
 intros SPAB SPA32 LO LOS SPT TOP47 G MI ST STG FRA FRAS FRs FK0 FLG SHC RSTK.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FAll _]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND FTOP F64 _ FRNG FSRNG _ _; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND, FTOP, F64, FRNG, FSRNG. clear FAll. change (Z.shiftr 64 3) with 8%Z in FSRNG.
    (pose proof (ablk_lin _ _ FBAND) as ndP__; nd_pre ndP__ 4%nat; intros _ Fb0 _ _; nd_post). band_ind FBAND bF.
    (nd_pre (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G) 6%nat; intros _ FLR FLB FLT _ (kF & kFr & kF1 & kF2); nd_post). band_ind FLB bG.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    assert (FW : Forall (own_ivA [(FF_FOPEN_OFFLINE, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    pose proof (munch_refl [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    burst_begin [(Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z [Fb; (Fb + 56)%Z; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    zstep. neg_lits.
    do 2 zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    do 4 zstep. zstep_sh0. do 3 zstep.
    burst_end MUb WMb.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FW (Forall_nil _) G' MU WM ltac:(lia)) as [G5 AG5];
      pose proof (munch_refl [(fflagA L FF_FOPEN_OFFLINE Fb, fflagA L FF_FOPEN_OFFLINE Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    rewrite app_nil_r in G5.
    destruct (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) as (FLC & _).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kF kFr kF1 kF2 bF bFr bFhi bFlo bFimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 15 zstep.
    release_frame FRA ST (SPA + 32)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST STG ltac:(lia)) as ST3. clear ST STG.
    release_frame FRs ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CL (bv_unsigned sp) G5 MU2 WM2 (incl_refl _) ltac:(lia)) as [AG6 _].
    apply evtF_done. subst POSTQ. cbv beta iota.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists mm end.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a K; split; [exact K| exact I] | exact AG6]. }
    split; [exact G6|]. split; [exact OF3|]. split; [exact LC3| exact TL3].
  Qed.
  End Sz7.
  Lemma fo_epi : ltac:(let t := eval cbv delta [fo_epi__stmt] in fo_epi__stmt in exact t).
  Proof using FRET GL. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 F fc L RNG s CL FB FL lo SPA Fb m ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r19 r20 r21 r22 r23 s11 t3 t4 t5 t6 k0 fra b0 b1 b2 b3 b4 b5 b6 b7 A x. ltac2:(SecDiet.SzSec.closeP 'fo_epi__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fopen_offline_proofA__stmt : Prop := fopen_offline_stmt HO FO sites GIOA TP.
  Section Sz8.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo FA EB f ej fuel : ltac2:(SecDiet.SzSec.tyM 'fopen_offline_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fopen_offline_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_offline_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CHK_NG CHK_PCAP FENTER0 FERROR FILENO FMT FREAD FRET GL GOTL SNPRINTF.
 intros PRE UC TR NF HinF -> -> -> HEB OEB E8.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    unfold PCAP_L3_STACK in BU. (nd_pre TR 3%nat; intros TRC TRM TRN; nd_post).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    rng_sp_window RSTK sp RSPW.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as ndP__; nd_pre ndP__ 3%nat; intros (FABAND & _ & FATOP & _) FA1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in FABAND, FATOP, FA1. unfold FILE_BLOCK in FABAND, FATOP. pose proof (ablk_lin _ _ FABAND) as (FAIMG & _). unfold AIMG_HI in FAIMG. clear FABAND.
    pose proof (proj1 OEB) as EBL.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL ltac:(lia)) as EBBAND. pose proof EBBAND as EBBAND'. band_ind EBBAND bE.
    remember (bv_unsigned sp - 128 - (bv_unsigned sp - 128) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 159 <= SPA <= bv_unsigned sp - 128 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -128) - (bv_unsigned sp + -128) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof G as G'. rewrite <- (app_nil_r CL) in G'.
    assert (MIe : hidc (mem_inv asegs m)) by exact MI.
    assert (HEBe : hidc (rw_cells asegs m EB [CB 256 ej])) by exact HEB.
    unfold pcap_fopen_offline_with_tstamp_precision, read_fail_msg, errmsg_for_errno.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_fread e_ferror e_fileno e_last_errno prims]. unfold PCAP_FOPEN_OFFLINE_WTP_ENTRY.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 96%nat ST. carve_frame 32%nat ST.
    zstep.
    do 12 zstep.
    zstep.
    zstep.
    rewrite land_m32F by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -96)%Z.
    destruct (stk_split asegs _ lo (SPA + 32) (bv_unsigned sp + -96) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 32) 32 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 32) with 32%Z in STL, FRA. replace (SPA + 32 - 32)%Z with SPA in STL, FRA by lia.
    do 5 zstep.
    do 2 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 2 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FWS : Forall (client_ivA FL CL) [(bv_unsigned sp - 160, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s CL FB FL mm) by (eapply (gl_client_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FWS]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ CL [] _ FL []); [exact G' | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FWS G'.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER0 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { apply NF. unfold frames_fopen_offline. cbn. first [ clear; tauto | tauto ]. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_FOPEN_OFFLINE) with 64%Z in *.
    change (Z.to_nat (64 - 32)) with 32%nat in *. change (Z.to_nat (64 / 8)) with 8%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 544692)) with (Z_to_bv 64 544692) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
    assert (UCb : ucallerA depth_fopen_offline L m2 sp s0 ra trC)
      by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha; destruct (AGb a ltac:(lia) ltac:(left; lia)) as [E1 _]; exact E1).
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 8 <= 0x10007fff8000
                   /\ (Fb + 64 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 8 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    burst_begin [(SPA, SPA + 32); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z [SPA; Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 4 zstep.
    zstep. neg_lits.
    zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    do 2 zstep.
    do 4 zstep.
    zstep. neg_lits.
    zstep_sh0.
    do 3 zstep.
    zstep.
    burst_end MUb WMb.
    zstep. if_false_by (eqz_false FA ltac:(lia)).
    do 5 zstep.
    zstep.
    (* [comment removed for export] *)
    clear GOT SHB SUA GSU.
    pose proof G1 as G1'. rewrite <- (app_nil_r CL) in G1'.
    assert (FWo : Forall (own_ivA [(FF_FOPEN_OFFLINE, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 160, bv_unsigned sp); (Fb, Fb + 64); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 8)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FWo (Forall_nil _) G1' MU WM ltac:(lia)) as [G2 AG2];
      assert (AGx : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m mm)
        by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb| intros x [Hx _]; exact Hx]|];
            eapply agrees_on_weaken; [exact AG2|]; intros x [Hx _]; split; [exact Hx| exact I]);
      assert (UC2 : ucallerA depth_fopen_offline L mm sp s0 ra trC)
        by (eapply ucaller_keep; [exact UCb| lia|]; intros a Ha; destruct (AG2 a ltac:(lia) ltac:(split; [left; lia| exact I])) as [E1 _]; exact E1)
    end.
    rewrite app_nil_r in G2.
    assert (FRIN : forall a, (Fb <= a < Fb + 64)%Z -> in_frames ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) a)
      by (intros a Ha; apply in_frames_In; exists (FF_FOPEN_OFFLINE, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    assert (SHIN : forall a, (Z.shiftr Fb 3 + 2147450880 <= a < Z.shiftr Fb 3 + 2147450880 + 8)%Z -> in_frame_sh ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) a)
      by (intros a Ha; apply in_frame_sh_In; exists (FF_FOPEN_OFFLINE, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 64 3) with 8%Z; lia]).
    assert (EBL' : clocA ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CL EB 256) by (eapply clocA_incl; [exact EBL| apply incl_refl| apply incl_tl; apply incl_refl]).
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [_] [8; 4; 12; 4; 4]%nat) in FRC; [|reflexivity]. cbn [mk_CB_cells app] in FRC.
    cbn [app] in G2.
    destruct (rw_cells_cut _ _ _ 1 FRC) as [FK0 T1]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in FK0, T1.
    destruct (rw_cells_cut _ _ _ 3 T1) as [_ T2]. clear T1. cbn [firstn skipn cells_size csize Nat.add] in T2.
    destruct (rw_cells_cut _ _ _ 1 T2) as [MGc T3]. clear T2. cbn [firstn skipn cells_size csize Nat.add] in MGc, T3.
    destruct (rw_cells_cut _ _ _ 1 T3) as [_ T4]. clear T3. cbn [firstn skipn cells_size csize Nat.add] in T4.
    destruct (rw_cells_cut _ _ _ 1 T4) as [ERRc T5]. clear T4. cbn [firstn skipn cells_size csize Nat.add] in ERRc, T5.
    destruct (rw_cells_cut _ _ _ 1 T5) as [_ FLG]. clear T5. cbn [firstn skipn cells_size csize Nat.add] in FLG.
    replace (Fb + Z.of_nat 8 + Z.of_nat 24)%Z with (Fb + 32)%Z in * by lia.
    replace (Fb + 32 + Z.of_nat 4 + Z.of_nat 12)%Z with (Fb + 48)%Z in * by lia.
    replace (Fb + 48 + Z.of_nat 4 + Z.of_nat 4)%Z with (Fb + 56)%Z in * by lia.
    (* [comment removed for export] *)
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G2) as [FAll2 _]. pose proof (Forall_inv FAll2) as FRM2. clear FAll2.
    pose proof (unp_of_sh_part _ _ _ 4%nat 0%nat 4 SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPM.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPM. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SiteMagic 32 G2 (or_introl eq_refl) eq_refl).
      replace (Fb + 32 + 0)%Z with (Fb + 32)%Z by lia.
      eapply FREAD with (L := L) (s := s1') (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := FA) (D := (Fb + 32)%Z) (n := 4%Z);
        [ split; [exact G2|]; rewrite Hspa; split; [exact ST1|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact MGc
        | split; [right; exists (FF_FOPEN_OFFLINE, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM2| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPM] ]. }
    intros got s2' RNG2 ms' PO. cbv beta in PO.
    (nd_pre PO 11%nat; intros FP2 av m4 junk' E OF2 MI2 ST2 AG3 G3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 3%nat; intros GLN GR MG2; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 544872)) with (Z_to_bv 64 544872) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    xf2 AG3 FR (left; lia). xf2 AG3 FRA (left; lia).
    xf2 AG3 FK0 (right; right; left; apply FRIN; lia). xf2 AG3 ERRc (right; right; left; apply FRIN; lia). xf2 AG3 FLG (right; right; left; apply FRIN; lia).
    xf2 AG3 SHC (right; right; right; apply SHIN; lia).
    xf2 AG3 HEB (eapply clocA_keeps; [exact EBL'| lia]).
    apply (agrees_stk _ _ _ _ _ AG3) in STG; [|intros a Ha; split; [left; lia| lia]].
    assert (AGx3 : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m m4).
    { eapply agrees_on_trans; [exact AGx|]. eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA); [exact G2| apply incl_refl| intros a K; exact K| lia| lia| exact AG3|].
      intros a NFr NEb. lia. }
    assert (UC3 : ucallerA depth_fopen_offline L m4 sp s0 ra trC)
      by (eapply ucaller_keep; [exact UC2| lia|]; intros a Ha; destruct (AG3 a ltac:(lia) ltac:(split; [left; lia| lia])) as [E1 _]; exact E1).
    clear MGc UNPM FRM2 G2 AG2 G1' AGx UC2 MI1 ST1 AG3 MU WM FSWR FWo.
    (* [comment removed for export] *)
    assert (FAIL : forall (RNGf : footprint) (mf : mem) (psf : PState H hptr) (msgf : list Z) (junk3 : list byte) (fraf : list cell) (k0f : word) (b0f b1f b2f b3f b4f b5f b6f b7f : byte)
                          (ra' t0f t1f t2f a0f a1f a2f a3f a4f a5f a6f a7f r19 r20 r21 r22 r23 t3f t4f t5f t6f : word),
      fp_le RNG2 RNGf -> mem_inv asegs mf -> stk asegs mf lo SPA -> stk asegs mf (SPA + 32) (bv_unsigned sp + -96) ->
      agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m mf ->
      GIOA L RNGf psf CL FB ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) mf ->
      rw_cells asegs mf SPA fraf -> cells_size fraf = 32%nat ->
      rw_cells asegs mf (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs mf Fb [C8 k0f] -> rw_cells asegs mf (Fb + 56) [C8 (Z_to_bv 64 (fflagA L FF_FOPEN_OFFLINE Fb))] ->
      rw_cells asegs mf (Z.shiftr Fb 3 + 2147450880) [C1 b0f; C1 b1f; C1 b2f; C1 b3f; C1 b4f; C1 b5f; C1 b6f; C1 b7f] ->
      rw_cells asegs mf EB [CB (length msgf + 1) (map b8 msgf ++ [Z_to_bv 8 0]); CB (255 - length msgf) junk3] -> Z.of_nat (length msgf) < 256 ->
      Forall (fun z => 0 < z < 256)%Z msgf -> ps_outfile psf = ps_outfile s ->
      implMG RNGf (fo_ret FO _ FF_FOPEN_OFFLINE (inl msgf)) psf POSTQ
        (MS (mkR ra' (Z_to_bv 64 SPA) gp tp t0f t1f t2f sp (Z_to_bv 64 SPA) a0f a1f a2f a3f a4f a5f a6f a7f
                 (Z_to_bv 64 Fb) r19 r20 r21 r22 r23 (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3f t4f t5f t6f)
            F (Z_to_bv 64 0x85340) fc None mf (seg_rom asegs))).
    { intros RNGf mf psf msgf junk3 fraf k0f b0f b1f b2f b3f b4f b5f b6f b7f ra' t0f t1f t2f a0f a1f a2f a3f a4f a5f a6f a7f r19 r20 r21 r22 r23 t3f t4f t5f t6f
             FPf MIf STf STGf AGf Gf FRAf FRASf FRf FKf FLGf SHCf HEBf LENf RNGMf OFf.
      clear FR FRA FK0 ERRc FLG SHC HEB STG MG2 MI2 ST2 G3 UC3 AGx3.
      pose proof (munch_refl ([] : list (Z * Z)) mf) as MUf. pose proof (wmono_refl asegs mf) as WMf.
      ienterG. zstep.
      apply evtF_done. eapply implMG_mono;
        [ eapply fo_epi with (L := L) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (SPA := SPA) (Fb := Fb);
          [ lia | exact SPA32 | lia | lia | lia | lia | exact Gf | exact MIf | exact STf | exact STGf | exact FRAf | exact FRASf | exact FRf | exact FKf | exact FLGf | exact SHCf
          | eapply rng_fp_le; [exact FPf| exact RSTK] ]
        | ].
      cbv beta. intros r s5' RNG5 ms5 PO. (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); rename ndR2__ into PO). destruct_exs PO.
      (destruct PO as (-> & ndR1__); nd_pre ndR1__ 7%nat; intros MI5 ST5 AG5 G5 OF5 LC5 TL5; nd_post).
      repeat match goal with Q := _ : _ -> _ -> footprint -> machine_state -> Prop |- _ => subst Q end. unfold open_result_post.
      split; [eapply fp_le_trans; [exact FP2| exact FPf]|].
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 0), mm, FB end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [congruence|].
      split; [assumption|]. split; [assumption|].
      split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGf| intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]
                                      | eapply agrees_on_weaken; [exact AG5| intros a [K _]; exact K]]. }
      exists junk3. split; [reflexivity|]. split; [reflexivity|]. split; [exact G5|].
      split; [eapply agrees_rw_cells; [exact AG5 | exact HEBf |]; intros a Ha; eapply clocA_keeps; [exact EBL|]; cbn [cells_size csize Nat.add] in Ha; lia |].
      split; [exact LENf| exact RNGMf]. }
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(EB, EB + 256)]%Z) by (apply Forall_cons; [exact EBBAND'| apply Forall_nil]).
    unfold zlength in *.
    destruct (Z.eq_dec (Z.of_nat (length got)) 4) as [L4|L4].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) L4). cbn [negb].
      apply implMG_bind_assoc.
      clear MG2 ERRc.
      pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      ienterG. zstep. rewrite (eqb_lits_false (Z.of_nat (length got)) 4) by lia. cbn [negb]. cbv iota.
      do 2 zstep. zstep.
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      apply evtF_done. eapply implMG_bind.
      { eapply FERROR with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := FA);
          [ split; [exact G3|]; rewrite Hspa; split; [exact ST2|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | exact HinF | reflexivity ]. }
      intros r ps3 RNG3 ms3 PO; cbv beta in PO; (nd_pre PO 9%nat; intros FP3 av3 m5 E MI3 ST3 AG4 G4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); rename ndR3__ into ERRNO).
      unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hspa in *; clear Hspa; subst spa.
      replace (ret_pc (Z_to_bv 64 545448)) with (Z_to_bv 64 545448) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      xf1 AG4 FR (left; lia). xf1 AG4 FRA (left; lia).
      xf1 AG4 FK0 (right; right; left; apply FRIN; lia). xf1 AG4 FLG (right; right; left; apply FRIN; lia).
      xf1 AG4 SHC (right; right; right; apply SHIN; lia).
      xf1 AG4 HEB (eapply clocA_keeps; [exact EBL'| lia]).
      apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; left; lia].
      assert (AGx4 : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m m5).
      { eapply agrees_on_trans; [exact AGx3|].
        eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA) (X := fun _ => True); [exact G3| apply incl_refl| intros a K; exact K| lia| lia| | intros; exact I].
        eapply agrees_on_weaken; [exact AG4| intros a [K _]; exact K]. }
      pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 (incl_tl _ (incl_refl _)) AGx4 FXB) as AGsh4.
      pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G4 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh4 ltac:(lia)) as OEB4.
      assert (OEB4' : cobjA RNG3 m5 ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CL EB 256)
        by (split; [exact EBL'| exact (proj2 OEB4)]).
      clear MI2 ST2 G3 AGx3 UC3 AG4 MU WM AGsh4 OEB4.
      destruct r.
      - (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN2 ER]. clear ERRNO.
        (nd_pre (gl_tls _ _ _ GL _ _ _ _ _ _ _ G4 RTLS) 6%nat; intros T0 T47 TUNP TRNG (RLO & RHI & TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8) _; nd_post).
        assert (ETP : bv_unsigned tp = ATP) by (rewrite TPE; unfold ATP; pose proof atp_lin; apply unsigned_lit; lia).
        assert (MSG : fmt_at m5 0x21380 "error reading dump file"%string)
          by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x21380 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
              split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
        apply implMG_errno_ll. set (e := lc_errno (ps_libc s2')) in *.
        pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
        cbn [Z.b2z]. ienterG. zstep. if_false.
        zstep. do 3 zstep. rewrite ETP.
        (* [comment removed for export] *)
        pose proof ATPv_pg as TPG. pose proof atp_lin as ((TPLO & _) & _).
        assert (ERN : (0 < ATP + -164 < 2^64)%Z) by (unfold ATP; atop_facts; lia).
        zstep. if_false_by (eqz_false (ATP + -164) ERN).
        zstep. replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
        zstep. if_false.
        ck TUNP 4%Z 0x852cc%Z [11%Z; 12%Z].
        zstep.
        do 4 zstep. zstep.
        replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
        remember (Z_to_bv 64 SPA) as spa eqn:Espa.
        assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
        apply evtF_done. eapply implMG_bind.
        { eapply FMT with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (EB := EB) (FMTA := 0x21380%Z) (e := e)
                          (fs := "error reading dump file"%string) (args := []) (junk := ej);
            [ split; [exact G4|]; rewrite Hspa; split; [exact ST3|]; split; [lia|]; split; [unfold PCAP_L1_STACK; lia|]; split; [lia|];
              split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
              split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
            | cbn [map]; intros [E|K]; [cbn in E; discriminate E| exact (NF FF_FMT_ERRMSG ltac:(unfold frames_fopen_offline; cbn; first [ clear; tauto | tauto ]) K)]
            | reflexivity | reflexivity | reflexivity | lia | reflexivity | exact MSG | reflexivity | cbn; lia
            | cbn [length firstn]; constructor
            | exact HEB | exact OEB4' | exact E8 ]. }
        intros r sF RNG5 ms5 PO. cbv beta in PO. (nd_pre PO 2%nat; intros FP5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into PO). destruct_exs PO.
        (destruct PO as (-> & ndR1__); nd_pre ndR1__ 8%nat; intros OF5 LC5 TL5 MI5 ST5 AG5 G5 HEB5; nd_post).
        rewrite Hspa in *. clear Hspa. subst spa.
        replace (ret_pc (Z_to_bv 64 545508)) with (Z_to_bv 64 545508) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        repeat match goal with HR : rng RNG3 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP5) in HR end.
        xf2 AG5 FR (left; lia). xf2 AG5 FRA (left; lia).
        xf2 AG5 FK0 (right; right; left; apply FRIN; lia). xf2 AG5 FLG (right; right; left; apply FRIN; lia).
        xf2 AG5 SHC (right; right; right; apply SHIN; lia).
        apply (agrees_stk _ _ _ _ _ AG5) in STG; [|intros a Ha; split; [left; lia| lia]].
        lazymatch type of AG5 with agrees_on _ _ ?mm => pose proof (munch_refl ([] : list (Z * Z)) mm) as MU5; pose proof (wmono_refl asegs mm) as WM5 end.
        clear MU WM MI3 ST3 HEB EN2 TUNP TA7.
        ienterG. zstep.
        apply evtF_done. eapply FAIL with (msgf := fmt_errmsg "error reading dump file" [] e);
          [ eapply fp_le_trans; [exact FP3| exact FP5] | exact MI5 | exact ST5 | exact STG
          | eapply agrees_on_trans; [exact AGx4|]; eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA);
              [exact G4| apply incl_refl| intros a K; exact K| lia| lia| exact AG5| intros a NFr NEb; exact NEb]
          | exact G5 | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC | exact HEB5
          | pose proof (fmt_errmsg_length "error reading dump file"%string [] e); lia
          | apply fmt_errmsg_ok; [vm_compute; reflexivity| constructor] | congruence ].
      - (* [comment removed for export] *)
        apply implMG_retb.
        assert (MSG : fmt_at m5 0x213c0 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string)
          by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x213c0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %zu file header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                   MI3 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
              split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
        pose proof (munch_refl [(SPA - 16384, SPA); (EB, EB + 256)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
        cbn [Z.b2z]. ienterG. zstep. if_true.
        do 6 zstep. zstep.
        remember (Z_to_bv 64 SPA) as spa eqn:Espa.
        assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
        eapply evtF_cut.
        { eapply SNPRINTF with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (DST := EB) (n := 256%Z) (FMTA := 0x213c0%Z)
                               (fs := "truncated dump file; tried to read %zu file header bytes, only got %zu"%string) (args := [AInt 4; AInt (Z.of_nat (length got))]) (junk := ej);
            [ split; [exact G4|]; rewrite Hspa; split; [exact ST3|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
              split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
              split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
            | reflexivity | reflexivity | reflexivity | lia | exact MSG | vm_compute; reflexivity | cbn; lia
            | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
            | exact HEB | exact OEB4' ]. }
        cbv beta. intros ms' PO. (nd_pre PO 9%nat; intros av6 m6 junk6 E MU6 WM6 MI6 ST6 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into HEB6).
        unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
        replace (ret_pc (Z_to_bv 64 545600)) with (Z_to_bv 64 545600) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        unfold STDIO_STACK in MU6.
        pose proof G4 as G4'. rewrite <- (app_nil_r CL) in G4'.
        assert (FWs : Forall (own_ivA [(FF_FOPEN_OFFLINE, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA - 16384, SPA)]%Z) by own_ivs.
        assert (FXs : Forall (cobj_iv FL CL) [(EB, EB + 256)]%Z) by cobj_ivs.
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ m6 _ _ _ FWs FXs G4' MU6 WM6 ltac:(lia)) as [G6 AG6].
        rewrite app_nil_r in G6.
        clear HEB.
        transport_after_call asegs m5 m6 MU6 WM6.
        change (Z.to_nat 256) with 256%nat in HEB6.
        lazymatch type of HEB6 with context [(256 - length ?X - 1)%nat] => replace (256 - length X - 1)%nat with (255 - length X)%nat in HEB6 by lia end.
        cbn [app] in G6.
        apply evtF_done. eapply FAIL with (msgf := Msg.trunc_file_header 4 (Z.of_nat (length got)));
          [ exact FP3 | exact MI6 | exact ST6 | exact STG
          | eapply agrees_on_trans; [exact AGx4| exact AG6]
          | exact G6 | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC | exact HEB6
          | pose proof (snprintf_length 256 "truncated dump file; tried to read %zu file header bytes, only got %zu"%string [AInt 4; AInt (Z.of_nat (length got))]) as LS;
            change (Z.to_nat (256 - 1)) with 255%nat in LS; unfold Msg.trunc_file_header, PCAP_ERRBUF_SIZE; lia
          | unfold Msg.trunc_file_header; apply snprintf_ok; [vm_compute; reflexivity| apply args_ok_ints2] | congruence ]. }
    (* [comment removed for export] *)
    assert (FOUND : forall (RNGf : footprint) (mf : mem) (psf : PState H hptr) (P : Z) (PB : list (@cblock hptr)) (p : pcap hptr hptr) (e3 : list byte)
                           (fraf : list cell) (k0f : word) (b0f b1f b2f b3f b4f b5f b6f b7f : byte)
                           (ra' t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f r19 r21 r22 r23 t3f t4f t5f t6f : word),
      pc_rfile p = f -> fp_le RNG2 RNGf -> mem_inv asegs mf -> stk asegs mf lo SPA -> stk asegs mf (SPA + 32) (bv_unsigned sp + -96) ->
      agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m mf ->
      GIOA L RNGf psf (CL ++ PB) FB ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) mf -> pre_PCAPR (hptr:=hptr) P p PB mf ->
      rw_cells asegs mf SPA fraf -> cells_size fraf = 32%nat ->
      rw_cells asegs mf (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs mf Fb [C8 k0f] -> rw_cells asegs mf (Fb + 56) [C8 (Z_to_bv 64 (fflagA L FF_FOPEN_OFFLINE Fb))] ->
      rw_cells asegs mf (Z.shiftr Fb 3 + 2147450880) [C1 b0f; C1 b1f; C1 b2f; C1 b3f; C1 b4f; C1 b5f; C1 b6f; C1 b7f] ->
      rw_cells asegs mf EB [CB 256 e3] -> ps_outfile psf = ps_outfile s ->
      implMG RNGf (mbind (s_fileno HO f) (fun _ => fo_ret FO _ FF_FOPEN_OFFLINE (inr p))) psf POSTQ
        (MS (mkR ra' (Z_to_bv 64 SPA) gp tp t0f t1f t2f sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) a1f a2f a3f a4f a5f a6f a7f
                 (Z_to_bv 64 Fb) r19 (Z_to_bv 64 FA) r21 r22 r23 (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 2147450880) s11 t3f t4f t5f t6f)
            F (Z_to_bv 64 0x8508c) fc None mf (seg_rom asegs))).   (* [comment removed for export] *)
    { intros RNGf mf psf P PB p e3 fraf k0f b0f b1f b2f b3f b4f b5f b6f b7f ra' t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f r19 r21 r22 r23 t3f t4f t5f t6f
             RFf FPf MIf STf STGf AGf Gf PPCf FRAf FRASf FRf FKf FLGf SHCf HEBf OFf.
      clear FR FRA FK0 ERRc FLG SHC HEB STG MG2 MI2 ST2 G3 UC3 AGx3 FAIL.
      (nd_pre PPCf 7%nat; intros rf st os Lrf Lst Los (B & Ib & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
      assert (HinP : In (pc_self p, P, psize p) ((CL ++ PB) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; rewrite EPB; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ Gf HinP) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOPb & P2) P1 PUNP PRNG PRSH PAR; nd_post).
      cbn [cb_addr cb_size fst snd] in PBAND, P3, PTOPb, P2, P1, PUNP, PRNG, PRSH, PAR. band_ind PBAND bP.
      pose proof (psize_pos p) as PS.
      repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FPf) in HR end.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF in CELLS. cbn [app] in CELLS.
      hide PRIV. hide BUF. hide IFS. hide HEBf.
      assert (FWP : Forall (own_ivA [(FF_FOPEN_OFFLINE, Fb, 64%Z)] PB (bv_unsigned sp)) [(P, P + 648)]%Z).
      { apply Forall_cons; [|apply Forall_nil]. right; left. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      pose proof (munch_refl [(P, P + 648)]%Z mf) as MUf. pose proof (wmono_refl asegs mf) as WMf.
      (* [comment removed for export] *)
      cut_cells CELLS 1%nat X0 P. cut_cells CELLS 9%nat X1 P. cut_cells CELLS 1%nat X2 P. cut_cells CELLS 1%nat X3 P.
      cut_cells CELLS 5%nat X4 P. cut_cells CELLS 1%nat X5 P. cut_cells CELLS 3%nat X6 P. cut_cells CELLS 1%nat X7 P.
      cut_cells CELLS 6%nat X8 P. cut_cells CELLS 1%nat X9 P. cut_cells CELLS 1%nat X10 P. cut_cells CELLS 1%nat X11 P.
      cut_cells CELLS 1%nat X12 P. rename CELLS into X13.
      (nd_pre (block_apart_frame _ _ _ GL _ _ _ _ _ _ _ (pc_self p, P, psize p) (FF_FOPEN_OFFLINE, Fb, 64%Z) Gf HinP (or_introl eq_refl) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kP kPr kP1 kP2; nd_post).
      cbn [cb_addr cb_size fb_addr fb_size fst snd] in kP1, kP2.
      ienterG.
      zstep. ub_al 7%Z ltac:(al16 P2). zstep. if_false.      (* [comment removed for export] *)
      zstep.
      ck0 PUNP; ck_go.
      do 2 zstep.
      ck0 PUNP; ck_go.
      do 3 zstep.
      zstep.
      (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FWP (Forall_nil _) Gf MUf WMf ltac:(lia)) as [G5 AG5];
        assert (AGo5 : agrees_on (fun a => outside [(P, P + 648)]%Z a) mf mm) by (eapply agrees_on_of_munch; [exact MUf | exact WMf | intros a _ Ho; exact Ho])
      end.
      cbn [app] in G5.
      assert (HinPa : forall a, (P <= a < P + 648)%Z -> in_block (CL ++ PB) a).
      { intros a Ha. apply in_block_app. right. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      apply evtF_done. eapply implMG_bind.
      { eapply FILENO with (L := L) (s := psf) (CL := CL ++ PB) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (f := f) (Af := FA);
          [ split; [exact G5|]; rewrite Hspa; split; [exact STf|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | exact HinF | reflexivity ]. }
      intros fd ps5 RNG5 ms5 PO. cbv beta in PO. (nd_pre PO 9%nat; intros FP5 av5 m7 E MI5 ST5 AG6 G6 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); rename ndR3__ into Hfd).
      unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hspa in *. clear Hspa. subst spa.
      replace (ret_pc (Z_to_bv 64 544976)) with (Z_to_bv 64 544976) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat match goal with HR : rng RNGf _ _ |- _ => apply (rng_fp_le _ _ _ _ FP5) in HR end.
      xf1 AG6 FRf (left; lia). xf1 AG6 FRAf (left; rewrite FRASf in *; lia).
      xf1 AG6 FKf (right; right; left; apply FRIN; lia). xf1 AG6 FLGf (right; right; left; apply FRIN; lia).
      xf1 AG6 SHCf (right; right; right; apply SHIN; lia).
      apply (agrees_stk _ _ _ _ _ AG6) in STGf; [|intros a Ha; left; lia].
      xf1 AG6 X0 (right; left; apply HinPa; lia). xf1 AG6 X1 (right; left; apply HinPa; lia). xf1 AG6 X2 (right; left; apply HinPa; lia).
      xf1 AG6 X3 (right; left; apply HinPa; lia). xf1 AG6 X4 (right; left; apply HinPa; lia). xf1 AG6 X5 (right; left; apply HinPa; lia).
      xf1 AG6 X6 (right; left; apply HinPa; lia). xf1 AG6 X7 (right; left; apply HinPa; lia). xf1 AG6 X8 (right; left; apply HinPa; lia).
      xf1 AG6 X9 (right; left; apply HinPa; lia). xf1 AG6 X10 (right; left; apply HinPa; lia). xf1 AG6 X11 (right; left; apply HinPa; lia).
      xf1 AG6 X12 (right; left; apply HinPa; lia). xf1 AG6 X13 (right; left; apply HinPa; lia).
      clear PUNP MIf STf MUf WMf.
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G6 HinP) as ndP__; nd_pre ndP__ 4%nat; intros _ _ PUNP _; nd_post). cbn [cb_addr cb_size fst snd] in PUNP.
      pose proof (GOTL _ _ _ _ _ _ _ G6) as GOT. unfold GOT_PCAP_ADDR, GOT_INSTALL_BPF, GOT_BREAKLOOP, PK in GOT. cbn [pk_oneshot pk_cleanup_sf] in GOT.
      pose proof (munch_refl [(P, P + 648)]%Z m7) as MU7. pose proof (wmono_refl asegs m7) as WM7.
      ienterG.
      do 2 zstep.
      ck0 PUNP; ck_go.
      do 2 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 2 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 4 zstep.
      ck0 PUNP; ck_go.
      do 3 zstep.
      ck0 PUNP; ck_go.
      do 3 zstep.
      (* [comment removed for export] *)
      merge_all X3. merge_all X5. merge_all X7. merge_all X9.
      join_cells X0 X1. join_cells X0 X2. join_cells X0 X3. join_cells X0 X4. join_cells X0 X5. join_cells X0 X6. join_cells X0 X7.
      join_cells X0 X8. join_cells X0 X9. join_cells X0 X10. join_cells X0 X11. join_cells X0 X12. join_cells X0 X13.
      rename X0 into CELLS.
      unhide PRIV. unhide BUF. unhide IFS. unhide HEBf.
      pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ Gf EPB) as [APB API].
      (pose proof WF as ndP__; nd_pre ndP__ 4%nat; intros _ _ W3 _; nd_post).
      assert (HinPB : In (pc_self p, P, psize p) PB) by (rewrite EPB; left; reflexivity).
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ Gf EBL' HinPB ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kq kqr kq1 kq2; nd_post).
      cbn [cb_addr cb_size fst snd] in kq1, kq2.
      assert (EBL2 : clocA ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (CL ++ PB) EB 256) by (eapply clocA_incl; [exact EBL'| apply incl_appl; apply incl_refl| apply incl_refl]).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ FWP (Forall_nil _) G6 MU7 WM7 ltac:(lia)) as [G8 AG8];
        assert (AGo8 : agrees_on (fun a => outside [(P, P + 648)]%Z a) m7 mm) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]);
        assert (AGX : agrees_on (fun a => in_block (CL ++ PB) a /\ ~ (P <= a < P + 648))%Z mf mm)
          by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGo5|]; intros a [_ Hn]; cbn [outside]; split; [exact Hn| exact I]|];
              eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG6|]; intros a [Ha _]; right; left; exact Ha|];
              eapply agrees_on_weaken; [exact AGo8|]; intros a [_ Hn]; cbn [outside]; split; [exact Hn| exact I]);
        assert (HEB8 : rw_cells asegs mm EB [CB 256 e3])
          by (eapply agrees_rw_cells; [exact AGo8|
                eapply agrees_rw_cells; [exact AG6| eapply agrees_rw_cells; [exact AGo5| exact HEBf| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]
                                        | intros a Ha; eapply clocA_keeps; [exact EBL2| cbn [cells_size csize Nat.add] in Ha; lia]]
                | intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia]);
        destruct (pcap_aux_agree p P B Ib pad bs mf mm _ AGX) as (BUF' & PRIV' & IFS'); [ | | | lia | exact BUF | exact PRIV | exact IFS |]
      end.
      { intros a Ha. split; [apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| lia]. }
      { intros a Ha. unfold PCAP_PRIV_OFF in Ha. split; [apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| lia]. }
      { intros sg q Hq a Ha. destruct (API sg q Hq) as [X1' X2'].
        split; [apply in_block_app; right; rewrite EPB; unfold pcap_blocks, in_block; rewrite Hq; do 2 apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia| lia]. }
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (PC8 : PCAPR P p PB FB mm) end.
      { exists FA. split; [rewrite RFf; exact HinF|]. exists B, Ib. eexists (mkPJ _ _ _ _ _ _ _ _ _ _ _). exists pad, bs.
        split; [exact EPB|].
        split; [unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PCAP_PRIV_OFF, PK; cbn [app pj_read_op pj_fd pj_a pj_b pj_c pj_d pj_e pj_f pj_g pj_h pj_breakloop pk_stats pk_oneshot]; exact CELLS|].
        split; [exact PRIV'|]. split; [exact BUF'|]. split; [exact PFX|]. split; [exact IFS'| exact WF]. }
      cbn [app] in G8.
      apply evtF_done. eapply implMG_mono;
        [ eapply fo_epi with (L := L) (CL := CL ++ PB) (FB := FB) (FL := FL) (lo := lo) (SPA := SPA) (Fb := Fb);
          [ lia | exact SPA32 | lia | lia | lia | lia | exact G8 | assumption | exact ST5 | exact STGf | exact FRAf | exact FRASf | exact FRf | exact FKf | exact FLGf | exact SHCf
          | exact RSTK ]
        | ].
      cbv beta. intros r s9' RNG9 ms9 PO. (destruct PO as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); rename ndR2__ into PO). destruct_exs PO.
      (destruct PO as (-> & ndR1__); nd_pre ndR1__ 7%nat; intros MI9 ST9 AG9 G9 OF9 LC9 TL9; nd_post).
      repeat match goal with Q := _ : _ -> _ -> footprint -> machine_state -> Prop |- _ => subst Q end. unfold open_result_post.
      split; [eapply fp_le_trans; [exact FP2|]; eapply fp_le_trans; [exact FPf| exact FP5]|].
      lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 P), mm, FB end.
      split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
      split; [congruence|].
      split; [assumption|]. split; [assumption|].
      split.
      { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGf| intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]|].
        eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5| intros a [K _]; split; [exact K| exact I]]|].
        eapply agrees_on_trans; [eapply agrees_on_weaken; [eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA) (X := fun _ => True) (CL := CL) (CLk := CL ++ PB);
                                    [exact Gf| apply incl_appl; apply incl_refl| intros a K; apply in_block_app; left; exact K| lia| lia
                                    | eapply agrees_on_weaken; [exact AG6| intros a [K _]; exact K] | intros; exact I]
                                 | intros a [K N]; split; [exact K| cbn [outside]; split; [exact N| exact I]]]|].
        eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG8| intros a [K _]; split; [exact K| exact I]]|].
        eapply agrees_on_weaken; [exact AG9|]. intros a [K _].
        destruct K as [K|[K|[K|K]]]; [left; exact K| right; left; apply in_block_app; left; exact K| right; right; left; exact K| right; right; right; exact K]. }
      exists P, PB. split; [reflexivity|]. split; [split; [reflexivity| exact RFf]|].
      split; [exact G9|].
      split; [eapply PCAPR_agree; [exact AG9| intros a Ha; right; left; apply in_block_app; right; exact Ha| exact PC8]|].
      exists e3. eapply agrees_rw_cells; [exact AG9| exact HEB8|]. intros a Ha.
      eapply clocA_keeps; [eapply clocA_incl; [exact EBL| apply incl_appl; apply incl_refl| apply incl_refl]|]. cbn [cells_size csize Nat.add] in Ha; lia. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) L4). cbn [negb].
    destruct (rw_cells_cut _ _ _ 1 MG2) as [MG _]. clear MG2. cbn [firstn] in MG.
    replace (length got) with 4%nat in MG by lia.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    pose proof (unp_of_sh_part _ _ _ 4%nat 0%nat 4 SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPM.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPM. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPM.
    pose proof (unp_of_sh_part _ _ _ 6%nat 0%nat 4 SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPE.
    change (8 * Z.of_nat 6)%Z with 48%Z in UNPE. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPE.
    pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 (incl_tl _ (incl_refl _)) AGx3 FXB) as AGsh3.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G3 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh3 ltac:(lia)) as OEB3.
    assert (OEB3' : cobjA RNG2 m4 ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CL EB 256) by (split; [exact EBL'| exact (proj2 OEB3)]).
    pose proof (rw_cells_nth_C8 _ _ _ 10%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BRA.
    cbn [firstn cells_size csize Nat.add] in BS0, BRA.
    replace (bv_unsigned sp + -96 + Z.of_nat 80)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
    replace (bv_unsigned sp + -96 + Z.of_nat 88)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
    assert (FRINc : forall A n, (Fb <= A)%Z -> (A + n <= Fb + 64)%Z -> clocA ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CL A n)
      by (intros A n H1 H2; right; exists (FF_FOPEN_OFFLINE, Fb, 64%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    ienterG. zstep. rewrite L4. if_false. do 6 zstep. zstep.
    (* [comment removed for export] *)
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (chk_any false) with (L := L) (s := s2') (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (MG := (Fb + 32)%Z) (FA := FA)
                                  (EB := EB) (ERR := (Fb + 48)%Z) (f := f) (magic := got) (ej := ej) (fuel := O) (trC := bv_unsigned ra :: trC);
        [ split; [exact G3|]; rewrite Hspa; split; [exact ST2|]; split; [lia|]; split; [unfold PCAP_L2_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x85088%Z UC3); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
              | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_fopen_offline, depth_pcap_check_header; lia]
        | rewrite unsigned_lit by lia; exact TRC
        | unfold frames_check_header; apply nofr_cons; [eapply nofr_sub; [exact NF| unfold frames_fopen_offline, frames_pcap_check_header; intros ff Hf; cbn in Hf |- *; clear - Hf; intuition]
                                                       | cbn; clear; intuition congruence]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | exact MG | exact GR | lia | exact HEB | exact ERRc | reflexivity
        | split; [apply FRINc; lia|]; eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPM]
        | split; [apply FRINc; lia|]; eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPE]
        | lia | exact OEB3' | lia | lia | Z.div_mod_to_equations; lia | exact E8 ]. }
    intros r1 ps3 RNG3 ms3 PO; unfold check_header_post in PO;
      (nd_pre PO 12%nat; intros FP3 av3 m5 errw E OF3 MI3 ST3 AG4 MG3 ERR3 REST; nd_post).
    unfold hpost_regs in E; destruct_exs E; subst ms3; rewrite Hspa in *; clear Hspa; subst spa.
    replace (ret_pc (Z_to_bv 64 544904)) with (Z_to_bv 64 544904) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    repeat match goal with HR : rng RNG2 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    xf3 AG4 FR (left; lia). xf3 AG4 FRA (left; lia).
    xf3 AG4 FK0 (right; right; left; apply FRIN; lia). xf3 AG4 FLG (right; right; left; apply FRIN; lia).
    xf3 AG4 SHC (right; right; right; apply SHIN; lia).
    apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| split; lia]].
    assert (AGx4 : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m m5).
    { eapply agrees_on_trans; [exact AGx3|]. eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA); [exact G3| apply incl_refl| intros a K; exact K| lia| lia| exact AG4|].
      intros a NFr NEb. split; [exact NEb| lia]. }
    assert (UC4 : ucallerA depth_fopen_offline L m5 sp s0 ra trC)
      by (eapply ucaller_keep; [exact UC3| lia|]; intros a Ha; destruct (AG4 a ltac:(lia) ltac:(split; [left; lia| split; lia])) as [E1 _]; exact E1).
    clear MG ERRc HEB UNPM UNPE FRM3 AGsh3 OEB3 OEB3' BS0 BRA MI2 ST2 MU WM UC3 AGx3 AG4 G3.
    assert (FP23 : fp_le RNG2 RNG3) by exact FP3.
    destruct r1 as [|msg|p].
    - (* [comment removed for export] *)
      (destruct REST as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros G4 [e3 HEB3]; nd_post).
      destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G4) as [FAll4 _]. pose proof (Forall_inv FAll4) as FRM4. clear FAll4.
      pose proof (unp_of_sh_part _ _ _ 4%nat 0%nat 4 SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPM.
      change (8 * Z.of_nat 4)%Z with 32%Z in UNPM. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPM.
      pose proof (unp_of_sh_part _ _ _ 6%nat 0%nat 4 SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia) ltac:(lia)) as UNPE.
      change (8 * Z.of_nat 6)%Z with 48%Z in UNPE. change (8 * Z.of_nat 0 + 4)%Z with 4%Z in UNPE.
      pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G4 (incl_tl _ (incl_refl _)) AGx4 FXB) as AGsh4.
      pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G4 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh4 ltac:(lia)) as OEB4.
      assert (OEB4' : cobjA RNG3 m5 ((FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) CL EB 256) by (split; [exact EBL'| exact (proj2 OEB4)]).
      pose proof (rw_cells_nth_C8 _ _ _ 10%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 11%nat _ FR eq_refl) as BRA.
      cbn [firstn cells_size csize Nat.add] in BS0, BRA.
      replace (bv_unsigned sp + -96 + Z.of_nat 80)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
      replace (bv_unsigned sp + -96 + Z.of_nat 88)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
      pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
      ienterG. zstep. if_true.
      zstep.
      replace (sx32 z64) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
      zstep. if_false.
      do 5 zstep. zstep.
      (* [comment removed for export] *)
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      apply evtF_done. eapply implMG_bind.
      { eapply (chk_any true) with (L := L) (s := ps3) (CL := CL) (FB := FB) (FL := (FF_FOPEN_OFFLINE, Fb, 64%Z) :: FL) (lo := lo) (MG := (Fb + 32)%Z) (FA := FA)
                                   (EB := EB) (ERR := (Fb + 48)%Z) (f := f) (magic := got) (ej := e3) (fuel := fuel) (trC := bv_unsigned ra :: trC);
          [ split; [exact G4|]; rewrite Hspa; split; [exact ST3|]; split; [lia|]; split; [unfold PCAP_L2_STACK; lia|]; split; [lia|];
            split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
            split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
          | eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x85308%Z UC4); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_check_header, depth_fopen_offline, depth_pcap_ng_check_header; lia]
          | rewrite unsigned_lit by lia; exact TRN
          | unfold frames_check_header; apply nofr_cons; [eapply nofr_sub; [exact NF| unfold frames_fopen_offline, frames_pcap_ng_check_header; intros ff Hf; cbn in Hf |- *; clear - Hf; intuition]
                                                         | cbn; clear; intuition congruence]
          | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | exact MG3 | exact GR | lia | exact HEB3 | exact ERR3 | reflexivity
          | split; [apply FRINc; lia|]; eapply frameA_aobj; [exact FRM4| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPM]
          | split; [apply FRINc; lia|]; eapply frameA_aobj; [exact FRM4| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia| exact UNPE]
          | lia | exact OEB4' | lia | lia | Z.div_mod_to_equations; lia | exact E8 ]. }
      intros r2 ps5 RNG5 ms5 PO; unfold check_header_post in PO;
        (nd_pre PO 12%nat; intros FP5 av5 m6 errw5 E OF5 MI5 ST5 AG5 MG5 ERR5 REST5; nd_post).
      unfold hpost_regs in E; destruct_exs E; subst ms5; rewrite Hspa in *; clear Hspa; subst spa.
      replace (ret_pc (Z_to_bv 64 545544)) with (Z_to_bv 64 545544) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat match goal with HR : rng RNG3 _ _ |- _ => apply (rng_fp_le _ _ _ _ FP5) in HR end.
      xf3 AG5 FR (left; lia). xf3 AG5 FRA (left; lia).
      xf3 AG5 FK0 (right; right; left; apply FRIN; lia). xf3 AG5 FLG (right; right; left; apply FRIN; lia).
      xf3 AG5 SHC (right; right; right; apply SHIN; lia).
      apply (agrees_stk _ _ _ _ _ AG5) in STG; [|intros a Ha; split; [left; lia| split; lia]].
      assert (AGx5 : agrees_on (fun x => client_keeps FL CL (bv_unsigned sp) x /\ outside [(EB, EB + 256)%Z] x) m m6).
      { eapply agrees_on_trans; [exact AGx4|]. eapply callee_ag with (SP := bv_unsigned sp) (EB := EB) (SPA := SPA); [exact G4| apply incl_refl| intros a K; exact K| lia| lia| exact AG5|].
        intros a NFr NEb. split; [exact NEb| lia]. }
      assert (FP25 : fp_le RNG2 RNG5) by (eapply fp_le_trans; [exact FP3| exact FP5]).
      clear MG3 HEB3 UNPM UNPE FRM4 AGsh4 OEB4 OEB4' BS0 BRA MI3 ST3 MU WM UC4 AGx4 AG5 ERR3.
      destruct r2 as [|msg|p].
      + (* [comment removed for export] *)
        (destruct REST5 as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros G5 [e5 HEB5]; nd_post).
        apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [20; 236]%nat) in HEB5; [|reflexivity]. cbn [mk_CB_cells app] in HEB5.
        destruct (rw_cells_cut _ _ _ 1 HEB5) as [EB1 EB2]. clear HEB5. cbn [firstn skipn cells_size csize Nat.add] in EB1, EB2.
        replace (EB + Z.of_nat 20)%Z with (EB + 20)%Z in EB2 by lia.
        set (UFF := [Z_to_bv 8 117; Z_to_bv 8 110; Z_to_bv 8 107; Z_to_bv 8 110; Z_to_bv 8 111; Z_to_bv 8 119; Z_to_bv 8 110; Z_to_bv 8 32; Z_to_bv 8 102; Z_to_bv 8 105;
                     Z_to_bv 8 108; Z_to_bv 8 101; Z_to_bv 8 32; Z_to_bv 8 102; Z_to_bv 8 111; Z_to_bv 8 114; Z_to_bv 8 109; Z_to_bv 8 97; Z_to_bv 8 116; Z_to_bv 8 0]).
        assert (MSGB : bytes_at asegs m6 0x21440 UFF)
          by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m6 0x21440 UFF MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))).
        assert (EUFF : map b8 Msg.unknown_file_format ++ [Z_to_bv 8 0] = UFF) by (vm_compute; reflexivity).
        pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G5) as (RT5 & _).
        pose proof (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G5 (incl_tl _ (incl_refl _)) AGx5 FXB) as AGsh5.
        pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OEB G5 (incl_refl _) (incl_tl _ (incl_refl _)) AGsh5 ltac:(lia)) as OEB5.
        pose proof (munch_refl [(SPA - 2224, SPA); (EB, EB + 20)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
        ienterG. zstep. if_false.
        zstep. replace (sx32 z64) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
        zstep. if_false.
        do 4 zstep. zstep. zstep.
        remember (Z_to_bv 64 SPA) as spa eqn:Espa.
        assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
        eapply evtF_cut.
        { eapply (asan_memcpy_specZ RNG5 _ spa) with (lo := lo) (Dst := EB) (Src := 0x21440%Z) (n := 20%Z) (src := UFF) (junk := firstn 20 e5);
            [ reflexivity | reflexivity | reflexivity | exact MI5 | rewrite Hspa; exact ST5 | rewrite Hspa; lia | lia | exact RT5 | exact MSGB | reflexivity | lia | exact EB1 | lia
            | eapply (gia_global_mobjA _ _ _ GL); [exact G5 | unfold client_globals; repeat (first [left; reflexivity | right]) | exact RIMG | exact RISH]
            | eapply mobjA_sub; [apply aobjA_mobjA; [exact (proj2 OEB5)| lia]| lia| lia| lia]
            | first [lia | atop_facts; lia] | lia | exact RIMG | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] ]. }
        cbv beta. intros ms' PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 6%nat; intros MU7 WM7 MI7 ST7 HD7 SRC7; nd_post).
        rewrite Hspa in *. clear Hspa. subst spa.
        replace (ret_pc (Z_to_bv 64 545432)) with (Z_to_bv 64 545432) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        pose proof G5 as G5'. rewrite <- (app_nil_r CL) in G5'.
        assert (FWs : Forall (own_ivA [(FF_FOPEN_OFFLINE, Fb, 64%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA - 2224, SPA)]%Z) by own_ivs.
        assert (FXs : Forall (cobj_iv FL CL) [(EB, EB + 20)]%Z).
        { apply Forall_cons; [|apply Forall_nil]. split; [cbn [fst snd]| cbn [fst snd]; lia]. replace (EB + 20 - EB)%Z with 20%Z by lia.
          destruct EBL as [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)]; [left; exists b| right; exists fr]; (split; [assumption|]; split; lia). }
        lazymatch type of MU7 with munch _ _ ?mm =>
          destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FWs FXs G5' MU7 WM7 ltac:(lia)) as [G7 AG7] end.
        rewrite app_nil_r in G7. cbn [app] in G7.
        lazymatch type of MU7 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU7 WM7 end.
        change (Z.to_nat 20) with 20%nat in HD7.
        pose proof (rw_cells_uncut _ _ _ _ _ HD7 EB2 ltac:(reflexivity)) as HEB7. rewrite <- EUFF in HEB7. cbn [app] in HEB7.
        zstep.
        apply evtF_done. eapply FAIL with (msgf := Msg.unknown_file_format) (junk3 := firstn 236 (skipn 20 e5));
          [ exact FP25 | exact MI7 | exact ST7 | exact STG
          | eapply agrees_on_trans; [exact AGx5|]; eapply agrees_on_weaken; [exact AG7|]; intros a [K N]; split; [exact K|]; cbn [outside] in *; split; [lia| exact I]
          | exact G7 | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC | exact HEB7
          | vm_compute; reflexivity | vm_compute; repeat constructor | congruence ].
      + (* [comment removed for export] *)
        (nd_pre REST5 2%nat; intros junk5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); nd_pre ndR3__ 4%nat; intros G5 HEB5 LEN5 RNGM5; nd_post).
        pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
        ienterG. zstep. if_false.
        zstep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
        zstep. if_true.
        apply evtF_done. eapply FAIL with (msgf := msg);
          [ exact FP25 | exact MI5 | exact ST5 | exact STG | exact AGx5 | exact G5 | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC | exact HEB5
          | exact LEN5 | exact RNGM5 | congruence ].
      + (* [comment removed for export] *)
        (nd_pre REST5 3%nat; intros P PB ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros G5 PPC RF [e5 HEB5]; nd_post).
        (pose proof PPC as ndP__; nd_pre ndP__ 7%nat; intros rf0 st0 os0 _ _ _ (B0 & I0 & jq0 & pad0 & bs0 & EPB0 & _); nd_post).
        (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 ltac:(apply in_or_app; left; apply in_or_app; right; rewrite EPB0; left; reflexivity)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & PT0 & _) P0 _; nd_post).
        cbn [cb_addr cb_size fst snd] in P0, PT0. pose proof (psize_pos p) as PS0.
        pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
        ienterG. zstep. if_true_by (nez_true P ltac:(lia)).
        apply evtF_done. eapply FOUND with (P := P) (PB := PB) (e3 := e5);
          [ exact RF | exact FP25 | exact MI5 | exact ST5 | exact STG | exact AGx5 | exact G5 | exact PPC | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC
          | exact HEB5 | congruence ].
    - (* [comment removed for export] *)
      (nd_pre REST 2%nat; intros junk4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); nd_pre ndR3__ 4%nat; intros G4 HEB4 LEN4 RNGM4; nd_post).
      pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
      ienterG. zstep. if_true.
      zstep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
      zstep. if_true.
      apply evtF_done. eapply FAIL with (msgf := msg);
        [ exact FP23 | exact MI3 | exact ST3 | exact STG | exact AGx4 | exact G4 | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC | exact HEB4
        | exact LEN4 | exact RNGM4 | congruence ].
    - (* [comment removed for export] *)
      (nd_pre REST 3%nat; intros P PB ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros G4 PPC RF [e4 HEB4]; nd_post).
      (pose proof PPC as ndP__; nd_pre ndP__ 7%nat; intros rf0 st0 os0 _ _ _ (B0 & I0 & jq0 & pad0 & bs0 & EPB0 & _); nd_post).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 ltac:(apply in_or_app; left; apply in_or_app; right; rewrite EPB0; left; reflexivity)) as ndP__; nd_pre ndP__ 3%nat; intros (_ & _ & PT0 & _) P0 _; nd_post).
      cbn [cb_addr cb_size fst snd] in P0, PT0. pose proof (psize_pos p) as PS0.
      pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
      ienterG. zstep. if_false_by (eqz_false P ltac:(lia)).
      apply evtF_done. eapply FOUND with (P := P) (PB := PB) (e3 := e4);
        [ exact RF | exact FP23 | exact MI3 | exact ST3 | exact STG | exact AGx4 | exact G4 | exact PPC | exact FRA | reflexivity | exact FR | exact FK0 | exact FLG | exact SHC
        | exact HEB4 | congruence ].
  Qed.
  End Sz8.
  Theorem fopen_offline_proofA : ltac:(let t := eval cbv delta [fopen_offline_proofA__stmt] in fopen_offline_proofA__stmt in exact t).
  Proof using CHK_NG CHK_PCAP FENTER0 FERROR FILENO FMT FREAD FRET GL GOTL SNPRINTF. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo FA EB f ej fuel. ltac2:(SecDiet.SzSec.closeP 'fopen_offline_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FopenOffline.
End CANSEC1.
End TwB.
