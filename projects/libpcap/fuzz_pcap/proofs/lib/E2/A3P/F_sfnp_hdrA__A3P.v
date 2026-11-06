(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_exitA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_normA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_failA__A3P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfnp_hdrA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_exitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_normA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_bodyA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_scaleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_sfnp_swapA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sassume := first [ match goal with H : ?T |- ?G => constr_eq T G; exact H end | eassumption ].
Import ListNotations.
Import ITree.Exc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
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
Local Ltac ck_lia ::= first [ atop_facts; plia_a | Z.div_mod_to_equations; lia ].
Local Ltac sh_lia ::= rewrite ?shad_div, ?nshad_div; unfold AsanEmbed.shlen, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z;
  first [ atop_facts; plia_a | Z.div_mod_to_equations; lia ].
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpHdr.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SET00 : set_shadow_stmt SET_SHADOW_00 0.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.

  Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof using . intros B C f g s RNG Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  Definition np_hshort__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 : word) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell) (hs n : Z),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9;
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= n <= hs)%Z -> (hs = 16 \/ hs = 24)%Z ->
    implMG RNGx (mbind (e_ferror (prims HO FO sites) f)
                   (fun e : bool => if e then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string [])
                                                    (fun m0 => e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf m0 p'))
                                    else if negb (n =? 0)%Z then e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf (Msg.trunc_header hs n) p')
                                         else e_fret (prims HO FO sites) FF_NEXT_PACKET (0%Z, hdr0, p'))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) r22 (Z_to_bv 64 hs) r24 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88460) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 p' hcs' dw hs n : ltac2:(SecDiet.SzSec.tyM 'np_hshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_hshort__body : ltac2:(SecDiet.SzSec.bodyP 'np_hshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF.
    intros CTX INV PC FRA HH Hh HD Hd NR HS.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    set (POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o).
    cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. zstep. zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := CL ++ PB) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (lo := lo) (f := f) (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. destruct PO as (FP3 & av & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 558184)) with (Z_to_bv 64 558184) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (AG3' : agrees_on (fun a => client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) SPA a /\ True) mm m3)
      by (eapply agrees_on_weaken; [exact AG3|]; intros a (K & _); exact K).
    assert (INV3 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG3 sx PB dsh m3).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun _ => True);
        [ exact INV | lia | lia | exact FP3 | exact G3 | reflexivity | exact MI3' | exact ST3 | exact AG3'
        | intros; exact I | intros; exact I | intros; exact I
        | eapply np_frame_keep with (Pn := fun _ => True); [exact AG3'| intros; exact I| exists k0, k1, k2, fj; exact FRC] ]. }
    assert (PC3 : PCAPR (hptr:=hptr) P p' PB FB m3)
      by (eapply PCAPR_agree; [exact AG3| intros a Ha; right; left; apply in_block_app; right; exact Ha| exact PC]).
    apply (agrees_rw_cells _ _ _ _ _ AG3) in FRA; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HH'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (rng_fp_le _ _ _ _ FP3) in RTLS.
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
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
      apply implMG_from_evtF. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      ck TUNP 4%Z 0x88480%Z [11%Z; 12%Z].
      zstep.
      do 4 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (np_fmt FO GIOA TP fflagA GL FFREE7 SETF8 FMT) with (pc := 0x88498%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj) (e := e);
        [ left; split; [left; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | lia | exact MSG | intros msg; reflexivity ].
    - destruct (Z.eq_dec n 0) as [NZ|NNZ].
      + (* [comment removed for export] *)
        replace (n =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact NZ). cbn [negb].
        apply implMG_from_evtF. zstep. if_true.
        zstep. if_cases Kz; [|zify_cond Kz; exfalso; lia].
        apply evtF_done. subst POSTQ. subst n.
        eapply (np_exit FO GIOA TP fflagA GL FFREE7) with (st := 0%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj);
          [ exact CTX | exact INV3 | exact PC3 | exact FRA | reflexivity | exact HH' | reflexivity | exact HD' | reflexivity | lia | intros X; discriminate X ].
      + (* [comment removed for export] *)
        replace (n =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact NNZ). cbn [negb].
        assert (MSG : fmt_at m3 0x21d80 "truncated dump file; tried to read %zu header bytes, only got %zu"%string)
          by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21d80 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %zu header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                  MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
              split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
        apply implMG_from_evtF. zstep. if_true.
        zstep. if_cases Kz; [zify_cond Kz; exfalso; lia|].
        do 6 zstep. zstep.
        apply evtF_done. subst POSTQ. unfold Msg.trunc_header, PCAP_ERRBUF_SIZE.
        eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x884bc%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj)
                                                                         (args := [AInt hs; AInt n]);
          [ left; split; [right; left; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
          | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
  Qed.
  End Sz2.
  Lemma np_hshort : ltac:(let t := eval cbv delta [np_hshort__stmt] in np_hshort__stmt in exact t).
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 p' hcs' dw hs n. ltac2:(SecDiet.SzSec.closeP 'np_hshort__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_hdr_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (hb : list Z) (junk' : list byte) (hcs : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm (Fb + 32) [CB (length hb) (map b8 hb); CB (Z.to_nat (k_hs k) - length hb) junk'] ->
    rw_cells asegs mm HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    Forall (fun z => 0 <= z < 256)%Z hb -> (0 <= zlength hb <= k_hs k)%Z -> (0 < alloc)%Z ->
    implMG RNGx (if negb (zlength hb =? k_hs k)%Z
                 then mbind (e_ferror (prims HO FO sites) (k_f k))
                        (fun e : bool => if e then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string [])
                                                         (fun m0 => e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf m0 (pv k bq bsz alloc data eb)))
                                         else if negb (zlength hb =? 0)%Z
                                              then e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf (Msg.trunc_header (k_hs k) (zlength hb)) (pv k bq bsz alloc data eb))
                                              else e_fret (prims HO FO sites) FF_NEXT_PACKET (0%Z, hdr0, pv k bq bsz alloc data eb))
                 else np_body_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb)
                        (if k_sw k then bswap32 (get_le32 hb 0) else get_le32 hb 0) (if k_sw k then bswap32 (get_le32 hb 4) else get_le32 hb 4)
                        (if k_sw k then bswap32 (get_le32 hb 8) else get_le32 hb 8) (if k_sw k then bswap32 (get_le32 hb 12) else get_le32 hb 12)) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (zlength hb)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.shiftr (P + 648) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               (Z_to_bv 64 (Fb + 32)) r23 (Z_to_bv 64 HA) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 648)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8836c) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb hb junk' hcs dw : ltac2:(SecDiet.SzSec.tyM 'np_hdr_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_hdr_post__body : ltac2:(SecDiet.SzSec.bodyP 'np_hdr_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
    intros CTX INV PC FRA HB HH Hh HD Hd GOTR GOTL AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear BUF.
    pose proof (munch_refl [(SPA, SPA + 120)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    destruct (Z.eq_dec (zlength hb) (k_hs k)) as [LEQ|LNE].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      apply implMG_from_evtF.
      ck0_at PUNP (P + 648)%Z; ck_go.
      zstep. zstep. zstep. if_cases Kq; [|zify_cond Kq; exfalso; lia].
      apply evtF_done. subst POSTQ.
      eapply np_hshort with (dsh := dsh) (PB := pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (hcs' := hcs);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | exact Hh | exact HD | exact Hd | exact GOTL | exact WHS ]. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
    assert (L16 : (16 <= length hb)%nat) by (unfold zlength in LEQ; lia).
    destruct hb as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|g8 [|g9 [|g10 [|g11 [|g12 [|g13 [|g14 [|g15 rest]]]]]]]]]]]]]]]];
      try (exfalso; cbn [length] in L16; lia). clear L16.
    pose proof GOTR as GR'. do 16 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']).
    pose proof (get_le32_hdr g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest) as (E0 & E4 & E8 & E12). cbv zeta in E0, E4, E8, E12.
    rewrite E0, E4, E8, E12. clear E0 E4 E8 E12.
    assert (LJ : length junk' = (Z.to_nat (k_hs k) - (16 + length rest))%nat) by (destruct HB as [[WFh _] _]; cbn in WFh; cbn [length] in WFh |- *; lia).
    assert (HB4 : rw_cells asegs mm (Fb + 32)
              ([C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7)); C4 (Z_to_bv 64 (le4val g8 g9 g10 g11)); C4 (Z_to_bv 64 (le4val g12 g13 g14 g15))]
               ++ [CB (length rest) (map b8 rest); CB (length junk') junk'])).
    { eapply rw_cells_recell; [exact HB | cbn; rewrite length_map; repeat split; try exact Logic.I; cbn [length] in LEQ |- *; unfold zlength in LEQ; cbn [length] in LEQ; lia |].
      cbn [cells_bytes cbytes app map]. unfold b8. rewrite (le4_lit g0 g1 g2 g3), (le4_lit g4 g5 g6 g7), (le4_lit g8 g9 g10 g11), (le4_lit g12 g13 g14 g15) by lia.
      cbn [app]. rewrite app_nil_r. reflexivity. }
    clear HB. destruct (rw_cells_cut _ _ _ 4 HB4) as [HB16 _]. clear HB4. cbn [firstn app] in HB16.
    apply implMG_from_evtF.
    ck0_at PUNP (P + 648)%Z; ck_go.
    zstep. zstep. zstep. if_cases Kq; [zify_cond Kq; exfalso; lia|].
    zstep.
    ck0 PUNP; ck_go.
    zstep. zstep. rewrite (np_sx32_small (Z.b2z (k_sw k))) by (destruct (k_sw k); cbn; lia).
    zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with HH1 : rw_cells asegs _ SPA _ |- _ => rename HH1 into FRA1 end.
    assert (FWs : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA, SPA + 120)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FWs) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m5)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FWs (Forall_nil _) G a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))));
      assert (INV5 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
                             (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh m5)
        by (unfold np_inv0, np_shadow; split; [exact FP|]; split; [exact G5|]; split; [exact OF|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
            split; [assumption|];
            split; [eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I]|];
            split; [exists k0, k1, k2, fj; assumption|]; split; assumption)
    end.
    destruct (k_sw k) eqn:ESW; cbn [Z.b2z].
    - (* [comment removed for export] *)
      if_false.
      eapply evtF_cut;
        [ eapply np_swap_seq with (HB := (Fb + 32)%Z) (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3) (g4 := g4) (g5 := g5) (g6 := g6) (g7 := g7)
                                  (g8 := g8) (g9 := g9) (g10 := g10) (g11 := g11) (g12 := g12) (g13 := g13) (g14 := g14) (g15 := g15);
          [ assumption | lia | lia | eapply rng_sub'; [exact FRNG| lia] | repeat (apply Forall_cons; [assumption|]); apply Forall_nil | exact HB16 ]
        | ].
      cbv beta. intros ms' PO. destruct PO as (cw & sw & uw & a3v & lw & a5v & a6v & a7v & t0v & -> & Fc & Fs & Fu & Fl).
      zstep.
      ck0 HAUNP; ck_go.
      rewrite (bswap32_le4val g0 g1 g2 g3), (bswap32_le4val g4 g5 g6 g7), (bswap32_le4val g8 g9 g10 g11), (bswap32_le4val g12 g13 g14 g15) by lia.
      rewrite <- (Z_to_bv_bv_unsigned cw), <- (Z_to_bv_bv_unsigned sw), <- (Z_to_bv_bv_unsigned uw), <- (Z_to_bv_bv_unsigned lw).
      rewrite <- Fc, <- Fs, <- Fu, <- Fl.
      pose proof (bv_unsigned_in_range 64 cw). pose proof (bv_unsigned_in_range 64 sw). pose proof (bv_unsigned_in_range 64 uw). pose proof (bv_unsigned_in_range 64 lw).
      unfold bv_modulus in *.
      apply evtF_done. subst POSTQ.
      eapply (np_scale HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP)
        with (dsh := dsh) (secx := bv_unsigned sw) (usecx := bv_unsigned uw) (capx := bv_unsigned cw) (lenx := bv_unsigned lw) (hcs := hcs);
        [ exact CTX | exact INV5 | exact PC5 | exact FRA1 | eassumption | exact Hh | eassumption | exact Hd | lia | lia | lia | lia | exact AL0 ].
    - (* [comment removed for export] *)
      if_true.
      rewrite (sx32_lit g8 g9 g10 g11) by lia.
      zstep. rewrite (sx32_lit g0 g1 g2 g3) by lia. zstep. rewrite (sx32_lit g4 g5 g6 g7) by lia. zstep. rewrite (sx32_lit g12 g13 g14 g15) by lia.
      zstep.
      ck0 HAUNP; ck_go.
      rewrite <- (sxv_mod32 g0 g1 g2 g3), <- (sxv_mod32 g4 g5 g6 g7), <- (sxv_mod32 g8 g9 g10 g11), <- (sxv_mod32 g12 g13 g14 g15) by lia.
      pose proof (sxv_range g0 g1 g2 g3). pose proof (sxv_range g4 g5 g6 g7). pose proof (sxv_range g8 g9 g10 g11). pose proof (sxv_range g12 g13 g14 g15).
      apply evtF_done. subst POSTQ.
      eapply (np_scale HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP)
        with (dsh := dsh) (secx := sxv g0 g1 g2 g3) (usecx := sxv g4 g5 g6 g7) (capx := sxv g8 g9 g10 g11) (lenx := sxv g12 g13 g14 g15) (hcs := hcs);
        [ exact CTX | exact INV5 | exact PC5 | exact FRA1 | sassume | exact Hh | sassume | exact Hd | lia | lia | lia | lia | exact AL0 ].
  Qed.
  End Sz3.
  Lemma np_hdr_post : ltac:(let t := eval cbv delta [np_hdr_post__stmt] in np_hdr_post__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb hb junk' hcs dw. ltac2:(SecDiet.SzSec.closeP 'np_hdr_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpHdr.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_chkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_bodyA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_sfchk_fsegA__B3P.F_sfnp_scaleA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_sfnp_swapA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Local Ltac sassume := first [ match goal with H : ?T |- ?G => constr_eq T G; exact H end | eassumption ].
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac ck_lia ::= first [ atop_facts; plia_a | Z.div_mod_to_equations; lia ].
Local Ltac sh_lia ::= rewrite ?shad_div, ?nshad_div; unfold AsanEmbed.shlen, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z;
  first [ atop_facts; plia_a | Z.div_mod_to_equations; lia ].
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpHdr.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SET00 : set_shadow_stmt SET_SHADOW_00 0.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.

  Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof using . intros B C f g s RNG Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  Definition np_hshort__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 : word) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell) (hs n : Z),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 c9; C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= n <= hs)%Z -> (hs = 16 \/ hs = 24)%Z ->
    implMG RNGx (mbind (e_ferror (prims HO FO sites) f)
                   (fun e : bool => if e then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string [])
                                                    (fun m0 => e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf m0 p'))
                                    else if negb (n =? 0)%Z then e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf (Msg.trunc_header hs n) p')
                                         else e_fret (prims HO FO sites) FF_NEXT_PACKET (0%Z, hdr0, p'))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) r22 (Z_to_bv 64 hs) r24 (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88910) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 p' hcs' dw hs n : ltac2:(SecDiet.SzSec.tyM 'np_hshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_hshort__body : ltac2:(SecDiet.SzSec.bodyP 'np_hshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF.
 intros CTX INV PC FRA HH Hh HD Hd NR HS.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    set (POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o).
    cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. zstep. zstep.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (FERROR _ spa) with (L := L) (s := sx) (CL := CL ++ PB) (FB := FB) (FL := (FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (lo := lo) (f := f) (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity ]. }
    intros r s3' RNG3 ms' PO. cbv beta in PO. destruct PO as (FP3 & av & m3 & E & MI3' & ST3 & AG3 & G3 & -> & -> & ERRNO).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 559384)) with (Z_to_bv 64 559384) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (AG3' : agrees_on (fun a => client_keeps ((FF_NEXT_PACKET, Fb, 8192%Z) :: FL) (CL ++ PB) SPA a /\ True) mm m3)
      by (eapply agrees_on_weaken; [exact AG3|]; intros a (K & _); exact K).
    assert (INV3 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG3 sx PB dsh m3).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun _ => True);
        [ exact INV | lia | lia | exact FP3 | exact G3 | reflexivity | exact MI3' | exact ST3 | exact AG3'
        | intros; exact I | intros; exact I | intros; exact I
        | eapply np_frame_keep with (Pn := fun _ => True); [exact AG3'| intros; exact I| exists k0, k1, k2, fj; exact FRC] ]. }
    assert (PC3 : PCAPR (hptr:=hptr) P p' PB FB m3)
      by (eapply PCAPR_agree; [exact AG3| intros a Ha; right; left; apply in_block_app; right; exact Ha| exact PC]).
    apply (agrees_rw_cells _ _ _ _ _ AG3) in FRA; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HH'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG3) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
    apply (rng_fp_le _ _ _ _ FP3) in RTLS.
    repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
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
      apply implMG_from_evtF. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      (* [comment removed for export] *)
      pose proof ATPv_pg as TPG. pose proof atp_lin as ((TPLO & _) & _).
      assert (ERN : (0 < ATP + -164 < 2^64)%Z) by (unfold ATP; atop_facts; lia).
      zstep. if_false_by (eqz_false (ATP + -164) ERN).
      zstep. replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
      zstep. if_false.
      ck TUNP 4%Z 0x8893c%Z [11%Z; 12%Z].
      zstep.
      do 4 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (np_fmt FO GIOA TP fflagA GL FFREE7 SETF8 FMT) with (pc := 0x88954%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj) (e := e);
        [ left; split; [left; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | lia | exact MSG | intros msg; reflexivity ].
    - destruct (Z.eq_dec n 0) as [NZ|NNZ].
      + (* [comment removed for export] *)
        replace (n =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact NZ). cbn [negb].
        apply implMG_from_evtF. zstep. if_true.
        zstep. if_cases Kz; [|zify_cond Kz; exfalso; lia].
        apply evtF_done. subst POSTQ. subst n.
        eapply (np_exit FO GIOA TP fflagA GL FFREE7) with (st := 0%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj);
          [ exact CTX | exact INV3 | exact PC3 | exact FRA | reflexivity | exact HH' | reflexivity | exact HD' | reflexivity | lia | intros X; discriminate X ].
      + (* [comment removed for export] *)
        replace (n =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact NNZ). cbn [negb].
        assert (MSG : fmt_at m3 0x21d80 "truncated dump file; tried to read %zu header bytes, only got %zu"%string)
          by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21d80 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %zu header bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                  MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
              split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
        apply implMG_from_evtF. zstep. if_true.
        zstep. if_cases Kz; [zify_cond Kz; exfalso; lia|].
        do 6 zstep. zstep. zstep.      (* [comment removed for export] *)
        apply evtF_done. subst POSTQ. unfold Msg.trunc_header, PCAP_ERRBUF_SIZE.
        eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x88d24%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj)
                                                                         (args := [AInt hs; AInt n]);
          [ left; split; [right; left; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
          | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
  Qed.
  End Sz2.
  Lemma np_hshort : ltac:(let t := eval cbv delta [np_hshort__stmt] in np_hshort__stmt in exact t).
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 p' hcs' dw hs n. ltac2:(SecDiet.SzSec.closeP 'np_hshort__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_hdr_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (hb : list Z) (junk' : list byte) (hcs : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm (Fb + 32) [CB (length hb) (map b8 hb); CB (Z.to_nat (k_hs k) - length hb) junk'] ->
    rw_cells asegs mm HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    Forall (fun z => 0 <= z < 256)%Z hb -> (0 <= zlength hb <= k_hs k)%Z -> (0 < alloc)%Z ->
    implMG RNGx (if negb (zlength hb =? k_hs k)%Z
                 then mbind (e_ferror (prims HO FO sites) (k_f k))
                        (fun e : bool => if e then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string [])
                                                         (fun m0 => e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf m0 (pv k bq bsz alloc data eb)))
                                         else if negb (zlength hb =? 0)%Z
                                              then e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf (Msg.trunc_header (k_hs k) (zlength hb)) (pv k bq bsz alloc data eb))
                                              else e_fret (prims HO FO sites) FF_NEXT_PACKET (0%Z, hdr0, pv k bq bsz alloc data eb))
                 else np_body_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb)
                        (if k_sw k then bswap32 (get_le32 hb 0) else get_le32 hb 0) (if k_sw k then bswap32 (get_le32 hb 4) else get_le32 hb 4)
                        (if k_sw k then bswap32 (get_le32 hb 8) else get_le32 hb 8) (if k_sw k then bswap32 (get_le32 hb 12) else get_le32 hb 12)) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (zlength hb)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.shiftr (P + 648) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               (Z_to_bv 64 (Fb + 32)) r23 (Z_to_bv 64 HA) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 648)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88798) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb hb junk' hcs dw : ltac2:(SecDiet.SzSec.tyM 'np_hdr_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_hdr_post__body : ltac2:(SecDiet.SzSec.bodyP 'np_hdr_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
 intros CTX INV PC FRA HB HH Hh HD Hd GOTR GOTL AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear BUF.
    pose proof (munch_refl [(SPA, SPA + 120)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    destruct (Z.eq_dec (zlength hb) (k_hs k)) as [LEQ|LNE].
    2:{ (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      apply implMG_from_evtF.
      ck0_at PUNP (P + 648)%Z; ck_go.
      zstep. zstep. zstep. if_cases Kq; [|zify_cond Kq; exfalso; lia].
      apply evtF_done. subst POSTQ.
      eapply np_hshort with (dsh := dsh) (PB := pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) (hcs' := hcs);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | exact Hh | exact HD | exact Hd | exact GOTL | exact WHS ]. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
    assert (L16 : (16 <= length hb)%nat) by (unfold zlength in LEQ; lia).
    destruct hb as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|g8 [|g9 [|g10 [|g11 [|g12 [|g13 [|g14 [|g15 rest]]]]]]]]]]]]]]]];
      try (exfalso; cbn [length] in L16; lia). clear L16.
    pose proof GOTR as GR'. do 16 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']).
    pose proof (get_le32_hdr g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 rest) as (E0 & E4 & E8 & E12). cbv zeta in E0, E4, E8, E12.
    rewrite E0, E4, E8, E12. clear E0 E4 E8 E12.
    assert (LJ : length junk' = (Z.to_nat (k_hs k) - (16 + length rest))%nat) by (destruct HB as [[WFh _] _]; cbn in WFh; cbn [length] in WFh |- *; lia).
    assert (HB4 : rw_cells asegs mm (Fb + 32)
              ([C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7)); C4 (Z_to_bv 64 (le4val g8 g9 g10 g11)); C4 (Z_to_bv 64 (le4val g12 g13 g14 g15))]
               ++ [CB (length rest) (map b8 rest); CB (length junk') junk'])).
    { eapply rw_cells_recell; [exact HB | cbn; rewrite length_map; repeat split; try exact Logic.I; cbn [length] in LEQ |- *; unfold zlength in LEQ; cbn [length] in LEQ; lia |].
      cbn [cells_bytes cbytes app map]. unfold b8. rewrite (le4_lit g0 g1 g2 g3), (le4_lit g4 g5 g6 g7), (le4_lit g8 g9 g10 g11), (le4_lit g12 g13 g14 g15) by lia.
      cbn [app]. rewrite app_nil_r. reflexivity. }
    clear HB. destruct (rw_cells_cut _ _ _ 4 HB4) as [HB16 _]. clear HB4. cbn [firstn app] in HB16.
    apply implMG_from_evtF.
    ck0_at PUNP (P + 648)%Z; ck_go.
    zstep. zstep. zstep. if_cases Kq; [zify_cond Kq; exfalso; lia|].
    zstep.
    ck0 PUNP; ck_go.
    zstep. zstep.      (* [comment removed for export] *)
    zstep. rewrite (np_sx32_small (Z.b2z (k_sw k))) by (destruct (k_sw k); cbn; lia).
    zstep. rewrite (sx32_lit g8 g9 g10 g11) by lia.
    zstep. ub_al 7%Z ltac:(exact HA8).      (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with HH1 : rw_cells asegs _ SPA _ |- _ => rename HH1 into FRA1 end.
    assert (FWs : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA, SPA + 120)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FWs) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m5)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FWs (Forall_nil _) G a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))));
      assert (AG5m : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m5)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I])
    end.
    (* [comment removed for export] *)
    assert (FX : Forall (cobj_iv FL CL) [(HA, HA + 24)]%Z) by cobj_ivs.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8; 8; 4; 4]%nat) in HH'; [|reflexivity]. cbn [mk_CB_cells app] in HH'.
    repeat match type of HH' with context [CB _ ?t] =>
      lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "hk" in set (j := t) in HH'; clearbody j end.
    clear MU WM.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
      pose proof (munch_refl [(HA, HA + 24)]%Z m5) as MU; pose proof (wmono_refl asegs m5) as WM;
      assert (JOIN : forall (sec usec cap32 len32 : Z) (capw lenw : word) (m7 : mem) (ra7 t07 t17 t27 a37 a47 a57 a67 a77 r23' t37 t47 t57 t67 : word),
        munch [(HA, HA + 24)]%Z m5 m7 -> wmono asegs m5 m7 -> mem_inv asegs m7 ->
        stk asegs m7 lo SPA -> stk asegs m7 (SPA + 120) (bv_unsigned sp + -104) ->
        rw_cells asegs m7 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells asegs m7 Fb [C8 k0; C8 k1; C8 k2; CB (Z.to_nat 8160) fj; C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))] ->
        rw_cells asegs m7 (Z.shiftr Fb 3 + 2147450880) np_shadow -> rw_cells asegs m7 (Z.shiftr Fb 3 + 2147450892) [CB 512 dsh] ->
        rw_cells asegs m7 SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 c4; C8 c5; C8 c6; C8 c8; C8 c7;
                               C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
        rw_cells asegs m7 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 capw; C4 lenw] ->
        rw_cells asegs m7 DA [dw] ->
        (0 <= sec < 2^32)%Z -> (0 <= usec < 2^32)%Z -> (bv_unsigned capw mod 2^32 = cap32)%Z -> (bv_unsigned lenw mod 2^32 = len32)%Z ->
        implMG RNGx (np_body_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) sec usec cap32 len32) sx POSTQ
          (MS (mkR ra7 (Z_to_bv 64 SPA) gp tp t07 t17 t27 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (HA + 20)) (Z_to_bv 64 (P + 660)) (Z_to_bv 64 0) a37 a47 a57 a67 a77
                   (Z_to_bv 64 (HA + 16)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
                   (Z_to_bv 64 (Fb + 32)) r23' (Z_to_bv 64 HA) (Z_to_bv 64 2147450880)
                   (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 648)) t37 t47 t57 t67)
              F (Z_to_bv 64 0x889f4) fc None m7 (seg_rom asegs)))
    end.
    { intros sec usec cap32 len32 capw lenw m7 ra7 t07 t17 t27 a37 a47 a57 a67 a77 r23' t37 t47 t57 t67 MU7 WM7 MI7 ST7 STG7 FR7 FRC7 SHC7 SHD7 FRA7 HH7 HD7 Rs Ru Fc Fl.
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m7 [] _ (bv_unsigned sp) (Forall_nil _) FX G5 MU7 WM7 ltac:(lia)) as [G7 AG7].
      assert (PC7 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m7)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU7| exact WM7|]; intros a _ Ha; exact Ha| | exact PC5];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ [] _ (bv_unsigned sp) (Forall_nil _) FX G5 a Ha)).
      subst POSTQ. rewrite <- Fc, <- Fl.
      rewrite <- (Z_to_bv_bv_unsigned capw), <- (Z_to_bv_bv_unsigned lenw) in HH7.
      pose proof (bv_unsigned_in_range 64 capw) as Rc. pose proof (bv_unsigned_in_range 64 lenw) as Rl. unfold bv_modulus in Rc, Rl.
      eapply (np_scale HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP) with (dsh := dsh) (dw := dw);
        [ exact CTX | | exact PC7 | exact FRA7 | exact HH7 | exact HD7 | exact Hd | exact Rs | exact Ru | lia | lia | exact AL0 ].
      unfold np_inv0. split; [exact FP|]. split; [exact G7|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG5m|]. eapply agrees_on_weaken; [exact AG7|]. intros a (K & (QN & _)). split; [exact K|]. split; [exact QN| exact I]. }
      split; [exists k0, k1, k2, fj; assumption|]. split; assumption. }
    destruct (k_sw k) eqn:ESW; cbn [Z.b2z].
    - (* [comment removed for export] *)
      if_false.
      eapply evtF_cut;
        [ eapply np_swap_seq with (HB := (Fb + 32)%Z) (HA := HA) (bH := bH) (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3) (g4 := g4) (g5 := g5) (g6 := g6) (g7 := g7)
                                  (g8 := g8) (g9 := g9) (g10 := g10) (g11 := g11) (g12 := g12) (g13 := g13) (g14 := g14) (g15 := g15);
          [ assumption | lia | lia | eapply rng_sub'; [exact FRNG| lia] | repeat (apply Forall_cons; [assumption|]); apply Forall_nil | exact HB16 | exact HH'
          | eassumption | lia | exact HA8 | lia | lia | lia | lia | lia | exact HARNG | exact HARSH | lia ]
        | ].
      cbv beta. intros ms' PO. destruct PO as (a1v & a3v & a4v & a5v & a6v & capw & lenw & m7 & -> & MU7 & WM7 & MI7 & HH7 & Fc & Fl).
      clear HH'.
      lazymatch type of MU7 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU7 WM7 end.
      clear MU7 WM7.
      zstep.
      ck0 PUNP; ck_go.
      rewrite (bswap32_le4val g0 g1 g2 g3), (bswap32_le4val g4 g5 g6 g7), (bswap32_le4val g8 g9 g10 g11), (bswap32_le4val g12 g13 g14 g15) by lia.
      apply evtF_done.
      eapply (JOIN (le4val g3 g2 g1 g0) (le4val g7 g6 g5 g4) (le4val g11 g10 g9 g8) (le4val g15 g14 g13 g12) capw lenw);
        [ exact MU | exact WM | exact MI7 | sassume | sassume | sassume | sassume | sassume | sassume | sassume | exact HH7 | sassume
        | unfold le4val; lia | unfold le4val; lia | exact Fc | exact Fl ].
    - (* [comment removed for export] *)
      if_true.
      ub_null.
      zstep. if_false.
      ck0 HAUNP; ck_go.
      zstep.
      ck0 HAUNP; ck_go. rewrite (sx32_lit g12 g13 g14 g15) by lia.
      zstep.
      ck0 HAUNP; ck_go.
      zstep. rewrite (np_zx32_small (le4val g0 g1 g2 g3)) by (unfold le4val; lia).
      zstep. zstep.
      ck0 HAUNP; ck_go.
      zstep. rewrite (np_zx32_small (le4val g4 g5 g6 g7)) by (unfold le4val; lia).
      zstep. zstep.
      ck0 PUNP; ck_go.
      apply evtF_done.
      eapply (JOIN (le4val g0 g1 g2 g3) (le4val g4 g5 g6 g7) (le4val g8 g9 g10 g11) (le4val g12 g13 g14 g15) (Z_to_bv 64 (sxv g8 g9 g10 g11)) (Z_to_bv 64 (sxv g12 g13 g14 g15)));
        [ exact MU | exact WM | assumption | sassume | sassume | sassume | sassume | sassume | sassume | sassume | sassume | sassume
        | unfold le4val; lia | unfold le4val; lia
        | pose proof (sxv_range g8 g9 g10 g11); rewrite unsigned_lit by lia; apply sxv_mod32; lia
        | pose proof (sxv_range g12 g13 g14 g15); rewrite unsigned_lit by lia; apply sxv_mod32; lia ].
  Qed.
  End Sz3.
  Lemma np_hdr_post : ltac:(let t := eval cbv delta [np_hdr_post__stmt] in np_hdr_post__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r23 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb hb junk' hcs dw. ltac2:(SecDiet.SzSec.closeP 'np_hdr_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpHdr.
End CANSEC1.
End TwB.
End F_sfnp_hdrA.

(* [comment removed for export] *)
Module F_sfnp_rdA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_exitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_normA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_bodyA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_scaleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_sfnp_swapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_hdrA__A3P.F_sfnp_hdrA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpRd.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SET00 : set_shadow_stmt SET_SHADOW_00 0.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.

  (* [comment removed for export] *)
  Definition np_rdhdr__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (hcs : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9;
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat -> (0 < alloc)%Z ->
    implMG RNGx (mo_bind MOps (e_fread (prims HO FO sites) (k_f k) (DStack SiteSfHdr 0) (k_hs k))
                   (fun hb : list Z =>
                      if negb (zlength hb =? k_hs k)%Z
                      then mbind (e_ferror (prims HO FO sites) (k_f k))
                             (fun e : bool => if e then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string [])
                                                              (fun m0 => e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf m0 (pv k bq bsz alloc data eb)))
                                              else if negb (zlength hb =? 0)%Z
                                                   then e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf (Msg.trunc_header (k_hs k) (zlength hb)) (pv k bq bsz alloc data eb))
                                                   else e_fret (prims HO FO sites) FF_NEXT_PACKET (0%Z, hdr0, pv k bq bsz alloc data eb))
                      else np_body_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb)
                             (if k_sw k then bswap32 (get_le32 hb 0) else get_le32 hb 0) (if k_sw k then bswap32 (get_le32 hb 4) else get_le32 hb 4)
                             (if k_sw k then bswap32 (get_le32 hb 8) else get_le32 hb 8) (if k_sw k then bswap32 (get_le32 hb 12) else get_le32 hb 12))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 DA) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               r22 r23 (Z_to_bv 64 HA) (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 648)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88328) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 k bq Bx bsz alloc data eb hcs dw : ltac2:(SecDiet.SzSec.tyM 'np_rdhdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_rdhdr__body : ltac2:(SecDiet.SzSec.bodyP 'np_rdhdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
    intros CTX INV PC FRA HH Hh HD Hd AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear BUF.
    (* [comment removed for export] *)
    assert (EAf : Afx = Af).
    { pose proof (HAL _ _ _ _ _ _ _ _ G (in_or_app _ _ _ (or_intror HinFx))) as E1.
      pose proof (HAL _ _ _ _ _ _ _ _ G (in_or_app _ _ _ (or_intror HinF))) as E2. unfold pv in E1. cbn [cb_tok cb_addr fst snd pc_rfile] in E1, E2. congruence. }
    subst Afx. clear HinFx.
    pose proof (munch_refl [(SPA, SPA + 120)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    cbn [mo_bind MOps e_fread prims].
    apply implMG_from_evtF.
    (* [comment removed for export] *)
    zstep.
    ck0 PUNP; ck_go.
    zstep.
    do 2 zstep.
    ck0_at PUNP (P + 648)%Z; ck_go.
    (* [comment removed for export] *)
    do 2 zstep.
    do 3 zstep.
    zstep.
    zstep.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA, SPA + 120)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ mx _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G3 AG3];
      assert (PC3 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mx)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))));
      assert (INV3 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
                             (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mx)
    end.
    { unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & _). split; [exact K| exact I]. }
      split; [exists k0, k1, k2, fj; assumption|]. split; assumption. }
    cbn [app] in G3.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    pose proof (unp_of_sh_bytes _ _ _ 4%nat 3%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPH.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPH. change (8 * Z.of_nat 3)%Z with 24%Z in UNPH.
    apply (rw_cells_split_CB asegs _ _ [_; _; _] (Z.to_nat 8160) _ [_] [8%nat; Z.to_nat (k_hs k); (Z.to_nat 8160 - 8 - Z.to_nat (k_hs k))%nat]) in FRC; [| cbn [sum_nat]; (atop_facts; plia)].
    cbn [mk_CB_cells app] in FRC.
    lazymatch type of FRC with rw_cells _ _ _ [_; _; _; CB _ ?l0; CB _ ?l1; CB _ ?l2; _] =>
      set (j0 := l0) in FRC; set (j1 := l1) in FRC; set (j2 := l2) in FRC; clearbody j0 j1 j2 end.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [F0 F12]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in F0, F12.
    destruct (rw_cells_cut _ _ _ 1 F12) as [F1 F2]. clear F12. cbn [firstn skipn cells_size csize Nat.add] in F1, F2.
    lazymatch type of F1 with rw_cells _ _ ?A _ => replace A with (Fb + 32)%Z in F1, F2 by lia end.
    lazymatch type of F2 with rw_cells _ _ ?A _ => replace A with (Fb + 32 + k_hs k)%Z in F2 by lia end.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SiteSfHdr 32%Z G3 (or_introl eq_refl) eq_refl).
      replace (Fb + 32 + 0)%Z with (Fb + 32)%Z by lia.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G3|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact F1
        | split; [right; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia|
                               eapply unpoisoned_sub; [exact UNPH| lia| lia]] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    destruct PO as (FP6 & av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 557932)) with (Z_to_bv 64 557932) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (KFR : forall A cs, rw_cells asegs m1 A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 8192)%Z ->
                   (A + Z.of_nat (cells_size cs) <= Fb + 32 \/ Fb + 32 + k_hs k <= A)%Z -> rw_cells asegs m6 A cs)
      by (intros A cs HC H1 H3 H4; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha; split; [|lia];
          right; right; left; apply in_frames_In; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    apply KFR in F0; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KFR in F2; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia]. clear KFR.
    assert (LG : (length got <= Z.to_nat (k_hs k))%nat) by (unfold zlength in GOTL; lia).
    pose proof (rw_cells_uncut _ _ _ _ _ F0 HD6 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
    pose proof (rw_cells_uncut _ _ _ _ _ J1 F2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2. clear J1 F0 F2.
    apply (rw_cells_merge asegs m6 Fb [C8 k0; C8 k1; C8 k2] [_; _; _; _] [_]) in J2.
    replace (cells_size [CB 8 j0; CB (length got) (map b8 got); CB (Z.to_nat (k_hs k) - length got) junk6; CB (Z.to_nat 8160 - 8 - Z.to_nat (k_hs k)) j2])
      with (Z.to_nat 8160) in J2 by (cbn [cells_size csize]; (atop_facts; plia)).
    cbn [app] in J2.
    assert (INV6 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG6 s6'
                           (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh m6).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (Fb + 32 <= a < Fb + 32 + k_hs k)%Z);
        [ exact INV3 | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia | intros a _ Ha; lia
        | eexists k0, k1, k2, _; exact J2 ]. }
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6).
    { eapply PCAPR_agree; [exact AG6| | exact PC3]. intros a Ha. split; [right; left; apply in_block_app; right; exact Ha|].
      intros Hin. eapply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G3);
        [ apply in_frames_In; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]
        | apply in_block_app; left; apply in_block_app; right; exact Ha ]. }
    apply (agrees_rw_cells _ _ _ _ _ AG6) in FRA; [|intros a Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HH; [|intros a Ha; rewrite Hh in Ha; split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)| lia]| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HD; [|intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)| lia]| lia]].
    subst POSTQ.
    eapply (np_hdr_post HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP) with (dsh := dsh) (hcs := hcs) (dw := dw);
      [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HD6 | exact HH | exact Hh | exact HD | exact Hd | exact GOTR | exact GOTL | exact AL0 ].
  Qed.
  End Sz1.
  Lemma np_rdhdr : ltac:(let t := eval cbv delta [np_rdhdr__stmt] in np_rdhdr__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c11 c12 c13 c14 k bq Bx bsz alloc data eb hcs dw. ltac2:(SecDiet.SzSec.closeP 'np_rdhdr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpRd.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_chkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_bodyA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_sfchk_fsegA__B3P.F_sfnp_scaleA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_sfnp_swapA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_hdrA__A3P.F_sfnp_hdrA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpRd.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SET00 : set_shadow_stmt SET_SHADOW_00 0.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.

  (* [comment removed for export] *)
  Definition np_rdhdr__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 : word)
      (r18 c0 c1 c2 c3 c4 c5 c6 c7 c8 c11 c12 c13 c14 : word)   (* [comment removed for export] *)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (hcs : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 c11; C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat -> (0 < alloc)%Z ->
    implMG RNGx (mo_bind MOps (e_fread (prims HO FO sites) (k_f k) (DStack SiteSfHdr 0) (k_hs k))
                   (fun hb : list Z =>
                      if negb (zlength hb =? k_hs k)%Z
                      then mbind (e_ferror (prims HO FO sites) (k_f k))
                             (fun e : bool => if e then mbind (errmsg_for_errno MOps (prims HO FO sites) "error reading dump file"%string [])
                                                              (fun m0 => e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf m0 (pv k bq bsz alloc data eb)))
                                              else if negb (zlength hb =? 0)%Z
                                                   then e_fret (prims HO FO sites) FF_NEXT_PACKET ((-1)%Z, hdr0, set_errbuf (Msg.trunc_header (k_hs k) (zlength hb)) (pv k bq bsz alloc data eb))
                                                   else e_fret (prims HO FO sites) FF_NEXT_PACKET (0%Z, hdr0, pv k bq bsz alloc data eb))
                      else np_body_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb)
                             (if k_sw k then bswap32 (get_le32 hb 0) else get_le32 hb 0) (if k_sw k then bswap32 (get_le32 hb 4) else get_le32 hb 4)
                             (if k_sw k then bswap32 (get_le32 hb 8) else get_le32 hb 8) (if k_sw k then bswap32 (get_le32 hb 12) else get_le32 hb 12))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               r22 r23 (Z_to_bv 64 HA) (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 648)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8874c) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 r18 c0 c1 c2 c3 c4 c5 c6 c7 c8 c11 c12 c13 c14 k bq Bx bsz alloc data eb hcs dw : ltac2:(SecDiet.SzSec.tyM 'np_rdhdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_rdhdr__body : ltac2:(SecDiet.SzSec.bodyP 'np_rdhdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
 intros CTX INV PC FRA HH Hh HD Hd AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear BUF.
    (* [comment removed for export] *)
    assert (EAf : Afx = Af).
    { pose proof (HAL _ _ _ _ _ _ _ _ G (in_or_app _ _ _ (or_intror HinFx))) as E1.
      pose proof (HAL _ _ _ _ _ _ _ _ G (in_or_app _ _ _ (or_intror HinF))) as E2. unfold pv in E1. cbn [cb_tok cb_addr fst snd pc_rfile] in E1, E2. congruence. }
    subst Afx. clear HinFx.
    pose proof (munch_refl [(SPA, SPA + 120)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    cbn [mo_bind MOps e_fread prims].
    apply implMG_from_evtF.
    (* [comment removed for export] *)
    zstep.
    ck0 PUNP; ck_go.
    (* [comment removed for export] *)
    ub_null.
    zstep. ub_al 7%Z ltac:(al16 P2). zstep. if_false.   (* [comment removed for export] *)
    do 2 zstep.
    ck0_at PUNP (P + 648)%Z; ck_go.
    (* [comment removed for export] *)
    do 2 zstep.
    do 3 zstep.
    zstep.
    zstep.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA, SPA + 120)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ mx _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G MU WM ltac:(lia)) as [G3 AG3];
      assert (PC3 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mx)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))));
      assert (INV3 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
                             (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mx)
    end.
    { unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G3|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG3|]. intros a (K & _). split; [exact K| exact I]. }
      split; [exists k0, k1, k2, fj; assumption|]. split; assumption. }
    cbn [app] in G3.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    pose proof (unp_of_sh_bytes _ _ _ 4%nat 3%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPH.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPH. change (8 * Z.of_nat 3)%Z with 24%Z in UNPH.
    apply (rw_cells_split_CB asegs _ _ [_; _; _] (Z.to_nat 8160) _ [_] [8%nat; Z.to_nat (k_hs k); (Z.to_nat 8160 - 8 - Z.to_nat (k_hs k))%nat]) in FRC; [| cbn [sum_nat]; (atop_facts; plia)].
    cbn [mk_CB_cells app] in FRC.
    lazymatch type of FRC with rw_cells _ _ _ [_; _; _; CB _ ?l0; CB _ ?l1; CB _ ?l2; _] =>
      set (j0 := l0) in FRC; set (j1 := l1) in FRC; set (j2 := l2) in FRC; clearbody j0 j1 j2 end.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [F0 F12]. clear FRC. cbn [firstn skipn cells_size csize Nat.add] in F0, F12.
    destruct (rw_cells_cut _ _ _ 1 F12) as [F1 F2]. clear F12. cbn [firstn skipn cells_size csize Nat.add] in F1, F2.
    lazymatch type of F1 with rw_cells _ _ ?A _ => replace A with (Fb + 32)%Z in F1, F2 by lia end.
    lazymatch type of F2 with rw_cells _ _ ?A _ => replace A with (Fb + 32 + k_hs k)%Z in F2 by lia end.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest].
      rewrite (gl_site _ _ _ GL _ _ _ _ _ _ _ _ _ _ SiteSfHdr 32%Z G3 (or_introl eq_refl) eq_refl).
      replace (Fb + 32 + 0)%Z with (Fb + 32)%Z by lia.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G3|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact F1
        | split; [right; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia|
                               eapply unpoisoned_sub; [exact UNPH| lia| lia]] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    destruct PO as (FP6 & av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 559000)) with (Z_to_bv 64 559000) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (KFR : forall A cs, rw_cells asegs m0 A cs -> (Fb <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fb + 8192)%Z ->
                   (A + Z.of_nat (cells_size cs) <= Fb + 32 \/ Fb + 32 + k_hs k <= A)%Z -> rw_cells asegs m6 A cs)
      by (intros A cs HC H1 H3 H4; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha; split; [|lia];
          right; right; left; apply in_frames_In; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    apply KFR in F0; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia].
    apply KFR in F2; [|lia|cbn [cells_size csize Nat.add]; lia|cbn [cells_size csize Nat.add]; lia]. clear KFR.
    assert (LG : (length got <= Z.to_nat (k_hs k))%nat) by (unfold zlength in GOTL; lia).
    pose proof (rw_cells_uncut _ _ _ _ _ F0 HD6 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
    pose proof (rw_cells_uncut _ _ _ _ _ J1 F2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2. clear J1 F0 F2.
    apply (rw_cells_merge asegs m6 Fb [C8 k0; C8 k1; C8 k2] [_; _; _; _] [_]) in J2.
    replace (cells_size [CB 8 j0; CB (length got) (map b8 got); CB (Z.to_nat (k_hs k) - length got) junk6; CB (Z.to_nat 8160 - 8 - Z.to_nat (k_hs k)) j2])
      with (Z.to_nat 8160) in J2 by (cbn [cells_size csize]; (atop_facts; plia)).
    cbn [app] in J2.
    assert (INV6 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG6 s6'
                           (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh m6).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (Fb + 32 <= a < Fb + 32 + k_hs k)%Z);
        [ exact INV3 | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia | intros a _ Ha; lia
        | eexists k0, k1, k2, _; exact J2 ]. }
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6).
    { eapply PCAPR_agree; [exact AG6| | exact PC3]. intros a Ha. split; [right; left; apply in_block_app; right; exact Ha|].
      intros Hin. eapply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G3);
        [ apply in_frames_In; exists (FF_NEXT_PACKET, Fb, 8192%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]
        | apply in_block_app; left; apply in_block_app; right; exact Ha ]. }
    apply (agrees_rw_cells _ _ _ _ _ AG6) in FRA; [|intros a Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HH; [|intros a Ha; rewrite Hh in Ha; split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL IFL)| lia]| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HD; [|intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL IFL)| lia]| lia]].
    subst POSTQ.
    eapply (np_hdr_post HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP) with (dsh := dsh) (hcs := hcs) (dw := dw);
      [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HD6 | exact HH | exact Hh | exact HD | exact Hd | exact GOTR | exact GOTL | exact AL0 ].
  Qed.
  End Sz1.
  Lemma np_rdhdr : ltac:(let t := eval cbv delta [np_rdhdr__stmt] in np_rdhdr__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 r18 c0 c1 c2 c3 c4 c5 c6 c7 c8 c11 c12 c13 c14 k bq Bx bsz alloc data eb hcs dw. ltac2:(SecDiet.SzSec.closeP 'np_rdhdr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpRd.
End CANSEC1.
End TwB.
End F_sfnp_rdA.

(* [comment removed for export] *)
Module F_sfnp_mainA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_exitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_normA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_failA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_bodyA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_scaleA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_sfnp_swapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_hdrA__A3P.F_sfnp_hdrA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_hdrA__A3P.F_sfnp_rdA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfnp_psegA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.
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
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32N : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
Definition np_sh_split__stmt : Prop := forall m S (sj : list byte) n,
  rw_cells asegs m S [CB 540 (repeat (Z_to_bv 8 0) 540); CB n sj] ->
  rw_cells asegs m S (repeat (C1 (Z_to_bv 8 0)) 12) /\ rw_cells asegs m (S + 12) [CB 512 (repeat (Z_to_bv 8 0) 512)]
  /\ rw_cells asegs m (S + 524) (repeat (C1 (Z_to_bv 8 0)) 16).
Section Sz2.
Variables m S sj n : ltac2:(SecDiet.SzSec.tyM 'np_sh_split__stmt "vvvv" @m).
#[using="Type"] Lemma np_sh_split__body : ltac2:(SecDiet.SzSec.bodyP 'np_sh_split__stmt "vvvv").
Proof.
  intros HC.
 pose proof HC as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & Lsj & _).
  assert (HC' : rw_cells asegs m S (repeat (C1 (Z_to_bv 8 0)) 12 ++ [CB 512 (repeat (Z_to_bv 8 0) 512)] ++ repeat (C1 (Z_to_bv 8 0)) 16 ++ [CB n sj])).
  { eapply rw_cells_recell; [exact HC| |].
    - apply cells_wf_app. split; [apply cells_wf_repeat_C1|]. cbn [app]. split; [apply repeat_length|]. apply cells_wf_app. split; [apply cells_wf_repeat_C1|].
      cbn. split; [exact Lsj| exact I].
    - rewrite !cells_bytes_app, !cells_bytes_repeat_C1. cbn [cells_bytes cbytes]. rewrite !app_nil_r.
      change 540%nat with (12 + (512 + 16))%nat. rewrite !repeat_app, <- !app_assoc. reflexivity. }
  apply rw_cells_app in HC' as [H1 HC']. apply rw_cells_app in HC' as [H2 HC']. apply rw_cells_app in HC' as [H3 _].
  change (cells_size (repeat (C1 (Z_to_bv 8 0)) 12)) with 12%nat in *. cbn [cells_size csize Nat.add] in H3.
  split; [exact H1|]. split; [replace (S + 12)%Z with (S + Z.of_nat 12)%Z by lia; exact H2|].
  lazymatch type of H3 with rw_cells _ _ ?A _ => replace (S + 524)%Z with A by lia end. exact H3.
Qed.
End Sz2.
#[using="Type"] Lemma np_sh_split : ltac:(let t := eval cbv delta [np_sh_split__stmt] in np_sh_split__stmt in exact t).
Proof. intros m S sj n. ltac2:(SecDiet.SzSec.closeP 'np_sh_split__body "vvvv"). Qed.

Section NpMain.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FENTER7 : fenter7_stmt_o FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SET00 : set_shadow_stmt SET_SHADOW_00 0.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.

  Definition pcap_next_packet_proofA__stmt : Prop := pcap_next_packet_stmt HO FO sites GIOA TP.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P HA DA p fuel hcs dc : ltac2:(SecDiet.SzSec.tyM 'pcap_next_packet_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_next_packet_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_next_packet_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FENTER7 FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
    intros PRE UC TR NF PC NG S0A -> -> -> HH Hh HD Hd OHA ODA DHD HA8 DA8.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    destruct p as [self rfile bufsize bufalloc buffer bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header priv].
    destruct priv as [sf|ng oif]; [| discriminate NG]. clear NG. destruct sf as [hdrsize lsw scl].
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & _ & _ & _ & _ & IFS & WF)).
    cbn [pc_priv ifaces_ok] in IFS. subst I.
    pose proof WF as WF'. unfold pcap_wf in WF'. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
         pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in WF'.
    destruct WF' as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & WHS & WBB). subst brk prec.
    assert (AL0 : (0 < bufalloc)%Z) by lia.
    set (k := mkNpk hptr self rfile swapped vmaj vmin snapshot linktype ltext header hdrsize lsw scl).
    change (mkPcap self rfile bufsize bufalloc buffer bufdata swapped vmaj vmin snapshot linktype ltext 0 0 errbuf header (PrivPcap (mkSf hdrsize lsw scl)))
      with (pv k buffer bufsize bufalloc bufdata errbuf) in *.
    rewrite EPB in G, PC. cbn [pc_rfile pv] in HinF. change rfile with (k_f k) in HinF.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    unfold PCAP_L2_STACK in BU.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (ICL0 : incl CLc (CLc ++ pcap_blocks (pv k buffer bufsize bufalloc bufdata errbuf) P B 0)) by (apply incl_appl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL0 (incl_refl _))) as (HALO & HAHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL0 (incl_refl _))) as (DALO & DAHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL0 (incl_refl _)) ltac:(lia)) as HABAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL0 (incl_refl _)) ltac:(lia)) as DABAND.
    band_ind HABAND bH. band_ind DABAND bD.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    unfold next_packet_op. cbn [pc_priv pv]. rewrite (np_model_eq MOps (prims HO FO sites)). cbn [e_fenter prims].
    unfold np_entry, is_ng. cbn [pc_priv pv pk_next_pcap PK].
    remember (bv_unsigned sp - 224 - (bv_unsigned sp - 224) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 240 <= SPA <= bv_unsigned sp - 224 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -224) - (bv_unsigned sp + -224) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    destruct SPAP as (SPAB & SPA32 & ESPA').
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 120%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    rewrite land_m32N by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -104)%Z.
    destruct (stk_split asegs _ lo (SPA + 120) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 120) 120 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 120) with 120%Z in STL, FRA. replace (SPA + 120 - 120)%Z with SPA in STL, FRA by lia.
    destruct (spill_words _ _ _ FRA) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & FRW). clear FRA.
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    (* [comment removed for export] *)
    do 5 zstep.
    do 2 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 2 zstep.
    zstep.
    (* [comment removed for export] *)
    set (PBx := pcap_blocks (pv k buffer bufsize bufalloc bufdata errbuf) P B 0) in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW0 : Forall (pcap_iv FL PBx) [(bv_unsigned sp - 240, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ PBx) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW0]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    assert (FWp : Forall (own_ivA ([] : list fblock) ([] : list (@cblock hptr)) (bv_unsigned sp)) [(bv_unsigned sp - 240, bv_unsigned sp)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    assert (PC1 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB m1).
    { eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC].
      intros a Ha. exact (pb_outside _ _ _ GL _ _ _ _ _ _ FL [] _ _ [] (bv_unsigned sp) FWp (Forall_nil _) G a Ha). }
    rename MU into MU0. rename WM into WM0. clear FW0 FWp GOT SHB SUA GSU.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER7 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { reflexivity. }
    { apply NF. left. reflexivity. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk sjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ LSJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_NEXT_PACKET) with 8192%Z in *.
    change (Z.to_nat (8192 - 32)) with (Z.to_nat 8160) in *.
    change (Z.to_nat (4320 / 8)) with 540%nat in SHC.
    destruct (np_sh_split _ _ _ _ SHC) as (SH12 & SHD & SH16). clear SHC LSJ sjunk.
    cbn [repeat] in SH12, SH16.
    replace (ret_pc (Z_to_bv 64 557572)) with (Z_to_bv 64 557572) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. pose proof (Forall_inv FAll) as FRM. pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 8192 3) with 1024%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRW; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HH'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL0 (incl_refl _))| exact Ha]].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL0 (incl_refl _))| exact Ha]].
    assert (PC2 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB m2)
      by (eapply PCAPR_agree; [exact AG1| intros a Ha; right; left; apply in_block_app; right; exact Ha| exact PC1]).
    assert (AGb : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; apply in_block_app; left; exact Ha| apply incl_refl]. }
    clear PC1 AGa AG1 G0 MU0 WM0 m1 MI STL.
    replace (Z.shiftr Fb 3 + 2147450880 + 12)%Z with (Z.shiftr Fb 3 + 2147450892)%Z in SHD by lia.
    replace (Z.shiftr Fb 3 + 2147450880 + 524)%Z with (Z.shiftr Fb 3 + 2147451404)%Z in SH16 by lia.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 1024 <= 0x10007fff8000)%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    destruct SHLO as (SLO & SHI).
    assert (RSP120 : rng RNG SPA 120) by (eapply rng_sub'; [exact RSPA| lia]).
    assert (SPALO : (17594333495296 <= SPA)%Z) by (atop_facts; lia).
    assert (LOLO : (17594333495296 <= lo)%Z) by (atop_facts; lia).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL0 (incl_refl _)) ltac:(lia)) as (kH & kHr & kH1 & kH2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL0 (incl_refl _)) ltac:(lia)) as (kD & kDr & kD1 & kD2).
    cbn [fb_addr fb_size fst snd] in kH1, kH2, kD1, kD2.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    call np_poison_seq; [try eassumption .. | ]; [lia .. | ].
    lazymatch goal with HH : rw_cells asegs _ SPA _ |- _ => rename HH into FRW end.
    lazymatch goal with HH : rw_cells asegs _ Fb _ |- _ => rename HH into FRC end.
    lazymatch goal with HH : rw_cells asegs _ (Z.shiftr Fb 3 + 2147450880)%Z _ |- _ => rename HH into SH12 end. unfold np_shadow_f8 in SH12.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 8192, bv_unsigned sp); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ mm _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ PBx _) FW) (Forall_nil _) G1 MU WM ltac:(lia)) as [G3 AG3];
      assert (PC3 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC2];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PBx) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G1 a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))))
    end.
    cbn [app] in G3.
    clear MU WM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (SETF8 _ spa) with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450892)%Z) (n := 512%Z) (old := repeat (Z_to_bv 8 0) 512);
        [ assumption | rewrite Hspa; exact ST1 | rewrite Hspa; unfold FAKE_STACK; lia | lia
        | exact (proj1 (gl_rt _ _ _ GL _ _ _ _ _ _ _ G3)) | exact (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G3)
        | reflexivity | reflexivity | lia | lia | exact SHD
        | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]
      | ].
    cbv beta. intros ms' PO. destruct PO as (a0v & m4 & E & MUc & WMc & MIc & STc & SHD4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. unfold FAKE_STACK in MUc.
    replace (ret_pc (Z_to_bv 64 557760)) with (Z_to_bv 64 557760) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (FWc : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(SPA - 4096, SPA); (Z.shiftr Fb 3 + 2147450892, Z.shiftr Fb 3 + 2147450892 + 512)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m4 _ [] (bv_unsigned sp)
                (Forall_impl _ (own_ivA_PB _ PBx _) FWc) (Forall_nil _) G3 MUc WMc ltac:(lia)) as [G4 AG4].
    assert (PC4 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB m4).
    { eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC3].
      intros a Ha. exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PBx) _ _ _ _ _ [] (bv_unsigned sp) FWc (Forall_nil _) G3 a (proj2 (in_block_app _ _ _) (or_intror Ha))). }
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end.
    assert (AGc : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m4).
    { eapply agrees_on_trans; [exact AGb|]. eapply agrees_on_trans; (eapply agrees_on_weaken; [eassumption|]); intros a K; (split; [exact K| exact I]). }
    clear FWc G1 G3 AG3 AG4 PC2 PC3 AGb.
    try clear MUc. try clear WMc. try clear ST1. try clear SHD. try clear FW. try subst spa. try clear Hspa. try clear MI1.
    cbn [app] in G4.
    (* [comment removed for export] *)
    assert (HinP : In (k_self k, P, 664%Z) ((CLc ++ PBx) ++ FB)) by (subst PBx; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 HinP) as ((PBAND & _ & PTOP & P16) & P0 & _ & PRNG & PRSH & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PRNG, PRSH.
    band_ind PBAND bP.
    assert (PHI : (P + 664 <= 2^47)%Z) by (atop_facts; lia).
    pose proof (munch_refl [(Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z m4) as MU.
    pose proof (wmono_refl asegs m4) as WM.
    call np_f3_seq; [try eassumption .. | ]; [lia .. | ].
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ mm _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ PBx _) FW) (Forall_nil _) G4 MU WM ltac:(lia)) as [G5 _];
      assert (PC5 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC4];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PBx) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G4 a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))));
      assert (C48 : rw_cells asegs mm (P + 48) [C8 (Z_to_bv 64 (P + 648))])
    end.
    { clear EPB WF W1 W2 W3 W4 W7 W8 W9 W10 W11 W12 WHS WBB Af HinF. subst PBx. np_open PC5.
      destruct (rw_cells_cut _ _ _ 7 CELLS) as [_ C7]. cbn [firstn skipn cells_size csize Nat.add] in C7.
      destruct (rw_cells_cut _ _ _ 1 C7) as [C48 _]. cbn [firstn skipn cells_size csize Nat.add] in C48.
      lazymatch type of C48 with rw_cells _ _ ?A _ => replace A with (P + 48)%Z in C48 by lia end. exact C48. }
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as (_ & _ & PUNP & _). cbn [cb_addr cb_size fst snd] in PUNP.
    clear G5 PC5.
    call np_s1_seq; [try eassumption .. | ]; [lia .. | ].
    lazymatch goal with HH : rw_cells asegs _ (Z.shiftr Fb 3 + 2147450880)%Z _ |- _ => rename HH into SH12 end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ mm _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ PBx _) FW) (Forall_nil _) G4 MU WM ltac:(lia)) as [G6 AG6];
      assert (PC6 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC4];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PBx) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G4 a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))))
    end.
    cbn [app] in G6. subst PBx.
    assert (CTX : np_ctx TP ra sp tp s0 L RNG CLc FB FL trC lo HA DA Af SPA (k_f k) m).
    { unfold np_ctx, PCAP_L2_STACK. do 5 (split; [first [assumption | lia]|]).
      split; [split; [exact RSTK| split; [exact RIMG| split; [exact RISH| exact RTLS]]]|].
      repeat (split; [first [assumption | reflexivity | lia]|]). first [assumption | lia]. }
    apply evtF_done. subst POSTQ0 POSTQ.
    eapply (np_rdhdr HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP)
      with (dsh := repeat (Z_to_bv 8 248) (Z.to_nat 512)) (hcs := [CB 24 hj]) (dw := CB 8 dj);
      [ exact CTX | | exact PC6 | exact FRW | exact HH' | reflexivity | exact HD' | reflexivity | exact AL0 ].
    unfold np_inv0. split; [apply fp_le_refl|]. split; [exact G6|]. split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [exact FR|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGc|]; intros a (K & _); exact K|].
             eapply agrees_on_weaken; [exact AG6|]. intros a (K & _). split; [exact K| exact I]. }
    split; [exists (Z_to_bv 64 1102416563), (Z_to_bv 64 115235), (Z_to_bv 64 557448), fjunk; exact FRC|]. split; [exact SH12| exact SHD4].
  Qed.
  End Sz3.
  Theorem pcap_next_packet_proofA : ltac:(let t := eval cbv delta [pcap_next_packet_proofA__stmt] in pcap_next_packet_proofA__stmt in exact t).
  Proof using GL HAL GPL FENTER7 FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. red. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P HA DA p fuel hcs dc. ltac2:(SecDiet.SzSec.closeP 'pcap_next_packet_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpMain.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_sfchk_fsegA__B3P.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_chkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_bodyA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_sfchk_fsegA__B3P.F_sfnp_scaleA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_sfnp_swapA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_hdrA__A3P.F_sfnp_hdrA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_hdrA__A3P.F_sfnp_rdA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_failA__A3P.F_sfnp_psegA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32N : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
Definition np_sh_split__stmt : Prop := forall m S (sj : list byte) n,
  rw_cells asegs m S [CB 540 (repeat (Z_to_bv 8 0) 540); CB n sj] ->
  rw_cells asegs m S (repeat (C1 (Z_to_bv 8 0)) 12) /\ rw_cells asegs m (S + 12) [CB 512 (repeat (Z_to_bv 8 0) 512)]
  /\ rw_cells asegs m (S + 524) (repeat (C1 (Z_to_bv 8 0)) 16).
Section Sz2.
Variables m S sj n : ltac2:(SecDiet.SzSec.tyM 'np_sh_split__stmt "vvvv" @m).
#[using="Type"] Lemma np_sh_split__body : ltac2:(SecDiet.SzSec.bodyP 'np_sh_split__stmt "vvvv").
Proof.
  intros HC.
 pose proof HC as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & Lsj & _).
  assert (HC' : rw_cells asegs m S (repeat (C1 (Z_to_bv 8 0)) 12 ++ [CB 512 (repeat (Z_to_bv 8 0) 512)] ++ repeat (C1 (Z_to_bv 8 0)) 16 ++ [CB n sj])).
  { eapply rw_cells_recell; [exact HC| |].
    - apply cells_wf_app. split; [apply cells_wf_repeat_C1|]. cbn [app]. split; [apply repeat_length|]. apply cells_wf_app. split; [apply cells_wf_repeat_C1|].
      cbn. split; [exact Lsj| exact I].
    - rewrite !cells_bytes_app, !cells_bytes_repeat_C1. cbn [cells_bytes cbytes]. rewrite !app_nil_r.
      change 540%nat with (12 + (512 + 16))%nat. rewrite !repeat_app, <- !app_assoc. reflexivity. }
  apply rw_cells_app in HC' as [H1 HC']. apply rw_cells_app in HC' as [H2 HC']. apply rw_cells_app in HC' as [H3 _].
  change (cells_size (repeat (C1 (Z_to_bv 8 0)) 12)) with 12%nat in *. cbn [cells_size csize Nat.add] in H3.
  split; [exact H1|]. split; [replace (S + 12)%Z with (S + Z.of_nat 12)%Z by lia; exact H2|].
  lazymatch type of H3 with rw_cells _ _ ?A _ => replace (S + 524)%Z with A by lia end. exact H3.
Qed.
End Sz2.
#[using="Type"] Lemma np_sh_split : ltac:(let t := eval cbv delta [np_sh_split__stmt] in np_sh_split__stmt in exact t).
Proof. intros m S sj n. ltac2:(SecDiet.SzSec.closeP 'np_sh_split__body "vvvv"). Qed.

Section NpMain.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FENTER7 : fenter7_stmt_o FO GIOA fflagA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis SET00 : set_shadow_stmt SET_SHADOW_00 0.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.
  Hypothesis MAXSNAP : max_snaplen_stmt.

  Definition pcap_next_packet_proofA__stmt : Prop := pcap_next_packet_stmt HO FO sites GIOA TP.
  Section Sz3.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P HA DA p fuel hcs dc : ltac2:(SecDiet.SzSec.tyM 'pcap_next_packet_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_next_packet_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_next_packet_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FENTER7 FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
 intros PRE UC TR NF PC NG S0A -> -> -> HH Hh HD Hd OHA ODA DHD HA8 DA8.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    destruct p as [self rfile bufsize bufalloc buffer bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header priv].
    destruct priv as [sf|ng oif]; [| discriminate NG]. clear NG. destruct sf as [hdrsize lsw scl].
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & _ & _ & _ & _ & IFS & WF)).
    cbn [pc_priv ifaces_ok] in IFS. subst I.
    pose proof WF as WF'. unfold pcap_wf in WF'. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
         pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in WF'.
    destruct WF' as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & WHS & WBB). subst brk prec.
    assert (AL0 : (0 < bufalloc)%Z) by lia.
    set (k := mkNpk hptr self rfile swapped vmaj vmin snapshot linktype ltext header hdrsize lsw scl).
    change (mkPcap self rfile bufsize bufalloc buffer bufdata swapped vmaj vmin snapshot linktype ltext 0 0 errbuf header (PrivPcap (mkSf hdrsize lsw scl)))
      with (pv k buffer bufsize bufalloc bufdata errbuf) in *.
    rewrite EPB in G, PC. cbn [pc_rfile pv] in HinF. change rfile with (k_f k) in HinF.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    unfold PCAP_L2_STACK in BU.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (ICL0 : incl CLc (CLc ++ pcap_blocks (pv k buffer bufsize bufalloc bufdata errbuf) P B 0)) by (apply incl_appl, incl_refl).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL0 (incl_refl _))) as (HALO & HAHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL0 (incl_refl _))) as (DALO & DAHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL0 (incl_refl _)) ltac:(lia)) as HABAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL0 (incl_refl _)) ltac:(lia)) as DABAND.
    band_ind HABAND bH. band_ind DABAND bD.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    unfold next_packet_op. cbn [pc_priv pv]. rewrite (np_model_eq MOps (prims HO FO sites)). cbn [e_fenter prims].
    unfold np_entry, is_ng. cbn [pc_priv pv pk_next_pcap PK].
    remember (bv_unsigned sp - 224 - (bv_unsigned sp - 224) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 240 <= SPA <= bv_unsigned sp - 224 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -224) - (bv_unsigned sp + -224) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    destruct SPAP as (SPAB & SPA32 & ESPA').
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 120%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    rewrite land_m32N by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -104)%Z.
    destruct (stk_split asegs _ lo (SPA + 120) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 120) 120 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 120) with 120%Z in STL, FRA. replace (SPA + 120 - 120)%Z with SPA in STL, FRA by lia.
    destruct (spill_words _ _ _ FRA) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & FRW). clear FRA.
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    (* [comment removed for export] *)
    do 5 zstep.
    do 2 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 2 zstep.
    zstep.
    (* [comment removed for export] *)
    set (PBx := pcap_blocks (pv k buffer bufsize bufalloc bufdata errbuf) P B 0) in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW0 : Forall (pcap_iv FL PBx) [(bv_unsigned sp - 240, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ PBx) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW0]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    assert (FWp : Forall (own_ivA ([] : list fblock) ([] : list (@cblock hptr)) (bv_unsigned sp)) [(bv_unsigned sp - 240, bv_unsigned sp)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>   (* [comment removed for export] *)
      assert (PC1 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB mm) end.
    { eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC].
      intros a Ha. exact (pb_outside _ _ _ GL _ _ _ _ _ _ FL [] _ _ [] (bv_unsigned sp) FWp (Forall_nil _) G a Ha). }
    rename MU into MU0. rename WM into WM0. clear FW0 FWp GOT SHB SUA GSU.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER7 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { reflexivity. }
    { apply NF. left. reflexivity. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk sjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ LSJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_NEXT_PACKET) with 8192%Z in *.
    change (Z.to_nat (8192 - 32)) with (Z.to_nat 8160) in *.
    change (Z.to_nat (4320 / 8)) with 540%nat in SHC.
    destruct (np_sh_split _ _ _ _ SHC) as (SH12 & SHD & SH16). clear SHC LSJ sjunk.
    cbn [repeat] in SH12, SH16.
    replace (ret_pc (Z_to_bv 64 558620)) with (Z_to_bv 64 558620) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. pose proof (Forall_inv FAll) as FRM. pose proof FRM as (FBAND' & FTOP' & F64 & _ & FRNG & FSRNG & _ & FSWR).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 8192 3) with 1024%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRW; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HH'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL0 (incl_refl _))| exact Ha]].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL0 (incl_refl _))| exact Ha]].
    assert (PC2 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB m2)
      by (eapply PCAPR_agree; [exact AG1| intros a Ha; right; left; apply in_block_app; right; exact Ha| exact PC1]).
    assert (AGb : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; apply in_block_app; left; exact Ha| apply incl_refl]. }
    clear PC1 AGa AG1 G0 MU0 WM0 MI STL.
    replace (Z.shiftr Fb 3 + 2147450880 + 12)%Z with (Z.shiftr Fb 3 + 2147450892)%Z in SHD by lia.
    replace (Z.shiftr Fb 3 + 2147450880 + 524)%Z with (Z.shiftr Fb 3 + 2147451404)%Z in SH16 by lia.
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 1024 <= 0x10007fff8000)%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    destruct SHLO as (SLO & SHI).
    assert (RSP120 : rng RNG SPA 120) by (eapply rng_sub'; [exact RSPA| lia]).
    assert (SPALO : (17594333495296 <= SPA)%Z) by (atop_facts; lia).
    assert (LOLO : (17594333495296 <= lo)%Z) by (atop_facts; lia).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL0 (incl_refl _)) ltac:(lia)) as (kH & kHr & kH1 & kH2).
    destruct (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL0 (incl_refl _)) ltac:(lia)) as (kD & kDr & kD1 & kD2).
    cbn [fb_addr fb_size fst snd] in kH1, kH2, kD1, kD2.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    call np_poison_seq; [try eassumption .. | ]; [lia .. | ].
    lazymatch goal with HH : rw_cells asegs _ SPA _ |- _ => rename HH into FRW end.
    lazymatch goal with HH : rw_cells asegs _ Fb _ |- _ => rename HH into FRC end.
    lazymatch goal with HH : rw_cells asegs _ (Z.shiftr Fb 3 + 2147450880)%Z _ |- _ => rename HH into SH12 end. unfold np_shadow_f8 in SH12.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 8192, bv_unsigned sp); (Fb, Fb + 8192); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ mm _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ PBx _) FW) (Forall_nil _) G1 MU WM ltac:(lia)) as [G3 AG3];
      assert (PC3 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC2];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PBx) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G1 a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))))
    end.
    cbn [app] in G3.
    clear MU WM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (SETF8 _ spa) with (lo := lo) (SA := (Z.shiftr Fb 3 + 2147450892)%Z) (n := 512%Z) (old := repeat (Z_to_bv 8 0) 512);
        [ assumption | rewrite Hspa; exact ST1 | rewrite Hspa; unfold FAKE_STACK; lia | lia
        | exact (proj1 (gl_rt _ _ _ GL _ _ _ _ _ _ _ G3)) | exact (gl_got_memset _ _ _ GL _ _ _ _ _ _ _ G3)
        | reflexivity | reflexivity | lia | lia | exact SHD
        | eapply rng_sub'; [exact FSRNG| lia] | rewrite Hspa; eapply rng_sub'; [exact RSTK| lia] | exact RIMG ]
      | ].
    cbv beta. intros ms' PO. destruct PO as (a0v & m4 & E & MUc & WMc & MIc & STc & SHD4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. unfold FAKE_STACK in MUc.
    replace (ret_pc (Z_to_bv 64 558808)) with (Z_to_bv 64 558808) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (FWc : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(SPA - 4096, SPA); (Z.shiftr Fb 3 + 2147450892, Z.shiftr Fb 3 + 2147450892 + 512)]%Z) by own_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m4 _ [] (bv_unsigned sp)
                (Forall_impl _ (own_ivA_PB _ PBx _) FWc) (Forall_nil _) G3 MUc WMc ltac:(lia)) as [G4 AG4].
    assert (PC4 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB m4).
    { eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC3].
      intros a Ha. exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PBx) _ _ _ _ _ [] (bv_unsigned sp) FWc (Forall_nil _) G3 a (proj2 (in_block_app _ _ _) (or_intror Ha))). }
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end.
    assert (AGc : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m4).
    { eapply agrees_on_trans; [exact AGb|]. eapply agrees_on_trans; (eapply agrees_on_weaken; [eassumption|]); intros a K; (split; [exact K| exact I]). }
    clear FWc G1 G3 AG3 AG4 PC2 PC3 AGb.
    try clear MUc. try clear WMc. try clear ST1. try clear SHD. try clear FW. try subst spa. try clear Hspa. try clear MI1.
    cbn [app] in G4.
    (* [comment removed for export] *)
    assert (HinP : In (k_self k, P, 664%Z) ((CLc ++ PBx) ++ FB)) by (subst PBx; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G4 HinP) as ((PBAND & _ & PTOP & P16) & P0 & _ & PRNG & PRSH & _).
    cbn [cb_addr cb_size fst snd] in PBAND, PTOP, P16, P0, PRNG, PRSH.
    band_ind PBAND bP.
    assert (PHI : (P + 664 <= 2^47)%Z) by (atop_facts; lia).
    pose proof (munch_refl [(Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z m4) as MU.
    pose proof (wmono_refl asegs m4) as WM.
    call np_f3_seq; [try eassumption .. | ]; [lia .. | ].
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 1024)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ mm _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ PBx _) FW) (Forall_nil _) G4 MU WM ltac:(lia)) as [G5 _];
      assert (PC5 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC4];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PBx) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G4 a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))));
      assert (C48 : rw_cells asegs mm (P + 48) [C8 (Z_to_bv 64 (P + 648))])
    end.
    { clear EPB WF W1 W2 W3 W4 W7 W8 W9 W10 W11 W12 WHS WBB Af HinF. subst PBx. np_open PC5.
      destruct (rw_cells_cut _ _ _ 7 CELLS) as [_ C7]. cbn [firstn skipn cells_size csize Nat.add] in C7.
      destruct (rw_cells_cut _ _ _ 1 C7) as [C48 _]. cbn [firstn skipn cells_size csize Nat.add] in C48.
      lazymatch type of C48 with rw_cells _ _ ?A _ => replace A with (P + 48)%Z in C48 by lia end. exact C48. }
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as (_ & _ & PUNP & _). cbn [cb_addr cb_size fst snd] in PUNP.
    clear G5 PC5.
    call np_s1_seq; [try eassumption .. | ]; [lia .. | ].
    lazymatch goal with HH : rw_cells asegs _ (Z.shiftr Fb 3 + 2147450880)%Z _ |- _ => rename HH into SH12 end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ mm _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ PBx _) FW) (Forall_nil _) G4 MU WM ltac:(lia)) as [G6 AG6];
      assert (PC6 : PCAPR (hptr:=hptr) P (pv k buffer bufsize bufalloc bufdata errbuf) PBx FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC4];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CLc ++ PBx) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G4 a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))))
    end.
    cbn [app] in G6. subst PBx.
    assert (CTX : np_ctx TP ra sp tp s0 L RNG CLc FB FL trC lo HA DA Af SPA (k_f k) m).
    { unfold np_ctx, PCAP_L2_STACK. do 5 (split; [first [assumption | lia]|]).
      split; [split; [exact RSTK| split; [exact RIMG| split; [exact RISH| exact RTLS]]]|].
      repeat (split; [first [assumption | reflexivity | lia]|]). first [assumption | lia]. }
    apply evtF_done. subst POSTQ0 POSTQ.
    eapply (np_rdhdr HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP)
      with (dsh := repeat (Z_to_bv 8 248) (Z.to_nat 512)) (hcs := [CB 24 hj]) (dw := CB 8 dj);
      [ exact CTX | | exact PC6 | exact FRW | exact HH' | reflexivity | exact HD' | reflexivity | exact AL0 ].
    unfold np_inv0. split; [apply fp_le_refl|]. split; [exact G6|]. split; [exact OF1|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [exact FR|].
    split. { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGc|]; intros a (K & _); exact K|].
             eapply agrees_on_weaken; [exact AG6|]. intros a (K & _). split; [exact K| exact I]. }
    split; [exists (Z_to_bv 64 1102416563), (Z_to_bv 64 115227), (Z_to_bv 64 558496), fjunk; exact FRC|]. split; [exact SH12| exact SHD4].
  Qed.
  End Sz3.
  Theorem pcap_next_packet_proofA : ltac:(let t := eval cbv delta [pcap_next_packet_proofA__stmt] in pcap_next_packet_proofA__stmt in exact t).
  Proof using GL HAL GPL FENTER7 FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. red. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P HA DA p fuel hcs dc. ltac2:(SecDiet.SzSec.closeP 'pcap_next_packet_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpMain.
End CANSEC1.
End TwB.
End F_sfnp_mainA.
