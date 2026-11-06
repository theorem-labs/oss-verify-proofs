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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfnp_normA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_exitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpNorm.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis PP : post_process_stmt.

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  Definition np_nshort__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell) (cap n : Z),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9;
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= n <= cap)%Z -> n <> cap -> (cap < 2^31)%Z ->
    implMG RNGx (mbind (read_fail_msg MOps (prims HO FO sites) f (Msg.trunc_captured_u cap n))
                       (fun m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, set_errbuf m0 p'))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 cap) r23 r24 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x889a4) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 h p' hcs' dw cap n : ltac2:(SecDiet.SzSec.tyM 'np_nshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_nshort__body : ltac2:(SecDiet.SzSec.bodyP 'np_nshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF.
    intros CTX INV PC FRA HH Hh HD Hd NR NC C31.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    set (POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o).
    unfold read_fail_msg. cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    apply implMG_bind_assoc.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. do 3 zstep. zstep.
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
    replace (ret_pc (Z_to_bv 64 559540)) with (Z_to_bv 64 559540) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
      apply implMG_from_evtF. zstep. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      ck TUNP 4%Z 0x889d0%Z [11%Z; 12%Z].
      zstep.
      do 4 zstep. zstep.
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (np_fmt FO GIOA TP fflagA GL FFREE7 SETF8 FMT) with (pc := 0x889e8%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj) (e := e);
        [ right; split; [left; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | lia | exact MSG | intros msg; reflexivity ].
    - (* [comment removed for export] *)
      apply implMG_retb.
      assert (MSG : fmt_at m3 0x21f40 "truncated dump file; tried to read %u captured bytes, only got %zu"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21f40 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %u captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      apply implMG_from_evtF. zstep. zstep. if_true.
      zstep. replace (bv_swrap 32 (cap + 0)) with cap by (rewrite bv_swrap32_eq, Z.add_0_r, Z.mod_small by lia; lia).
      do 5 zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.trunc_captured_u, PCAP_ERRBUF_SIZE.
      eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x88a5c%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj)
                                                                               (args := [AInt cap; AInt n]);
        [ right; split; [right; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
  Qed.
  End Sz2.
  Lemma np_nshort : ltac:(let t := eval cbv delta [np_nshort__stmt] in np_nshort__stmt in exact t).
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 h p' hcs' dw cap n. ltac2:(SecDiet.SzSec.closeP 'np_nshort__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_nread_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r24 r27 t3 t4 t5 t6 : word)
      (c0 c1 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (got eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc got eb) (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    Forall (fun x => 0 <= x < 256)%Z got -> (0 <= zlength got <= cap)%Z -> (cap <= 2^30)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (if negb (zlength got =? cap)%Z
                 then mbind (read_fail_msg MOps (prims HO FO sites) (k_f k) (Msg.trunc_captured_u cap (zlength got)))
                            (fun m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len, set_errbuf m0 (pv k bq bsz alloc got eb)))
                 else let '(hdr, d) := pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec cap len) got in
                      fo_ret FO _ FF_NEXT_PACKET (1%Z, hdr, set_bufdata d (pv k bq bsz alloc got eb))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (zlength got)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 HA) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (HA + 16))
               (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880)) r24 (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x888f0) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r24 r27 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc got eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_nread_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_nread_post__body : ltac2:(SecDiet.SzSec.bodyP 'np_nread_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF PP.
    intros CTX INV PC FRA HH HD Hd GOTR GOTL C30 Hl32 AL0.
    np_setup GL CTX INV.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    destruct (Z.eq_dec (zlength got) cap) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
      apply implMG_from_evtF.
      ck0_at HAUNP (HA + 16)%Z; ck_go.
      zstep. rewrite (np_zx32_small cap) by lia.
      zstep. zstep.
      if_cases Kq; [zify_cond Kq; exfalso; lia|].
      apply evtF_done. subst POSTQ.
      eapply (np_finish FO GIOA TP fflagA GL FFREE7 PP) with (dsh := dsh) (sec := sec) (usec := usec);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | exact HD | exact Hd | reflexivity | reflexivity | exact GOTR
        | unfold zlength in LEQ; lia | unfold zlength in LEQ; lia | exact Hl32 | exact AL0 ].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      apply implMG_from_evtF.
      ck0_at HAUNP (HA + 16)%Z; ck_go.
      zstep. rewrite (np_zx32_small cap) by lia.
      zstep. zstep.
      if_cases Kq; [|zify_cond Kq; exfalso; lia].
      apply evtF_done. subst POSTQ.
      eapply (np_nshort) with (dsh := dsh) (PB := pcap_blocks (pv k bq bsz alloc got eb) P Bx 0)
                              (hcs' := [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | reflexivity | exact HD | exact Hd | exact GOTL | exact LNE | lia ].
  Qed.
  End Sz3.
  Lemma np_nread_post : ltac:(let t := eval cbv delta [np_nread_post__stmt] in np_nread_post__stmt in exact t).
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r24 r27 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc got eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_nread_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition np_nread__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 r27 t3 t4 t5 t6 : word)
      (c0 c1 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap <= bsz)%Z -> (cap <= k_snap k)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_read_model MOps (prims HO FO sites) (k_f k) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 24)) r23 r24 (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x888b8) fc None mm (seg_rom asegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 r27 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_nread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_nread__body : ltac2:(SecDiet.SzSec.bodyP 'np_nread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
    intros CTX INV PC FRA HH HD Hd Hcap Hcs Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs mm _ [] (Z.to_nat alloc) _ [] [Z.to_nat cap; (Z.to_nat alloc - Z.to_nat cap)%nat]) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. cbn [firstn skipn cells_size csize Nat.add] in BD, BT.
    unfold np_read_model, read_fail_msg, errmsg_for_errno.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_fread e_ferror e_last_errno pc_buffer pc_linktype pc_swapped pc_bufdata set_bufdata set_errbuf
         pc_self pc_rfile pc_bufsize pc_bufalloc pc_version_major pc_version_minor pc_snapshot pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv pv].
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    ck0 PUNP; ck_go.
    ck0_at HAUNP (HA + 16)%Z; ck_go.
    zstep. rewrite (np_zx32_small cap) by lia.
    do 2 zstep.
    zstep.
    (* [comment removed for export] *)
    pose proof (HAL _ _ _ _ _ _ _ (bq, Bx, alloc) G HinB) as EA. cbn [cb_tok cb_addr fst snd] in EA.
    assert (INP : forall a, (P <= a < P + 664)%Z -> in_block (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) a)
      by (intros a Ha; apply in_block_In; exists (k_self k, P, 664%Z); split; [apply in_or_app; right; exact HinPB| cbn [cb_addr cb_size fst snd]; lia]).
    assert (INB : forall a, (Bx <= a < Bx + alloc)%Z -> in_block (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) a)
      by (intros a Ha; apply in_block_In; exists (bq, Bx, alloc); split; [apply in_or_app; right; exact HinBB| cbn [cb_addr cb_size fst snd]; lia]).
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest]. rewrite EA. rewrite Z.add_0_r.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact BD
        | split; [left; exists (bq, Bx, alloc); split; [apply in_or_app; right; exact HinBB| cbn [cb_addr cb_size fst snd]; lia]|];
          eapply blockA_aobj; [exact BBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    destruct PO as (FP6 & av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 559344)) with (Z_to_bv 64 559344) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (INV6 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG6 s6'
                           (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) dsh m6).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (Bx <= a < Bx + cap)%Z);
        [ exact INV | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia
        | intros a K _ Hin; eapply (keeps_not_PB FO GIOA fflagA GL); [exact G| exact IFL| | exact K|];
            [lia| apply in_block_In; exists (bq, Bx, alloc); split; [exact HinBB| cbn [cb_addr cb_size fst snd]; lia]]
        | eapply np_frame_keep; [exact AG6| intros a Ha; cbv beta; lia| exists k0, k1, k2, fj; exact FRC] ]. }
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
              ((SPA <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664) \/ (Bx + cap <= A /\ A + Z.of_nat (cells_size cs) <= Bx + alloc))%Z ->
              rw_cells asegs m6 A cs).
    { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|[HX|HX]].
      - split; [left; lia| lia].
      - split; [right; left; apply INP; lia| lia].
      - split; [right; left; apply INB; lia| lia]. }
    assert (KOB : forall A n cs, rw_cells asegs mm A cs -> clocA FL CL A n -> Z.of_nat (cells_size cs) = n ->
                   (A + n <= Bx \/ Bx + cap <= A)%Z -> rw_cells asegs m6 A cs)
      by (intros A n0 cs HC LOC HSz HDj; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha; split; [|lia];
          eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]).
    apply KEEP in FRA; [| left; lia].
    apply KEEP in CELLS; [| right; left; cbn [cells_size csize Nat.add]; lia]. apply KEEP in PRIV; [| right; left; cbn [cells_size csize Nat.add]; lia].
    apply KEEP in BT; [| right; right; cbn [cells_size csize Nat.add]; lia].
    apply (KOB _ 24%Z) in HH; [|exact (proj1 OHA)|reflexivity|lia].
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    apply (KOB _ 8%Z) in HD'; [|exact (proj1 ODA)|reflexivity|lia].
    clear KEEP KOB.
    pose proof (rw_cells_uncut _ _ _ _ _ HD6 BT ltac:(cbn [cells_size csize Nat.add]; unfold zlength in GOTL; lia)) as BUF6. cbn [app] in BUF6. merge_all BUF6.
    replace (length got + (Z.to_nat cap - length got + (Z.to_nat alloc - Z.to_nat cap + 0)))%nat with (Z.to_nat alloc) in BUF6 by (unfold zlength in GOTL; lia).
    rewrite app_nil_r in BUF6.
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc got eb) (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) FB m6).
    { exists Afx. split; [exact HinFx|]. exists Bx, 0%Z, jx, padx, (map b8 got ++ junk6 ++ firstn (Z.to_nat alloc - Z.to_nat cap) (skipn (Z.to_nat cap) bsx)).
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [unfold pv; cbn [pc_bufalloc]; exact BUF6|].
      split; [unfold pv; cbn [pc_bufdata]; replace (length got) with (length (map b8 got)) by (apply length_map);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      unfold pcap_wf, pv in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. unfold zlength in GOTL. repeat split; try lia; try tauto. }
    subst POSTQ.
    eapply (np_nread_post) with (dsh := dsh) (sec := sec) (usec := usec) (cap := cap) (len := len) (got := got) (dw := CB 8 dwj);
      [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HH | exact HD' | reflexivity | exact GOTR | exact GOTL | lia | exact Hl32 | exact AL0 ].
  Qed.
  End Sz4.
  Lemma np_nread : ltac:(let t := eval cbv delta [np_nread__stmt] in np_nread__stmt in exact t).
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r23 r24 r27 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_nread__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpNorm.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Section NpNorm.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis PP : post_process_stmt.

  #[using="Type"] Lemma implMG_errno_ll : forall {B C} (f : Z -> Monad.M (PState H hptr) B) (g : B -> Monad.M (PState H hptr) C) (s : PState H hptr) RNG Q ms,
    implMG RNG (mbind (f (lc_errno (ps_libc s))) g) s Q ms -> implMG RNG (mbind (mbind (s_get_errno (H:=H) (hptr:=hptr)) f) g) s Q ms.
  Proof. intros B C f g s RNG Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  Definition np_nshort__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (f : hptr) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (PB : list (@cblock hptr)) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r22 r23 r24 r27 t3 t4 t5 t6 : word)
      (c0 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 : word) (h : pkthdr) (p' : PcapTypes.pcap hptr hptr) (hcs' : list cell) (dw : cell) (cap n : Z),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA f m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx PB dsh mm ->
    PCAPR (hptr:=hptr) P p' PB FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 c9; C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs' -> cells_size hcs' = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= n <= cap)%Z -> n <> cap -> (cap < 2^31)%Z ->
    implMG RNGx (mbind (read_fail_msg MOps (prims HO FO sites) f (Msg.trunc_captured_u cap n))
                       (fun m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, h, set_errbuf m0 p'))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 cap) r22 r23 r24 (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88f48) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r22 r23 r24 r27 t3 t4 t5 t6 c0 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 h p' hcs' dw cap n : ltac2:(SecDiet.SzSec.tyM 'np_nshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_nshort__body : ltac2:(SecDiet.SzSec.bodyP 'np_nshort__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF.
 intros CTX INV PC FRA HH Hh HD Hd NR NC C31.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    destruct (rw_cells_forget _ _ _ _ HD) as [dj HD']. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'. clear HD.
    set (POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o).
    unfold read_fail_msg. cbn [mo_bind mo_ret MOps e_ferror e_fret prims].
    apply implMG_bind_assoc.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    apply implMG_from_evtF. do 2 zstep. zstep.
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
    replace (ret_pc (Z_to_bv 64 560980)) with (Z_to_bv 64 560980) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      apply implMG_from_evtF. zstep. if_false.
      zstep. do 3 zstep. rewrite ETP.
      (* [comment removed for export] *)
      zstep.
      pose proof ATPv_pg as TPG. pose proof atp_lin as ((TPLO & _) & _).
      assert (XX : (0 < ATP + -164 < 2 ^ 64)%Z) by (unfold ATP; atop_facts; lia).
      zstep. if_false_by (eqz_false (ATP + -164) XX).
      zstep. replace (Z.land (ATP + -164) 3) with 0%Z by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; unfold ATP; Z.div_mod_to_equations; lia).
      zstep. if_false.
      ck TUNP 4%Z 0x88f7c%Z [11%Z; 12%Z].
      zstep.
      do 3 zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
      replace (sx32 (Z_to_bv 64 e)) with (Z_to_bv 64 (s32 e)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      apply evtF_done. subst POSTQ.
      eapply (np_fmt FO GIOA TP fflagA GL FFREE7 SETF8 FMT) with (pc := 0x88954%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj) (e := e);
        [ left; split; [left; reflexivity| reflexivity] | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | lia | exact MSG | intros msg; reflexivity ].
    - (* [comment removed for export] *)
      apply implMG_retb.
      assert (MSG : fmt_at m3 0x21f40 "truncated dump file; tried to read %u captured bytes, only got %zu"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m3 0x21f40 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "truncated dump file; tried to read %u captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                MI3' ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      repeat match goal with HR : rng RNGx _ _ |- _ => apply (rng_fp_le _ _ _ _ FP3) in HR end.
      apply implMG_from_evtF. zstep. if_true.
      zstep. replace (bv_swrap 32 (cap + 0)) with cap by (rewrite bv_swrap32_eq, Z.add_0_r, Z.mod_small by lia; lia).
      do 5 zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.trunc_captured_u, PCAP_ERRBUF_SIZE.
      eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x89000%Z) (PB := PB) (dsh := dsh) (hcs' := [CB 24 hj]) (dw := CB 8 dj)
                                                                               (args := [AInt cap; AInt n]);
        [ right; split; reflexivity | exact CTX | exact INV3 | exact PC3 | exact FRA | exact HH' | reflexivity | exact HD' | reflexivity
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
  Qed.
  End Sz2.
  Lemma np_nshort : ltac:(let t := eval cbv delta [np_nshort__stmt] in np_nshort__stmt in exact t).
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb f m o RNGx sx PB dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r22 r23 r24 r27 t3 t4 t5 t6 c0 c2 c3 c4 c5 c6 c7 c8 c9 c12 c13 c14 h p' hcs' dw cap n. ltac2:(SecDiet.SzSec.closeP 'np_nshort__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_nread_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r21 r24 r27 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (got eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc got eb) (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    Forall (fun x => 0 <= x < 256)%Z got -> (0 <= zlength got <= cap)%Z -> (cap <= 2^30)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (if negb (zlength got =? cap)%Z
                 then mbind (read_fail_msg MOps (prims HO FO sites) (k_f k) (Msg.trunc_captured_u cap (zlength got)))
                            (fun m0 => fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len, set_errbuf m0 (pv k bq bsz alloc got eb)))
                 else let '(hdr, d) := pcapint_post_process (k_lt k) (k_sw k) (mkHdr sec usec cap len) got in
                      fo_ret FO _ FF_NEXT_PACKET (1%Z, hdr, set_bufdata d (pv k bq bsz alloc got eb))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (zlength got)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 HA) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) r21 (Z_to_bv 64 (HA + 16))
               (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880)) r24 (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88e78) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r21 r24 r27 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc got eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_nread_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_nread_post__body : ltac2:(SecDiet.SzSec.bodyP 'np_nread_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF PP.
 intros CTX INV PC FRA HH HD Hd GOTR GOTL C30 Hl32 AL0.
    np_setup GL CTX INV.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end.
    destruct (Z.eq_dec (zlength got) cap) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
      apply implMG_from_evtF.
      ck0_at HAUNP (HA + 16)%Z; ck_go.
      zstep. rewrite (np_zx32_small cap) by lia.
      zstep.
      if_cases Kq; [zify_cond Kq; exfalso; lia|].
      apply evtF_done. subst POSTQ.
      eapply (np_finish FO GIOA TP fflagA GL FFREE7 PP) with (dsh := dsh) (sec := sec) (usec := usec);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | exact HD | exact Hd | reflexivity | reflexivity | exact GOTR
        | unfold zlength in LEQ; lia | unfold zlength in LEQ; lia | exact Hl32 | exact AL0 ].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      apply implMG_from_evtF.
      ck0_at HAUNP (HA + 16)%Z; ck_go.
      zstep. rewrite (np_zx32_small cap) by lia.
      zstep.
      if_cases Kq; [|zify_cond Kq; exfalso; lia].
      apply evtF_done. subst POSTQ.
      eapply (np_nshort) with (dsh := dsh) (PB := pcap_blocks (pv k bq bsz alloc got eb) P Bx 0)
                              (hcs' := [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | reflexivity | exact HD | exact Hd | exact GOTL | exact LNE | lia ].
  Qed.
  End Sz3.
  Lemma np_nread_post : ltac:(let t := eval cbv delta [np_nread_post__stmt] in np_nread_post__stmt in exact t).
  Proof using GL FFREE7 SETF8 FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r21 r24 r27 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc got eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_nread_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition np_nread__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r23 r24 r27 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap <= bsz)%Z -> (cap <= k_snap k)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_read_model MOps (prims HO FO sites) (k_f k) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) r21 (Z_to_bv 64 (P + 24)) r23 r24 (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88e40) fc None mm (seg_rom asegs)).
  Section Sz4.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r23 r24 r27 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_nread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_nread__body : ltac2:(SecDiet.SzSec.bodyP 'np_nread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
 intros CTX INV PC FRA HH HD Hd Hcap Hcs Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs mm _ [] (Z.to_nat alloc) _ [] [Z.to_nat cap; (Z.to_nat alloc - Z.to_nat cap)%nat]) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. cbn [firstn skipn cells_size csize Nat.add] in BD, BT.
    unfold np_read_model, read_fail_msg, errmsg_for_errno.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_fread e_ferror e_last_errno pc_buffer pc_linktype pc_swapped pc_bufdata set_bufdata set_errbuf
         pc_self pc_rfile pc_bufsize pc_bufalloc pc_version_major pc_version_minor pc_snapshot pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv pv].
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    ck0 PUNP; ck_go.
    ck0_at HAUNP (HA + 16)%Z; ck_go.
    zstep. rewrite (np_zx32_small cap) by lia.
    do 2 zstep.
    zstep.
    (* [comment removed for export] *)
    pose proof (HAL _ _ _ _ _ _ _ (bq, Bx, alloc) G HinB) as EA. cbn [cb_tok cb_addr fst snd] in EA.
    assert (INP : forall a, (P <= a < P + 664)%Z -> in_block (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) a)
      by (intros a Ha; apply in_block_In; exists (k_self k, P, 664%Z); split; [apply in_or_app; right; exact HinPB| cbn [cb_addr cb_size fst snd]; lia]).
    assert (INB : forall a, (Bx <= a < Bx + alloc)%Z -> in_block (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) a)
      by (intros a Ha; apply in_block_In; exists (bq, Bx, alloc); split; [apply in_or_app; right; exact HinBB| cbn [cb_addr cb_size fst snd]; lia]).
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { apply implMG_mget. cbn [eval_rdest]. rewrite EA. rewrite Z.add_0_r.
      eapply (FREAD _ spa) with (Af := Af);
        [ split; [exact G|]; rewrite Hspa; split; [exact ST|]; split; [lia|]; split; [unfold STDIO_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact BD
        | split; [left; exists (bq, Bx, alloc); split; [apply in_or_app; right; exact HinBB| cbn [cb_addr cb_size fst snd]; lia]|];
          eapply blockA_aobj; [exact BBLK| cbn [cb_addr cb_size fst snd]; lia| cbn [cb_addr cb_size fst snd]; lia| lia] ]. }
    intros got s6' RNG6 ms' PO. cbv beta in PO.
    destruct PO as (FP6 & av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 560760)) with (Z_to_bv 64 560760) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (INV6 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNG6 s6'
                           (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) dsh m6).
    { eapply (np_inv0_callee FO GIOA fflagA GL) with (Pn := fun a => ~ (Bx <= a < Bx + cap)%Z);
        [ exact INV | lia | lia | exact FP6 | exact G6 | exact OF6 | exact MI6 | exact ST6 | exact AG6
        | intros a Ha; lia | intros a Ha; lia
        | intros a K _ Hin; eapply (keeps_not_PB FO GIOA fflagA GL); [exact G| exact IFL| | exact K|];
            [lia| apply in_block_In; exists (bq, Bx, alloc); split; [exact HinBB| cbn [cb_addr cb_size fst snd]; lia]]
        | eapply np_frame_keep; [exact AG6| intros a Ha; cbv beta; lia| exists k0, k1, k2, fj; exact FRC] ]. }
    assert (KEEP : forall A cs, rw_cells asegs mm A cs ->
              ((SPA <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664) \/ (Bx + cap <= A /\ A + Z.of_nat (cells_size cs) <= Bx + alloc))%Z ->
              rw_cells asegs m6 A cs).
    { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|[HX|HX]].
      - split; [left; lia| lia].
      - split; [right; left; apply INP; lia| lia].
      - split; [right; left; apply INB; lia| lia]. }
    assert (KOB : forall A n cs, rw_cells asegs mm A cs -> clocA FL CL A n -> Z.of_nat (cells_size cs) = n ->
                   (A + n <= Bx \/ Bx + cap <= A)%Z -> rw_cells asegs m6 A cs)
      by (intros A n0 cs HC LOC HSz HDj; eapply agrees_rw_cells; [exact AG6| exact HC|]; intros a Ha; split; [|lia];
          eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ LOC ICL IFL)| lia]).
    apply KEEP in FRA; [| left; lia].
    apply KEEP in CELLS; [| right; left; cbn [cells_size csize Nat.add]; lia]. apply KEEP in PRIV; [| right; left; cbn [cells_size csize Nat.add]; lia].
    apply KEEP in BT; [| right; right; cbn [cells_size csize Nat.add]; lia].
    apply (KOB _ 24%Z) in HH; [|exact (proj1 OHA)|reflexivity|lia].
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    apply (KOB _ 8%Z) in HD'; [|exact (proj1 ODA)|reflexivity|lia].
    clear KEEP KOB.
    pose proof (rw_cells_uncut _ _ _ _ _ HD6 BT ltac:(cbn [cells_size csize Nat.add]; unfold zlength in GOTL; lia)) as BUF6. cbn [app] in BUF6. merge_all BUF6.
    replace (length got + (Z.to_nat cap - length got + (Z.to_nat alloc - Z.to_nat cap + 0)))%nat with (Z.to_nat alloc) in BUF6 by (unfold zlength in GOTL; lia).
    rewrite app_nil_r in BUF6.
    assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc got eb) (pcap_blocks (pv k bq bsz alloc got eb) P Bx 0) FB m6).
    { exists Afx. split; [exact HinFx|]. exists Bx, 0%Z, jx, padx, (map b8 got ++ junk6 ++ firstn (Z.to_nat alloc - Z.to_nat cap) (skipn (Z.to_nat cap) bsx)).
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [unfold pv; cbn [pc_bufalloc]; exact BUF6|].
      split; [unfold pv; cbn [pc_bufdata]; replace (length got) with (length (map b8 got)) by (apply length_map);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      unfold pcap_wf, pv in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. unfold zlength in GOTL. repeat split; try lia; try tauto. }
    subst POSTQ.
    eapply (np_nread_post) with (dsh := dsh) (sec := sec) (usec := usec) (cap := cap) (len := len) (got := got) (dw := CB 8 dwj);
      [ exact CTX | exact INV6 | exact PC6 | exact FRA | exact HH | exact HD' | reflexivity | exact GOTR | exact GOTL | lia | exact Hl32 | exact AL0 ].
  Qed.
  End Sz4.
  Lemma np_nread : ltac:(let t := eval cbv delta [np_nread__stmt] in np_nread__stmt in exact t).
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r18 r21 r23 r24 r27 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_nread__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpNorm.
End CANSEC1.
End TwB.
End F_sfnp_normA.

(* [comment removed for export] *)
Module F_sfnp_norm2A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_exitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpNorm2.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Definition np_ngrow_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (c0 c1 c12 c13 c14 : word)
      (k : npk hptr) (bq q' : hptr) (Bx A' bsz alloc nb : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell)
      (Afx : Z) (jx : pcap_junk) (padx bsx junk6 : list byte),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) dsh mm ->
    In (k_f k, Afx, FILE_BLOCK) FB ->
    rw_cells asegs mm P (pcap_cells_gen (pv k bq bsz alloc data eb) P Bx (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx) ->
    rw_cells asegs mm (P + PCAP_PRIV_OFF) (priv_cells (pv k bq bsz alloc data eb) 0 padx) ->
    pcap_wf (pv k bq bsz alloc data eb) ->
    firstn (length data) bsx = map b8 data -> length bsx = Z.to_nat alloc ->
    rw_cells asegs mm A' [CB (Z.to_nat (Z.min alloc nb)) (firstn (Z.to_nat (Z.min alloc nb)) bsx); CB (Z.to_nat (nb - Z.min alloc nb)) junk6] ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap <= nb)%Z -> (nb <= k_snap k)%Z -> (nb <= 2^27)%Z -> (0 < nb)%Z -> (0 <= len < 2^32)%Z ->
    implMG RNGx (np_read_model MOps (prims HO FO sites) (k_f k) (pv k q' nb nb (zfirstn nb data) eb) (mkHdr sec usec cap len) cap) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.shiftr (P + 20) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P)
               (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880)) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 nb) (Z_to_bv 64 (P + 20)) (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88898) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq q' Bx A' bsz alloc nb data eb sec usec cap len dw Afx jx padx bsx junk6 : ltac2:(SecDiet.SzSec.tyM 'np_ngrow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_ngrow_post__body : ltac2:(SecDiet.SzSec.bodyP 'np_ngrow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
    intros CTX INV HinFx CELLS PRIV WF PFX LBS NEW FRA HH HD Hd Hcap NBS NB27 AL0 Hl32.
    np_setup GL CTX INV.
    np_blocks GL G OHA ODA IFL.
    unfold pv, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision
         pc_header pc_priv pk_next_pcap pk_cleanup_sf PK] in CELLS.
    unfold pv, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV. cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    pose proof WF as WF'. unfold pcap_wf, pv in WF'.
    cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
         pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in WF'.
    destruct WF' as (W1 & W2 & W3 & W4 & _ & _ & W7 & W8 & W9 & W10 & W11 & W12 & WHS & WBB). unfold INT_MAX in W1.
    merge_all NEW. replace (Z.to_nat (Z.min alloc nb) + (Z.to_nat (nb - Z.min alloc nb) + 0))%nat with (Z.to_nat nb) in NEW by lia. rewrite app_nil_r in NEW.
    pose proof (munch_refl [(P + 20, P + 32)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep. if_false_by (eqz_false A' ltac:(lia)).
    ck0_at PUNP (P + 24)%Z; ck_go.
    zstep.
    ck0_at PUNP (P + 20)%Z; ck_go.
    zstep. zstep.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] [(k_self k, P, 664%Z); (q', A', nb)] (bv_unsigned sp)) [(P + 20, P + 32)]%Z)
      by (apply Forall_cons; [|apply Forall_nil]; right; left; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m7 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m7 _ [] (bv_unsigned sp) FW (Forall_nil _) G MU WM ltac:(lia)) as [G7 AG7];
      assert (AGm7 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m7)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG7|]; intros a (K & _); split; [exact K| exact I])
    end.
    assert (PC7 : PCAPR (hptr:=hptr) P (pv k q' nb nb (zfirstn nb data) eb) (pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) FB m1).
    { exists Afx. split; [exact HinFx|]. exists A', 0%Z, jx, padx, (firstn (Z.to_nat (Z.min alloc nb)) bsx ++ junk6).
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [unfold pv; cbn [pc_bufalloc]; exact NEW|].
      split; [unfold pv, zfirstn, b8; cbn [pc_bufdata]; apply pfx_realloc; [exact PFX | lia | lia]|].
      split; [reflexivity|].
      unfold pcap_wf, pv in *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *.
      unfold zfirstn. rewrite length_firstn. unfold INT_MAX. repeat split; try lia; try tauto. }
    apply evtF_done. subst POSTQ.
    eapply (np_nread HO FO sites GIOA TP fflagA GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP) with (dsh := dsh) (sec := sec) (usec := usec);
      [ exact CTX | | exact PC7 | exact FRA | exact HH | exact HD | exact Hd | lia | lia | exact Hl32 | exact AL0 ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G7|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [exact AGm7|].
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz1.
  Lemma np_ngrow_post : ltac:(let t := eval cbv delta [np_ngrow_post__stmt] in np_ngrow_post__stmt in exact t).
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq q' Bx A' bsz alloc nb data eb sec usec cap len dw Afx jx padx bsx junk6. ltac2:(SecDiet.SzSec.closeP 'np_ngrow_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_normal__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r22 r27 t3 t4 t5 t6 : word)
      (c0 c1 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap <= k_snap k)%Z -> (cap <= max_snaplen_for_dlt (k_lt k))%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_norm_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (k_snap k)) a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) r22 (Z_to_bv 64 cap) (Z_to_bv 64 (P + 20)) (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88820) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r22 r27 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_normal__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_normal__body : ltac2:(SecDiet.SzSec.bodyP 'np_normal__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF REALLOC RPC PP.
    intros CTX INV PC FRA HH HD Hd Hcap Hcm Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    pose proof (max_snaplen_le (k_lt k)) as MSL.
    unfold np_norm_model, grow_buffer.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_realloc pc_bufsize pc_snapshot pc_rfile pc_buffer pc_bufdata
         pc_self pc_bufalloc pc_swapped pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv pv].
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    ck0 PUNP; ck_go.
    zstep. rewrite (np_sx32_small bsz) by lia.
    zstep.
    destruct (Z.ltb_spec bsz cap) as [GROW|NOGROW].
    - (* [comment removed for export] *)
      replace (bsz <? cap)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      zstep. if_cases Kb; try (zify_cond Kb; exfalso; lia).
      eapply evtF_cut; [eapply (np_roundup_seq) with (cap := cap) (snap := k_snap k); lia|].
      cbv beta. intros ms' (a1v & a2v & ->).
      pose proof (roundup_bounds cap ltac:(lia)) as RB.
      set (nb := (if (k_snap k <? roundup_pow2_u32 cap)%Z then k_snap k else roundup_pow2_u32 cap)) in *.
      assert (NB1 : (cap <= nb <= k_snap k)%Z) by (subst nb; destruct (Z.ltb_spec (k_snap k) (roundup_pow2_u32 cap)); lia).
      assert (NB2 : (nb <= 2^27)%Z) by (subst nb; destruct (Z.ltb_spec (k_snap k) (roundup_pow2_u32 cap)); lia).
      clearbody nb.
      ck0 PUNP; ck_go.
      zstep. do 2 zstep. rewrite (Z.mod_small nb) by lia.
      zstep.
      apply evtF_done. apply implMG_bind_assoc.
      eapply np_realloc with (pc := 0x88898%Z) (k := k) (bsz := bsz) (alloc := alloc) (data := data) (eb := eb) (dsh := dsh);
        [ exact GL | exact GPL | exact REALLOC | exact RPC | right; reflexivity | exact CTX | exact INV | exact PC | lia | exact AL0 | ].
      intros q' A' RNG6 s6' m6 junk6 bsx' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' FP6 INV6 AG6 PFX6 LBS6 NEW6.
      apply implMG_retb. cbv beta iota.
      cbn [negb set_buffer pc_self pc_rfile pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
           pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
      assert (ICL1 : incl CL (CL ++ [(k_self k, P, 664%Z)])) by (apply incl_appl, incl_refl).
      assert (KP : forall A cs, rw_cells asegs mm A cs -> (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664)%Z -> rw_cells asegs m6 A cs).
      { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. right; left. apply in_block_In.
        exists (k_self k, P, 664%Z). split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]. }
      apply KP in CELLS; [| cbn [cells_size csize Nat.add]; lia]. apply KP in PRIV; [| cbn [cells_size csize Nat.add]; lia]. clear KP.
      apply (agrees_rw_cells _ _ _ _ _ AG6) in FRA; [|intros a Ha; left; lia].
      apply (agrees_rw_cells _ _ _ _ _ AG6) in HH; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL1 IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      apply (agrees_rw_cells _ _ _ _ _ AG6) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL1 IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
      subst POSTQ.
      eapply np_ngrow_post with (dsh := dsh) (bq := bq) (Bx := Bx) (bsz := bsz) (alloc := alloc) (data := data) (Afx := Afx) (jx := jx) (padx := padx)
                                (bsx := bsx') (junk6 := junk6) (dw := CB 8 dwj);
        [ exact CTX | exact INV6 | exact HinFx | exact CELLS | exact PRIV | exact WF | exact PFX6 | exact LBS6 | exact NEW6 | exact FRA | exact HH | exact HD'
        | reflexivity | lia | lia | lia | lia | exact Hl32 ].
    - (* [comment removed for export] *)
      replace (bsz <? cap)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      zstep. if_cases Kb; try (zify_cond Kb; exfalso; lia).
      apply evtF_done. apply implMG_retb. cbv beta iota. cbn [negb]. subst POSTQ.
      eapply (np_nread HO FO sites GIOA TP fflagA GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP) with (dsh := dsh) (sec := sec) (usec := usec);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | exact HD | exact Hd | lia | lia | exact Hl32 | exact AL0 ].
  Qed.
  End Sz2.
  Lemma np_normal : ltac:(let t := eval cbv delta [np_normal__stmt] in np_normal__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF REALLOC RPC PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r22 r27 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_normal__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpNorm2.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpNorm2.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis FFREE7 : ffree7_stmt_o FO GIOA fflagA.
  Hypothesis SETF8 : set_shadow_stmt SET_SHADOW_F8 248.
  Hypothesis FREAD : fread_stmt_o HO GIOA.
  Hypothesis FERROR : ferror_stmt_o HO GIOA.
  Hypothesis FMT : fmt_errmsg_stmt FO GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis REALLOC : realloc_stmt_o HO GIOA TP.
  Hypothesis RPC : (~ (ACLIENT_LO <= tp_rpc TP < ACLIENT_HI))%Z.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Definition np_ngrow_post__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq q' : hptr) (Bx A' bsz alloc nb : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell)
      (Afx : Z) (jx : pcap_junk) (padx bsx junk6 : list byte),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) dsh mm ->
    In (k_f k, Afx, FILE_BLOCK) FB ->
    rw_cells asegs mm P (pcap_cells_gen (pv k bq bsz alloc data eb) P Bx (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx) ->
    rw_cells asegs mm (P + PCAP_PRIV_OFF) (priv_cells (pv k bq bsz alloc data eb) 0 padx) ->
    pcap_wf (pv k bq bsz alloc data eb) ->
    firstn (length data) bsx = map b8 data -> length bsx = Z.to_nat alloc ->
    rw_cells asegs mm A' [CB (Z.to_nat (Z.min alloc nb)) (firstn (Z.to_nat (Z.min alloc nb)) bsx); CB (Z.to_nat (nb - Z.min alloc nb)) junk6] ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap <= nb)%Z -> (nb <= k_snap k)%Z -> (nb <= 2^27)%Z -> (0 < nb)%Z -> (0 <= len < 2^32)%Z ->
    implMG RNGx (np_read_model MOps (prims HO FO sites) (k_f k) (pv k q' nb nb (zfirstn nb data) eb) (mkHdr sec usec cap len) cap) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.shiftr (P + 20) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P)
               (Z_to_bv 64 (Z.shiftr (P + 24) 3 + 2147450880)) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 nb) (Z_to_bv 64 (P + 20)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) (Z_to_bv 64 Fb) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88e24) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c12 c13 c14 k bq q' Bx A' bsz alloc nb data eb sec usec cap len dw Afx jx padx bsx junk6 : ltac2:(SecDiet.SzSec.tyM 'np_ngrow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_ngrow_post__body : ltac2:(SecDiet.SzSec.bodyP 'np_ngrow_post__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP.
 intros CTX INV HinFx CELLS PRIV WF PFX LBS NEW FRA HH HD Hd Hcap NBS NB27 AL0 Hl32.
    np_setup GL CTX INV.
    np_blocks GL G OHA ODA IFL.
    unfold pv, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision
         pc_header pc_priv pk_next_pcap pk_cleanup_sf PK] in CELLS.
    unfold pv, priv_cells, sf_cells, PCAP_PRIV_OFF in PRIV. cbn [pc_priv sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    pose proof WF as WF'. unfold pcap_wf, pv in WF'.
    cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
         pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in WF'.
    destruct WF' as (W1 & W2 & W3 & W4 & _ & _ & W7 & W8 & W9 & W10 & W11 & W12 & WHS & WBB). unfold INT_MAX in W1.
    merge_all NEW. replace (Z.to_nat (Z.min alloc nb) + (Z.to_nat (nb - Z.min alloc nb) + 0))%nat with (Z.to_nat nb) in NEW by lia. rewrite app_nil_r in NEW.
    pose proof (munch_refl [(P + 20, P + 32)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep. if_false_by (eqz_false A' ltac:(lia)).
    ck0_at PUNP (P + 24)%Z; ck_go.
    zstep.
    ck0_at PUNP (P + 20)%Z; ck_go.
    zstep.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] [(k_self k, P, 664%Z); (q', A', nb)] (bv_unsigned sp)) [(P + 20, P + 32)]%Z)
      by (apply Forall_cons; [|apply Forall_nil]; right; left; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m7 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m7 _ [] (bv_unsigned sp) FW (Forall_nil _) G MU WM ltac:(lia)) as [G7 AG7];
      assert (AGm7 : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(HA, HA + 24); (DA, DA + 8)]%Z a) m m7)
        by (eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG7|]; intros a (K & _); split; [exact K| exact I])
    end.
    assert (PC7 : PCAPR (hptr:=hptr) P (pv k q' nb nb (zfirstn nb data) eb) (pcap_blocks (pv k q' nb nb (zfirstn nb data) eb) P A' 0) FB m1).
    { exists Afx. split; [exact HinFx|]. exists A', 0%Z, jx, padx, (firstn (Z.to_nat (Z.min alloc nb)) bsx ++ junk6).
      split; [reflexivity|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [unfold pv; cbn [pc_bufalloc]; exact NEW|].
      split; [unfold pv, zfirstn, b8; cbn [pc_bufdata]; apply pfx_realloc; [exact PFX | lia | lia]|].
      split; [reflexivity|].
      unfold pcap_wf, pv in *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *.
      unfold zfirstn. rewrite length_firstn. unfold INT_MAX. repeat split; try lia; try tauto. }
    apply evtF_done. subst POSTQ.
    eapply (np_nread HO FO sites GIOA TP fflagA GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP) with (dsh := dsh) (sec := sec) (usec := usec);
      [ exact CTX | | exact PC7 | exact FRA | exact HH | exact HD | exact Hd | lia | lia | exact Hl32 | exact AL0 ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G7|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [exact AGm7|].
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz1.
  Lemma np_ngrow_post : ltac:(let t := eval cbv delta [np_ngrow_post__stmt] in np_ngrow_post__stmt in exact t).
  Proof using GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c12 c13 c14 k bq q' Bx A' bsz alloc nb data eb sec usec cap len dw Afx jx padx bsx junk6. ltac2:(SecDiet.SzSec.closeP 'np_ngrow_post__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_normal__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r22 r27 t3 t4 t5 t6 : word)
      (c0 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 (Z_to_bv 64 Fb); C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap <= k_snap k)%Z -> (cap <= max_snaplen_for_dlt (k_lt k))%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_norm_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (k_snap k)) a1 a2 a3 a4 a5 a6 a7
               r18 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) r22 (Z_to_bv 64 cap) (Z_to_bv 64 (P + 20)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88dac) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r22 r27 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_normal__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_normal__body : ltac2:(SecDiet.SzSec.bodyP 'np_normal__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF REALLOC RPC PP.
 intros CTX INV PC FRA HH HD Hd Hcap Hcm Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    pose proof (max_snaplen_le (k_lt k)) as MSL.
    unfold np_norm_model, grow_buffer.
    cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_realloc pc_bufsize pc_snapshot pc_rfile pc_buffer pc_bufdata
         pc_self pc_bufalloc pc_swapped pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv pv].
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    ck0 PUNP; ck_go.
    zstep. rewrite (np_sx32_small bsz) by lia.
    zstep.
    destruct (Z.ltb_spec bsz cap) as [GROW|NOGROW].
    - (* [comment removed for export] *)
      replace (bsz <? cap)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      zstep. if_cases Kb; try (zify_cond Kb; exfalso; lia).
      eapply evtF_cut; [eapply (np_roundup_seq) with (cap := cap) (snap := k_snap k); lia|].
      cbv beta. intros ms' (a1v & a2v & ->).
      pose proof (roundup_bounds cap ltac:(lia)) as RB.
      set (nb := (if (k_snap k <? roundup_pow2_u32 cap)%Z then k_snap k else roundup_pow2_u32 cap)) in *.
      assert (NB1 : (cap <= nb <= k_snap k)%Z) by (subst nb; destruct (Z.ltb_spec (k_snap k) (roundup_pow2_u32 cap)); lia).
      assert (NB2 : (nb <= 2^27)%Z) by (subst nb; destruct (Z.ltb_spec (k_snap k) (roundup_pow2_u32 cap)); lia).
      clearbody nb.
      ck0 PUNP; ck_go.
      zstep. do 2 zstep. rewrite (Z.mod_small nb) by lia.
      zstep.
      apply evtF_done. apply implMG_bind_assoc.
      eapply np_realloc with (pc := 0x88e24%Z) (k := k) (bsz := bsz) (alloc := alloc) (data := data) (eb := eb) (dsh := dsh);
        [ exact GL | exact GPL | exact REALLOC | exact RPC | right; reflexivity | exact CTX | exact INV | exact PC | lia | exact AL0 | ].
      intros q' A' RNG6 s6' m6 junk6 bsx' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' FP6 INV6 AG6 PFX6 LBS6 NEW6.
      apply implMG_retb. cbv beta iota.
      cbn [negb set_buffer pc_self pc_rfile pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
           pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
      assert (ICL1 : incl CL (CL ++ [(k_self k, P, 664%Z)])) by (apply incl_appl, incl_refl).
      assert (KP : forall A cs, rw_cells asegs mm A cs -> (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664)%Z -> rw_cells asegs m6 A cs).
      { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. right; left. apply in_block_In.
        exists (k_self k, P, 664%Z). split; [apply in_or_app; right; left; reflexivity| cbn [cb_addr cb_size fst snd]; lia]. }
      apply KP in CELLS; [| cbn [cells_size csize Nat.add]; lia]. apply KP in PRIV; [| cbn [cells_size csize Nat.add]; lia]. clear KP.
      apply (agrees_rw_cells _ _ _ _ _ AG6) in FRA; [|intros a Ha; left; lia].
      apply (agrees_rw_cells _ _ _ _ _ AG6) in HH; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 OHA) ICL1 IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      apply (agrees_rw_cells _ _ _ _ _ AG6) in HD'; [|intros a Ha; eapply clocA_keeps; [exact (clocA_incl _ _ _ _ _ _ (proj1 ODA) ICL1 IFL)| cbn [cells_size csize Nat.add] in Ha; lia]].
      subst POSTQ.
      eapply np_ngrow_post with (dsh := dsh) (bq := bq) (Bx := Bx) (bsz := bsz) (alloc := alloc) (data := data) (Afx := Afx) (jx := jx) (padx := padx)
                                (bsx := bsx') (junk6 := junk6) (dw := CB 8 dwj);
        [ exact CTX | exact INV6 | exact HinFx | exact CELLS | exact PRIV | exact WF | exact PFX6 | exact LBS6 | exact NEW6 | exact FRA | exact HH | exact HD'
        | reflexivity | lia | lia | lia | lia | exact Hl32 ].
    - (* [comment removed for export] *)
      replace (bsz <? cap)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      zstep. if_cases Kb; try (zify_cond Kb; exfalso; lia).
      apply evtF_done. apply implMG_retb. cbv beta iota. cbn [negb]. subst POSTQ.
      eapply (np_nread HO FO sites GIOA TP fflagA GL HAL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF PP) with (dsh := dsh) (sec := sec) (usec := usec);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | exact HD | exact Hd | lia | lia | exact Hl32 | exact AL0 ].
  Qed.
  End Sz2.
  Lemma np_normal : ltac:(let t := eval cbv delta [np_normal__stmt] in np_normal__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF REALLOC RPC PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r18 r22 r27 t3 t4 t5 t6 c0 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_normal__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpNorm2.
End CANSEC1.
End TwB.
End F_sfnp_norm2A.

(* [comment removed for export] *)
Module F_sfnp_chkA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_exitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A.
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
        assert (A2 : (8 * (P / 8) + 8 <= hi)%Z) by (pose proof (Z.mul_div_le P 8 (eq_refl : (0 < 8)%Z)) as CKgr; ck_lia);
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
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpChk.
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
  Definition np_dispatch__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r24 t3 t4 t5 t6 : word)
      (c0 c1 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap)%Z -> (cap <= max_snaplen_for_dlt (k_lt k))%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (if (k_snap k <? cap)%Z then np_over_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec
                 else np_norm_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (k_snap k)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 cap)
               r24 (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8868c) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r24 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_dispatch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_dispatch__body : ltac2:(SecDiet.SzSec.bodyP 'np_dispatch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP.
    intros CTX INV PC FRA HH HD Hd Hc0 Hcm Hl32 AL0.
    pose proof (max_snaplen_le (k_lt k)) as MSL.
    pose proof PC as (_ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WF)). unfold pcap_wf, pv in WF. cbn [pc_snapshot] in WF. destruct WF as (W1 & _). unfold INT_MAX in W1.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep. replace (bv_swrap 32 (k_snap k + 0)) with (k_snap k) by (rewrite bv_swrap32_eq, Z.add_0_r, Z.mod_small by lia; lia).
    zstep. zstep.
    destruct (Z.ltb_spec (k_snap k) cap) as [LT|GE].
    - if_cases Kc; try (zify_cond Kc; exfalso; first [ revert Kc; plia_cheap | lia ]).
      apply evtF_done. subst POSTQ.
      eapply (np_over HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP) with (dsh := dsh) (sec := sec) (usec := usec);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | exact HD | exact Hd | exact LT | lia | exact Hl32 | exact AL0 ].
    - if_cases Kc; try (zify_cond Kc; exfalso; first [ revert Kc; plia_cheap | lia ]).
      apply evtF_done. subst POSTQ.
      eapply (np_normal HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF REALLOC RPC PP) with (dsh := dsh) (sec := sec) (usec := usec);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH | exact HD | exact Hd | lia | exact Hcm | exact Hl32 | exact AL0 ].
  Qed.
  End Sz1.
  Lemma np_dispatch : ltac:(let t := eval cbv delta [np_dispatch__stmt] in np_dispatch__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r24 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_dispatch__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_caperr__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c7 c9 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5;
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 c7; C8 (Z_to_bv 64 (P + 100)); C8 c9;
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap < 2^32)%Z -> (max_snaplen_for_dlt (k_lt k) < cap)%Z -> (0 < alloc)%Z ->
    implMG RNGx (if (k_snap k <? cap)%Z
                 then fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len, set_errbuf (Msg.invalid_caplen_snaplen cap (k_snap k)) (pv k bq bsz alloc data eb))
                 else fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len,
                                                   set_errbuf (Msg.invalid_caplen_maximum cap (max_snaplen_for_dlt (k_lt k))) (pv k bq bsz alloc data eb))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (k_snap k)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) r22 (Z_to_bv 64 (s32 cap))
               r24 (Z_to_bv 64 Fb) (Z_to_bv 64 2147450880) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88674) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c7 c9 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_caperr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_caperr__body : ltac2:(SecDiet.SzSec.bodyP 'np_caperr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 SNPRINTF MAXSNAP.
    intros CTX INV PC FRA HH HD Hd Hc32 Hmx AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear PRIV BUF.
    pose proof (max_snaplen_range (k_lt k)) as MSR. unfold INT_MAX in MSR.
    pose proof (unsigned_s32 cap Hc32) as US.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep. replace (bv_swrap 32 (k_snap k + 0)) with (k_snap k) by (rewrite bv_swrap32_eq, Z.add_0_r, Z.mod_small by lia; lia).
    zstep. zstep.
    assert (US' : (s32 cap mod 18446744073709551616 = if cap <? 2 ^ 31 then cap else cap + 2 ^ 64 - 2 ^ 32)%Z) by (rewrite <- US; symmetry; apply unsigned_lit_wrap).
    destruct (Z.ltb_spec (k_snap k) cap) as [LT|GE].
    - (* [comment removed for export] *)
      if_cases Kc; [zify_cond Kc; exfalso; destruct (Z.ltb_spec cap (2^31)); lia|].
      assert (MSG : fmt_at mm 0x21e00 "invalid packet capture length %u, bigger than snaplen of %d"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x21e00 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "invalid packet capture length %u, bigger than snaplen of %d"%string) ++ [Z_to_bv 8 0])
                                MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      do 3 zstep. do 3 zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.invalid_caplen_snaplen, PCAP_ERRBUF_SIZE. rewrite <- (snp_caplen_snaplen_s32 cap (k_snap k)).
      eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x8881c%Z) (dsh := dsh) (PB := pcap_blocks (pv k bq bsz alloc data eb) P Bx 0)
                                                                       (args := [AInt (s32 cap); AInt (k_snap k)]);
        [ left; split; [right; right; left; reflexivity| reflexivity] | exact CTX | exact INV | exact PC | exact FRA | exact HH | reflexivity | exact HD | exact Hd
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
    - (* [comment removed for export] *)
      if_cases Kc; [|zify_cond Kc; exfalso; destruct (Z.ltb_spec cap (2^31)); lia].
      ck0_at PUNP (P + 100)%Z; ck_go.
      zstep. zstep. rewrite (np_sx32_small (k_lt k)) by lia.
      zstep.
      (* [comment removed for export] *)
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      clear MU WM.
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      eapply evtF_cut;
        [ eapply (MAXSNAP _ spa) with (lo := lo) (dlt := k_lt k); [ assumption | rewrite Hspa; exact ST | reflexivity | lia ] | ].
      cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. destruct PO as (-> & MUc & WMc & MIc & STc & ->).
      rewrite Hspa in *.
      replace (ret_pc (Z_to_bv 64 559104)) with (Z_to_bv 64 559104) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA - 0, SPA)]%Z) by own_ivs.
      lazymatch type of MUc with munch _ _ ?m6 =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m6 _ [] (bv_unsigned sp)
                    (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G MUc WMc ltac:(lia)) as [G6 AG6];
        assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6)
          by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC];
              intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a
                                    (proj2 (in_block_app _ _ _) (or_intror Ha))))
      end.
      lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end. clear MUc WMc.
      subst spa.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m6 _) =>
        assert (MSG : fmt_at m6 0x21e60 "invalid packet capture length %u, bigger than maximum of %u"%string)
          by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m6 0x21e60 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "invalid packet capture length %u, bigger than maximum of %u"%string) ++ [Z_to_bv 8 0])
                                  MIc ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
              split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]));
        pose proof (munch_refl ([] : list (Z * Z)) m6) as MU; pose proof (wmono_refl asegs m6) as WM end.
      do 3 zstep. do 3 zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.invalid_caplen_maximum, PCAP_ERRBUF_SIZE. rewrite <- (snp_caplen_max_s32 cap (max_snaplen_for_dlt (k_lt k))).
      eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x8881c%Z) (dsh := dsh) (PB := pcap_blocks (pv k bq bsz alloc data eb) P Bx 0)
                                                                       (args := [AInt (s32 cap); AInt (max_snaplen_for_dlt (k_lt k))]) (dw := CB 8 dwj);
        [ left; split; [right; right; left; reflexivity| reflexivity] | exact CTX | | exact PC6 | eassumption | eassumption | reflexivity | eassumption | reflexivity
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
      unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG6|]. intros a (K & _). split; [exact K| exact I]. }
      split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz2.
  Lemma np_caperr : ltac:(let t := eval cbv delta [np_caperr__stmt] in np_caperr__stmt in exact t).
  Proof using GL FFREE7 SETF8 SNPRINTF MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c7 c9 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_caperr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_chk__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r27 t3 t4 t5 t6 : word)
      (c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap < 2^32)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_tail MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880)) (Z_to_bv 64 (HA + 16)) (Z_to_bv 64 HA) (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8860c) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r27 t3 t4 t5 t6 c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_chk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_chk__body : ltac2:(SecDiet.SzSec.bodyP 'np_chk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
    intros CTX INV PC FRA HH HD Hd Hc32 Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear PRIV BUF.
    pose proof (max_snaplen_range (k_lt k)) as MSR. unfold INT_MAX in MSR.
    pose proof (unsigned_s32 cap Hc32) as US.
    assert (US' : (s32 cap mod 18446744073709551616 = if cap <? 2 ^ 31 then cap else cap + 2 ^ 64 - 2 ^ 32)%Z) by (rewrite <- US; symmetry; apply unsigned_lit_wrap).
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    unfold np_tail. cbn [pc_snapshot pc_linktype pv].
    pose proof (munch_refl [(SPA, SPA + 120)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep.
    ck0_at HAUNP (HA + 16)%Z; ck_go.
    zstep.
    do 3 zstep.
    ck0_at PUNP (P + 100)%Z; ck_go.
    rewrite (sx32_s32 cap) by lia.
    zstep. zstep. rewrite (np_sx32_small (k_lt k)) by lia.
    zstep.
    (* [comment removed for export] *)
    assert (FWs : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA, SPA + 120)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FWs) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m5)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FWs (Forall_nil _) G a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))))
    end.
    clear MU WM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (MAXSNAP _ spa) with (lo := lo) (dlt := k_lt k); [ assumption | rewrite Hspa; eassumption | reflexivity | lia ] | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. destruct PO as (-> & MUc & WMc & MIc & STc & ->).
    rewrite Hspa in *.
    replace (ret_pc (Z_to_bv 64 558656)) with (Z_to_bv 64 558656) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (FW0 : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA - 0, SPA)]%Z) by own_ivs.
    lazymatch type of MUc with munch _ _ ?m6 =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m6 _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW0) (Forall_nil _) G5 MUc WMc ltac:(lia)) as [G6 AG6];
      assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC5];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW0 (Forall_nil _) G5 a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))))
    end.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end. clear MUc WMc.
    subst spa.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m6 _) =>
      pose proof (munch_refl [(SPA, SPA + 120)]%Z m6) as MU; pose proof (wmono_refl asegs m6) as WM end.
    zstep.
    ck0_at HAUNP (HA + 16)%Z; ck_go.
    zstep. zstep. do 2 zstep.
    ck0_at PUNP (P + 96)%Z; ck_go.
    rewrite (sx32_s32 cap) by lia.
    zstep. rewrite (np_zx32_small (k_snap k)) by lia.
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with HH1 : rw_cells asegs _ SPA _ |- _ => rename HH1 into FRA1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m7 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m7 _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FWs) (Forall_nil _) G6 MU WM ltac:(lia)) as [G7 AG7];
      assert (PC7 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m7)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC6];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FWs (Forall_nil _) G6 a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))));
      assert (INV7 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
                             (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh m7)
        by (unfold np_inv0, np_shadow; split; [exact FP|]; split; [exact G7|]; split; [exact OF|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
            split; [assumption|];
            split; [eapply agrees_on_trans; [exact AG|]; eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I]|];
                    eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG6|]; intros a (K & _); split; [exact K| exact I]|];
                    eapply agrees_on_weaken; [exact AG7|]; intros a (K & _); split; [exact K| exact I]|];
            split; [exists k0, k1, k2, fj; assumption|]; split; assumption)
    end.
    destruct (Z.ltb_spec (max_snaplen_for_dlt (k_lt k)) cap) as [BIG|OK].
    - if_cases Kc; [zify_cond Kc; exfalso; destruct (Z.ltb_spec cap (2^31)); lia|].
      apply evtF_done. subst POSTQ.
      eapply np_caperr with (dsh := dsh) (sec := sec) (usec := usec) (len := len) (dw := CB 8 dwj);
        [ exact CTX | exact INV7 | exact PC7 | exact FRA1 | eassumption | eassumption | reflexivity | exact Hc32 | exact BIG | exact AL0 ].
    - if_cases Kc; [|zify_cond Kc; exfalso; destruct (Z.ltb_spec cap (2^31)); lia].
      pose proof (max_snaplen_le (k_lt k)) as MSL.
      rewrite (s32_id cap) by lia.
      apply evtF_done. subst POSTQ.
      eapply np_dispatch with (dsh := dsh) (sec := sec) (usec := usec) (len := len) (dw := CB 8 dwj);
        [ exact CTX | exact INV7 | exact PC7 | exact FRA1 | eassumption | eassumption | reflexivity | lia | exact OK | exact Hl32 | exact AL0 ].
  Qed.
  End Sz3.
  Lemma np_chk : ltac:(let t := eval cbv delta [np_chk__stmt] in np_chk__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r27 t3 t4 t5 t6 c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_chk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpChk.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
        assert (A2 : (8 * (P / 8) + 8 <= hi)%Z) by (pose proof (Z.mul_div_le P 8 (eq_refl : (0 < 8)%Z)) as CKgr; ck_lia);
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
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpChk.
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
  Definition np_dispatch__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r24 t3 t4 t5 t6 : word)
      (c0 c1 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 (Z_to_bv 64 HA);
                           C8 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880));
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 (Z_to_bv 64 (HA + 16)); C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap)%Z -> (cap <= max_snaplen_for_dlt (k_lt k))%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (if (k_snap k <? cap)%Z then np_over_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec
                 else np_norm_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (k_snap k)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 96)) (Z_to_bv 64 cap)
               r24 (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) (Z_to_bv 64 (Z.shiftr (P + 96) 3 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88b9c) fc None mm (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r24 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_dispatch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_dispatch__body : ltac2:(SecDiet.SzSec.bodyP 'np_dispatch__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP.
 intros CTX INV PC FRA HH HD Hd Hc0 Hcm Hl32 AL0.
    pose proof (max_snaplen_le (k_lt k)) as MSL.
    pose proof PC as (_ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WF)). unfold pcap_wf, pv in WF. cbn [pc_snapshot] in WF. destruct WF as (W1 & _). unfold INT_MAX in W1.
    np_setup GL CTX INV.
    pose proof (munch_refl [(SPA, SPA + 120)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep. replace (bv_swrap 32 (k_snap k + 0)) with (k_snap k) by (rewrite bv_swrap32_eq, Z.add_0_r, Z.mod_small by lia; lia).
    zstep.
    zstep.                                (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (FWs : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA, SPA + 120)]%Z) by own_ivs.
    lazymatch goal with HH1 : rw_cells asegs _ SPA _ |- _ => rename HH1 into FRA1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m7 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m7 _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FWs) (Forall_nil _) G MU WM ltac:(lia)) as [G7 AG7];
      assert (PC7 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m7)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FWs (Forall_nil _) G a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))));
      assert (INV7 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
                             (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh m7)
        by (unfold np_inv0, np_shadow; split; [exact FP|]; split; [exact G7|]; split; [exact OF|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
            split; [assumption|];
            split; [eapply agrees_on_trans; [exact AG|]; eapply agrees_on_weaken; [exact AG7|]; intros a (K & _); split; [exact K| exact I]|];
            split; [exists k0, k1, k2, fj; assumption|]; split; assumption)
    end.
    zstep.
    destruct (Z.ltb_spec (k_snap k) cap) as [LT|GE].
    - if_cases Kc; try (zify_cond Kc; exfalso; first [ revert Kc; plia_cheap | lia ]).
      apply evtF_done. subst POSTQ.
      eapply (np_over HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP) with (dsh := dsh) (sec := sec) (usec := usec);
        [ exact CTX | exact INV7 | exact PC7 | exact FRA1 | eassumption | eassumption | exact Hd | exact LT | lia | exact Hl32 | exact AL0 ].
    - if_cases Kc; try (zify_cond Kc; exfalso; first [ revert Kc; plia_cheap | lia ]).
      apply evtF_done. subst POSTQ.
      eapply (np_normal HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 FREAD FERROR FMT SNPRINTF REALLOC RPC PP) with (dsh := dsh) (sec := sec) (usec := usec);
        [ exact CTX | exact INV7 | exact PC7 | exact FRA1 | eassumption | eassumption | exact Hd | lia | exact Hcm | exact Hl32 | exact AL0 ].
  Qed.
  End Sz1.
  Lemma np_dispatch : ltac:(let t := eval cbv delta [np_dispatch__stmt] in np_dispatch__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r24 t3 t4 t5 t6 c0 c1 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_dispatch__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_caperr__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 : word)
      (c0 c1 c2 c3 c4 c5 c7 c9 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5;
                           C8 (Z_to_bv 64 (Z.shiftr (P + 100) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 100)); C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 c9; C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap < 2^32)%Z -> (max_snaplen_for_dlt (k_lt k) < cap)%Z -> (0 < alloc)%Z ->
    implMG RNGx (if (k_snap k <? cap)%Z
                 then fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len, set_errbuf (Msg.invalid_caplen_snaplen cap (k_snap k)) (pv k bq bsz alloc data eb))
                 else fo_ret FO _ FF_NEXT_PACKET ((-1)%Z, mkHdr sec usec cap len,
                                                   set_errbuf (Msg.invalid_caplen_maximum cap (max_snaplen_for_dlt (k_lt k))) (pv k bq bsz alloc data eb))) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (k_snap k)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb) r22 (Z_to_bv 64 (s32 cap))
               r24 (Z_to_bv 64 2147450880) (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88b84) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c7 c9 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw : ltac2:(SecDiet.SzSec.tyM 'np_caperr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_caperr__body : ltac2:(SecDiet.SzSec.bodyP 'np_caperr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL FFREE7 SETF8 SNPRINTF MAXSNAP.
 intros CTX INV PC FRA HH HD Hd Hc32 Hmx AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear PRIV BUF.
    pose proof (max_snaplen_range (k_lt k)) as MSR. unfold INT_MAX in MSR.
    pose proof (unsigned_s32 cap Hc32) as US.
    pose proof (munch_refl ([] : list (Z * Z)) mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep. replace (bv_swrap 32 (k_snap k + 0)) with (k_snap k) by (rewrite bv_swrap32_eq, Z.add_0_r, Z.mod_small by lia; lia).
    zstep. zstep.
    assert (US' : (s32 cap mod 18446744073709551616 = if cap <? 2 ^ 31 then cap else cap + 2 ^ 64 - 2 ^ 32)%Z) by (rewrite <- US; symmetry; apply unsigned_lit_wrap).
    destruct (Z.ltb_spec (k_snap k) cap) as [LT|GE].
    - (* [comment removed for export] *)
      if_cases Kc; [zify_cond Kc; exfalso; destruct (Z.ltb_spec cap (2^31)); lia|].
      assert (MSG : fmt_at mm 0x21e00 "invalid packet capture length %u, bigger than snaplen of %d"%string)
        by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mm 0x21e00 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "invalid packet capture length %u, bigger than snaplen of %d"%string) ++ [Z_to_bv 8 0])
                                MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
            split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right])).
      do 3 zstep. do 3 zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.invalid_caplen_snaplen, PCAP_ERRBUF_SIZE. rewrite <- (snp_caplen_snaplen_s32 cap (k_snap k)).
      eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x88d24%Z) (dsh := dsh) (PB := pcap_blocks (pv k bq bsz alloc data eb) P Bx 0)
                                                                       (args := [AInt (s32 cap); AInt (k_snap k)]);
        [ left; split; [right; left; reflexivity| reflexivity] | exact CTX | exact INV | exact PC | exact FRA | exact HH | reflexivity | exact HD | exact Hd
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
    - (* [comment removed for export] *)
      if_cases Kc; [|zify_cond Kc; exfalso; destruct (Z.ltb_spec cap (2^31)); lia].
      ck0_at PUNP (P + 100)%Z; ck_go.
      zstep. zstep. rewrite (np_sx32_small (k_lt k)) by lia.
      zstep.
      (* [comment removed for export] *)
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      clear MU WM.
      remember (Z_to_bv 64 SPA) as spa eqn:Espa.
      assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
      eapply evtF_cut;
        [ eapply (MAXSNAP _ spa) with (lo := lo) (dlt := k_lt k); [ assumption | rewrite Hspa; exact ST | reflexivity | lia ] | ].
      cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. destruct PO as (-> & MUc & WMc & MIc & STc & ->).
      rewrite Hspa in *.
      replace (ret_pc (Z_to_bv 64 560392)) with (Z_to_bv 64 560392) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      assert (FW : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA - 0, SPA)]%Z) by own_ivs.
      lazymatch type of MUc with munch _ _ ?m6 =>
        destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m6 _ [] (bv_unsigned sp)
                    (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW) (Forall_nil _) G MUc WMc ltac:(lia)) as [G6 AG6];
        assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6)
          by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC];
              intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW (Forall_nil _) G a
                                    (proj2 (in_block_app _ _ _) (or_intror Ha))))
      end.
      lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end. clear MUc WMc.
      subst spa.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m6 _) =>
        assert (MSG : fmt_at m6 0x21e60 "invalid packet capture length %u, bigger than maximum of %u"%string)
          by (split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m6 0x21e60 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "invalid packet capture length %u, bigger than maximum of %u"%string) ++ [Z_to_bv 8 0])
                                  MIc ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|];
              split; [lia|]; split; [cbn; lia|]; unfold client_globals; repeat (first [left; reflexivity | right]));
        pose proof (munch_refl ([] : list (Z * Z)) m6) as MU; pose proof (wmono_refl asegs m6) as WM end.
      do 3 zstep. do 3 zstep. zstep.
      apply evtF_done. subst POSTQ. unfold Msg.invalid_caplen_maximum, PCAP_ERRBUF_SIZE. rewrite <- (snp_caplen_max_s32 cap (max_snaplen_for_dlt (k_lt k))).
      eapply (np_snp FO GIOA TP fflagA GL FFREE7 SETF8 SNPRINTF) with (pc := 0x88d24%Z) (dsh := dsh) (PB := pcap_blocks (pv k bq bsz alloc data eb) P Bx 0)
                                                                       (args := [AInt (s32 cap); AInt (max_snaplen_for_dlt (k_lt k))]) (dw := CB 8 dwj);
        [ left; split; [right; left; reflexivity| reflexivity] | exact CTX | | exact PC6 | eassumption | eassumption | reflexivity | eassumption | reflexivity
        | exact MSG | vm_compute; reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor] ].
      unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G6|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG6|]. intros a (K & _). split; [exact K| exact I]. }
      split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz2.
  Lemma np_caperr : ltac:(let t := eval cbv delta [np_caperr__stmt] in np_caperr__stmt in exact t).
  Proof using GL FFREE7 SETF8 SNPRINTF MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r24 r27 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c7 c9 c12 c13 c14 k bq Bx bsz alloc data eb sec usec cap len dw. ltac2:(SecDiet.SzSec.closeP 'np_caperr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma np_chk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r22 r23 r27 t3 t4 t5 t6 : word)
      (c0 c1 c4 c5 c6 c7 c8 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= cap < 2^32)%Z -> (0 <= len < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_tail MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec cap len) cap len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (HA + 16)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               r22 r23 (Z_to_bv 64 HA) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88b18) fc None mm (seg_rom asegs)).      (* [comment removed for export] *)
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
    intros until dw. intros CTX INV PC FRA HH HD Hd Hc32 Hl32 AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear PRIV BUF.
    pose proof (max_snaplen_range (k_lt k)) as MSR. unfold INT_MAX in MSR.
    pose proof (unsigned_s32 cap Hc32) as US.
    assert (US' : (s32 cap mod 18446744073709551616 = if cap <? 2 ^ 31 then cap else cap + 2 ^ 64 - 2 ^ 32)%Z) by (rewrite <- US; symmetry; apply unsigned_lit_wrap).
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    unfold np_tail. cbn [pc_snapshot pc_linktype pv].
    pose proof (munch_refl [(SPA, SPA + 120)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep.
    ck0 HAUNP; ck_go.
    zstep.
    do 3 zstep.
    ck0_at PUNP (P + 100)%Z; ck_go.
    rewrite (sx32_s32 cap) by lia.
    zstep. zstep. rewrite (np_sx32_small (k_lt k)) by lia.
    zstep.
    (* [comment removed for export] *)
    assert (FWs : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA, SPA + 120)]%Z) by own_ivs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m5 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m5 _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FWs) (Forall_nil _) G MU WM ltac:(lia)) as [G5 AG5];
      assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m5)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FWs (Forall_nil _) G a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))))
    end.
    clear MU WM.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    eapply evtF_cut;
      [ eapply (MAXSNAP _ spa) with (lo := lo) (dlt := k_lt k); [ assumption | rewrite Hspa; eassumption | reflexivity | lia ] | ].
    cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. destruct PO as (-> & MUc & WMc & MIc & STc & ->).
    rewrite Hspa in *.
    replace (ret_pc (Z_to_bv 64 559956)) with (Z_to_bv 64 559956) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (FW0 : Forall (own_ivA [(FF_NEXT_PACKET, Fb, 8192%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp)) [(SPA - 0, SPA)]%Z) by own_ivs.
    lazymatch type of MUc with munch _ _ ?m6 =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m6 _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FW0) (Forall_nil _) G5 MUc WMc ltac:(lia)) as [G6 AG6];
      assert (PC6 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m6)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MUc| exact WMc|]; intros a _ Ha; exact Ha| | exact PC5];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FW0 (Forall_nil _) G5 a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))))
    end.
    lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call asegs ma mb MUc WMc end. clear MUc WMc.
    subst spa.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m6 _) =>
      pose proof (munch_refl [(SPA, SPA + 120)]%Z m6) as MU; pose proof (wmono_refl asegs m6) as WM end.
    zstep.
    ck0_at HAUNP (HA + 16)%Z; ck_go.
    zstep. do 2 zstep.                   (* [comment removed for export] *)
    ck0_at PUNP (P + 96)%Z; ck_go.
    rewrite (sx32_s32 cap) by lia.
    zstep. rewrite (np_zx32_small (k_snap k)) by lia.
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with HH1 : rw_cells asegs _ SPA _ |- _ => rename HH1 into FRA1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m7 _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m7 _ [] (bv_unsigned sp)
                  (Forall_impl _ (own_ivA_PB _ (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _) FWs) (Forall_nil _) G6 MU WM ltac:(lia)) as [G7 AG7];
      assert (PC7 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m7)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC6];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ [] (CL ++ pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) _ _ _ _ _ [] (bv_unsigned sp) FWs (Forall_nil _) G6 a
                                  (proj2 (in_block_app _ _ _) (or_intror Ha))));
      assert (INV7 : np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
                             (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh m7)
        by (unfold np_inv0, np_shadow; split; [exact FP|]; split; [exact G7|]; split; [exact OF|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
            split; [assumption|];
            split; [eapply agrees_on_trans; [exact AG|]; eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I]|];
                    eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG6|]; intros a (K & _); split; [exact K| exact I]|];
                    eapply agrees_on_weaken; [exact AG7|]; intros a (K & _); split; [exact K| exact I]|];
            split; [exists k0, k1, k2, fj; assumption|]; split; assumption)
    end.
    destruct (Z.ltb_spec (max_snaplen_for_dlt (k_lt k)) cap) as [BIG|OK].
    - if_cases Kc; [zify_cond Kc; exfalso; destruct (Z.ltb_spec cap (2^31)); lia|].
      apply evtF_done. subst POSTQ.
      eapply np_caperr with (dsh := dsh) (sec := sec) (usec := usec) (len := len) (dw := CB 8 dwj);
        [ exact CTX | exact INV7 | exact PC7 | exact FRA1 | eassumption | eassumption | reflexivity | exact Hc32 | exact BIG | exact AL0 ].
    - if_cases Kc; [|zify_cond Kc; exfalso; destruct (Z.ltb_spec cap (2^31)); lia].
      pose proof (max_snaplen_le (k_lt k)) as MSL.
      rewrite (s32_id cap) by lia.
      apply evtF_done. subst POSTQ.
      eapply np_dispatch with (dsh := dsh) (sec := sec) (usec := usec) (len := len) (dw := CB 8 dwj);
        [ exact CTX | exact INV7 | exact PC7 | exact FRA1 | eassumption | eassumption | reflexivity | lia | exact OK | exact Hl32 | exact AL0 ].
  Qed.
End NpChk.
End CANSEC1.
End TwB.
End F_sfnp_chkA.

(* [comment removed for export] *)
Module F_sfnp_bodyA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_exitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_chkA.
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
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

(* [comment removed for export] *)
Lemma le4_s32 : forall c, (0 <= c < 2^32)%Z -> le4 (Z_to_bv 64 (s32 c)) = le4 (Z_to_bv 64 c).
Proof.
  intros c Hc. pose proof (unsigned_s32 c Hc) as US.
  rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 (s32 c))). rewrite US.
  destruct (Z.ltb_spec c (2^31)); [reflexivity|].
  rewrite (le4_mod32 (c + 2^64 - 2^32)) by lia. f_equal. f_equal. Z.div_mod_to_equations. lia.
Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpBody.
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
  Definition np_lswap__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a4 a5 a6 a7 r27 t3 t4 t5 t6 : word)
      (c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec capr lenr : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 capr); C4 (Z_to_bv 64 lenr)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= capr < 2^32)%Z -> (0 <= lenr < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_tail MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec lenr capr) lenr capr sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (HA + 20)) a1 a2 (Z_to_bv 64 (Z.shiftr (HA + 20) 3 + 2147450880)) a4 a5 a6 a7
               (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880)) (Z_to_bv 64 (HA + 16)) (Z_to_bv 64 HA) (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x885ec) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a4 a5 a6 a7 r27 t3 t4 t5 t6 c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb sec usec capr lenr dw : ltac2:(SecDiet.SzSec.tyM 'np_lswap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_lswap__body : ltac2:(SecDiet.SzSec.bodyP 'np_lswap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
    intros CTX INV PC FRA HH HD Hd Rc Rl AL0.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof (munch_refl [(HA, HA + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    ck0_at HAUNP (HA + 16)%Z; ck_go.
    ck0_at HAUNP (HA + 20)%Z; ck_go.
    rewrite (sx32_s32 capr) by lia.
    zstep. rewrite (sx32_s32 lenr) by lia.
    zstep. zstep.
    lazymatch goal with HH1 : rw_cells asegs _ HA _ |- _ => rename HH1 into HH6 end.
    assert (HH7 : rw_cells asegs m1 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 lenr); C4 (Z_to_bv 64 capr)]).
    { eapply rw_cells_recell; [exact HH6 | cbn; repeat split; exact Logic.I |].
      cbn [cells_bytes cbytes app]. rewrite (le4_s32 lenr), (le4_s32 capr) by lia. reflexivity. }
    assert (FX : Forall (cobj_iv FL CL) [(HA, HA + 24)]%Z) by cobj_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m1 [] _ (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G5 AG5].
    assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m1)
      by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
          intros a Ha; exact (pb_outside _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ [] _ (bv_unsigned sp) (Forall_nil _) FX G a Ha)).
    apply evtF_done. subst POSTQ.
    eapply (np_chk HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP)
      with (dsh := dsh) (sec := sec) (usec := usec) (cap := lenr) (len := capr) (dw := CB 8 dwj);
      [ exact CTX | | exact PC5 | eassumption | exact HH7 | eassumption | reflexivity | exact Rl | exact Rc | exact AL0 ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G5|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG5|]. intros a (K & (QN & _)). split; [exact K|]. split; [exact QN| exact I]. }
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz2.
  Lemma np_lswap : ltac:(let t := eval cbv delta [np_lswap__stmt] in np_lswap__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a4 a5 a6 a7 r27 t3 t4 t5 t6 c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb sec usec capr lenr dw. ltac2:(SecDiet.SzSec.closeP 'np_lswap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_lsw__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec capx lenx : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 capx); C4 (Z_to_bv 64 lenx)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= capx < 2^64)%Z -> (0 <= lenx < 2^64)%Z -> (0 < alloc)%Z ->
    implMG RNGx (let '(caplen, len) := match k_lsw k with
                                        | NOT_SWAPPED => ((capx mod 2^32)%Z, (lenx mod 2^32)%Z)
                                        | MAYBE_SWAPPED => if (capx mod 2^32 <=? lenx mod 2^32)%Z then ((capx mod 2^32)%Z, (lenx mod 2^32)%Z) else ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                        | SWAPPED => ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                        end in
                 np_tail MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec caplen len) caplen len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (HA + 20)) a1 a2 (Z_to_bv 64 (Z.shiftr (HA + 20) 3 + 2147450880)) a4 a5 a6 a7
               (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880)) (Z_to_bv 64 (HA + 16)) (Z_to_bv 64 HA) (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 648)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x885a8) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb sec usec capx lenx dw : ltac2:(SecDiet.SzSec.tyM 'np_lsw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_lsw__body : ltac2:(SecDiet.SzSec.bodyP 'np_lsw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
    intros CTX INV PC FRA HH HD Hd Hcx Hlx AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear CELLS BUF.
    set (capr := (capx mod 2^32)%Z) in *. set (lenr := (lenx mod 2^32)%Z) in *.
    assert (Rc : (0 <= capr < 2^32)%Z) by (subst capr; Z.div_mod_to_equations; lia).
    assert (Rl : (0 <= lenr < 2^32)%Z) by (subst lenr; Z.div_mod_to_equations; lia).
    pose proof (unsigned_s32 capr Rc) as US1. pose proof (unsigned_s32 lenr Rl) as US2.
    assert (HH' : rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 capr); C4 (Z_to_bv 64 lenr)]).
    { eapply rw_cells_recell; [exact HH | cbn; repeat split; exact Logic.I |].
      cbn [cells_bytes cbytes app]. rewrite (le4_mod32 lenx), (le4_mod32 capx) by lia. reflexivity. }
    clear HH.
    pose proof (munch_refl [(HA, HA + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep.
    ck0 PUNP; ck_go.
    zstep. rewrite (np_sx32_small (lenswap_code (k_lsw k))) by (destruct (k_lsw k); cbn; lia).
    zstep.
    destruct (k_lsw k); cbn [lenswap_code].
    - (* [comment removed for export] *)
      zstep. if_false. zstep. zstep. if_true.
      apply evtF_done. subst POSTQ.
      eapply (np_chk HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP)
        with (dsh := dsh) (sec := sec) (usec := usec) (cap := capr) (len := lenr);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH' | exact HD | exact Hd | exact Rc | exact Rl | exact AL0 ].
    - (* [comment removed for export] *)
      zstep. if_true.
      apply evtF_done. subst POSTQ.
      eapply np_lswap with (dsh := dsh) (sec := sec) (usec := usec);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH' | exact HD | exact Hd | exact Rc | exact Rl | exact AL0 ].
    - (* [comment removed for export] *)
      zstep. if_false. zstep. zstep. if_false.
      ck0_at HAUNP (HA + 16)%Z; ck_go.
      ck0_at HAUNP (HA + 20)%Z; ck_go.
      rewrite (sx32_s32 capr) by lia.
      zstep. rewrite (sx32_s32 lenr) by lia.
      zstep.
      destruct (Z.leb_spec capr lenr) as [LE|GT].
      + if_cases Kc; [|zify_cond Kc; exfalso; rewrite <- ?unsigned_lit_wrap, ?US1, ?US2 in Kc; destruct (Z.ltb_spec capr (2^31)); destruct (Z.ltb_spec lenr (2^31)); lia].
        apply evtF_done. subst POSTQ.
        eapply (np_chk HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP)
          with (dsh := dsh) (sec := sec) (usec := usec) (cap := capr) (len := lenr);
          [ exact CTX | exact INV | exact PC | exact FRA | exact HH' | exact HD | exact Hd | exact Rc | exact Rl | exact AL0 ].
      + if_cases Kc; [zify_cond Kc; exfalso; rewrite <- ?unsigned_lit_wrap, ?US1, ?US2 in Kc; destruct (Z.ltb_spec capr (2^31)); destruct (Z.ltb_spec lenr (2^31)); lia|].
        apply evtF_done. subst POSTQ.
        eapply np_lswap with (dsh := dsh) (sec := sec) (usec := usec);
          [ exact CTX | exact INV | exact PC | exact FRA | exact HH' | exact HD | exact Hd | exact Rc | exact Rl | exact AL0 ].
  Qed.
  End Sz3.
  Lemma np_lsw : ltac:(let t := eval cbv delta [np_lsw__stmt] in np_lsw__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb sec usec capx lenx dw. ltac2:(SecDiet.SzSec.closeP 'np_lsw__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End NpBody.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_chkA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

(* [comment removed for export] *)
Lemma le4_s32 : forall c, (0 <= c < 2^32)%Z -> le4 (Z_to_bv 64 (s32 c)) = le4 (Z_to_bv 64 c).
Proof.
  intros c Hc. pose proof (unsigned_s32 c Hc) as US.
  rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 (s32 c))). rewrite US.
  destruct (Z.ltb_spec c (2^31)); [reflexivity|].
  rewrite (le4_mod32 (c + 2^64 - 2^32)) by lia. f_equal. f_equal. Z.div_mod_to_equations. lia.
Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NpBody.
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
  Definition np_lswap__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r22 r23 r27 t3 t4 t5 t6 : word)
      (c0 c1 c4 c5 c6 c7 c8 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec capr lenr : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 capr); C4 (Z_to_bv 64 lenr)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= capr < 2^32)%Z -> (0 <= lenr < 2^32)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_tail MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec lenr capr) lenr capr sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (HA + 20)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (HA + 16)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               r22 r23 (Z_to_bv 64 HA) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) r27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x88ae0) fc None mm (seg_rom asegs)).
  Section Sz2.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r22 r23 r27 t3 t4 t5 t6 c0 c1 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb sec usec capr lenr dw : ltac2:(SecDiet.SzSec.tyM 'np_lswap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_lswap__body : ltac2:(SecDiet.SzSec.bodyP 'np_lswap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
 intros CTX INV PC FRA HH HD Hd Rc Rl AL0.
    np_setup GL CTX INV.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof (munch_refl [(HA, HA + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    ck0 HAUNP; ck_go.
    ck0 HAUNP; ck_go.
    rewrite (sx32_s32 capr) by lia.
    zstep. rewrite (sx32_s32 lenr) by lia.
    zstep. zstep.
    zstep.                                (* [comment removed for export] *)
    lazymatch goal with HH1 : rw_cells asegs _ HA _ |- _ => rename HH1 into HH6 end.
    assert (HH7 : rw_cells asegs m1 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 lenr); C4 (Z_to_bv 64 capr)]).
    { eapply rw_cells_recell; [exact HH6 | cbn; repeat split; exact Logic.I |].
      cbn [cells_bytes cbytes app]. rewrite (le4_s32 lenr), (le4_s32 capr) by lia. reflexivity. }
    assert (FX : Forall (cobj_iv FL CL) [(HA, HA + 24)]%Z) by cobj_ivs.
    destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m1 [] _ (bv_unsigned sp) (Forall_nil _) FX G MU WM ltac:(lia)) as [G5 AG5].
    assert (PC5 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m1)
      by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact Ha| | exact PC];
          intros a Ha; exact (pb_outside _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ [] _ (bv_unsigned sp) (Forall_nil _) FX G a Ha)).
    apply evtF_done. subst POSTQ.
    eapply (np_chk HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP)
      with (dsh := dsh) (sec := sec) (usec := usec) (cap := lenr) (len := capr) (dw := CB 8 dwj);
      [ exact CTX | | exact PC5 | eassumption | exact HH7 | eassumption | reflexivity | exact Rl | exact Rc | exact AL0 ].
    unfold np_inv0, np_shadow. split; [exact FP|]. split; [exact G5|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG5|]. intros a (K & (QN & _)). split; [exact K|]. split; [exact QN| exact I]. }
    split; [exists k0, k1, k2, fj; assumption|]. split; assumption.
  Qed.
  End Sz2.
  Lemma np_lswap : ltac:(let t := eval cbv delta [np_lswap__stmt] in np_lswap__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 r22 r23 r27 t3 t4 t5 t6 c0 c1 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb sec usec capr lenr dw. ltac2:(SecDiet.SzSec.closeP 'np_lswap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma np_lsw : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a1 a3 a4 a5 a6 a7 r22 r23 t3 t4 t5 t6 : word)
      (c0 c1 c4 c5 c6 c7 c8 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec capx lenx : Z) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 (Z_to_bv 64 (P + 56)); C8 c4; C8 c5; C8 c6; C8 c8; C8 c7; C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892));
                           C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 capx); C4 (Z_to_bv 64 lenx)] -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= capx < 2^64)%Z -> (0 <= lenx < 2^64)%Z -> (0 < alloc)%Z ->
    implMG RNGx (let '(caplen, len) := match k_lsw k with
                                        | NOT_SWAPPED => ((capx mod 2^32)%Z, (lenx mod 2^32)%Z)
                                        | MAYBE_SWAPPED => if (capx mod 2^32 <=? lenx mod 2^32)%Z then ((capx mod 2^32)%Z, (lenx mod 2^32)%Z) else ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                        | SWAPPED => ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                        end in
                 np_tail MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr sec usec caplen len) caplen len sec usec) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (HA + 20)) a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7
               (Z_to_bv 64 (HA + 16)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               r22 r23 (Z_to_bv 64 HA) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 Fb) (Z_to_bv 64 (P + 648)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x88a80) fc None mm (seg_rom asegs)).      (* [comment removed for export] *)
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
    intros until dw. intros CTX INV PC FRA HH HD Hd Hcx Hlx AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear CELLS BUF.
    set (capr := (capx mod 2^32)%Z) in *. set (lenr := (lenx mod 2^32)%Z) in *.
    assert (Rc : (0 <= capr < 2^32)%Z) by (subst capr; Z.div_mod_to_equations; lia).
    assert (Rl : (0 <= lenr < 2^32)%Z) by (subst lenr; Z.div_mod_to_equations; lia).
    pose proof (unsigned_s32 capr Rc) as US1. pose proof (unsigned_s32 lenr Rl) as US2.
    assert (HH' : rw_cells asegs mm HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 capr); C4 (Z_to_bv 64 lenr)]).
    { eapply rw_cells_recell; [exact HH | cbn; repeat split; exact Logic.I |].
      cbn [cells_bytes cbytes app]. rewrite (le4_mod32 lenx), (le4_mod32 capx) by lia. reflexivity. }
    clear HH.
    pose proof (munch_refl [(HA, HA + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep.
    ck0 PUNP; ck_go.
    zstep. rewrite (np_sx32_small (lenswap_code (k_lsw k))) by (destruct (k_lsw k); cbn; lia).
    zstep.
    destruct (k_lsw k); cbn [lenswap_code].
    - (* [comment removed for export] *)
      zstep. if_false. zstep. zstep. if_true.
      zstep. if_false.                    (* [comment removed for export] *)
      apply evtF_done. subst POSTQ.
      eapply (np_chk HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP)
        with (dsh := dsh) (sec := sec) (usec := usec) (cap := capr) (len := lenr);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH' | exact HD | exact Hd | exact Rc | exact Rl | exact AL0 ].
    - (* [comment removed for export] *)
      zstep. if_true.
      zstep. if_false.                    (* [comment removed for export] *)
      apply evtF_done. subst POSTQ.
      eapply np_lswap with (dsh := dsh) (sec := sec) (usec := usec);
        [ exact CTX | exact INV | exact PC | exact FRA | exact HH' | exact HD | exact Hd | exact Rc | exact Rl | exact AL0 ].
    - (* [comment removed for export] *)
      zstep. if_false. zstep. zstep. if_false.
      zstep. if_false.                    (* [comment removed for export] *)
      ck0 HAUNP; ck_go.
      ck0 HAUNP; ck_go.
      rewrite (sx32_s32 capr) by lia.
      zstep. rewrite (sx32_s32 lenr) by lia.
      zstep.
      destruct (Z.leb_spec capr lenr) as [LE|GT].
      + (* [comment removed for export] *)
        if_cases Kc; [zify_cond Kc; exfalso; rewrite <- ?unsigned_lit_wrap, ?US1, ?US2 in Kc; destruct (Z.ltb_spec capr (2^31)); destruct (Z.ltb_spec lenr (2^31)); lia|].
        zstep.
        apply evtF_done. subst POSTQ.
        eapply (np_chk HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP)
          with (dsh := dsh) (sec := sec) (usec := usec) (cap := capr) (len := lenr);
          [ exact CTX | exact INV | exact PC | exact FRA | exact HH' | exact HD | exact Hd | exact Rc | exact Rl | exact AL0 ].
      + if_cases Kc; [|zify_cond Kc; exfalso; rewrite <- ?unsigned_lit_wrap, ?US1, ?US2 in Kc; destruct (Z.ltb_spec capr (2^31)); destruct (Z.ltb_spec lenr (2^31)); lia].
        apply evtF_done. subst POSTQ.
        eapply np_lswap with (dsh := dsh) (sec := sec) (usec := usec);
          [ exact CTX | exact INV | exact PC | exact FRA | exact HH' | exact HD | exact Hd | exact Rc | exact Rl | exact AL0 ].
  Qed.

End NpBody.
End CANSEC1.
End TwB.
End F_sfnp_bodyA.

(* [comment removed for export] *)
Module F_sfnp_scaleA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ppA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_fuzz_segA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_defsA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfnp_exitA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_fuzz_segA__A3P.F_sfnp_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_failA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_finA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_normA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_growA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_norm2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_discA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_overA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_exitA__A3P.F_sfnp_over2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfnp_normA__A3P.F_sfnp_bodyA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sassume := first [ match goal with H : ?T |- ?G => constr_eq T G; exact H end | eassumption ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.

(* [comment removed for export] *)
Lemma div1000_magic71 : forall u, (0 <= u < 2^32)%Z -> (u * 2361183241434822607 / 2^64 / 2^7 = u / 1000)%Z.
Proof. intros u Hu. rewrite Z.div_div by lia. change (2^64 * 2^7)%Z with (2^71)%Z. Z.div_mod_to_equations. lia. Qed.
Definition usec_div1000_A__stmt : Prop := forall u, (0 <= u < 2^32)%Z ->
  (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 u) * 2361183241434822607) 64))) 7
   + Z.shiftr (Z.shiftr (bv_signed (Z_to_bv 64 u) * 2361183241434822607) 64 mod 18446744073709551616) 63 = u / 1000)%Z.
Section Sz2.
Variables u : ltac2:(SecDiet.SzSec.tyM 'usec_div1000_A__stmt "v" @u).
#[using="Type"] Lemma usec_div1000_A__body : ltac2:(SecDiet.SzSec.bodyP 'usec_div1000_A__stmt "v").
Proof.
  intros Hu.
 rewrite (signed_lit_small u) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (Q : (0 <= u * 2361183241434822607 / 2^64 < 2^30)%Z) by (Z.div_mod_to_equations; lia).
  set (q := (u * 2361183241434822607 / 2^64)%Z) in *.
  rewrite (signed_lit_small q) by lia. rewrite (Z.mod_small q) by lia.
  replace (q / 2^63)%Z with 0%Z by (symmetry; apply Z.div_small; lia). rewrite Z.add_0_r.
  subst q. apply div1000_magic71. exact Hu.
Qed.
End Sz2.
Lemma usec_div1000_A : ltac:(let t := eval cbv delta [usec_div1000_A__stmt] in usec_div1000_A__stmt in exact t).
Proof. intros u. ltac2:(SecDiet.SzSec.closeP 'usec_div1000_A__body "v"). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NpScale.
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
  Definition np_scale__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (CL FB : list (@cblock hptr)) (FL : list fblock) (trC : list Z)
      (lo P HA DA Af SPA Fb : Z) (m : mem) (o : option hptr)
      (RNGx : footprint) (sx : PState H hptr) (dsh : list byte) (mm : mem)
      (ra0 t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 t6 : word)
      (c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 : word)
      (k : npk hptr) (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (secx usecx capx lenx : Z) (hcs : list cell) (dw : cell),
    np_ctx TP ra sp tp s0 L RNG CL FB FL trC lo HA DA Af SPA (k_f k) m ->
    np_inv0 GIOA fflagA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo HA DA SPA Fb o m RNGx sx
            (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) dsh mm ->
    PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB mm ->
    rw_cells asegs mm SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 (Z_to_bv 64 DA);
                           C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
    rw_cells asegs mm HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs mm DA [dw] -> csize dw = 8%nat ->
    (0 <= secx < 2^64)%Z -> (0 <= usecx < 2^64)%Z -> (0 <= capx < 2^64)%Z -> (0 <= lenx < 2^64)%Z -> (0 < alloc)%Z ->
    implMG RNGx (np_body_model MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (secx mod 2^32) (usecx mod 2^32) (capx mod 2^32) (lenx mod 2^32)) sx
      (next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo P HA DA m o)
      (MS (mkR ra0 (Z_to_bv 64 SPA) gp tp t0 t1 t2 sp (Z_to_bv 64 SPA) (Z_to_bv 64 capx) (Z_to_bv 64 secx) (Z_to_bv 64 usecx) a3 (Z_to_bv 64 lenx) a5 a6 a7
               (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
               (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880)) (Z_to_bv 64 (HA + 16)) (Z_to_bv 64 HA) (Z_to_bv 64 Fb)
               (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 648)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x884e0) fc None mm (seg_rom asegs)).
  Section Sz3.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 t6 c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb secx usecx capx lenx hcs dw : ltac2:(SecDiet.SzSec.tyM 'np_scale__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma np_scale__body : ltac2:(SecDiet.SzSec.bodyP 'np_scale__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP.
    intros CTX INV PC FRA HH Hh HD Hd Hsx Hux Hcx Hlx AL0.
    np_setup GL CTX INV.
    np_open PC.
    np_blocks GL G OHA ODA IFL.
    clear CELLS BUF.
    assert (Rs : (0 <= secx mod 2^32 < 2^32)%Z) by (Z.div_mod_to_equations; lia).
    assert (Ru : (0 <= usecx mod 2^32 < 2^32)%Z) by (Z.div_mod_to_equations; lia).
    destruct (rw_cells_forget _ _ _ _ HH) as [hj HH']. rewrite Hh in HH'. clear HH.
    apply (rw_cells_split_CB asegs mm _ [] 24 _ [] [8; 8; 4; 4]%nat) in HH'; [|reflexivity]. cbn [mk_CB_cells app] in HH'.
    repeat match type of HH' with context [CB _ ?t] =>
      lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "hk" in set (j := t) in HH'; clearbody j end.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    assert (ROM : ro_cells asegs mm 0x10350 [C8 (Z_to_bv 64 2361183241434822607)]).
    { pose proof (ro_cells_image asegs mm 0x10350 (le8 (Z_to_bv 64 2361183241434822607)) MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite length_le8; lia)) as [WFr BYr].
      split; [cbn; repeat split| cbn [cells_bytes cbytes] in *; exact BYr]. }
    unfold np_body_model. cbn [sf_of pc_priv sf_scale_type sf_lengths_swapped pv].
    pose proof (munch_refl [(HA, HA + 24)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (POSTQ := Q) end. apply implMG_from_evtF.
    zstep. zstep.
    ck0 HAUNP; ck_go.
    zstep.
    ck0 HAUNP; ck_go.
    do 3 zstep.
    zstep. zstep.
    ck0_at HAUNP (HA + 8)%Z; ck_go.
    do 4 zstep.
    ck0 PUNP; ck_go.
    zstep. rewrite (np_sx32_small (sfscale_code (k_scl k))) by (destruct (k_scl k); cbn; lia).
    zstep. zstep.
    assert (FX : Forall (cobj_iv FL CL) [(HA, HA + 24)]%Z) by cobj_ivs.
    assert (FIN : forall (usecv : Z) (m7 : mem) (ra7 t07 t17 t27 a17 a27 a47 a57 a67 a77 t37 t47 t57 t67 : word),
      munch [(HA, HA + 24)]%Z mm m7 -> wmono asegs mm m7 -> mem_inv asegs m7 ->
      stk asegs m7 lo SPA -> stk asegs m7 (SPA + 120) (bv_unsigned sp + -104) ->
      rw_cells asegs m7 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs m7 Fb [C8 k0; C8 k1; C8 k2; CB (Z.to_nat 8160) fj; C8 (Z_to_bv 64 (fflagA L FF_NEXT_PACKET Fb))] ->
      rw_cells asegs m7 (Z.shiftr Fb 3 + 2147450880) np_shadow -> rw_cells asegs m7 (Z.shiftr Fb 3 + 2147450892) [CB 512 dsh] ->
      rw_cells asegs m7 SPA [C8 c0; C8 c1; C8 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)); C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 (Z_to_bv 64 DA);
                             C8 (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450892)); C8 (Z_to_bv 64 Af); C8 c12; C8 c13; C8 c14] ->
      rw_cells asegs m7 HA [C8 (Z_to_bv 64 (secx mod 4294967296)); C8 (Z_to_bv 64 usecv); C4 (Z_to_bv 64 capx); C4 (Z_to_bv 64 lenx)] ->
      rw_cells asegs m7 DA [CB 8 dwj] ->
      implMG RNGx (let '(caplen, len) := match k_lsw k with
                                          | NOT_SWAPPED => ((capx mod 2^32)%Z, (lenx mod 2^32)%Z)
                                          | MAYBE_SWAPPED => if (capx mod 2^32 <=? lenx mod 2^32)%Z then ((capx mod 2^32)%Z, (lenx mod 2^32)%Z) else ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                          | SWAPPED => ((lenx mod 2^32)%Z, (capx mod 2^32)%Z)
                                          end in
                   np_tail MOps (prims HO FO sites) (pv k bq bsz alloc data eb) (mkHdr (secx mod 2^32) usecv caplen len) caplen len (secx mod 2^32) usecv) sx POSTQ
        (MS (mkR ra7 (Z_to_bv 64 SPA) gp tp t07 t17 t27 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (HA + 20)) a17 a27 (Z_to_bv 64 (Z.shiftr (HA + 20) 3 + 2147450880)) a47 a57 a67 a77
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr Fb 3 + 2147450880)) (Z_to_bv 64 P) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880)) (Z_to_bv 64 (HA + 16)) (Z_to_bv 64 HA) (Z_to_bv 64 Fb)
                 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 648)) t37 t47 t57 t67)
            F (Z_to_bv 64 0x885a8) fc None m7 (seg_rom asegs))).
    { intros usecv m7 ra7 t07 t17 t27 a17 a27 a47 a57 a67 a77 t37 t47 t57 t67 MU7 WM7 MI7 ST7 STG7 FR7 FRC7 SHC7 SHD7 FRA7 HH7 HD7.
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ m7 [] _ (bv_unsigned sp) (Forall_nil _) FX G MU7 WM7 ltac:(lia)) as [G7 AG7].
      assert (PC7 : PCAPR (hptr:=hptr) P (pv k bq bsz alloc data eb) (pcap_blocks (pv k bq bsz alloc data eb) P Bx 0) FB m7)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU7| exact WM7|]; intros a _ Ha; exact Ha| | exact PC];
            intros a Ha; exact (pb_outside _ _ _ GL _ _ _ _ _ _ FL [(FF_NEXT_PACKET, Fb, 8192%Z)] _ [] _ (bv_unsigned sp) (Forall_nil _) FX G a Ha)).
      subst POSTQ.
      eapply (np_lsw HO FO sites GIOA TP fflagA GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP) with (dsh := dsh) (dw := CB 8 dwj);
        [ exact CTX | | exact PC7 | exact FRA7 | exact HH7 | exact HD7 | reflexivity | exact Hcx | exact Hlx | exact AL0 ].
      unfold np_inv0. split; [exact FP|]. split; [exact G7|]. split; [exact OF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [assumption|].
      split. { eapply agrees_on_trans; [exact AG|]. eapply agrees_on_weaken; [exact AG7|]. intros a (K & (QN & _)). split; [exact K|]. split; [exact QN| exact I]. }
      split; [exists k0, k1, k2, fj; assumption|]. split; assumption. }
    destruct (k_scl k) eqn:ESCL; cbn [sfscale_code].
    - (* [comment removed for export] *)
      if_false. zstep. zstep. if_true.
      apply evtF_done. eapply FIN; sassume.
    - (* [comment removed for export] *)
      if_false. zstep. zstep. if_false.
      ck0_at HAUNP (HA + 8)%Z; ck_go.
      zstep. zstep. zstep. zstep.
      ck0_at HAUNP (HA + 8)%Z; ck_go.
      zstep.
      apply evtF_done. eapply FIN; sassume.
    - (* [comment removed for export] *)
      if_true.
      ck0_at HAUNP (HA + 8)%Z; ck_go.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite (usec_div1000_A (usecx mod 4294967296)) by lia.
      ck0_at HAUNP (HA + 8)%Z; ck_go.
      zstep.
      apply evtF_done. eapply FIN; sassume.
  Qed.
  End Sz3.
  Lemma np_scale : ltac:(let t := eval cbv delta [np_scale__stmt] in np_scale__stmt in exact t).
  Proof using GL HAL GPL FFREE7 SETF8 SET00 FREAD FERROR FMT SNPRINTF REALLOC RPC PP MAXSNAP. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CL FB FL trC lo P HA DA Af SPA Fb m o RNGx sx dsh mm ra0 t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 t6 c0 c1 c3 c4 c5 c6 c7 c8 c12 c13 c14 k bq Bx bsz alloc data eb secx usecx capx lenx hcs dw. ltac2:(SecDiet.SzSec.closeP 'np_scale__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpScale.
End CANSEC1.
End F_sfnp_scaleA.
