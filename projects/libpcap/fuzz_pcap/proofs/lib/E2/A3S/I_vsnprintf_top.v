(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strerror__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.Printf_snsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vfprintf_sn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vsnprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vsnprintf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition VSNPRINTF_STUB : Z := 0x444a4.
Definition VSNPRINTF_I_ENTRY : Z := 0x47e18.
Definition VSNPRINTF_I_DEPTH : Z := 8064.   (* [comment removed for export] *)

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Lemma arg_ok_inner : forall RNG Fp FS ap B BS m m' lo sp sp' w a (W : list (Z * Z)),
  arg_ok lo 0 B BS RNG m lo sp lo w a -> sp' <= sp -> lo <= Fp -> Fp + FS <= sp -> lo <= ap -> ap + 8 <= sp ->
  munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  arg_ok Fp FS B BS RNG m' lo sp' ap w a.
Proof.
  intros RNG Fp FS ap B BS m m' lo sp sp' w a W H Hsp HF1 HF2 HA1 HA2 MU WM AW HW. destruct a as [s|i|u|u]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & S47 & RGs & SOs). exists slack.
  split.
  { eapply bytes_at_transport; [exact BY | exact MU |].
    rewrite length_app, zb_length. cbn [length]. unfold zlength in *.
    clear - HW D1 D3. induction HW as [|[u1 u2] W' Hiv _ IH]; cbn [disjoint_from]; [exact I|]. cbn [fst snd] in Hiv. split; [Lia.lia | exact IH]. }
  split; [exact HF|]. split; [exact PAD|]. split; [exact NZ|].
  split; [clear - D1 Hsp; Lia.lia|]. split; [clear - D1 HF1 HF2; Lia.lia|]. split; [exact D3|]. split; [clear - D1 HA1 HA2; Lia.lia|].
  split; [exact S47|]. split; [exact RGs|]. exact (sobj_transport _ _ _ _ _ _ SOs MU WM AW).
Qed.
#[using="Type"] Lemma args_ok_inner : forall RNG Fp FS ap B BS m m' lo sp sp' ws args (W : list (Z * Z)),
  args_ok lo 0 B BS RNG m lo sp lo ws args -> sp' <= sp -> lo <= Fp -> Fp + FS <= sp -> lo <= ap -> ap + 8 <= sp ->
  munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  args_ok Fp FS B BS RNG m' lo sp' ap ws args.
Proof.
  intros RNG Fp FS ap B BS m m' lo sp sp' ws args W. revert ws. induction args as [|a args IH]; intros ws H Hsp HF1 HF2 HA1 HA2 MU WM AW HW; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_inner; eassumption | apply IH; assumption].
Qed.
End CANSEC0.

Section VsnI.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D n A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Let q := bv_unsigned sp.
  Hypothesis HN : 1 <= n < 2^31.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - VSNPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QHI : q <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^64.
  Hypothesis HD : 0 < D /\ D + n <= 2^63 /\ (D + n <= 0x10000 \/ 0x603000 <= D) /\ (D + n <= lo \/ VA + 8 * zlength slots <= D).
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESD : iesafe [(D, D + n)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RD : rng RNG D n.
  Hypothesis R0 : rng0 RNG.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem vsnprintf_ie_spec : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells asegs m D [CB (Z.to_nat n) jd] ->
    bytes_at asegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok lo 0 D n RNG m lo q lo slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m -> fany fc ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m D (D + n) ->
    pargs_okL RNG lo sp m its (Z_to_bv 64 VA) -> pargs_sep [(D, D + n)] its (Z_to_bv 64 VA) ->
    evtF asegs RNG (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSNPRINTF_I_ENTRY) fc None m (seg_rom asegs)).
  Proof using HN HF P1 PIECES LO GLO QHI HA HVA HD KLO IESD RSTK RIMG RVA RD R0 FSTR NOZ EF OK.
    pin_using (fun (HN HF P1 PIECES LO GLO QHI HA HVA HD KLO : unit) => tt).
    intros until jd. intros -> -> -> -> DST BY VAA AOK ST SSP MI FRM ENV CKP SOSTK SOFMT SOPFX SOD PAOK PSEP.
    unfold VSNPRINTF_I_DEPTH, VSNPRINTF_I_ENTRY, GLOBALS_TOP in *. subst q.
    pose proof (sobj_appW _ _ _ _ SOD) as APD.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vsnprintf_i_pre_e RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PAOK ]. }
    cbv beta. intros ms1 MID. unfold vsnprintf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & j8 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -4480, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    assert (DST1 : rw_cells asegs m1 D [CB (Z.to_nat n) jd]).
    { eapply (rw_cells_transport asegs _ m m1); [exact DST | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; unfold zlength in *; lia]. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (VAA1 : va_area m1 VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAA | exact MU1 | cbn [disjoint_from]; rewrite u64s_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (AOK1 : args_ok (bv_unsigned sp + -2160 - 704) SN_FS D n RNG m1 lo (bv_unsigned sp + -2160) (bv_unsigned sp + -2160 - 720) slots args).
    { eapply args_ok_inner; [exact AOK | lia | lia | unfold SN_FS; lia | lia | lia | exact MU1 | exact WM1 | exact AW1 |].
      constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (CKP1 : rt_ckpf m1).
    { eapply (rw_cells_transport asegs _ m m1); [exact CKP | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -2160)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOD1 : sobj RNG m1 D (D + n)) by (eapply sobj_transport; [exact SOD | exact MU1 | exact WM1 | exact AW1]).
    assert (PAOK1 : pargs_okL RNG lo (Z_to_bv 64 (bv_unsigned sp + -2160)) m1 its (Z_to_bv 64 VA)).
    { eapply pargs_okL_transport; [exact PAOK | exact MU1 | exact WM1 | exact AW1
                                  | eapply pargs_sep_stack; [exact PAOK | constructor; [cbn [fst snd]; lia | constructor]]
                                  | rewrite unsigned_lit by lia; lia]. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vsnprintf_spec RNG (Z_to_bv 64 0x47eac) (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp sp (Z_to_bv 64 A) (Z_to_bv 64 D) (Z_to_bv 64 n)
                (Z_to_bv 64 0x140128) s5 s6 s7 s8 s9 s10 s11 F fc D n A VA lo fmtz slots args ps r canary fstr its) with (jd := jd);
        rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP;
        first [ exact HN | exact HF | exact P1 | exact PIECES | exact KLO | exact IESD | exact RIMG | exact RVA | exact RD | exact R0 | exact FSTR | exact NOZ | exact EF | exact OK
              | reflexivity | exact DST1 | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact FRM | exact ENV1 | exact CKP1
              | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOD1 | exact PAOK1 | exact PSEP
              | eapply rng_sub'; [exact RSTK | lia]
              | unfold zlength in *; lia ]. }
    cbv beta. intros ms2 PO. unfold vsnprintf_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (v5 & v6 & v7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v28 & v29 & v30 & v31 & jd' & m2 & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & DST2 & Hr).
    (* [comment removed for export] *)
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -96)
                    [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; unfold zlength in *; lia]. }
    assert (STM2 : stk asegs m2 (bv_unsigned sp + -2160) (bv_unsigned sp + -96)).
    { eapply stk_transport_disjoint; [exact STM1 | exact MU2 | exact WM2 | cbn [disjoint_from]; unfold zlength in *; lia]. }
    assert (AW2 : appW [(lo, bv_unsigned sp + -2160); (D, D + n)]) by (apply appW_cons; [apply appW_one_high; exact KLO | exact APD]).
    assert (ENV2 : icptenv m2) by (eapply icptenv_transport; [exact ENV1 | exact MU2 | exact WM2 | solve_iesafe]).
    assert (SOD2 : sobj RNG m2 D (D + n)) by (eapply sobj_transport; [exact SOD1 | exact MU2 | exact WM2 | exact AW2]).
    pose proof (rw_cells_merge asegs m2 _ [] [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 8 j8] _ FR2) as FRm. cbn [app cells_size csize Nat.add] in FRm.
    replace (ret_pc (Z_to_bv 64 0x47eac)) with (Z_to_bv 64 0x47eac : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vsnprintf_i_post RNG) with (lo := lo) (D := D) (n := n) (r := r);
        first [ exact MI2 | exact ST2 | exact STM2 | exact FRm | exact KLO | exact ENV2 | exact HN | exact SOD2 | exact RIMG | exact RSTK | lia ]. }
    cbv beta. intros ms3 PO3. unfold vsnprintf_i_post_post in PO3.
    destruct PO3 as (w5 & w6 & w7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w28 & w29 & w30 & w31 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    apply evtF_done. unfold vsnprintf_post.
    do 14 eexists. exists jd', m3.
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m3).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - apply (munch_trans _ m1 m2 m3).
               + eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia.
               + eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
    split. { destruct SSP2 as [G1 G2]. split; (eapply (rw_cells_transport asegs _ m2 m3); [eassumption | exact MU3 | exact WM3 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    split; [| exact Hr].
    eapply (rw_cells_transport asegs _ m2 m3); [exact DST2 | exact MU3 | exact WM3 |].
    pose proof (rw_cells_bound _ _ _ _ DST2) as DB2. cbn [cells_size csize Nat.add] in DB2 |- *. cbn [disjoint_from]. unfold zlength in *. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem vsnprintf_i_spec : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells asegs m D [CB (Z.to_nat n) jd] ->
    bytes_at asegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok lo 0 D n RNG m lo q lo slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m -> fany fc ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m D (D + n) ->
    pargs_okL RNG lo sp m its (Z_to_bv 64 VA) -> pargs_sep [(D, D + n)] its (Z_to_bv 64 VA) ->
    evtF asegs RNG (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSNPRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HN HF P1 PIECES LO GLO QHI HA HVA HD KLO IESD RSTK RIMG RVA RD R0 FSTR NOZ EF OK.
    intros until jd. intros E0 E1 E2 E3 DST BY VAA AOK ST SSP MI FRM ENV CKP SOSTK SOFMT SOPFX SOD PAOK PSEP.
    unfold VSNPRINTF_STUB. zstep.
    eapply vsnprintf_ie_spec; eassumption.
  Qed.
End VsnI.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.Printf_snsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vfprintf_sn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vsnprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vsnprintf.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition VSNPRINTF_STUB : Z := 0x4450c.
Definition VSNPRINTF_I_ENTRY : Z := 0x47e80.
Definition VSNPRINTF_I_DEPTH : Z := 8064.   (* [comment removed for export] *)

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Lemma arg_ok_inner : forall RNG Fp FS ap B BS m m' lo sp sp' w a (W : list (Z * Z)),
  arg_ok lo 0 B BS RNG m lo sp lo w a -> sp' <= sp -> lo <= Fp -> Fp + FS <= sp -> lo <= ap -> ap + 8 <= sp ->
  munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  arg_ok Fp FS B BS RNG m' lo sp' ap w a.
Proof.
  intros RNG Fp FS ap B BS m m' lo sp sp' w a W H Hsp HF1 HF2 HA1 HA2 MU WM AW HW. destruct a as [s|i|u|u]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & S47 & RGs & SOs). exists slack.
  split.
  { eapply bytes_at_transport; [exact BY | exact MU |].
    rewrite length_app, zb_length. cbn [length]. unfold zlength in *.
    clear - HW D1 D3. induction HW as [|[u1 u2] W' Hiv _ IH]; cbn [disjoint_from]; [exact I|]. cbn [fst snd] in Hiv. split; [Lia.lia | exact IH]. }
  split; [exact HF|]. split; [exact PAD|]. split; [exact NZ|].
  split; [clear - D1 Hsp; Lia.lia|]. split; [clear - D1 HF1 HF2; Lia.lia|]. split; [exact D3|]. split; [clear - D1 HA1 HA2; Lia.lia|].
  split; [exact S47|]. split; [exact RGs|]. exact (sobj_transport _ _ _ _ _ _ SOs MU WM AW).
Qed.
#[using="Type"] Lemma args_ok_inner : forall RNG Fp FS ap B BS m m' lo sp sp' ws args (W : list (Z * Z)),
  args_ok lo 0 B BS RNG m lo sp lo ws args -> sp' <= sp -> lo <= Fp -> Fp + FS <= sp -> lo <= ap -> ap + 8 <= sp ->
  munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  args_ok Fp FS B BS RNG m' lo sp' ap ws args.
Proof.
  intros RNG Fp FS ap B BS m m' lo sp sp' ws args W. revert ws. induction args as [|a args IH]; intros ws H Hsp HF1 HF2 HA1 HA2 MU WM AW HW; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_inner; eassumption | apply IH; assumption].
Qed.
End CANSEC0.

Section VsnI.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D n A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Let q := bv_unsigned sp.
  Hypothesis HN : 1 <= n < 2^31.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - VSNPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QHI : q <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^64.
  Hypothesis HD : 0 < D /\ D + n <= 2^63 /\ (D + n <= 0x10000 \/ 0x604000 <= D) /\ (D + n <= lo \/ VA + 8 * zlength slots <= D).
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESD : iesafe [(D, D + n)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RD : rng RNG D n.
  Hypothesis R0 : rng0 RNG.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem vsnprintf_ie_spec : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells asegs m D [CB (Z.to_nat n) jd] ->
    bytes_at asegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok lo 0 D n RNG m lo q lo slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m -> fany fc ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m D (D + n) ->
    pargs_okL RNG lo sp m its (Z_to_bv 64 VA) -> pargs_sep [(D, D + n)] its (Z_to_bv 64 VA) ->
    evtF asegs RNG (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSNPRINTF_I_ENTRY) fc None m (seg_rom asegs)).
  Proof using HN HF P1 PIECES LO GLO QHI HA HVA HD KLO IESD RSTK RIMG RVA RD R0 FSTR NOZ EF OK.
    pin_using (fun (HN HF P1 PIECES LO GLO QHI HA HVA HD KLO : unit) => tt).
    intros until jd. intros -> -> -> -> DST BY VAA AOK ST SSP MI FRM ENV CKP SOSTK SOFMT SOPFX SOD PAOK PSEP.
    unfold VSNPRINTF_I_DEPTH, VSNPRINTF_I_ENTRY, GLOBALS_TOP in *. subst q.
    pose proof (sobj_appW _ _ _ _ SOD) as APD.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vsnprintf_i_pre_e RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PAOK ]. }
    cbv beta. intros ms1 MID. unfold vsnprintf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & j8 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -4480, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    assert (DST1 : rw_cells asegs m1 D [CB (Z.to_nat n) jd]).
    { eapply (rw_cells_transport asegs _ m m1); [exact DST | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; unfold zlength in *; lia]. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (VAA1 : va_area m1 VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAA | exact MU1 | cbn [disjoint_from]; rewrite u64s_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (AOK1 : args_ok (bv_unsigned sp + -2160 - 704) SN_FS D n RNG m1 lo (bv_unsigned sp + -2160) (bv_unsigned sp + -2160 - 720) slots args).
    { eapply args_ok_inner; [exact AOK | lia | lia | unfold SN_FS; lia | lia | lia | exact MU1 | exact WM1 | exact AW1 |].
      constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (CKP1 : rt_ckpf m1).
    { eapply (rw_cells_transport asegs _ m m1); [exact CKP | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -2160)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOD1 : sobj RNG m1 D (D + n)) by (eapply sobj_transport; [exact SOD | exact MU1 | exact WM1 | exact AW1]).
    assert (PAOK1 : pargs_okL RNG lo (Z_to_bv 64 (bv_unsigned sp + -2160)) m1 its (Z_to_bv 64 VA)).
    { eapply pargs_okL_transport; [exact PAOK | exact MU1 | exact WM1 | exact AW1
                                  | eapply pargs_sep_stack; [exact PAOK | constructor; [cbn [fst snd]; lia | constructor]]
                                  | rewrite unsigned_lit by lia; lia]. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vsnprintf_spec RNG (Z_to_bv 64 0x47f14) (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp sp (Z_to_bv 64 A) (Z_to_bv 64 D) (Z_to_bv 64 n)
                (Z_to_bv 64 0x140528) s5 s6 s7 s8 s9 s10 s11 F fc D n A VA lo fmtz slots args ps r canary fstr its) with (jd := jd);
        rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP;
        first [ exact HN | exact HF | exact P1 | exact PIECES | exact KLO | exact IESD | exact RIMG | exact RVA | exact RD | exact R0 | exact FSTR | exact NOZ | exact EF | exact OK
              | reflexivity | exact DST1 | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact FRM | exact ENV1 | exact CKP1
              | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOD1 | exact PAOK1 | exact PSEP
              | eapply rng_sub'; [exact RSTK | lia]
              | unfold zlength in *; lia ]. }
    cbv beta. intros ms2 PO. unfold vsnprintf_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (v5 & v6 & v7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v28 & v29 & v30 & v31 & jd' & m2 & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & DST2 & Hr).
    (* [comment removed for export] *)
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -96)
                    [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; unfold zlength in *; lia]. }
    assert (STM2 : stk asegs m2 (bv_unsigned sp + -2160) (bv_unsigned sp + -96)).
    { eapply stk_transport_disjoint; [exact STM1 | exact MU2 | exact WM2 | cbn [disjoint_from]; unfold zlength in *; lia]. }
    assert (AW2 : appW [(lo, bv_unsigned sp + -2160); (D, D + n)]) by (apply appW_cons; [apply appW_one_high; exact KLO | exact APD]).
    assert (ENV2 : icptenv m2) by (eapply icptenv_transport; [exact ENV1 | exact MU2 | exact WM2 | solve_iesafe]).
    assert (SOD2 : sobj RNG m2 D (D + n)) by (eapply sobj_transport; [exact SOD1 | exact MU2 | exact WM2 | exact AW2]).
    pose proof (rw_cells_merge asegs m2 _ [] [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 8 j8] _ FR2) as FRm. cbn [app cells_size csize Nat.add] in FRm.
    replace (ret_pc (Z_to_bv 64 0x47f14)) with (Z_to_bv 64 0x47f14 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vsnprintf_i_post RNG) with (lo := lo) (D := D) (n := n) (r := r);
        first [ exact MI2 | exact ST2 | exact STM2 | exact FRm | exact KLO | exact ENV2 | exact HN | exact SOD2 | exact RIMG | exact RSTK | lia ]. }
    cbv beta. intros ms3 PO3. unfold vsnprintf_i_post_post in PO3.
    destruct PO3 as (w5 & w6 & w7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w28 & w29 & w30 & w31 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    apply evtF_done. unfold vsnprintf_post.
    do 14 eexists. exists jd', m3.
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m3).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - apply (munch_trans _ m1 m2 m3).
               + eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia.
               + eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
    split. { destruct SSP2 as [G1 G2]. split; (eapply (rw_cells_transport asegs _ m2 m3); [eassumption | exact MU3 | exact WM3 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    split; [| exact Hr].
    eapply (rw_cells_transport asegs _ m2 m3); [exact DST2 | exact MU3 | exact WM3 |].
    pose proof (rw_cells_bound _ _ _ _ DST2) as DB2. cbn [cells_size csize Nat.add] in DB2 |- *. cbn [disjoint_from]. unfold zlength in *. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem vsnprintf_i_spec : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (jd : list byte),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells asegs m D [CB (Z.to_nat n) jd] ->
    bytes_at asegs m A (zb fmtz) ->
    va_area m VA slots -> args_ok lo 0 D n RNG m lo q lo slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m -> fany fc ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m D (D + n) ->
    pargs_okL RNG lo sp m its (Z_to_bv 64 VA) -> pargs_sep [(D, D + n)] its (Z_to_bv 64 VA) ->
    evtF asegs RNG (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VSNPRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HN HF P1 PIECES LO GLO QHI HA HVA HD KLO IESD RSTK RIMG RVA RD R0 FSTR NOZ EF OK.
    intros until jd. intros E0 E1 E2 E3 DST BY VAA AOK ST SSP MI FRM ENV CKP SOSTK SOFMT SOPFX SOD PAOK PSEP.
    unfold VSNPRINTF_STUB. zstep.
    eapply vsnprintf_ie_spec; eassumption.
  Qed.
End VsnI.
End TwB.
