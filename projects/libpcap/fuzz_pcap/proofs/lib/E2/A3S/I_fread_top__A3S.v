(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_read__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fread.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require MonadX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Walk FP StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_core.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_mkstemp__A3S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module I_fread_top.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_read__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fread. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_fread_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fread_misc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FREAD_STUB : Z := 0x4448c.
Definition FREAD_I_DEPTH : Z := 4432.   (* [comment removed for export] *)

Section FreadI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (D n lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Definition fri_W : list (Z * Z) := [(bv_unsigned sp - FREAD_I_DEPTH, bv_unsigned sp); (Fp, Fp + 232); (B, B + bs); (D, D + n)].

  (* [comment removed for export] *)
  Definition fread_i_postM : (list Z * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ fr_inv f0 (snd r) /\ Z.of_nat (length (fst r)) <= n /\
      Forall (fun z => 0 <= z < 256) (fst r) /\ Forall (fun z => 0 <= z < 256) (f_rbuf (snd r)) /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (rp' : Z) (bufbytes' rest' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch fri_W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags' rp' (rp' + zlength (f_rbuf (snd r))) closefn 0 0 0 F_STDIO_READ (wfn_of (snd r)) seekfn B bs prev next (f_fd f0) mode' (lbf_of (snd r)) tail)
      /\ flags_ok (snd r) flags'
      /\ rw_cells asegs m' B [CB (Z.to_nat bs) bufbytes']
      /\ (f_rbuf (snd r) <> [] -> B <= rp' /\ rp' + zlength (f_rbuf (snd r)) <= B + bs
                                /\ firstn (length (f_rbuf (snd r))) (skipn (Z.to_nat (rp' - B)) bufbytes') = to_bytes (f_rbuf (snd r)))
      /\ 0 <= rp' /\ rp' + zlength (f_rbuf (snd r)) < 2^63
      /\ rw_cells asegs m' D [CB (length (fst r)) (to_bytes (fst r)); CB (Z.to_nat n - length (fst r)) rest']
      /\ ssp_cells m' canary.

  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis NB : 0 <= n <= 2^30.
  Hypothesis LO : lo <= bv_unsigned sp - FREAD_I_DEPTH.
  Hypothesis GLO : 0x603000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis DSEP1 : D + n <= got_ssp \/ got_ssp + 8 <= D.
  Hypothesis DSEP2 : D + n <= ssp_guard \/ ssp_guard + 8 <= D.
  Hypothesis B0 : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis D0 : 0 <= D.
  Hypothesis D47 : D + n <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.
  Hypothesis SD1 : D + n <= lo \/ bv_unsigned sp <= D.
  Hypothesis SD2 : D + n <= Fp \/ Fp + 232 <= D.
  Hypothesis SD3 : D + n <= B \/ B + bs <= D.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis ENV : icptenv m.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + bs)].
  Hypothesis IESD : iesafe [(D, D + n)].
  Hypothesis APWF : appW [(Fp, Fp + 232)].
  Hypothesis SOB : sobj RNG m B (B + bs).
  Hypothesis SOD : sobj RNG m D (D + n).
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B bs.
  Hypothesis RD : rng RNG D n.
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis R0 : rng0 RNG.

  Definition fread_i_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp : Z) (bufbytes djunk : list byte),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn 0 0 0 F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      flags_ok f0 flags ->
      rw_cells asegs m B [CB (Z.to_nat bs) bufbytes] ->
      (f_rbuf f0 <> [] -> B <= rp /\ rp + zlength (f_rbuf f0) <= B + bs /\ firstn (length (f_rbuf f0)) (skipn (Z.to_nat (rp - B)) bufbytes) = to_bytes (f_rbuf f0)) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      rw_cells asegs m D [CB (Z.to_nat n) djunk] ->
      f_wactive f0 = false -> f_wbuf f0 = [] -> Forall (fun z => 0 <= z < 256) (f_rbuf f0) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 Fp ->
      stk asegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv asegs m ->
      implAM RNG (fread_file f0 B D n) st fread_i_postM
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD_STUB) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk : ltac2:(SecDiet.SzSec.tyM 'fread_i_spec__stmt "vvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_i_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_i_spec__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO ENV IESF IESB IESD APWF SOB SOD RSTK RFP RBUF RD RIMG R0. pin_using (fun (B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO : unit) => tt).
    intros FC FL BUF RREL RP0 RPHI DST WACT WB0 RBR -> -> -> -> ST SSP MI.
    pose proof (sobj_appW _ _ _ _ SOB) as APWB. pose proof (sobj_appW _ _ _ _ SOD) as APWD.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD_STUB, FREAD_I_DEPTH in *.
    apply implAM_from_evt.
    pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fread_i_pre RNG); first [exact MI | exact ST | lia | exact KLO | exact (ie_ini _ ENV) | exact (ie_fread _ ENV) | exact RIMG | exact RSTK]. }
    cbv beta. intros ms1 MID.
    destruct MID as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1 & INI1).
    apply evtF_done.
    (* [comment removed for export] *)
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn 0 0 0 F_STDIO_READ (wfn_of f0) seekfn B (f_bufsize f0) prev next (f_fd f0) mode (lbf_of f0) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 B [CB (Z.to_nat (f_bufsize f0)) bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (DST1 : rw_cells asegs m1 D [CB (Z.to_nat n) djunk]).
    { eapply (rw_cells_transport asegs _ m m1); [exact DST | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOB1 : sobj RNG m1 B (B + f_bufsize f0)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | solve_appW]).
    assert (SOD1 : sobj RNG m1 D (D + n)) by (eapply sobj_transport; [exact SOD | exact MU1 | exact WM1 | solve_appW]).
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (fread_spec (St:=St) RNG (Z_to_bv 64 0x46690) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp sp (Z_to_bv 64 1) (Z_to_bv 64 D) (Z_to_bv 64 Fp) (Z_to_bv 64 n) (Z_to_bv 64 1)
               s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m1)
        with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes) (djunk := djunk);
        rewrite ?unsigned_lit by lia; unfold FREAD_DEPTH;
        first [ exact FC1 | exact FL | exact BUF1 | exact RREL | exact DST1 | exact WACT | exact WB0 | exact RBR | exact ST1 | exact SSP1 | exact MI1
              | exact NCH | exact FD | exact BS | exact NB | exact GLO | exact Fp0 | exact FPLO | exact FSEP1 | exact FSEP2 | exact BSEP1 | exact BSEP2
              | exact DSEP1 | exact DSEP2 | exact B0 | exact B47 | exact D0 | exact D47 | exact SB2 | exact SD2 | exact SD3
              | exact KLO | exact ENV1 | exact IESF | exact IESB | exact IESD | exact APWF | exact SOB1 | exact SOD1 | exact RFP | exact RBUF | exact RD | exact RIMG | exact R0
              | reflexivity | eapply rng_sub'; [exact RSTK | lia] | lia ]. }
    cbv beta. intros [got f'] st' ms' (-> & INV' & GB & GF & GRB & PO). cbn [fst snd] in INV', GB, GF, GRB, PO |- *.
    destruct PO as (v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & flags' & mode' & rp' & bufbytes' & rest' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & FL2 & BUF2 & RR2 & RP21 & RP22 & DST2 & SSP2).
    unfold fr_W, FREAD_DEPTH in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x46690)) with (Z_to_bv 64 0x46690 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof INV' as (I1 & I2 & I3 & I4 & I5 & I6 & I7). rewrite ?I3 in *.
    (* [comment removed for export] *)
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (STM2 : stk asegs m2 (bv_unsigned sp - 2128) (bv_unsigned sp - 56)).
    { eapply stk_transport_disjoint; [exact STM1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    assert (ENV2 : icptenv m2) by (eapply icptenv_transport; [exact ENV1 | exact MU2 | exact WM2 | solve_iesafe]).
    assert (SOD2 : sobj RNG m2 D (D + n)) by (eapply sobj_transport; [exact SOD1 | exact MU2 | exact WM2 | solve_appW]).
    assert (LG : 0 <= zlength got <= n) by (unfold zlength; lia).
    destruct (sobj_sub _ _ _ _ D (D + zlength got) SOD2 ltac:(lia) ltac:(lia) ltac:(lia)) as (APP2 & UNP2 & NSZ2 & RLO & RHI & HR2 & WR2 & RSH2).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fread_i_post RNG) with (lo := lo) (res := zlength got) (size := 1) (N := zlength got) (RLO := RLO) (RHI := RHI);
        rewrite ?unsigned_lit by lia;
        first [ exact MI2 | exact ST2 | exact STM2 | exact FR2 | exact (ie_got _ ENV2) | exact (ie_shb _ ENV2) | exact (ie_lay _ ENV2) | exact WR2 | exact RIMG | exact RSTK
              | exact KLO | exact APP2 | exact UNP2 | exact HR2 | exact RSH2 | reflexivity | lia ]. }
    cbv beta. intros ms3 PO3.
    destruct PO3 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    apply evtF_done. unfold fread_i_postM. cbn [fst snd].
    split; [reflexivity|]. split; [exact INV'|]. split; [exact GB|]. split; [exact GF|]. split; [exact GRB|].
    do 14 eexists. exists flags', mode', rp', bufbytes', rest', m3.
    split; [reflexivity|].
    split. { unfold fri_W, FREAD_I_DEPTH. apply (munch_trans _ m m1 m3).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - apply (munch_trans _ m1 m2 m3).
               + eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia.
               + eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
    split. { eapply (rw_cells_transport asegs _ m2 m3); [exact FC2 | exact MU3 | exact WM3 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    split; [exact FL2|].
    split. { eapply (rw_cells_transport asegs _ m2 m3); [exact BUF2 | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    split; [exact RR2|]. split; [exact RP21|]. split; [exact RP22|].
    split. { eapply (rw_cells_transport asegs _ m2 m3); [exact DST2 | exact MU3 | exact WM3 |].
             pose proof (rw_cells_bound _ _ _ _ DST2) as DB2. cbn [cells_size csize Nat.add] in DB2 |- *. cbn [disjoint_from]. lia. }
    destruct SSP2 as [G1 G2]. split; (eapply (rw_cells_transport asegs _ m2 m3); [eassumption | exact MU3 | exact WM3 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]).
  Qed.
  End Sz1.
  Theorem fread_i_spec : ltac:(let t := eval cbv delta [fread_i_spec__stmt] in fread_i_spec__stmt in exact t).
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO ENV IESF IESB IESD APWF SOB SOD RSTK RFP RBUF RD RIMG R0. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk. ltac2:(SecDiet.SzSec.closeP 'fread_i_spec__body "vvvvvvvvvvvvvvvvvvvv"). Qed.
End FreadI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FreadIMisc.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Hypothesis LO : lo <= bv_unsigned sp - FREAD_I_DEPTH.
  Hypothesis GLO : 0x603000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis ENV : icptenv m.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition fread_i_zero_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp wend wpos wbase wfn fd lbf D Dm : Z),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode lbf tail) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      0 <= wend < 2^64 -> 0 <= wpos < 2^64 -> 0 <= wbase < 2^64 -> 0 <= wfn < 2^64 -> 0 <= fd < 2^64 -> 0 <= lbf < 2^64 ->
      0 <= B -> B + bs < 2^64 -> 0 <= bs ->
      0 <= D < 2^64 ->
      stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      iesafe [(Fp, Fp + 232)] -> appW [(Fp, Fp + 232)] ->
      sobj RNG m B (B + bs) -> (f_rbuf f0 <> [] -> B <= rp /\ rp + zlength (f_rbuf f0) <= B + bs) -> (B + bs <= lo \/ bv_unsigned sp <= B) -> rng RNG B bs ->
      sobj RNG m D D -> (D <= lo \/ bv_unsigned sp <= D) -> rng RNG D 0 ->
      implAM RNG (fread_file f0 B Dm 0) st
        (fun r st' ms' => st' = st /\ r = ([], set_rbuf (f_rbuf f0) f0) /\
           exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
             ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (ret_pc ra) fc None m' (seg_rom asegs)
             /\ munch [(bv_unsigned sp - FREAD_I_DEPTH, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
             /\ stk asegs m' lo (bv_unsigned sp)
             /\ rw_cells asegs m' Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD_STUB) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm : ltac2:(SecDiet.SzSec.tyM 'fread_i_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_i_zero_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_i_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv").
  Proof using FPLO Fp0 LO SP47 KLO ENV RSTK RFP RIMG GLO. pin_using (fun (FPLO Fp0 LO SP47 KLO GLO : unit) => tt).
    intros FC RP0 RPHI W1 W2 W3 W4 W5 W6 B0 BHI BS0 HD ST MI IESF APWF SOB RRB SB1 RBUF SOD SD1 RD0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    unfold FREAD_STUB, FREAD_I_DEPTH in *.
    apply implAM_from_evt.
    pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zs.
    eapply evtF_cut.
    { eapply (fread_i_pre RNG); first [exact MI | exact ST | lia | exact KLO | exact (ie_ini _ ENV) | exact (ie_fread _ ENV) | exact RIMG | exact RSTK]. }
    cbv beta. intros ms1 MID.
    destruct MID as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1 & INI1).
    apply evtF_done.
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B (f_bufsize f0) prev next fd mode lbf tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOB1 : sobj RNG m1 B (B + f_bufsize f0)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | solve_appW]).
    assert (SOD1 : sobj RNG m1 D D) by (eapply sobj_transport; [exact SOD | exact MU1 | exact WM1 | solve_appW]).
    eapply implAM_post_evt.
    { eapply (fread_zero_spec (St:=St) RNG (Z_to_bv 64 0x46690) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp sp (Z_to_bv 64 1) (Z_to_bv 64 D) (Z_to_bv 64 Fp) (Z_to_bv 64 0) (Z_to_bv 64 1)
               s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail lo m1)
        with (flags := flags) (mode := mode) (rp := rp) (wend := wend) (wpos := wpos) (wbase := wbase) (wfn := wfn) (fd := fd) (lbf := lbf) (D := D) (Dm := Dm);
        rewrite ?unsigned_lit by lia;
        first [ exact FC1 | exact ST1 | exact MI1 | exact KLO | exact ENV1 | exact IESF | exact APWF | exact SOB1 | exact RRB | exact RBUF | exact SOD1 | exact RD0
              | exact RFP | exact RIMG | exact Fp0 | exact FPLO | eapply rng_sub'; [exact RSTK | lia] | lia ]. }
    cbv beta. intros r st' ms' (-> & -> & PO).
    destruct PO as (v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & mode' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2).
    rewrite ?unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x46690)) with (Z_to_bv 64 0x46690 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (STM2 : stk asegs m2 (bv_unsigned sp - 2128) (bv_unsigned sp - 56)).
    { eapply stk_transport_disjoint; [exact STM1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    assert (ENV2 : icptenv m2) by (eapply icptenv_transport; [exact ENV1 | exact MU2 | exact WM2 | solve_iesafe]).
    assert (SOD2 : sobj RNG m2 D D) by (eapply sobj_transport; [exact SOD1 | exact MU2 | exact WM2 | solve_appW]).
    destruct SOD2 as (APP2 & UNP2 & NSZ2 & RLO & RHI & HR2 & WR2 & RSH2).
    eapply evtF_cut.
    { eapply (fread_i_post RNG) with (lo := lo) (res := 0) (size := 1) (N := 0) (RLO := RLO) (RHI := RHI);
        rewrite ?unsigned_lit by lia; rewrite ?Z.add_0_r;
        first [ exact MI2 | exact ST2 | exact STM2 | exact FR2 | exact (ie_got _ ENV2) | exact (ie_shb _ ENV2) | exact (ie_lay _ ENV2) | exact WR2 | exact RIMG | exact RSTK
              | exact KLO | exact APP2 | exact UNP2 | exact HR2 | exact RSH2 | reflexivity | lia ]. }
    cbv beta. intros ms3 PO3.
    destruct PO3 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    apply evtF_done.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. exists mode', m3.
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m3).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - apply (munch_trans _ m1 m2 m3).
               + eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia.
               + eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
    eapply (rw_cells_transport asegs _ m2 m3); [exact FC2 | exact MU3 | exact WM3 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia.
  Qed.
  End Sz2.
  Theorem fread_i_zero_spec : ltac:(let t := eval cbv delta [fread_i_zero_spec__stmt] in fread_i_zero_spec__stmt in exact t).
  Proof using FPLO Fp0 LO SP47 KLO ENV RSTK RFP RIMG GLO. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm. ltac2:(SecDiet.SzSec.closeP 'fread_i_zero_spec__body "vvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis B0' : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.

  Definition fread_i_nord_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp D n : Z) (bufbytes : list byte),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn
                             (if f_wactive f0 then B + f_bufsize f0 else 0) (if f_wactive f0 then B + zlength (f_wbuf f0) else 0) (if f_wactive f0 then B else 0)
                             F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      Z.land (bv_unsigned flags) F_NORD = (if f_nord f0 then F_NORD else 0) ->
      Z.land (bv_unsigned flags) F_EOF = (if f_eof f0 then F_EOF else 0) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells asegs m B [CB (Z.to_nat bs) bufbytes] -> firstn (length (f_wbuf f0)) bufbytes = to_bytes (f_wbuf f0) ->
      (f_wactive f0 = false -> f_wbuf f0 = []) -> zlength (f_wbuf f0) <= bs ->
      f_rbuf f0 = [] -> f_nord f0 = true ->
      0 <= rp -> rp < 2^63 ->
      0 < n < 2^63 ->
      stk asegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv asegs m ->
      rng RNG B bs -> rng0 RNG ->
      implAM RNG (fread_file f0 B D n) st (fun _ _ _ => False)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD_STUB) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes : ltac2:(SecDiet.SzSec.tyM 'fread_i_nord_spec__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_i_nord_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_i_nord_spec__stmt "vvvvvvvvvvvvvvvvv").
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO ENV RSTK RFP RIMG. pin_using (fun (B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO : unit) => tt).
    intros FC FLN FLE FL64 BUF BUFP WB0 WBL RB NORD RP0 RPHI HN ST SSP MI RBUF R0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD_STUB, FREAD_I_DEPTH in *.
    apply implAM_from_evt.
    pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zs.
    eapply evtF_cut.
    { eapply (fread_i_pre RNG); first [exact MI | exact ST | lia | exact KLO | exact (ie_ini _ ENV) | exact (ie_fread _ ENV) | exact RIMG | exact RSTK]. }
    cbv beta. intros ms1 MID.
    destruct MID as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1 & INI1).
    apply evtF_done.
    eapply (fread_nord_spec (St:=St) RNG (Z_to_bv 64 0x46690) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp sp (Z_to_bv 64 1) (Z_to_bv 64 D) (Z_to_bv 64 Fp) (Z_to_bv 64 n) (Z_to_bv 64 1)
               s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail lo canary m1)
        with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes);
        rewrite ?unsigned_lit by lia;
        first [ exact FLN | exact FLE | exact FL64 | exact BUFP | exact WB0 | exact WBL | exact RB | exact NORD | exact ST1 | exact MI1 | exact RBUF | exact R0
              | exact KLO | exact RFP | exact RIMG | exact Fp0 | exact FPLO | exact FSEP1 | exact FSEP2 | exact NCH | exact FD | exact BS | exact B0' | exact B47 | exact SB2
              | exact GLO
              | (eapply (rw_cells_transport asegs _ m m1); [exact FC | exact MU1 | exact WM1 |]; unfold fcells; rewrite file_cells_size; cbn [disjoint_from]; lia)
              | (eapply (rw_cells_transport asegs _ m m1); [exact BUF | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia])
              | (split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]))
              | eapply rng_sub'; [exact RSTK | lia] | lia ].
  Qed.
  End Sz3.
  Theorem fread_i_nord_spec : ltac:(let t := eval cbv delta [fread_i_nord_spec__stmt] in fread_i_nord_spec__stmt in exact t).
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO ENV RSTK RFP RIMG. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes. ltac2:(SecDiet.SzSec.closeP 'fread_i_nord_spec__body "vvvvvvvvvvvvvvvvv"). Qed.
End FreadIMisc.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_fread_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fread_misc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FREAD_STUB : Z := 0x444f4.
Definition FREAD_I_DEPTH : Z := 4432.   (* [comment removed for export] *)

Section FreadI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (D n lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Definition fri_W : list (Z * Z) := [(bv_unsigned sp - FREAD_I_DEPTH, bv_unsigned sp); (Fp, Fp + 232); (B, B + bs); (D, D + n)].

  (* [comment removed for export] *)
  Definition fread_i_postM : (list Z * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ fr_inv f0 (snd r) /\ Z.of_nat (length (fst r)) <= n /\
      Forall (fun z => 0 <= z < 256) (fst r) /\ Forall (fun z => 0 <= z < 256) (f_rbuf (snd r)) /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (rp' : Z) (bufbytes' rest' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch fri_W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags' rp' (rp' + zlength (f_rbuf (snd r))) closefn 0 0 0 F_STDIO_READ (wfn_of (snd r)) seekfn B bs prev next (f_fd f0) mode' (lbf_of (snd r)) tail)
      /\ flags_ok (snd r) flags'
      /\ rw_cells asegs m' B [CB (Z.to_nat bs) bufbytes']
      /\ (f_rbuf (snd r) <> [] -> B <= rp' /\ rp' + zlength (f_rbuf (snd r)) <= B + bs
                                /\ firstn (length (f_rbuf (snd r))) (skipn (Z.to_nat (rp' - B)) bufbytes') = to_bytes (f_rbuf (snd r)))
      /\ 0 <= rp' /\ rp' + zlength (f_rbuf (snd r)) < 2^63
      /\ rw_cells asegs m' D [CB (length (fst r)) (to_bytes (fst r)); CB (Z.to_nat n - length (fst r)) rest']
      /\ ssp_cells m' canary.

  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis NB : 0 <= n <= 2^30.
  Hypothesis LO : lo <= bv_unsigned sp - FREAD_I_DEPTH.
  Hypothesis GLO : 0x604000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis DSEP1 : D + n <= got_ssp \/ got_ssp + 8 <= D.
  Hypothesis DSEP2 : D + n <= ssp_guard \/ ssp_guard + 8 <= D.
  Hypothesis B0 : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis D0 : 0 <= D.
  Hypothesis D47 : D + n <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.
  Hypothesis SD1 : D + n <= lo \/ bv_unsigned sp <= D.
  Hypothesis SD2 : D + n <= Fp \/ Fp + 232 <= D.
  Hypothesis SD3 : D + n <= B \/ B + bs <= D.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis ENV : icptenv m.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + bs)].
  Hypothesis IESD : iesafe [(D, D + n)].
  Hypothesis APWF : appW [(Fp, Fp + 232)].
  Hypothesis SOB : sobj RNG m B (B + bs).
  Hypothesis SOD : sobj RNG m D (D + n).
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B bs.
  Hypothesis RD : rng RNG D n.
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis R0 : rng0 RNG.

  Definition fread_i_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp : Z) (bufbytes djunk : list byte),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn 0 0 0 F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      flags_ok f0 flags ->
      rw_cells asegs m B [CB (Z.to_nat bs) bufbytes] ->
      (f_rbuf f0 <> [] -> B <= rp /\ rp + zlength (f_rbuf f0) <= B + bs /\ firstn (length (f_rbuf f0)) (skipn (Z.to_nat (rp - B)) bufbytes) = to_bytes (f_rbuf f0)) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      rw_cells asegs m D [CB (Z.to_nat n) djunk] ->
      f_wactive f0 = false -> f_wbuf f0 = [] -> Forall (fun z => 0 <= z < 256) (f_rbuf f0) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 Fp ->
      stk asegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv asegs m ->
      implAM RNG (fread_file f0 B D n) st fread_i_postM
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD_STUB) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk : ltac2:(SecDiet.SzSec.tyM 'fread_i_spec__stmt "vvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_i_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_i_spec__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO ENV IESF IESB IESD APWF SOB SOD RSTK RFP RBUF RD RIMG R0. pin_using (fun (B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO : unit) => tt).
    intros FC FL BUF RREL RP0 RPHI DST WACT WB0 RBR -> -> -> -> ST SSP MI.
    pose proof (sobj_appW _ _ _ _ SOB) as APWB. pose proof (sobj_appW _ _ _ _ SOD) as APWD.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD_STUB, FREAD_I_DEPTH in *.
    apply implAM_from_evt.
    pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zs. (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fread_i_pre RNG); first [exact MI | exact ST | lia | exact KLO | exact (ie_ini _ ENV) | exact (ie_fread _ ENV) | exact RIMG | exact RSTK]. }
    cbv beta. intros ms1 MID.
    destruct MID as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1 & INI1).
    apply evtF_done.
    (* [comment removed for export] *)
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn 0 0 0 F_STDIO_READ (wfn_of f0) seekfn B (f_bufsize f0) prev next (f_fd f0) mode (lbf_of f0) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 B [CB (Z.to_nat (f_bufsize f0)) bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (DST1 : rw_cells asegs m1 D [CB (Z.to_nat n) djunk]).
    { eapply (rw_cells_transport asegs _ m m1); [exact DST | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOB1 : sobj RNG m1 B (B + f_bufsize f0)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | solve_appW]).
    assert (SOD1 : sobj RNG m1 D (D + n)) by (eapply sobj_transport; [exact SOD | exact MU1 | exact WM1 | solve_appW]).
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (fread_spec (St:=St) RNG (Z_to_bv 64 0x466f8) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp sp (Z_to_bv 64 1) (Z_to_bv 64 D) (Z_to_bv 64 Fp) (Z_to_bv 64 n) (Z_to_bv 64 1)
               s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail D n lo canary m1)
        with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes) (djunk := djunk);
        rewrite ?unsigned_lit by lia; unfold FREAD_DEPTH;
        first [ exact FC1 | exact FL | exact BUF1 | exact RREL | exact DST1 | exact WACT | exact WB0 | exact RBR | exact ST1 | exact SSP1 | exact MI1
              | exact NCH | exact FD | exact BS | exact NB | exact GLO | exact Fp0 | exact FPLO | exact FSEP1 | exact FSEP2 | exact BSEP1 | exact BSEP2
              | exact DSEP1 | exact DSEP2 | exact B0 | exact B47 | exact D0 | exact D47 | exact SB2 | exact SD2 | exact SD3
              | exact KLO | exact ENV1 | exact IESF | exact IESB | exact IESD | exact APWF | exact SOB1 | exact SOD1 | exact RFP | exact RBUF | exact RD | exact RIMG | exact R0
              | reflexivity | eapply rng_sub'; [exact RSTK | lia] | lia ]. }
    cbv beta. intros [got f'] st' ms' (-> & INV' & GB & GF & GRB & PO). cbn [fst snd] in INV', GB, GF, GRB, PO |- *.
    destruct PO as (v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & flags' & mode' & rp' & bufbytes' & rest' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & FL2 & BUF2 & RR2 & RP21 & RP22 & DST2 & SSP2).
    unfold fr_W, FREAD_DEPTH in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x466f8)) with (Z_to_bv 64 0x466f8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof INV' as (I1 & I2 & I3 & I4 & I5 & I6 & I7). rewrite ?I3 in *.
    (* [comment removed for export] *)
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (STM2 : stk asegs m2 (bv_unsigned sp - 2128) (bv_unsigned sp - 56)).
    { eapply stk_transport_disjoint; [exact STM1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    assert (ENV2 : icptenv m2) by (eapply icptenv_transport; [exact ENV1 | exact MU2 | exact WM2 | solve_iesafe]).
    assert (SOD2 : sobj RNG m2 D (D + n)) by (eapply sobj_transport; [exact SOD1 | exact MU2 | exact WM2 | solve_appW]).
    assert (LG : 0 <= zlength got <= n) by (unfold zlength; lia).
    destruct (sobj_sub _ _ _ _ D (D + zlength got) SOD2 ltac:(lia) ltac:(lia) ltac:(lia)) as (APP2 & UNP2 & NSZ2 & RLO & RHI & HR2 & WR2 & RSH2).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fread_i_post RNG) with (lo := lo) (res := zlength got) (size := 1) (N := zlength got) (RLO := RLO) (RHI := RHI);
        rewrite ?unsigned_lit by lia;
        first [ exact MI2 | exact ST2 | exact STM2 | exact FR2 | exact (ie_got _ ENV2) | exact (ie_shb _ ENV2) | exact (ie_lay _ ENV2) | exact WR2 | exact RIMG | exact RSTK
              | exact KLO | exact APP2 | exact UNP2 | exact HR2 | exact RSH2 | reflexivity | lia ]. }
    cbv beta. intros ms3 PO3.
    destruct PO3 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    apply evtF_done. unfold fread_i_postM. cbn [fst snd].
    split; [reflexivity|]. split; [exact INV'|]. split; [exact GB|]. split; [exact GF|]. split; [exact GRB|].
    do 14 eexists. exists flags', mode', rp', bufbytes', rest', m3.
    split; [reflexivity|].
    split. { unfold fri_W, FREAD_I_DEPTH. apply (munch_trans _ m m1 m3).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - apply (munch_trans _ m1 m2 m3).
               + eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia.
               + eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
    split. { eapply (rw_cells_transport asegs _ m2 m3); [exact FC2 | exact MU3 | exact WM3 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    split; [exact FL2|].
    split. { eapply (rw_cells_transport asegs _ m2 m3); [exact BUF2 | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    split; [exact RR2|]. split; [exact RP21|]. split; [exact RP22|].
    split. { eapply (rw_cells_transport asegs _ m2 m3); [exact DST2 | exact MU3 | exact WM3 |].
             pose proof (rw_cells_bound _ _ _ _ DST2) as DB2. cbn [cells_size csize Nat.add] in DB2 |- *. cbn [disjoint_from]. lia. }
    destruct SSP2 as [G1 G2]. split; (eapply (rw_cells_transport asegs _ m2 m3); [eassumption | exact MU3 | exact WM3 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]).
  Qed.
  End Sz1.
  Theorem fread_i_spec : ltac:(let t := eval cbv delta [fread_i_spec__stmt] in fread_i_spec__stmt in exact t).
  Proof using B0 B47 BS BSEP1 BSEP2 D0 D47 DSEP1 DSEP2 FD FPLO FSEP1 FSEP2 Fp0 GLO LO NB NCH SB1 SB2 SD1 SD2 SD3 SP47 KLO ENV IESF IESB IESD APWF SOB SOD RSTK RFP RBUF RD RIMG R0. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp bufbytes djunk. ltac2:(SecDiet.SzSec.closeP 'fread_i_spec__body "vvvvvvvvvvvvvvvvvvvv"). Qed.
End FreadI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FreadIMisc.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Hypothesis LO : lo <= bv_unsigned sp - FREAD_I_DEPTH.
  Hypothesis GLO : 0x604000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis ENV : icptenv m.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition fread_i_zero_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp wend wpos wbase wfn fd lbf D Dm : Z),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode lbf tail) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      0 <= wend < 2^64 -> 0 <= wpos < 2^64 -> 0 <= wbase < 2^64 -> 0 <= wfn < 2^64 -> 0 <= fd < 2^64 -> 0 <= lbf < 2^64 ->
      0 <= B -> B + bs < 2^64 -> 0 <= bs ->
      0 <= D < 2^64 ->
      stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      iesafe [(Fp, Fp + 232)] -> appW [(Fp, Fp + 232)] ->
      sobj RNG m B (B + bs) -> (f_rbuf f0 <> [] -> B <= rp /\ rp + zlength (f_rbuf f0) <= B + bs) -> (B + bs <= lo \/ bv_unsigned sp <= B) -> rng RNG B bs ->
      sobj RNG m D D -> (D <= lo \/ bv_unsigned sp <= D) -> rng RNG D 0 ->
      implAM RNG (fread_file f0 B Dm 0) st
        (fun r st' ms' => st' = st /\ r = ([], set_rbuf (f_rbuf f0) f0) /\
           exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
             ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (ret_pc ra) fc None m' (seg_rom asegs)
             /\ munch [(bv_unsigned sp - FREAD_I_DEPTH, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
             /\ stk asegs m' lo (bv_unsigned sp)
             /\ rw_cells asegs m' Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD_STUB) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm : ltac2:(SecDiet.SzSec.tyM 'fread_i_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_i_zero_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_i_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv").
  Proof using FPLO Fp0 LO SP47 KLO ENV RSTK RFP RIMG GLO. pin_using (fun (FPLO Fp0 LO SP47 KLO GLO : unit) => tt).
    intros FC RP0 RPHI W1 W2 W3 W4 W5 W6 B0 BHI BS0 HD ST MI IESF APWF SOB RRB SB1 RBUF SOD SD1 RD0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    unfold FREAD_STUB, FREAD_I_DEPTH in *.
    apply implAM_from_evt.
    pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zs.
    eapply evtF_cut.
    { eapply (fread_i_pre RNG); first [exact MI | exact ST | lia | exact KLO | exact (ie_ini _ ENV) | exact (ie_fread _ ENV) | exact RIMG | exact RSTK]. }
    cbv beta. intros ms1 MID.
    destruct MID as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1 & INI1).
    apply evtF_done.
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B (f_bufsize f0) prev next fd mode lbf tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOB1 : sobj RNG m1 B (B + f_bufsize f0)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | solve_appW]).
    assert (SOD1 : sobj RNG m1 D D) by (eapply sobj_transport; [exact SOD | exact MU1 | exact WM1 | solve_appW]).
    eapply implAM_post_evt.
    { eapply (fread_zero_spec (St:=St) RNG (Z_to_bv 64 0x466f8) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp sp (Z_to_bv 64 1) (Z_to_bv 64 D) (Z_to_bv 64 Fp) (Z_to_bv 64 0) (Z_to_bv 64 1)
               s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail lo m1)
        with (flags := flags) (mode := mode) (rp := rp) (wend := wend) (wpos := wpos) (wbase := wbase) (wfn := wfn) (fd := fd) (lbf := lbf) (D := D) (Dm := Dm);
        rewrite ?unsigned_lit by lia;
        first [ exact FC1 | exact ST1 | exact MI1 | exact KLO | exact ENV1 | exact IESF | exact APWF | exact SOB1 | exact RRB | exact RBUF | exact SOD1 | exact RD0
              | exact RFP | exact RIMG | exact Fp0 | exact FPLO | eapply rng_sub'; [exact RSTK | lia] | lia ]. }
    cbv beta. intros r st' ms' (-> & -> & PO).
    destruct PO as (v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & mode' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2).
    rewrite ?unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x466f8)) with (Z_to_bv 64 0x466f8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (STM2 : stk asegs m2 (bv_unsigned sp - 2128) (bv_unsigned sp - 56)).
    { eapply stk_transport_disjoint; [exact STM1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    assert (ENV2 : icptenv m2) by (eapply icptenv_transport; [exact ENV1 | exact MU2 | exact WM2 | solve_iesafe]).
    assert (SOD2 : sobj RNG m2 D D) by (eapply sobj_transport; [exact SOD1 | exact MU2 | exact WM2 | solve_appW]).
    destruct SOD2 as (APP2 & UNP2 & NSZ2 & RLO & RHI & HR2 & WR2 & RSH2).
    eapply evtF_cut.
    { eapply (fread_i_post RNG) with (lo := lo) (res := 0) (size := 1) (N := 0) (RLO := RLO) (RHI := RHI);
        rewrite ?unsigned_lit by lia; rewrite ?Z.add_0_r;
        first [ exact MI2 | exact ST2 | exact STM2 | exact FR2 | exact (ie_got _ ENV2) | exact (ie_shb _ ENV2) | exact (ie_lay _ ENV2) | exact WR2 | exact RIMG | exact RSTK
              | exact KLO | exact APP2 | exact UNP2 | exact HR2 | exact RSH2 | reflexivity | lia ]. }
    cbv beta. intros ms3 PO3.
    destruct PO3 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    apply evtF_done.
    split; [reflexivity|]. split; [reflexivity|].
    do 14 eexists. exists mode', m3.
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m3).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - apply (munch_trans _ m1 m2 m3).
               + eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia.
               + eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
    eapply (rw_cells_transport asegs _ m2 m3); [exact FC2 | exact MU3 | exact WM3 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia.
  Qed.
  End Sz2.
  Theorem fread_i_zero_spec : ltac:(let t := eval cbv delta [fread_i_zero_spec__stmt] in fread_i_zero_spec__stmt in exact t).
  Proof using FPLO Fp0 LO SP47 KLO ENV RSTK RFP RIMG GLO. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm. ltac2:(SecDiet.SzSec.closeP 'fread_i_zero_spec__body "vvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis B0' : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.

  Definition fread_i_nord_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp D n : Z) (bufbytes : list byte),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn
                             (if f_wactive f0 then B + f_bufsize f0 else 0) (if f_wactive f0 then B + zlength (f_wbuf f0) else 0) (if f_wactive f0 then B else 0)
                             F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      Z.land (bv_unsigned flags) F_NORD = (if f_nord f0 then F_NORD else 0) ->
      Z.land (bv_unsigned flags) F_EOF = (if f_eof f0 then F_EOF else 0) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells asegs m B [CB (Z.to_nat bs) bufbytes] -> firstn (length (f_wbuf f0)) bufbytes = to_bytes (f_wbuf f0) ->
      (f_wactive f0 = false -> f_wbuf f0 = []) -> zlength (f_wbuf f0) <= bs ->
      f_rbuf f0 = [] -> f_nord f0 = true ->
      0 <= rp -> rp < 2^63 ->
      0 < n < 2^63 ->
      stk asegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv asegs m ->
      rng RNG B bs -> rng0 RNG ->
      implAM RNG (fread_file f0 B D n) st (fun _ _ _ => False)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD_STUB) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes : ltac2:(SecDiet.SzSec.tyM 'fread_i_nord_spec__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_i_nord_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_i_nord_spec__stmt "vvvvvvvvvvvvvvvvv").
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO ENV RSTK RFP RIMG. pin_using (fun (B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO : unit) => tt).
    intros FC FLN FLE FL64 BUF BUFP WB0 WBL RB NORD RP0 RPHI HN ST SSP MI RBUF R0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD_STUB, FREAD_I_DEPTH in *.
    apply implAM_from_evt.
    pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zs.
    eapply evtF_cut.
    { eapply (fread_i_pre RNG); first [exact MI | exact ST | lia | exact KLO | exact (ie_ini _ ENV) | exact (ie_fread _ ENV) | exact RIMG | exact RSTK]. }
    cbv beta. intros ms1 MID.
    destruct MID as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1 & INI1).
    apply evtF_done.
    eapply (fread_nord_spec (St:=St) RNG (Z_to_bv 64 0x466f8) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp sp (Z_to_bv 64 1) (Z_to_bv 64 D) (Z_to_bv 64 Fp) (Z_to_bv 64 n) (Z_to_bv 64 1)
               s6 s7 s8 s9 s10 s11 F fc f0 st Fp closefn seekfn B prev next tail lo canary m1)
        with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes);
        rewrite ?unsigned_lit by lia;
        first [ exact FLN | exact FLE | exact FL64 | exact BUFP | exact WB0 | exact WBL | exact RB | exact NORD | exact ST1 | exact MI1 | exact RBUF | exact R0
              | exact KLO | exact RFP | exact RIMG | exact Fp0 | exact FPLO | exact FSEP1 | exact FSEP2 | exact NCH | exact FD | exact BS | exact B0' | exact B47 | exact SB2
              | exact GLO
              | (eapply (rw_cells_transport asegs _ m m1); [exact FC | exact MU1 | exact WM1 |]; unfold fcells; rewrite file_cells_size; cbn [disjoint_from]; lia)
              | (eapply (rw_cells_transport asegs _ m m1); [exact BUF | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia])
              | (split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]))
              | eapply rng_sub'; [exact RSTK | lia] | lia ].
  Qed.
  End Sz3.
  Theorem fread_i_nord_spec : ltac:(let t := eval cbv delta [fread_i_nord_spec__stmt] in fread_i_nord_spec__stmt in exact t).
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO ENV RSTK RFP RIMG. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes. ltac2:(SecDiet.SzSec.closeP 'fread_i_nord_spec__body "vvvvvvvvvvvvvvvvv"). Qed.
End FreadIMisc.
End TwB.
End I_fread_top.

(* [comment removed for export] *)
Module Printf_fsink.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr SysStep ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AProto. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require MonadX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_read__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface F_printf_core_common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma zb_to_bytes : forall l, zb l = to_bytes l.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land32_lowbyte : forall x, 0 <= x -> Z.land x 32 = 0 -> Z.land (x mod 256) 32 = 0.
Proof.
  intros x Hx H. change 256 with (2^8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm x (Z.ones 8)), <- Z.land_assoc, H. apply Z.land_0_r.
Qed.

Section FileSink.
  Context {St : Type}.
  (* [comment removed for export] *)
  Variables (Fp B bs : Z) (rpos rend closefn readfn seekfn prev next : Z) (tail : list byte).
  (* [comment removed for export] *)
  Variable sw0 : bool.
  (* [comment removed for export] *)
  Variable ch0 : bool.
  (* [comment removed for export] *)
  Variable st0 : St.

  (* [comment removed for export] *)
  Definition fsink_inv (f : file_st) : Prop :=
    f_wactive f = true /\ f_rbuf f = [] /\ f_bufsize f = bs /\ f_nowr f = false
    /\ (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31))
    /\ (f_stdoutw f = true -> sw0 = true) /\ f_chan f = ch0.

  Definition SINK_file (m : mem) (fs : file_st * St) : Prop :=
    let f := fst fs in
    snd fs = st0 /\ fsink_inv f /\
    exists (flags mode : word) (bufbytes : list byte),
      rw_cells asegs m Fp (fcells flags rpos rend closefn (B + bs) (B + zlength (f_wbuf f)) B readfn (wfn_of f) seekfn B bs prev next (f_fd f) mode (lbf_of f) tail)
      /\ flags_ok f flags
      /\ rw_cells asegs m B [CB (Z.to_nat bs) bufbytes]
      /\ firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f)
      /\ zlength (f_wbuf f) <= bs.

  (* [comment removed for export] *)
  Definition TOPOK_file (sp : Z) : Prop := True.

  (* [comment removed for export] *)
  Definition PIECE_MAX : Z := 2^26 - 1024.
  Definition OUT_file (s : list Z) : M (file_st * St) unit :=
    fun fs => if zlength s <=? PIECE_MAX
              then ebind (fwritex (fst fs) s (snd fs)) (fun r => ITree.Ret (Ok (tt, (fst r, snd r))))
              else ITree.Ret Unr.

  (* [comment removed for export] *)
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis B0 : 0 < B.
  Hypothesis BS0 : 0 <= bs <= 1024.
  Hypothesis BShi : B + bs <= 2^47.   (* [comment removed for export] *)
  Hypothesis Fphi : Fp + 232 < 2^63.
  Hypothesis FB : B + bs <= Fp \/ Fp + 232 <= B.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis TL : firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8.
  (* [comment removed for export] *)
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + bs)].

  Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
    Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
  Proof using BS0 BSEP1 BSEP2 FB FSEP1 FSEP2. pin_using (fun (BS0 BSEP1 BSEP2 FB FSEP1 FSEP2 : unit) => tt).
    intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
  Qed.

  Lemma file_sink_frame : sink_frame_stmt Fp 232 B bs SINK_file.
  Proof using BS0 BSEP1 BSEP2 FB FSEP1 FSEP2. pin_using (fun (BS0 BSEP1 BSEP2 FB FSEP1 FSEP2 : unit) => tt).
    unfold sink_frame_stmt. intros W m m' [f st] (EST & INV & flags & mode & bufbytes & FC & FL & BUF & BP & WBL) MU WM D1 D2. cbn [fst snd] in *.
    split; [exact EST|]. split; [exact INV|]. exists flags, mode, bufbytes.
    split. { eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. unfold fcells. rewrite file_cells_size.
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split; [exact FL|].
    split. { eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D2 | lia | cbn; lia | cbn; lia]. }
    split; [exact BP | exact WBL].
  Qed.

  Lemma file_sink_flags : sink_flags_stmt Fp SINK_file.
  Proof using Fp0 Fphi. pin_using (fun (Fp0 Fphi : unit) => tt).
    unfold sink_flags_stmt. intros m [f st] (EST & INV & flags & mode & bufbytes & FC & FL & _). cbn [fst snd] in *.
    exists (Z_to_bv 8 (bv_unsigned flags)).
    pose proof (bv_unsigned_in_range 64 flags) as FR. unfold bv_modulus in FR.
    split.
    - unfold fcells, file_cells in FC. apply (proj1 (rw_cells_app asegs m Fp [C4 flags] _)) in FC. destruct FC as [FC _].
      destruct FC as [[WF BY] WR]. split; [split|].
      + cbn. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes] in BY |- *. rewrite app_nil_r in BY |- *.
        change (le4 flags) with ([Z_to_bv 8 (bv_unsigned flags)] ++ Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8)) in BY.
        apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [BY _]. exact BY.
      + cbn [cells_size csize Nat.add] in WR |- *. destruct WR as (A1 & A2 & A3). split; [lia|]. split; [lia|]. intros i Hi. apply A3. lia.
    - rewrite Z_to_bv_unsigned. change (2 ^ Z.of_N 8) with 256. apply land32_lowbyte; [lia|].
      destruct FL as (_ & _ & _ & FE & _). exact FE.
  Qed.

  Lemma file_topok : topok_stmt TOPOK_file.
  Proof using Type. pin_using tt. unfold topok_stmt, TOPOK_file. intros; exact I. Qed.

  (* [comment removed for export] *)
  Lemma fsink_inv_fx : forall f f', fsink_inv f -> fx_inv f f' -> fsink_inv f'.
  Proof using Type. pin_using tt.
    intros f f' (WA & RB & BS & NW & CH & SWB & CHN) (E1 & E2 & E3 & E4 & E5 & E6 & WA' & RB' & SW & LB).
    unfold fsink_inv. rewrite E1, E2, E3, E5, WA', RB', WA, RB. repeat split; auto.
  Qed.
  Lemma flags_ok_fx : forall f f' flags, fx_inv f f' -> flags_ok f flags -> flags_ok f' flags.
  Proof using Type. pin_using tt.
    intros f f' flags (E1 & E2 & E3 & E4 & E5 & E6 & _) FL. unfold flags_ok in *. rewrite E2, E4, E5, E6. exact FL.
  Qed.

  (* [comment removed for export] *)
  Lemma file_out : out_stmtA Fp 232 Fp B bs SINK_file TOPOK_file OUT_file.
  Proof using B0 BS0 BSEP1 BSEP2 BShi FB FSEP1 FSEP2 Fp0 IESF IESB. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi FB FSEP1 FSEP2 Fp0 : unit) => tt).
    unfold out_stmt. intros until canary. intros HS SRC BYT LB -> -> ST LO GLO SPHI S47 TQ SSP MI D1 D2 D3 D4 D5
           KH ENV SOS SOF SOB RGSTK RGIMG RGS RGF RGB.
    pose proof (sobj_appW _ _ _ _ SOF) as APF. pose proof (sobj_appW _ _ _ _ SOB) as APB.
    destruct st as [f st']. destruct HS as (EST & INV & flags & mode & bufbytes & FC & FL & BUF & BP & WBL). cbn [fst snd] in *.
    pose proof INV as (WA & RB & BSZ & NW & CH & SWB & CHN).
    unfold OUT_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. cbn in A0R.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite zb_length in SB.
    set (S := bv_unsigned a0) in *.
    assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm). rewrite NW in FLw.
    unfold implXM, OUT_file. cbn [fst snd].
    destruct (zlength bs0 <=? PIECE_MAX) eqn:SMALL.
    2:{ apply implF_ret_unr. }
    apply Z.leb_le in SMALL. unfold PIECE_MAX in SMALL.
    eapply implF_ebind.
    { pose proof (fwritex_spec (St:=St) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (zlength bs0)) (Z_to_bv 64 Fp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc m st' f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes bs0 S lo canary) as FX.
      unfold implAM in FX. rewrite WA, BSZ in FX. apply FX; clear FX;
        rewrite ?zb_to_bytes in *; unfold FWRITEX_DEPTH, zlength in *;
        fastfirst (first [ noevar_assumption | exact FC | exact BUF | exact BP | exact SRC | exact BYT | exact EA0 | reflexivity | exact CH | exact ST | exact SSP | exact MI
              | exact FLsvb | exact FLw
              | intros X; rewrite X in WA; discriminate
              | lia | exact KH | exact ENV | exact IESF | exact IESB | exact APF | exact APB | exact SOS | exact SOB | exact RGSTK | exact RGF | exact RGB | exact RGS | exact RGIMG
              | match goal with |- ?g => idtac "FILEOUT-PREM:" g end; fail ]). }
    cbv beta. intros [f' st''] RNG' ms' [-> PO]. cbn [fst snd] in PO |- *.
    unfold fwritex_post in PO.
    destruct PO as (-> & FXI & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP').
    apply implF_ret_ok. apply evtF_done. unfold postF. cbn [fst snd]. split; [reflexivity|]. unfold out_post, SR.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, fx_W; cbn [outside]. rewrite BSZ. intros; lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    { (* [comment removed for export] *)
      split; [cbn [snd]; congruence|]. split; [exact (fsink_inv_fx f f' INV FXI)|].
      pose proof FXI as (E1 & E2 & E3 & E4 & E5 & E6 & WA' & RB' & SW & LBI).
      cbn [fst snd]. exists flags, mode', bufbytes'. rewrite ?E1, ?BSZ. rewrite ?WA, ?BSZ in FC'. rewrite ?BSZ in BUF'. rewrite ?BSZ in WBL'.
      split; [exact FC'|]. split; [exact (flags_ok_fx f f' flags FXI FL)|]. split; [exact BUF'|]. split; [exact BP'| exact WBL']. }
    split; [exact SSP'|].
    (* [comment removed for export] *)
    eapply bytes_at_transport; [exact SRC | exact MU |].
    unfold fx_W. rewrite zb_length, BSZ. cbn [disjoint_from]. unfold zlength in *. lia.
  Qed.
End FileSink.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Bridge.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition pieces_small (ps : list (list Z)) : Prop := Forall (fun p => zlength p <= PIECE_MAX) ps.

  Lemma out_pieces_bridgeF : forall ps (f : file_st) (st : St) (r : Z) RNG (Q : Z * (file_st * St) -> footprint -> machine_state -> Prop) ms,
    pieces_small ps ->
    implS asegs RNG (outsk OUT_file ps (mret r) (f, st)) (epostF Q) ms ->
    implS asegs RNG (out_pieces f ps st) (epostF (fun p RNG' ms' => Q (r, (fst p, snd p)) RNG' ms')) ms.
  Proof using Type. pin_using tt.
    induction ps as [|p ps IH]; intros f st r RNG Q ms SM H; cbn [outsk out_pieces] in *.
    - exact H.
    - apply Forall_cons_iff in SM. destruct SM as [SM1 SM2].
      unfold mbind, OUT_file, ebind in *. cbn [fst snd] in H.
      replace (zlength p <=? PIECE_MAX) with true in H by (symmetry; apply Z.leb_le; exact SM1).
      apply (implF_bind_assoc_rev asegs) in H.
      eapply (implF_bind_ext2 asegs _ _ _ _ _ (fun _ => True)); [apply tforall_true | | exact H].
      cbv beta. intros [|[f1 st1]] RNG' ms1 _ H1; cbn [ITree.bind fst snd] in H1 |- *.
      + exact H1.
      + apply IH; [exact SM2 | exact H1].
  Qed.

  (* [comment removed for export] *)
  Lemma out_pieces_bridge : forall ps (f : file_st) (st : St) (r : Z) RNG (Q : Z -> file_st * St -> machine_state -> Prop) ms,
    pieces_small ps ->
    implAM RNG (outsk OUT_file ps (mret r)) (f, st) Q ms ->
    implAM RNG (out_pieces f ps) st (fun f' st' ms' => Q r (f', st') ms') ms.
  Proof using Type. pin_using tt.
    intros ps f st r RNG Q ms SM H. unfold implAM in *.
    eapply implF_mono; [apply (out_pieces_bridgeF ps f st r RNG _ ms SM H)|].
    intros [|[f1 st1]] RNG' ms'; cbn; [exact (fun x => x)|]. unfold postF. cbn [fst snd]. exact (fun x => x).
  Qed.
End Bridge.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma zb_to_bytes : forall l, zb l = to_bytes l.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land32_lowbyte : forall x, 0 <= x -> Z.land x 32 = 0 -> Z.land (x mod 256) 32 = 0.
Proof.
  intros x Hx H. change 256 with (2^8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm x (Z.ones 8)), <- Z.land_assoc, H. apply Z.land_0_r.
Qed.

Section FileSink.
  Context {St : Type}.
  (* [comment removed for export] *)
  Variables (Fp B bs : Z) (rpos rend closefn readfn seekfn prev next : Z) (tail : list byte).
  (* [comment removed for export] *)
  Variable sw0 : bool.
  (* [comment removed for export] *)
  Variable ch0 : bool.
  (* [comment removed for export] *)
  Variable st0 : St.

  (* [comment removed for export] *)
  Definition fsink_inv (f : file_st) : Prop :=
    f_wactive f = true /\ f_rbuf f = [] /\ f_bufsize f = bs /\ f_nowr f = false
    /\ (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31))
    /\ (f_stdoutw f = true -> sw0 = true) /\ f_chan f = ch0.

  Definition SINK_file (m : mem) (fs : file_st * St) : Prop :=
    let f := fst fs in
    snd fs = st0 /\ fsink_inv f /\
    exists (flags mode : word) (bufbytes : list byte),
      rw_cells asegs m Fp (fcells flags rpos rend closefn (B + bs) (B + zlength (f_wbuf f)) B readfn (wfn_of f) seekfn B bs prev next (f_fd f) mode (lbf_of f) tail)
      /\ flags_ok f flags
      /\ rw_cells asegs m B [CB (Z.to_nat bs) bufbytes]
      /\ firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f)
      /\ zlength (f_wbuf f) <= bs.

  (* [comment removed for export] *)
  Definition TOPOK_file (sp : Z) : Prop := True.

  (* [comment removed for export] *)
  Definition PIECE_MAX : Z := 2^26 - 1024.
  Definition OUT_file (s : list Z) : M (file_st * St) unit :=
    fun fs => if zlength s <=? PIECE_MAX
              then ebind (fwritex (fst fs) s (snd fs)) (fun r => ITree.Ret (Ok (tt, (fst r, snd r))))
              else ITree.Ret Unr.

  (* [comment removed for export] *)
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis B0 : 0 < B.
  Hypothesis BS0 : 0 <= bs <= 1024.
  Hypothesis BShi : B + bs <= 2^47.   (* [comment removed for export] *)
  Hypothesis Fphi : Fp + 232 < 2^63.
  Hypothesis FB : B + bs <= Fp \/ Fp + 232 <= B.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis TL : firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8.
  (* [comment removed for export] *)
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + bs)].

  Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
    Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
  Proof using BS0 BSEP1 BSEP2 FB FSEP1 FSEP2. pin_using (fun (BS0 BSEP1 BSEP2 FB FSEP1 FSEP2 : unit) => tt).
    intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
  Qed.

  Lemma file_sink_frame : sink_frame_stmt Fp 232 B bs SINK_file.
  Proof using BS0 BSEP1 BSEP2 FB FSEP1 FSEP2. pin_using (fun (BS0 BSEP1 BSEP2 FB FSEP1 FSEP2 : unit) => tt).
    unfold sink_frame_stmt. intros W m m' [f st] (EST & INV & flags & mode & bufbytes & FC & FL & BUF & BP & WBL) MU WM D1 D2. cbn [fst snd] in *.
    split; [exact EST|]. split; [exact INV|]. exists flags, mode, bufbytes.
    split. { eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. unfold fcells. rewrite file_cells_size.
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split; [exact FL|].
    split. { eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D2 | lia | cbn; lia | cbn; lia]. }
    split; [exact BP | exact WBL].
  Qed.

  Lemma file_sink_flags : sink_flags_stmt Fp SINK_file.
  Proof using Fp0 Fphi. pin_using (fun (Fp0 Fphi : unit) => tt).
    unfold sink_flags_stmt. intros m [f st] (EST & INV & flags & mode & bufbytes & FC & FL & _). cbn [fst snd] in *.
    exists (Z_to_bv 8 (bv_unsigned flags)).
    pose proof (bv_unsigned_in_range 64 flags) as FR. unfold bv_modulus in FR.
    split.
    - unfold fcells, file_cells in FC. apply (proj1 (rw_cells_app asegs m Fp [C4 flags] _)) in FC. destruct FC as [FC _].
      destruct FC as [[WF BY] WR]. split; [split|].
      + cbn. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes] in BY |- *. rewrite app_nil_r in BY |- *.
        change (le4 flags) with ([Z_to_bv 8 (bv_unsigned flags)] ++ Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8)) in BY.
        apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [BY _]. exact BY.
      + cbn [cells_size csize Nat.add] in WR |- *. destruct WR as (A1 & A2 & A3). split; [lia|]. split; [lia|]. intros i Hi. apply A3. lia.
    - rewrite Z_to_bv_unsigned. change (2 ^ Z.of_N 8) with 256. apply land32_lowbyte; [lia|].
      destruct FL as (_ & _ & _ & FE & _). exact FE.
  Qed.

  Lemma file_topok : topok_stmt TOPOK_file.
  Proof using Type. pin_using tt. unfold topok_stmt, TOPOK_file. intros; exact I. Qed.

  (* [comment removed for export] *)
  Lemma fsink_inv_fx : forall f f', fsink_inv f -> fx_inv f f' -> fsink_inv f'.
  Proof using Type. pin_using tt.
    intros f f' (WA & RB & BS & NW & CH & SWB & CHN) (E1 & E2 & E3 & E4 & E5 & E6 & WA' & RB' & SW & LB).
    unfold fsink_inv. rewrite E1, E2, E3, E5, WA', RB', WA, RB. repeat split; auto.
  Qed.
  Lemma flags_ok_fx : forall f f' flags, fx_inv f f' -> flags_ok f flags -> flags_ok f' flags.
  Proof using Type. pin_using tt.
    intros f f' flags (E1 & E2 & E3 & E4 & E5 & E6 & _) FL. unfold flags_ok in *. rewrite E2, E4, E5, E6. exact FL.
  Qed.

  (* [comment removed for export] *)
  Lemma file_out : out_stmtA Fp 232 Fp B bs SINK_file TOPOK_file OUT_file.
  Proof using B0 BS0 BSEP1 BSEP2 BShi FB FSEP1 FSEP2 Fp0 IESF IESB. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi FB FSEP1 FSEP2 Fp0 : unit) => tt).
    unfold out_stmt. intros until canary. intros HS SRC BYT LB -> -> ST LO GLO SPHI S47 TQ SSP MI D1 D2 D3 D4 D5
           KH ENV SOS SOF SOB RGSTK RGIMG RGS RGF RGB.
    pose proof (sobj_appW _ _ _ _ SOF) as APF. pose proof (sobj_appW _ _ _ _ SOB) as APB.
    destruct st as [f st']. destruct HS as (EST & INV & flags & mode & bufbytes & FC & FL & BUF & BP & WBL). cbn [fst snd] in *.
    pose proof INV as (WA & RB & BSZ & NW & CH & SWB & CHN).
    unfold OUT_DEPTH, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. cbn in A0R.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite zb_length in SB.
    set (S := bv_unsigned a0) in *.
    assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm). rewrite NW in FLw.
    unfold implXM, OUT_file. cbn [fst snd].
    destruct (zlength bs0 <=? PIECE_MAX) eqn:SMALL.
    2:{ apply implF_ret_unr. }
    apply Z.leb_le in SMALL. unfold PIECE_MAX in SMALL.
    eapply implF_ebind.
    { pose proof (fwritex_spec (St:=St) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (zlength bs0)) (Z_to_bv 64 Fp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc m st' f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes bs0 S lo canary) as FX.
      unfold implAM in FX. rewrite WA, BSZ in FX. apply FX; clear FX;
        rewrite ?zb_to_bytes in *; unfold FWRITEX_DEPTH, zlength in *;
        fastfirst (first [ noevar_assumption | exact FC | exact BUF | exact BP | exact SRC | exact BYT | exact EA0 | reflexivity | exact CH | exact ST | exact SSP | exact MI
              | exact FLsvb | exact FLw
              | intros X; rewrite X in WA; discriminate
              | lia | exact KH | exact ENV | exact IESF | exact IESB | exact APF | exact APB | exact SOS | exact SOB | exact RGSTK | exact RGF | exact RGB | exact RGS | exact RGIMG
              | match goal with |- ?g => idtac "FILEOUT-PREM:" g end; fail ]). }
    cbv beta. intros [f' st''] RNG' ms' [-> PO]. cbn [fst snd] in PO |- *.
    unfold fwritex_post in PO.
    destruct PO as (-> & FXI & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP').
    apply implF_ret_ok. apply evtF_done. unfold postF. cbn [fst snd]. split; [reflexivity|]. unfold out_post, SR.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, fx_W; cbn [outside]. rewrite BSZ. intros; lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    { (* [comment removed for export] *)
      split; [cbn [snd]; congruence|]. split; [exact (fsink_inv_fx f f' INV FXI)|].
      pose proof FXI as (E1 & E2 & E3 & E4 & E5 & E6 & WA' & RB' & SW & LBI).
      cbn [fst snd]. exists flags, mode', bufbytes'. rewrite ?E1, ?BSZ. rewrite ?WA, ?BSZ in FC'. rewrite ?BSZ in BUF'. rewrite ?BSZ in WBL'.
      split; [exact FC'|]. split; [exact (flags_ok_fx f f' flags FXI FL)|]. split; [exact BUF'|]. split; [exact BP'| exact WBL']. }
    split; [exact SSP'|].
    (* [comment removed for export] *)
    eapply bytes_at_transport; [exact SRC | exact MU |].
    unfold fx_W. rewrite zb_length, BSZ. cbn [disjoint_from]. unfold zlength in *. lia.
  Qed.
End FileSink.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Bridge.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition pieces_small (ps : list (list Z)) : Prop := Forall (fun p => zlength p <= PIECE_MAX) ps.

  Lemma out_pieces_bridgeF : forall ps (f : file_st) (st : St) (r : Z) RNG (Q : Z * (file_st * St) -> footprint -> machine_state -> Prop) ms,
    pieces_small ps ->
    implS asegs RNG (outsk OUT_file ps (mret r) (f, st)) (epostF Q) ms ->
    implS asegs RNG (out_pieces f ps st) (epostF (fun p RNG' ms' => Q (r, (fst p, snd p)) RNG' ms')) ms.
  Proof using Type. pin_using tt.
    induction ps as [|p ps IH]; intros f st r RNG Q ms SM H; cbn [outsk out_pieces] in *.
    - exact H.
    - apply Forall_cons_iff in SM. destruct SM as [SM1 SM2].
      unfold mbind, OUT_file, ebind in *. cbn [fst snd] in H.
      replace (zlength p <=? PIECE_MAX) with true in H by (symmetry; apply Z.leb_le; exact SM1).
      apply (implF_bind_assoc_rev asegs) in H.
      eapply (implF_bind_ext2 asegs _ _ _ _ _ (fun _ => True)); [apply tforall_true | | exact H].
      cbv beta. intros [|[f1 st1]] RNG' ms1 _ H1; cbn [ITree.bind fst snd] in H1 |- *.
      + exact H1.
      + apply IH; [exact SM2 | exact H1].
  Qed.

  (* [comment removed for export] *)
  Lemma out_pieces_bridge : forall ps (f : file_st) (st : St) (r : Z) RNG (Q : Z -> file_st * St -> machine_state -> Prop) ms,
    pieces_small ps ->
    implAM RNG (outsk OUT_file ps (mret r)) (f, st) Q ms ->
    implAM RNG (out_pieces f ps) st (fun f' st' ms' => Q r (f', st') ms') ms.
  Proof using Type. pin_using tt.
    intros ps f st r RNG Q ms SM H. unfold implAM in *.
    eapply implF_mono; [apply (out_pieces_bridgeF ps f st r RNG _ ms SM H)|].
    intros [|[f1 st1]] RNG' ms'; cbn; [exact (fun x => x)|]. unfold postF. cbn [fst snd]. exact (fun x => x).
  Qed.
End Bridge.
End TwB.
End Printf_fsink.

(* [comment removed for export] *)
Module F_vfprintf_file.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep FP ITree Nodes Decode StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AProto. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require MonadX Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_read__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface F_printf_core_common F_printf_core. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.Printf_outsA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Lemma rwc_eqA : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H ->. exact H. Qed.
Ltac readdr H A' := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let H' := fresh in assert (H' : rw_cells asegs m A' cs) by (eapply rwc_eqA; [exact H | lia]); clear H; rename H' into H end.

Definition VFPRINTF : Z := 0x9aee0.
Definition TOWRITE : Z := 0x9ac80.
Definition VF_FRAME : Z := 368.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
  intros f c k Hk Hc. rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof. intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity. Qed.
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
  rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

(* [comment removed for export] *)
Definition flags_ok_clr_err__stmt : Prop := forall f (flags : word),
  flags_ok f flags -> flags_ok f (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)).
Section Sz6.
Variables f flags : ltac2:(SecDiet.SzSec.tyM 'flags_ok_clr_err__stmt "vv" @f).
#[using="Type"] Lemma flags_ok_clr_err__body : ltac2:(SecDiet.SzSec.bodyP 'flags_ok_clr_err__stmt "vv").
Proof.
  intros FL.
 pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R.
  pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583) as LR.
  unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *. rewrite unsigned_lit by lia.
  destruct FL as (A1 & A2 & A3 & A4 & A5 & A6).
  rewrite <- !Z.land_assoc.
  change (Z.land 18446744073709551583 4) with 4. change (Z.land 18446744073709551583 8) with 8.
  change (Z.land 18446744073709551583 16) with 16. change (Z.land 18446744073709551583 32) with 0.
  change (Z.land 18446744073709551583 64) with 64. change (Z.land 18446744073709551583 1) with 1.
  rewrite Z.land_0_r.
  repeat split; try reflexivity; rewrite land_low7, sx32_mod128, <- land_low7 by lia; assumption.
Qed.
End Sz6.
Lemma flags_ok_clr_err : ltac:(let t := eval cbv delta [flags_ok_clr_err__stmt] in flags_ok_clr_err__stmt in exact t).
Proof. intros f flags. ltac2:(SecDiet.SzSec.closeP 'flags_ok_clr_err__body "vv"). Qed.

(* [comment removed for export] *)
Lemma flags_ok_relw : forall f (flags : word), flags_ok f flags -> flags_ok f (sx32 flags).
Proof.
  intros f flags FL. unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *.
  destruct FL as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; rewrite land_low7, sx32_mod128, <- land_low7 by lia; assumption.
Qed.

Lemma flags_err_clear_lw : forall f (flags : word), flags_ok f flags -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof.
  intros f flags (_ & _ & _ & A4 & _). rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact A4.
Qed.
Lemma flags_nowr_clear : forall f (flags : word), flags_ok f flags -> f_nowr f = false -> Z.land (bv_unsigned flags) 8 = 0.
Proof. intros f flags (_ & A2 & _) NW. unfold F_NOWR in A2. rewrite NW in A2. exact A2. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Forall_disj_vff : forall (W : list (Z * Z)) lo sp Fp FS B BS a n,
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  (a + n <= lo \/ sp <= a) -> (a + n <= Fp \/ Fp + FS <= a) -> (a + n <= B \/ B + BS <= a) -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W lo sp Fp FS B BS a n H H1 H2 H3 Hn. induction H as [|[u1 u2] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.
Definition arg_ok_vff__stmt : Prop := forall RNG Fp FS B BS m m' lo sp sp' ap w a (W : list (Z * Z)),
  arg_ok Fp FS B BS RNG m lo sp ap w a -> sp' <= sp -> munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  arg_ok Fp FS B BS RNG m' lo sp' ap w a.
Section Sz11.
Variables RNG Fp FS B BS m m' lo sp sp' ap w a W : ltac2:(SecDiet.SzSec.tyM 'arg_ok_vff__stmt "vvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma arg_ok_vff__body : ltac2:(SecDiet.SzSec.bodyP 'arg_ok_vff__stmt "vvvvvvvvvvvvvv").
Proof.
  intros H Hsp MU WM AW HW.
 destruct a as [s|i|u|u]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & S47 & RGs & SOs). exists slack.
  split; [|repeat (split; [fastfirst (first [assumption | lia])|]); exact (sobj_transport _ _ _ _ _ _ SOs MU WM AW)].
  eapply bytes_at_transport; [exact BY | exact MU |].
  rewrite length_app, zb_length. cbn [length]. unfold zlength in *.
  eapply Forall_disj_vff; [exact HW | | | | lia]; lia.
Qed.
End Sz11.
Lemma arg_ok_vff : ltac:(let t := eval cbv delta [arg_ok_vff__stmt] in arg_ok_vff__stmt in exact t).
Proof. intros RNG Fp FS B BS m m' lo sp sp' ap w a W. ltac2:(SecDiet.SzSec.closeP 'arg_ok_vff__body "vvvvvvvvvvvvvv"). Qed.
Lemma args_ok_vff : forall RNG Fp FS B BS m m' lo sp sp' ap ws args (W : list (Z * Z)),
  args_ok Fp FS B BS RNG m lo sp ap ws args -> sp' <= sp -> munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  args_ok Fp FS B BS RNG m' lo sp' ap ws args.
Proof.
  intros RNG Fp FS B BS m m' lo sp sp' ap ws args W. revert ws. induction args as [|a args IH]; intros ws H Hsp MU WM AW HW; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vff; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MonadFacts.
  Context {rc : runConstT}.
  Context {St : Type}.

  (* [comment removed for export] *)
  Lemma implM_bind_mret : forall {A} RNG (c : M St A) s Q ms,
    implAM RNG c s Q ms -> implAM RNG (mbind c mret) s Q ms.
  Proof using Type. pin_using tt.
    intros A RNG c s Q ms H. eapply implAM_bind; [exact H|]. intros a s' ms' HQ. apply implAM_ret. apply evtF_done. exact HQ.
  Qed.

  Lemma implM_ms_eq : forall {A} RNG (c : M St A) s Q ms ms', implAM RNG c s Q ms' -> ms = ms' -> implAM RNG c s Q ms.
  Proof using Type. pin_using tt. intros A RNG c s Q ms ms' H ->. exact H. Qed.
End MonadFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VfFile.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Variables (sw0 ch0 : bool).
  Let q := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FLOC : (684904 <= Fp /\ Fp + 232 <= 714232) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis BLOC : (6297088 <= B /\ B + 1024 <= GLOBALS_TOP) \/ (0 < B /\ B + 1024 <= lo /\ (B + 1024 <= 65536 \/ GLOBALS_TOP <= B)).
  Hypothesis FB : B + 1024 <= Fp \/ Fp + 232 <= B.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + 1024)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B 1024.

  #[local] Notation SINKf rpos rend := (SINK_file (St:=St) Fp B 1024 rpos rend closefn readfn seekfn prev next tail sw0 ch0).
  #[local] Notation OUTf := (OUT_file (St:=St)).

  (* [comment removed for export] *)
  Definition vfprintf_file_post (rpos rend : Z) (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fsink_inv 1024 sw0 ch0 f' /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (bufbytes' : list byte) (m' : mem) (rpos' rend' : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q); (Fp, Fp + 232); (B, B + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q
      /\ ssp_cells m' canary
      /\ rw_cells asegs m' Fp (fcells flags' rpos' rend' closefn (B + 1024) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B 1024 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ ((rpos' = rpos /\ rend' = rend) \/ (rpos' = 0 /\ rend' = 0))
      /\ flags_ok f' flags'
      /\ rw_cells asegs m' B [CB 1024%nat bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= 1024.

  (* [comment removed for export] *)
  Lemma sinkfacts : 0 <= Fp /\ 0 < B /\ 0 <= 1024 <= 1024 /\ B + 1024 <= 2^47 (* [comment removed for export] *) /\ Fp + 232 < 2^63
    /\ (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) /\ (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp)
    /\ (B + 1024 <= got_ssp \/ got_ssp + 8 <= B) /\ (B + 1024 <= ssp_guard \/ ssp_guard + 8 <= B).
  Proof using BLOC FLOC HVA LO fmtz. pin_using (fun (BLOC FLOC HVA LO fmtz : unit) => tt).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold got_ssp, ssp_guard, GLOBALS_TOP, VF_FRAME, PC_DEPTH, q, zlength in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition vf_pass2__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m m1 : mem) (f1 : file_st) (st : St)
      (flags flags1 mode1 : word) (bufbytes1 junk : list byte) (rpos rend rpos1 rend1 : Z),
    ((rpos1 = rpos /\ rend1 = rend) \/ (rpos1 = 0 /\ rend1 = 0)) ->
    rw_cells asegs m1 Fp (fcells flags1 rpos1 rend1 closefn (B + 1024) (B + zlength (f_wbuf f1)) B readfn (wfn_of f1) seekfn B 1024 prev next (f_fd f1) mode1 (lbf_of f1) tail) ->
    flags_ok f1 flags1 -> fsink_inv 1024 sw0 ch0 f1 ->
    rw_cells asegs m1 B [CB 1024%nat bufbytes1] -> firstn (length (f_wbuf f1)) bufbytes1 = to_bytes (f_wbuf f1) -> zlength (f_wbuf f1) <= 1024 ->
    rw_cells asegs m1 (q + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 248 junk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                   C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at asegs m1 A (zb fmtz) -> va_area m1 VA slots -> args_ok Fp 232 B 1024 RNG m1 lo q (q + -368) slots args ->
    stk asegs m1 lo (q + -368) -> ssp_cells m1 canary -> mem_inv asegs m1 ->
    munch [(lo, q); (Fp, Fp + 232); (B, B + 1024)] m m1 -> wmono asegs m m1 ->
    Z.land (bv_unsigned (sx32 flags)) 32 = 0 ->
    icptenv m1 -> sobj RNG m1 lo q -> sobj RNG m1 A (A + zlength fmtz) -> sobj RNG m1 68460 68469 -> sobj RNG m1 Fp (Fp + 232) -> sobj RNG m1 B (B + 1024) ->
    implAM RNG (out_pieces f1 ps) st (vfprintf_file_post rpos rend m st)
      (MS (mkR x1 (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 0) (sx32 flags) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9afd0) fc None m1 (seg_rom asegs)).
  Section Sz16.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 bufbytes1 junk rpos rend rpos1 rend1 : ltac2:(SecDiet.SzSec.tyM 'vf_pass2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma vf_pass2__body : ltac2:(SecDiet.SzSec.bodyP 'vf_pass2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL KLO IESF IESB RSTK RIMG RVA RFP RBUF. pin_using (fun (BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL KLO : unit) => tt).
    intros RP FC1 FL1 INV1 BUF1 BP1 WBL1 FR BY VAA AOK ST SSP MI MU WM OLDERR ENV1 SOSTK1 SOFMT1 SOPFX1 SOF1 SOB1.
    pose proof sinkfacts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB. pose proof (rw_CB_length _ _ _ _ BUF1) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof INV1 as (WA1 & RB1 & BS1 & NW1 & CH1 & SW1 & CN1).
    (* [comment removed for export] *)
    pose proof (printf_core_proof (at_nodeA asegs) (silA ASHM) (npeekA asegs) fstepS (file_st * St) Fp 232 Fp B 1024 (SINKf rpos1 rend1 st) TOPOK_file OUTf
                  (file_sink_frame Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K3 FB K6 K7 K8 K9)
                  (file_sink_flags Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K1 K5)
                  file_topok
                  (file_out Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K1 K2 K3 K4 FB K6 K7 K8 K9 IESF IESB)) as PC2.
    unfold printf_core_stmt in PC2.
    set (PCQ := printf_core_post (St:=file_st * St) Fp 232 B 1024 (SINKf rpos1 rend1 st) (Z_to_bv 64 0x9afe8) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp
                  (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 6297080) (Z_to_bv 64 1) (Z_to_bv 64 0) (sx32 flags) s6 s7 s8 s9 s10 s11 F fc
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -368) : word)) lo canary m1).
    apply (implAM_post_evt RNG (out_pieces f1 ps) st (fun f' st' ms' => PCQ r (f', st') ms')).
    { apply out_pieces_bridge; [exact SMALL|].
      eapply (printf_model_outsA OUTf RNG fmtz args ps r mret); [exact PIECES|].
      apply implM_bind_mret.
      apply implAM_from_evt. do 5 zs. zs. apply evtF_done.
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      replace (Z_to_bv 64 VA : word) with (Z_to_bv 64 (VA + 8 * 0) : word) in APC by (f_equal; lia).
      eapply implM_ms_eq; [eapply PC2 with (i := 0%Z) (slots := slots) | subst PCQ; ms_eq]; clear PC2; rewrite ?unsigned_lit by (keep_hyps sp A fmtz bufbytes1 HA lo LO GLO SPHI; lia);
        unfold PC_DEPTH, GLOBALS_TOP, TOPOK_file, zlength.
      all: match goal with |- ?g => fastfirst (first [ noevar_assumption |
             (* [comment removed for export] *) split; [reflexivity | split; [exact INV1 | exists flags1, mode1, bufbytes1; cbn [fst]; split; [exact FC1 | split; [exact FL1 | split; [exact BUF1 | split; [exact BP1 | exact WBL1]]]]]]
           | exact BY | exact HF | reflexivity | exact APC | exact VAA | exact I
           | cbn [skipn Z.to_nat]; eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes1; lia) | apply (munch_refl []) | apply wmono_refl | apply Forall_nil | constructor]
           | exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption
           | exact KLO | exact ENV1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact SOB1 | exact RIMG | exact RVA | exact RFP | exact RBUF
           | eapply sobj_sub; [exact SOSTK1 | (keep_hyps sp lo fmtz bufbytes1 LO; lia) | (keep_hyps sp VA fmtz slots bufbytes1 HVA lo LO; lia) | (keep_hyps sp fmtz bufbytes1; lia)]
           | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fmtz bufbytes1 LO; lia)]
           | eapply rng_sub'; [exact RIMG | (keep_hyps sp A fmtz bufbytes1 HA; lia)]
           | (keep_hyps sp VA fmtz slots bufbytes1 HVA Fp lo FLOC B GLO BLOC; lia)
           | idtac "VFP2-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' PO. clear PC2. subst PCQ.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & -> & -> & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [_ FR]. cbn [cells_size csize Nat.add app] in FR.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
    clear BY VAA AOK BUF1 FC1.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
    fix_ret.
    destruct SNK3 as (EST3 & INV3 & flags3 & mode3 & bufbytes3 & FC3 & FL3 & BUF3 & BP3 & WBL3). cbn [fst snd] in EST3, INV3, FC3, FL3, BUF3, BP3, WBL3. subst st'.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC3.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 (sx32 flags3)) as FR3. unfold bv_modulus in FR3. cbn in FR3.
    zs. zs. rewrite (flags_err_clear_lw f' flags3 FL3). zs. rewrite OLDERR, Z.lor_0_r.
    zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA); CB 248 junk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                   C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
      [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact APC3|]; cbn [cells_size csize Nat.add app]; eapply rwc_eqA; [exact FR | lia]
      | clear APC3 FR ] end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evtF_done. unfold vfprintf_file_post, q. split; [reflexivity|]. split; [exact INV3|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [unfold fcells, file_cells; exact FC3|].
    split; [exact RP|].
    split; [apply flags_ok_relw; exact FL3|].
    split; [exact BUF3|]. split; [exact BP3| exact WBL3].
  Qed.
  End Sz16.
  Lemma vf_pass2 : ltac:(let t := eval cbv delta [vf_pass2__stmt] in vf_pass2__stmt in exact t).
  Proof using BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL KLO IESF IESB RSTK RIMG RVA RFP RBUF. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 bufbytes1 junk rpos rend rpos1 rend1. ltac2:(SecDiet.SzSec.closeP 'vf_pass2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Ltac vff_ctx ENV SOSTK SOFMT SOPFX SOF SOB MU WM :=
    lazymatch type of MU with munch _ _ ?mc =>
      assert (ENVc : icptenv mc) by (eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe]);
      lazymatch type of SOSTK with sobj ?R _ ?a ?b => assert (SOSTKc : sobj R mc a b) by (eapply sobj_transport; [exact SOSTK | exact MU | exact WM | solve_appW]) end;
      lazymatch type of SOFMT with sobj ?R _ ?a ?b => assert (SOFMTc : sobj R mc a b) by (eapply sobj_transport; [exact SOFMT | exact MU | exact WM | solve_appW]) end;
      lazymatch type of SOPFX with sobj ?R _ ?a ?b => assert (SOPFXc : sobj R mc a b) by (eapply sobj_transport; [exact SOPFX | exact MU | exact WM | solve_appW]) end;
      lazymatch type of SOF with sobj ?R _ ?a ?b => assert (SOFc : sobj R mc a b) by (eapply sobj_transport; [exact SOF | exact MU | exact WM | solve_appW]) end;
      lazymatch type of SOB with sobj ?R _ ?a ?b => assert (SOBc : sobj R mc a b) by (eapply sobj_transport; [exact SOB | exact MU | exact WM | solve_appW]) end
    end.

  (* [comment removed for export] *)
  Lemma flags_ok_set_w : forall f fl act wb, flags_ok f fl -> flags_ok (set_w act wb (set_rbuf [] f)) fl.
  Proof using Type. pin_using tt. intros f fl act wb FL. unfold flags_ok in *. cbn. exact FL. Qed.

  Definition vfprintf_file_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells asegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at asegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 B 1024 RNG m lo q (q - VF_FRAME) slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) -> sobj RNG m B (B + 1024) ->
    implAM RNG (vfprintf f ps) st (vfprintf_file_post rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom asegs)).
  Section Sz18.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend : ltac2:(SecDiet.SzSec.tyM 'vfprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_file_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL KLO IESF IESB RSTK RIMG RVA RFP RBUF. pin_using (fun (BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL KLO : unit) => tt).
 intros -> -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY VAA AOK ST SSP MI ENV SOSTK SOFMT SOPFX SOF SOB.
    pose proof (sobj_appW _ _ _ _ SOF) as APWF. pose proof (sobj_appW _ _ _ _ SOB) as APWB.
    pose proof sinkfacts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    unfold fcells, file_cells in FC0.
    pose proof (rw_CB_length _ _ _ _ BUF0) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    (* [comment removed for export] *)
    unfold vfprintf. rewrite BS. change (1024 =? 0) with false. cbv iota.
    (* [comment removed for export] *)
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash FC0. stash BUF0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    apply implAM_from_evt.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB asegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg _ _ _ => apply (proj1 (rw_cells_app sg _ _ [_;_;_] _)) in FR end.
    destruct FR as [FRlo FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    lazymatch type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -104)%Z in FRhi by lia end.
    do 12 zs. do 14 zs.
    lazymatch type of FRlo with rw_cells ?sg ?mm ?A ?cs1 => lazymatch type of FRhi with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in FRhi by (cbn [cells_size csize Nat.add]; lia);
      pose proof (proj2 (rw_cells_app sg mm A cs1 cs2) (conj FRlo FRhi)) as FR; clear FRlo FRhi end end.
    cbn [app] in FR.
    unfold hide in FC0, BUF0.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call asegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (B, B + 1024)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; (keep_hyps sp Fp B lo x H; lia) | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; (keep_hyps sp A lo fmtz GLO HA; lia)];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA; (keep_hyps sp VA lo slots HVA; lia)]
    end.
    clear MUp. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evtF_cut.
    { eapply PC1; rewrite ?unsigned_lit by (keep_hyps sp A fmtz bufbytes HA lo LO GLO SPHI; lia); unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | (keep_hyps sp lo fmtz bufbytes LO; lia) | (keep_hyps sp lo fmtz bufbytes GLO; lia) | (keep_hyps sp VA fmtz slots bufbytes HVA; lia)
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | (keep_hyps sp A fmtz bufbytes HA; lia) | (keep_hyps sp fmtz bufbytes; lia) | (keep_hyps sp fmtz bufbytes SPHI; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fmtz bufbytes; lia)] | exact RIMG | eapply rng_sub'; [exact RIMG | (keep_hyps sp A fmtz bufbytes HA; lia)] ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. first [if_lit | brf Kb; [exfalso; revert Kb; cbn; rewrite ?unsigned_lit by lia; cbn; lia|]]. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    unfold hide in AOK, VAAm. clear BYm VAA. unfold va_area in VAAm.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (VAA : va_area mc VA slots)
        by (unfold va_area; eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA FLOC BLOC GLO LO SPHI NNs; lia]) end.
    clear VAAm.
    pose proof (flags_ok_clr_err f flags FL0) as FL1.
    pose proof (flags_err_clear_lw f flags FL0) as OLDERR.
    destruct (f_wactive f) eqn:WACT.
    - (* [comment removed for export] *)
      zs. brf Kw; [| exfalso; revert Kw; rewrite ?unsigned_lit by lia; lia].
      apply evtF_done. unfold ensure_w. rewrite WACT. apply implM_retb.
      vff_ctx ENV SOSTK SOFMT SOPFX SOF SOB MU WM.
      eapply implM_ms_eq; [eapply (vf_pass2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (rpos := rpos) (rend := rend) | ms_eq].
      all: try first [ left; split; reflexivity | exact FC0 | exact FL1 | exact BUF0 | exact BP0 | exact WBL | exact FR | exact BY | exact VAA | unfold va_area; exact VAA | exact STc
                     | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2]
                     | exact ENVc | exact SOSTKc | exact SOFMTc | exact SOPFXc | exact SOFc | exact SOBc | assumption ].
      all: try (split; [exact WACT | split; [exact RB | split; [exact BS | split; [exact NW | split; [exact CH | split; [exact SWB | exact CHN]]]]]]).
      all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes; lia) | exact MU | exact WM | solve_appW | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz bufbytes Fp B; lia)).
      all: match goal with |- ?g => idtac "VFB1-LEFT:" g end.
      all: fail.
    - (* [comment removed for export] *)
      zs. brf Kw; [exfalso; revert Kw; rewrite ?unsigned_lit by lia; lia |].
      zs. zs. zs. (* [comment removed for export] *)
      specialize (WB0 eq_refl).
      eapply evtF_cut.
      { pose proof (flags_nowr_clear _ _ FL1 ltac:(cbn; exact NW)) as X8.
        eapply evt_ms_eq; [eapply towrite_specZ | ms_eq].
        all: first [ exact FC0 | exact X8 | assumption | lia | match goal with |- ?g => idtac "TW-LEFT:" g end ]. }
      cbv beta. intros ms' PO.
      destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & mode' & m'' & -> & MUc & WMc & MIt & FCt).
      clear FC0. unfold va_area in VAA.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      fix_ret.
      zs. if_lit. (* [comment removed for export] *)
      apply evtF_done. unfold ensure_w, towrite. rewrite WACT, NW. apply implM_retb.
      vff_ctx ENV SOSTK SOFMT SOPFX SOF SOB MU WM.
      eapply implM_ms_eq; [eapply (vf_pass2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (rpos := rpos) (rend := rend) (f1 := set_w true [] (set_rbuf [] f)) | ms_eq].
      all: try first [ right; split; reflexivity | exact FL1 | apply flags_ok_set_w; exact FL1 | exact BUF0 | exact WBL | exact FR | exact BY | exact VAA | unfold va_area; exact VAA | exact STc
                     | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2]
                     | exact ENVc | exact SOSTKc | exact SOFMTc | exact SOPFXc | exact SOFc | exact SOBc | assumption ].
      all: try (cbn [f_wbuf set_w set_rbuf zlength length Z.of_nat]; rewrite Z.add_0_r; unfold fcells, wfn_of, lbf_of; cbn; unfold wfn_of, lbf_of in FCt; exact FCt).
      all: try (split; [reflexivity | split; [reflexivity | split; [exact BS | split; [exact NW | split; [exact CH | split; [exact SWB | exact CHN]]]]]]).
      all: try (cbn [f_wbuf set_w set_rbuf length]; reflexivity).
      all: try (cbn [f_wbuf set_w set_rbuf]; unfold zlength; cbn [length Z.of_nat]; (keep_hyps sp fmtz bufbytes; lia)).
      all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes; lia) | exact MU | exact WM | solve_appW | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz bufbytes Fp B; lia)).
      all: match goal with |- ?g => idtac "VFB2-LEFT:" g end.
      all: fail.
  Qed.
  End Sz18.
  Theorem vfprintf_file_spec : ltac:(let t := eval cbv delta [vfprintf_file_spec__stmt] in vfprintf_file_spec__stmt in exact t).
  Proof using BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL KLO IESF IESB RSTK RIMG RVA RFP RBUF. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend. ltac2:(SecDiet.SzSec.closeP 'vfprintf_file_spec__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End VfFile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VfUbf.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B0 : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Let q := bv_unsigned sp.
  Let Bi := q - 352.   (* [comment removed for export] *)
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.   (* [comment removed for export] *)
  Hypothesis FLOC : (684904 <= Fp /\ Fp + 232 <= 714232) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis HB0 : 0 < B0 < 2^64.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis R0 : rng0 RNG.

  #[local] Notation SINKu rpos rend := (SINK_file (St:=St) Fp Bi 80 rpos rend closefn readfn seekfn prev next tail false true).

  Definition vfprintf_ubf_post (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = [] /\ f_bufsize f' = 0 /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q); (Fp, Fp + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q
      /\ ssp_cells m' canary
      /\ rw_cells asegs m' Fp (fcells flags' 0 0 closefn 0 0 0 readfn (wfn_of f') seekfn B0 0 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ flags_ok f' flags'.

  Lemma sinkfacts_u : 0 <= Fp /\ 0 < Bi /\ 0 <= 80 <= 1024 /\ Bi + 80 <= 2^47 (* [comment removed for export] *) /\ Fp + 232 < 2^63 /\ (Bi + 80 <= Fp \/ Fp + 232 <= Bi)
    /\ (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) /\ (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp)
    /\ (Bi + 80 <= got_ssp \/ got_ssp + 8 <= Bi) /\ (Bi + 80 <= ssp_guard \/ ssp_guard + 8 <= Bi).
  Proof using FLOC GLO HVA LO fmtz. pin_using (fun (FLOC GLO HVA LO fmtz : unit) => tt).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold got_ssp, ssp_guard, GLOBALS_TOP, VF_FRAME, PC_DEPTH, q, Bi, zlength in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma flags_ok_ws : forall f fl act wb n, flags_ok f fl -> flags_ok (set_w act wb (set_bufsize n f)) fl.
  Proof using Type. pin_using tt. intros f fl act wb n FL. unfold flags_ok in *. cbn. exact FL. Qed.
  Lemma flags_ok_ws' : forall f fl act wb n, flags_ok (set_w act wb (set_bufsize n f)) fl -> flags_ok f fl.
  Proof using Type. pin_using tt. intros f fl act wb n FL. unfold flags_ok in *. cbn in FL. exact FL. Qed.

  (* [comment removed for export] *)
  Definition vf_pass2u__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m m1 : mem) (f1 : file_st) (st : St)
      (flags flags1 mode1 : word) (ibuf rest : list byte),
    rw_cells asegs m1 Fp (fcells flags1 0 0 closefn (Bi + 80) (Bi + zlength (f_wbuf f1)) Bi readfn (wfn_of f1) seekfn Bi 80 prev next (f_fd f1) mode1 (lbf_of f1) tail) ->
    flags_ok f1 flags1 -> fsink_inv 80 false true f1 -> f_wbuf f1 = [] ->
    rw_cells asegs m1 Bi [CB 80%nat ibuf] ->
    rw_cells asegs m1 (q + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA)] ->
    rw_cells asegs m1 (q + -272) [CB 168 rest; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                 C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at asegs m1 A (zb fmtz) -> va_area m1 VA slots -> args_ok Fp 232 Bi 80 RNG m1 lo q (q + -368) slots args ->
    stk asegs m1 lo (q + -368) -> ssp_cells m1 canary -> mem_inv asegs m1 ->
    munch [(lo, q); (Fp, Fp + 232)] m m1 -> wmono asegs m m1 ->
    Z.land (bv_unsigned (sx32 flags)) 32 = 0 ->
    icptenv m1 -> sobj RNG m1 lo q -> sobj RNG m1 A (A + zlength fmtz) -> sobj RNG m1 68460 68469 -> sobj RNG m1 Fp (Fp + 232) ->
    implAM RNG (f2 <- out_pieces f1 ps ;; f3 <- file_writefn f2 [] ;; mret (set_w false [] (set_bufsize 0 f3))) st (vfprintf_ubf_post m st)
      (MS (mkR x1 (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 B0) (sx32 flags) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9afd0) fc None m1 (seg_rom asegs)).
  Section Sz22.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 ibuf rest : ltac2:(SecDiet.SzSec.tyM 'vf_pass2u__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma vf_pass2u__body : ltac2:(SecDiet.SzSec.bodyP 'vf_pass2u__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FLOC GLO HA HB0 HF HVA LO PIECES SMALL KLO IESF RSTK RIMG RVA RFP R0. pin_using (fun (FLOC GLO HA HB0 HF HVA LO PIECES SMALL KLO : unit) => tt).
    intros FC1 FL1 INV1 WB1 BUF1 APC2 FR BY VAA AOK ST SSP MI MU WM OLDERR ENV1 SOSTK1 SOFMT1 SOPFX1 SOF1.
    pose proof sinkfacts_u as (K1 & K2 & K3 & K4 & K5 & KFB & K6 & K7 & K8 & K9).
    assert (IESBi : iesafe [(Bi, Bi + 80)]) by (apply iesafe_one_high; unfold Bi, q, VF_FRAME, PC_DEPTH, KHIGH in *; lia).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB. pose proof (rw_CB_length _ _ _ _ BUF1) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof INV1 as (WA1 & RB1 & BS1 & NW1 & CH1 & SW1 & CN1).
    (* [comment removed for export] *)
    pose proof (printf_core_proof (at_nodeA asegs) (silA ASHM) (npeekA asegs) fstepS (file_st * St) Fp 232 Fp Bi 80 (SINKu 0 0 st) TOPOK_file (OUT_file (St:=St))
                  (file_sink_frame Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K3 KFB K6 K7 K8 K9)
                  (file_sink_flags Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K1 K5)
                  file_topok
                  (file_out Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K1 K2 K3 K4 KFB K6 K7 K8 K9 IESF IESBi)) as PC2.
    unfold printf_core_stmt in PC2.
    set (PCQ := printf_core_post (St:=file_st * St) Fp 232 Bi 80 (SINKu 0 0 st) (Z_to_bv 64 0x9afe8) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp
                  (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 6297080) (Z_to_bv 64 1) (Z_to_bv 64 B0) (sx32 flags) s6 s7 s8 s9 s10 s11 F fc
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -368) : word)) lo canary m1).
    unfold q, Bi in *.
    eapply implAM_bind with (Q1 := fun f' st' ms' => PCQ r (f', st') ms').
    { { apply out_pieces_bridge; [exact SMALL|].
        eapply (printf_model_outsA (OUT_file (St:=St)) RNG fmtz args ps r mret); [exact PIECES|].
        apply implM_bind_mret.
        apply implAM_from_evt. do 5 zs. zs. apply evtF_done.
        apply (proj1 (rw_cells_app asegs _ _ [_] _)) in APC2. destruct APC2 as [APC AP2]. cbn [cells_size csize Nat.add app] in AP2.
        replace (Z_to_bv 64 VA : word) with (Z_to_bv 64 (VA + 8 * 0) : word) in APC by (f_equal; lia).
        assert (SNK : SINK_file Fp (bv_unsigned sp - 352) 80 0 0 closefn readfn seekfn prev next tail false true st m1 (f1, st)).
        { split; [reflexivity|]. split; [exact INV1|]. exists flags1, mode1, ibuf. cbn [fst].
          split; [exact FC1|]. split; [exact FL1|]. split; [exact BUF1|]. rewrite WB1. split; [reflexivity| unfold zlength; cbn; lia]. }
        eapply implM_ms_eq; [eapply PC2 with (i := 0%Z) (slots := slots) | subst PCQ; ms_eq]; clear PC2; rewrite ?unsigned_lit by lia;
          unfold PC_DEPTH, GLOBALS_TOP, TOPOK_file, zlength.
        all: match goal with |- ?g => fastfirst (first [ noevar_assumption |
               exact SNK
             | exact BY | exact HF | reflexivity | exact APC | exact VAA | unfold va_area; exact VAA | exact I
             | cbn [skipn Z.to_nat]; eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz ibuf; lia) | apply (munch_refl []) | apply wmono_refl | apply Forall_nil | constructor]
             | exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption
             | exact KLO | exact ENV1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact RIMG | exact RVA | exact RFP
             | eapply sobj_sub; [exact SOSTK1 | (keep_hyps sp lo fmtz ibuf LO; lia) | (keep_hyps sp fmtz ibuf K4 VA slots HVA lo LO; lia) | (keep_hyps sp fmtz ibuf; lia)]
             | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fmtz ibuf LO; lia)]
             | eapply rng_sub'; [exact RIMG | (keep_hyps sp A fmtz ibuf HA; lia)]
             | (keep_hyps sp fmtz ibuf K4 Fp VA lo slots FLOC HVA; lia)
             | idtac "VFU2-LEFT:" g; fail ]) end. } }
    cbv beta. intros f2 st2 ms2 PO. clear PC2. subst PCQ.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & -> & -> & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    clear BY VAA AOK BUF1 FC1.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in APC2. destruct APC2 as [_ AP2]. cbn [cells_size csize Nat.add app] in AP2.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in AP2 by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
    destruct SNK3 as (EST3 & INV3 & flags3 & mode3 & bufbytes3 & FC3 & FL3 & BUF3 & BP3 & WBL3). cbn [fst snd] in EST3, INV3, FC3, FL3, BUF3, BP3, WBL3. subst st2.
    pose proof INV3 as (WA3 & RB3 & BS3 & NW3 & CH3 & SW3 & CN3).
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (SWF : f_stdoutw f2 = false) by (destruct (f_stdoutw f2) eqn:E; [discriminate (SW3 eq_refl) | reflexivity]).
    assert (WFN : wfn_of f2 = F_STDIO_WRITE) by (unfold wfn_of; rewrite SWF; reflexivity).
    rewrite CN3 in CH3.
    pose proof (rw_CB_length _ _ _ _ BUF3) as LB3.
    assert (NNw : 0 <= zlength (f_wbuf f2)) by (unfold zlength; lia).
    pose proof (CB_prefix_bytes_at m3 (bv_unsigned sp - 352) (Z.to_nat 80) bufbytes3 (to_bytes (f_wbuf f2)) BUF3 ltac:(rewrite length_to_bytes; exact BP3)) as WBB.
    unfold fcells, file_cells in FC3. rewrite WFN in FC3. unfold F_STDIO_WRITE in FC3.
    apply implAM_from_evt. fix_ret.
    (* [comment removed for export] *)
    zs. zs. zs. brf Kb; [exfalso; revert Kb; rewrite ?unsigned_lit by lia; lia|].
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs.
    apply evtF_done. unfold file_writefn. rewrite SWF.
    eapply implAM_bind.
    { eapply implM_ms_eq;
        [eapply (stdio_write_spec (St:=St) RNG) with (f := f2) (s := []) (S := 0) (lo := lo) (canary := canary) (Fp := Fp) (flags := flags3)
           (rpos := 0) (rend := 0) (closefn := closefn) (wend := bv_unsigned sp - 352 + 80) (readfn := readfn) (writefn := 630444) (seekfn := seekfn)
           (B := bv_unsigned sp - 352) (bufsize := 80) (prev := prev) (next := next) (mode := mode3) (lbf := lbf_of f2) (tail := tail)
        | unfold F_STDIO_WRITE; ms_eq].
      all: rewrite ?unsigned_lit by lia.
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | unfold fcells, file_cells; exact FC3 | exact WBB | apply bytes_at_nil; (keep_hyps sp fmtz ibuf bufbytes3; lia) | reflexivity | rewrite CN3; exact CH3 | exact ST3 | exact MI3
             | split; [exact SSP1 | exact SSP2] | left; reflexivity
             | exact RFP | exact RIMG | apply (rng0_use _ _ R0); (keep_hyps sp lo fmtz ibuf bufbytes3 LO GLO SPHI; lia)
             | eapply rng_sub'; [exact RSTK | unfold STDIO_WRITE_DEPTH, zlength in *; (keep_hyps sp lo fmtz ibuf bufbytes3 f2 LO WBL3; lia)]
             | unfold STDIO_WRITE_DEPTH, got_ssp, ssp_guard, zlength in *; cbn [length Z.of_nat] in *; (keep_hyps sp lo fmtz ibuf bufbytes3 LO K4 Fp B0 GLO FLOC K6 K7 SPHI VA slots f2 HVA WBL3 KFB; lia)
             | idtac "SWCALL-LEFT:" g; fail ]) end. }
    cbv beta. intros f3 st3 ms3 PO.
    destruct PO as (-> & -> & w5 & w6 & w7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w28 & w29 & w30 & w31 & m4 & -> & MUc & WMc & MI4 & ST4 & FC4 & SSP4).
    unfold sw_W, STDIO_WRITE_DEPTH in MUc. rewrite !unsigned_lit in MUc, ST4 by lia.
    clear FC3 WBB.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
    apply implAM_ret. fix_ret.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC4.
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs.
    zs. replace (0 <? bv_unsigned sp - 352)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    zs. zs. rewrite ?Z.lor_0_l. zs.
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 (sx32 flags3)) as FR3. unfold bv_modulus in FR3. cbn in FR3.
    zs. zs. rewrite (flags_err_clear_lw f2 flags3 FL3). zs. rewrite OLDERR, Z.lor_0_r.
    zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with AP : rw_cells _ mm (bv_unsigned sp + -368)%Z [C8 ?apv'], B3 : rw_cells _ mm (q - 352)%Z [CB _ ?bb], R : rw_cells _ mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
      assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv'] ++ [C8 (Z_to_bv 64 VA)] ++ [CB (Z.to_nat 80) bb] ++ rest));
      [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact AP2 | lia]|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact B3 | unfold q; lia]|]; cbn [cells_size csize Nat.add Z.to_nat Pos.to_nat Pos.iter_op Nat.mul];
        eapply rwc_eqA; [exact R | lia]
      | clear AP AP2 B3 R ] end end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evtF_done. unfold vfprintf_ubf_post, q. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [cbn; exact RB3|]. split; [reflexivity|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [unfold fcells, file_cells; cbn [f_fd set_w set_bufsize]; unfold wfn_of, lbf_of in *; cbn [f_stdoutw f_lbf_nl set_w set_bufsize]; rewrite SWF; unfold F_STDIO_WRITE; exact FC4|].
    apply flags_ok_ws. apply flags_ok_relw. exact FL3.
  Qed.
  End Sz22.
  Lemma vf_pass2u : ltac:(let t := eval cbv delta [vf_pass2u__stmt] in vf_pass2u__stmt in exact t).
  Proof using FLOC GLO HA HB0 HF HVA LO PIECES SMALL KLO IESF RSTK RIMG RVA RFP R0. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 ibuf rest. ltac2:(SecDiet.SzSec.closeP 'vf_pass2u__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition vfprintf_ubf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (rpos rend we wp wb : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn we wp wb readfn (wfn_of f) seekfn B0 0 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags -> f_bufsize f = 0 -> f_nowr f = false -> f_rbuf f = [] -> f_wbuf f = [] ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_stdoutw f = false ->
    0 <= we < 2^64 -> 0 <= wp < 2^64 -> 0 <= wb < 2^64 -> 0 <= rpos < 2^64 -> 0 <= rend < 2^64 ->
    bytes_at asegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 Bi 80 RNG m lo q (q - VF_FRAME) slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) ->
    implAM RNG (vfprintf f ps) st (vfprintf_ubf_post m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom asegs)).
  Section Sz23.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb : ltac2:(SecDiet.SzSec.tyM 'vfprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_ubf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL KLO IESF RSTK RIMG RVA RFP R0. pin_using (fun (FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL KLO : unit) => tt).
 intros -> -> -> FC0 FL0 BS NW RB WB CHN FD SWF Rwe Rwp Rwb Rrp Rre BY VAA AOK ST SSP MI ENV SOSTK SOFMT SOPFX SOF.
    pose proof (sobj_appW _ _ _ _ SOF) as APWF.
    pose proof sinkfacts_u as (K1 & K2 & K3 & K4 & K5 & KFB & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q, Bi in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    unfold fcells, file_cells in FC0.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    (* [comment removed for export] *)
    unfold vfprintf. rewrite BS. change (0 =? 0) with true. cbv iota.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash FC0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    apply implAM_from_evt.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB asegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg _ _ _ => apply (proj1 (rw_cells_app sg _ _ [_;_;_] _)) in FR end.
    destruct FR as [FRlo FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    lazymatch type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -104)%Z in FRhi by lia end.
    do 12 zs. do 14 zs.
    lazymatch type of FRlo with rw_cells ?sg ?mm ?A ?cs1 => lazymatch type of FRhi with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in FRhi by (cbn [cells_size csize Nat.add]; lia);
      pose proof (proj2 (rw_cells_app sg mm A cs1 cs2) (conj FRlo FRhi)) as FR; clear FRlo FRhi end end.
    cbn [app] in FR.
    unfold hide in FC0.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call asegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA; lia]
    end.
    clear MUp. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evtF_cut.
    { eapply PC1; rewrite ?unsigned_lit by (keep_hyps sp A fmtz HA lo LO GLO SPHI; lia); unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | (keep_hyps sp lo fmtz LO; lia) | (keep_hyps sp lo fmtz GLO; lia) | (keep_hyps sp fmtz K4; lia)
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | (keep_hyps sp A fmtz HA; lia) | (keep_hyps sp fmtz; lia) | (keep_hyps sp fmtz SPHI; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fmtz; lia)] | exact RIMG | eapply rng_sub'; [exact RIMG | (keep_hyps sp A fmtz HA; lia)] ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    do 8 zs. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    unfold hide in AOK, VAAm. clear BYm VAA. unfold va_area in VAAm.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (VAA : bytes_at asegs mc VA (u64s slots))
        by (eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA FLOC GLO LO SPHI NNs; lia]) end.
    clear VAAm.
    pose proof (flags_ok_clr_err f flags FL0) as FL1.
    pose proof (flags_err_clear_lw f flags FL0) as OLDERR.
    pose proof (flags_nowr_clear _ _ FL1 ltac:(cbn; exact NW)) as X8.
    eapply evtF_cut.
    { eapply evt_ms_eq; [eapply towrite_specZ | ms_eq].
      all: first [ exact FC0 | exact X8 | assumption | lia | match goal with |- ?g => idtac "TWU-LEFT:" g end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    clear FC0.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. (* [comment removed for export] *)
    apply evtF_done. unfold towrite. cbn [f_nowr set_w set_bufsize]. rewrite NW. apply implM_retb.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ _ (bv_unsigned sp + -368)%Z (_ :: _ :: CB 248 _ :: _) |- _ => rename H into FRv end.
    apply (rw_cells_split_CB asegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_; _] _)) in FRv. destruct FRv as [APC2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [IBc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr IBc (bv_unsigned sp - 352)%Z. readdr FRv (bv_unsigned sp + -272)%Z.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (ENVc : icptenv mc) by (eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe]);
      assert (SOSTKc : sobj RNG mc lo (bv_unsigned sp)) by (eapply sobj_transport; [exact SOSTK | exact MU | exact WM | solve_appW]);
      assert (SOFMTc : sobj RNG mc A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU | exact WM | solve_appW]);
      assert (SOPFXc : sobj RNG mc 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU | exact WM | solve_appW]);
      assert (SOFc : sobj RNG mc Fp (Fp + 232)) by (eapply sobj_transport; [exact SOF | exact MU | exact WM | solve_appW])
    end.
    eapply implM_ms_eq; [eapply (vf_pass2u _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (f1 := set_w true [] (set_rbuf [] (set_w false [] (set_bufsize 80 f)))) | ms_eq].
    all: try first [ exact FL1 | apply flags_ok_ws; exact FL1 | exact IBc | exact APC2 | exact FRv | exact BY | unfold va_area; exact VAA | exact STc
                   | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2]
                   | exact ENVc | exact SOSTKc | exact SOFMTc | exact SOPFXc | exact SOFc | assumption ].
    all: try (lazymatch goal with |- rw_cells _ _ Fp ?cs1 => lazymatch type of FCt with rw_cells _ _ _ ?cs0 =>
                replace cs1 with cs0; [exact FCt|];
                unfold fcells, file_cells, wfn_of, lbf_of; cbn [f_wbuf f_fd f_stdoutw f_lbf_nl set_w set_rbuf set_bufsize]; unfold zlength; cbn [length Z.of_nat];
                rewrite ?unsigned_lit by lia; repeat fastfirst (first [reflexivity | (keep_hyps sp fmtz; lia) | progress f_equal]) end end).
    all: try (unfold fsink_inv; cbn [f_wactive f_rbuf f_bufsize f_nowr f_chan f_fd f_stdoutw set_w set_rbuf set_bufsize];
              split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact NW | split; [rewrite CHN; exact FD | split; [rewrite SWF; discriminate | exact CHN]]]]]]).
    all: try (cbn [f_wbuf set_w set_rbuf set_bufsize]; reflexivity).
    all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz; lia) | exact MU | exact WM | solve_appW | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz Fp; lia)).
    all: match goal with |- ?g => idtac "VFUB-LEFT:" g end.
    all: fail.
  Qed.
  End Sz23.
  Theorem vfprintf_ubf_spec : ltac:(let t := eval cbv delta [vfprintf_ubf_spec__stmt] in vfprintf_ubf_spec__stmt in exact t).
  Proof using FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL KLO IESF RSTK RIMG RVA RFP R0. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb. ltac2:(SecDiet.SzSec.closeP 'vfprintf_ubf_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End VfUbf.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.FP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.Printf_outsA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Lemma rwc_eqA : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H ->. exact H. Qed.
Ltac readdr H A' := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let H' := fresh in assert (H' : rw_cells asegs m A' cs) by (eapply rwc_eqA; [exact H | lia]); clear H; rename H' into H end.

Definition VFPRINTF : Z := 0x9b2c4.
Definition TOWRITE : Z := 0x9b064.
Definition VF_FRAME : Z := 368.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
  intros f c k Hk Hc. rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof. intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity. Qed.
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
  rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

(* [comment removed for export] *)
Definition flags_ok_clr_err__stmt : Prop := forall f (flags : word),
  flags_ok f flags -> flags_ok f (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)).
Section Sz6.
Variables f flags : ltac2:(SecDiet.SzSec.tyM 'flags_ok_clr_err__stmt "vv" @f).
#[using="Type"] Lemma flags_ok_clr_err__body : ltac2:(SecDiet.SzSec.bodyP 'flags_ok_clr_err__stmt "vv").
Proof.
  intros FL.
 pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R.
  pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583) as LR.
  unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *. rewrite unsigned_lit by lia.
  destruct FL as (A1 & A2 & A3 & A4 & A5 & A6).
  rewrite <- !Z.land_assoc.
  change (Z.land 18446744073709551583 4) with 4. change (Z.land 18446744073709551583 8) with 8.
  change (Z.land 18446744073709551583 16) with 16. change (Z.land 18446744073709551583 32) with 0.
  change (Z.land 18446744073709551583 64) with 64. change (Z.land 18446744073709551583 1) with 1.
  rewrite Z.land_0_r.
  repeat split; try reflexivity; rewrite land_low7, sx32_mod128, <- land_low7 by lia; assumption.
Qed.
End Sz6.
Lemma flags_ok_clr_err : ltac:(let t := eval cbv delta [flags_ok_clr_err__stmt] in flags_ok_clr_err__stmt in exact t).
Proof. intros f flags. ltac2:(SecDiet.SzSec.closeP 'flags_ok_clr_err__body "vv"). Qed.

(* [comment removed for export] *)
Lemma flags_ok_relw : forall f (flags : word), flags_ok f flags -> flags_ok f (sx32 flags).
Proof.
  intros f flags FL. unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *.
  destruct FL as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; rewrite land_low7, sx32_mod128, <- land_low7 by lia; assumption.
Qed.

Lemma flags_err_clear_lw : forall f (flags : word), flags_ok f flags -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof.
  intros f flags (_ & _ & _ & A4 & _). rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact A4.
Qed.
Lemma flags_nowr_clear : forall f (flags : word), flags_ok f flags -> f_nowr f = false -> Z.land (bv_unsigned flags) 8 = 0.
Proof. intros f flags (_ & A2 & _) NW. unfold F_NOWR in A2. rewrite NW in A2. exact A2. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Forall_disj_vff : forall (W : list (Z * Z)) lo sp Fp FS B BS a n,
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  (a + n <= lo \/ sp <= a) -> (a + n <= Fp \/ Fp + FS <= a) -> (a + n <= B \/ B + BS <= a) -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W lo sp Fp FS B BS a n H H1 H2 H3 Hn. induction H as [|[u1 u2] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.
Definition arg_ok_vff__stmt : Prop := forall RNG Fp FS B BS m m' lo sp sp' ap w a (W : list (Z * Z)),
  arg_ok Fp FS B BS RNG m lo sp ap w a -> sp' <= sp -> munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  arg_ok Fp FS B BS RNG m' lo sp' ap w a.
Section Sz11.
Variables RNG Fp FS B BS m m' lo sp sp' ap w a W : ltac2:(SecDiet.SzSec.tyM 'arg_ok_vff__stmt "vvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma arg_ok_vff__body : ltac2:(SecDiet.SzSec.bodyP 'arg_ok_vff__stmt "vvvvvvvvvvvvvv").
Proof.
  intros H Hsp MU WM AW HW.
 destruct a as [s|i|u|u]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & S47 & RGs & SOs). exists slack.
  split; [|repeat (split; [fastfirst (first [assumption | lia])|]); exact (sobj_transport _ _ _ _ _ _ SOs MU WM AW)].
  eapply bytes_at_transport; [exact BY | exact MU |].
  rewrite length_app, zb_length. cbn [length]. unfold zlength in *.
  eapply Forall_disj_vff; [exact HW | | | | lia]; lia.
Qed.
End Sz11.
Lemma arg_ok_vff : ltac:(let t := eval cbv delta [arg_ok_vff__stmt] in arg_ok_vff__stmt in exact t).
Proof. intros RNG Fp FS B BS m m' lo sp sp' ap w a W. ltac2:(SecDiet.SzSec.closeP 'arg_ok_vff__body "vvvvvvvvvvvvvv"). Qed.
Lemma args_ok_vff : forall RNG Fp FS B BS m m' lo sp sp' ap ws args (W : list (Z * Z)),
  args_ok Fp FS B BS RNG m lo sp ap ws args -> sp' <= sp -> munch W m m' -> wmono asegs m m' -> appW W ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= sp) \/ (Fp <= fst iv /\ snd iv <= Fp + FS) \/ (B <= fst iv /\ snd iv <= B + BS)) W ->
  args_ok Fp FS B BS RNG m' lo sp' ap ws args.
Proof.
  intros RNG Fp FS B BS m m' lo sp sp' ap ws args W. revert ws. induction args as [|a args IH]; intros ws H Hsp MU WM AW HW; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vff; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MonadFacts.
  Context {rc : runConstT}.
  Context {St : Type}.

  (* [comment removed for export] *)
  Lemma implM_bind_mret : forall {A} RNG (c : M St A) s Q ms,
    implAM RNG c s Q ms -> implAM RNG (mbind c mret) s Q ms.
  Proof using Type. pin_using tt.
    intros A RNG c s Q ms H. eapply implAM_bind; [exact H|]. intros a s' ms' HQ. apply implAM_ret. apply evtF_done. exact HQ.
  Qed.

  Lemma implM_ms_eq : forall {A} RNG (c : M St A) s Q ms ms', implAM RNG c s Q ms' -> ms = ms' -> implAM RNG c s Q ms.
  Proof using Type. pin_using tt. intros A RNG c s Q ms ms' H ->. exact H. Qed.
End MonadFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VfFile.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Variables (sw0 ch0 : bool).
  Let q := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FLOC : (685896 <= Fp /\ Fp + 232 <= 715256) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis BLOC : (6298112 <= B /\ B + 1024 <= GLOBALS_TOP) \/ (0 < B /\ B + 1024 <= lo /\ (B + 1024 <= 65536 \/ GLOBALS_TOP <= B)).
  Hypothesis FB : B + 1024 <= Fp \/ Fp + 232 <= B.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + 1024)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B 1024.

  #[local] Notation SINKf rpos rend := (SINK_file (St:=St) Fp B 1024 rpos rend closefn readfn seekfn prev next tail sw0 ch0).
  #[local] Notation OUTf := (OUT_file (St:=St)).

  (* [comment removed for export] *)
  Definition vfprintf_file_post (rpos rend : Z) (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fsink_inv 1024 sw0 ch0 f' /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (bufbytes' : list byte) (m' : mem) (rpos' rend' : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q); (Fp, Fp + 232); (B, B + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q
      /\ ssp_cells m' canary
      /\ rw_cells asegs m' Fp (fcells flags' rpos' rend' closefn (B + 1024) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B 1024 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ ((rpos' = rpos /\ rend' = rend) \/ (rpos' = 0 /\ rend' = 0))
      /\ flags_ok f' flags'
      /\ rw_cells asegs m' B [CB 1024%nat bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= 1024.

  (* [comment removed for export] *)
  Lemma sinkfacts : 0 <= Fp /\ 0 < B /\ 0 <= 1024 <= 1024 /\ B + 1024 <= 2^47 (* [comment removed for export] *) /\ Fp + 232 < 2^63
    /\ (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) /\ (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp)
    /\ (B + 1024 <= got_ssp \/ got_ssp + 8 <= B) /\ (B + 1024 <= ssp_guard \/ ssp_guard + 8 <= B).
  Proof using BLOC FLOC HVA LO fmtz. pin_using (fun (BLOC FLOC HVA LO fmtz : unit) => tt).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold got_ssp, ssp_guard, GLOBALS_TOP, VF_FRAME, PC_DEPTH, q, zlength in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition vf_pass2__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m m1 : mem) (f1 : file_st) (st : St)
      (flags flags1 mode1 : word) (bufbytes1 junk : list byte) (rpos rend rpos1 rend1 : Z),
    ((rpos1 = rpos /\ rend1 = rend) \/ (rpos1 = 0 /\ rend1 = 0)) ->
    rw_cells asegs m1 Fp (fcells flags1 rpos1 rend1 closefn (B + 1024) (B + zlength (f_wbuf f1)) B readfn (wfn_of f1) seekfn B 1024 prev next (f_fd f1) mode1 (lbf_of f1) tail) ->
    flags_ok f1 flags1 -> fsink_inv 1024 sw0 ch0 f1 ->
    rw_cells asegs m1 B [CB 1024%nat bufbytes1] -> firstn (length (f_wbuf f1)) bufbytes1 = to_bytes (f_wbuf f1) -> zlength (f_wbuf f1) <= 1024 ->
    rw_cells asegs m1 (q + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); CB 248 junk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                   C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at asegs m1 A (zb fmtz) -> va_area m1 VA slots -> args_ok Fp 232 B 1024 RNG m1 lo q (q + -368) slots args ->
    stk asegs m1 lo (q + -368) -> ssp_cells m1 canary -> mem_inv asegs m1 ->
    munch [(lo, q); (Fp, Fp + 232); (B, B + 1024)] m m1 -> wmono asegs m m1 ->
    Z.land (bv_unsigned (sx32 flags)) 32 = 0 ->
    icptenv m1 -> sobj RNG m1 lo q -> sobj RNG m1 A (A + zlength fmtz) -> sobj RNG m1 68460 68469 -> sobj RNG m1 Fp (Fp + 232) -> sobj RNG m1 B (B + 1024) ->
    implAM RNG (out_pieces f1 ps) st (vfprintf_file_post rpos rend m st)
      (MS (mkR x1 (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 0) (sx32 flags) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9b3b4) fc None m1 (seg_rom asegs)).
  Section Sz16.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 bufbytes1 junk rpos rend rpos1 rend1 : ltac2:(SecDiet.SzSec.tyM 'vf_pass2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma vf_pass2__body : ltac2:(SecDiet.SzSec.bodyP 'vf_pass2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL KLO IESF IESB RSTK RIMG RVA RFP RBUF. pin_using (fun (BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL KLO : unit) => tt).
    intros RP FC1 FL1 INV1 BUF1 BP1 WBL1 FR BY VAA AOK ST SSP MI MU WM OLDERR ENV1 SOSTK1 SOFMT1 SOPFX1 SOF1 SOB1.
    pose proof sinkfacts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB. pose proof (rw_CB_length _ _ _ _ BUF1) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof INV1 as (WA1 & RB1 & BS1 & NW1 & CH1 & SW1 & CN1).
    (* [comment removed for export] *)
    pose proof (printf_core_proof (at_nodeA asegs) (silA ASHM) (npeekA asegs) fstepS (file_st * St) Fp 232 Fp B 1024 (SINKf rpos1 rend1 st) TOPOK_file OUTf
                  (file_sink_frame Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K3 FB K6 K7 K8 K9)
                  (file_sink_flags Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K1 K5)
                  file_topok
                  (file_out Fp B 1024 rpos1 rend1 closefn readfn seekfn prev next tail sw0 ch0 st K1 K2 K3 K4 FB K6 K7 K8 K9 IESF IESB)) as PC2.
    unfold printf_core_stmt in PC2.
    set (PCQ := printf_core_post (St:=file_st * St) Fp 232 B 1024 (SINKf rpos1 rend1 st) (Z_to_bv 64 0x9b3cc) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp
                  (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 6298104) (Z_to_bv 64 1) (Z_to_bv 64 0) (sx32 flags) s6 s7 s8 s9 s10 s11 F fc
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -368) : word)) lo canary m1).
    apply (implAM_post_evt RNG (out_pieces f1 ps) st (fun f' st' ms' => PCQ r (f', st') ms')).
    { apply out_pieces_bridge; [exact SMALL|].
      eapply (printf_model_outsA OUTf RNG fmtz args ps r mret); [exact PIECES|].
      apply implM_bind_mret.
      apply implAM_from_evt. do 5 zs. zs. apply evtF_done.
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      replace (Z_to_bv 64 VA : word) with (Z_to_bv 64 (VA + 8 * 0) : word) in APC by (f_equal; lia).
      eapply implM_ms_eq; [eapply PC2 with (i := 0%Z) (slots := slots) | subst PCQ; ms_eq]; clear PC2; rewrite ?unsigned_lit by (keep_hyps sp A fmtz bufbytes1 HA lo LO GLO SPHI; lia);
        unfold PC_DEPTH, GLOBALS_TOP, TOPOK_file, zlength.
      all: match goal with |- ?g => fastfirst (first [ noevar_assumption |
             (* [comment removed for export] *) split; [reflexivity | split; [exact INV1 | exists flags1, mode1, bufbytes1; cbn [fst]; split; [exact FC1 | split; [exact FL1 | split; [exact BUF1 | split; [exact BP1 | exact WBL1]]]]]]
           | exact BY | exact HF | reflexivity | exact APC | exact VAA | exact I
           | cbn [skipn Z.to_nat]; eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes1; lia) | apply (munch_refl []) | apply wmono_refl | apply Forall_nil | constructor]
           | exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption
           | exact KLO | exact ENV1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact SOB1 | exact RIMG | exact RVA | exact RFP | exact RBUF
           | eapply sobj_sub; [exact SOSTK1 | (keep_hyps sp lo fmtz bufbytes1 LO; lia) | (keep_hyps sp VA fmtz slots bufbytes1 HVA lo LO; lia) | (keep_hyps sp fmtz bufbytes1; lia)]
           | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fmtz bufbytes1 LO; lia)]
           | eapply rng_sub'; [exact RIMG | (keep_hyps sp A fmtz bufbytes1 HA; lia)]
           | (keep_hyps sp VA fmtz slots bufbytes1 HVA Fp lo FLOC B GLO BLOC; lia)
           | idtac "VFP2-LEFT:" g; fail ]) end. }
    cbv beta. intros f' st' ms' PO. clear PC2. subst PCQ.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & -> & -> & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [_ FR]. cbn [cells_size csize Nat.add app] in FR.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
    clear BY VAA AOK BUF1 FC1.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
    fix_ret.
    destruct SNK3 as (EST3 & INV3 & flags3 & mode3 & bufbytes3 & FC3 & FL3 & BUF3 & BP3 & WBL3). cbn [fst snd] in EST3, INV3, FC3, FL3, BUF3, BP3, WBL3. subst st'.
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC3.
    (* [comment removed for export] *)
    zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 (sx32 flags3)) as FR3. unfold bv_modulus in FR3. cbn in FR3.
    zs. zs. rewrite (flags_err_clear_lw f' flags3 FL3). zs. rewrite OLDERR, Z.lor_0_r.
    zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA); CB 248 junk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                   C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
      [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact APC3|]; cbn [cells_size csize Nat.add app]; eapply rwc_eqA; [exact FR | lia]
      | clear APC3 FR ] end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evtF_done. unfold vfprintf_file_post, q. split; [reflexivity|]. split; [exact INV3|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [unfold fcells, file_cells; exact FC3|].
    split; [exact RP|].
    split; [apply flags_ok_relw; exact FL3|].
    split; [exact BUF3|]. split; [exact BP3| exact WBL3].
  Qed.
  End Sz16.
  Lemma vf_pass2 : ltac:(let t := eval cbv delta [vf_pass2__stmt] in vf_pass2__stmt in exact t).
  Proof using BLOC FB FLOC GLO HA HF HVA LO PIECES SMALL KLO IESF IESB RSTK RIMG RVA RFP RBUF. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 bufbytes1 junk rpos rend rpos1 rend1. ltac2:(SecDiet.SzSec.closeP 'vf_pass2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Ltac vff_ctx ENV SOSTK SOFMT SOPFX SOF SOB MU WM :=
    lazymatch type of MU with munch _ _ ?mc =>
      assert (ENVc : icptenv mc) by (eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe]);
      lazymatch type of SOSTK with sobj ?R _ ?a ?b => assert (SOSTKc : sobj R mc a b) by (eapply sobj_transport; [exact SOSTK | exact MU | exact WM | solve_appW]) end;
      lazymatch type of SOFMT with sobj ?R _ ?a ?b => assert (SOFMTc : sobj R mc a b) by (eapply sobj_transport; [exact SOFMT | exact MU | exact WM | solve_appW]) end;
      lazymatch type of SOPFX with sobj ?R _ ?a ?b => assert (SOPFXc : sobj R mc a b) by (eapply sobj_transport; [exact SOPFX | exact MU | exact WM | solve_appW]) end;
      lazymatch type of SOF with sobj ?R _ ?a ?b => assert (SOFc : sobj R mc a b) by (eapply sobj_transport; [exact SOF | exact MU | exact WM | solve_appW]) end;
      lazymatch type of SOB with sobj ?R _ ?a ?b => assert (SOBc : sobj R mc a b) by (eapply sobj_transport; [exact SOB | exact MU | exact WM | solve_appW]) end
    end.

  (* [comment removed for export] *)
  Lemma flags_ok_set_w : forall f fl act wb, flags_ok f fl -> flags_ok (set_w act wb (set_rbuf [] f)) fl.
  Proof using Type. pin_using tt. intros f fl act wb FL. unfold flags_ok in *. cbn. exact FL. Qed.

  Definition vfprintf_file_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells asegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at asegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 B 1024 RNG m lo q (q - VF_FRAME) slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) -> sobj RNG m B (B + 1024) ->
    implAM RNG (vfprintf f ps) st (vfprintf_file_post rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom asegs)).
  Section Sz18.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend : ltac2:(SecDiet.SzSec.tyM 'vfprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_file_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_file_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL KLO IESF IESB RSTK RIMG RVA RFP RBUF. pin_using (fun (BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL KLO : unit) => tt).
 intros -> -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY VAA AOK ST SSP MI ENV SOSTK SOFMT SOPFX SOF SOB.
    pose proof (sobj_appW _ _ _ _ SOF) as APWF. pose proof (sobj_appW _ _ _ _ SOB) as APWB.
    pose proof sinkfacts as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    unfold fcells, file_cells in FC0.
    pose proof (rw_CB_length _ _ _ _ BUF0) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    (* [comment removed for export] *)
    unfold vfprintf. rewrite BS. change (1024 =? 0) with false. cbv iota.
    (* [comment removed for export] *)
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash FC0. stash BUF0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    apply implAM_from_evt.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB asegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg _ _ _ => apply (proj1 (rw_cells_app sg _ _ [_;_;_] _)) in FR end.
    destruct FR as [FRlo FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    lazymatch type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -104)%Z in FRhi by lia end.
    do 12 zs. do 14 zs.
    lazymatch type of FRlo with rw_cells ?sg ?mm ?A ?cs1 => lazymatch type of FRhi with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in FRhi by (cbn [cells_size csize Nat.add]; lia);
      pose proof (proj2 (rw_cells_app sg mm A cs1 cs2) (conj FRlo FRhi)) as FR; clear FRlo FRhi end end.
    cbn [app] in FR.
    unfold hide in FC0, BUF0.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call asegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (B, B + 1024)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; (keep_hyps sp Fp B lo x H; lia) | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; (keep_hyps sp A lo fmtz GLO HA; lia)];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA; (keep_hyps sp VA lo slots HVA; lia)]
    end.
    clear MUp. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evtF_cut.
    { eapply PC1; rewrite ?unsigned_lit by (keep_hyps sp A fmtz bufbytes HA lo LO GLO SPHI; lia); unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | (keep_hyps sp lo fmtz bufbytes LO; lia) | (keep_hyps sp lo fmtz bufbytes GLO; lia) | (keep_hyps sp VA fmtz slots bufbytes HVA; lia)
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | (keep_hyps sp A fmtz bufbytes HA; lia) | (keep_hyps sp fmtz bufbytes; lia) | (keep_hyps sp fmtz bufbytes SPHI; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fmtz bufbytes; lia)] | exact RIMG | eapply rng_sub'; [exact RIMG | (keep_hyps sp A fmtz bufbytes HA; lia)] ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. first [if_lit | brf Kb; [exfalso; revert Kb; cbn; rewrite ?unsigned_lit by lia; cbn; lia|]]. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    unfold hide in AOK, VAAm. clear BYm VAA. unfold va_area in VAAm.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (VAA : va_area mc VA slots)
        by (unfold va_area; eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA FLOC BLOC GLO LO SPHI NNs; lia]) end.
    clear VAAm.
    pose proof (flags_ok_clr_err f flags FL0) as FL1.
    pose proof (flags_err_clear_lw f flags FL0) as OLDERR.
    destruct (f_wactive f) eqn:WACT.
    - (* [comment removed for export] *)
      zs. brf Kw; [| exfalso; revert Kw; rewrite ?unsigned_lit by lia; lia].
      apply evtF_done. unfold ensure_w. rewrite WACT. apply implM_retb.
      vff_ctx ENV SOSTK SOFMT SOPFX SOF SOB MU WM.
      eapply implM_ms_eq; [eapply (vf_pass2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (rpos := rpos) (rend := rend) | ms_eq].
      all: try first [ left; split; reflexivity | exact FC0 | exact FL1 | exact BUF0 | exact BP0 | exact WBL | exact FR | exact BY | exact VAA | unfold va_area; exact VAA | exact STc
                     | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2]
                     | exact ENVc | exact SOSTKc | exact SOFMTc | exact SOPFXc | exact SOFc | exact SOBc | assumption ].
      all: try (split; [exact WACT | split; [exact RB | split; [exact BS | split; [exact NW | split; [exact CH | split; [exact SWB | exact CHN]]]]]]).
      all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes; lia) | exact MU | exact WM | solve_appW | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz bufbytes Fp B; lia)).
      all: match goal with |- ?g => idtac "VFB1-LEFT:" g end.
      all: fail.
    - (* [comment removed for export] *)
      zs. brf Kw; [exfalso; revert Kw; rewrite ?unsigned_lit by lia; lia |].
      zs. zs. zs. (* [comment removed for export] *)
      specialize (WB0 eq_refl).
      eapply evtF_cut.
      { pose proof (flags_nowr_clear _ _ FL1 ltac:(cbn; exact NW)) as X8.
        eapply evt_ms_eq; [eapply towrite_specZ | ms_eq].
        all: first [ exact FC0 | exact X8 | assumption | lia | match goal with |- ?g => idtac "TW-LEFT:" g end ]. }
      cbv beta. intros ms' PO.
      destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & mode' & m'' & -> & MUc & WMc & MIt & FCt).
      clear FC0. unfold va_area in VAA.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      fix_ret.
      zs. if_lit. (* [comment removed for export] *)
      apply evtF_done. unfold ensure_w, towrite. rewrite WACT, NW. apply implM_retb.
      vff_ctx ENV SOSTK SOFMT SOPFX SOF SOB MU WM.
      eapply implM_ms_eq; [eapply (vf_pass2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (rpos := rpos) (rend := rend) (f1 := set_w true [] (set_rbuf [] f)) | ms_eq].
      all: try first [ right; split; reflexivity | exact FL1 | apply flags_ok_set_w; exact FL1 | exact BUF0 | exact WBL | exact FR | exact BY | exact VAA | unfold va_area; exact VAA | exact STc
                     | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2]
                     | exact ENVc | exact SOSTKc | exact SOFMTc | exact SOPFXc | exact SOFc | exact SOBc | assumption ].
      all: try (cbn [f_wbuf set_w set_rbuf zlength length Z.of_nat]; rewrite Z.add_0_r; unfold fcells, wfn_of, lbf_of; cbn; unfold wfn_of, lbf_of in FCt; exact FCt).
      all: try (split; [reflexivity | split; [reflexivity | split; [exact BS | split; [exact NW | split; [exact CH | split; [exact SWB | exact CHN]]]]]]).
      all: try (cbn [f_wbuf set_w set_rbuf length]; reflexivity).
      all: try (cbn [f_wbuf set_w set_rbuf]; unfold zlength; cbn [length Z.of_nat]; (keep_hyps sp fmtz bufbytes; lia)).
      all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz bufbytes; lia) | exact MU | exact WM | solve_appW | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz bufbytes Fp B; lia)).
      all: match goal with |- ?g => idtac "VFB2-LEFT:" g end.
      all: fail.
  Qed.
  End Sz18.
  Theorem vfprintf_file_spec : ltac:(let t := eval cbv delta [vfprintf_file_spec__stmt] in vfprintf_file_spec__stmt in exact t).
  Proof using BLOC FB FLOC GLO HA HF HVA LO P1 PIECES SMALL KLO IESF IESB RSTK RIMG RVA RFP RBUF. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode bufbytes rpos rend. ltac2:(SecDiet.SzSec.closeP 'vfprintf_file_spec__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End VfFile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VfUbf.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B0 : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word).
  Let q := bv_unsigned sp.
  Let Bi := q - 352.   (* [comment removed for export] *)
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VF_FRAME - PC_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.   (* [comment removed for export] *)
  Hypothesis FLOC : (685896 <= Fp /\ Fp + 232 <= 715256) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis HB0 : 0 < B0 < 2^64.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis R0 : rng0 RNG.

  #[local] Notation SINKu rpos rend := (SINK_file (St:=St) Fp Bi 80 rpos rend closefn readfn seekfn prev next tail false true).

  Definition vfprintf_ubf_post (m : mem) (st : St) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = [] /\ f_bufsize f' = 0 /\
      exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q); (Fp, Fp + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q
      /\ ssp_cells m' canary
      /\ rw_cells asegs m' Fp (fcells flags' 0 0 closefn 0 0 0 readfn (wfn_of f') seekfn B0 0 prev next (f_fd f') mode' (lbf_of f') tail)
      /\ flags_ok f' flags'.

  Lemma sinkfacts_u : 0 <= Fp /\ 0 < Bi /\ 0 <= 80 <= 1024 /\ Bi + 80 <= 2^47 (* [comment removed for export] *) /\ Fp + 232 < 2^63 /\ (Bi + 80 <= Fp \/ Fp + 232 <= Bi)
    /\ (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) /\ (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp)
    /\ (Bi + 80 <= got_ssp \/ got_ssp + 8 <= Bi) /\ (Bi + 80 <= ssp_guard \/ ssp_guard + 8 <= Bi).
  Proof using FLOC GLO HVA LO fmtz. pin_using (fun (FLOC GLO HVA LO fmtz : unit) => tt).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold got_ssp, ssp_guard, GLOBALS_TOP, VF_FRAME, PC_DEPTH, q, Bi, zlength in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma flags_ok_ws : forall f fl act wb n, flags_ok f fl -> flags_ok (set_w act wb (set_bufsize n f)) fl.
  Proof using Type. pin_using tt. intros f fl act wb n FL. unfold flags_ok in *. cbn. exact FL. Qed.
  Lemma flags_ok_ws' : forall f fl act wb n, flags_ok (set_w act wb (set_bufsize n f)) fl -> flags_ok f fl.
  Proof using Type. pin_using tt. intros f fl act wb n FL. unfold flags_ok in *. cbn in FL. exact FL. Qed.

  (* [comment removed for export] *)
  Definition vf_pass2u__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m m1 : mem) (f1 : file_st) (st : St)
      (flags flags1 mode1 : word) (ibuf rest : list byte),
    rw_cells asegs m1 Fp (fcells flags1 0 0 closefn (Bi + 80) (Bi + zlength (f_wbuf f1)) Bi readfn (wfn_of f1) seekfn Bi 80 prev next (f_fd f1) mode1 (lbf_of f1) tail) ->
    flags_ok f1 flags1 -> fsink_inv 80 false true f1 -> f_wbuf f1 = [] ->
    rw_cells asegs m1 Bi [CB 80%nat ibuf] ->
    rw_cells asegs m1 (q + -368) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA)] ->
    rw_cells asegs m1 (q + -272) [CB 168 rest; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                 C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at asegs m1 A (zb fmtz) -> va_area m1 VA slots -> args_ok Fp 232 Bi 80 RNG m1 lo q (q + -368) slots args ->
    stk asegs m1 lo (q + -368) -> ssp_cells m1 canary -> mem_inv asegs m1 ->
    munch [(lo, q); (Fp, Fp + 232)] m m1 -> wmono asegs m m1 ->
    Z.land (bv_unsigned (sx32 flags)) 32 = 0 ->
    icptenv m1 -> sobj RNG m1 lo q -> sobj RNG m1 A (A + zlength fmtz) -> sobj RNG m1 68460 68469 -> sobj RNG m1 Fp (Fp + 232) ->
    implAM RNG (f2 <- out_pieces f1 ps ;; f3 <- file_writefn f2 [] ;; mret (set_w false [] (set_bufsize 0 f3))) st (vfprintf_ubf_post m st)
      (MS (mkR x1 (Z_to_bv 64 (q + -368)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 B0) (sx32 flags) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9b3b4) fc None m1 (seg_rom asegs)).
  Section Sz22.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 ibuf rest : ltac2:(SecDiet.SzSec.tyM 'vf_pass2u__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma vf_pass2u__body : ltac2:(SecDiet.SzSec.bodyP 'vf_pass2u__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FLOC GLO HA HB0 HF HVA LO PIECES SMALL KLO IESF RSTK RIMG RVA RFP R0. pin_using (fun (FLOC GLO HA HB0 HF HVA LO PIECES SMALL KLO : unit) => tt).
    intros FC1 FL1 INV1 WB1 BUF1 APC2 FR BY VAA AOK ST SSP MI MU WM OLDERR ENV1 SOSTK1 SOFMT1 SOPFX1 SOF1.
    pose proof sinkfacts_u as (K1 & K2 & K3 & K4 & K5 & KFB & K6 & K7 & K8 & K9).
    assert (IESBi : iesafe [(Bi, Bi + 80)]) by (apply iesafe_one_high; unfold Bi, q, VF_FRAME, PC_DEPTH, KHIGH in *; lia).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB. pose proof (rw_CB_length _ _ _ _ BUF1) as LBB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof INV1 as (WA1 & RB1 & BS1 & NW1 & CH1 & SW1 & CN1).
    (* [comment removed for export] *)
    pose proof (printf_core_proof (at_nodeA asegs) (silA ASHM) (npeekA asegs) fstepS (file_st * St) Fp 232 Fp Bi 80 (SINKu 0 0 st) TOPOK_file (OUT_file (St:=St))
                  (file_sink_frame Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K3 KFB K6 K7 K8 K9)
                  (file_sink_flags Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K1 K5)
                  file_topok
                  (file_out Fp Bi 80 0 0 closefn readfn seekfn prev next tail false true st K1 K2 K3 K4 KFB K6 K7 K8 K9 IESF IESBi)) as PC2.
    unfold printf_core_stmt in PC2.
    set (PCQ := printf_core_post (St:=file_st * St) Fp 232 Bi 80 (SINKu 0 0 st) (Z_to_bv 64 0x9b3cc) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp
                  (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 6298104) (Z_to_bv 64 1) (Z_to_bv 64 B0) (sx32 flags) s6 s7 s8 s9 s10 s11 F fc
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -368) : word)) lo canary m1).
    unfold q, Bi in *.
    eapply implAM_bind with (Q1 := fun f' st' ms' => PCQ r (f', st') ms').
    { { apply out_pieces_bridge; [exact SMALL|].
        eapply (printf_model_outsA (OUT_file (St:=St)) RNG fmtz args ps r mret); [exact PIECES|].
        apply implM_bind_mret.
        apply implAM_from_evt. do 5 zs. zs. apply evtF_done.
        apply (proj1 (rw_cells_app asegs _ _ [_] _)) in APC2. destruct APC2 as [APC AP2]. cbn [cells_size csize Nat.add app] in AP2.
        replace (Z_to_bv 64 VA : word) with (Z_to_bv 64 (VA + 8 * 0) : word) in APC by (f_equal; lia).
        assert (SNK : SINK_file Fp (bv_unsigned sp - 352) 80 0 0 closefn readfn seekfn prev next tail false true st m1 (f1, st)).
        { split; [reflexivity|]. split; [exact INV1|]. exists flags1, mode1, ibuf. cbn [fst].
          split; [exact FC1|]. split; [exact FL1|]. split; [exact BUF1|]. rewrite WB1. split; [reflexivity| unfold zlength; cbn; lia]. }
        eapply implM_ms_eq; [eapply PC2 with (i := 0%Z) (slots := slots) | subst PCQ; ms_eq]; clear PC2; rewrite ?unsigned_lit by (keep_hyps sp A fmtz ibuf HA lo LO GLO SPHI; lia);
          unfold PC_DEPTH, GLOBALS_TOP, TOPOK_file, zlength.
        all: match goal with |- ?g => fastfirst (first [ noevar_assumption |
               exact SNK
             | exact BY | exact HF | reflexivity | exact APC | exact VAA | unfold va_area; exact VAA | exact I
             | cbn [skipn Z.to_nat]; eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz ibuf; lia) | apply (munch_refl []) | apply wmono_refl | apply Forall_nil | constructor]
             | exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption
             | exact KLO | exact ENV1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact RIMG | exact RVA | exact RFP
             | eapply sobj_sub; [exact SOSTK1 | (keep_hyps sp lo fmtz ibuf LO; lia) | (keep_hyps sp fmtz ibuf K4 VA slots HVA lo LO; lia) | (keep_hyps sp fmtz ibuf; lia)]
             | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fmtz ibuf LO; lia)]
             | eapply rng_sub'; [exact RIMG | (keep_hyps sp A fmtz ibuf HA; lia)]
             | (keep_hyps sp fmtz ibuf K4 Fp VA lo slots FLOC HVA; lia)
             | idtac "VFU2-LEFT:" g; fail ]) end. } }
    cbv beta. intros f2 st2 ms2 PO. clear PC2. subst PCQ.
    unfold printf_core_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & -> & -> & ST3 & SNK3 & SSP3 & APC3 & Hr).
    unfold SR in MUc. cbn [app] in MUc.
    clear BY VAA AOK BUF1 FC1.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in APC2. destruct APC2 as [_ AP2]. cbn [cells_size csize Nat.add app] in AP2.
    replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in AP2 by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
    destruct SNK3 as (EST3 & INV3 & flags3 & mode3 & bufbytes3 & FC3 & FL3 & BUF3 & BP3 & WBL3). cbn [fst snd] in EST3, INV3, FC3, FL3, BUF3, BP3, WBL3. subst st2.
    pose proof INV3 as (WA3 & RB3 & BS3 & NW3 & CH3 & SW3 & CN3).
    clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (SWF : f_stdoutw f2 = false) by (destruct (f_stdoutw f2) eqn:E; [discriminate (SW3 eq_refl) | reflexivity]).
    assert (WFN : wfn_of f2 = F_STDIO_WRITE) by (unfold wfn_of; rewrite SWF; reflexivity).
    rewrite CN3 in CH3.
    pose proof (rw_CB_length _ _ _ _ BUF3) as LB3.
    assert (NNw : 0 <= zlength (f_wbuf f2)) by (unfold zlength; lia).
    pose proof (CB_prefix_bytes_at m3 (bv_unsigned sp - 352) (Z.to_nat 80) bufbytes3 (to_bytes (f_wbuf f2)) BUF3 ltac:(rewrite length_to_bytes; exact BP3)) as WBB.
    unfold fcells, file_cells in FC3. rewrite WFN in FC3. unfold F_STDIO_WRITE in FC3.
    apply implAM_from_evt. fix_ret.
    (* [comment removed for export] *)
    zs. zs. zs. brf Kb; [exfalso; revert Kb; rewrite ?unsigned_lit by lia; lia|].
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs.
    apply evtF_done. unfold file_writefn. rewrite SWF.
    eapply implAM_bind.
    { eapply implM_ms_eq;
        [eapply (stdio_write_spec (St:=St) RNG) with (f := f2) (s := []) (S := 0) (lo := lo) (canary := canary) (Fp := Fp) (flags := flags3)
           (rpos := 0) (rend := 0) (closefn := closefn) (wend := bv_unsigned sp - 352 + 80) (readfn := readfn) (writefn := 631440) (seekfn := seekfn)
           (B := bv_unsigned sp - 352) (bufsize := 80) (prev := prev) (next := next) (mode := mode3) (lbf := lbf_of f2) (tail := tail)
        | unfold F_STDIO_WRITE; ms_eq].
      all: rewrite ?unsigned_lit by lia.
      all: match goal with |- ?g => fastfirst (first
             [ noevar_assumption | unfold fcells, file_cells; exact FC3 | exact WBB | apply bytes_at_nil; (keep_hyps sp fmtz ibuf bufbytes3; lia) | reflexivity | rewrite CN3; exact CH3 | exact ST3 | exact MI3
             | split; [exact SSP1 | exact SSP2] | left; reflexivity
             | exact RFP | exact RIMG | apply (rng0_use _ _ R0); (keep_hyps sp lo fmtz ibuf bufbytes3 LO GLO SPHI; lia)
             | eapply rng_sub'; [exact RSTK | unfold STDIO_WRITE_DEPTH, zlength in *; (keep_hyps sp lo fmtz ibuf bufbytes3 f2 LO WBL3; lia)]
             | unfold STDIO_WRITE_DEPTH, got_ssp, ssp_guard, zlength in *; cbn [length Z.of_nat] in *; (keep_hyps sp lo fmtz ibuf bufbytes3 LO K4 Fp B0 GLO FLOC K6 K7 SPHI VA slots f2 HVA WBL3 KFB; lia)
             | idtac "SWCALL-LEFT:" g; fail ]) end. }
    cbv beta. intros f3 st3 ms3 PO.
    destruct PO as (-> & -> & w5 & w6 & w7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w28 & w29 & w30 & w31 & m4 & -> & MUc & WMc & MI4 & ST4 & FC4 & SSP4).
    unfold sw_W, STDIO_WRITE_DEPTH in MUc. rewrite !unsigned_lit in MUc, ST4 by lia.
    clear FC3 WBB.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
    apply implAM_ret. fix_ret.
    clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold fcells, file_cells in FC4.
    (* [comment removed for export] *)
    zs. zs. zs. zs. zs.
    zs. replace (0 <? bv_unsigned sp - 352)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    zs. zs. rewrite ?Z.lor_0_l. zs.
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 (sx32 flags3)) as FR3. unfold bv_modulus in FR3. cbn in FR3.
    zs. zs. rewrite (flags_err_clear_lw f2 flags3 FL3). zs. rewrite OLDERR, Z.lor_0_r.
    zs. zs. zs. zs. zs. if_lit.
    (* [comment removed for export] *)
    zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 9 zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with AP : rw_cells _ mm (bv_unsigned sp + -368)%Z [C8 ?apv'], B3 : rw_cells _ mm (q - 352)%Z [CB _ ?bb], R : rw_cells _ mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
      assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv'] ++ [C8 (Z_to_bv 64 VA)] ++ [CB (Z.to_nat 80) bb] ++ rest));
      [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact AP2 | lia]|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact B3 | unfold q; lia]|]; cbn [cells_size csize Nat.add Z.to_nat Pos.to_nat Pos.iter_op Nat.mul];
        eapply rwc_eqA; [exact R | lia]
      | clear AP AP2 B3 R ] end end.
    cbn [app] in FALL.
    match goal with H : stk _ _ lo (bv_unsigned sp + -368)%Z |- _ => release_frame FALL H (bv_unsigned sp) end.
    apply evtF_done. unfold vfprintf_ubf_post, q. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [cbn; exact RB3|]. split; [reflexivity|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|].
    split; [split; [exact SSP1 | exact SSP2]|].
    split; [unfold fcells, file_cells; cbn [f_fd set_w set_bufsize]; unfold wfn_of, lbf_of in *; cbn [f_stdoutw f_lbf_nl set_w set_bufsize]; rewrite SWF; unfold F_STDIO_WRITE; exact FC4|].
    apply flags_ok_ws. apply flags_ok_relw. exact FL3.
  Qed.
  End Sz22.
  Lemma vf_pass2u : ltac:(let t := eval cbv delta [vf_pass2u__stmt] in vf_pass2u__stmt in exact t).
  Proof using FLOC GLO HA HB0 HF HVA LO PIECES SMALL KLO IESF RSTK RIMG RVA RFP R0. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m m1 f1 st flags flags1 mode1 ibuf rest. ltac2:(SecDiet.SzSec.closeP 'vf_pass2u__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition vfprintf_ubf_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (rpos rend we wp wb : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn we wp wb readfn (wfn_of f) seekfn B0 0 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags -> f_bufsize f = 0 -> f_nowr f = false -> f_rbuf f = [] -> f_wbuf f = [] ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_stdoutw f = false ->
    0 <= we < 2^64 -> 0 <= wp < 2^64 -> 0 <= wb < 2^64 -> 0 <= rpos < 2^64 -> 0 <= rend < 2^64 ->
    bytes_at asegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 Bi 80 RNG m lo q (q - VF_FRAME) slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) ->
    implAM RNG (vfprintf f ps) st (vfprintf_ubf_post m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF) fc None m (seg_rom asegs)).
  Section Sz23.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb : ltac2:(SecDiet.SzSec.tyM 'vfprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma vfprintf_ubf_spec__body : ltac2:(SecDiet.SzSec.bodyP 'vfprintf_ubf_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL KLO IESF RSTK RIMG RVA RFP R0. pin_using (fun (FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL KLO : unit) => tt).
 intros -> -> -> FC0 FL0 BS NW RB WB CHN FD SWF Rwe Rwp Rwb Rrp Rre BY VAA AOK ST SSP MI ENV SOSTK SOFMT SOPFX SOF.
    pose proof (sobj_appW _ _ _ _ SOF) as APWF.
    pose proof sinkfacts_u as (K1 & K2 & K3 & K4 & K5 & KFB & K6 & K7 & K8 & K9).
    unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, got_ssp, ssp_guard in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold q, Bi in *.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmtz) as LZB. rewrite LZB in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    unfold fcells, file_cells in FC0.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    unfold zlength in HA, HVA, NNf, NNs.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
    (* [comment removed for export] *)
    unfold vfprintf. rewrite BS. change (0 =? 0) with true. cbv iota.
    pose proof BY as BYm. pose proof VAA as VAAm.
    stash FC0. stash BY. stash VAA. stash AOK. stash BYm. stash VAAm.
    unfold VFPRINTF.
    apply implAM_from_evt.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells asegs ?mm ?A [CB 368 ?j] |- _ =>
        apply (rw_cells_split_CB asegs mm A [] 368 j [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg _ _ _ => apply (proj1 (rw_cells_app sg _ _ [_;_;_] _)) in FR end.
    destruct FR as [FRlo FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
    lazymatch type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -104)%Z in FRhi by lia end.
    do 12 zs. do 14 zs.
    lazymatch type of FRlo with rw_cells ?sg ?mm ?A ?cs1 => lazymatch type of FRhi with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A + Z.of_nat (cells_size cs1))%Z in FRhi by (cbn [cells_size csize Nat.add]; lia);
      pose proof (proj2 (rw_cells_app sg mm A cs1 cs2) (conj FRlo FRhi)) as FR; clear FRlo FRhi end end.
    cbn [app] in FR.
    unfold hide in FC0.
    lazymatch type of MUp with munch ?Wp ?ma ?mb =>
      transport_after_call asegs ma mb MUp WM;
      assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z ma mb)
        by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; clear -SPHI; intros; lia | exact MUp]);
      unfold hide in BY, VAA;
      eapply (bytes_at_transport _ Wp ma mb) in BY; [| exact MUp | cbn [disjoint_from]; rewrite zb_length; clear -HA GLO; lia];
      unfold va_area in VAA;
      eapply (bytes_at_transport _ Wp ma mb) in VAA; [| exact MUp | cbn [disjoint_from]; rewrite u64s_length; clear -HVA; lia]
    end.
    clear MUp. stash VAA.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evtF_cut.
    { eapply PC1; rewrite ?unsigned_lit by (keep_hyps sp A fmtz HA lo LO GLO SPHI; lia); unfold PC_DEPTH, GLOBALS_TOP, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | (keep_hyps sp lo fmtz LO; lia) | (keep_hyps sp lo fmtz GLO; lia) | (keep_hyps sp fmtz K4; lia)
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | (keep_hyps sp A fmtz HA; lia) | (keep_hyps sp fmtz; lia) | (keep_hyps sp fmtz SPHI; lia)
        | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo fmtz; lia)] | exact RIMG | eapply rng_sub'; [exact RIMG | (keep_hyps sp A fmtz HA; lia)] ]. }
    cbv beta. intros ms' PO. clear PC1. unfold printf_core1_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    zs. zs. first [if_lit | brf Kl; [|exfalso; revert Kl; cbn; rewrite ?unsigned_lit by lia; cbn; lia]]. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. if_lit. (* [comment removed for export] *)
    do 8 zs. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    unfold hide in AOK, VAAm. clear BYm VAA. unfold va_area in VAAm.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (VAA : bytes_at asegs mc VA (u64s slots))
        by (eapply bytes_at_transport; [exact VAAm | exact MU | cbn [disjoint_from]; rewrite u64s_length; clear -HVA FLOC GLO LO SPHI NNs; lia]) end.
    clear VAAm.
    pose proof (flags_ok_clr_err f flags FL0) as FL1.
    pose proof (flags_err_clear_lw f flags FL0) as OLDERR.
    pose proof (flags_nowr_clear _ _ FL1 ltac:(cbn; exact NW)) as X8.
    eapply evtF_cut.
    { eapply evt_ms_eq; [eapply towrite_specZ | ms_eq].
      all: first [ exact FC0 | exact X8 | assumption | lia | match goal with |- ?g => idtac "TWU-LEFT:" g end ]. }
    cbv beta. intros ms' PO.
    destruct PO as (y5 & y6 & y7 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y28 & y29 & y30 & y31 & mode' & m'' & -> & MUc & WMc & MIt & FCt).
    clear FC0.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
    fix_ret.
    zs. if_lit. (* [comment removed for export] *)
    apply evtF_done. unfold towrite. cbn [f_nowr set_w set_bufsize]. rewrite NW. apply implM_retb.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ _ (bv_unsigned sp + -368)%Z (_ :: _ :: CB 248 _ :: _) |- _ => rename H into FRv end.
    apply (rw_cells_split_CB asegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_; _] _)) in FRv. destruct FRv as [APC2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [IBc FRv]. cbn [cells_size csize Nat.add app] in FRv.
    readdr IBc (bv_unsigned sp - 352)%Z. readdr FRv (bv_unsigned sp + -272)%Z.
    lazymatch type of MU with munch _ _ ?mc =>
      assert (ENVc : icptenv mc) by (eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe]);
      assert (SOSTKc : sobj RNG mc lo (bv_unsigned sp)) by (eapply sobj_transport; [exact SOSTK | exact MU | exact WM | solve_appW]);
      assert (SOFMTc : sobj RNG mc A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU | exact WM | solve_appW]);
      assert (SOPFXc : sobj RNG mc 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU | exact WM | solve_appW]);
      assert (SOFc : sobj RNG mc Fp (Fp + 232)) by (eapply sobj_transport; [exact SOF | exact MU | exact WM | solve_appW])
    end.
    eapply implM_ms_eq; [eapply (vf_pass2u _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) with (f1 := set_w true [] (set_rbuf [] (set_w false [] (set_bufsize 80 f)))) | ms_eq].
    all: try first [ exact FL1 | apply flags_ok_ws; exact FL1 | exact IBc | exact APC2 | exact FRv | exact BY | unfold va_area; exact VAA | exact STc
                   | exact MU | exact WM | exact OLDERR | split; [exact SSP1 | exact SSP2]
                   | exact ENVc | exact SOSTKc | exact SOFMTc | exact SOPFXc | exact SOFc | assumption ].
    all: try (lazymatch goal with |- rw_cells _ _ Fp ?cs1 => lazymatch type of FCt with rw_cells _ _ _ ?cs0 =>
                replace cs1 with cs0; [exact FCt|];
                unfold fcells, file_cells, wfn_of, lbf_of; cbn [f_wbuf f_fd f_stdoutw f_lbf_nl set_w set_rbuf set_bufsize]; unfold zlength; cbn [length Z.of_nat];
                rewrite ?unsigned_lit by lia; repeat fastfirst (first [reflexivity | (keep_hyps sp fmtz; lia) | progress f_equal]) end end).
    all: try (unfold fsink_inv; cbn [f_wactive f_rbuf f_bufsize f_nowr f_chan f_fd f_stdoutw set_w set_rbuf set_bufsize];
              split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact NW | split; [rewrite CHN; exact FD | split; [rewrite SWF; discriminate | exact CHN]]]]]]).
    all: try (cbn [f_wbuf set_w set_rbuf set_bufsize]; reflexivity).
    all: try (eapply args_ok_vff; [exact AOK | (keep_hyps sp fmtz; lia) | exact MU | exact WM | solve_appW | ]; repeat constructor; cbn [fst snd]; (keep_hyps sp lo fmtz Fp; lia)).
    all: match goal with |- ?g => idtac "VFUB-LEFT:" g end.
    all: fail.
  Qed.
  End Sz23.
  Theorem vfprintf_ubf_spec : ltac:(let t := eval cbv delta [vfprintf_ubf_spec__stmt] in vfprintf_ubf_spec__stmt in exact t).
  Proof using FLOC GLO HA HB0 HF HVA LO P1 PIECES SMALL KLO IESF RSTK RIMG RVA RFP R0. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m f st flags mode rpos rend we wp wb. ltac2:(SecDiet.SzSec.closeP 'vfprintf_ubf_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End VfUbf.
End TwB.
End F_vfprintf_file.

(* [comment removed for export] *)
Module I_vfprintf_top.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.F_vfprintf_file OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition VFPRINTF_STUB : Z := 0x444a0.
Definition VFPRINTF_I_DEPTH : Z := 5600.   (* [comment removed for export] *)

Section VfFileI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Variables (sw0 ch0 : bool).
  Let q := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VFPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.
  Hypothesis FLOC : (684904 <= Fp /\ Fp + 232 <= 714232) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis BLOC : (6297088 <= B /\ B + 1024 <= GLOBALS_TOP) \/ (0 < B /\ B + 1024 <= lo /\ (B + 1024 <= 65536 \/ GLOBALS_TOP <= B)).
  Hypothesis FB : B + 1024 <= Fp \/ Fp + 232 <= B.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + 1024)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B 1024.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem vfprintf_i_file_spec : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells asegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at asegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 B 1024 RNG m lo q (q - 416) slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) -> sobj RNG m B (B + 1024) ->
    pargs_okL RNG lo sp m its (Z_to_bv 64 VA) ->
    implAM RNG (vfprintf f ps) st (vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HF P1 PIECES SMALL LO GLO HA HVA FLOC BLOC FB KLO IESF IESB RSTK RIMG RVA RFP RBUF FSTR NOZ EF OK.
    pin_using (fun (HF P1 PIECES SMALL LO GLO HA HVA FLOC BLOC FB KLO : unit) => tt).
    intros until rend. intros -> -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY VAA AOK ST SSP MI ENV CKP SOSTK SOFMT SOPFX SOF SOB PAOK.
    unfold VFPRINTF_I_DEPTH, VFPRINTF_STUB, GLOBALS_TOP in *. subst q.
    pose proof (sobj_appW _ _ _ _ SOF) as APWF. pose proof (sobj_appW _ _ _ _ SOB) as APWB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC0) as FBD. unfold fcells in FBD. rewrite file_cells_size in FBD.
    pose proof (rw_cells_bound _ _ _ _ BUF0) as BBD. cbn [cells_size csize Nat.add] in BBD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    apply implAM_from_evt.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vfprintf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PAOK ]. }
    cbv beta. intros ms1 MID. unfold vfprintf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & j16 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -2368, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC0 | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 B [CB 1024%nat bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF0 | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (VAA1 : va_area m1 VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAA | exact MU1 | cbn [disjoint_from]; rewrite u64s_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (AOK1 : args_ok Fp 232 B 1024 RNG m1 lo (bv_unsigned sp + -48) (bv_unsigned sp + -48 - VF_FRAME) slots args).
    { unfold VF_FRAME. replace (bv_unsigned sp + -48 - 368) with (bv_unsigned sp - 416) by lia.
      eapply args_ok_vff; [exact AOK | lia | exact MU1 | exact WM1 | exact AW1 |]. constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -48)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOF1 : sobj RNG m1 Fp (Fp + 232)) by (eapply sobj_transport; [exact SOF | exact MU1 | exact WM1 | exact AW1]).
    assert (SOB1 : sobj RNG m1 B (B + 1024)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | exact AW1]).
    apply evtF_done.
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (vfprintf_file_spec (St:=St) RNG (Z_to_bv 64 0x47dd4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 Fp) (Z_to_bv 64 VA)
                s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail A VA lo fmtz slots args ps r canary sw0 ch0)
        with (f := f) (flags := flags) (mode := mode) (bufbytes := bufbytes) (rpos := rpos) (rend := rend);
        rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP;
        first [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact FLOC | exact BLOC | exact FB | exact KLO | exact IESF | exact IESB | exact RIMG | exact RVA | exact RFP | exact RBUF
              | reflexivity | exact FC1 | exact FL0 | exact BUF1 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
              | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact ENV1 | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact SOB1
              | eapply rng_sub'; [exact RSTK | lia]
              | unfold zlength in *; lia ]. }
    cbv beta. intros f' st' ms2 PO. unfold vfprintf_file_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m2 & rpos' & rend'
                     & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & FC2 & RP2 & FL2 & BUF2 & BP2 & WBL2).
    (* [comment removed for export] *)
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -48) [CB 16 j16; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    replace (ret_pc (Z_to_bv 64 0x47dd4)) with (Z_to_bv 64 0x47dd4 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vfprintf_i_post RNG) with (j16 := j16); rewrite ?unsigned_lit by lia; [exact MI2 | exact FR2 | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms3 ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in SK by lia.
    apply evtF_done. unfold vfprintf_file_post. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact FC2|]. split; [exact RP2|]. split; [exact FL2|]. split; [exact BUF2|]. split; [exact BP2 | exact WBL2].
  Qed.
End VfFileI.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.F_vfprintf_file.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition VFPRINTF_STUB : Z := 0x44508.
Definition VFPRINTF_I_DEPTH : Z := 5600.   (* [comment removed for export] *)

Section VfFileI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Variables (sw0 ch0 : bool).
  Let q := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= q - VFPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HVA : q <= VA /\ VA + 8 * zlength slots <= 2^47.
  Hypothesis FLOC : (685896 <= Fp /\ Fp + 232 <= 715256) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis BLOC : (6298112 <= B /\ B + 1024 <= GLOBALS_TOP) \/ (0 < B /\ B + 1024 <= lo /\ (B + 1024 <= 65536 \/ GLOBALS_TOP <= B)).
  Hypothesis FB : B + 1024 <= Fp \/ Fp + 232 <= B.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + 1024)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B 1024.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem vfprintf_i_file_spec : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells asegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at asegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 B 1024 RNG m lo q (q - 416) slots args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) -> sobj RNG m B (B + 1024) ->
    pargs_okL RNG lo sp m its (Z_to_bv 64 VA) ->
    implAM RNG (vfprintf f ps) st (vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VFPRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HF P1 PIECES SMALL LO GLO HA HVA FLOC BLOC FB KLO IESF IESB RSTK RIMG RVA RFP RBUF FSTR NOZ EF OK.
    pin_using (fun (HF P1 PIECES SMALL LO GLO HA HVA FLOC BLOC FB KLO : unit) => tt).
    intros until rend. intros -> -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY VAA AOK ST SSP MI ENV CKP SOSTK SOFMT SOPFX SOF SOB PAOK.
    unfold VFPRINTF_I_DEPTH, VFPRINTF_STUB, GLOBALS_TOP in *. subst q.
    pose proof (sobj_appW _ _ _ _ SOF) as APWF. pose proof (sobj_appW _ _ _ _ SOB) as APWB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC0) as FBD. unfold fcells in FBD. rewrite file_cells_size in FBD.
    pose proof (rw_cells_bound _ _ _ _ BUF0) as BBD. cbn [cells_size csize Nat.add] in BBD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    pose proof (va_area_bound _ _ _ VAA) as VAB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia). assert (NNs : 0 <= zlength slots) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    apply implAM_from_evt.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vfprintf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PAOK ]. }
    cbv beta. intros ms1 MID. unfold vfprintf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & j16 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -2368, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC0 | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 B [CB 1024%nat bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF0 | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (VAA1 : va_area m1 VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAA | exact MU1 | cbn [disjoint_from]; rewrite u64s_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (AOK1 : args_ok Fp 232 B 1024 RNG m1 lo (bv_unsigned sp + -48) (bv_unsigned sp + -48 - VF_FRAME) slots args).
    { unfold VF_FRAME. replace (bv_unsigned sp + -48 - 368) with (bv_unsigned sp - 416) by lia.
      eapply args_ok_vff; [exact AOK | lia | exact MU1 | exact WM1 | exact AW1 |]. constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -48)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOF1 : sobj RNG m1 Fp (Fp + 232)) by (eapply sobj_transport; [exact SOF | exact MU1 | exact WM1 | exact AW1]).
    assert (SOB1 : sobj RNG m1 B (B + 1024)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | exact AW1]).
    apply evtF_done.
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (vfprintf_file_spec (St:=St) RNG (Z_to_bv 64 0x47e3c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 Fp) (Z_to_bv 64 VA)
                s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail A VA lo fmtz slots args ps r canary sw0 ch0)
        with (f := f) (flags := flags) (mode := mode) (bufbytes := bufbytes) (rpos := rpos) (rend := rend);
        rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP;
        first [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact FLOC | exact BLOC | exact FB | exact KLO | exact IESF | exact IESB | exact RIMG | exact RVA | exact RFP | exact RBUF
              | reflexivity | exact FC1 | exact FL0 | exact BUF1 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
              | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact ENV1 | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact SOB1
              | eapply rng_sub'; [exact RSTK | lia]
              | unfold zlength in *; lia ]. }
    cbv beta. intros f' st' ms2 PO. unfold vfprintf_file_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m2 & rpos' & rend'
                     & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & FC2 & RP2 & FL2 & BUF2 & BP2 & WBL2).
    (* [comment removed for export] *)
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -48) [CB 16 j16; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    replace (ret_pc (Z_to_bv 64 0x47e3c)) with (Z_to_bv 64 0x47e3c : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vfprintf_i_post RNG) with (j16 := j16); rewrite ?unsigned_lit by lia; [exact MI2 | exact FR2 | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms3 ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in SK by lia.
    apply evtF_done. unfold vfprintf_file_post. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact FC2|]. split; [exact RP2|]. split; [exact FL2|]. split; [exact BUF2|]. split; [exact BP2 | exact WBL2].
  Qed.
End VfFileI.
End TwB.
End I_vfprintf_top.

(* [comment removed for export] *)
Module I_fprintf_top.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_mkstemp__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.F_vfprintf_file OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_mkstemp__A3S.I_snprintf_top.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FPRINTF_STUB : Z := 0x444ac.
Definition FPRINTF_I_DEPTH : Z := 5664.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FprintfFileI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (a2 a3 a4 a5 a6 a7 : word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Variables (sw0 ch0 : bool).
  Let p := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - FPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis FLOC : (684904 <= Fp /\ Fp + 232 <= 714232) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis BLOC : (6297088 <= B /\ B + 1024 <= GLOBALS_TOP) \/ (0 < B /\ B + 1024 <= lo /\ (B + 1024 <= 65536 \/ GLOBALS_TOP <= B)).
  Hypothesis FB : B + 1024 <= Fp \/ Fp + 232 <= B.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + 1024)].
  Hypothesis RSTK : rng RNG lo (p - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B 1024.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem fprintf_i_file_spec : forall (t0 t1 t2 a0 a1 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells asegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at asegs m A (zb fmtz) -> args_ok Fp 232 B 1024 RNG m lo p (p - 480) [a2; a3; a4; a5; a6; a7] args ->
    stk asegs m lo p -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo p -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) -> sobj RNG m B (B + 1024) ->
    pwords_ok RNG lo sp m its [a2; a3; a4; a5; a6; a7] ->
    implAM RNG (vfprintf f ps) st (vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FPRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HF P1 PIECES SMALL LO GLO PHI HA FLOC BLOC FB KLO IESF IESB RSTK RIMG RFP RBUF FSTR NOZ EF OK.
    pin_using (fun (HF P1 PIECES SMALL LO GLO PHI HA FLOC BLOC FB KLO : unit) => tt).
    intros until rend. intros -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY AOK ST SSP MI ENV CKP SOSTK SOFMT SOPFX SOF SOB PWOK.
    unfold FPRINTF_I_DEPTH, FPRINTF_STUB, GLOBALS_TOP in *. subst p.
    pose proof (sobj_appW _ _ _ _ SOF) as APWF. pose proof (sobj_appW _ _ _ _ SOB) as APWB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC0) as FBD. unfold fcells in FBD. rewrite file_cells_size in FBD.
    pose proof (rw_cells_bound _ _ _ _ BUF0) as BBD. cbn [cells_size csize Nat.add] in BBD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    apply implAM_from_evt.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fprintf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PWOK ]. }
    cbv beta. intros ms1 MID. unfold fprintf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & j32 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -2432, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC0 | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 B [CB 1024%nat bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF0 | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (AOK1 : args_ok Fp 232 B 1024 RNG m1 lo (bv_unsigned sp + -112) (bv_unsigned sp + -112 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args).
    { unfold VF_FRAME. replace (bv_unsigned sp + -112 - 368) with (bv_unsigned sp - 480) by lia.
      eapply args_ok_vff; [exact AOK | lia | exact MU1 | exact WM1 | exact AW1 |]. constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -112)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOF1 : sobj RNG m1 Fp (Fp + 232)) by (eapply sobj_transport; [exact SOF | exact MU1 | exact WM1 | exact AW1]).
    assert (SOB1 : sobj RNG m1 B (B + 1024)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | exact AW1]).
    (* [comment removed for export] *)
    pose proof FR1 as FRc.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in VAc by lia.
    pose proof (va_area_of_cells m1 (bv_unsigned sp + -48) [a2; a3; a4; a5; a6; a7] VAc) as VAA1.
    apply evtF_done.
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (vfprintf_file_spec (St:=St) RNG (Z_to_bv 64 0x482cc) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 Fp) (Z_to_bv 64 (bv_unsigned sp + -48))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail A (bv_unsigned sp + -48) lo fmtz [a2; a3; a4; a5; a6; a7] args ps r canary sw0 ch0)
        with (f := f) (flags := flags) (mode := mode) (bufbytes := bufbytes) (rpos := rpos) (rend := rend);
        rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP;
        first [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact FLOC | exact BLOC | exact FB | exact KLO | exact IESF | exact IESB | exact RIMG | exact RFP | exact RBUF
              | reflexivity | exact FC1 | exact FL0 | exact BUF1 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
              | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact ENV1 | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact SOB1
              | eapply rng_sub'; [exact RSTK | unfold zlength; cbn [length]; lia]
              | unfold zlength in *; cbn [length] in *; lia ]. }
    cbv beta. intros f' st' ms2 PO. unfold vfprintf_file_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m2 & rpos' & rend'
                     & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & FC2 & RP2 & FL2 & BUF2 & BP2 & WBL2).
    (* [comment removed for export] *)
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -112) ([CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra] ++ [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7])).
    { cbn [app]. eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    replace (ret_pc (Z_to_bv 64 0x482cc)) with (Z_to_bv 64 0x482cc : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fprintf_i_post RNG) with (j32 := j32); rewrite ?unsigned_lit by lia; [exact MI2 | exact FR2 | reflexivity | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms3 ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    cbn [app] in FR2.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -112 + Z.of_nat 112) with (bv_unsigned sp) in SK by lia.
    apply evtF_done. unfold vfprintf_file_post. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact FC2|]. split; [exact RP2|]. split; [exact FL2|]. split; [exact BUF2|]. split; [exact BP2 | exact WBL2].
  Qed.
End FprintfFileI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FprintfUbfI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B0 : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (a2 a3 a4 a5 a6 a7 : word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Let p := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - FPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis FLOC : (684904 <= Fp /\ Fp + 232 <= 714232) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis HB0 : 0 < B0 < 2^64.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis RSTK : rng RNG lo (p - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis R0 : rng0 RNG.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem fprintf_i_ubf_spec : forall (t0 t1 t2 a0 a1 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (rpos rend we wp wb : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn we wp wb readfn (wfn_of f) seekfn B0 0 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags -> f_bufsize f = 0 -> f_nowr f = false -> f_rbuf f = [] -> f_wbuf f = [] ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_stdoutw f = false ->
    0 <= we < 2^64 -> 0 <= wp < 2^64 -> 0 <= wb < 2^64 -> 0 <= rpos < 2^64 -> 0 <= rend < 2^64 ->
    bytes_at asegs m A (zb fmtz) -> args_ok Fp 232 (p - 464) 80 RNG m lo p (p - 480) [a2; a3; a4; a5; a6; a7] args ->
    stk asegs m lo p -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo (p - 112) ->   (* [comment removed for export] *) sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) ->
    pwords_ok RNG lo sp m its [a2; a3; a4; a5; a6; a7] ->
    implAM RNG (vfprintf f ps) st (vfprintf_ubf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B0 closefn readfn seekfn prev next tail lo canary m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FPRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HF P1 PIECES SMALL LO GLO PHI HA FLOC HB0 KLO IESF RSTK RIMG RFP R0 FSTR NOZ EF OK.
    pin_using (fun (HF P1 PIECES SMALL LO GLO PHI HA FLOC HB0 KLO : unit) => tt).
    intros until wb. intros -> -> FC0 FL0 BS NW RB WB CHN FD SWF Rwe Rwp Rwb Rrp Rre BY AOK ST SSP MI ENV CKP SOSTK SOFMT SOPFX SOF PWOK.
    unfold FPRINTF_I_DEPTH, FPRINTF_STUB, GLOBALS_TOP in *. subst p.
    pose proof (sobj_appW _ _ _ _ SOF) as APWF.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC0) as FBD. unfold fcells in FBD. rewrite file_cells_size in FBD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    apply implAM_from_evt.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fprintf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PWOK ]. }
    cbv beta. intros ms1 MID. unfold fprintf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & j32 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -2432, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rpos rend closefn we wp wb readfn (wfn_of f) seekfn B0 0 prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC0 | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (AOK1 : args_ok Fp 232 (bv_unsigned sp + -112 - 352) 80 RNG m1 lo (bv_unsigned sp + -112) (bv_unsigned sp + -112 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args).
    { unfold VF_FRAME. replace (bv_unsigned sp + -112 - 368) with (bv_unsigned sp - 480) by lia. replace (bv_unsigned sp + -112 - 352) with (bv_unsigned sp - 464) by lia.
      eapply args_ok_vff; [exact AOK | lia | exact MU1 | exact WM1 | exact AW1 |]. constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -112)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOF1 : sobj RNG m1 Fp (Fp + 232)) by (eapply sobj_transport; [exact SOF | exact MU1 | exact WM1 | exact AW1]).
    pose proof FR1 as FRc.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in VAc by lia.
    pose proof (va_area_of_cells m1 (bv_unsigned sp + -48) [a2; a3; a4; a5; a6; a7] VAc) as VAA1.
    apply evtF_done.
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (vfprintf_ubf_spec (St:=St) RNG (Z_to_bv 64 0x482cc) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 Fp) (Z_to_bv 64 (bv_unsigned sp + -48))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B0 closefn readfn seekfn prev next tail A (bv_unsigned sp + -48) lo fmtz [a2; a3; a4; a5; a6; a7] args ps r canary)
        with (f := f) (flags := flags) (mode := mode) (rpos := rpos) (rend := rend) (we := we) (wp := wp) (wb := wb);
        rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP;
        first [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact FLOC | exact HB0 | exact KLO | exact IESF | exact RIMG | exact RFP | exact R0
              | reflexivity | exact FC1 | exact FL0 | exact BS | exact NW | exact RB | exact WB | exact CHN | exact FD | exact SWF | exact Rwe | exact Rwp | exact Rwb | exact Rrp | exact Rre
              | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact ENV1 | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOF1
              | eapply rng_sub'; [exact RSTK | unfold zlength; cbn [length]; lia]
              | unfold zlength in *; cbn [length] in *; lia ]. }
    cbv beta. intros f' st' ms2 PO. unfold vfprintf_ubf_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (-> & WA' & WB' & RB' & BS' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & m2
                     & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & FC2 & FL2).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -112) ([CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra] ++ [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7])).
    { cbn [app]. eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    replace (ret_pc (Z_to_bv 64 0x482cc)) with (Z_to_bv 64 0x482cc : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fprintf_i_post RNG) with (j32 := j32); rewrite ?unsigned_lit by lia; [exact MI2 | exact FR2 | reflexivity | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms3 ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    cbn [app] in FR2.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -112 + Z.of_nat 112) with (bv_unsigned sp) in SK by lia.
    apply evtF_done. unfold vfprintf_ubf_post. split; [reflexivity|]. split; [exact WA'|]. split; [exact WB'|]. split; [exact RB'|]. split; [exact BS'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact FC2 | exact FL2].
  Qed.
End FprintfUbfI.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.F_vfprintf_file.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_mkstemp__A3S.I_snprintf_top.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FPRINTF_STUB : Z := 0x44514.
Definition FPRINTF_I_DEPTH : Z := 5664.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FprintfFileI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (a2 a3 a4 a5 a6 a7 : word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Variables (sw0 ch0 : bool).
  Let p := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - FPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis FLOC : (685896 <= Fp /\ Fp + 232 <= 715256) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis BLOC : (6298112 <= B /\ B + 1024 <= GLOBALS_TOP) \/ (0 < B /\ B + 1024 <= lo /\ (B + 1024 <= 65536 \/ GLOBALS_TOP <= B)).
  Hypothesis FB : B + 1024 <= Fp \/ Fp + 232 <= B.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + 1024)].
  Hypothesis RSTK : rng RNG lo (p - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B 1024.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem fprintf_i_file_spec : forall (t0 t1 t2 a0 a1 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells asegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at asegs m A (zb fmtz) -> args_ok Fp 232 B 1024 RNG m lo p (p - 480) [a2; a3; a4; a5; a6; a7] args ->
    stk asegs m lo p -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo p -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) -> sobj RNG m B (B + 1024) ->
    pwords_ok RNG lo sp m its [a2; a3; a4; a5; a6; a7] ->
    implAM RNG (vfprintf f ps) st (vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FPRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HF P1 PIECES SMALL LO GLO PHI HA FLOC BLOC FB KLO IESF IESB RSTK RIMG RFP RBUF FSTR NOZ EF OK.
    pin_using (fun (HF P1 PIECES SMALL LO GLO PHI HA FLOC BLOC FB KLO : unit) => tt).
    intros until rend. intros -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY AOK ST SSP MI ENV CKP SOSTK SOFMT SOPFX SOF SOB PWOK.
    unfold FPRINTF_I_DEPTH, FPRINTF_STUB, GLOBALS_TOP in *. subst p.
    pose proof (sobj_appW _ _ _ _ SOF) as APWF. pose proof (sobj_appW _ _ _ _ SOB) as APWB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC0) as FBD. unfold fcells in FBD. rewrite file_cells_size in FBD.
    pose proof (rw_cells_bound _ _ _ _ BUF0) as BBD. cbn [cells_size csize Nat.add] in BBD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    apply implAM_from_evt.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fprintf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PWOK ]. }
    cbv beta. intros ms1 MID. unfold fprintf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & j32 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -2432, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC0 | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 B [CB 1024%nat bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF0 | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (AOK1 : args_ok Fp 232 B 1024 RNG m1 lo (bv_unsigned sp + -112) (bv_unsigned sp + -112 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args).
    { unfold VF_FRAME. replace (bv_unsigned sp + -112 - 368) with (bv_unsigned sp - 480) by lia.
      eapply args_ok_vff; [exact AOK | lia | exact MU1 | exact WM1 | exact AW1 |]. constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -112)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOF1 : sobj RNG m1 Fp (Fp + 232)) by (eapply sobj_transport; [exact SOF | exact MU1 | exact WM1 | exact AW1]).
    assert (SOB1 : sobj RNG m1 B (B + 1024)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | exact AW1]).
    (* [comment removed for export] *)
    pose proof FR1 as FRc.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in VAc by lia.
    pose proof (va_area_of_cells m1 (bv_unsigned sp + -48) [a2; a3; a4; a5; a6; a7] VAc) as VAA1.
    apply evtF_done.
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (vfprintf_file_spec (St:=St) RNG (Z_to_bv 64 0x48334) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 Fp) (Z_to_bv 64 (bv_unsigned sp + -48))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail A (bv_unsigned sp + -48) lo fmtz [a2; a3; a4; a5; a6; a7] args ps r canary sw0 ch0)
        with (f := f) (flags := flags) (mode := mode) (bufbytes := bufbytes) (rpos := rpos) (rend := rend);
        rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP;
        first [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact FLOC | exact BLOC | exact FB | exact KLO | exact IESF | exact IESB | exact RIMG | exact RFP | exact RBUF
              | reflexivity | exact FC1 | exact FL0 | exact BUF1 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
              | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact ENV1 | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact SOB1
              | eapply rng_sub'; [exact RSTK | unfold zlength; cbn [length]; lia]
              | unfold zlength in *; cbn [length] in *; lia ]. }
    cbv beta. intros f' st' ms2 PO. unfold vfprintf_file_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m2 & rpos' & rend'
                     & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & FC2 & RP2 & FL2 & BUF2 & BP2 & WBL2).
    (* [comment removed for export] *)
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -112) ([CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra] ++ [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7])).
    { cbn [app]. eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    replace (ret_pc (Z_to_bv 64 0x48334)) with (Z_to_bv 64 0x48334 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fprintf_i_post RNG) with (j32 := j32); rewrite ?unsigned_lit by lia; [exact MI2 | exact FR2 | reflexivity | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms3 ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    cbn [app] in FR2.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -112 + Z.of_nat 112) with (bv_unsigned sp) in SK by lia.
    apply evtF_done. unfold vfprintf_file_post. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact FC2|]. split; [exact RP2|]. split; [exact FL2|]. split; [exact BUF2|]. split; [exact BP2 | exact WBL2].
  Qed.
End FprintfFileI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FprintfUbfI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp B0 : Z) (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (a2 a3 a4 a5 a6 a7 : word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Let p := bv_unsigned sp.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - FPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis FLOC : (685896 <= Fp /\ Fp + 232 <= 715256) \/ (0 < Fp /\ Fp + 232 <= lo /\ (Fp + 232 <= 65536 \/ GLOBALS_TOP <= Fp)).
  Hypothesis HB0 : 0 < B0 < 2^64.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis RSTK : rng RNG lo (p - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis R0 : rng0 RNG.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem fprintf_i_ubf_spec : forall (t0 t1 t2 a0 a1 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (rpos rend we wp wb : Z),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn we wp wb readfn (wfn_of f) seekfn B0 0 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags -> f_bufsize f = 0 -> f_nowr f = false -> f_rbuf f = [] -> f_wbuf f = [] ->
    f_chan f = true -> (f_fd f = 1 \/ f_fd f = 2) -> f_stdoutw f = false ->
    0 <= we < 2^64 -> 0 <= wp < 2^64 -> 0 <= wb < 2^64 -> 0 <= rpos < 2^64 -> 0 <= rend < 2^64 ->
    bytes_at asegs m A (zb fmtz) -> args_ok Fp 232 (p - 464) 80 RNG m lo p (p - 480) [a2; a3; a4; a5; a6; a7] args ->
    stk asegs m lo p -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo (p - 112) ->   (* [comment removed for export] *) sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) ->
    pwords_ok RNG lo sp m its [a2; a3; a4; a5; a6; a7] ->
    implAM RNG (vfprintf f ps) st (vfprintf_ubf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B0 closefn readfn seekfn prev next tail lo canary m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FPRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HF P1 PIECES SMALL LO GLO PHI HA FLOC HB0 KLO IESF RSTK RIMG RFP R0 FSTR NOZ EF OK.
    pin_using (fun (HF P1 PIECES SMALL LO GLO PHI HA FLOC HB0 KLO : unit) => tt).
    intros until wb. intros -> -> FC0 FL0 BS NW RB WB CHN FD SWF Rwe Rwp Rwb Rrp Rre BY AOK ST SSP MI ENV CKP SOSTK SOFMT SOPFX SOF PWOK.
    unfold FPRINTF_I_DEPTH, FPRINTF_STUB, GLOBALS_TOP in *. subst p.
    pose proof (sobj_appW _ _ _ _ SOF) as APWF.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC0) as FBD. unfold fcells in FBD. rewrite file_cells_size in FBD.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    apply implAM_from_evt.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fprintf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PWOK ]. }
    cbv beta. intros ms1 MID. unfold fprintf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & j32 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -2432, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rpos rend closefn we wp wb readfn (wfn_of f) seekfn B0 0 prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC0 | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (AOK1 : args_ok Fp 232 (bv_unsigned sp + -112 - 352) 80 RNG m1 lo (bv_unsigned sp + -112) (bv_unsigned sp + -112 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args).
    { unfold VF_FRAME. replace (bv_unsigned sp + -112 - 368) with (bv_unsigned sp - 480) by lia. replace (bv_unsigned sp + -112 - 352) with (bv_unsigned sp - 464) by lia.
      eapply args_ok_vff; [exact AOK | lia | exact MU1 | exact WM1 | exact AW1 |]. constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -112)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOF1 : sobj RNG m1 Fp (Fp + 232)) by (eapply sobj_transport; [exact SOF | exact MU1 | exact WM1 | exact AW1]).
    pose proof FR1 as FRc.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in VAc by lia.
    pose proof (va_area_of_cells m1 (bv_unsigned sp + -48) [a2; a3; a4; a5; a6; a7] VAc) as VAA1.
    apply evtF_done.
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (vfprintf_ubf_spec (St:=St) RNG (Z_to_bv 64 0x48334) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 Fp) (Z_to_bv 64 (bv_unsigned sp + -48))
                s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B0 closefn readfn seekfn prev next tail A (bv_unsigned sp + -48) lo fmtz [a2; a3; a4; a5; a6; a7] args ps r canary)
        with (f := f) (flags := flags) (mode := mode) (rpos := rpos) (rend := rend) (we := we) (wp := wp) (wb := wb);
        rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP;
        first [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact FLOC | exact HB0 | exact KLO | exact IESF | exact RIMG | exact RFP | exact R0
              | reflexivity | exact FC1 | exact FL0 | exact BS | exact NW | exact RB | exact WB | exact CHN | exact FD | exact SWF | exact Rwe | exact Rwp | exact Rwb | exact Rrp | exact Rre
              | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact ENV1 | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOF1
              | eapply rng_sub'; [exact RSTK | unfold zlength; cbn [length]; lia]
              | unfold zlength in *; cbn [length] in *; lia ]. }
    cbv beta. intros f' st' ms2 PO. unfold vfprintf_ubf_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (-> & WA' & WB' & RB' & BS' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & m2
                     & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & FC2 & FL2).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -112) ([CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra] ++ [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7])).
    { cbn [app]. eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    replace (ret_pc (Z_to_bv 64 0x48334)) with (Z_to_bv 64 0x48334 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fprintf_i_post RNG) with (j32 := j32); rewrite ?unsigned_lit by lia; [exact MI2 | exact FR2 | reflexivity | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms3 ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    cbn [app] in FR2.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -112 + Z.of_nat 112) with (bv_unsigned sp) in SK by lia.
    apply evtF_done. unfold vfprintf_ubf_post. split; [reflexivity|]. split; [exact WA'|]. split; [exact WB'|]. split; [exact RB'|]. split; [exact BS'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact FC2 | exact FL2].
  Qed.
End FprintfUbfI.
End TwB.
End I_fprintf_top.

(* [comment removed for export] *)
Module I_printf_top.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_mlib__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_mkstemp__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.F_vfprintf_file OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_mkstemp__A3S.I_snprintf_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_vfprintf_top.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PRINTF_STUB : Z := 0x444a8.
Definition VPRINTF_STUB : Z := 0x4449c.
Definition PRINTF_I_DEPTH : Z := 5712.   (* [comment removed for export] *)
Definition VPRINTF_I_DEPTH : Z := 5648.  (* [comment removed for export] *)

Section PrintfI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (a1 a2 a3 a4 a5 a6 a7 : word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Variables (sw0 ch0 : bool).
  Let p := bv_unsigned sp.
  Let Fp := A_STDOUT.
  Let B := A_STDOUT_BUF.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - PRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis RSTK : rng RNG lo (p - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RBUF : rng RNG B 1024.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem printf_i_spec : forall (t0 t1 t2 a0 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 A ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells asegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at asegs m A (zb fmtz) -> args_ok Fp 232 B 1024 RNG m lo p (p - 528) [a1; a2; a3; a4; a5; a6; a7] args ->
    stk asegs m lo p -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo p -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) -> sobj RNG m B (B + 1024) ->
    pwords_ok RNG lo sp m its [a1; a2; a3; a4; a5; a6; a7] ->
    implAM RNG (vfprintf f ps) st (vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HF P1 PIECES SMALL LO GLO PHI HA KLO RSTK RIMG RBUF FSTR NOZ EF OK.
    intros until rend. intros -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY AOK ST SSP MI ENV CKP SOSTK SOFMT SOPFX SOF SOB PWOK.
    unfold PRINTF_I_DEPTH, PRINTF_STUB, GLOBALS_TOP in *. subst p Fp B. unfold A_STDOUT, A_STDOUT_BUF in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    apply implAM_from_evt.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (printf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PWOK ]. }
    cbv beta. intros ms1 MID. unfold printf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & j24 & j8 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -2432, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    pose proof (rw_cells_bound _ _ _ _ FC0) as FBD. unfold fcells in FBD. rewrite file_cells_size in FBD.
    assert (FC1 : rw_cells asegs m1 695440 (fcells flags rpos rend closefn (if f_wactive f then 6299856 + 1024 else 0) (if f_wactive f then 6299856 + zlength (f_wbuf f) else 0) (if f_wactive f then 6299856 else 0)
                           readfn (wfn_of f) seekfn 6299856 1024 prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC0 | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 6299856 [CB 1024%nat bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF0 | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (CKP1 : rt_ckpf m1).
    { eapply (rw_cells_transport asegs _ m m1); [exact CKP | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (AOK1 : args_ok 695440 232 6299856 1024 RNG m1 lo (bv_unsigned sp + -112) (bv_unsigned sp + -112 - 416) [a1; a2; a3; a4; a5; a6; a7] args).
    { replace (bv_unsigned sp + -112 - 416) with (bv_unsigned sp - 528) by lia.
      eapply args_ok_vff; [exact AOK | lia | exact MU1 | exact WM1 | exact AW1 |]. constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -112)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOF1 : sobj RNG m1 695440 (695440 + 232)) by (eapply sobj_transport; [exact SOF | exact MU1 | exact WM1 | exact AW1]).
    assert (SOB1 : sobj RNG m1 6299856 (6299856 + 1024)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | exact AW1]).
    (* [comment removed for export] *)
    pose proof FR1 as FRc. cbn [app] in FRc.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -112 + Z.of_nat 56) with (bv_unsigned sp + -56) in VAc by lia.
    pose proof (va_area_of_cells m1 (bv_unsigned sp + -56) [a1; a2; a3; a4; a5; a6; a7] VAc) as VAA1.
    assert (PWOK1 : pwords_ok RNG lo (Z_to_bv 64 (bv_unsigned sp + -112)) m1 its [a1; a2; a3; a4; a5; a6; a7]).
    { eapply pwords_ok_transport; [exact PWOK | exact MU1 | exact WM1 | exact AW1
                                  | eapply pstrs_sep_stack; [exact PWOK | constructor; [cbn [fst snd]; lia | constructor]]
                                  | rewrite unsigned_lit by lia; lia]. }
    assert (PAOK1 : pargs_okL RNG lo (Z_to_bv 64 (bv_unsigned sp + -112)) m1 its (Z_to_bv 64 (bv_unsigned sp + -56))).
    { eapply (pargs_okL_of_words RNG lo _ m1 its [a1; a2; a3; a4; a5; a6; a7]);
        [exact PWOK1 | exact VAc | rewrite unsigned_lit by lia; lia | cbn [length]; lia | cbn [length]; eapply rng_sub'; [exact RSTK | lia]]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    do 6 zstep. zstep.
    apply evtF_done.
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (vfprintf_i_file_spec (St:=St) RNG (Z_to_bv 64 0x481d0) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 (bv_unsigned sp + -56))
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 695440 6299856 closefn readfn seekfn prev next tail A (bv_unsigned sp + -56) lo fmtz [a1; a2; a3; a4; a5; a6; a7] args ps r canary
                fstr its sw0 ch0)
        with (f := f) (flags := flags) (mode := mode) (bufbytes := bufbytes) (rpos := rpos) (rend := rend);
        rewrite ?unsigned_lit by lia; unfold VFPRINTF_I_DEPTH, GLOBALS_TOP;
        first [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OK
              | reflexivity | exact FC1 | exact FL0 | exact BUF1 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
              | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact ENV1 | exact CKP1 | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact SOB1
              | exact PAOK1
              | (unfold iesafe; cbn [disjoint_from]; repeat split; lia)
              | eapply rng_sub'; [exact RSTK | unfold zlength; cbn [length]; lia]
              | eapply rng_sub'; [exact RIMG | lia]
              | (left; lia)
              | unfold zlength in *; cbn [length] in *; lia ]. }
    cbv beta. intros f' st' ms2 PO. unfold vfprintf_file_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m2 & rpos' & rend'
                     & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & FC2 & RP2 & FL2 & BUF2 & BP2 & WBL2).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -112) ([CB 24 j24; C8 s1; C8 s0; C8 ra] ++ [CB 8 j8; C8 a1; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7])).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [app disjoint_from cells_size csize Nat.add]; lia]. }
    replace (ret_pc (Z_to_bv 64 0x481d0)) with (Z_to_bv 64 0x481d0 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (printf_i_post RNG) with (j24 := j24); rewrite ?unsigned_lit by lia; [exact MI2 | exact FR2 | reflexivity | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms3 ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    cbn [app] in FR2.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -112 + Z.of_nat 112) with (bv_unsigned sp) in SK by lia.
    apply evtF_done. unfold vfprintf_file_post. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact FC2|]. split; [exact RP2|]. split; [exact FL2|]. split; [exact BUF2|]. split; [exact BP2 | exact WBL2].
  Qed.
End PrintfI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VprintfI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Variables (sw0 ch0 : bool).
  Let p := bv_unsigned sp.
  Let Fp := A_STDOUT.
  Let B := A_STDOUT_BUF.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - VPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HVA : p <= VA /\ VA + 8 * zlength slots <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis RSTK : rng RNG lo (p - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem vprintf_i_spec : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 VA ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells asegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at asegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 B 1024 RNG m lo p (p - 464) slots args ->
    stk asegs m lo p -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo p -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) -> sobj RNG m B (B + 1024) ->
    pargs_okL RNG lo sp m its (Z_to_bv 64 VA) ->
    implAM RNG (vfprintf f ps) st (vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VPRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HF P1 PIECES SMALL LO GLO HVA HA KLO RSTK RIMG RVA FSTR NOZ EF OK.
    intros until rend. intros -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY VAA AOK ST SSP MI ENV CKP SOSTK SOFMT SOPFX SOF SOB PAOK.
    unfold VPRINTF_I_DEPTH, VPRINTF_STUB, GLOBALS_TOP in *.
    pose proof (va_area_bound _ _ _ VAA) as VAB. assert (NNs : 0 <= zlength slots) by (unfold zlength; lia). subst p Fp B. unfold A_STDOUT, A_STDOUT_BUF in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    apply implAM_from_evt.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vprintf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PAOK ]. }
    cbv beta. intros ms1 MID. unfold vprintf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & j24 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -2368, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    pose proof (rw_cells_bound _ _ _ _ FC0) as FBD. unfold fcells in FBD. rewrite file_cells_size in FBD.
    assert (FC1 : rw_cells asegs m1 695440 (fcells flags rpos rend closefn (if f_wactive f then 6299856 + 1024 else 0) (if f_wactive f then 6299856 + zlength (f_wbuf f) else 0) (if f_wactive f then 6299856 else 0)
                           readfn (wfn_of f) seekfn 6299856 1024 prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC0 | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 6299856 [CB 1024%nat bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF0 | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (CKP1 : rt_ckpf m1).
    { eapply (rw_cells_transport asegs _ m m1); [exact CKP | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (VAA1 : va_area m1 VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAA | exact MU1 | cbn [disjoint_from]; rewrite u64s_length; unfold zlength in *; lia]. }
    assert (AOK1 : args_ok 695440 232 6299856 1024 RNG m1 lo (bv_unsigned sp + -48) (bv_unsigned sp + -48 - 416) slots args).
    { replace (bv_unsigned sp + -48 - 416) with (bv_unsigned sp - 464) by lia.
      eapply args_ok_vff; [exact AOK | lia | exact MU1 | exact WM1 | exact AW1 |]. constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -48)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOF1 : sobj RNG m1 695440 (695440 + 232)) by (eapply sobj_transport; [exact SOF | exact MU1 | exact WM1 | exact AW1]).
    assert (SOB1 : sobj RNG m1 6299856 (6299856 + 1024)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | exact AW1]).
    assert (PAOK1 : pargs_okL RNG lo (Z_to_bv 64 (bv_unsigned sp + -48)) m1 its (Z_to_bv 64 VA)).
    { eapply pargs_okL_transport; [exact PAOK | exact MU1 | exact WM1 | exact AW1
                                  | eapply pargs_sep_stack; [exact PAOK | constructor; [cbn [fst snd]; lia | constructor]]
                                  | rewrite unsigned_lit by lia; lia]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    do 6 zstep. zstep.
    apply evtF_done.
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (vfprintf_i_file_spec (St:=St) RNG (Z_to_bv 64 0x47264) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 VA)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 695440 6299856 closefn readfn seekfn prev next tail A VA lo fmtz slots args ps r canary
                fstr its sw0 ch0)
        with (f := f) (flags := flags) (mode := mode) (bufbytes := bufbytes) (rpos := rpos) (rend := rend);
        rewrite ?unsigned_lit by lia; unfold VFPRINTF_I_DEPTH, GLOBALS_TOP;
        first [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RIMG | exact RVA | exact FSTR | exact NOZ | exact EF | exact OK
              | reflexivity | exact FC1 | exact FL0 | exact BUF1 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
              | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact ENV1 | exact CKP1 | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact SOB1
              | exact PAOK1
              | (unfold iesafe; cbn [disjoint_from]; repeat split; lia)
              | eapply rng_sub'; [exact RSTK | unfold zlength; cbn [length]; lia]
              | eapply rng_sub'; [exact RIMG | lia]
              | (left; lia)
              | unfold zlength in *; cbn [length] in *; lia ]. }
    cbv beta. intros f' st' ms2 PO. unfold vfprintf_file_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m2 & rpos' & rend'
                     & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & FC2 & RP2 & FL2 & BUF2 & BP2 & WBL2).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -48) [CB 24 j24; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [app disjoint_from cells_size csize Nat.add]; lia]. }
    replace (ret_pc (Z_to_bv 64 0x47264)) with (Z_to_bv 64 0x47264 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vprintf_i_post RNG) with (j24 := j24); rewrite ?unsigned_lit by lia; [exact MI2 | exact FR2 | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms3 ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in SK by lia.
    apply evtF_done. unfold vfprintf_file_post. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact FC2|]. split; [exact RP2|]. split; [exact FL2|]. split; [exact BUF2|]. split; [exact BP2 | exact WBL2].
  Qed.
End VprintfI.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_mlib__Musl.Printf_pieces.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.Printf_fsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.F_vfprintf_file.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_mkstemp__A3S.I_snprintf_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_vfprintf_top.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PRINTF_STUB : Z := 0x44510.
Definition VPRINTF_STUB : Z := 0x44504.
Definition PRINTF_I_DEPTH : Z := 5712.   (* [comment removed for export] *)
Definition VPRINTF_I_DEPTH : Z := 5648.  (* [comment removed for export] *)

Section PrintfI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A lo : Z) (fmtz : list Z) (a1 a2 a3 a4 a5 a6 a7 : word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Variables (sw0 ch0 : bool).
  Let p := bv_unsigned sp.
  Let Fp := A_STDOUT.
  Let B := A_STDOUT_BUF.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - PRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis PHI : p <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis RSTK : rng RNG lo (p - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RBUF : rng RNG B 1024.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem printf_i_spec : forall (t0 t1 t2 a0 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 A ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells asegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at asegs m A (zb fmtz) -> args_ok Fp 232 B 1024 RNG m lo p (p - 528) [a1; a2; a3; a4; a5; a6; a7] args ->
    stk asegs m lo p -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo p -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) -> sobj RNG m B (B + 1024) ->
    pwords_ok RNG lo sp m its [a1; a2; a3; a4; a5; a6; a7] ->
    implAM RNG (vfprintf f ps) st (vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HF P1 PIECES SMALL LO GLO PHI HA KLO RSTK RIMG RBUF FSTR NOZ EF OK.
    intros until rend. intros -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY AOK ST SSP MI ENV CKP SOSTK SOFMT SOPFX SOF SOB PWOK.
    unfold PRINTF_I_DEPTH, PRINTF_STUB, GLOBALS_TOP in *. subst p Fp B. unfold A_STDOUT, A_STDOUT_BUF in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    apply implAM_from_evt.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (printf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PWOK ]. }
    cbv beta. intros ms1 MID. unfold printf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & j24 & j8 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -2432, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    pose proof (rw_cells_bound _ _ _ _ FC0) as FBD. unfold fcells in FBD. rewrite file_cells_size in FBD.
    assert (FC1 : rw_cells asegs m1 696432 (fcells flags rpos rend closefn (if f_wactive f then 6300880 + 1024 else 0) (if f_wactive f then 6300880 + zlength (f_wbuf f) else 0) (if f_wactive f then 6300880 else 0)
                           readfn (wfn_of f) seekfn 6300880 1024 prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC0 | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 6300880 [CB 1024%nat bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF0 | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (CKP1 : rt_ckpf m1).
    { eapply (rw_cells_transport asegs _ m m1); [exact CKP | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (AOK1 : args_ok 696432 232 6300880 1024 RNG m1 lo (bv_unsigned sp + -112) (bv_unsigned sp + -112 - 416) [a1; a2; a3; a4; a5; a6; a7] args).
    { replace (bv_unsigned sp + -112 - 416) with (bv_unsigned sp - 528) by lia.
      eapply args_ok_vff; [exact AOK | lia | exact MU1 | exact WM1 | exact AW1 |]. constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -112)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOF1 : sobj RNG m1 696432 (696432 + 232)) by (eapply sobj_transport; [exact SOF | exact MU1 | exact WM1 | exact AW1]).
    assert (SOB1 : sobj RNG m1 6300880 (6300880 + 1024)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | exact AW1]).
    (* [comment removed for export] *)
    pose proof FR1 as FRc. cbn [app] in FRc.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -112 + Z.of_nat 56) with (bv_unsigned sp + -56) in VAc by lia.
    pose proof (va_area_of_cells m1 (bv_unsigned sp + -56) [a1; a2; a3; a4; a5; a6; a7] VAc) as VAA1.
    assert (PWOK1 : pwords_ok RNG lo (Z_to_bv 64 (bv_unsigned sp + -112)) m1 its [a1; a2; a3; a4; a5; a6; a7]).
    { eapply pwords_ok_transport; [exact PWOK | exact MU1 | exact WM1 | exact AW1
                                  | eapply pstrs_sep_stack; [exact PWOK | constructor; [cbn [fst snd]; lia | constructor]]
                                  | rewrite unsigned_lit by lia; lia]. }
    assert (PAOK1 : pargs_okL RNG lo (Z_to_bv 64 (bv_unsigned sp + -112)) m1 its (Z_to_bv 64 (bv_unsigned sp + -56))).
    { eapply (pargs_okL_of_words RNG lo _ m1 its [a1; a2; a3; a4; a5; a6; a7]);
        [exact PWOK1 | exact VAc | rewrite unsigned_lit by lia; lia | cbn [length]; lia | cbn [length]; eapply rng_sub'; [exact RSTK | lia]]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    do 6 zstep. zstep.
    apply evtF_done.
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (vfprintf_i_file_spec (St:=St) RNG (Z_to_bv 64 0x48238) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 (bv_unsigned sp + -56))
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 696432 6300880 closefn readfn seekfn prev next tail A (bv_unsigned sp + -56) lo fmtz [a1; a2; a3; a4; a5; a6; a7] args ps r canary
                fstr its sw0 ch0)
        with (f := f) (flags := flags) (mode := mode) (bufbytes := bufbytes) (rpos := rpos) (rend := rend);
        rewrite ?unsigned_lit by lia; unfold VFPRINTF_I_DEPTH, GLOBALS_TOP;
        first [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RIMG | exact FSTR | exact NOZ | exact EF | exact OK
              | reflexivity | exact FC1 | exact FL0 | exact BUF1 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
              | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact ENV1 | exact CKP1 | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact SOB1
              | exact PAOK1
              | (unfold iesafe; cbn [disjoint_from]; repeat split; lia)
              | eapply rng_sub'; [exact RSTK | unfold zlength; cbn [length]; lia]
              | eapply rng_sub'; [exact RIMG | lia]
              | (left; lia)
              | unfold zlength in *; cbn [length] in *; lia ]. }
    cbv beta. intros f' st' ms2 PO. unfold vfprintf_file_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m2 & rpos' & rend'
                     & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & FC2 & RP2 & FL2 & BUF2 & BP2 & WBL2).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -112) ([CB 24 j24; C8 s1; C8 s0; C8 ra] ++ [CB 8 j8; C8 a1; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7])).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [app disjoint_from cells_size csize Nat.add]; lia]. }
    replace (ret_pc (Z_to_bv 64 0x48238)) with (Z_to_bv 64 0x48238 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (printf_i_post RNG) with (j24 := j24); rewrite ?unsigned_lit by lia; [exact MI2 | exact FR2 | reflexivity | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms3 ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    cbn [app] in FR2.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -112 + Z.of_nat 112) with (bv_unsigned sp) in SK by lia.
    apply evtF_done. unfold vfprintf_file_post. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact FC2|]. split; [exact RP2|]. split; [exact FL2|]. split; [exact BUF2|]. split; [exact BP2 | exact WBL2].
  Qed.
End PrintfI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section VprintfI.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (closefn readfn seekfn prev next : Z) (tail : list byte)
            (A VA lo : Z) (fmtz : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Variables (sw0 ch0 : bool).
  Let p := bv_unsigned sp.
  Let Fp := A_STDOUT.
  Let B := A_STDOUT_BUF.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis SMALL : pieces_small ps.
  Hypothesis LO : lo <= p - VPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis HVA : p <= VA /\ VA + 8 * zlength slots <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis RSTK : rng RNG lo (p - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RVA : rng RNG VA (8 * zlength slots).
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Theorem vprintf_i_spec : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (f : file_st) (st : St)
      (flags mode : word) (bufbytes : list byte) (rpos rend : Z),
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 VA ->
    rw_cells asegs m Fp (fcells flags rpos rend closefn (if f_wactive f then B + 1024 else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                           readfn (wfn_of f) seekfn B 1024 prev next (f_fd f) mode (lbf_of f) tail) ->
    flags_ok f flags ->
    rw_cells asegs m B [CB 1024%nat bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
    (f_wactive f = false -> f_wbuf f = []) -> zlength (f_wbuf f) <= 1024 ->
    f_bufsize f = 1024 -> f_nowr f = false -> f_rbuf f = [] ->
    (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) -> (f_stdoutw f = true -> sw0 = true) -> f_chan f = ch0 ->
    bytes_at asegs m A (zb fmtz) -> va_area m VA slots -> args_ok Fp 232 B 1024 RNG m lo p (p - 464) slots args ->
    stk asegs m lo p -> ssp_cells m canary -> mem_inv asegs m ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo p -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m Fp (Fp + 232) -> sobj RNG m B (B + 1024) ->
    pargs_okL RNG lo sp m its (Z_to_bv 64 VA) ->
    implAM RNG (vfprintf f ps) st (vfprintf_file_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp B closefn readfn seekfn prev next tail lo canary sw0 ch0 rpos rend m st)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VPRINTF_STUB) fc None m (seg_rom asegs)).
  Proof using HF P1 PIECES SMALL LO GLO HVA HA KLO RSTK RIMG RVA FSTR NOZ EF OK.
    intros until rend. intros -> -> FC0 FL0 BUF0 BP0 WB0 WBL BS NW RB CH SWB CHN BY VAA AOK ST SSP MI ENV CKP SOSTK SOFMT SOPFX SOF SOB PAOK.
    unfold VPRINTF_I_DEPTH, VPRINTF_STUB, GLOBALS_TOP in *.
    pose proof (va_area_bound _ _ _ VAA) as VAB. assert (NNs : 0 <= zlength slots) by (unfold zlength; lia). subst p Fp B. unfold A_STDOUT, A_STDOUT_BUF in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia).
    assert (LFS : zlength fmtz = Z.of_nat (length fstr) + 1).
    { unfold zlength. rewrite <- (zb_length fmtz), FSTR, length_app. cbn [length]. lia. }
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    apply implAM_from_evt.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vprintf_i_pre RNG) with (lo := lo) (FMT := A) (fstr := fstr) (its := its);
        [ exact MI | exact ST | lia | exact KLO | exact ENV | exact CKP | reflexivity | rewrite <- FSTR; exact BY | exact NOZ | left; lia
        | rewrite <- LFS; exact SOFMT | exact RIMG | exact RSTK | eapply rng_sub'; [exact RIMG | lia] | exact EF | exact OK | exact PAOK ]. }
    cbv beta. intros ms1 MID. unfold vprintf_i_mid in MID.
    destruct MID as (u5 & u6 & u7 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & j24 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -2368, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    pose proof (rw_cells_bound _ _ _ _ FC0) as FBD. unfold fcells in FBD. rewrite file_cells_size in FBD.
    assert (FC1 : rw_cells asegs m1 696432 (fcells flags rpos rend closefn (if f_wactive f then 6300880 + 1024 else 0) (if f_wactive f then 6300880 + zlength (f_wbuf f) else 0) (if f_wactive f then 6300880 else 0)
                           readfn (wfn_of f) seekfn 6300880 1024 prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC0 | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 6300880 [CB 1024%nat bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF0 | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { eapply bytes_at_transport; [exact BY | exact MU1 | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    assert (CKP1 : rt_ckpf m1).
    { eapply (rw_cells_transport asegs _ m m1); [exact CKP | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (VAA1 : va_area m1 VA slots).
    { unfold va_area in *. eapply bytes_at_transport; [exact VAA | exact MU1 | cbn [disjoint_from]; rewrite u64s_length; unfold zlength in *; lia]. }
    assert (AOK1 : args_ok 696432 232 6300880 1024 RNG m1 lo (bv_unsigned sp + -48) (bv_unsigned sp + -48 - 416) slots args).
    { replace (bv_unsigned sp + -48 - 416) with (bv_unsigned sp - 464) by lia.
      eapply args_ok_vff; [exact AOK | lia | exact MU1 | exact WM1 | exact AW1 |]. constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -48)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU1 | exact WM1 | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU1 | exact WM1 | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU1 | exact WM1 | exact AW1]).
    assert (SOF1 : sobj RNG m1 696432 (696432 + 232)) by (eapply sobj_transport; [exact SOF | exact MU1 | exact WM1 | exact AW1]).
    assert (SOB1 : sobj RNG m1 6300880 (6300880 + 1024)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | exact AW1]).
    assert (PAOK1 : pargs_okL RNG lo (Z_to_bv 64 (bv_unsigned sp + -48)) m1 its (Z_to_bv 64 VA)).
    { eapply pargs_okL_transport; [exact PAOK | exact MU1 | exact WM1 | exact AW1
                                  | eapply pargs_sep_stack; [exact PAOK | constructor; [cbn [fst snd]; lia | constructor]]
                                  | rewrite unsigned_lit by lia; lia]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    do 6 zstep. zstep.
    apply evtF_done.
    (* [comment removed for export] *)
    eapply implAM_post_evt.
    { eapply (vfprintf_i_file_spec (St:=St) RNG (Z_to_bv 64 0x472cc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 VA)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 696432 6300880 closefn readfn seekfn prev next tail A VA lo fmtz slots args ps r canary
                fstr its sw0 ch0)
        with (f := f) (flags := flags) (mode := mode) (bufbytes := bufbytes) (rpos := rpos) (rend := rend);
        rewrite ?unsigned_lit by lia; unfold VFPRINTF_I_DEPTH, GLOBALS_TOP;
        first [ exact HF | exact P1 | exact PIECES | exact SMALL | exact HA | exact KLO | exact RIMG | exact RVA | exact FSTR | exact NOZ | exact EF | exact OK
              | reflexivity | exact FC1 | exact FL0 | exact BUF1 | exact BP0 | exact WB0 | exact WBL | exact BS | exact NW | exact RB | exact CH | exact SWB | exact CHN
              | exact BY1 | exact VAA1 | exact AOK1 | exact ST1 | exact SSP1 | exact MI1 | exact ENV1 | exact CKP1 | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOF1 | exact SOB1
              | exact PAOK1
              | (unfold iesafe; cbn [disjoint_from]; repeat split; lia)
              | eapply rng_sub'; [exact RSTK | unfold zlength; cbn [length]; lia]
              | eapply rng_sub'; [exact RIMG | lia]
              | (left; lia)
              | unfold zlength in *; cbn [length] in *; lia ]. }
    cbv beta. intros f' st' ms2 PO. unfold vfprintf_file_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (-> & INV' & z5 & z6 & z7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z28 & z29 & z30 & z31 & flags' & mode' & bufbytes' & m2 & rpos' & rend'
                     & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & FC2 & RP2 & FL2 & BUF2 & BP2 & WBL2).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -48) [CB 24 j24; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [app disjoint_from cells_size csize Nat.add]; lia]. }
    replace (ret_pc (Z_to_bv 64 0x472cc)) with (Z_to_bv 64 0x472cc : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vprintf_i_post RNG) with (j24 := j24); rewrite ?unsigned_lit by lia; [exact MI2 | exact FR2 | eapply rng_sub'; [exact RSTK | lia]]. }
    cbv beta. intros ms3 ->. rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in SK by lia.
    apply evtF_done. unfold vfprintf_file_post. split; [reflexivity|]. split; [exact INV'|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact FC2|]. split; [exact RP2|]. split; [exact FL2|]. split; [exact BUF2|]. split; [exact BP2 | exact WBL2].
  Qed.
End VprintfI.
End TwB.
End I_printf_top.
