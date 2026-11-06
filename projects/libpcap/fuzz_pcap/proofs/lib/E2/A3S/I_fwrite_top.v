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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_fwrite. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_printf_lib__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_fwrite.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac cl_lit_hyps :=
  repeat match goal with
  | H : context [cells_size ?cs] |- _ =>
      tryif (match goal with H' := _ |- _ => constr_eq H' H end) then fail else
      (sl_spine_closed cs;
       let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
       change (cells_size cs) with n in H)
  end.
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Ltac mw LO := unfold sub_fp; cbn [outside]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; clear - Ha LO; lia.

Definition FWRITE_STUB : Z := 0x44490.
Definition FWRITE_I_DEPTH : Z := 4496.   (* [comment removed for export] *)

Section FwriteI.
  Context {rc : runConstT}.
  Context {St : Type}.

  Definition fwrite_i_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (s : list Z) (S size nmemb lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) ->
      bytes_at asegs m S (to_bytes s) -> Forall (fun c => 0 <= c < 256) s ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 nmemb -> a3 = Z_to_bv 64 Fp ->
      1 <= size < 2^64 -> 0 <= nmemb < 2^64 -> size * nmemb = zlength s ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITE_I_DEPTH -> 0x603000 <= lo -> bv_unsigned sp <= 2^47 ->
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      0 < B -> B + f_bufsize f <= 2^47 -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f ->
      0 <= S -> S + zlength s < 2^64 -> (zlength s = 0 \/ S + zlength s <= 2^47) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (zlength s = 0 \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S) /\ (S + zlength s <= B \/ B + f_bufsize f <= S))) ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      Z.land (bv_unsigned flags) F_SVB = 0 -> Z.land (bv_unsigned flags) F_NOWR = 0 ->
      KHIGH <= lo -> icptenv m -> iesafe [(Fp, Fp + 232)] -> iesafe [(B, B + f_bufsize f)] -> appW [(Fp, Fp + 232)] -> appW [(B, B + f_bufsize f)] ->
      sobj RNG m S (S + zlength s) -> sobj RNG m B (B + f_bufsize f) -> (S + zlength s <= lo \/ bv_unsigned sp <= S) ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      implAM RNG (fwrite_file f s) st
        (fwrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B prev next tail nmemb lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE_STUB) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary : ltac2:(SecDiet.SzSec.tyM 'fwrite_i_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  #[using="Type"] Lemma fwrite_i_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwrite_i_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros FC BUF BUFP WB0 SRC BYT -> -> -> -> SZ NM SN CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 B0 BShi BS0 WBL S0 S64 Shi LENW SEPS SEPB FL64 FL8
                                 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (rw_cells_bound _ _ _ _ BUF) as BB. (sl_lit_sizes_in BB; cbn [cells_size csize Nat.add] in BB).
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC.
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FWRITE_STUB, FWRITE_I_DEPTH in *.
    destruct SEPB as [SB1 SB2].
    apply implAM_from_evt.
    pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zs. (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fwrite_i_pre RNG); first [exact MI | exact ST | exact KLO | exact (ie_ini _ ENV) | exact (ie_fwrite _ ENV) | exact RIMG | exact RSTK | lia]. }
    cbv beta. intros ms1 MID.
    destruct MID as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1 & INI1).
    apply evtF_done.
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF | exact MU1 | exact WM1 | (sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]); lia]. }
    assert (SRC1 : bytes_at asegs m1 S (to_bytes s)).
    { eapply bytes_at_transport; [exact SRC | exact MU1 |]. rewrite length_to_bytes. cbn [disjoint_from]. unfold zlength in *. lia. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; (sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]); lia]). }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOS1 : sobj RNG m1 S (S + zlength s)) by (eapply sobj_transport; [exact SOS | exact MU1 | exact WM1 | solve_appW]).
    assert (SOB1 : sobj RNG m1 B (B + f_bufsize f)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | solve_appW]).
    eapply implAM_post_evt.
    { eapply (fwrite_spec (St:=St) RNG (Z_to_bv 64 0x46904) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp)
        with (m := m1) (f := f) (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (readfn := readfn) (seekfn := seekfn) (B := B)
             (prev := prev) (next := next) (mode := mode) (tail := tail) (bufbytes := bufbytes) (s := s) (S := S) (size := size) (nmemb := nmemb) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia; unfold FWRITE_DEPTH;
        first [ exact FC1 | exact BUF1 | exact BUFP | exact WB0 | exact SRC1 | exact BYT | exact CH | exact ST1 | exact SSP1 | exact MI1 | exact SN
              | exact Fp0 | exact FPLO | exact FSEP1 | exact FSEP2 | exact BSEP1 | exact BSEP2 | exact B0 | exact BShi | exact BS0 | exact WBL | exact S0 | exact S64 | exact Shi | exact LENW
              | exact FL64 | exact FL8 | exact KLO | exact ENV1 | exact IESF | exact IESB | exact APWF | exact APWB | exact SOS1 | exact SOB1 | exact RFP | exact RBUF | exact RS | exact RIMG
              | exact GLO | reflexivity | eapply rng_sub'; [exact RSTK | lia]
              | (split; [lia | exact SB2]) | lia ]. }
    cbv beta. intros f' st' ms' (-> & INV' & PO).
    destruct PO as (v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & mode' & bufbytes' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & BUF2 & BUFP2 & WBL2 & SSP2).
    unfold fx_W in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x46904)) with (Z_to_bv 64 0x46904 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    replace (if size =? 0 then 0 else nmemb) with nmemb in * by (destruct (Z.eqb_spec size 0); [lia | reflexivity]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | (sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]); lia]. }
    assert (STM2 : stk asegs m2 (bv_unsigned sp - 2128) (bv_unsigned sp - 56)).
    { eapply stk_transport_disjoint; [exact STM1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    assert (ENV2 : icptenv m2) by (eapply icptenv_transport; [exact ENV1 | exact MU2 | exact WM2 | solve_iesafe]).
    assert (SOS2 : sobj RNG m2 S (S + zlength s)) by (eapply sobj_transport; [exact SOS1 | exact MU2 | exact WM2 | solve_appW]).
    destruct SOS2 as (APP2 & UNP2 & NSZ2 & RLO & RHI & HR2 & WR2 & RSH2).
    assert (ZL : 0 <= zlength s) by (unfold zlength; lia).
    eapply evtF_cut.
    { eapply (fwrite_i_post RNG) with (lo := lo) (res := nmemb) (size := size) (N := zlength s) (RLO := RLO) (RHI := RHI);
        rewrite ?unsigned_lit by lia;
        first [ exact MI2 | exact ST2 | exact STM2 | exact FR2 | exact (ie_got _ ENV2) | exact (ie_shb _ ENV2) | exact (ie_lay _ ENV2) | exact WR2 | exact RIMG | exact RSTK
              | exact KLO | exact APP2 | exact UNP2 | exact HR2 | exact RSH2 | reflexivity | lia | nia ]. }
    cbv beta. intros ms3 PO3.
    destruct PO3 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    apply evtF_done. unfold fwrite_post.
    split; [reflexivity|]. split; [exact INV'|].
    do 14 eexists. exists mode', bufbytes', m3.
    split; [reflexivity|].
    split. { unfold fx_W. apply (munch_trans _ m m1 m3).
             - eapply munch_weaken; [| exact MU1]. mw LO.
             - apply (munch_trans _ m1 m2 m3).
               + eapply munch_weaken; [| exact MU2]. mw LO.
               + eapply munch_weaken; [| exact MU3]. mw LO. }
    split; [eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
    split. { eapply (rw_cells_transport asegs _ m2 m3); [exact FC2 | exact MU3 | exact WM3 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    split. { eapply (rw_cells_transport asegs _ m2 m3); [exact BUF2 | exact MU3 | exact WM3 | (sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]); lia]. }
    split; [exact BUFP2|]. split; [exact WBL2|].
    destruct SSP2 as [G1 G2]. split; (eapply (rw_cells_transport asegs _ m2 m3); [eassumption | exact MU3 | exact WM3 | unfold got_ssp, ssp_guard; (sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]); lia]).
  Qed.
  End Sz1.
  #[using="Type"] Theorem fwrite_i_spec : ltac:(let t := eval cbv delta [fwrite_i_spec__stmt] in fwrite_i_spec__stmt in exact t).
  Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary. ltac2:(SecDiet.SzSec.closeP 'fwrite_i_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FwriteI.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_lib__A3S.I_fwrite.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Ltac mw LO := unfold sub_fp; cbn [outside]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; clear - Ha LO; lia.

Definition FWRITE_STUB : Z := 0x444f8.
Definition FWRITE_I_DEPTH : Z := 4496.   (* [comment removed for export] *)

Section FwriteI.
  Context {rc : runConstT}.
  Context {St : Type}.

  Definition fwrite_i_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (s : list Z) (S size nmemb lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) ->
      bytes_at asegs m S (to_bytes s) -> Forall (fun c => 0 <= c < 256) s ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 nmemb -> a3 = Z_to_bv 64 Fp ->
      1 <= size < 2^64 -> 0 <= nmemb < 2^64 -> size * nmemb = zlength s ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITE_I_DEPTH -> 0x604000 <= lo -> bv_unsigned sp <= 2^47 ->
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      0 < B -> B + f_bufsize f <= 2^47 -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f ->
      0 <= S -> S + zlength s < 2^64 -> (zlength s = 0 \/ S + zlength s <= 2^47) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (zlength s = 0 \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S) /\ (S + zlength s <= B \/ B + f_bufsize f <= S))) ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      Z.land (bv_unsigned flags) F_SVB = 0 -> Z.land (bv_unsigned flags) F_NOWR = 0 ->
      KHIGH <= lo -> icptenv m -> iesafe [(Fp, Fp + 232)] -> iesafe [(B, B + f_bufsize f)] -> appW [(Fp, Fp + 232)] -> appW [(B, B + f_bufsize f)] ->
      sobj RNG m S (S + zlength s) -> sobj RNG m B (B + f_bufsize f) -> (S + zlength s <= lo \/ bv_unsigned sp <= S) ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      implAM RNG (fwrite_file f s) st
        (fwrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B prev next tail nmemb lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE_STUB) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary : ltac2:(SecDiet.SzSec.tyM 'fwrite_i_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  #[using="Type"] Lemma fwrite_i_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwrite_i_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros FC BUF BUFP WB0 SRC BYT -> -> -> -> SZ NM SN CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 B0 BShi BS0 WBL S0 S64 Shi LENW SEPS SEPB FL64 FL8
                                 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (rw_cells_bound _ _ _ _ BUF) as BB. (sl_lit_sizes_in BB; cbn [cells_size csize Nat.add] in BB).
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC.
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FWRITE_STUB, FWRITE_I_DEPTH in *.
    destruct SEPB as [SB1 SB2].
    apply implAM_from_evt.
    pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zs. (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (fwrite_i_pre RNG); first [exact MI | exact ST | exact KLO | exact (ie_ini _ ENV) | exact (ie_fwrite _ ENV) | exact RIMG | exact RSTK | lia]. }
    cbv beta. intros ms1 MID.
    destruct MID as (u0 & u1 & u2 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & STM1 & FR1 & INI1).
    apply evtF_done.
    assert (FC1 : rw_cells asegs m1 Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m1); [exact FC | exact MU1 | exact WM1 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    assert (BUF1 : rw_cells asegs m1 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF | exact MU1 | exact WM1 | (sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]); lia]. }
    assert (SRC1 : bytes_at asegs m1 S (to_bytes s)).
    { eapply bytes_at_transport; [exact SRC | exact MU1 |]. rewrite length_to_bytes. cbn [disjoint_from]. unfold zlength in *. lia. }
    assert (SSP1 : ssp_cells m1 canary).
    { split; (eapply (rw_cells_transport asegs _ m m1); [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; (sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]); lia]). }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SOS1 : sobj RNG m1 S (S + zlength s)) by (eapply sobj_transport; [exact SOS | exact MU1 | exact WM1 | solve_appW]).
    assert (SOB1 : sobj RNG m1 B (B + f_bufsize f)) by (eapply sobj_transport; [exact SOB | exact MU1 | exact WM1 | solve_appW]).
    eapply implAM_post_evt.
    { eapply (fwrite_spec (St:=St) RNG (Z_to_bv 64 0x4696c) (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp)
        with (m := m1) (f := f) (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (readfn := readfn) (seekfn := seekfn) (B := B)
             (prev := prev) (next := next) (mode := mode) (tail := tail) (bufbytes := bufbytes) (s := s) (S := S) (size := size) (nmemb := nmemb) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia; unfold FWRITE_DEPTH;
        first [ exact FC1 | exact BUF1 | exact BUFP | exact WB0 | exact SRC1 | exact BYT | exact CH | exact ST1 | exact SSP1 | exact MI1 | exact SN
              | exact Fp0 | exact FPLO | exact FSEP1 | exact FSEP2 | exact BSEP1 | exact BSEP2 | exact B0 | exact BShi | exact BS0 | exact WBL | exact S0 | exact S64 | exact Shi | exact LENW
              | exact FL64 | exact FL8 | exact KLO | exact ENV1 | exact IESF | exact IESB | exact APWF | exact APWB | exact SOS1 | exact SOB1 | exact RFP | exact RBUF | exact RS | exact RIMG
              | exact GLO | reflexivity | eapply rng_sub'; [exact RSTK | lia]
              | (split; [lia | exact SB2]) | lia ]. }
    cbv beta. intros f' st' ms' (-> & INV' & PO).
    destruct PO as (v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & mode' & bufbytes' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & BUF2 & BUFP2 & WBL2 & SSP2).
    unfold fx_W in MU2. rewrite ?unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x4696c)) with (Z_to_bv 64 0x4696c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    replace (if size =? 0 then 0 else nmemb) with nmemb in * by (destruct (Z.eqb_spec size 0); [lia | reflexivity]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | (sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]); lia]. }
    assert (STM2 : stk asegs m2 (bv_unsigned sp - 2128) (bv_unsigned sp - 56)).
    { eapply stk_transport_disjoint; [exact STM1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    assert (ENV2 : icptenv m2) by (eapply icptenv_transport; [exact ENV1 | exact MU2 | exact WM2 | solve_iesafe]).
    assert (SOS2 : sobj RNG m2 S (S + zlength s)) by (eapply sobj_transport; [exact SOS1 | exact MU2 | exact WM2 | solve_appW]).
    destruct SOS2 as (APP2 & UNP2 & NSZ2 & RLO & RHI & HR2 & WR2 & RSH2).
    assert (ZL : 0 <= zlength s) by (unfold zlength; lia).
    eapply evtF_cut.
    { eapply (fwrite_i_post RNG) with (lo := lo) (res := nmemb) (size := size) (N := zlength s) (RLO := RLO) (RHI := RHI);
        rewrite ?unsigned_lit by lia;
        first [ exact MI2 | exact ST2 | exact STM2 | exact FR2 | exact (ie_got _ ENV2) | exact (ie_shb _ ENV2) | exact (ie_lay _ ENV2) | exact WR2 | exact RIMG | exact RSTK
              | exact KLO | exact APP2 | exact UNP2 | exact HR2 | exact RSH2 | reflexivity | lia | nia ]. }
    cbv beta. intros ms3 PO3.
    destruct PO3 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    apply evtF_done. unfold fwrite_post.
    split; [reflexivity|]. split; [exact INV'|].
    do 14 eexists. exists mode', bufbytes', m3.
    split; [reflexivity|].
    split. { unfold fx_W. apply (munch_trans _ m m1 m3).
             - eapply munch_weaken; [| exact MU1]. mw LO.
             - apply (munch_trans _ m1 m2 m3).
               + eapply munch_weaken; [| exact MU2]. mw LO.
               + eapply munch_weaken; [| exact MU3]. mw LO. }
    split; [eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
    split. { eapply (rw_cells_transport asegs _ m2 m3); [exact FC2 | exact MU3 | exact WM3 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
    split. { eapply (rw_cells_transport asegs _ m2 m3); [exact BUF2 | exact MU3 | exact WM3 | (sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]); lia]. }
    split; [exact BUFP2|]. split; [exact WBL2|].
    destruct SSP2 as [G1 G2]. split; (eapply (rw_cells_transport asegs _ m2 m3); [eassumption | exact MU3 | exact WM3 | unfold got_ssp, ssp_guard; (sl_lit_sizes; cbn [disjoint_from cells_size csize Nat.add]); lia]).
  Qed.
  End Sz1.
  #[using="Type"] Theorem fwrite_i_spec : ltac:(let t := eval cbv delta [fwrite_i_spec__stmt] in fwrite_i_spec__stmt in exact t).
  Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary. ltac2:(SecDiet.SzSec.closeP 'fwrite_i_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FwriteI.
End TwB.
