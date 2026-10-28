(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import F_printf_iface Stdio_kit StdioFiles MonadF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Stdio_iface () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c5ARocqVerifyHarness?AgentSubmission5BothW;Stdio_iface=stderr_wfile0I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_iface<stderr_wfileK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5BothW:StdioFiles:file_cellsC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums8positive03c5ARocqVerifyHarness?AgentSubmission5BothW;Stdio_ifaceCstderr_wfile0_wfileC5ARocqVerifyHarness?AgentSubmission5BothW>F_printf_ifaceAstderr_wfile_file".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition stderr_wfile0 (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells bsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x60d998 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0
    /\ (wend = 0 \/ (wend = 0x60d998 /\ e = 0x60d998))
    /\ 0 <= e < 2^63.

Lemma stderr_wfile0_wfile : forall m, stderr_wfile0 m -> stderr_wfile m.
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio_iface ()) ["CANSEC1"] "p'0h04tailh14wendh21eh32H0h44modeh55flagsh62FLh71Hh82_Hh93_H0h:1mi001xp;1p;2p;4p;;p;3g0000j1<Tg000Uj1MTg0013j1KTg001Vj1VTg0028j1UTg003<j1STg003\j1?Tg004:j16Tg004_j2TTg005<R0j24Tg005WR1j20Tg0061j1;Tg0077j4RTg007Rj4CTg007ll;QTg008lj2ETg009Vj2GTg00:4j3BTg00:Nj2JTg00:hj2PTg00;Dj2ITg00;`j4HTf0R2#<#<p=8%62#6p=D%<2#6p=5%62#<p=9%62#6#6#6p=:P2f1R3f2R4f3R5f4R6f5R7g00<VR8f6R9f7R:f8R;f9R<M;Qp=1g00=4R=1E43/G2;B8p=>AB=28p=AAB=32p=31465,J71P841I32'4'4p=7g00=RR>P5P4P3CH/42p=@10=2p=2P>P9P7P6CH1E54/G3=B=8/42'4p==P>P4P3P2CHp=F1E54/G3=B=8/42p=OAB=38/J2p=N1P841I32'4p=Lg00>GR8#<R>#8R?#<#8#MR@#KRA%M?#KR?#V[%U2P1PA%S?R?P9%<8#D#5#9#5#9#:#9#8#?RBP6P3P4P4%<8#9#5#D#8#5#5#5#5#8#?RC%98#8#8#D#5#9#5#9#5#9#8#?RD%?>REP5%68#:R8#D#:#:#:#:#:#:#?RFP2M:1RG%9>#8#?R>9>@6RH%A3RI133DRJ134DRKP4P4%?8,TER8E7RL'4RMC@X0?'0X1=#2X2=#2X4A,0AX5A%;4P2P;PBPGPMC@X0?,0?X1=#2X2=#2X4A,0AP1PAP<PBP7P3P4P4PCPDPEP5PFP2M:1P@P7P>PLF=X0?,0?X1=#2X2=#2X4A%;9P2f;RMPBP:P3P4P4PCPDPEP5PFP2M:1P@P:P>PLF=X0?,0?X1=#2X2=#2P1P=f<RNPBP;P3P4P4PCPDPEP6PFP2M:1P@P;P>PLF=X0?,0?X1=#2X2=f:RO#;P2f>RPPBPOP3P4P4PCPDPEP9PFP2M:1P@POP>PLF=X0?,0?X1=#2P1P=f?RLPBPMP3P5P5PCPDPEP:PFP2M:1P@PMP>PIPJ135DP5P5P8E7F=X0?,0?X1=%;PP2fARQPBf=RRP3P7P7PCPDPEP<PFP2M:1P@PRP>PIPJ137DRJP7P7P8E7F=X0?,0?P1P?fBR1PBPPP4P9P9PCPDPEPOPFP2M:1P@PPP>%A4PK139DP9P9P8E7F=X0?%;1P2fDR9PBf@RKP6P;P;PCPDPEPNPFP2M:1P@PKP>%A6136D13;DR6P;P;P8E7F=P0fERPPQP7P<P<PCPDPEPRPFP3M:17FBP@PQP>%A7PJ13<DRJP<P<P8E7COfFRO#;P2fGRIfCRSP:PMPMPCPDPEPLPFP5M:17FBP@P9P>%A;P613NDR6PNPNP8E7COP0A>@P>%A<PJ13RDRJPRPRP8E7fJR;#;P2A>@I>%ANP613KDPKPKP8E7P013QD,4J,NRALQQ8fNRJ#;P213LD13SD'4,NLAL998PAfVPBPGPHC@X0?,0?X1=#2X2=#2X4A,0AX5AfMRHPAfUPBfQRGP3P4P4PCPDPEP5PFP2M:1A>@G>C@X0?,0?X1=#2X2=#2X4AfIR5P=fTPBfPR9P3P4P4PCPDPEfLPFP2M:1A>@9>C@X0?,0?X1=#2X2=PPP=fSPBfOR9P3PIPIPCPDPEfKPFP2M:1A>@9>C@X0?,0?X1=PQP?fRPBPJP1POPOPCPDPEP;PFP2M:1A>@J>C@X0?PRPHPQPPPPPCPDPEP5PFPRM:19FGBA>@H>P<P7CRCCCCCCCCCCW9W8P3P2O2n2001000000121000000W3W6P3P2O2n2001000000121000000W3W7P3P2O2n2001000000121000000W3X0?P3P2O2n2011000000121100000W3X1=P3P2O2n2011000000121100000W3X2=P3P2O2n2011000000121100000W3X4AP3P2O2n2011000000121100000W3X5AP3P2O2n2011000000121100000W3W:o"). Qed.
Lemma stderr_wfile0_file : forall m, stderr_wfile0 m -> stderr_file m.
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio_iface ()) ["CANSEC1"] "h01Hh11mp;1p;2g0000j10Tg000Uj12Tg0013j11Tg001Vj13Tg0028j16Tg00>lj25Tg00@6j24Tg00>G#0#0#0R0#0#0#0#2#1%20#1#3[f0R0#6f1R11510'4W0W1o"). Qed.

(* [comment removed for export] *)
Definition FWRITE_DEPTH : Z := 240.

Section Fwrite.
  Context {St : Type}.

  Definition fwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)                         (* [comment removed for export] *)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Definition fwrite_diag_stmt : Prop :=
    forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
      towrite_stmt ->
      stderr_wfile0 m ->
      bytes_at bsegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
      a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv bsegs m ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng RNG (bv_unsigned a0) (zlength s) ->
      (bv_unsigned sp < 2^47) -> (bv_unsigned a0 + zlength s <= 2^47) ->      (* [comment removed for export] *)
      implAM RNG (stderr_fwrite s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xa7a10) fc None m (seg_rom bsegs)).
End Fwrite.

End CANSEC1.
