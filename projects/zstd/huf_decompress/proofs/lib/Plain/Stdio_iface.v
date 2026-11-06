(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import F_memset F_memcpy F_printf_iface Stdio_kit StdioFiles.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Stdio_iface () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5Plain;Stdio_iface=stderr_wfile0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5Plain>F_printf_iface<stderr_wfileC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5Plain:StdioFiles:file_cellsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib5Plain;Stdio_ifaceCstderr_wfile0_wfileC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>F_printf_ifaceAstderr_wfile_fileC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition stderr_wfile0 (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells psegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x57f00 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0
    /\ (wend = 0 \/ (wend = 0x57f00 /\ e = 0x57f00))
    /\ 0 <= e < 2^63.

Lemma stderr_wfile0_wfile : forall m, stderr_wfile0 m -> stderr_wfile m.
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio_iface ()) [] "p'0h04tailh14wendh21eh32H0h44modeh55flagsh62FLh71Hh82_Hh93_H0h:1mi001xp;1p;2p;4p;;p;3g0000j1@Tg000Uj1JTg0013j1ITg001Vj1UTg0028j1TTg003<j1RTg003\j17Tg004Aj1=Tg004_j2STg005<R0j25Tg005WR1j20Tg0061j1:Tg0077j4QTg007Rj4ATg007ll;PTg008lj2ETg009Vj2GTg00:4j3?Tg00:Nj2HTg00:hj2NTg00;Dj2OTg00;`j4DTf0R2#@#@p=4%72#7p=C%72#@p=B%72#7#7#7p=6P2f1R3f2R4f3R5f4R6f5R7g00<VR8f6R9f7R:f8R;f9R<M;Pp=1g00=4R=1E43/G2;?8p=;A?=28p=>A?=32p=31565,H71N841O32'5'5p=8g00=RR>P5P4P3CD/52p=<10=2p=2P>P9P7P6CD1E54/G3=?=8/52'5p=9P>P4P3P2CDp=F1E54/G3=?=8/52p=MA?=38/H2p=L1N841O32'5p=Kg00>GR8#@R>#4R?#@#4#JR@#IRA%J?#IR?#U[%T2P1PA%R?R?P9%48#C#B#7#4#6#4#4#=RBP6P3P4P4%C8#6#B#4#C#B#4#=RC%@8#B#7#C#6#4#4#4#4#=RD%=>REP5%78#6R8#C#6#6#6#6#6#6#=RFP2M:1RG%B>#4#=R>9;@6RH%>3RI133DRJ134DRKP4P4%=8,SER8E8RL'5RMC<X0?'0X1=#2X2=#2X4A,0AX5A%:4P2P;PBPGPMC<X0?,0?X1=#2X2=#2X4A,0AP1PAP<PBP7P3P4P4PCPDPEP5PFP2M:1P@P7P>PLF9X0?,0?X1=#2X2=#2X4A%:9P2f;RMPBP:P3P4P4PCPDPEP5PFP2M:1P@P:P>PLF9X0?,0?X1=#2X2=#2P1P=f<RNPBP;P3P4P4PCPDPEP6PFP2M:1P@P;P>PLF9X0?,0?X1=#2X2=f:RO#:P2f>RPPBPOP3P4P4PCPDPEP9PFP2M:1P@POP>PLF9X0?,0?X1=#2P1P=f?RLPBPMP3P5P5PCPDPEP:PFP2M:1P@PMP>PIPJ135DP5P5P8E8F9X0?,0?X1=%:PP2fARQPBf=RRP3P7P7PCPDPEP<PFP2M:1P@PRP>PIPJ137DRJP7P7P8E8F9X0?,0?P1P?fBR1PBPPP4P9P9PCPDPEPOPFP2M:1P@PPP>%>4PK139DP9P9P8E8F9X0?%:1P2fDR9PBf@RKP6P;P;PCPDPEPNPFP2M:1P@PKP>%>6136D13;DR6P;P;P8E8F9P0fERPPQP7P<P<PCPDPEPRPFP3M:17FBP@PQP>%>7PJ13<DRJP<P<P8E8CMfFRO#:P2fGRIfCRSP:PMPMPCPDPEPLPFP5M:17FBP@P9P>%>;P613NDR6PNPNP8E8CMP0A;@P>%><PJ13RDRJPRPRP8E8fJR;#:P2A;@I>%>NP613KDPKPKP8E8P013QD,5J,LRAKQQ8fNRJ#:P213LD13SD'5,LLAK998PAfVPBPGPHC<X0?,0?X1=#2X2=#2X4A,0AX5AfMRHPAfUPBfQRGP3P4P4PCPDPEP5PFP2M:1A;@G>C<X0?,0?X1=#2X2=#2X4AfIR5P=fTPBfPR9P3P4P4PCPDPEfLPFP2M:1A;@9>C<X0?,0?X1=#2X2=PPP=fSPBfOR9P3PIPIPCPDPEfKPFP2M:1A;@9>C<X0?,0?X1=PQP?fRPBPJP1POPOPCPDPEP;PFP2M:1A;@J>C<X0?PRPHPQPPPPPCPDPEP5PFPRM:19FGBA;@H>P<P7CQCACACACACAW9W8P3P2O2n2001000000121000000W3W6P3P2O2n2001000000121000000W3W7P3P2O2n2001000000121000000W3X0?P3P2O2n2011000000121100000W3X1=P3P2O2n2011000000121100000W3X2=P3P2O2n2011000000121100000W3X4AP3P2O2n2011000000121100000W3X5AP3P2O2n2011000000121100000W3W:o"). Qed.
Lemma stderr_wfile0_file : forall m, stderr_wfile0 m -> stderr_file m.
Proof.
ltac2:(KReplay.run1 (kr_t_Stdio_iface ()) [] "h01Hh11mp;1p;2g0000j10Tg000Uj12Tg0013j11Tg001Vj13Tg0028j16Tg00>lj25Tg00@6j24Tg00>G#0#0#0R0#0#0#0#2#1%20#1#3[f0R0#6f1R11510'4W0W1o"). Qed.

(* [comment removed for export] *)
Definition FWRITE_DEPTH : Z := 240.

Section Fwrite.
  Context {St : Type}.

  Definition fwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Definition fwrite_diag_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
      towrite_stmt ->
      stderr_wfile0 m ->
      bytes_at psegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
      a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^47) -> (bv_unsigned a0 + zlength s <= 2^47) ->      (* [comment removed for export] *)
      (bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv psegs m ->
      implM psegs (stderr_fwrite s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1fb1c) fc None m (seg_rom psegs)).
  (* [comment removed for export] *)
  Definition fwrite_1n_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
      towrite_stmt ->
      stderr_wfile0 m ->
      bytes_at psegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
      a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (zlength s) -> a3 = Z_to_bv 64 RSTDERR ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^47) -> (bv_unsigned a0 + zlength s <= 2^47) ->      (* [comment removed for export] *)
      (bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv psegs m ->
      implM psegs (stderr_fwrite s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1fb1c) fc None m (seg_rom psegs)).
End Fwrite.

(* [comment removed for export] *)
Definition FPUTS_DEPTH : Z := 272.
Section Fputs.
  Context {St : Type}.
  Definition fputs_stderr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z) (slack : list byte),
      towrite_stmt ->
      stderr_wfile0 m ->
      bytes_at psegs m (bv_unsigned a0) (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256) s -> 0 < zlength s < 2^31 ->
      ((- (bv_unsigned a0 + zlength s + 1)) mod 8 <= zlength slack) ->
      a1 = Z_to_bv 64 RSTDERR ->
      stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPUTS_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned a0 + zlength s + 1 + zlength slack <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s + 1 + zlength slack <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv psegs m ->
      implM psegs (stderr_fputs s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1fac8) fc None m (seg_rom psegs)).
End Fputs.
