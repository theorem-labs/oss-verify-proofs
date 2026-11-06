(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Export FX_Exit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_FX_Stdio_iface () := "C69OSSVerify5KrLib2K54Spec5Monad1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio6upd_soC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Monad5implMC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K54Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Monad9implM_updC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23>FX_Stdio_iface@stdio_write_postC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23>FX_Stdio_ifaceCstdout_writefn_postC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib2K53A23>FX_Stdio_iface<stderr_wfileC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53A237FX_Exit;stderr_fileC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53A239FX_Layout:file_cellsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03c69OSSVerify5KrLib2K53A23>FX_Stdio_iface=stderr_wfile0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init5Logic3and01I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltc69OSSVerify5KrLib2K53A23>FX_Stdio_ifaceCstderr_wfile0_wfileC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23>FX_Stdio_ifaceAstderr_wfile_fileC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdioRules.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Lemma implM_rdso : forall {A} (f : stdout_st -> M St A) (s : St) Q ms,
    implM asegs (f (get_so s)) s Q ms -> implM asegs (Monad.mbind (rd_so get_so) f) s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_FX_Stdio_iface ()) ["StdioRules"] "h01Ah11Hh21Qh31fh42msh51sp;2p;7p,2StR0p4p300R1g0000R2p4p710p8P1p1000dp4p710p8p200R1P2p4p7210p8P1p1001]p4p73110p8P1g002UR3p4p73110p8P2j21TP3j70Tg003Mf1R3,10[f2R2g004KR4p-0[\0[P0g005Rf4f3p,6get_soP2O1O1P2P3f0R3F0P3W1X44W2X50W3X01o"). Qed.
  Lemma implM_updso : forall {A} (g : stdout_st -> stdout_st) (f : unit -> M St A) (s : St) Q ms,
    implM asegs (f tt) (set_so (g (get_so s)) s) Q ms -> implM asegs (Monad.mbind (upd_so get_so set_so g) f) s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_FX_Stdio_iface ()) ["StdioRules"] "h01Ah11Hh21Qh31fh41gh52msh61sp;2p;7p200R0g0000R1p4p7210p8P0p1001]p4p73110p8P0g002UR2p4p73110p8P1j21TP2j70Tg003MR2P2[g006Jp,2StR2f2R1'1[f3R3g004KR4p-0[\2[P2g005Rf5P3g006jO1p,6set_sof4p,6get_soP1O1O1P1O2f1f0R1F0P1W1X54W2X62W3W4X00o"). Qed.
  Lemma implM_updso_last : forall (g : stdout_st -> stdout_st) (s : St) (Q : unit -> St -> machine_state -> Prop) ms,
    Q tt (set_so (g (get_so s)) s) ms -> implM asegs (upd_so get_so set_so g) s Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_FX_Stdio_iface ()) ["StdioRules"] "h01sh11Hh21Qh31gh42msp;4p;7g007Jj41Tg008Cj70Tg003MR0P0[p,2StR0g006Jg004KR1p-0[\0[f1R2g006jR3p,6set_soR4f3R5p,6get_soR6f2R7O1O1P7O2f0R8O3P0g005RR9P4f5P6P8O1O1P8O2X00P5P7P2P9P7P3P4f4P6P5O1O1P5O2O2P2P8C1F0W1X41W2W0W3o"). Qed.
End StdioRules.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STDIO_WRITE : Z := 0x1faa24.
Definition STDIO_WRITE_DEPTH : Z := 112.   (* [comment removed for export] *)

Section StdioWrite.
  Context {St : Type}.

  Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp : Z) (flags : word) (B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
      (l : Z) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
      /\ ssp_cells m' canary
      /\ st' = st.

  Definition stdio_write_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (buf s : list Z) (S lo : Z) (canary : word),
      rw_cells asegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      bytes_at asegs m B (to_bytes buf) ->
      bytes_at asegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (fd = 1 \/ fd = 2) ->
      stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      ssp_cells m canary -> mem_inv asegs m ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize < 2^64) ->
      (zlength buf + zlength s <= 2^26) -> (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (S = 0 \/ 0 < zlength s) ->   (* [comment removed for export] *)
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      (B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
      implM asegs (stdio_writev (St:=St) fd buf s) st
            (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                              (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1faa24) fc None m (seg_rom asegs)).
End StdioWrite.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wfn_of (so : stdout_st) : Z := if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (so : stdout_st) : Z := if so_lbf_nl so then 10 else 0xffffffff.
Definition stdout_cells (so : stdout_st) (flags mode : word) (tail : list byte) : list cell :=
  file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF (wfn_of so) RSTDOUT_BUF 1024 1 mode (lbf_of so) tail.

Definition STDOUT_WRITE_DEPTH : Z := 144.   (* [comment removed for export] *)

Section StdoutWrite.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  (* [comment removed for export] *)
  Definition so_after (so : stdout_st) : stdout_st :=
    mkStdout true [] (if so_first so then false else so_lbf_nl so) false.

  Definition stdout_writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (flags mode : word) (tail : list byte) (l : Z) (lo : Z) (canary : word) (m : mem) (st : St)
      : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - STDOUT_WRITE_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' RSTDOUT (stdout_cells (so_after (get_so st)) flags mode tail)
      /\ ssp_cells m' canary
      /\ st' = set_so (so_after (get_so st)) st.

  Definition stdout_writefn_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (flags mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      let so := get_so st in
      so_active so = true ->
      rw_cells asegs m RSTDOUT (stdout_cells so flags mode tail) ->
      Z.land (bv_unsigned flags) 64 = 0 ->
      bytes_at asegs m RSTDOUT_BUF (to_bytes (so_buf so)) -> (zlength (so_buf so) <= 1024) ->
      bytes_at asegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDOUT_WRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      ssp_cells m canary -> mem_inv asegs m ->
      (zlength s <= 2^26 - 1024) -> (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (S = 0 \/ 0 < zlength s) ->   (* [comment removed for export] *)
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= RSTDOUT \/ RSTDOUT + 232 <= S))) ->
      implM asegs (stdout_writefn get_so set_so s) st
            (stdout_writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags mode tail (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (wfn_of so)) fc None m (seg_rom asegs)).
End StdoutWrite.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stderr_wfile (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x783e20 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0.
Lemma stderr_wfile_file : forall m, stderr_wfile m -> stderr_file m.
Proof.
ltac2:(KReplay.run1 (kr_t_FX_Stdio_iface ()) [] "p'0h04tailh14wendh21eh32H0h44modeh55flagsh61Hh72_Hh81mi001xp;1p;2p;4p;;p;3p1009?p4p710R0p10000p4p710R1p8P0p1000dp4p710R0p8p100:Jp4p710R2P1p8P2P0p8g00;Xj14Tg00<=j1GTg00<[j1BTg00=>j1LTg00=`j1KTg00>gj1JTg00?Gj19Tg00?ej13Tg00@JR0j20Tg00@dj1:Tg00Acj4<Tg00B=l;ITg00C=j2FTg00Cgj2DTg00DEj3ETg00D_j4?Tg00EXR2j2CTf0R1#4#4p=;%41#3p=>%31#4#4#4p=7%31#3#3#3p=5%31#4p==%31#3p=AP1f1R3f2R4f3R5f4R6f5R7g00F3R8f6R9f7R:f8R;f9R<M;Ip=1g00FQR=1F43/D1;E8p=@g005RR>P5P4P3C?/C1p=H10=1p=2P>P7P6P5C?1F43/D1=E=8'Cp=6P>P4P3P1C?p=8g00FoR>#4R8#;R?#4#;#GR@#BRA%G?#BR?#L[%K1P0PA%J?R?P9%4>#;#>#>#7#7#>#7#9RBP6P3P4P4%5>#=#=#=#7#=#>#;#9RC%A>#7#;#5#7#7#;#9RD%98REP5%3>#A#5#5#5#5#5#5#5#9R>P1M:1RF%78#9R89@@6RGCHX0?'0X1=#2X2=#2X4A,0AX5A%:4P1P;PBPFPGCHX0?,0?X1=#2X2=#2X4A,0AP0PAP<PBP7P3P4P4PCPDPEP5P>P1M:1P@P7P8E6X0?,0?X1=#2X2=#2X4A%:9P1f;RGPBP:P3P4P4PCPDPEP5P>P1M:1P@P:P8E6X0?,0?X1=#2X2=#2P0P=f<RHPBP;P3P4P4PCPDPEP6P>P1M:1P@P;P8E6X0?,0?X1=#2X2=f:RI#:P1f>RJPBPIP3P4P4PCPDPEP9P>P1M:1P@PIP8E6X0?,0?X1=#2P0P=f?RKPBPGP3P5P5PCPDPEP:P>P1M:1P@PGP8E6X0?,0?X1=%:JP1fARLPBf=RMP3P7P7PCPDPEP<P>P1M:1P@PMP8E6X0?,0?P0P?fBR0PBPJP4P9P9PCPDPEPIP>P1M:1P@PJP8E6X0?%:0P1fDR9PBf@RNP6P;P;PCPDPEPHP>P1M:1P@PNP8E6P2fER2PLP7P<P<PCPDPEPMP>P3M:178BA@@L8fFRN#:P1fGRHfCR;P:PGPGPCPDPEPKP>P5M:178BA@@98PAfN?8BFX0?,0?X1=#2X2=#2X4A,0AX5AP2PAfMfIP3P4P4PCPDPEP5P>P1M:178BX0?,0?X1=#2X2=#2X4APLP=fLfHP3P4P4PCPDPEP9P>P1M:178BX0?,0?X1=#2X2=PMP=fKPHP3PKPKPCPDPEP;P>P1M:178BX0?,0?X1=P<P?fJPNPIPJPJPCPDPEP0P>P1M:178BX0?P7P3C<C<C<C<C<W7W6P3P1O2n2001000000121000000W3X0?P3P1O2n2001000000121100000W3X1=P3P1O2n2001000000121100000W3X2=P3P1O2n2001000000121100000W3X4AP3P1O2n2011000000121100000W3X5AP3P1O2n2011000000121100000W3W8o"). Qed.

Definition stderr_wfile0 (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x783e20 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0
    /\ (wend = 0 \/ (wend = 0x783e20 /\ e = 0x783e20))
    /\ 0 <= e < 2^63.
Lemma stderr_wfile0_wfile : forall m, stderr_wfile0 m -> stderr_wfile m.
Proof.
ltac2:(KReplay.run1 (kr_t_FX_Stdio_iface ()) [] "p'0h04tailh14wendh21eh32H0h44modeh55flagsh62FLh71Hh82_Hh93_H0h:1mi001xp;1p;2p;4p;;p;3g00;Xj15Tg00<=j1NTg00<[j1KTg00=>j1WTg00GTj1VTg00>gj1TTg00?Gj1=Tg00?ej16Tg00H\j2UTg00EXR0j24Tg00@JR1j20Tg00=`j1;Tg00I9j4STg00Acj4BTg00B=l;RTg00C=j2ETg00Cgj2GTg00DEj3@Tg00ITj2JTg00Inj2PTg00JJj2QTg00D_j4HTf0R2#5#5p=A%52#6p=D%62#5#5#5p=9%62#6#6#6p=7%62#5p=C%62#6p=IP2f1R3f2R4f3R5f4R6f5R7g00F3R8f6R9f7R:f8R;f9R<M;Rp=1g00FQR=1E43/G2;@8p=<A@=28p=?A@=32p=31465,J71P841Q32'4'4p=8g005RR>P5P4P3CH/42p=>10=2p=2P>P9P7P6CH1E54/G3=@=8/42'4p=:P>P4P3P2CHp=F1E54/G3=@=8/42p=OA@=38/J2p=M1P841Q32'4p=Lg00FoR8#5R>#AR?#5#A#NR@#KRA%N?#KR?#W[%V2P1PA%T?R?P9%58#A#D#D#9#9#D#9#=RBP6P3P4P4%78#C#C#C#9#C#D#A#=RC%I8#9#A#7#9#9#A#=RD%=>REP5%68#7R8#I#7#7#7#7#7#7#=RFP2M:1RG%9>#=R>9<@6RH%?3RI133DRJ134DRKP4P4%=8,UER8E8RL'4RMC>X0?'0X1=#2X2=#2X4A,0AX5A%;4P2P;PBPGPMC>X0?,0?X1=#2X2=#2X4A,0AP1PAP<PBP7P3P4P4PCPDPEP5PFP2M:1P@P7P>PLF:X0?,0?X1=#2X2=#2X4A%;9P2f;RMPBP:P3P4P4PCPDPEP5PFP2M:1P@P:P>PLF:X0?,0?X1=#2X2=#2P1P=f<RNPBP;P3P4P4PCPDPEP6PFP2M:1P@P;P>PLF:X0?,0?X1=#2X2=f:RO#;P2f>RPPBPOP3P4P4PCPDPEP9PFP2M:1P@POP>PLF:X0?,0?X1=#2P1P=f?RLPBPMP3P5P5PCPDPEP:PFP2M:1P@PMP>PIPJ135DP5P5P8E8F:X0?,0?X1=%;PP2fARQPBf=RRP3P7P7PCPDPEP<PFP2M:1P@PRP>PIPJ137DRJP7P7P8E8F:X0?,0?P1P?fBR1PBPPP4P9P9PCPDPEPOPFP2M:1P@PPP>%?4PK139DP9P9P8E8F:X0?%;1P2fDR9PBf@RKP6P;P;PCPDPEPNPFP2M:1P@PKP>%?6136D13;DR6P;P;P8E8F:P0fERPPQP7P<P<PCPDPEPRPFP3M:17FBP@PQP>%?7PJ13<DRJP<P<P8E8COfFRO#;P2fGRIfCRSP:PMPMPCPDPEPLPFP5M:17FBP@P9P>%?;P613NDR6PNPNP8E8COP0A<@P>%?<PJ13RDRJPRPRP8E8fJR;#;P2A<@I>%?NP613KDPKPKP8E8P013QD,4J,MRALQQ8fNRJ#;P213LD13SD'4,MLAL998PAfVPBPGPHC>X0?,0?X1=#2X2=#2X4A,0AX5AfMRHPAfUPBfQRGP3P4P4PCPDPEP5PFP2M:1A<@G>C>X0?,0?X1=#2X2=#2X4AfIR5P=fTPBfPR9P3P4P4PCPDPEfLPFP2M:1A<@9>C>X0?,0?X1=#2X2=PPP=fSPBfOR9P3PIPIPCPDPEfKPFP2M:1A<@9>C>X0?,0?X1=PQP?fRPBPJP1POPOPCPDPEP;PFP2M:1A<@J>C>X0?PRPHPQPPPPPCPDPEP5PFPRM:19FGBA<@H>P<P7CSCBCBCBCBCBW9W8P3P2O2n2001000000121000000W3W6P3P2O2n2001000000121000000W3W7P3P2O2n2001000000121000000W3X0?P3P2O2n2011000000121100000W3X1=P3P2O2n2011000000121100000W3X2=P3P2O2n2011000000121100000W3X4AP3P2O2n2011000000121100000W3X5AP3P2O2n2011000000121100000W3W:o"). Qed.
Lemma stderr_wfile0_file : forall m, stderr_wfile0 m -> stderr_file m.
Proof.
ltac2:(KReplay.run1 (kr_t_FX_Stdio_iface ()) [] "h01Hh11mp;1p;2g00;Xj10Tg00<=j12Tg00<[j11Tg00=>j13Tg00GTj16Tg00Jfj25Tg00L4j24Tg00Fo#0#0#0R0#0#0#0#2#1%20#1#3[f0R0#6f1R11510'4W0W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FWRITE_DEPTH : Z := 240.

Section Fwrite.
  Context {St : Type}.

  Definition fwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Definition fwrite_diag_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
      stderr_wfile0 m ->
      bytes_at asegs m (bv_unsigned a0) (map (fun z => Z_to_bv 8 z) s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^25 ->
      a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
      stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv asegs m ->
      implM asegs (stderr_fwrite s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1fbc98) fc None m (seg_rom asegs)).
End Fwrite.
