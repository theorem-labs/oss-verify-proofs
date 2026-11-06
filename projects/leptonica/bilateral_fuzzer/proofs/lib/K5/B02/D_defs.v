(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_frmkit RT_frmrom D_iface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import MainSkel.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_D_defs () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib2K52AS8AsanAcct<segs_below_bC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53B026ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct@wx_segs_nowrap_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcctCwx_segs_nowrap_of_bC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53Lib5RzCPS>mat_stable_obsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53B028RT_iface3rtsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface4ARTMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface4PMfdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface=af_mat_stableC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026D_defs?PMfd_mat_stableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS>mat_stable_andC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8rt_allowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026D_defsBASTA_PM_mat_stableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029RT_frmkit8astf_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c69OSSVerify5KrLib2K53B026D_defs8asegs_wxC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026D_defs;asegs_belowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029RT_frmrom9asegs_frmC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib2K53B029RT_frmkit;ASTF_conseqC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53B029RT_frmkit8ASTF_exIC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC69OSSVerify5KrLib2K53Lib5RzCPS5macctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface4frmWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS2HZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC69OSSVerify5KrLib2K53Lib2FP4frm0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib5RzCPS3HIDC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC69OSSVerify5KrLib2K52AS8AsanAcct8restrictC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib2K53B026D_defs:drv_constsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026D_defs<stderr_cellsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53B027D_iface9ssp_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_iface7GOT_SSPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026D_defs<GOT_LLVMINITC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026D_defs7S_SHORTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B026D_defs6S_OVERC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_iface9SSP_GUARDC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition TP_A : Z := 0x64cf48.               (* [comment removed for export] *)
Definition ERRNO_A : Z := TP_A - 164.           (* [comment removed for export] *)
Definition MAIN_RA : Z := 0xf6bf0.              (* [comment removed for export] *)
Definition GOT_STDERR : Z := 0x10b7c0.           (* [comment removed for export] *)
Definition STDERR_VAR : Z := 0x10aa58.           (* [comment removed for export] *)
Definition RET_OPEN : Z := 0x960b4.             (* [comment removed for export] *)
Definition GOT_LLVMINIT : Z := 0x10b7c8.         (* [comment removed for export] *)
Definition TR_INIT : Z := 0x64c3d0.             (* [comment removed for export] *)
Definition TR_EMPTY : Z := 0x64c3e0.            (* [comment removed for export] *)
Definition TR_INCB : Z := 0x64c3d4.            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fds0 : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

Lemma asegs_below : segs_below_b asegs SEGTOP_A = true.
Proof.
ltac2:(KReplay.run1 (kr_t_D_defs ()) [] "p;2p;3g0000j22Tg000Jj21Tg001Jj30Tg001dR0g002DR1'2g002dg003\'1=001eo"). Qed.
Lemma asegs_wx : wx_segs_nowrap asegs.
Proof.
ltac2:(KReplay.run1 (kr_t_D_defs ()) [] "p;2p;1p;3g0000j23Tg004Yj12Tg001Jj30Tg005]j21Tg002dR0g001dR1g002DR2'3%20=012e'1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Kit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma PMfd_mat_stable : forall F0 fs0, mat_stable (PMfd F0 fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_D_defs ()) ["Kit"] "h02F0h13fdsh23fs'h33fs0p;1p;2p;3g006dj10Tg007Ij17Tg007gj14Tg008Jj21Tg008jj13Tg001Jj32Tg009Jj26Tg009ej15Tg00:e#0#0#0#0#0#0#7#4R0g00;J'1#3R1g00<BR2g00=01100#3g00=gf4f6521f3f5522'6UUUX22X11#5W3W0o"). Qed.

Lemma ASTA_PM_mat_stable : forall Σ F0 fs0, mat_stable (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo).
Proof.
ltac2:(KReplay.run1 (kr_t_D_defs ()) ["Kit"] "h02F0h13fs0h22Σp;1p;2p;3p;4g00>Ej1:Tg006dj10Tg007Ij12Tg007gj11Tg008Jj29Tg008jj18Tg00?=j23Tg00@6j24Tg00@oj35Tg00B1j26Tg00C3j47Tp,2RTR0#:g00:e#0#0#0#0#0#0#2#1g00;J'9#8g00<Bf2R1,30f1R2f0R3'4p,2AF=5011623C7W1W0W2o"). Qed.

(* [comment removed for export] *)
Lemma asta_evt : forall Σ F0 fs0 Pm Q, (forall ms, Pm ms -> evt asegs Q ms) ->
  cps asegs (ASTA RT Σ (PMfd F0 fs0) Pm) (ASTA RT Σ (PMfd F0 fs0) Q).
Proof.
ltac2:(KReplay.run1 (kr_t_D_defs ()) ["Kit"] "h02F0h11Hh22Pmh31Qh43fs0h52moh62msh71xh82Σp;1p;2p;3p;;p;4g00>Ej1?Tg006dj10Tg007Ij13Tg007gj12Tg008Jj2>Tg008jj1;Tg00D3j3:Tg00Dgj24Tg00?=j35Tg00@6j36j2=Tg009Jj27Tg00Edj38Tg00Fil;9Tg00Ggj41Tg00H`j3<Tp,2RTR0#?g00:e#0#0#0#0#0#0#3#2g00;J'>#;g00<Bg00IUR1p-0R2]7P2\1f2R2f0R3O1g002dR4f1R57:2[^61P4g003\g00J\g00KWg00LUf5R1,40P2g00MTf6=503f4R6=613'7W5P5f3R79816P3M;9P0P11=67R7P2C1P0P1P7P5C15<4eW1W3W2W4W0W8o"). Qed.

(* [comment removed for export] *)
Lemma ASTA_conseq : forall Σ PMc Pm Pm' c, ASTA RT Σ PMc Pm c -> (forall ms, Pm ms -> Pm' ms) -> ASTA RT Σ PMc Pm' c.
Proof.
ltac2:(KReplay.run1 (kr_t_D_defs ()) ["Kit"] "h02moh11Hh22H0h32HPh43PMch52Pmh63Pm'h71ch82msh91xh:2Σp;1p;5p;2p;3p;:g00>Ej15Tg00Ggj50Tg00Dgj23Tg00?=j31Tg009Jj22Tg00NJl:4Tp,2RTR0#5g00MTR1p-0R2[g00IUR3P2[P2^93g00OKP0f4R2f3R4f2R5f0R6D0P2P6O1P2f1R7O1[^83g003\f6R3,30P2P4f7R2=106P3P6O1'2X01R8P8P5P7P6f8=106P2P6O1'2X01P6O1P6W2X01M:4P0P3f5P4P5D0eW3W1W7W6W5W4W:o"). Qed.

Lemma ASTA_ex : forall {X} Σ PMc (Pm : X -> machine_state -> Prop) c,
  ASTA RT Σ PMc (fun ms => exists x, Pm x ms) c -> exists x, ASTA RT Σ PMc (Pm x) c.
Proof.
ltac2:(KReplay.run1 (kr_t_D_defs ()) ["Kit"] "h01xh11Hh23PMch32Pmh41Xh51ch62moh72msh82Σp;1p;2p;5p;3p;7p200R0g00P@R1p4p7210p8g00>Ej16Tg00Q>j21Tg00Ggj50Tg00Dgj22Tg00?=j35Tg009Jj24TP1j73Tp,2RTR1#6g00MTR2p-0R3[f2R4g00IUR5P3[[g00OKP1f3R3P4f5R6P3f0R7f1R8O2X06'1X75P7D0g003\P6f4R5,21P4A5167P5P7O1'4X62P8P7F3P1P6P5P3P7O1P4D0X06,16eW1W5W3W2W8X40o"). Qed.

(* [comment removed for export] *)
Lemma ASTA_unpack : forall Σ PMc (Pm : machine_state -> Prop) c, ASTA RT Σ PMc Pm c -> exists ms, Pm ms /\ ASTA RT Σ PMc (eq ms) c.
Proof.
ltac2:(KReplay.run1 (kr_t_D_defs ()) ["Kit"] "p'0h02msh11Hh22H1h32H2h43H2'h52H3h62H4h73PMch82Pmh91ci001ch:2moh;2Σi019cfg_modeli026cfg_msp;1p;5p;2p;3p;4g00>Ej1GTg00Ggj54Tg001Jj2>j3ETg009JR0j21Tg00Q>j29Tg00QXj20Tg00Dgj23Tg00RMj12Tg00SCj3;Tg00T:j28Tg00U3j26Tg00Ugj1=Tg00Vfj1<Tg0000j2DTg00WYj4:Tg00X4j4CTg00XNj2?Tg00YCj1BTg00Z6j2@Tg00?=j3ATf2R1f1R2'?f0R3#B'@p=5f3R4?A12/13p=71?12/@3p=Fp,2RTR5#Gg00MTR6p-0R7[g00IUR8P7[g00OKR7P7P5f4R7P4P1P3D4P7P3O1P5f6R9f5R:1>83R;P1D4'1X08,98[P3P5f7R<P9P:1023D4P0g003\R=f8R>,35R?1012R1#2R@3;A5?@1,89P5P>P@P<P@O1C716?1'1'1P>P3O1P5f:R1f9R?P;1074R4D4'1X08,98P31351%245;=f;R4,35R@10:7R7#2RA;57,8?P5P4PAP1PAO1C716@7'1'1P0f<R7,35R@109:RA#2RB;5A,81P5P7PBP4PBO1C716@A'1P7P3O1P5f>RAf=R@P;10><R<D4'1X08,98P3135A%2<;5<,87P0P@f?R<,3510?>R>#2;5>R>O1%=>#<P5f@R>101?R?#2RBP<PBO1C7135>/6?'1P>P3O1P5fBR?fARBP;1074RCD4'1X08,98[P3P<135B1041R4#2;54O1135?%2C;5C#=#<P5fCRC10@7R7#2R4P?P4O1C7135C/67'1P0P5fDR010A@RA#2R7PCP7O1C71350/6AP0P3O1P5fFR0fERAP;10><R<D4'1X08,98P3P5P0%2<R<PAP<O1C7fGR<,3510B>'6P8P<P3O1P5fIfHR>P;10C?D4'1X08135>RC?FB?R;P0P;O1P5P>P<1>8;R010?BRBD4P9%2BR99;=CA5C9BR=,80R0P5P>P9P<P9O1C7R916CBRB'1RC'1P@P0PCAE8;=%==#<1D8=P:C:P9PBP2P3C:C:C:C:CCW6W5P2P3O2n2001000000121000000W1W4W3P2P3O2n2001000000121000000W1P2P3O2n2001000000121000000W1W2P2P3O2n2001000000121000000W1X:6X08P2P3O2n01100000121102101W9W8W7W;o"). Qed.

End Kit.

(* [comment removed for export] *)
Definition fp_local (W : list (Z * Z)) (P : mem -> Prop) : Prop :=
  forall m m', P m -> (forall a : word, in_ranges W (bv_unsigned a) -> m' a = m a) -> P m'.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition stderr_cells (m : mem) : Prop :=
  ro_cells asegs m GOT_STDERR [C8 (Z_to_bv 64 STDERR_VAR)] /\ ro_cells asegs m STDERR_VAR [C8 (Z_to_bv 64 STDERR_FILE)].
(* [comment removed for export] *)
Definition S_SHORT : Z := 0x22c59.              (* [comment removed for export] *)
Definition S_OVER : Z := 0x1673a.               (* [comment removed for export] *)
Definition drv_consts (m : mem) : Prop :=
  stderr_cells m /\ ro_cells asegs m GOT_SSP [C8 (Z_to_bv 64 SSP_GUARD)] /\ ro_cells asegs m GOT_LLVMINIT [C8 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ acc asegs m S_SHORT 31 /\ acc asegs m S_OVER 31.

Lemma drv_ssp : forall m g, drv_consts m -> ro_cells asegs m SSP_GUARD [C8 g] -> ssp_cells m.
Proof.
ltac2:(KReplay.run1 (kr_t_D_defs ()) [] "h02H0h11gh21Hh32HGh42_Hh53_H0h61mp;1p;2p;4p;3g006dj13Tg007Ij1@Tg007gj1<Tg00[2j1ATg00[Tj1GTg00\Qj1?Tg00]Pj2>Tg00^6j11Tg00^nj1BTg00_Nj17Tg00`3j1FTg009JR0j20Tg00`Qj1;Tg00WYj4ETg00X4j4DTg00aNj3CTg00anj4:Tg00bgj4=Tg00c\R1f1R2f0R33Cp=2g002dR4P2g00dTP3C:p=4P4P2g00eOP3C:p=6P4P2g00fNP3C=p=9P4P2g00gHP3C=p=8P4P2g00hAR4P3C:p=5g00:eR5#3#3#3R6#3#3#3#@R7#<R8%@6#<#A[%G2P0f2R6#?1>74#1%B1R1'2R4,46g00i>,>7#1/21R7,66%75#7#7#7#FR5,961865'0'0'0f3%16/21'5f4R9#;[P3%?9f5R9/44169719951895'0'0'0P0f6R0/44160719051805'0'0f7%10/21'5f8R0#;[P31404f9R0/6719051805'0'0f:R5%10/21'5P8f<R0/44%13/21,50'0X18P5f;R0/44%15/21,50P6P3CECDW3W5W2P2P3O2n2001000000120000000W0W4P2P3O2n2001000000121000000W0X18W6o"). Qed.

(* [comment removed for export] *)
Definition drv_cell (x : Z) : Prop :=
  (ERRNO_A <= x < ERRNO_A + 4) \/ (SSP_GUARD <= x < SSP_GUARD + 8) \/ (g_read_stage <= x < g_read_stage + 65536).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Drv.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
(* [comment removed for export] *)
Variable LIB : mem -> Prop.
(* [comment removed for export] *)
Variable argvb : list (list byte).
Variable fs : Fs.

(* [comment removed for export] *)
Definition CLX (so : stdout_st) (m : mem) : Prop :=
  OUT_rep so m /\ ERR_rep m /\ XENV m /\ LIB m /\ (exists g, ro_cells asegs m SSP_GUARD [C8 g])
  /\ (exists v, rw_cells asegs m ERRNO_A [C4 v]) /\ stk asegs m g_read_stage (g_read_stage + 65536).

(* [comment removed for export] *)
Definition argv_rep (m : mem) (ap : Z) : Prop :=
  exists ptrs : list word, u64arr asegs m ap ptrs /\ length ptrs = Nat.min 2 (length argvb)   (* [comment removed for export] *)
    /\ (forall i s p, nth_error argvb i = Some s -> nth_error ptrs i = Some p ->
         bytes_at asegs m (bv_unsigned p) (s ++ [Z_to_bv 8 0])
         /\ ap + 8 * Z.of_nat (length argvb) <= bv_unsigned p /\ bv_unsigned p + Z.of_nat (length s) + 1 <= USTACK_TOP - 16)
    (* [comment removed for export] *)
    /\ (forall i s p, nth_error argvb i = Some s -> nth_error ptrs i = Some p ->
         exists slack, bytes_at asegs m (bv_unsigned p + Z.of_nat (length s) + 1) slack
           /\ (- (bv_unsigned p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
           /\ bv_unsigned p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 16).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CREDIT_DRV : Z := 2^36 + 2^30.

(* [comment removed for export] *)
Definition sigma0_ok (Σ : rts RT) (usp : Z) : Prop :=
  rt_live RT Σ = [] /\ rt_frames RT Σ = [] /\ CREDIT_DRV <= rt_credit RT Σ /\ usp <= rt_sp0 RT Σ
  /\ 0x7fff80000000 <= rt_sp0 RT Σ    (* [comment removed for export] *).

(* [comment removed for export] *)
Definition START (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (entry_st (Z_to_bv 64 MAIN_RA) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1
             (Z_to_bv 64 (Z.of_nat (length argvb))) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc a_main m)) c
    /\ ART RT Σ m /\ mem_inv asegs m /\ CLX stdout_init m /\ argv_rep m ap
    /\ stk asegs m (rt_sp0 RT Σ - STACK_WIN) usp /\ sigma0_ok Σ usp
    /\ usp mod 16 = 0 /\ usp < ap /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp.

(* [comment removed for export] *)
Definition main_frame (m : mem) (usp : Z) (s0 s1 s2 s3 s4 s5 s6 s7 : word) : Prop :=
  exists junk, rw_cells asegs m (usp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 MAIN_RA)].

(* [comment removed for export] *)
Definition MAINCTX (Σ : rts RT) (so : stdout_st) (usp ap : Z) (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ CLX so m /\ argv_rep m ap /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7
  /\ stk asegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 80)
  /\ usp mod 16 = 0 /\ usp < ap /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ.

(* [comment removed for export] *)
Definition path_b : list byte := nth 1 argvb [].

(* [comment removed for export] *)
Definition path_slack (m : mem) (path : Z) : Prop :=
  exists slack, bytes_at asegs m (path + Z.of_nat (length path_b) + 1) slack
    /\ (- (path + Z.of_nat (length path_b) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ path + Z.of_nat (length path_b) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 16.

(* [comment removed for export] *)
Definition OPEN (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap path : Z) (gp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (entry_st (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
             (Z_to_bv 64 path) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc e_open m)) c
    /\ MAINCTX Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m /\ sigma0_ok Σ usp
    /\ bytes_at asegs m path (path_b ++ [Z_to_bv 8 0]) /\ ap < path /\ path + Z.of_nat (length path_b) + 1 <= USTACK_TOP - 16
    /\ path_slack m path.

(* [comment removed for export] *)
Definition FAILED (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap path : Z) (gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (ret_st (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 2) s1 (Z_to_bv 64 path)
              s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m) c
    /\ MAINCTX Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m /\ sigma0_ok Σ usp
    /\ bytes_at asegs m path (path_b ++ [Z_to_bv 8 0]) /\ ap < path /\ path + Z.of_nat (length path_b) + 1 <= USTACK_TOP - 16
    /\ path_slack m path.

(* [comment removed for export] *)
Definition OPENED (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap path : Z) (gp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) ent,
    ASTA RT Σ (PMfd (fd_insert fds0 (Z_to_bv 64 3) ent) fs)
      (ret_st (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) (Z_to_bv 64 2) s1 (Z_to_bv 64 path)
              s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 3) m) c
    /\ MAINCTX Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m /\ sigma0_ok Σ usp
    /\ bytes_at asegs m path (path_b ++ [Z_to_bv 8 0]) /\ ap < path /\ path + Z.of_nat (length path_b) + 1 <= USTACK_TOP - 16
    /\ open_ent path_b fs = Some ent /\ path_slack m path.

(* [comment removed for export] *)
Definition EXIT (code : Z) : config -> Prop := EXITc fs code.

End Drv.
