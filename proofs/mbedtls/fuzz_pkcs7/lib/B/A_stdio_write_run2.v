(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ShapeX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_stdio_defs A_stdio_write_run1 A_code_de000_df000 A_code_e3000_e4000       .
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_A_stdio_write_run2 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "sw_regs_but"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_add"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.ret_ok"; "mem_sw2"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run2 ()) "(0.(1.(2.&40.)(3.O1.(4.&5.+2.$5.))(3.O2.(4.&5.+2.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+8.$5.))(3.O2.(4.&5.+8.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+9.$5.))(3.O2.(4.&5.+9.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+15.$5.))(3.O2.(4.&5.+15.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+3.$5.))(3.O2.(4.&5.+3.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+4.$5.))(3.O2.(4.&5.+4.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+17.$5.))(3.O2.(4.&5.+17.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+18.$5.))(3.O2.(4.&5.+18.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+19.$5.))(3.O2.(4.&5.+19.$5.)))(0.(1.(2.&40.)(3.O1.(4.&5.+1:.$5.))(3.O2.(4.&5.+1:.$5.)))(1.(2.&40.)(3.O1.(4.&5.+1;.$5.))(3.O2.(4.&5.+1;.$5.)))))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L25050322224.7L46395073080.7L51796643714.7L68704157111.7L7422712323.7 00000500600;00@00AS1k1KSS1k1KS1k1KS". (* [comment removed for export] *)
Lemma sw_c1_eq : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pk,$8.P,(1.(2.&40.)(3.R4.(4.&5.+:.$5.))(9.&40.R1.))P,(1.(2.&40.)(3.R5.(4.&5.+16.$5.))(9.&40.R2.))P,(0.(:.=R3.)(;.R3.+80000000.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R8.(4.&40.+>6744.$5.)R7.R6.)(?.$10.R1.(4.&40.+>674<.$5.)R7.R6.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R5.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(3.R8.(4.&5.+13.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(3.R8.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(3.R8.(4.&5.+12.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(3.R8.(4.&5.+16.$5.)))(11.R8.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_e3394 D_e3394.
    stepn F_de150 D_de150.
    stepn F_de154 D_de154.
    stepb_tk F_de158 D_de158 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_de184 D_de184 (0x0e6748 : word) ltac:(bveq).
    stepb_ft F_e3398 D_e3398 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L18468513025.10L25056563258.10L28303469649.10L46393059122.10L51794627208.10L68710529213.10L7416373001.10 L892735127.10  00000500:00C00D00I00N00O00YS1k1KS1k1KS3rem3REMSS1k1KS1k1KSS1k3rem2NE". (* [comment removed for export] *)
Lemma sw_c1_ne : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pk,$8.Prem,$8.P,(1.(2.&40.)(3.R5.(4.&5.+:.$5.))(9.&40.R2.))P,(1.(2.&40.)(3.R6.(4.&5.+16.$5.))(9.&40.R2.))P,(0.(:.=R4.)(;.R4.+80000000.))P,(0.(:.=R4.)(;.R4.(12.+2.+40.)))P,(13.(1.$8.R6.R5.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R;.(4.&40.+>6744.$5.)R:.R9.)(?.$10.R1.(4.&40.+>67=8.$5.)R:.R9.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R8.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(3.R;.(4.&5.+13.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(3.R;.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(3.R;.(4.&5.+12.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(3.R;.(4.&5.+16.$5.)))(11.R;.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_e3394 D_e3394.
    stepn F_de150 D_de150.
    stepn F_de154 D_de154.
    stepb_tk F_de158 D_de158 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_de184 D_de184 (0x0e6748 : word) ltac:(bveq).
    stepb_tk F_e3398 D_e3398 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L25050322224.7L46395073080.7L51796643714.7L68704157111.7L7422712323.7 00000500600;00@00AS1k1KSS1k1KS1k1KS". (* [comment removed for export] *)
Lemma sw_c2_eq : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pk,$8.P,(1.(2.&40.)(3.R4.(4.&5.+:.$5.))(9.&40.R1.))P,(1.(2.&40.)(3.R5.(4.&5.+16.$5.))(9.&40.R2.))P,(0.(:.=R3.)(;.R3.+80000000.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R8.(4.&40.+>67<<.$5.)R7.R6.)(?.$10.R1.(4.&40.+>674<.$5.)R7.R6.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R5.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(3.R8.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(3.R8.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(3.R8.(4.&5.+12.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(3.R8.(4.&5.+16.$5.)))(11.R8.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom k Ha0 Hs6 K.
  eexists. split.
  - stepn F_e341c D_e341c.
    stepn F_de150 D_de150.
    stepn F_de154 D_de154.
    stepb_tk F_de158 D_de158 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_de184 D_de184 (0x0e67d0 : word) ltac:(bveq).
    stepn F_e3420 D_e3420.
    stepb_tk F_e3424 D_e3424 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L18468513025.10L25056563258.10L28303469649.10L46393059122.10L51794627208.10L68710529213.10L7416373001.10 L892735127.10  00000500:00C00D00I00N00O00YS1k1KS1k1KS3rem3REMSS1k1KS1k1KSS1k3rem2NE". (* [comment removed for export] *)
Lemma sw_c2_ne : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Pk,$8.Prem,$8.P,(1.(2.&40.)(3.R5.(4.&5.+:.$5.))(9.&40.R2.))P,(1.(2.&40.)(3.R6.(4.&5.+16.$5.))(9.&40.R2.))P,(0.(:.=R4.)(;.R4.+80000000.))P,(0.(:.=R4.)(;.R4.(12.+2.+40.)))P,(13.(1.$8.R6.R5.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R;.(4.&40.+>67<<.$5.)R:.R9.)(?.$10.R1.(4.&40.+>67=8.$5.)R:.R9.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R8.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(3.R;.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(3.R;.(4.&5.+14.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(3.R;.(4.&5.+12.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(3.R;.(4.&5.+16.$5.)))(11.R;.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom k rem Ha0 Hs6 K REM NE.
  eexists. split.
  - stepn F_e341c D_e341c.
    stepn F_de150 D_de150.
    stepn F_de154 D_de154.
    stepb_tk F_de158 D_de158 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
    stepret F_de184 D_de184 (0x0e67d0 : word) ltac:(bveq).
    stepn F_e3420 D_e3420.
    stepb_ft F_e3424 D_e3424 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00S0?L10280736971.36L13407836438.36L17092638480.36L18269819461.36L18465319169.36L20761114571.36L2113765295.36 L23059327388.36L25788507542.36L30353437961.36L30615705186.36L31423039979.36L34746617165.36L41354176210.36L42162907784.36L42610603118.36L43133927157.36L43583623536.36L50303523641.36L51752061730.36L52393267191.36L53814970162.36L54426471177.36L55384194001.36L55994841076.36L56531911202.36L58117285038.36L58122910131.36L58942869324.36L63389555895.36L64062127316.36L68266315287.36L7004927526.36 L8131977782.36 L8603618994.36 00000700J00V00_00k01201601[01l02302B02S02Z02i03003K03T03`03o04604B04N04U04Y04j05105:05F05M05Y05b06306?06K06LS2fd2FDS3cnt2n03rem3CNT2CRS2su2io4IOloS2su4SUhiS2su2io4IOhiS1f3FhiS2ioS2su2io4SUlo4SUhi4IOlo4IOhi1f3Flo3FhiS2su2io4SUhi4IOhiS2fd2FDS3cnt2n03CNT2N0S2su2io4SUlo4IOloS2n02N0S3cnt2n03CNT2N0S1f3FloS2su2io4SUlo4SUhi4IOlo4IOhiS2su4SUhiS2su2io4IOhiS3cnt2n03CNT2N0S2fd2FDS2su2io4IOloS3cnt2n03CNTS2fd2FDS2ioS2su2io4SUlo4IOloS2ic2ICS2su4SUloS3cnt2n03CNTS2ic2ICS3cnt2n03CNTS3rem3REMS2su2io4SUhi4IOhiS3cnt2n03CNTS3cnt2n03CNTS". (* [comment removed for export] *)
Lemma sw_retry_a : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Psu,$8.Pf,$8.Pfd,$8.Pio,$8.Pic,$8.Pcnt,$8.Pn0,$8.Prem,$8.Pb0,(2.&40.)P,(1.(2.&40.)(3.R<.(4.&5.+:.$5.))(9.&40.R4.))P,(1.(2.&40.)(3.R=.(4.&5.+13.$5.))(9.&40.R7.))P,(1.(2.&40.)(3.R>.(4.&5.+12.$5.))(9.&40.R7.))P,(1.(2.&40.)(3.R?.(4.&5.+16.$5.))(9.&40.R5.))P,(1.(2.&40.)(3.R10.(4.&5.+9.$5.))(9.&40.R<.))P,(1.(2.&40.)(3.R11.(4.&5.+2.$5.))(9.&40.(14.R>.+70.)))P,(:.(15.+100000000.+70.)R?.)P,(:.R10.+800000000000.)P,(:.+?:360.R10.)P,(:.(15.R11.+>8.)+?;358.)P,(:.(14.R13.+68.)R10.)P,(:.(15.R11.+10.)(14.R14.+48.))P,(0.(:.+1.R11.)(:.R11.+2.))P,(0.(:.+1.R11.)(:.R11.R10.))P,(;.R11.(12.+2.+3>.))P,(:.R13.R11.)P,(;.R12.(12.+2.+3>.))P,(:.(15.(16.&40.R12.)R14.)(12.+2.+40.))P,(1.$17.(18.$>.R1=.(9.&40.(14.R1;.+70.))#70.)$19.)P,(1.(7.(1:.(2.&8.)))(1;.$>.R1>.(9.&40.R19.)#8.)(1<.(1:.(2.&8.))(1=.#8.R14.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1?.(9.&40.(15.R1:.+8.))#8.)(1<.(1:.(2.&8.))(1=.#8.(9.&40.R17.))))P,(1.(7.(1:.(2.&8.)))(1;.$>.R20.(9.&40.(15.R1=.+78.))#4.)(1<.(1:.(2.&8.))(1=.#4.(9.&40.R1<.))))P,(0.(;.=R1=.)(;.R1=.+80000000.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R24.(4.&40.+>67=8.$5.)R23.R22.)(?.$10.R1.(4.&40.+>67<8.$5.)(1>.(1>.R23.(9.&40.R1>.)(1=.#8.(9.&40.(15.(16.&40.R19.)R1<.))))(9.&40.(15.R1>.+8.))(1=.#8.(9.&40.(14.R1;.R1<.))))R22.))(0.(1.(2.&40.)(3.R1.(4.&5.+11.$5.))(9.&40.+42.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R1?.))(0.(1.(2.&40.)(3.R1.(4.&5.+;.$5.))(9.&40.R1>.))(0.(1.(2.&40.)(3.R1.(4.&5.+<.$5.))(9.&40.R1=.))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(9.&40.R1=.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(9.&40.R1>.))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(9.&40.R1>.))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(9.&40.(14.R1:.R1<.)))(11.R24.R1.)))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom su f fd io ic cnt n0 rem b0
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi IC CNT N0 CR REM B0 SOK Mb0 Mn0 Mfd FD.
  pose proof (u64_range b0) as Hb0.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_e3428 D_e3428 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_e342c D_e342c (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_e3430 D_e3430. rewrite Ha0, (sltu_ge n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_e3434 D_e3434.
    stepn F_e3438 D_e3438. rewrite Hs3.
    (* [comment removed for export] *)
    stepLD8 F_e343c D_e343c b0.
    (* [comment removed for export] *)
    stepn F_e3440 D_e3440.
    stepn F_e3444 D_e3444. rewrite v_and_0_l.
    stepn F_e3448 D_e3448. rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_e344c D_e344c. rewrite (v_add_wZ b0 cnt) by lia.
    (* [comment removed for export] *)
    stepST F_e3450 D_e3450 (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_tk F_e3454 D_e3454 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    stepn F_e33ec D_e33ec.
    stepn F_e33f0 D_e33f0.
    stepn F_e33f4 D_e33f4. rewrite Hs3, (v_add_ZZ' io 8) by lia.
    (* [comment removed for export] *)
    stepLD8 F_e33f8 D_e33f8 (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_e33fc D_e33fc. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_e3400 D_e3400 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_e3404 D_e3404. rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.
    (* [comment removed for export] *)
    stepn F_e3408 D_e3408. rewrite (v_sub_Z n0 cnt) by lia.
    stepST F_e340c D_e340c (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_e3410 D_e3410.
    stepn F_e3414 D_e3414.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00V0?L10280736968.37L12029941357.37L13407836437.37L16717740147.37L18269819462.37L20761114568.37L22660558467.37L23059327391.37L23782380733.37L25788507541.37L28792676756.37L30353437962.37L30615705185.37L31423039976.37L34746617166.37L3755985812.37 L39994935250.37L42162907787.37L42610603117.37L43133927158.37L44323377073.37L47491862257.37L48229675763.37L50303523642.37L5054388755.37 L51752061729.37L53814970161.37L54426471178.37L58055266580.37L58117285037.37L58652200285.37L62020616823.37L63568846513.37L64062127319.37L65619408082.37L67748056979.37L68048261367.37L7004927525.37 00000700M00_00k01401;01D01i02:02K02\02c03903J03`03k03o04604Q04Z04[05105=05M05Y05`05k06206C06L06W06h06i07207607B07S07^S2fd2FDS3cnt2n03rem2N02CR3REMS3cnt2n03rem2N02CRS2su2io4IOhiS2su4SUhiS1f3FhiS2n14N1hiS2su2io4SUlo4SUhi4IOlo4IOhi1f3Flo3FhiS3cnt2n02n12N02N1S2su2io4SUhi4IOhiS2su2io4SUhi4IOhiS2fd2FDS3cnt2n03rem2N02CR3REMS2su2io4SUlo4IOloS3cnt2n03rem2N02CR3REMS3cnt2n02N0S2ioS1f3FloS2su2io4SUlo4SUhi4IOlo4IOhiS2su4SUhiSS3cnt2n03rem2N02CR3REMS2su2io4IOhiS3cnt3rem2CR3REMS2su2io4IOloS2fd2FDS3cnt2n02N0S2fd2FDS2su2io4SUhi4IOhiS2su4SUloS3cnt2n02N0S2su2io4SUlo4IOloSS3rem3REMS2ioS2su2io4IOloS2su2io4SUlo4IOloS3cnt2n02N0". (* [comment removed for export] *)
Lemma sw_retry_b : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Psu,$8.Pf,$8.Pfd,$8.Pio,$8.Pcnt,$8.Pn0,$8.Pn1,$8.Prem,$8.Pb1,(2.&40.)P,(1.(2.&40.)(3.R<.(4.&5.+:.$5.))(9.&40.R5.))P,(1.(2.&40.)(3.R=.(4.&5.+13.$5.))(9.&40.R7.))P,(1.(2.&40.)(3.R>.(4.&5.+12.$5.))(9.&40.+2.))P,(1.(2.&40.)(3.R?.(4.&5.+16.$5.))(9.&40.R5.))P,(1.(2.&40.)(3.R10.(4.&5.+9.$5.))(9.&40.R<.))P,(1.(2.&40.)(3.R11.(4.&5.+2.$5.))(9.&40.(14.R>.+70.)))P,(:.(15.+100000000.+70.)R?.)P,(:.R10.+800000000000.)P,(:.+?:360.R10.)P,(:.(15.R11.+>8.)+?;358.)P,(:.(14.R13.+68.)R10.)P,(:.(15.R11.+20.)(14.R14.+48.))P,(0.(:.=R10.)(;.R10.R11.))P,(:.R12.R?.)P,(;.R10.(12.+2.+3>.))P,(:.(14.R14.R13.)R12.)P,(;.R13.(12.+2.+3>.))P,(:.(15.(16.&40.R12.)R14.)(12.+2.+40.))P,(1.$17.(18.$>.R1=.(9.&40.(14.R1;.+70.))#70.)$19.)P,(1.(7.(1:.(2.&8.)))(1;.$>.R1>.(9.&40.(15.R19.+8.))#8.)(1<.(1:.(2.&8.))(1=.#8.(9.&40.R17.))))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1?.(9.&40.(15.R1:.+10.))#8.)(1<.(1:.(2.&8.))(1=.#8.R15.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R20.(9.&40.(15.R1;.+18.))#8.)(1<.(1:.(2.&8.))(1=.#8.(9.&40.R18.))))P,(1.(7.(1:.(2.&8.)))(1;.$>.R21.(9.&40.(15.R1>.+78.))#4.)(1<.(1:.(2.&8.))(1=.#4.(9.&40.R1=.))))P,(0.(;.=R1>.)(;.R1>.+80000000.))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R25.(4.&40.+>67=8.$5.)R24.R23.)(?.$10.R1.(4.&40.+>67<8.$5.)(1>.(1>.R24.(9.&40.(15.R1?.+10.))(1=.#8.(9.&40.(15.(16.&40.R1:.)(14.R1>.R1=.)))))(9.&40.(15.R1?.+18.))(1=.#8.(9.&40.(14.R1<.(14.R1>.R1=.)))))R23.))(0.(1.(2.&40.)(3.R1.(4.&5.+11.$5.))(9.&40.+42.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))(9.&40.R20.))(0.(1.(2.&40.)(3.R1.(4.&5.+;.$5.))(9.&40.(15.R1?.+10.)))(0.(1.(2.&40.)(3.R1.(4.&5.+<.$5.))(9.&40.+1.))(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))(9.&40.+1.))(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))(9.&40.R1?.))(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))(9.&40.(15.R1?.+10.)))(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))(9.&40.(14.R1;.R1>.)))(11.R25.R1.)))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom su f fd io cnt n0 n1 rem b1
         Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi N0 CR REM N1 N1hi B1 SOK Mn0 Mb1 Mn1 Mfd FD.
  pose proof (u64_range b1) as Hb1.
  eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_e3428 D_e3428 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).
    (* [comment removed for export] *)
    stepLD8 F_e342c D_e342c (Z_to_bv 64 n0).
    (* [comment removed for export] *)
    stepn F_e3430 D_e3430. rewrite Ha0, (sltu_lt n0 cnt) by lia.
    (* [comment removed for export] *)
    stepn F_e3434 D_e3434.
    stepn F_e3438 D_e3438. rewrite Hs3, (v_add_ZZ' io 16) by lia.
    (* [comment removed for export] *)
    stepLD8 F_e343c D_e343c b1.
    (* [comment removed for export] *)
    stepn F_e3440 D_e3440.
    stepn F_e3444 D_e3444. rewrite (v_and_m1_l n0) by lia.
    stepn F_e3448 D_e3448. rewrite Ha0, (v_sub_Z cnt n0) by lia.
    (* [comment removed for export] *)
    stepn F_e344c D_e344c. rewrite (v_add_wZ b1 (cnt - n0)) by lia.
    (* [comment removed for export] *)
    stepST F_e3450 D_e3450 (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepb_ft F_e3454 D_e3454 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepn F_e3458 D_e3458.
    stepn F_e345c D_e345c.
    stepn F_e33f0 D_e33f0.
    stepn F_e33f4 D_e33f4. rewrite Hs3, (v_add_ZZ' io 24) by lia.
    (* [comment removed for export] *)
    stepLD8 F_e33f8 D_e33f8 (Z_to_bv 64 n1).
    (* [comment removed for export] *)
    stepn F_e33fc D_e33fc. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.
    (* [comment removed for export] *)
    stepLD F_e3400 D_e3400 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    (* [comment removed for export] *)
    stepn F_e3404 D_e3404. rewrite Hs2. vals_lit.
    (* [comment removed for export] *)
    stepn F_e3408 D_e3408. rewrite (v_sub_Z n1 (cnt - n0)) by lia.
    stepST F_e340c D_e340c (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_e3410 D_e3410.
    stepn F_e3414 D_e3414.
    apply mst_refl.
  - unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) := ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run2 ()) "(1>.(1>.(1>.O4.(9.&40.(15.O3.+20.))(1=.#8.(1?.O2.O1.)))(9.&40.(15.O3.+28.))(1=.#8.O2.))(9.&40.(15.O3.+38.))(1=.#8.O2.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L10121903703.38L12312047713.38L16602618209.38L18255059343.38L19806447020.38L20763130881.38L22039186417.38L23061340758.38L23239445089.38L28041405809.38L28345629740.38L3200043361.38 L41437587813.38L41962448993.38L42177634626.38L46563833311.38L4659297741.38 L50291981665.38L56852889183.38L56969508193.38L57587215532.38L58131885924.38L58817447263.38L60169027681.38L61320992461.38L66360533396.38L67357286477.38L8688146017.38 L9985600753.38 00000400800<00E00L00S00Z01201601=01D01H01L01P01W01^01e01i02002402;02D02K02O02V02a02h02l033S2suS2suS2suS2su4SUhiS1f3FhiS1f3FhiS1f3FloS2su1f4SUlo4SUhi3Flo3FhiS2suS1f3FloS1f3FhiS2suS2suS2suS1f3FloS1f3FhiS1f3FloS2suS1f3FhiS2suS1f3FhiS2su4SUloS1f3FhiS2suS1f3FloS1f3Flo3FhiS1f3FloS2suS1f3Flo". (* [comment removed for export] *)
Lemma sw_done : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write_run2 ()) "Pregs,(6.&5.(2.&40.))Pmem,P,(2.&40.)(7.(2.&8.))Prom,P,(2.&40.)(7.(2.&8.))Psu,$8.Pf,$8.Pl,(2.&40.)Pbufp,(2.&40.)Pbufsz,(2.&40.)Pcan,(2.&40.)Pret,(2.&40.)Ps0v,(2.&40.)Ps1v,(2.&40.)Ps2v,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)P,(1.(2.&40.)(3.R11.(4.&5.+2.$5.))(9.&40.(14.R>.+70.)))P,(1.(2.&40.)(3.R12.(4.&5.+8.$5.))R=.)P,(1.(2.&40.)(3.R13.(4.&5.+9.$5.))(9.&40.R?.))P,(1.(2.&40.)(3.R14.(4.&5.+15.$5.))(9.&40.+65<:=0.))P,(:.(15.+100000000.+70.)R12.)P,(:.R13.+800000000000.)P,(:.+?:360.R13.)P,(:.(15.R14.+>8.)+?;358.)P,(20.R10.)P,(1.(7.(1:.(2.&8.)))(1;.$>.R19.(9.&40.(14.R17.+8.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1:.(9.&40.(14.R18.+10.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1;.(9.&40.(14.R19.+18.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1<.(9.&40.(14.R1:.+20.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1=.(9.&40.(14.R1;.+28.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1>.(9.&40.(14.R1<.+30.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R1?.(9.&40.(14.R1=.+38.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R20.(9.&40.(14.R1>.+40.))#8.)(1<.(1:.(2.&8.))(1=.#8.R11.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R21.(9.&40.(14.R1?.+48.))#8.)(1<.(1:.(2.&8.))(1=.#8.R1:.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R22.(9.&40.+65<:=0.)#8.)(1<.(1:.(2.&8.))(1=.#8.R1;.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R23.(9.&40.(15.R20.+58.))#8.)(1<.(1:.(2.&8.))(1=.#8.R1>.)))P,(1.(7.(1:.(2.&8.)))(1;.$>.R24.(9.&40.(15.R21.+60.))#8.)(1<.(1:.(2.&8.))(1=.#8.R1>.)))(<.(6.&5.(2.&40.))Lregs',(6.&5.(2.&40.))(0.(=.$>.(?.$10.R27.(4.&40.+>674<.$5.)R26.R25.)(?.$10.R1.R1>.(21.R26.R23.R21.R20.)R25.))(0.(1.(2.&40.)(3.R1.(4.&5.+:.$5.))R22.)(0.(1.(2.&40.)(3.R1.(4.&5.+2.$5.))(9.&40.R24.))(0.(1.(2.&40.)(3.R1.(4.&5.+1.$5.))R1>.)(0.(1.(2.&40.)(3.R1.(4.&5.+8.$5.))R1=.)(0.(1.(2.&40.)(3.R1.(4.&5.+9.$5.))R1<.)(0.(1.(2.&40.)(3.R1.(4.&5.+12.$5.))R1;.)(0.(1.(2.&40.)(3.R1.(4.&5.+13.$5.))R1:.)(0.(1.(2.&40.)(3.R1.(4.&5.+14.$5.))R19.)(0.(1.(2.&40.)(3.R1.(4.&5.+15.$5.))R18.)(0.(1.(2.&40.)(3.R1.(4.&5.+16.$5.))R17.)(0.(1.(2.&40.)(3.R1.(4.&5.+3.$5.))(3.R27.(4.&5.+3.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+4.$5.))(3.R27.(4.&5.+4.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+17.$5.))(3.R27.(4.&5.+17.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+18.$5.))(3.R27.(4.&5.+18.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+19.$5.))(3.R27.(4.&5.+19.$5.)))(0.(1.(2.&40.)(3.R1.(4.&5.+1:.$5.))(3.R27.(4.&5.+1:.$5.)))(1.(2.&40.)(3.R1.(4.&5.+1;.$5.))(3.R27.(4.&5.+1;.$5.)))))))))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom su f l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v
         Hsp Hs0 Hs1 Hs5 SUlo SUhi Flo Fhi Hret
         M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz.
  unfold mem_sw2. eexists. split.
  - (* [comment removed for export] *)
    stepLD F_e339c D_e339c (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_e33a0 D_e33a0 (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_e33a4 D_e33a4.
    (* [comment removed for export] *)
    stepST F_e33a8 D_e33a8 (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
    stepST F_e33ac D_e33ac (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
    stepST F_e33b0 D_e33b0 (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).
    (* [comment removed for export] *)
    stepn F_e33b4 D_e33b4. rewrite Hs0.
    stepLD F_e33b8 D_e33b8 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_e33bc D_e33bc (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_e33c0 D_e33c0 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD F_e33c4 D_e33c4 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_e33c8 D_e33c8 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_e33cc D_e33cc (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_e33d0 D_e33d0 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_e33d4 D_e33d4 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_e33d8 D_e33d8 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_e33dc D_e33dc (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepLD F_e33e0 D_e33e0 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
    stepn F_e33e4 D_e33e4. rewrite Hsp. sp_renorm.
    replace (su - 0)%Z with su by lia.
    stepret F_e33e8 D_e33e8 ret ltac:(reflexivity).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
