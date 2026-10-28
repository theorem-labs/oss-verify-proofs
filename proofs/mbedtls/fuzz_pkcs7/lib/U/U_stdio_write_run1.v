(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ShapeX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_defs U_code_3e000_3f000.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_stdio_write_run1 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_sub"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_add"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_sltu"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_xor"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_and"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_subw"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.sw_file"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.ssp_cells"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "mem_sw1"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L11319357266.4L26983627995.4L61883795790.4L9301361693.4 00000600=00D00NS1a2H2S1a1b1HS1a1b1HS1a1b1H2H2". (* [comment removed for export] *)
Lemma v_sub_Z : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "Pa,$0.Pb,$0.P,(1.(2.=R1.)(2.R1.R2.))P,(3.R3.(4.+2.+40.))(5.(6.&40.)(7.(8.&40.R4.)(8.&40.R3.))(8.&40.(9.R4.R3.)))")
(* [comment removed for export] *).
Proof. intros a b H H2. unfold v_sub. u_norm. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L11321447016.3L26981515745.300000500:S1a1HS1a1H". (* [comment removed for export] *)
Lemma v_add_Z : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "Pa,$0.Pl,(6.&40.)P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))(5.(6.&40.)(:.(8.&40.R3.)R2.)(8.&40.(;.R3.(<.&40.R2.))))")
(* [comment removed for export] *).
Proof. intros a l H. unfold v_add. u_norm. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L30992445322.3L68384130463.300000500:S1c1HS1c1H". (* [comment removed for export] *)
Lemma v_add_wZ : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "Pb,(6.&40.)Pc,$0.P,(1.(2.=R1.)(3.R1.(4.+2.+40.)))(5.(6.&40.)(:.R3.(8.&40.R2.))(8.&40.(;.(<.&40.R3.)R2.)))")
(* [comment removed for export] *).
Proof. intros b c H. unfold v_add. u_norm. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L22555305665.4L56093683742.4L8105207512.4 L9074517989.4 00000600;00A00FS1y2H0S1x1HS1y2H0S1x1H". (* [comment removed for export] *)
Lemma v_add_ZZ' : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "Px,$0.Py,$0.P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))(5.(6.&40.)(:.(8.&40.R4.)(8.&40.R3.))(8.&40.(;.R4.R3.)))")
(* [comment removed for export] *).
Proof. intros. unfold v_add. u_norm. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L11317248263.5L15047223637.5L26985714318.5L35445065565.6L38950503102.5L46268770189.7L61885900571.5L9299274312.5 L9666699386.6 00000600700=00E00F00R00X00^00fS1a2HaSS1a2HaS1a1b2HrSS1a1b2Hr3HgeS1b2HbS1b2HbS1a1b2Hr". (* [comment removed for export] *)
Lemma sltu0_xor_ne : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "Pa,$0.Pb,$0.P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))P,(=.(5.$0.R4.R3.))(5.(6.&40.)(>.(8.&40.=)(?.(8.&40.R5.)(8.&40.R4.)))(8.&40.+1.))")
(* [comment removed for export] *).
Proof.
  intros a b Ha Hb Hne. unfold v_sltu, c_ltu, bv_ltu, v_xor.
  rewrite (u_Z2bv a), (u_Z2bv b), (u_Z2bv 0) by lia.
  pose proof (Z_lxor_range a b Ha Hb) as Hr.
  rewrite u_Z2bv by lia.
  destruct (Z.ltb_spec 0 (Z.lxor a b)) as [Hlt|Hge]; [reflexivity|].
  exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L15043407825.1L38955369530.1000001002SS". (* [comment removed for export] *)
Lemma sltu0_xor_eq : forall a : word, v_sltu (Z_to_bv 64 0) (v_xor a a) = Z_to_bv 64 0.
Proof.
  intros a. unfold v_sltu, c_ltu, bv_ltu, v_xor. rewrite Z.lxor_nilpotent.
  rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L11319357266.4L26983627995.4L51113368739.5L61883795790.4L9301361693.4 00000600=00G00N00XS1a2H2S1a1b1HS1a1b1H2H0S1a1b1HS1a1b1H2H2". (* [comment removed for export] *)
Lemma sltu_ge : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "Pa,$0.Pb,$0.P,(1.(2.=R1.)(2.R1.R2.))P,(3.R3.(4.+2.+40.))(5.(6.&40.)(>.(8.&40.R4.)(8.&40.R3.))(8.&40.=))")
(* [comment removed for export] *).
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [lia|reflexivity].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L11319357266.4L12059015339.5L26983627995.4L61883795790.4L9301361693.4 00000:00D00K00R00XS1a1b1H2H2S1a1b1H2H0S1a1b1HS1a1b1HS1b2H2". (* [comment removed for export] *)
Lemma sltu_lt : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "Pa,$0.Pb,$0.P,(1.(2.=R2.)(3.R2.R1.))P,(3.R2.(4.+2.+40.))(5.(6.&40.)(>.(8.&40.R4.)(8.&40.R3.))(8.&40.+1.))")
(* [comment removed for export] *).
Proof.
  intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
  destruct (Z.ltb_spec a b); [reflexivity|lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L11321447016.2L15043033658.2L24928565580.3L26981515745.2L38954701265.2L43507992856.2L68214771681.200000500600>00C00D00I00JS1a1HSS1a1H2H0S1a1HSS1a1HS". (* [comment removed for export] *)
Lemma c_lts_pos_0 : forall a, (0 <= a < 2^63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof.
  intros a H. unfold c_lts, bv_lts. rewrite !bv_signed_small by (u_norm; lia). u_norm.
  destruct (Z.ltb_spec a 0); [lia|reflexivity].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L15043813962.1L38955485601.1000001002SS". (* [comment removed for export] *)
Lemma v_and_0_l : forall (x : word), v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof. intros x. unfold v_and. rewrite (u_Z2bv 0) by lia. rewrite Z.land_0_l. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L11321447016.2L14305402461.2L16256612006.2L26981515745.2L35495549846.2L56759370246.200000500600700<00=00BS1a1HSSS1a1HSS1a1H". (* [comment removed for export] *)
Lemma v_and_m1_l : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "Pa,$0.P,(1.(2.=R1.)(3.R1.(4.+2.+40.)))(5.(6.&40.)(10.(8.&40.+????????????????.)(8.&40.R2.))(8.&40.R2.))")
(* [comment removed for export] *).
Proof.
  intros a H. unfold v_and. u_norm.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  f_equal. apply Z.mod_small. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L11319357266.4L26983627995.4L33339142890.4L61883795790.4L9301361693.4 00000600=00G00N00XS1a2H2S1a1b1HS1a1b1H2H2S1a1b1HS1a1b1H2H2". (* [comment removed for export] *)
Lemma v_subw_small_lit : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "Pa,$0.Pb,$0.P,(1.(2.=R1.)(2.R1.R2.))P,(3.R3.(4.+2.+1?.))(5.(6.&40.)(11.(8.&40.R4.)(8.&40.R3.))(8.&40.(9.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros a b H H2. unfold v_subw. u_norm.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_sw1 (mem : word -> option byte) (su : Z) (ra s0 s1 s2 s3 s4 s5 s6 : word)
           (can : word) (wb n : Z) (s l : word) := ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "(12.(12.(12.(12.(12.(12.(12.(12.(12.(12.(12.(12.(12.O?.(8.&40.(9.O>.+8.))(13.#8.O=.))(8.&40.(9.O>.+10.))(13.#8.O<.))(8.&40.(9.O>.+18.))(13.#8.O;.))(8.&40.(9.O>.+20.))(13.#8.O:.))(8.&40.(9.O>.+28.))(13.#8.O9.))(8.&40.(9.O>.+30.))(13.#8.O8.))(8.&40.(9.O>.+38.))(13.#8.O7.))(8.&40.(9.O>.+40.))(13.#8.O6.))(8.&40.(9.O>.+48.))(13.#8.O5.))(8.&40.(9.O>.+68.))(13.#8.(8.&40.O4.)))(8.&40.(9.O>.+60.))(13.#8.(8.&40.O3.)))(8.&40.(9.O>.+58.))(13.#8.O2.))(8.&40.(9.O>.+50.))(13.#8.O1.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "01F0?L10267740279.35L13247673482.35L13474458130.35L1455345938.35 L15225323513.35L15545203569.35L16446805873.35L17228253041.35L18256855801.35L18350835766.35L19510434194.35L19619008889.35L20101496458.35L20765190007.35L23063935264.35L23282780529.35L24376326070.35L25298379478.35L25528043282.35L26767684465.35L26806332281.35L26861093686.35L27097339769.35L27654056305.35L28150024816.35L28459475961.35L30365869493.35L30395639094.35L31530594962.35L32886582966.35L33413402378.35L33431204209.35L35669973258.35L36396486838.35L37000693881.35L3710204554.35 L37299958905.35L37547679762.35L38923082806.35L40074407314.35L40962413794.35L4149911434.35 L41503823242.35L41530146314.35L42175576628.35L42351292938.35L42415816246.35L42772198257.35L43121487433.35L43583262610.35L44443642377.35L44479417977.35L44904318321.35L44940299190.35L45846897009.35L46074731282.35L47663329870.35L48451251638.35L48873234937.35L48998968689.35L49250003642.35L50256958346.35L5030960889.35 L50686982001.35L50942720310.35L51748215710.35L52208152735.35L54439238581.35L55628064914.35L55849559729.35L56472664074.35L56961508534.35L58129495058.35L61631010322.35L6173188874.35 L62532358935.35L62995386934.35L63569132258.35L6375927161.35 L64155493266.35L65765122442.35L66254805241.35L6626505662.35 L66562573561.35L68660185969.35L7455669394.35 00000700;00D00M00V00Z00^00b00k00o01801A01E01L01d01h01l02702@02D02M02Q02Z02^02g03003703;03D03H03L03P03T03X03a03e03n04704;04D04R04V04Z04^04e04i04m05105:05C05L05U05Y05]05a05j06:06>06G06K06[06_06h06l07007707B07I07R07[07_07c07l08508908=08A08O08X08a08e08n09>09G09K09TS2fd2FDS2suS2su4SUloS2su4SUloS2su4SUhiS2suS2suS2suS2su4SUhiS2suS2su4SUloS2su4SUhiS2suS1f3FhiS2su1f4SUlo4SUhi3Flo3FhiS2suS2suS2wb2wp3WBPS2su4SUloS2suS2su4SUhiS2suS2su4SUhiS2suS2su4SUhiS2su4SUhiS2fd2FDS2suS2su4SUloS2suS2suS2suS2suS2suS2su4SUhiS2suS2su4SUhiS2su4SUloS2suS2su4SUloS2su4SUlo4SUhiS2suS2suS2suS1f3FloS2suS2suS2suS2su4SUhiS2su4SUloS2su4SUloS2su4SUhiS2suS2suS2suS2su4SUloS2wb2wp3WBP4WPhiS2suS2su4SUhiS2suS2wb2wp3WBP4WPhiS2suS2su4SUhiS2suS2suS2fd2FDS2wb2wp3WBPS2fd2FDS2su4SUloS2wp4WPhiS2suS2suS2su4SUloS2su4SUloS2suS2suS2suS2su4SUlo4SUhiS2su4SUhiS2su4SUloS2suS2su4SUhiS2wb2wp3WBP4WPhiS2su4SUhiS2suS2su4SUlo". (* [comment removed for export] *)
Lemma sw_enter : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "Pregs,(14.&5.(6.&40.))Pmem,P,(6.&40.)(15.(6.&8.))Prom,P,(6.&40.)(15.(6.&8.))Psu,$0.Pf,$0.Pwb,$0.Pwp,$0.Pfd,$0.Ps,(6.&40.)Pl,(6.&40.)Pbufp,(6.&40.)Pbufsz,(6.&40.)Pcan,(6.&40.)Pret,(6.&40.)P,(5.(6.&40.)(16.R>.(17.&5.+2.$18.))(8.&40.R;.))P,(5.(6.&40.)(16.R?.(17.&5.+:.$18.))(8.&40.R;.))P,(5.(6.&40.)(16.R10.(17.&5.+;.$18.))R8.)P,(5.(6.&40.)(16.R11.(17.&5.+<.$18.))R8.)P,(5.(6.&40.)(16.R12.(17.&5.+1.$18.))R5.)P,(2.(;.+100000000.+70.)R10.)P,(2.R11.+800000000000.)P,(5.$19.(1:.$1;.R14.(8.&40.(9.R12.+70.))#70.)$1<.)P,(2.+4<000.R12.)P,(2.(;.R13.+>8.)+7=330.)P,(1=.R17.R14.R13.R12.R11.R>.R=.)P,(1>.R18.R=.)P,(1.(3.=R13.)(3.R13.+80000000.))P,(1.(2.=R16.)(3.R16.R15.))P,(3.R16.(4.+2.+40.))P,(3.(;.(9.R17.R18.)(<.&40.R14.))+80000000.)(1?.(14.&5.(6.&40.))Lregs',(14.&5.(6.&40.))(1.(20.$1;.(21.$22.R1?.(17.&40.+41:34.$18.)R1>.R1=.)(21.$22.R1.(17.&40.+41:;<.$18.)(23.R1>.R1<.R12.(16.R1?.(17.&5.+8.$18.))(16.R1?.(17.&5.+9.$18.))(16.R1?.(17.&5.+12.$18.))(16.R1?.(17.&5.+13.$18.))(16.R1?.(17.&5.+14.$18.))(16.R1?.(17.&5.+15.$18.))(16.R1?.(17.&5.+16.$18.))R13.R1:.(9.R19.R1:.)R17.R16.)R1=.))(1.(5.(6.&40.)(16.R1.(17.&5.+11.$18.))(8.&40.+42.))(1.(5.(6.&40.)(16.R1.(17.&5.+:.$18.))(8.&40.R18.))(1.(5.(6.&40.)(16.R1.(17.&5.+;.$18.))(8.&40.(9.R1<.+68.)))(1.(5.(6.&40.)(16.R1.(17.&5.+<.$18.))(8.&40.+2.))(1.(5.(6.&40.)(16.R1.(17.&5.+2.$18.))(8.&40.(9.R1<.+70.)))(1.(5.(6.&40.)(16.R1.(17.&5.+8.$18.))R16.)(1.(5.(6.&40.)(16.R1.(17.&5.+9.$18.))(8.&40.R1;.))(1.(5.(6.&40.)(16.R1.(17.&5.+12.$18.))(8.&40.+2.))(1.(5.(6.&40.)(16.R1.(17.&5.+13.$18.))(8.&40.(9.R1<.+68.)))(1.(5.(6.&40.)(16.R1.(17.&5.+15.$18.))(8.&40.+7=330.))(1.(5.(6.&40.)(16.R1.(17.&5.+16.$18.))(8.&40.(;.(9.R19.R1:.)(<.&40.R16.))))(1.(5.(6.&40.)(16.R1.(17.&5.+3.$18.))(16.R1?.(17.&5.+3.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+4.$18.))(16.R1?.(17.&5.+4.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+17.$18.))(16.R1?.(17.&5.+17.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+18.$18.))(16.R1?.(17.&5.+18.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+19.$18.))(16.R1?.(17.&5.+19.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+1:.$18.))(16.R1?.(17.&5.+1:.$18.)))(5.(6.&40.)(16.R1.(17.&5.+1;.$18.))(16.R1?.(17.&5.+1;.$18.))))))))))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom su f wb wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WBP WPhi SMALL.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_3e2e8 D_3e2e8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_3e2ec D_3e2ec (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_3e2f0 D_3e2f0 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_3e2f4 D_3e2f4 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_3e2f8 D_3e2f8 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_3e2fc D_3e2fc (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_3e300 D_3e300 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_3e304 D_3e304 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_3e308 D_3e308 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_3e30c D_3e30c. rewrite Ha2.
    stepn F_3e310 D_3e310. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_3e314 D_3e314.
    stepLD8 F_3e318 D_3e318 (Z_to_bv 64 0x7d330).
    stepLD8 F_3e31c D_3e31c can.
    stepST F_3e320 D_3e320 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepLD8 F_3e324 D_3e324 (Z_to_bv 64 wp).
    stepLD8 F_3e328 D_3e328 (Z_to_bv 64 wb).
    (* [comment removed for export] *)
    stepn F_3e32c D_3e32c. rewrite (v_sub_Z wp wb) by lia.
    stepn F_3e330 D_3e330.
    (* [comment removed for export] *)
    stepST F_3e334 D_3e334 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) ltac:(sok_frame SOK).
    stepST F_3e338 D_3e338 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 (wp - wb)) ltac:(sok_frame SOK).
    stepST F_3e33c D_3e33c (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_3e340 D_3e340 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
    (* [comment removed for export] *)
    stepn F_3e344 D_3e344. rewrite (v_add_Z (wp - wb) l) by lia.
    stepn F_3e348 D_3e348. rewrite (sltu0_xor_ne wp wb) by lia.
    (* [comment removed for export] *)
    stepb_ft F_3e34c D_3e34c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_3e350 D_3e350.
    replace (v_addi (Z_to_bv 64 (su - 112)) 8) with (Z_to_bv 64 (su - 104))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepn F_3e354 D_3e354.
    (* [comment removed for export] *)
    stepLD F_3e35c D_3e35c (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_3e360 D_3e360.
    stepn F_3e364 D_3e364.
    stepn F_3e368 D_3e368.
    stepn F_3e36c D_3e36c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "01B0?L10282835863.34L13245195114.34L13485030898.34L1448609522.34 L15226972185.34L15543446673.34L16452714641.34L17213722769.34L18267723033.34L18340470742.34L19496128114.34L19621250713.34L20111862122.34L20759015575.34L23057231552.34L23272480401.34L24362082390.34L25525604594.34L26769925265.34L26796293273.34L26875860182.34L27108196505.34L27659976337.34L28139167120.34L28466213913.34L30351340117.34L30389727958.34L31536473458.34L32897481046.34L33411750122.34L33424500369.34L34310552911.34L35685027562.34L36398204758.34L37003141017.34L3720605034.34 L37306688409.34L37562284018.34L38908054486.34L40071871090.34L40960131842.34L41493512810.34L41532353002.34L4156311658.34 L42165005780.34L42357466602.34L42426116566.34L42774373521.34L43131828649.34L43572861042.34L44458245609.34L44489562521.34L44902601361.34L44933602390.34L45841053329.34L46080871666.34L48436722262.34L48888067609.34L48997218961.34L5020092697.34 L50254742634.34L50697281681.34L50944732886.34L51749964926.34L54428568661.34L55622123378.34L55834734929.34L56487751658.34L56972112726.34L57097743095.34L58119382002.34L6158660842.34 L61632692722.34L62985307606.34L63583890690.34L6390954649.34 L64140473458.34L65750890090.34L66269925145.34L66565083929.34L68661910673.34L7457647474.34 00000700;00D00M00V00Z00^00b00k00o01801A01E01L01d01h01l02502902B02F02O02S02\02e02l03003903=03A03E03N03R03V03_03c03l04504904B04P04T04X04\04c04g04k04o05805A05J05S05W05[05_05h05l06506906B06F06J06N06U06\06e06n07207607:07C07G07P07T07b07k08408808A08J08N08WS2fd2FDS2suS2su4SUloS2su4SUloS2su4SUhiS2suS2suS2suS2su4SUhiS2suS2su4SUloS2su4SUhiS2suS1f3FhiS2su1f4SUlo4SUhi3Flo3FhiS2suS2suS2su4SUloS2suS2su4SUhiS2suS2su4SUhiS2suS2su4SUhiS2su4SUhiS2fd2FDS2suS2su4SUloS2suS2suS2suS2wp4WPhiS2suS2suS2su4SUhiS2suS2su4SUhiS2su4SUloS2suS2su4SUloS2su4SUlo4SUhiS2suS2suS2suS1f3FloS2suS2suS2suS2su4SUhiS2su4SUloS2su4SUloS2su4SUhiS2suS2suS2suS2su4SUloS2suS2su4SUhiS2suS2su4SUhiS2suS2suS2suS2fd2FDS2fd2FDS2su4SUloS2wp4WPhiS2suS2suS2suS2su4SUloS2suS2su4SUloS2suS2su4SUlo4SUhiS2su4SUhiS2su4SUloS2suS2su4SUhiS2su4SUhiS2suS2su4SUlo". (* [comment removed for export] *)
Lemma sw_enter_eq : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write_run1 ()) "Pregs,(14.&5.(6.&40.))Pmem,P,(6.&40.)(15.(6.&8.))Prom,P,(6.&40.)(15.(6.&8.))Psu,$0.Pf,$0.Pwp,$0.Pfd,$0.Ps,(6.&40.)Pl,(6.&40.)Pbufp,(6.&40.)Pbufsz,(6.&40.)Pcan,(6.&40.)Pret,(6.&40.)P,(5.(6.&40.)(16.R=.(17.&5.+2.$18.))(8.&40.R:.))P,(5.(6.&40.)(16.R>.(17.&5.+:.$18.))(8.&40.R:.))P,(5.(6.&40.)(16.R?.(17.&5.+;.$18.))R8.)P,(5.(6.&40.)(16.R10.(17.&5.+<.$18.))R8.)P,(5.(6.&40.)(16.R11.(17.&5.+1.$18.))R5.)P,(2.(;.+100000000.+70.)R?.)P,(2.R10.+800000000000.)P,(5.$19.(1:.$1;.R13.(8.&40.(9.R11.+70.))#70.)$1<.)P,(2.+4<000.R11.)P,(2.(;.R12.+>8.)+7=330.)P,(1=.R16.R13.R12.R12.R11.R>.R=.)P,(1>.R17.R=.)P,(1.(3.=R13.)(3.R13.+80000000.))P,(1.(2.=R15.)(3.R15.(4.+2.+40.)))P,(3.(<.&40.R13.)+80000000.)(1?.(14.&5.(6.&40.))Lregs',(14.&5.(6.&40.))(1.(20.$1;.(21.$22.R1=.(17.&40.+41:34.$18.)R1<.R1;.)(21.$22.R1.(17.&40.+41:;<.$18.)(23.R1<.R1:.R11.(16.R1=.(17.&5.+8.$18.))(16.R1=.(17.&5.+9.$18.))(16.R1=.(17.&5.+12.$18.))(16.R1=.(17.&5.+13.$18.))(16.R1=.(17.&5.+14.$18.))(16.R1=.(17.&5.+15.$18.))(16.R1=.(17.&5.+16.$18.))R12.R18.=R16.R15.)R1;.))(1.(5.(6.&40.)(16.R1.(17.&5.+11.$18.))(8.&40.+42.))(1.(5.(6.&40.)(16.R1.(17.&5.+:.$18.))(8.&40.R17.))(1.(5.(6.&40.)(16.R1.(17.&5.+;.$18.))(8.&40.(9.R1:.+58.)))(1.(5.(6.&40.)(16.R1.(17.&5.+<.$18.))(8.&40.+1.))(1.(5.(6.&40.)(16.R1.(17.&5.+2.$18.))(8.&40.(9.R1:.+70.)))(1.(5.(6.&40.)(16.R1.(17.&5.+8.$18.))R15.)(1.(5.(6.&40.)(16.R1.(17.&5.+9.$18.))(8.&40.R19.))(1.(5.(6.&40.)(16.R1.(17.&5.+12.$18.))(8.&40.+1.))(1.(5.(6.&40.)(16.R1.(17.&5.+13.$18.))(8.&40.(9.R1:.+58.)))(1.(5.(6.&40.)(16.R1.(17.&5.+15.$18.))(8.&40.+7=330.))(1.(5.(6.&40.)(16.R1.(17.&5.+16.$18.))R15.)(1.(5.(6.&40.)(16.R1.(17.&5.+3.$18.))(16.R1=.(17.&5.+3.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+4.$18.))(16.R1=.(17.&5.+4.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+17.$18.))(16.R1=.(17.&5.+17.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+18.$18.))(16.R1=.(17.&5.+18.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+19.$18.))(16.R1=.(17.&5.+19.$18.)))(1.(5.(6.&40.)(16.R1.(17.&5.+1:.$18.))(16.R1=.(17.&5.+1:.$18.)))(5.(6.&40.)(16.R1.(17.&5.+1;.$18.))(16.R1=.(17.&5.+1;.$18.))))))))))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros regs mem rom su f wp fd s l bufp bufsz can ret
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
         FD WPhi SMALL.
  pose proof (u64_range l) as Hl.
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  unfold mem_sw1. eexists. split.
  - stepn F_3e2e8 D_3e2e8. rewrite Hsp. sp_renorm.
    stepST F_3e2ec D_3e2ec (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
    stepST F_3e2f0 D_3e2f0 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
    stepST F_3e2f4 D_3e2f4 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
    stepST F_3e2f8 D_3e2f8 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
    stepST F_3e2fc D_3e2fc (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
    stepST F_3e300 D_3e300 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
    stepST F_3e304 D_3e304 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
    stepST F_3e308 D_3e308 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
    stepn F_3e30c D_3e30c. rewrite Ha2.
    stepn F_3e310 D_3e310. rewrite Ha0.
    stepn F_3e314 D_3e314.
    stepLD8 F_3e318 D_3e318 (Z_to_bv 64 0x7d330).
    stepLD8 F_3e31c D_3e31c can.
    stepST F_3e320 D_3e320 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
    stepLD8 F_3e324 D_3e324 (Z_to_bv 64 wp).
    stepLD8 F_3e328 D_3e328 (Z_to_bv 64 wp).
    stepn F_3e32c D_3e32c. rewrite (v_sub_Z wp wp) by lia. rewrite Z.sub_diag.
    stepn F_3e330 D_3e330.
    stepST F_3e334 D_3e334 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wp) ltac:(sok_frame SOK).
    stepST F_3e338 D_3e338 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 0) ltac:(sok_frame SOK).
    stepST F_3e33c D_3e33c (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
    stepST F_3e340 D_3e340 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
    stepn F_3e344 D_3e344.
    stepn F_3e348 D_3e348. rewrite sltu0_xor_eq.
    (* [comment removed for export] *)
    stepb_tk F_3e34c D_3e34c ltac:(apply c_eq_refl).
    stepn F_3e358 D_3e358.
    replace (v_addi (Z_to_bv 64 (su - 112)) 24) with (Z_to_bv 64 (su - 88))
      by (unfold v_addi; u_norm; f_equal; lia).
    stepLD F_3e35c D_3e35c (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small fd) by lia.
    stepn F_3e360 D_3e360.
    stepn F_3e364 D_3e364.
    stepn F_3e368 D_3e368.
    stepn F_3e36c D_3e36c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
