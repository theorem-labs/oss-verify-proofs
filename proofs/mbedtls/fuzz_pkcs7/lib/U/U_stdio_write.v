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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ShapeX BBFrame MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_defs U_stdio_write_run1 U_stdio_write_run2 U_code_3e000_3f000.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_stdio_write () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.at_"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BB.StoreOk.mem_grows"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "stdpp.bitvector.definitions.Z_to_bv"; "Loop.LM"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_write_run2.mem_sw2"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Loop.RI"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Peano.lt"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.app"; "LM"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_write_run1.mem_sw1"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.sw_post"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.sw_file"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.ssp_cells"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.ret_ok"].


(* [comment removed for export] *)
Lemma rz_emit_nil : forall c K, realizes RSEGS c K -> realizes RSEGS c (t_emit [] K).
Proof.
  intros c K H. eapply rz_conseq; [exact H|].
  apply t_eq_sym. apply t_emit_nil_eq. exact (realizes_nonempty _ _ _ H).
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L66915493008.500000;S1A1k2l12Hk". (* [comment removed for export] *)
Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
  (k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
  (length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
  intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L14744466972.6L63808858833.600000<00FS1b1k3Hle2NES1b1k2Hk1H". (* [comment removed for export] *)
Lemma u_at_le : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "Pb,(0.&40.)Pk,$1.P,(2.=R1.)P,(2.(3.(4.&40.R3.)R2.)(5.+2.+40.))(6.(7.$1.(4.&40.(8.R4.R3.))(3.(4.&40.R4.)R3.))(9.(7.$1.(4.&40.(8.R4.R3.))=)(7.$1.(3.(4.&40.R4.)R3.)(5.+2.+40.))))")
(* [comment removed for export] *).
Proof.
  intros b k Hk Hle. unfold at_. pose proof (u64_range b).
  destruct (Z.eq_dec (bv_unsigned b + k) (2 ^ 64)) as [E|NE].
  - right. split; [|exact E]. rewrite E. vm_compute. reflexivity.
  - left. u_norm. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Loop.
  Variables (su f fd : Z) (l bufp bufsz can ret : word).
  Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
  Variable mem1 : word -> option byte.
  Variable model : Model.
  Variable K : TSet.

  Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
  Hypothesis SUhi : (su <= 0x800000000000)%Z.
  Hypothesis Flo : (0x4c000 <= f)%Z.
  Hypothesis Fhi : (f + 232 <= 0x7d330)%Z.
  Hypothesis FD : (0 < fd < 2147483648)%Z.
  Hypothesis Hfd : fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hret : ret_ok ret.
  Hypothesis HKnil : K [].
  Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
  Hypothesis M8  : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
  Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
  Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
  Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
  Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
  Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
  Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
  Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
  Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x7d330) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
  Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
  Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).

  (* [comment removed for export] *)
  Definition LM (m : word -> option byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "(9.Px,(0.&40.)P,(:.(9.(2.(;.Vsu,+68.)(4.&40.R1.))(<.(4.&40.R1.)(;.Vsu,+48.))))(7.(=.(0.&8.))A1.O1.R2.A1.Vmem1,R2.)(>.Vmem1,O1.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Hypothesis HK : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "Pregs',(?.&5.(0.&40.))Pm,P,(0.&40.)(=.(0.&8.))P,(7.(0.&40.)(10.R2.(11.&5.+:.$12.))Vl,)P,(7.(0.&40.)(10.R3.(11.&5.+2.$12.))(13.&40.Vsu,))P,(7.(0.&40.)(10.R4.(11.&5.+1.$12.))Vret,)P,(7.(0.&40.)(10.R5.(11.&5.+8.$12.))Ve8,)P,(7.(0.&40.)(10.R6.(11.&5.+9.$12.))Ve9,)P,(7.(0.&40.)(10.R7.(11.&5.+12.$12.))Ve18,)P,(7.(0.&40.)(10.R8.(11.&5.+13.$12.))Ve19,)P,(7.(0.&40.)(10.R9.(11.&5.+14.$12.))Ve20,)P,(7.(0.&40.)(10.R:.(11.&5.+15.$12.))Ve21,)P,(7.(0.&40.)(10.R;.(11.&5.+16.$12.))Ve22,)P,(7.(0.&40.)(10.R<.(11.&5.+17.$12.))Vg23,)P,(7.(0.&40.)(10.R=.(11.&5.+18.$12.))Vg24,)P,(7.(0.&40.)(10.R>.(11.&5.+19.$12.))Vg25,)P,(7.(0.&40.)(10.R?.(11.&5.+1:.$12.))Vg26,)P,(7.(0.&40.)(10.R10.(11.&5.+1;.$12.))Vg27,)P,(7.(0.&40.)(10.R11.(11.&5.+3.$12.))Vg3,)P,(7.(0.&40.)(10.R12.(11.&5.+4.$12.))Vg4,)P,(14.R12.)(15.$16.(17.(18.$19.R14.Vret,(1:.R13.Vf,Vbufp,Vbufsz,)(1;.$16.))Vmodel,)VK,)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition RI (regs : bvmap 5 word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "(9.(7.(0.&40.)(10.O1.(11.&5.+2.$12.))(13.&40.(;.Vsu,+70.)))(9.(7.(0.&40.)(10.O1.(11.&5.+8.$12.))Vl,)(9.(7.(0.&40.)(10.O1.(11.&5.+9.$12.))(13.&40.Vf,))(9.(7.(0.&40.)(10.O1.(11.&5.+15.$12.))(13.&40.+7=330.))(9.(7.(0.&40.)(10.O1.(11.&5.+3.$12.))Vg3,)(9.(7.(0.&40.)(10.O1.(11.&5.+4.$12.))Vg4,)(9.(7.(0.&40.)(10.O1.(11.&5.+17.$12.))Vg23,)(9.(7.(0.&40.)(10.O1.(11.&5.+18.$12.))Vg24,)(9.(7.(0.&40.)(10.O1.(11.&5.+19.$12.))Vg25,)(9.(7.(0.&40.)(10.O1.(11.&5.+1:.$12.))Vg26,)(7.(0.&40.)(10.O1.(11.&5.+1;.$12.))Vg27,)))))))))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma RI_but : forall regs regs', RI regs -> sw_regs_but regs regs' -> RI regs'.
  Proof.
    (intros regs regs' dd_H; ddestruct dd_H as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27); intros dd_H; ddestruct dd_H as (P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27)).
    unfold RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. repeat split; assumption.
  Qed.

  #[using="Type"] Lemma LM_refl : LM mem1.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L34301897727.6100000?S2su1a1n1D1x2Hx". (* [comment removed for export] *)
  #[using="Type"] Lemma LM_rdn : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "Pm,P,(0.&40.)(=.(0.&8.))Pa,(0.&40.)Pn,$1<.Pbs,(1=.(0.&8.))P,(14.R4.)P,(7.(=.(1=.(0.&8.)))(1>.$16.Vmem1,R4.R3.)(1?.(1=.(0.&8.))R2.))P,(2.(3.(4.&40.R5.)(20.R4.))(5.+2.+40.))P,(6.(2.(3.(4.&40.R6.)(20.R5.))(;.Vsu,+68.))(2.(;.Vsu,+48.)(4.&40.R6.)))(7.(=.(1=.(0.&8.)))(1>.$16.R8.R7.R6.)(1?.(1=.(0.&8.))R5.))")
(* [comment removed for export] *).
  Proof.
    intros m a n bs [E G] H Hnw D.
    rewrite (rdn_ext RSEGS n m mem1 a Hnw); [exact H|].
    intros x Hx. apply E. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma LM_store_ok : forall m (a : word) n,
    LM m -> store_ok RSEGS mem1 a n = true -> store_ok RSEGS m a n = true.
  Proof. intros m a n [E G] H. eapply store_ok_mono; [exact G | exact H]. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L11319347736.59L20950175652.59L26983618961.59L62729228902.5900000?00N00]010S2su4SUhi1a3HhiS2su4SUhi1a3HhiS2su4SUlo1a3HloS2su1a3Hlo3Hhi1x2Hx". (* [comment removed for export] *)
  #[using="SUlo SUhi"] Lemma LM_wbytes8 : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "Pm,P,(0.&40.)(=.(0.&8.))Pa,$1.Pv,(0.&40.)P,(14.R3.)P,(2.(;.Vsu,+68.)R3.)P,(2.(3.R4.+8.)(;.Vsu,+48.))(14.(21.R6.(13.&40.R5.)(22.#8.R4.)))")
(* [comment removed for export] *).
  Proof.
    intros m a v [E G] Hlo Hhi. split.
    - intros x Hx. rewrite wbytes_outside.
      + apply E, Hx.
      + unfold in_rng. rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
      + rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - eapply mem_grows_trans; [exact G | apply wbytes_grows].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00`0?L11035108906.64L12046594218.64L13497491428.64L14381951466.64L1450776433.64 L14786730236.64L15229008282.64L16409309519.64L18686485407.64L19498164209.64L19623417626.64L20079803434.64L23557463466.64L23604957098.64L25523437937.64L25636384892.64L27110363418.64L27275840207.64L28644939065.64L30832478159.64L31534445809.64L31620860714.64L32767542045.64L33796332957.64L37222482698.64L37304660506.64L37560247921.64L38142927439.64L43570694641.64L44145328810.64L44491720730.64L48886032282.64L48990993359.64L5018065050.64 L52549200079.64L5561227727.64 L55624281841.64L55686926762.64L59166191914.64L59857523535.64L61634859121.64L61905521265.64L63414157391.64L6388919066.64 L64142501361.64L66567242394.64L68101818041.64L7488482404.64 00000900B00I00J00S00b00k00o01801A01J01S01\01e01n02=02F02J02Q02U02^02g02n03503603?03H03L03U03^03g04004404=04A04E04N04W04`04d04m04n05205;05D05M05T05[S2su4SUhiS2su4SUhiS1f3FloSS2su4SUloS2su1f4SUlo3FhiS2su4SUhiS2suS2su4SUloS2su4SUloS2su4SUhiS2su4SUhiS2su4SUhiS2su4SUhiS2su4SUloS2su1f4SUlo3FhiS2su4SUhiS2suS1f3FhiS2suS2su4SUloS2su4SUhiS1f3FhiS1f3FhiSS2su4SUhiS2su4SUloS2suS2su4SUloS2su4SUhiS2su4SUhiS2su4SUhiS2suS2su4SUhiS2suS2suS2su4SUloS2su4SUhiS2su4SUhiS2suS2su4SUloSS2suS2su4SUhiS2su4SUloS2su4SUhiS1f3FhiS1f3Flo". (* [comment removed for export] *)
  #[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK"] Lemma finish : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "Pregs,(?.&5.(0.&40.))Pm,P,(0.&40.)(=.(0.&8.))P,(23.R2.)P,(14.R2.)(15.$16.(17.(18.$19.R4.(11.&40.+41:<8.$12.)R3.(1;.$16.))Vmodel,)VK,)")
(* [comment removed for export] *).
  Proof.
    intros regs m RIr LMm.
    ddestruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    ddestruct (sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)
      as (regs2 & RUN & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27);
      try assumption.
    all: try (eapply LM_rdn; [exact LMm | eassumption | u_norm; lia | u_norm; lia]).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
    apply HK; try assumption.
    - rewrite Q23; exact R23.
    - rewrite Q24; exact R24.
    - rewrite Q25; exact R25.
    - rewrite Q26; exact R26.
    - rewrite Q27; exact R27.
    - rewrite Q3; exact R3.
    - rewrite Q4; exact R4.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK"] Lemma finish_nil : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "Pregs,(?.&5.(0.&40.))Pm,P,(0.&40.)(=.(0.&8.))P,(23.R2.)P,(14.R2.)(15.$16.(17.(18.$19.R4.(11.&40.+41:<8.$12.)R3.(1;.$16.))Vmodel,)(24.(25.$26.)VK,))")
(* [comment removed for export] *).
  Proof. intros. apply rz_emit_nil. apply finish; assumption. Qed.


  (* [comment removed for export] *)
  #[using="Type"] Lemma pc_3e3fc : v_addi (0x41b44 : word) 4 = (0x41b48 : word).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0140@L13484894876.107L13487025709.96 L13721927173.84 L14595720312.97 L14863433994.108L14982117813.84 L15128961468.107L15128961468.108L1868536578.107 L1870602163.96  L2131570563.108 L23057627566.106L23059758367.95 L23059758367.96 L23950079757.97 L24001246580.101L24001331040.101L24893549885.94 L25209069666.97 L25328974635.96 L28144053903.108L29402961269.96 L29405024708.108L32377906728.96 L32379581177.84 L32379986585.94 L35312854505.97 L36982274404.97 L36984339925.108L37002742007.107L37004872774.96 L37004872774.97 L37033469903.84 L38132829117.94 L38481817782.101L39716597944.94 L40699307608.84 L40930435204.108L41810202512.84 L42366415918.95 L43389386584.97 L45729570616.94 L45729943384.84 L46087295189.97 L4878356317.84  L49366094276.84 L49450551896.108L49648375619.96 L50223214883.101L50926684401.84 L57118366167.97 L57120496998.108L58141766505.84 L59310627411.70 L61052735102.84 L64660844871.108L64767252683.108L64912887836.97 L6565153332.84  L66267405510.96 L66269534327.107L7457782812.107 L7459846317.96  L7459846317.97  L8927474081.97  L8929245077.101 L932467074.107  L934597939.96   00000P00g01601I01n01o02G02_03?03V04404Y05505_05n06M06i07;07P07d08@08O08g09909K09]09l0:A0:_0;?0;V0;m0<<0<N0<i0=;0=N0=l0>A0>B0>U0>g0?90?H0?Z0?[0@30@L0@g0AD0AX0B50BJ0BW0Bf0CA0C\0D30DH0D_0E?0E_0F60FM0F`0G<0G\0H3S2su4SUlo1n1k2bs3LEN2Kb2k'2K12K2S2su4SUlo1n1k2bs3LEN2KbS1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb3M30S2su1n1k1b2bs3LEN2Kb4DISJ2k'2K12K22NEFS1n1k2bs3LEN2Kb2k'2K12K2S1n1k2bs3LEN2Kb2k'2K12K2S2su4SUhi1n1k2bs3LEN2Kb2k'2K12K2S2su4SUhi1n1k2bs3LEN2KbS1n1k1b2bs3LEN2Kb3TSB2k'2K12K2S2su4SUlo4SUhi1n1k2bs3LEN2Kb2k'2K12K2S2su4SUlo4SUhi1n1k2bs3LEN2KbS2su4SUlo4SUhi1n1k1b2bs3LEN2Kb4DISJ3TSB2HbS1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb3M302k'2K12K22EQS1n1k2bs3LEN2Kb3M302k'2K12K2S2su1n1k2bs3LEN2KbS1n1k1b2bs3LEN2Kb3TSBS1n1k1b2bs3LEN2Kb2NWS1n1k2bs3LEN2Kb3M302k'2K12K2S1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb2k'2K12K2S2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2KbS1n1k1b2bs3LEN2Kb3TSBS1n1k1b2bs3LEN2Kb3TSB2k'2K12K2S2su4SUhi1n1k2bs3LEN2Kb2k'2K12K2S2su4SUhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbS1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb2k'2K12K22EQS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb3M30S1n1k1b2bs3LEN2Kb3TSB2k'2K12K2S1f3Fhi1n1k2bs3LEN2KbFS1n1k2bs3LEN2Kb3M30S2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbFS1n1k2bs3LEN2Kb2k'2K12K2S2su1n1k1b2bs3LEN2Kb4DISJS1n1k2bs3LEN2Kb2k'2K12K22NES2su1f4SUlo3Fhi1n1k2bs3LEN2KbS1n1k1b2bs3LEN2Kb2HbS1n1k1b2bs3LEN2Kb2Hb2k'2K12K2S1f3Flo1n1k2bs3LEN2KbS1k2bs3LEN2KbS1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb2k'2K12K22NES1n1k2bs3LEN2Kb2k'2K12K22EQS2su4SUhi1n1k2bs3LEN2KbS1f3Fhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2Kb2k'2K12K2S2su4SUlo1n1k2bs3LEN2Kb2k'2K12K2S2su4SUlo1n1k2bs3LEN2KbS2su4SUlo1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb3M30S1n1k2bs3LEN2Kb3M302k'2K12K2S2su4SUhi1n1k2bs3LEN2Kb2k'2K12K2S2su4SUhi1n1k2bs3LEN2Kb". (* [comment removed for export] *)
  #[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK"] Lemma loop1 : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "Pn,$1<.Pregs,(?.&5.(0.&40.))Pm,P,(0.&40.)(=.(0.&8.))Pk,$1<.Pb,(0.&40.)Pbs,(1=.(0.&8.))P,(27.(28.(0.&8.)R1.)R6.)P,(23.R6.)P,(14.R6.)P,(7.(0.&40.)(10.R8.(11.&5.+:.$12.))(13.&40.(20.R6.)))P,(7.(0.&40.)(10.R9.(11.&5.+16.$12.))(13.&40.(20.(28.(0.&8.)R5.))))P,(7.(0.&40.)(10.R:.(11.&5.+12.$12.))(13.&40.+1.))P,(7.(0.&40.)(10.R;.(11.&5.+13.$12.))(13.&40.(;.Vsu,+58.)))P,(9.(27.#1.R:.)(29.R:.(28.(0.&8.)R8.)))P,(7.(=.(1=.(0.&8.)))(1>.$16.R<.(13.&40.(;.Vsu,+58.))#8.)(1?.(1=.(0.&8.))(22.#8.R:.)))P,(7.(=.(1=.(0.&8.)))(1>.$16.R=.(13.&40.(;.Vsu,+50.))#8.)(1?.(1=.(0.&8.))(22.#8.(13.&40.(20.(28.(0.&8.)R:.))))))P,(7.(=.(1=.(0.&8.)))(1>.$16.Vmem1,R<.(28.(0.&8.)R;.))(1?.(1=.(0.&8.))R;.))P,(6.(2.(3.(4.&40.R=.)(20.(28.(0.&8.)R<.)))(;.Vsu,+70.))(2.Vsu,(4.&40.R=.)))P,(2.(3.(4.&40.R>.)(20.(28.(0.&8.)R=.)))(5.+2.+40.))P,(2.(3.(4.&40.R?.)(20.(28.(0.&8.)R>.)))+800000000000.)P,(2.(20.(28.(0.&8.)R?.))(5.+2.+1>.))(15.$16.(17.(18.$19.R14.(11.&40.+41;54.$12.)R13.(1;.$16.))Vmodel,)(24.(2:.(0.&8.)$26.(2;.(13.&40.Vfd,))(2<.(0.&8.)R12.R10.))VK,))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros regs m k b bs LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW TSB M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    ddestruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b) as Hb.
    (* [comment removed for export] *)
    ddestruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
                (Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
      as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
    { eapply LM_store_ok; [exact LMm | exact SOK1]. }
    { replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
    { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
    replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
    set (m' := wbytes (wbytes m _ _) _ _).
    assert (LMm' : LM m').
    { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
    assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
    (* [comment removed for export] *)
    eapply (rz_writev1_wall RSEGS regs1 (0x41b44 : word) m' model W_3e3f8 fd
              (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
              (Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
      [ exact F_3e3f8 | exact E_3e3f8 | exact Hh | exact Hlazy | exact Hfd | exact FD
      | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
    - subst m'. rdn_solve.
    - subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
    - rewrite word_to_nat_Z by lia.
      replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
      subst m'. repeat rdn_peel1.
      change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
      apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
      eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
    - u_norm. unfold TASK_SIZE. lia.
    - u_norm. unfold TASK_SIZE. lia.
    - u_norm. lia.
    - u_norm. lia.
    - (* [comment removed for export] *)
      intros k' K1 K2. rewrite pc_3e3fc. rewrite length_skipn in K2.
      destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
      + (* [comment removed for export] *)
        ddestruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite Q22. f_equal. lia. }
        { lia. }
        eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
        apply finish_nil; [| exact LMm'].
        eapply RI_but; [exact RI1|].
        revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      + (* [comment removed for export] *)
        ddestruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                    (Z.of_nat (length bs) - Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact Q22. }
        { lia. }
        { lia. }
        { lia. }
        eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (IH regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs)).
        * rewrite length_skipn. lia.
        * eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * exact LMm'.
        * exact P10.
        * rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
        * rewrite P18. gres. exact Q18.
        * rewrite P19. gres. exact Q20.
        * rewrite length_skipn. lia.
        * subst m'. unfold at_. rdn_solve.
        * subst m'. rewrite length_skipn.
          replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
        * rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * rewrite length_skipn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02D0@L13280524840.106L13282440591.94 L13282606745.104L13368944527.94 L13369028124.94 L13369109657.104L13371222056.106L13484894876.117L13487025709.106L14595720312.107L14863433994.118L14982179664.94 L14982259395.94 L15128961468.117L15183436003.118L15185501266.106L15482316339.106L15484445314.117L15688928829.104L15688928829.106L15882612607.107L15937122122.118L16073330249.107L16400099507.106L16402164738.117L16771550251.94 L18126960131.118L1868536578.117 L1870602163.106 L21308939195.119L2131570563.118 L2148049626.118 L2305417016.94  L2305496747.94  L23057202721.105L23057202721.107L23057627566.115L23059758367.104L23059758367.106L24001246580.111L24001331040.111L24599660093.104L24613036018.94 L24613213793.94 L24893549885.104L25209069666.107L26793766726.106L26793766726.107L26795895799.117L27405481149.104L28463687622.106L28465816439.117L29670166300.119L30912932890.107L32377906728.106L32711568644.118L34324482128.94 L35312854505.107L36088903494.104L36088903494.106L36088903494.107L36090967031.118L36493952086.94 L37002742007.117L37004872774.106L37004872774.107L37033407786.94 L38132829117.104L38208764674.106L39300302624.107L39300399279.118L39716597944.104L39749132041.107L40070195629.106L40070195629.107L40072260892.117L40469550215.94 L40930435204.118L41810140533.94 L41810318566.94 L42366415918.105L43717670067.107L44497811097.107L4456445451.118 L4458508986.107 L44682844822.118L44684975655.107L45614927000.118L45729570616.104L46078943021.106L46081006492.117L46947524142.118L46949653151.107L47812675782.117L49158700695.118L49365977778.94 L49366156065.94 L49837473654.107L49839782984.108L50223214883.111L50926474119.94 L50926623252.94 L51498914432.118L51757206968.104L53937290678.107L54109462973.104L54109462973.106L54568067256.94 L56530858809.108L56890554374.107L57005878884.104L57766165181.94 L57766277934.94 L57766508600.104L58141827468.94 L58141911071.94 L58286516448.94 L58704251412.107L59310627411.78 L59847102226.94 L60194671094.104L61657668143.107L63456137687.107L6464229729.107 L64912887836.107L6565222609.94  L6565368130.94  L65683937934.94 L66267405510.106L66269534327.117L67137529884.107L67838202498.107L6783889049.104 L6784050575.94  L6785935912.106 L68210972022.104L68358160965.118L68426955787.111L7194169106.107 L7200641517.119 L7457782812.117 L7459846317.106 L7459846317.107 L8269512862.118 L8927474081.107 L8929245077.111 L932467074.117  L934597939.106  00000J00d01>01X02202L02f03N03m04H05705805905Y06906P06o07W07X08;08V09909T0:30:[0;50;U0<=0<\0=W0>>0>d0??0?Z0?[0@S0AC0Aj0B_0CI0D00DJ0Da0E80ER0F:0FY0G80G`0H:0HY0IA0J<0JS0Jm0KQ0Kl0LC0La0MB0M`0NG0Nb0OJ0Oi0PH0P_0Q90Q_0R60RV0S00SN0Sm0TL0U40UK0V20VO0Vl0Vm0WS0X10XX0Y60Y]0Z;0Z[0[50[T0\<0\`0];0][0^;0^<0^=0^T0^n0_T0`90`^0aA0a[0b20b30bV0c00cJ0ca0d80dR0dl0eF0ec0f@0fW0fn0g@0gW0h60hT0ho0iF0ie0jB0j_0j`0k?0kg0lF0l]0m70mQ0mk0nJ0nj0oP0ok10g11O11n12M12m13K14214Z159S2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES2su4SUlo1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S2su4SUlo1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb3M302LES2su1n1k3bs02b13bs13LEN2Kb5DISJ12GT2k'2K12K22NEFFS1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LE2k'2K12K2FS2su1n1k3bs02b13bs13LEN2Kb5DISJ12LES1n1k3bs03bs13LEN2Kb3M302GTS1n1k3bs03bs13LEN2Kb2GT2k'2K12K22EQS1n1k3bs03bs13LEN2Kb3M302LES2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k2b03bs02b13bs13LEN2Kb3TS03TS12LE2k'2K12K22NE1HS1n1k3bs02b13bs13LEN2Kb3TS12GT2k'2K12K2S1n1k3bs03bs13LEN2Kb2LE2k'2K12K22NE2GTS1n1k3bs03bs13LEN2Kb3M302GTS1n1k3bs03bs13LEN2Kb3M302LEFS2su4SUlo4SUhi1n1k2b03bs03bs13LEN2Kb5DISJ03TS03Hb02LE2NKS2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2LE2k'2K12K22GTS2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2LE2GTS2su4SUlo4SUhi1n1k3bs02b13bs13LEN2Kb5DISJ13TS13Hb12GTS1n1k3bs03bs13LEN2Kb3M302LE2k'2K12K22EQ2GTS1n1k3bs03bs13LEN2Kb3M302LE2k'2K12K22GTS2su1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS1n1k2b03bs03bs13LEN2Kb3TS02LE2b13TS12GTS2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su4SUhi1n1k2b03bs02b13bs13LEN2Kb3TS03TS12LE2k'2K12K22NE1HS1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb3M302GT2k'2K12K2S1n1k3bs03bs13LEN2Kb3M302GTS1n1k3bs03bs13LEN2Kb2LES1n1k3bs02b13bs13LEN2Kb3NW12LES1n1k3bs02b13bs13LEN2Kb3NW12LE2GTS1n1k3bs02b13bs13LEN2Kb3TS12GTS1n1k3bs02b13bs13LEN2Kb3TS12GT2k'2K12K2S1n1k3bs03bs13LEN2Kb3M302LES2su4SUhi1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs02b13bs13LEN2Kb5DISJ12LE2GTS1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su1n1k3bs03bs13LEN2Kb2GTS1n1k2b03bs03bs13LEN2Kb3Hb02LES2su4SUlo1n1k3bs03bs13LEN2Kb2LES2su4SUlo1n1k3bs03bs13LEN2Kb2LES2su4SUlo1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S1n1k3bs03bs13LEN2Kb2GTS1n1k3bs02b13bs13LEN2Kb3TS12GT2k'2K12K2S1f3Fhi1n1k3bs03bs13LEN2Kb2LES1f3Fhi1n1k3bs03bs13LEN2Kb2GTFS2su1n1k2b03bs03bs13LEN2Kb5DISJ02LE2NKS1n1k3bs02b13bs13LEN2Kb3TS12LES1n1k2b03bs03bs13LEN2Kb3TS02LE2k'2K12K2S1n1k2b03bs03bs13LEN2Kb3TS02LES1n1k3bs02b13bs13LEN2Kb3Hb12GT2k'2K12K2S1n1k3bs02b13bs13LEN2Kb3Hb12GTS1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su1n1k3bs03bs13LEN2Kb2GTS2su4SUlo1n1k3bs03bs13LEN2Kb2LES2su4SUlo1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S1n1k3bs03bs13LEN2Kb3M302LE2k'2K12K2S1n1k3bs03bs13LEN2Kb3M302GTS1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S1n1k3bs03bs13LEN2Kb2LE2k'2K12K2FFS1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2LE2EKS1n1k3bs03bs13LEN2Kb2LE2k'2K12K22NE2GTS2su1f4SUlo3Fhi1n1k3bs03bs13LEN2Kb2GTS2su1f4SUlo3Fhi1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2LE2k'2K12K22EQS2su1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2LEFS2su1n1k3bs02b13bs13LEN2Kb5DISJ12LES2su1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2LE2EKS1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LES1f3Flo1n1k3bs03bs13LEN2Kb2LES1f3Flo1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2GTS1k3bs03bs13LEN2KbS1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2LES1n1k2b03bs03bs13LEN2Kb3NW02LES1n1k3bs03bs13LEN2Kb3M302LES1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2GTS1f3Fhi1n1k3bs03bs13LEN2Kb2LES1f3Fhi1n1k3bs03bs13LEN2Kb2GTFS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S1n1k3bs03bs13LEN2Kb2LE2k'2K12K22EQ2GTS1n1k3bs03bs13LEN2Kb3M302LES2su1n1k2b03bs02b13bs13LEN2Kb5DISJ03TS03Hb12LE2k'2K12K22NE1HS2su4SUlo1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S2su4SUlo1n1k3bs03bs13LEN2Kb2GTS2su4SUlo1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S1n1k3bs03bs13LEN2Kb3M302LE2GTS1n1k3bs03bs13LEN2Kb3M302LE2k'2K12K22GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2GT". (* [comment removed for export] *)
  #[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK"] Lemma loop2 : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "Pn,$1<.Pregs,(?.&5.(0.&40.))Pm,P,(0.&40.)(=.(0.&8.))Pk,$1<.Pb0,(0.&40.)Pbs0,(1=.(0.&8.))Pb1,(0.&40.)Pbs1,(1=.(0.&8.))P,(27.(2=.(28.(0.&8.)R3.)(28.(0.&8.)R1.))R8.)P,(23.R8.)P,(14.R8.)P,(7.(0.&40.)(10.R:.(11.&5.+:.$12.))(13.&40.(20.R8.)))P,(7.(0.&40.)(10.R;.(11.&5.+16.$12.))(13.&40.(3.(20.(28.(0.&8.)R7.))(20.(28.(0.&8.)R5.)))))P,(7.(0.&40.)(10.R<.(11.&5.+12.$12.))(13.&40.+2.))P,(7.(0.&40.)(10.R=.(11.&5.+13.$12.))(13.&40.(;.Vsu,+68.)))P,(9.(27.#1.R<.)(29.R<.(2=.(28.(0.&8.)R:.)(28.(0.&8.)R8.))))P,(7.(=.(1=.(0.&8.)))(1>.$16.R>.(13.&40.(;.Vsu,+68.))#8.)(1?.(1=.(0.&8.))(22.#8.R<.)))P,(7.(=.(1=.(0.&8.)))(1>.$16.R?.(13.&40.(;.Vsu,+60.))#8.)(1?.(1=.(0.&8.))(22.#8.(13.&40.(20.(28.(0.&8.)R<.))))))P,(7.(=.(1=.(0.&8.)))(1>.$16.R10.(13.&40.(;.Vsu,+58.))#8.)(1?.(1=.(0.&8.))(22.#8.R<.)))P,(7.(=.(1=.(0.&8.)))(1>.$16.R11.(13.&40.(;.Vsu,+50.))#8.)(1?.(1=.(0.&8.))(22.#8.(13.&40.(20.(28.(0.&8.)R<.))))))P,(7.(=.(1=.(0.&8.)))(1>.$16.Vmem1,R10.(28.(0.&8.)R?.))(1?.(1=.(0.&8.))R?.))P,(7.(=.(1=.(0.&8.)))(1>.$16.Vmem1,R?.(28.(0.&8.)R>.))(1?.(1=.(0.&8.))R>.))P,(6.(2.(3.(4.&40.R12.)(20.(28.(0.&8.)R11.)))(;.Vsu,+70.))(2.Vsu,(4.&40.R12.)))P,(2.(3.(4.&40.R13.)(20.(28.(0.&8.)R12.)))(5.+2.+40.))P,(2.(3.(4.&40.R14.)(20.(28.(0.&8.)R13.)))+800000000000.)P,(6.(2.(3.(4.&40.R13.)(20.(28.(0.&8.)R12.)))(;.Vsu,+70.))(2.Vsu,(4.&40.R13.)))P,(2.(3.(4.&40.R14.)(20.(28.(0.&8.)R13.)))(5.+2.+40.))P,(2.(3.(4.&40.R15.)(20.(28.(0.&8.)R14.)))+800000000000.)P,(2.(3.(20.(28.(0.&8.)R17.))(20.(28.(0.&8.)R15.)))(5.+2.+1>.))(15.$16.(17.(18.$19.R1<.(11.&40.+41;54.$12.)R1;.(1;.$16.))Vmodel,)(24.(2:.(0.&8.)$26.(2;.(13.&40.Vfd,))(2<.(0.&8.)R1:.(2>.(0.&8.)R18.R16.)))VK,))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros regs m k b0 bs0 b1 bs1 LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb
      Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 TS0 DISJ1 NW1 TS1 M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    ddestruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
    destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
    - (* [comment removed for export] *)
      ddestruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_le k bs0 bs1 LE).
      eapply (rz_writev2_wall RSEGS regs1 (0x41b44 : word) m' model W_3e3f8 fd
                (Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
                (Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
                b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
        [ exact F_3e3f8 | exact E_3e3f8 | exact Hh | exact Hlazy | exact Hfd | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
      + subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
        destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
        { replace (length bs0 - k)%nat with 0%nat by lia.
          rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
        apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
      + rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
        subst m'. repeat rdn_peel1.
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + u_norm. unfold TASK_SIZE. lia.
      + u_norm. unfold TASK_SIZE. lia.
      + u_norm. unfold TASK_SIZE. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2. rewrite pc_3e3fc. rewrite length_app, length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
        * ddestruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
          apply finish_nil; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * ddestruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (IH regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
          -- subst m'. repeat rdn_peel1. exact Mb1.
          -- subst m'. repeat rdn_peel1. exact Mn1.
          -- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
          -- exact Bbs1.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- exact DISJ1.
          -- exact NW1.
          -- exact TS1.
          -- rewrite length_skipn. lia.
    - (* [comment removed for export] *)
      ddestruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs1))
                  (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
      { replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
      replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
      replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_ge k bs0 bs1) by lia.
      eapply (rz_writev1_wall RSEGS regs1 (0x41b44 : word) m' model W_3e3f8 fd
                (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
                (Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
                (skipn (k - length bs0) bs1) K);
        [ exact F_3e3f8 | exact E_3e3f8 | exact Hh | exact Hlazy | exact Hfd | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
        apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + u_norm. unfold TASK_SIZE. lia.
      + u_norm. unfold TASK_SIZE. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2. rewrite pc_3e3fc. rewrite length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
        * ddestruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
          apply finish_nil; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * ddestruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (loop1 (length bs1) regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
             rdn_solve.
          -- rewrite length_skipn.
             apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- rewrite length_skipn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac wout1 :=
  rewrite wbytes_outside;
  [ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
    | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].

Local Ltac2 Set LiaOrc.tbl := fun () => "00k0?L11033083325.30L12048755517.30L13485029350.30L1448611046.30 L15226970637.30L19496125542.30L19621252237.30L19800062943.25L19802301230.30L20081829821.30L22028604802.25L22034910579.30L23055219749.25L23555425853.30L23602795581.30L25525607142.30L26796291725.30L27108199053.30L28045517811.30L28047801090.25L28339167839.25L28341353134.30L28466216461.30L30301955978.30L31536476006.30L31623024829.30L32020620566.25L32948137878.25L34301897727.30L37003138445.30L37306689933.30L37562285542.30L40071868518.30L41052754966.25L43572859494.30L44147497277.30L44489560973.30L46080870118.30L47622961597.30L48888069133.30L5020091149.30 L5224515210.30 L55622120806.30L55684762173.30L57591360046.30L57593410271.25L59168352957.30L60192935997.30L61632695270.30L6390952077.30 L64140476006.30L65923238410.30L66269922573.30L66565085453.30L67197232445.30L68209233085.30L7457644902.30 L9992057474.25 L9998264947.30 00000900B00K00T00]00f00o01601=01F01M01T01_01h02102:02C02L02S02Z02a02h03103803A03J03Q03X03l04504>04G04P04W04`04i05205;05D05M05V05]05f05o06606=06F06O06X06a06j07107:07C07L07U07^07e07lS2su4SUhiS2su4SUhiS2su4SUloS2su4SUloS2su4SUhiS2su4SUloS2su4SUhiS1f3FhiS1f3FhiS2su4SUhiS1f3FloS1f3FloS1f3Flo3FhiS2su4SUhiS2su4SUhiS2su4SUloS2su4SUhiS2su4SUhiS1f3FloS1f3FloS1f3FhiS1f3FhiS2su4SUhiS1f3FhiS2su4SUloS2su4SUhiS1f3FhiS1f3FhiS1f1x3Hx33Hx22su3Hx1S2su4SUhiS2su4SUhiS2su4SUloS2su4SUloS1f3FhiS2su4SUloS2su4SUhiS2su4SUhiS2su4SUloS2su4SUhiS2su4SUhiS2su4SUhiS1f3FhiS2su4SUloS2su4SUhiS1f3FhiS1f3FhiS2su4SUhiS2su4SUhiS2su4SUloS2su4SUhiS2su4SUloS1f3FhiS2su4SUhiS2su4SUhiS2su4SUhiS2su4SUhiS2su4SUloS1f3FloS1f3Flo". (* [comment removed for export] *)
Lemma sw_post_of_LM : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "Pmem,P,(0.&40.)(=.(0.&8.))Pm,P,(0.&40.)(=.(0.&8.))Psu,$1.Pf,$1.Pra,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Pcan,(0.&40.)Pwb,$1.Pn,$1.Ps,(0.&40.)Pl,(0.&40.)Pbufp,(0.&40.)Pbufsz,(0.&40.)P,(2.(3.+100000000.+70.)R11.)P,(2.R12.+800000000000.)P,(2.+4<000.R12.)P,(2.(3.R13.+>8.)+7=330.)P,(2?.R15.(30.R17.R15.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R16.)(31.R18.R16.R15.R7.R6.(1:.R17.R15.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros mem m su f ra s0 s1 s2 s3 s4 s5 s6 can wb n s l bufp bufsz SUlo SUhi Flo Fhi [E G].
  constructor.
  - intros x Hx1 Hx2 Hx3. pose proof (u64_range x) as Hx.
    unfold mem_sw2. do 3 wout1.
    rewrite (E x) by lia.
    unfold mem_sw1. do 13 wout1. reflexivity.
  - unfold mem_sw2. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    eapply mem_grows_trans; [|exact G].
    unfold mem_sw1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    apply mem_grows_refl.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma pc_3e374 : v_addi (0x41abc : word) 4 = (0x41ac0 : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "03D0@L10451225604.105L10753966476.75 L10753966476.77 L11032983989.75 L11526926882.116L11901016311.116L12048920373.75 L1256872595.75  L1257161697.114 L1257161697.116 L12997348297.103L13280524840.105L13371222056.105L13485192174.77 L13487069094.71 L1448773870.77  L1450797864.66  L15043608204.75 L15043608204.77 L15227135493.77 L15229011777.62 L15482658610.68 L16075492727.107L16392907144.101L16397784372.69 L16601853929.103L16601853929.105L16898339721.116L17881014268.114L17881014268.116L18565594373.105L1870194232.71  L19253132333.116L19255261340.105L19496026222.77 L19498148524.63 L19621349509.77 L19623439297.67 L19831847103.86 L19834079253.105L20081992629.75 L2106008076.75  L2106008076.77  L21315100337.116L21348632588.75 L21348632588.77 L21526331436.116L23057138836.58 L23059235098.59 L23059235224.60 L23059235358.61 L23059235476.63 L23059235484.62 L23059235610.64 L23059235736.65 L23059235870.66 L23059236122.68 L23061332120.67 L23061340758.73 L23061341002.72 L23061342530.71 L23061839391.57 L23555326517.75 L23602696245.75 L2438423736.65  L24998566707.59 L25083312391.116L25229160586.74 L25229160586.76 L25523437482.62 L25525706478.77 L25638372620.75 L25638372620.77 L26793766726.105L26794235463.68 L26796126853.77 L27066001620.105L27108101765.77 L27110353991.63 L27232730064.103L27356147980.75 L27356147980.77 L27626075660.75 L27626075660.77 L27680656157.116L28385701599.85 L28425419721.105L28461931073.69 L28466051589.77 L2896845708.75  L2896845708.77  L29664004630.116L31534418214.65 L31536638830.77 L31623189685.75 L31643174668.107L32377906728.101L32377906728.103L3357332016.64  L33654464268.75 L33654464268.77 L34036561206.61 L34968463928.60 L35058197836.109L35484391334.114L35484391334.116L35865491350.114L3596963748.114 L3688857966.114 L3688857966.116 L37003039109.77 L37004872774.101L37004872774.103L37005194307.70 L37304634435.61 L37306527109.77 L37560228782.64 L37562120686.77 L38330114477.116L39432119625.107L40069845164.68 L40070195629.105L40072033390.77 L40753612742.114L40753612742.116L40958126430.70 L41368749068.75 L41368749068.77 L41989192787.114L42301405714.107L42301405714.109L42301585938.107L42301585938.109L43418818933.109L43573024366.77 L43585357997.59 L437925327.105  L440054142.116  L44147662133.75 L44489660293.77 L44491716045.65 L4573932432.102 L46076732074.69 L46080770798.77 L4688150159.114 L46947524142.116L47079107252.67 L47623060917.75 L47661233521.82 L479204745.116  L48015335606.66 L48369346333.114L48886045635.66 L48888166405.77 L49245793925.105L5018084677.64  L5020190469.77  L5168345137.114 L5168345137.116 L51925702685.116L52195914368.85 L53953412492.75 L53953412492.77 L54915456150.114L54915456150.116L55622021486.77 L55624290472.61 L55684664885.75 L55971983837.114L57326225612.114L58243082892.75 L58243082892.77 L59168517813.75 L60192838709.75 L60423849022.82 L61285582255.105L61632752550.60 L61632860142.77 L62119007538.63 L62618979729.116L63053070388.62 L63423745034.116L63549705722.114L6378023494.59  L6390854789.77  L64026413559.101L64140573294.77 L64142481706.67 L64561810032.114L64561810032.116L64912887836.101L64912887836.103L65505213902.116L65924622434.116L66100072588.75 L66100072588.77 L66267882829.71 L66269757701.77 L66564922629.77 L66565175629.60 L67137529884.105L67197395253.75 L67305707640.105L6785935912.105 L68209133749.75 L7203132647.116 L7457482094.77  L7459815592.70  L7459846317.101 L7459846317.103 L8929243807.109 L934489398.70   00000I00J00k01B01C01]02402P03003T04204D04V04m05D05[06206306T06k07B07Y08808908P08c09:0:00:X0;R0<00<G0<m0=K0=b0>90>P0>g0?\0?]0@40@50@V0@W0@X0A90A[0B70BS0Bo0CK0Cg0DC0D_0E;0EW0F30FO0G50G[0HA0H]0I40IK0Ib0J90Jb0Jc0Ke0L<0LS0LT0M50ML0Mc0N:0NT0Nk0OB0OT0OU0P60P70PX0PY0Q>0Qb0R90RP0RQ0S20S30SJ0Sa0T80TN0TR0T`0U70U80UY0V00VG0W30WS0X70XV0Xl0Xm0Xn0YE0YN0Ya0Z80ZO0Zf0[=0[T0[U0[k0\B0\Y0]00]10]20]N0]O0^00^10^S0_10_P0_k0`_0a60aM0af0bG0b^0c50cL0cM0cd0d;0dN0di0e@0eW0ej0fP0fg0fh0g?0gV0h80hO0hf0hg0hh0hi0iF0iG0ih0ii0ij0jA0jX0jo0k00k10k20kS0kj0lA0l[0m40mK0mb0n90nP0ng0nh0o>0oU0ol10B10Y11011111211;11N12412\12]13>13U13l14C14Z15115H15m16?16V16W16n17E17N17a18N18eS2wb2wp7pending5extra3WBPFS2su1s1l7pending5extra4LENE5DISJES2su7pending5extra4SUhiFS7pending5extra1k2K12K22EKS2su7pending5extra4SUhiS1s1l7pending5extra4LENE3TSES1s1l2x06extra'4LENE3TSE1k2K12K2S1s1l7pending5extra4LENE3TSE1k2K12K2S2wp1l2x06extra'4LENP4LENE3M30S2su7pending5extraS2su7pending5extraS2su7pending5extra4SUloS2su7pending5extra4SUloS2su7pending5extra4SUloS2su7pending5extra4SUloFS2su1s1l7pending5extra4LENE5DISJES2su7pending5extra4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2wp2x06extra'4LENP3M301k2K12K2SS2su7pending5extra4SUhiS1s1l2x06extra'3TSES1s1l7pending5extra3TSES2su2wb2wp7pending5extra3WBP4LENP5DISJP3NEQ1k2K12K22NKS2su1s1l2x06extra'4LENE5DISJE1k2K12K22NKS2su2wb2wp1s1l7pending5extra3WBP4LENE5DISJE3NEQ1k2K12K22NKS2wb2wp7pending5extra4LENP3M30S2su7pending5extra4SUhiS2wb2wp7pending5extra4LENP3TSP1k2K12K2S2wb2wp7pending5extra4LENP3TSPS2su7pending5extra4SUloS2su7pending5extra4SUloS2su7pending5extra4SUhiS2su7pending5extra4SUhiS4regs3mem5model2wb2wp2fd2p08pending'5extra1K4LENP2EQFS2su7pending5extra4SUhiFS2su1s1l7pending5extra4LENE5DISJEFFS2su1s1l7pending5extra4LENE5DISJES2wb2wp7pending5extra4LENP1k2K12K2S2su7pending5extra4SUlo4SUhiS2su7pending5extra4SUlo4SUhiS2su7pending5extra4SUlo4SUhiS2su7pending5extra4SUlo4SUhiS2su7pending5extra4SUlo4SUhiS2su7pending5extra4SUlo4SUhiS2su7pending5extra4SUlo4SUhiS2su7pending5extra4SUlo4SUhiS2su7pending5extra4SUlo4SUhiS2su7pending5extra4SUlo4SUhiS2su7pending5extra4SUlo4SUhiS2su1f7pending5extra4SUlo4SUhi3Flo3FhiS2su1f7pending5extra4SUlo4SUhi3Flo3FhiS2su1f7pending5extra4SUlo4SUhi3Flo3FhiS2su7pending5extra4SUlo4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2wb2wp1l7pending5extra4LENP4LENE1k2K12K2FS2su2wb2wp1s1l7pending5extra4SUlo4SUhi3WBP4LENP4LENE5DISJP3TSP3TSES2su7pending5extra4SUloS2su7pending5extra4SUloFS2su1s1l7pending5extra4LENE5DISJES2su7pending5extra4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2wb2wp7pending5extra4LENPS2su7pending5extra4SUhiS2su7pending5extra4SUhiS1l2x06extra'4LENEFS2su1s1l7pending5extra4LENE5DISJEFS2su1s1l7pending5extra4LENE5DISJEFS2wb2wp1l7pending5extra4LENP4LENE3M30S2wb2wp1l7pending5extra3WBP4LENE3NEQS2su7pending5extra4SUhiS2su7pending5extra4SUhiFS2su1s1l7pending5extra4LENE5DISJEFS2su7pending5extra4SUloS2su7pending5extra4SUloS2su7pending5extra4SUhiS2x06extra'1k2K12K22NKS2suS2su2x06extra'S2su7pending5extra4SUhiFS2su1s1l7pending5extra4LENE5DISJES2su7pending5extra4SUhiS2su7pending5extra4SUhiS2wb2wp1l7pending5extra4LENP4LENE1k2K12K22EKS1s1l2x06extra'4LENE3TSE1k2K12K2S1s1l7pending5extra4LENE3TSE1k2K12K2S2wp2x06extra'4LENP3M301k2K12K2S2x06extra'1k2K12K22NKFFS2su7pending5extra4SUhiS2su4SUhiS2su2x06extra'4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUloS2su7pending5extra4SUloFS2x06extra'1k2K12K22EKS2su7pending5extra4SUloS2su7pending5extra4SUloS2su7pending5extra4SUloFFS2su7pending5extra4SUlo4SUhiFS2su1s1l7pending5extra4LENE5DISJEFS2wp2x06extra'4LENP3M301k2K12K22EKS7pending5extra3M301k2K12K22EKS2wp2x06extra'4LENP3M301k2K12K2S7pending5extra3M301k2K12K2S2wb2wp1l7pending5extra3WBP4LENP4LENE3NEQ1k2K12K22NKS2su7pending5extra4SUloS2su7pending5extra4SUloS2wb2wp7pending5extra3WBPS2wb2wp7pending5extra3WBP1k2K12K2S2su7pending5extra4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiFS2su7pending5extra4SUloS2su7pending5extra4SUloS2x06extra'1k2K12K2S7pending5extra3M301k2K12K2S2su7pending5extra4SUhiS2su7pending5extra4SUhiS2wp5extra3WBP4WPhiS2wb2wp7pending5extra4LENP3TSP1k2K12K2S2su7pending5extra4SUhiFS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2wb2wp7pending5extra3WBP4LENP3M30S2su7pending5extra4SUhiS2su7pending5extra4SUhiFFFS2wb2wp7pending5extra3WBP3NEQFS2su1s1l7pending5extra4LENE5DISJEFFS2su7pending5extra4SUloS2su7pending5extra4SUloS2su7pending5extra4SUhiFFFS2su1s1l7pending5extra4LENE5DISJES2su7pending5extra4SUhiS2su7pending5extra4SUhiS2wp1l5extra4LENP4LENE3M30S2wb2wp7pending5extra3TSPS2su7pending5extra4SUloS2su7pending5extra4SUloS2su7pending5extra4SUhiS7pending5extra1k2K12K2S2su7pending5extra4SUhiFS2x06extra'1k2K12K22EKS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2wp1s1l4LENP4LENE3TSES2su7pending5extra4SUloS2su7pending5extra4SUloFFS2su4SUhiS2su2x06extra'4SUhiS2wb2wp7pending5extra4LENP3TSP1k2K12K2S2wb2wp7pending5extra3WBP3NEQ1k2K12K22NKFS2su1s1l7pending5extra4LENE5DISJES2su7pending5extra4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2su7pending5extra4SUhiS2wb2wp1l7pending5extra4LENP4LENE3M30S2su7pending5extraS2su7pending5extra4SUhiFS2su7pending5extra4SUloS2su7pending5extra4SUloS2su4SUloS2su2x06extra'4SUloS2wb2wp1l7pending5extra4LENP4LENE3M301k2K12K2S2su7pending5extra4SUhi". (* [comment removed for export] *)
Theorem ref_stdio_write : ltac2:(CDefT.buildp (gd_tbl_P_stdio_write ()) "Pregs,(?.&5.(0.&40.))Pmem,P,(0.&40.)(=.(0.&8.))Pmodel,$32.Psu,$1.Pf,$1.Pwb,$1.Pwp,$1.Pfd,$1.Ps,(0.&40.)Pl,(0.&40.)Pbufp,(0.&40.)Pbufsz,(0.&40.)Pcan,(0.&40.)Pret,(0.&40.)Ppending,(1=.(0.&8.))Pextra,(1=.(0.&8.))PK,$33.P,(7.(0.&40.)(10.R11.(11.&5.+2.$12.))(13.&40.R>.))P,(7.(0.&40.)(10.R12.(11.&5.+:.$12.))(13.&40.R>.))P,(7.(0.&40.)(10.R13.(11.&5.+;.$12.))R;.)P,(7.(0.&40.)(10.R14.(11.&5.+<.$12.))R;.)P,(7.(0.&40.)(10.R15.(11.&5.+1.$12.))R8.)P,(2.(3.+100000000.+70.)R13.)P,(2.R14.+800000000000.)P,(7.$34.(35.$16.R17.(13.&40.(;.R15.+70.))#70.)$36.)P,(2.+4<000.R15.)P,(2.(3.R16.+>8.)+7=330.)P,(37.R1:.R17.R16.R15.R14.R11.R10.)P,(38.R1;.R10.)P,(9.(<.=R16.)(<.R16.+80000000.))P,(7.(=.$39.)(3:.(3;.R1<.)(13.&40.R17.))(1?.$39.(3<.(13.&40.R17.))))P,(7.(=.(0.&40.))(3=.R1=.)(3>.(0.&40.)))P,(7.(1=.(3?.(0.&40.)(0.&40.)))(40.R1>.)(25.(3?.(0.&40.)(0.&40.))))P,(9.(2.=R1<.)(2.R1<.R1;.))P,(<.R1<.(5.+2.+40.))P,(7.$1.(;.R1=.R1>.)(20.(28.(0.&8.)R15.)))P,(7.$1.(4.&40.R1;.)(20.(28.(0.&8.)R15.)))P,(2.(3.(20.(28.(0.&8.)R17.))(20.(28.(0.&8.)R16.)))(5.+2.+1>.))P,(6.(2.R20.(;.R23.+70.))(2.R23.R21.))P,(6.(2.(3.(4.&40.R1?.)(4.&40.R1>.))(;.R24.+70.))(2.R24.(4.&40.R1?.)))P,(2.(3.(4.&40.R20.)(4.&40.R1?.))(5.+2.+40.))P,(2.R23.+800000000000.)P,(2.(3.(4.&40.R22.)(4.&40.R21.))+800000000000.)P,(7.(=.(1=.(0.&8.)))(1>.$16.R2:.(13.&40.R26.)(28.(0.&8.)R1=.))(1?.(1=.(0.&8.))R1=.))P,(7.(=.(1=.(0.&8.)))(1>.$16.R2;.R24.(28.(0.&8.)R1=.))(1?.(1=.(0.&8.))R1=.))P,(41.R20.)P,A1.R1>.(25.$26.)P,Pregs',(?.&5.(0.&40.))Pmem',P,(0.&40.)(=.(0.&8.))P,(7.(0.&40.)(10.R2.(11.&5.+:.$12.))R28.)P,(7.(0.&40.)(10.R3.(11.&5.+2.$12.))(13.&40.R2?.))P,(7.(0.&40.)(10.R4.(11.&5.+1.$12.))R26.)P,(7.(0.&40.)(10.R5.(11.&5.+8.$12.))(10.R34.(11.&5.+8.$12.)))P,(7.(0.&40.)(10.R6.(11.&5.+9.$12.))(10.R35.(11.&5.+9.$12.)))P,(7.(0.&40.)(10.R7.(11.&5.+12.$12.))(10.R36.(11.&5.+12.$12.)))P,(7.(0.&40.)(10.R8.(11.&5.+13.$12.))(10.R37.(11.&5.+13.$12.)))P,(7.(0.&40.)(10.R9.(11.&5.+14.$12.))(10.R38.(11.&5.+14.$12.)))P,(7.(0.&40.)(10.R:.(11.&5.+15.$12.))(10.R39.(11.&5.+15.$12.)))P,(7.(0.&40.)(10.R;.(11.&5.+16.$12.))(10.R3:.(11.&5.+16.$12.)))P,(7.(0.&40.)(10.R<.(11.&5.+17.$12.))(10.R3;.(11.&5.+17.$12.)))P,(7.(0.&40.)(10.R=.(11.&5.+18.$12.))(10.R3<.(11.&5.+18.$12.)))P,(7.(0.&40.)(10.R>.(11.&5.+19.$12.))(10.R3=.(11.&5.+19.$12.)))P,(7.(0.&40.)(10.R?.(11.&5.+1:.$12.))(10.R3>.(11.&5.+1:.$12.)))P,(7.(0.&40.)(10.R10.(11.&5.+1;.$12.))(10.R3?.(11.&5.+1;.$12.)))P,(7.(0.&40.)(10.R11.(11.&5.+3.$12.))(10.R40.(11.&5.+3.$12.)))P,(7.(0.&40.)(10.R12.(11.&5.+4.$12.))(10.R41.(11.&5.+4.$12.)))P,(31.R41.R3?.R3>.R38.R37.R12.)(15.$16.(17.(18.$19.R14.R36.R13.(1;.$16.))R41.)R33.)(15.$16.(17.(18.$19.R30.(11.&40.+41:34.$12.)R2?.(1;.$16.))R2>.)(24.(2:.(0.&8.)$26.(2;.(13.&40.R29.))(2>.(0.&8.)R22.R21.))R20.))")
(* [comment removed for export] *).
Proof.
  intros regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD Hfd Hh Hlazy WBP WPhi
         LENP LENE M30 DISJP DISJE SNW TSP TSE RDP RDE Hret HKnil HK.
  pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
  pose proof SWF as SWF'. pose proof SSP as SSP'.
  destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
  { rewrite <- LENE. symmetry. apply u64_roundtrip'. }
  (* [comment removed for export] *)
  set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                       (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
  assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
  { subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
  assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x7d330) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
  assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }
  (* [comment removed for export] *)
  assert (HK' : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     LM su mem1 m ->
     realizes RSEGS (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K).
  { intros. apply HK. all: try assumption.
    eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
    match goal with H : LM _ _ _ |- _ => exact H end. }
  pose proof (finish_nil su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
  pose proof (loop1 su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
  pose proof (loop2 su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
  pose proof (LM_refl su mem1) as LM1.
  destruct (Z.eq_dec wb wp) as [EQ|NEQ].
  - (* [comment removed for export] *)
    destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
    subst wb.
    ddestruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?M _) _) _ =>
      replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
    rewrite Z.sub_diag in M96.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    destruct extra as [|x0 extra'].
    + (* [comment removed for export] *)
      cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
      eapply (rz_writev1_zero RSEGS regs1 (0x41abc : word) mem1 model W_3e370 fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
        [ exact F_3e370 | exact E_3e370 | exact Hh | exact Hlazy | exact Hfd | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | u_norm; unfold TASK_SIZE; lia | unfold TASK_SIZE; lia
        | ].
      { u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
      rewrite pc_3e374.
      ddestruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
        as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
      { gres. reflexivity. }
      { gres. rewrite R22. exact HlZ. }
      { lia. }
      eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
      apply FIN; [|exact LM1].
      eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
    + (* [comment removed for export] *)
      eapply (rz_writev1_wall RSEGS regs1 (0x41abc : word) mem1 model W_3e370 fd
                (Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
        [ exact F_3e370 | exact E_3e370 | exact Hh | exact Hlazy | exact Hfd | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | exact HKnil | ].
      * u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
      * unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
      * u_norm. unfold TASK_SIZE. lia.
      * unfold TASK_SIZE. lia.
      * cbn [length] in LENE. lia.
      * lia.
      * intros k K1 K2. rewrite pc_3e374.
        destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
        -- ddestruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. f_equal. lia. }
           { lia. }
           eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
           apply FIN; [|exact LM1].
           eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- ddestruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                       (Z.of_nat (length (x0 :: extra'))))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. reflexivity. }
           { lia. }
           { lia. }
           { lia. }
           eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           apply (L1 (length (x0 :: extra')) regs2 mem1 k s (x0 :: extra')); try lia.
           ++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
           ++ exact LM1.
           ++ exact P10.
           ++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
           ++ rewrite P18. gres. exact R18.
           ++ rewrite P19. gres. exact R19.
           ++ exact M88.
           ++ rewrite <- HlZ. exact M80.
           ++ exact Be.
  - (* [comment removed for export] *)
    ddestruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1. fold mem1.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    eapply (rz_writev2_wall RSEGS regs1 (0x41abc : word) mem1 model W_3e370 fd
              (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
      [ exact F_3e370 | exact E_3e370 | exact Hh | exact Hlazy | exact Hfd | exact FD
      | exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | exact HKnil | ].
    + u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
    + u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
    + u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
    + rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
    + unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
    + u_norm. unfold TASK_SIZE. lia.
    + u_norm. unfold TASK_SIZE. lia.
    + unfold TASK_SIZE. lia.
    + u_norm. lia.
    + u_norm. lia.
    + intros k K1 K2. rewrite pc_3e374. rewrite length_app in K2.
      destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
      * ddestruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite R22. f_equal. lia. }
        { lia. }
        eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
        apply FIN; [|exact LM1].
        eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      * ddestruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                    (wp - wb + bv_unsigned l))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact R22. }
        { lia. }
        { lia. }
        { lia. }
        eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (L2 (length pending + length extra)%nat regs2 mem1 k (Z_to_bv 64 wb) pending s extra); try lia.
        -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- exact LM1.
        -- exact P10.
        -- rewrite P22. gres. rewrite R22. f_equal. lia.
        -- rewrite P18. gres. exact R18.
        -- rewrite P19. gres. exact R19.
        -- exact M104.
        -- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
        -- exact M88.
        -- rewrite <- HlZ. exact M80.
        -- exact Bp.
        -- exact Be.
        -- u_norm. lia.
        -- u_norm. lia.
        -- u_norm. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
