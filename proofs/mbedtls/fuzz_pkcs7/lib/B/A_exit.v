(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape Tac RegsExt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ShapeX BBFrame AgentLib SymExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow Restrict RestrictLib NodesA NodesA2 SymDriveA RestrictRun.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_stdio_defs A_exit_defs A_exit_run2 A_exit_run3
  A_stdio_write_run1 A_stdio_write_run2 A_stdio_write A_exit_lib A_exit_front1 A_unreg_globals A_aglob_table A_exit_front
 A_code_dd000_de000 A_code_e3000_e4000    .
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_stdio_write P_exit.  (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_A_exit () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.nil"; "Thm.WEX"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.B.A_exit_base.file_clean"; "RocqVerifyHarness.AgentSubmission.B.A_exit_defs.stdout_pendingA"; "RocqVerifyHarness.AgentSubmission.LibA.Restrict.restrict"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.B.A_exit_defs.exit_commonA"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "stdpp.bitvector.definitions.bv_and"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.B.A_exit_run3.stdout_dirty_hdr"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "RocqVerifyHarness.AgentSubmission.B.A_exit_defs.exit_preA"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition regs_tree (regs : bvmap 5 word) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "(0.(1.O1.(2.&5.+1.$3.))(1.O1.(2.&5.+2.$3.))(1.O1.(2.&5.+3.$3.))(1.O1.(2.&5.+4.$3.))(1.O1.(2.&5.+5.$3.))(1.O1.(2.&5.+6.$3.))(1.O1.(2.&5.+7.$3.))(1.O1.(2.&5.+8.$3.))(1.O1.(2.&5.+9.$3.))(1.O1.(2.&5.+:.$3.))(1.O1.(2.&5.+;.$3.))(1.O1.(2.&5.+<.$3.))(1.O1.(2.&5.+=.$3.))(1.O1.(2.&5.+>.$3.))(1.O1.(2.&5.+?.$3.))(1.O1.(2.&5.+10.$3.))(1.O1.(2.&5.+11.$3.))(1.O1.(2.&5.+12.$3.))(1.O1.(2.&5.+13.$3.))(1.O1.(2.&5.+14.$3.))(1.O1.(2.&5.+15.$3.))(1.O1.(2.&5.+16.$3.))(1.O1.(2.&5.+17.$3.))(1.O1.(2.&5.+18.$3.))(1.O1.(2.&5.+19.$3.))(1.O1.(2.&5.+1:.$3.))(1.O1.(2.&5.+1;.$3.))(1.O1.(2.&5.+1<.$3.))(1.O1.(2.&5.+1=.$3.))(1.O1.(2.&5.+1>.$3.))(1.O1.(2.&5.+1?.$3.)))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L19795167282.400000;S4regs1i2Hi". (* [comment removed for export] *)
Lemma getr_regs_tree : forall regs (r : reg), getr (regs_tree regs) r = getr regs r.
Proof.
  intros regs r. pose proof (ridx_range r) as Hi. rewrite <- (ridx_roundtrip r). set (i := ridx r) in *. clearbody i.
  destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
    lazymatch goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
      let rk := eval vm_compute in (Z.of_nat kk) in change (Z.of_nat kk) with rk end;
    unfold regs_tree, mkR; [unfold getr; cbn; reflexivity | ..]; cbn [getr bv_eqb Z.eqb bv_unsigned Z_to_bv]; reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rdn_munch : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "PW,(4.$5.)Pm,P,(6.&40.)(7.(6.&8.))Pm',P,(6.&40.)(7.(6.&8.))Pa,(6.&40.)Pn,$8.P,(9.R5.R4.R3.)P,(:.R6.(;.&40.R3.)(<.R2.))P,(=.(>.(;.&40.R4.)(<.R3.))(?.+2.+40.))(10.(7.(4.(6.&8.)))(11.$12.R6.R5.R4.)(11.$12.R7.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros W m m' a n MU D NW. apply rdn_ext; [exact NW|]. intros x Hx. apply MU. eapply disjoint_outside; [exact D | exact Hx].
Qed.


Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L15045343008.13L26985714050.12L41041291118.14L58757241649.13L66026891576.1200000300B00Z00]00lS1nS2lo1a1n2H03HloS2lo2hi1a1n3Hlo3Hhi1i2HiS1nS2hi1a1n2H13Hhi". (* [comment removed for export] *)
Lemma stk_wmono_store_ok : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pm,P,(6.&40.)(7.(6.&8.))Pm',P,(6.&40.)(7.(6.&8.))Plo,$13.Phi,$13.Pa,$13.Pn,$8.P,(14.$12.R6.R4.R3.)P,(15.$12.R7.R6.)P,(=.R6.R4.)P,(=.(>.R5.(<.R4.))R6.)(10.$16.(17.$12.R9.(18.&40.R6.)R5.)$19.)")
(* [comment removed for export] *).
Proof.
  (intros m m' lo hi a n dd_H; ddestruct dd_H as (H0 & H1 & ST); intros WM Hlo Hhi).
  assert (WR : wr_at RSEGS m' a (Z.of_nat n)).
  { split; [lia|]. split; [lia|]. intros i Hi. apply WM. apply (proj1 (ST (a + i)%Z ltac:(lia))). }
  pose proof (wr_at_store_ok RSEGS m' a (Z.of_nat n) 0 n WR ltac:(lia) ltac:(lia)) as S. rewrite Z.add_0_r in S. exact S.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L10358294872.10L1309844146.7  L23615032493.9 L24933826308.7 L28807814807.1000000900B00K00T00eS2cs1i2HiS1A2cs2B1S2cs1i2HiS1A2cs2B0S1A2cs2B02B11i2Hi". (* [comment removed for export] *)
Lemma rw_of_ro_sok : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pm,P,(6.&40.)(7.(6.&8.))PA,$13.Pcs,(4.$1:.)P,(1;.$12.R3.R2.R1.)P,(10.$16.(17.$12.R4.(18.&40.R3.)(1<.R2.))$19.)(1=.$12.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m A cs RO SOK. split; [exact RO|]. destruct RO as [WF (B0 & B1 & _)]. rewrite cells_bytes_length in B1 by exact WF.
  split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (store_ok_wview RSEGS m (Z_to_bv 64 A) (cells_size cs) (Z.to_nat i) SOK ltac:(lia)) as W.
  rewrite unsigned_lit in W by lia. rewrite Z2Nat.id in W by lia. exact W.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma wseg_101880 : wseg_ok RSEGS (Z_to_bv 64 0x1053a0) 8192%nat = true.
Proof. vm_compute. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L11329207438.5L34694718175.5L39308628102.5L56763568741.500000300<00E00RS1nS1a1n3HhiS1a1n3HloS1a1n3Hlo3Hhi". (* [comment removed for export] *)
Lemma store_ok_1ae : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pm,P,(6.&40.)(7.(6.&8.))Pa,$13.Pn,$8.P,(=.+1053:0.R2.)P,(=.(>.R3.(<.R2.))+1073:0.)(10.$16.(17.$12.R5.(18.&40.R4.)R3.)$19.)")
(* [comment removed for export] *).
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window RSEGS m (Z_to_bv 64 0x1053a0) (Z_to_bv 64 a) 8192%nat n 0x1053a0 0x1073a0);
    [reflexivity | reflexivity | lia | exact wseg_101880 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rtc_cell RTC :=
  lazymatch goal with
  | |- ro_cells _ _ ?A [C8 (Z_to_bv 64 ?v)] => apply (asan_rtc_cell _ A 8%nat v RTC)
  | |- ro_cells _ _ ?A [C4 (Z_to_bv 64 ?v)] => apply (asan_rtc_cell _ A 4%nat v RTC)
  | |- ro_cells _ _ ?A [C1 (Z_to_bv 8 ?v)] => apply (asan_rtc_cell _ A 1%nat v RTC)
  end; cbn [rtc_cells]; repeat (first [left; reflexivity | right]).

Lemma exit_got_rtc : forall m, asan_rtc m -> exit_got m.
Proof. intros m RTC. split; rtc_cell RTC. Qed.
Lemma unreg_got_rtc : forall m, asan_rtc m -> unreg_got m.
Proof. intros m RTC. split; rtc_cell RTC. Qed.
Lemma unreg_consts_rtc : forall m, asan_rtc m -> unreg_consts m.
Proof. intros m RTC. split; rtc_cell RTC. Qed.
Lemma cov_rtc : forall m, asan_rtc m -> ro_cells RSEGS m 0x19b8a0 [C1 (Z_to_bv 8 0)].
Proof. intros m RTC. rtc_cell RTC. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L43843533375.2L9577354143.2 000001002SS". (* [comment removed for export] *)
Lemma flag_rtc : forall m, asan_rtc m -> rw_cells RSEGS m 0x106340 [C8 (Z_to_bv 64 1)].
Proof. intros m RTC. apply rw_of_ro_sok; [rtc_cell RTC | apply store_ok_1ae; cbn; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L30727007039.2L58929173663.2000001002SS". (* [comment removed for export] *)
Lemma mux_rtc : forall m, asan_rtc m -> rw_cells RSEGS m 0x1072b0 [C8 (Z_to_bv 64 0)].
Proof. intros m RTC. apply rw_of_ro_sok; [rtc_cell RTC | apply store_ok_1ae; cbn; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Ltac norm_getr :=
  repeat match goal with
  | |- context [getr (TNode ?a ?b ?c) ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let v := eval cbn [tget] in (match tget p (TNode a b c) with Some v => v | None => w0 end) in
      change (getr (TNode a b c) r) with v
  end.

Section Thm.
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable K : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000%Z.
  Hypothesis GSB : al_gsb AL = 0x1099f8%Z.
  Hypothesis IMGCS : img_cs AL CS.
  Hypothesis K_halted : forall mo, K mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pmo,$1>.Pacc,(4.(1?.(6.&40.)$8.))P,A1.VK,R2.P,(20.VAL,VCS,R2.)(21.$1>.Lmo',$1>.(22.(10.(7.$1>.)(23.R5.R4.)(24.$1>.R1.))(22.A1.VK,R1.(25.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pmo,$1>.Pmo',$1>.P,A1.VK,R2.P,(10.$26.(27.R2.)(27.R3.))P,(10.(4.(1?.(6.&40.)(6.&40.)))(28.R3.)(28.R4.))P,(10.(4.(6.&40.))(29.R4.)(29.R5.))P,(10.(7.(6.&40.))(2:.R5.)(2:.R6.))A1.VK,R6.")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Variable su : Z.
  Hypothesis SUlo : (4294967296 + 320 <= su)%Z.      (* [comment removed for export] *)
  Hypothesis SUhi : (su <= 2^47)%Z.
  Hypothesis FRCS : forall z, (su - 320 <= z < su)%Z -> CS z.

  (* [comment removed for export] *)
  Definition WEX : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "(2;.(1?.$13.$13.)(2<.$13.$13.+7???:000.+800=3000.)(2;.(1?.$13.$13.)(2<.$13.$13.+63<080.+63<084.)(2;.(1?.$13.$13.)(2<.$13.$13.+106340.+106348.)(2;.(1?.$13.$13.)(2<.$13.$13.+1072;0.+1072;8.)(2;.(1?.$13.$13.)(2<.$13.$13.+106390.+106391.)(2;.(1?.$13.$13.)(2<.$13.$13.+65<=00.+65<=04.)(2;.(1?.$13.$13.)(2<.$13.$13.+65<:>0.+65<:?8.)(2;.(1?.$13.$13.)(2<.$13.$13.(2=.Vsu,+140.)Vsu,)(2>.(1?.$13.$13.))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L11321447016.22L1442294162.22 L24662439586.22L24902630162.22L26981515745.22L34418999250.22L37779921682.22L49042914505.22L49672006162.22L63169175506.22L66031090011.2200000700>00E00L00S00Z00a01001701>01ES1a1n1HS1a1n1HS1a1n1HS1a1n1HS1a1n1HS1a1n1HS1a1n1HS2su4SUlo1a1n1HS1a1n1HS1a1n1HS1a1n1H". (* [comment removed for export] *)
  #[using="SUlo"] Lemma rdn_WEX : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pm,P,(6.&40.)(7.(6.&8.))Pm',P,(6.&40.)(7.(6.&8.))Pa,$13.Pn,$8.P,(9.$2?.R4.R3.)P,(30.(22.(=.+?1000.R3.)(=.(>.R3.(<.R2.))+?;358.))(30.(22.(=.+65<=23.R3.)(=.(>.R3.(<.R2.))+65<=24.))(30.(22.(=.+65=188.R3.)(=.(>.R3.(<.R2.))+65=190.))(30.(22.(=.+65<:=0.R3.)(=.(>.R3.(<.R2.))+65<:=8.))(22.(=.+65=1:0.R3.)(=.(>.R3.(<.R2.))+65=5:0.))))))(10.(7.(4.(6.&8.)))(11.$12.R5.(18.&40.R4.)R3.)(11.$12.R6.(18.&40.R4.)R3.))")
(* [comment removed for export] *).
  Proof.
    intros m m' a n MU H. apply (rdn_munch WEX m m'); [exact MU | | u_norm; lia].
    u_norm. cbn [WEX disjoint_from]. repeat split; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac tr_rdn MU := rewrite (rdn_WEX _ _ _ _ MU) by lia; assumption.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L21802040518.2900000;S1f3Hlo3Hhi". (* [comment removed for export] *)
  #[using="SUlo"] Lemma file_clean_WEX : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pm,P,(6.&40.)(7.(6.&8.))Pm',P,(6.&40.)(7.(6.&8.))Pf,$13.Pwp,(6.&40.)Prp,(6.&40.)P,(9.$2?.R5.R4.)P,(=.+?:488.R4.)P,(=.(>.R5.+>8.)+?:780.)P,(31.R8.R6.R5.R4.)(31.R8.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    (intros m m' f wp rp MU Hlo Hhi dd_H; ddestruct dd_H as (A1 & A2 & A3 & A4 & A5)). repeat split; tr_rdn MU.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L14297820934.24L2318320646.24 L25029676550.24L57419445590.24L68518603910.24000001002003004005SSSSS". (* [comment removed for export] *)
  #[using="SUlo"] Lemma stdio_globals_WEX : forall m m', munch WEX m m' -> stdio_globals m -> stdio_globals m'.
  Proof.
    (intros m m' MU dd_H; ddestruct dd_H as (A1 & A2 & A3 & A4 & A5)). repeat split; tr_rdn MU.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L34777098371.22L54165570947.22000001002SS". (* [comment removed for export] *)
  #[using="SUlo"] Lemma ssp_cells_WEX : forall m m' can, munch WEX m m' -> ssp_cells m can -> ssp_cells m' can.
  Proof.
    intros m m' can MU (A1 & A2). split; tr_rdn MU.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L11929749831.40L21794397569.4000000O00XS2wb2wp7pending8sp_range6sp_lenS7pending". (* [comment removed for export] *)
  #[using="SUlo"] Lemma stdout_pendingA_WEX : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pm,P,(6.&40.)(7.(6.&8.))Pm',P,(6.&40.)(7.(6.&8.))Pwb,$13.Pwp,$13.Pbufp,(6.&40.)Pbufsz,(6.&40.)Prp1,(6.&40.)Pcan,(6.&40.)Ppending,(4.(6.&8.))P,(9.$2?.R9.R8.)P,(32.R:.R8.R7.R6.R5.R4.R3.R2.)(32.R:.R9.R8.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros m m' wb wp bufp bufsz rp1 can pending MU P. destruct P. split; try assumption; try tr_rdn MU.
    all: first [ eapply ssp_cells_WEX; eauto | rewrite (rdn_WEX _ _ _ _ MU); [assumption| lia] ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Let D : word -> bool := Dimg [(su - 320, su)%Z].
  #[using="Type"] Lemma T_Dseg : forall a : word, segcov RSEGS (bv_unsigned a) = true -> D a = true.
  Proof. intros a H. unfold D. apply Dimg_Dseg. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L28376355032.21000009S2su1z2Hz". (* [comment removed for export] *)
  #[using="IMG FRCS"] Lemma T_DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
  Proof.
    intros a H. unfold D in H. eapply (Dimg_DOK AL CS IMG [(su - 320, su)%Z]); [|exact H].
    constructor; [|constructor]. cbn. intros z Hz. apply FRCS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L14982947482.17000009S2su4SUlo". (* [comment removed for export] *)
  #[using="SUlo"] Lemma T_D0 : D (Z_to_bv 64 0) = false.
  Proof. unfold D. apply Dimg_D0. constructor; [cbn; lia|constructor]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L14989311460.23L28139165318.23L28376355032.2300000900B00YS2su4SUloS2su4SUhiS2su2lo2hi3Hlo3Hhi1z2Hz". (* [comment removed for export] *)
  #[using="SUlo SUhi"] Lemma T_frame : forall lo hi, (su - 320 <= lo)%Z -> (hi <= su)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply (Dimg_cov [(su - 320, su)%Z] (su - 320) su); [left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40646207469.2300000DS2lo2hi3Hlo3Hhi1z2Hz". (* [comment removed for export] *)
  #[using="Type"] Lemma T_img : forall lo hi, (0x10000 <= lo)%Z -> (hi <= 0x65f000)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply (Dimg_img [(su - 320, su)%Z]). unfold AIMG_LO, AIMG_HI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Definition rrunT := rz_smsteps_RK RSEGS D AL CS K K_halted K_mat T_Dseg asegs_top T_DOK T_D0.

  Ltac rres T := first
    [ eapply (rdn_restrictD RSEGS D); [T | u_norm; lia | first [apply T_frame; u_norm; lia | apply T_img; u_norm; lia]]
    | eapply (store_ok_restrictD RSEGS D); [T | u_norm; lia | apply T_frame; u_norm; lia] ].
  Ltac dz := first [lia | apply T_frame; lia | apply T_img; lia].
  Ltac solve_outside := intros xx Hxx; repeat (rewrite (wbytes_agree_outD_Z D) by (first [exact Hxx | dz])); reflexivity.
  Ltac push_restrict_in H := repeat (rewrite (wbytes_restrict_Z D) in H by dz).
  Ltac rrunK RUN KMH KMnew :=
    push_restrict_in RUN;
    eapply rrunT; [exact (KM_K _ _ _ KMH) | exact RUN | solve_outside | ];
    clear RUN;
    let mo1 := fresh "mo" in let HK1 := fresh "HKm" in let MM1 := fresh "MM" in
    intros mo1 HK1 MM1; pose proof (KM_step _ _ _ _ KMH HK1 MM1) as KMnew; clear HK1 MM1.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L10961704545.28L17748879557.28L19802178785.28L20670879744.28L21269600837.28L22034803388.28L25008261424.28L29909649170.28L30301831237.28L33109128325.28L37044631088.28L38734942336.28L40094605628.28L41952509857.28L42350128508.28L42490243008.28L45570946386.28L46105476284.28L4692874864.28 L49791655442.28L50422769633.28L50775506304.28L5224374597.28 L57591205345.28L62811904640.28L65707013394.28L68142318994.28L6948393648.28 L937527088.28  L9998372284.28 00000700>00E00L00S00Z00[00b00i01001101801?01F01M01T01[01b01c01j02102802?02F02M02T02[02\02]02dS1f3FhiS1f3FhiS1f3FhiS1f3FloS1f3FhiS1f3FloFS1f3FhiS1f3FhiS1f3FhiFS1f3FloS1f3FloS1f3FhiS1f3FloS1f3FloS1f3FhiS1f3FloFS1f3FhiS1f3FhiS1f3FloS1f3FhiS1f3FhiS1f3FloS1f3FhiS1f3FhiFFS1f3Flo". (* [comment removed for export] *)
  #[using="Type"] Lemma file_clean_restrict : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pmem,P,(6.&40.)(7.(6.&8.))Pf,$13.Pwp,(6.&40.)Prp,(6.&40.)P,(=.+?:488.R3.)P,(=.(>.R4.+>8.)+?:780.)P,(31.R6.R5.R4.R3.)(31.(33.VD,R7.)R6.R5.R4.)")
(* [comment removed for export] *).
  Proof. (intros mem f wp rp Flo Fhi dd_H; ddestruct dd_H as (A1 & A2 & A3 & A4 & A5)). repeat split; rres ltac:(eassumption). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L11877557842.23L15823379762.23L17044074450.23L20036404050.23L21919181657.23L26989216541.23L28566315021.23L31563882793.23L34510520402.23L3632175405.23 L38904319117.23L39003257869.23L40634725554.23L41778728861.23L48639568413.23L48873085597.23L49402687154.23L5296698157.23 L53498900013.23L54967437746.23L57643455273.23L59134363293.23L6001714205.23 L60876622733.23L63709029545.23L64072102829.23L64985955981.23L66442924098.23L68194921890.23L9911450153.23 00000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00F00G00H00I00J00K00L00M00NSSSSSFSSSSSFSSFSSSSSSFFSSSSSSS". (* [comment removed for export] *)
  #[using="Type"] Lemma stdio_globals_restrict : forall mem, stdio_globals mem -> stdio_globals (restrict D mem).
  Proof. (intros mem dd_H; ddestruct dd_H as (A1 & A2 & A3 & A4 & A5)). repeat split; rres ltac:(eassumption). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01?0?L10197891347.82L10226654351.53L10782901340.82L13334624911.53L14900201395.87L14901945081.89L15213653512.87L15215577922.89L17259695690.89L17261964032.87L1959583980.82 L20079732669.89L20082246391.87L20506007223.82L22155881139.87L22157545465.89L23408145876.53L23602442615.87L23604892733.89L23867809606.82L23867809734.81L24834809721.89L24836815411.87L27251732034.89L27253721864.87L27263877741.82L280640787.82  L280640915.81  L28376355032.55L28929059398.82L28929059654.80L31081274947.82L31620927677.89L31623460343.87L32634741912.87L33179402639.53L35224978895.87L35651202110.82L37590237359.77L37590367791.82L37592137268.87L37592285579.53L37820351306.89L37822293504.87L39010146017.53L40140938566.82L40143048902.79L41683651684.82L44145400125.89L44147407991.87L44333973091.87L44336159529.89L44589887818.89L44592075776.87L45299247042.89L45301432968.87L45380048179.87L45381988473.89L46760686194.82L48262620200.82L51965146211.87L51967136041.89L53512151081.53L53999253085.82L54322846087.53L54517943081.89L54519885411.87L56206093331.82L56206093587.80L63788619520.87L63791149642.89L67021155501.53L67654170723.87L67656621353.89L8176458019.82 L8474122003.82 L8476203667.79 L9186022280.87 L9187702466.89 00000400500>00?00C00G00K00O00]00k01401=01F01O01S01W01X01a01j01n02202602:02>02B02C02G02K02T02X02\02]02f02o03003103203303A03O03]03k04904G04H04L04P04Q04Z04c04d04e05305A05E05I05M05Q05Z05^05_05`05a05b05k05l05m06106506C06Q06R06S06T06]06a06e06i06mS2suFS2su4SUhiFS2suS2suS2suS2suS2su4SUlo4SUhiS2su4SUlo4SUhiS2su4SUhiS2su4SUhiS2su4SUhiS2su4SUloS2suS2suFS2su4SUhiS2su4SUhiS2suS2suS2suS2suS2suS2suFS2suS2suS2su1z2HzS2suS2suFS2su4SUhiS2su4SUhiFFFFS2su4SUlo4SUhiS2su4SUlo4SUhiS2su4SUlo4SUhiS2su4SUlo4SUhiS2su4SUlo4SUhiS2su4SUlo4SUhiFS2suS2suFS2su4SUhiS2su4SUhiFFS2su4SUlo4SUhiS2su4SUlo4SUhiS2suS2suS2suS2suS2su4SUhiS2suFFFFS2su4SUloFFS2suS2suS2su4SUlo4SUhiS2su4SUlo4SUhiFFFS2su4SUloS2suS2suS2suS2su". (* [comment removed for export] *)
  #[using="AL CS IMG ALWF CSOK ASB IMGCS K_halted K_mat SUlo SUhi FRCS D"] Theorem ref_exit_cleanA : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pregs,(34.&5.(6.&40.))Pmem,P,(6.&40.)(7.(6.&8.))Pmo,$1>.Pcode,(6.&40.)Ptid,$13.Pwp0,(6.&40.)Prp0,(6.&40.)Pwp2,(6.&40.)Prp2,(6.&40.)Pwp1,(6.&40.)Prp1,(6.&40.)P,(35.R;.R:.Vsu,R8.R7.R6.R5.R4.R3.)P,(31.R;.+?:578.R3.R2.)P,A1.VK,R;.(36.$12.(37.(38.$39.R>.(18.&40.+>11:8.)R=.(3:.$12.))R<.)(3;.(3<.&40.R;.(18.&40.+??.))(3=.R<.)))")
(* [comment removed for export] *).
  Proof.
    intros regs mem mo code tid wp0 rp0 wp2 rp2 wp1 rp1 EC F1 HK. destruct EC.
    apply (srzJ_getr_ext RSEGS (regs_tree regs) regs). { intros r. apply getr_regs_tree. }
    unfold regs_tree. rewrite ec_sp, ec_tp, ec_a0.
    change (mkst ?R ?pc ?M ?rom) with (MS R bvmap_empty pc (Z_to_bv 32 0) None M rom).
    ddestruct ec_atexit as (b & fin & jp & jq & jf & AT & ICB).
    eapply (rz_evtA_K RSEGS AL CS K K_halted K_mat); [exact HK | | ].
    { eapply (exit_frontA AL IMG ALWF CS CSOK) with (lo := (su - 320)%Z) (tid := tid) (recs := aglob_recs); try exact ASB; try exact GSB; try exact IMGCS;
        rewrite ?(unsigned_lit su) by lia; try eassumption; try reflexivity; try lia.
      - apply cov_rtc; assumption.
      - apply exit_got_rtc; assumption.
      - apply aglob_table_at; assumption.
      - apply aglob_recs_ok.
      - apply unreg_got_rtc; assumption.
      - apply unreg_consts_rtc; assumption.
      - apply flag_rtc; assumption.
      - apply mux_rtc; assumption.
      - intros z Hz. apply FRCS. lia. }
    cbn beta. intros ms' mo' POST HK' MM'. unfold exit_front_post in POST.
    ddestruct POST as (t0 & t1 & t2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & ST' & MP').
    rewrite ?(unsigned_lit su) in * by lia.
    pose proof (conj HK' MM' : KM K mo mo') as KM1.
    change (MS ?R _ ?pc _ _ ?M ?rom) with (mkst R pc M rom).
    replace (Z_to_bv 64 945304) with (0x0e6c98 : word) by (apply bv_eq; reflexivity).
    pose proof (stdio_globals_WEX _ _ MU ec_glob) as G'.
    pose proof (file_clean_WEX _ _ 0x0fa668%Z _ _ MU ltac:(lia) ltac:(lia) ec_in) as F0'.
    pose proof (file_clean_WEX _ _ 0x0fa578%Z _ _ MU ltac:(lia) ltac:(lia) F1) as F1'.
    pose proof (file_clean_WEX _ _ 0x0fa488%Z _ _ MU ltac:(lia) ltac:(lia) ec_err) as F2'.
    lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?R _ _ _) _) _ =>
      destruct (w3a R (restrict D m') (seg_rom RSEGS) (Z_to_bv 64 su) code wp0 rp0 wp1 rp1 wp2 rp2)
        as (regs3 & RUN & R10 & R17 & R2) end.
    all: rewrite ?(unsigned_lit su) by lia.
    all: try (unfold mkR; norm_getr; first [reflexivity | f_equal; lia]).
    all: try lia.
    2:{ apply stdio_globals_restrict. exact G'. }
    2:{ apply file_clean_restrict; [lia|lia|exact F0']. }
    2:{ apply file_clean_restrict; [lia|lia|exact F1']. }
    2:{ apply file_clean_restrict; [lia|lia|exact F2']. }
    { rres ltac:(eapply stk_wmono_store_ok; [exact ec_stk | exact WM | lia | cbn; lia]). }
    unfold mem_w3a in RUN. rewrite ?(unsigned_lit su) in RUN by lia. rrunK RUN KM1 KM2.
    eapply srzJ_conseq; [ eapply rz_exit_atA; [exact F_ddbd0 | exact E_ddbd0 | exact (K_halted _ (KM_K _ _ _ KM2)) | left; exact R17 | exact R10] |].
    rewrite (mo_mat_fs _ _ (proj2 KM2)). apply t_eq_refl.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0?L12805911077.39L13981522492.39L16807856713.39L18679800688.39L19046536713.39L24863824165.39L25523800892.39L2646492027.39 L26860240688.39L28364816165.39L3326192117.39 L35551845755.39L37185622581.39L40837825916.39L44536991792.39L45178557029.39L4754141001.39 L49234622773.39L49403929929.39L56763279995.39L57623070012.39L61254788149.39L6171207867.39 L6738528560.39 00000100:00C00L00U00V00_00h01101201;01D01M01V01_01`01i02202;02D02M02V02_02hFS7pendingS7pendingS7pendingS7pendingFS7pendingS7pendingS7pendingFS7pendingS7pendingS7pendingS7pendingS7pendingFS7pendingS7pendingS7pendingS7pendingS7pendingS7pendingS7pendingS7pending". (* [comment removed for export] *)
  #[using="Type"] Lemma stdout_dirty_hdr_restrict : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pmem,P,(6.&40.)(7.(6.&8.))Pwb,$13.Pwp,$13.Pbufp,(6.&40.)Pbufsz,(6.&40.)Prp1,(6.&40.)Pcan,(6.&40.)Ppending,(4.(6.&8.))P,(32.R8.R7.R6.R5.R4.R3.R2.R1.)(3>.(33.VD,R9.)R8.R7.)")
(* [comment removed for export] *).
  Proof. intros mem wb wp bufp bufsz rp1 can pending P. destruct P. repeat split; rres ltac:(eassumption). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "03B0@L10159020581.150L10197534807.103L10226654351.59 L10782733592.103L10909750220.150L11786685351.150L12293099734.150L13103549367.150L13334624911.59 L1396209851.116 L14363332030.150L14387241996.150L1454800652.150 L14901945081.115L14912791793.113L14945553763.150L14948546207.115L14958558102.150L15036707968.116L15200718408.150L15201062218.113L15215577922.115L15222892295.149L15222892295.150L17084321820.149L17249372226.113L17259695690.115L18826971676.149L18865312702.150L18908947811.150L19141879351.150L1959367080.103 L20069671349.113L20079732669.115L20506322931.103L20931972210.116L22151334643.150L22151678449.113L22157545465.115L22545790557.116L23061504478.149L23408145876.59 L23589851701.113L23604892733.115L23611318236.115L23810651303.150L23867809350.86 L24445564451.150L24834809721.115L24841001329.113L25222752604.115L25529819116.149L25529819116.150L26276014969.150L27156547762.150L27251732034.115L27257923658.113L27263546153.103L2753895692.115 L27844961501.116L280640531.86   L28286843235.150L28376355032.117L28376355032.61 L28744396274.103L28824154827.150L29089154041.150L29343532771.150L29960581662.116L29968876060.149L30885754851.150L30887756316.149L31325729797.150L31610557879.150L31610869429.113L31620927677.115L31843224163.150L33179402639.59 L34030360050.149L34497979031.150L34862219595.150L35274989248.116L35651542394.103L35695668786.150L36552436939.150L37302381703.149L37302381703.150L37587934582.113L37587934710.155L37588246132.150L37590011755.103L37590237359.83 L37592285579.59 L37820351306.115L37826479426.113L38061151038.150L38231066551.150L38891777608.150L38940057451.116L39010146017.59 L39279403548.149L3931594699.150 L39510636572.149L39649887756.150L397833522.150  L39858881970.150L39941488973.116L40140762114.103L40143048902.85 L40336249368.116L4035179332.113 L40646207469.118L4068304099.150 L4079211286.150 L41684008224.103L42107162147.103L42914517543.150L43654797310.150L44145400125.115L44151594805.113L44151774263.150L44329770273.113L44336159529.115L44579501890.113L44589887818.115L44709289948.115L45290393750.150L45299247042.115L45313712840.150L45314023882.113L45367293299.150L45367473777.113L45381988473.115L46297080997.150L46657250802.150L46760330038.103L46771147305.150L46968659340.150L47516683164.149L47650749359.103L47893299257.150L4818518458.116 L48262305132.103L48574040523.150L48933707943.150L49398451319.150L50250571959.150L5042673692.149 L50579007964.115L51081254883.150L51514765719.113L51967136041.115L51969333025.113L52206271393.116L5292462568.150 L53512151081.59 L54264794745.150L54322846087.59 L54515682593.113L54517943081.115L54607914059.150L55155020252.115L55187919324.115L55626297452.149L55626297452.150L55843089807.116L5608126135.150 L56271863607.150L56431232423.150L56739572530.118L57630847468.150L5767494951.150 L59294930572.150L59709344278.150L5997545176.150 L60373201372.115L60576358322.150L607588515.150  L61387609868.150L62109912254.150L62498861246.150L62870240907.150L63059468402.149L63531574846.150L63791149642.115L63801209922.113L64424641507.150L64546769271.150L64865531385.150L6567995491.150 L6613924447.103 L66193449703.150L66356490716.115L6649838313.116 L67021155501.59 L67023552099.150L67649968929.113L67656621353.115L68498418937.150L6934486024.116 L7868803321.150 L8067349731.150 L8176773223.103 L8182741368.150 L8474437207.103 L8476203667.85  L9181835466.113 L9187702466.115 L9238439602.150 L923891030.150  00000<00H00I00Z00k00l01801D01E01V01b02302D02P02\02h03403E03Q03]03i04504F04W04m05C05Y05o06;06G06S06d07507F07W07c07o08;08G08S08i08j09;09L09b09c09g0:30:?0:K0;10;B0;S0;_0;k0<70<C0<D0<P0<\0<`0<l0==0=F0=G0=S0=_0=k0>H0>^0>j0?@0?Q0?b0@30@D0@P0@Q0@b0@n0A:0AR0AS0A_0Ak0B<0BM0Bc0C90CO0Ce0D30DA0DW0Dm0E90EE0EQ0E]0E^0F40F@0FV0Fg0G30G?0GP0G\0G`0H10H20HT0H`0I10I20IO0IP0I\0Im0J>0JO0JP0JQ0Jg0K=0KS0Kd0L00L<0LH0LT0L`0Ll0M80MD0MU0Mf0N70NM0Nj0O60OW0Oc0Oo0P00P<0PH0P^0Q40Q@0QA0QB0QC0Q[0Qg0Qh0R40R=0R>0R?0RK0Ra0S70SH0SY0T10T=0TI0TJ0Ta0Tm0Tn0U?0UP0UQ0Ug0V30V?0VP0V\0Vh0W40WE0WQ0Wg0X=0XI0XU0Xa0Xm0YJ0YK0Ya0Ym0Yn0Z:0Z;0Z<0ZH0ZT0Z`0Zl0[=0[N0[Z0[^0[j0\60\B0\NS2su7pendingS2su7pendingFS2su4SUhi7pendingS2su4SUlo7pendingFS2su7pendingS2su7pendingFS2su4SUlo7pendingS2su7pendingS2su4SUlo7pendingS2su4SUlo7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingS2su4SUlo7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingS2su4SUhi7pendingS2su4SUhi7pendingS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su7pendingS2su7pendingS2su7pendingS2su4SUhi7pendingS2su4SUhi7pendingS2su4SUhi7pendingS2su4SUlo7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingS2su4SUlo4SUhi7pendingFS2su4SUhi7pendingS2su4SUhi7pendingS2su4SUlo4SUhi7pendingFS2suS2su7pendingS2su7pendingS2su7pendingS2su4SUlo4SUhi2wb2wp7pending5RANGE3LENS2su4SUlo7pendingS2su4SUlo7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingFS2su7pendingS2su7pendingS2suS2su7pendingS2su7pending1z2HzS2su1z2HzFS2su7pendingS2su7pendingS2su7pendingS2su4SUlo2wb2wp7pending5RANGES2su4SUlo4SUhi7pendingS2su7pendingS2su4SUlo4SUhi7pendingS2su4SUlo7pendingS2su4SUhi7pendingS2su4SUhi7pendingS2su4SUhi7pendingS2su7pendingFS2su4SUhi7pendingS2su7pendingS2su7pendingS2su2wb2wp7pending5RANGEFS2su7pendingS2su7pendingS2su4SUhi7pendingS2su4SUhi7pendingS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su4SUlo4SUhiS2su4SUlo4SUhiS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingFS2su4SUlo4SUhi7pendingS2su7pendingS2su4SUlo4SUhi7pendingS2su4SUlo7pendingS2su7pendingS2su7pendingS2su4SUlo7pendingS2su7pendingS2suS2su4SUhi7pendingFS2su4SUlo2wb2wp7pending5RANGE1z2HzS2su7pendingS2su4SUlo7pendingFS2su4SUlo2wb2wp7pending5RANGEFS2su7pendingS2su4SUhi7pendingS2su4SUhi7pendingS2su4SUhi7pendingFFS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su4SUlo7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingS2su4SUhi7pendingS2su4SUhi7pendingS2su4SUlo7pendingS2su4SUlo4SUhi7pendingS2su4SUlo2wb2wp7pending5RANGES2su7pendingS2su4SUlo2wb2wp7pending5RANGE3LENS2su7pendingS2su7pendingFS2su7pendingS2su7pendingS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su7pendingFFFS2su2wb2wp7pending5RANGES2su7pendingFS2su7pendingS2su4SUloFFS2su7pendingS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su4SUlo7pendingS2su4SUlo7pendingS2su2wb2wp7pending5RANGES2su7pendingS2su7pendingFS2AL2CS2su7pending1z2HzS2su7pendingFS2su4SUlo7pendingS2su4SUlo7pendingFS2su4SUlo4SUhi7pendingS2su7pendingS2su7pendingS2su4SUlo7pendingS2su7pendingS2su7pendingS2su7pendingS2su4SUhi7pendingS2su7pendingS2su4SUlo4SUhi7pendingS2su4SUlo4SUhi7pendingS2su7pendingS2su7pendingS2su7pendingS2su7pendingS2su4SUlo2wb2wp7pending5RANGEFS2su4SUlo4SUhi7pendingS2su7pendingFS2su7pendingFFS2su7pendingS2su7pendingS2su7pendingS2su7pendingS2su4SUlo7pendingS2su4SUlo7pendingS2su7pendingS2suS2su7pendingS2su7pendingS2su7pendingS2su7pending". (* [comment removed for export] *)
  #[using="AL CS IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly SUlo SUhi FRCS D"] Theorem ref_exit_flushA : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pregs,(34.&5.(6.&40.))Pmem,P,(6.&40.)(7.(6.&8.))Pmo,$1>.Pcode,(6.&40.)Ptid,$13.Pwp0,(6.&40.)Prp0,(6.&40.)Pwp2,(6.&40.)Prp2,(6.&40.)Pwb,$13.Pwp,$13.Pbufp,(6.&40.)Pbufsz,(6.&40.)Prp1,(6.&40.)Pcan,(6.&40.)Ppending,(4.(6.&8.))P,(35.R10.R?.Vsu,R=.R<.R;.R:.R9.R8.)P,(32.R10.R8.R7.R6.R5.R4.R3.R2.)P,(10.(7.$3?.)(40.(41.R10.)(18.&40.+1.))(24.$3?.(42.(18.&40.+1.))))P,A1.VK,R11.(36.$12.(37.(38.$39.R14.(18.&40.+>11:8.)R13.(3:.$12.))R12.)(43.(44.+1.R5.)(3;.(3<.&40.R11.(18.&40.+??.))(3=.R12.))))")
(* [comment removed for export] *).
  Proof.
    intros regs mem mo code tid wp0 rp0 wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hfd HK. destruct EC.
    apply (srzJ_getr_ext RSEGS (regs_tree regs) regs). { intros r. apply getr_regs_tree. }
    unfold regs_tree. rewrite ec_sp, ec_tp, ec_a0.
    change (mkst ?R ?pc ?M ?rom) with (MS R bvmap_empty pc (Z_to_bv 32 0) None M rom).
    ddestruct ec_atexit as (b & fin & jp & jq & jf & AT & ICB).
    eapply (rz_evtA_K RSEGS AL CS K K_halted K_mat); [exact HK | | ].
    { eapply (exit_frontA AL IMG ALWF CS CSOK) with (lo := (su - 320)%Z) (tid := tid) (recs := aglob_recs); try exact ASB; try exact GSB; try exact IMGCS;
        rewrite ?(unsigned_lit su) by lia; try eassumption; try reflexivity; try lia.
      - apply cov_rtc; assumption.
      - apply exit_got_rtc; assumption.
      - apply aglob_table_at; assumption.
      - apply aglob_recs_ok.
      - apply unreg_got_rtc; assumption.
      - apply unreg_consts_rtc; assumption.
      - apply flag_rtc; assumption.
      - apply mux_rtc; assumption.
      - intros z Hz. apply FRCS. lia. }
    cbn beta. intros ms' mo' POST HK' MM'. unfold exit_front_post in POST.
    ddestruct POST as (t0 & t1 & t2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & ST' & MP').
    rewrite ?(unsigned_lit su) in * by lia.
    pose proof (conj HK' MM' : KM K mo mo') as KM1.
    change (MS ?R _ ?pc _ _ ?M ?rom) with (mkst R pc M rom).
    replace (Z_to_bv 64 945304) with (0x0e6c98 : word) by (apply bv_eq; reflexivity).
    pose proof (stdio_globals_WEX _ _ MU ec_glob) as G'.
    pose proof (file_clean_WEX _ _ 0x0fa668%Z _ _ MU ltac:(lia) ltac:(lia) ec_in) as F0'.
    pose proof (file_clean_WEX _ _ 0x0fa488%Z _ _ MU ltac:(lia) ltac:(lia) ec_err) as F2'.
    pose proof (stdout_pendingA_WEX _ _ _ _ _ _ _ _ _ MU SP) as SP'.
    pose proof SP' as SPk. destruct SP' as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
    zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
    (* [comment removed for export] *)
    lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?R _ _ _) _) _ =>
      destruct (w3b1 R (restrict D m') (seg_rom RSEGS) (Z_to_bv 64 su) code wp0 rp0 wb wp)
        as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp) end.
    all: rewrite ?(unsigned_lit su) by lia.
    all: try (unfold mkR; norm_getr; first [reflexivity | f_equal; lia]).
    all: try lia.
    2:{ apply stdio_globals_restrict. exact G'. }
    2:{ apply file_clean_restrict; [lia|lia|exact F0']. }
    2:{ eapply stdout_dirty_hdr_restrict. exact SPk. }
    { rres ltac:(eapply stk_wmono_store_ok; [exact ec_stk | exact WM | lia | cbn; lia]). }
    unfold mem_w3a in RUN3. rewrite ?(unsigned_lit su) in RUN3 by lia. rewrite ?(unsigned_lit su) in R3sp by lia.
    rrunK RUN3 KM1 KM2.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x0e6d48) with (0x0e6d48 : word) in R3ra by (apply bv_eq; reflexivity).
    unfold W. rewrite <- (app_nil_r pending).
    set (mem3 := wbytes (wbytes (wbytes (wbytes m' (Z_to_bv 64 (su - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x0e1214)))
                   (Z_to_bv 64 (su - 32)) (word_to_le_bytes 8 code)) (Z_to_bv 64 (su - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x0e6ca8)))
                   (Z_to_bv 64 (su - 48)) (word_to_le_bytes 8 code)).
    assert (FRCS32 : forall z, (su - 32 - 112 <= z < su - 32)%Z -> CS z) by (intros z Hz; apply FRCS; lia).
    eapply (ref_stdio_writeA AL CS K IMG K_halted K_mat K_vmonly (su - 32)%Z ltac:(lia) ltac:(lia) FRCS32
              regs3 mem3 mo0 0x0fa578 wb wp 1 (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x0e6d48 : word) pending []);
      [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
      | subst mem3; store_ok_peel; eapply stk_wmono_store_ok; [exact ec_stk | exact WM | lia | cbn; lia]
      | lia | lia
      | split; subst mem3; zaddr_goal; rdn_solve
      | split; subst mem3; rdn_solve
      | lia
      | destruct KM2 as [_ MMx]; unfold m_fds in *; destruct MMx as (Efd & _); rewrite Efd; exact Hfd
      | exact (KM_K _ _ _ KM2)
      | intros z Hz; right; right; pose proof IMG as IMG'; unfold asan_img_ok in IMG'; ddestruct IMG' as (_ & -> & -> & _); lia
      | u_norm; intros z Hz; lia
      | lia | lia | exact LEN
      | cbn [length]; u_norm; reflexivity
      | cbn [length]; lia                       (* [comment removed for export] *)
      | lia | u_norm; lia | u_norm; lia
      | lia | u_norm; lia                       (* [comment removed for export] *)
      | subst mem3; repeat rdn_peel1; exact BYTES
      | reflexivity
      | apply ret_ok_even; reflexivity
      | apply t_emit_has_nil
      | ].
    intros regs4 mem4 mo4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST4 HK4 MM4.
    pose proof (KM_step _ _ _ _ KM2 HK4 MM4) as KM4.
    rewrite R3s0 in Q8.
    pose proof F2' as F2''. ddestruct F2'' as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    (* [comment removed for export] *)
    pose proof G' as G''. ddestruct G'' as (Gnl & Gofl & Gin & Gout & Gerr).
    ddestruct (w3b2 regs4 (restrict D mem4) (seg_rom RSEGS) (Z_to_bv 64 su) code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp).
    all: rewrite ?(unsigned_lit su) by lia.
    1: exact Q2.
    1: exact Q8.
    1,2: lia.
    1,2,3,4,5: rres ltac:(eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST4); [subst mem3; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; rres ltac:(eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST4); [subst mem3; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    rewrite ?(unsigned_lit su) in R5sp by lia.
    rrunK RUN5 KM4 KM5.
    eapply srzJ_conseq; [ eapply rz_exit_atA; [exact F_ddbd0 | exact E_ddbd0 | exact (K_halted _ (KM_K _ _ _ KM5)) | left; exact R5a7 | exact R5a0] |].
    rewrite (mo_mat_fs _ _ (proj2 KM5)). apply t_eq_refl.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="AL CS IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly SUlo SUhi FRCS D"] Theorem ref_exitA : ltac2:(CDefT.buildp (gd_tbl_A_exit ()) "Pregs,(34.&5.(6.&40.))Pmem,P,(6.&40.)(7.(6.&8.))Pmo,$1>.Pcode,(6.&40.)Ppending,(4.(6.&8.))P,(45.Vsu,R5.R4.R3.R2.R1.)P,A1.VK,R4.(36.$12.(37.(38.$39.R7.(18.&40.+>11:8.)R6.(3:.$12.))R5.)(43.(44.+1.R3.)(3;.(3<.&40.R4.(18.&40.+??.))(3=.R5.))))")
(* [comment removed for export] *).
  Proof.
    (intros regs mem mo code pending dd_H; ddestruct dd_H as (tid & wp0 & rp0 & wp2 & rp2 & EC & CASES); intros HK).
    destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
    - eapply srzJ_conseq; [ | apply t_emit_nil_exit ].
      eapply ref_exit_cleanA; eassumption.
    - eapply ref_exit_flushA; eassumption.
  Qed.

  (* [comment removed for export] *)
  End Thm.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

