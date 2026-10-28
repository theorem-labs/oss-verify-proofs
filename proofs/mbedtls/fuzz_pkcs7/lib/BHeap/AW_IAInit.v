(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_IMemset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00e2b5412d6fab04 1 1 16 2 1 1 37 1 4 29 1 30 1 38 1 39 16P00f2ed2101489a17 0 4 0 1 38 1 48 1 49 1P01ee80e0b6588978 0 4 0 1 34 1 44 1 45 1P02a549420989badc 0 4 0 1 34 1 44 1 45 1P05c2fa5c1279155f 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16P05f7a584ac6d5e20 1 1 16 2 1 1 37 1 4 29 1 30 1 38 1 39 16P06871c5957c5d8b3 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16P073f786e5c26963a 0 4 0 1 28 1 36 1 37 1P0784831f743abbc1 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P078911d62ce6a796 0 4 0 1 28 1 36 1 37 1P0793b9d7a2ba7096 0 5 1 16 35 16 36 16 45 16 46 16P08807609fe0bd8b6 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P0963ea89bd753434 0 5 1 16 29 16 30 16 37 16 38 16P0ae02594dca4a3cf 0 4 0 1 28 1 36 1 37 1P0bcd47f02e32ecc5 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P0d41fb4d45947ee0 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16P0dfef4058ff015fa 0 4 0 1 38 1 48 1 49 1P0e3b5cbb58280594 0 5 0 16 39 16 40 16 49 16 50 16P10f358c1e1645737 0 4 0 1 28 1 36 1 37 1P119132251333cb92 0 4 0 1 34 1 44 1 45 1P11a003cdb02901e0 1 1 16 2 0 1 49 1 4 39 1 40 1 50 1 51 16P1244a4a272633eed 0 4 0 1 28 1 36 1 37 1P13ce5b25c872aac1 0 4 0 1 28 1 36 1 37 1P1566144b862cc864 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P15697bd1477a4e63 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P15b8df56a8dbd881 0 4 0 1 34 1 44 1 45 1P1faf533c445f0e5d 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16P20226601c031afb9 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P21cfd76630b986ea 0 4 0 1 34 1 44 1 45 1P2288c17a6427e734 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16P22b30954e82ef39c 0 4 0 1 28 1 36 1 37 1P230b0b4cbf7f9523 1 1 16 2 1 1 37 1 4 29 1 30 1 38 1 39 16P2376ffcabadef1dc 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16P2410687483f076d2 0 4 0 1 34 1 44 1 45 1P24626c5393dbb4b0 0 5 1 16 35 16 36 16 45 16 46 16P254347da5dd46d51 0 5 1 16 29 16 30 16 37 16 38 16P258403e3fb15a805 0 4 0 1 28 1 36 1 37 1P25b64b98ba88255a 0 4 0 1 38 1 48 1 49 1P26a39cefe36a34f1 1 1 16 2 0 1 47 1 4 37 1 38 1 48 1 49 16P26cfa1c456f5f9e1 0 4 0 1 28 1 36 1 37 1P26e05e8ec8d209a4 0 4 0 1 38 1 48 1 49 1P2763f5c619a8326b 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P28b67ff530c98062 1 1 16 2 0 1 49 1 4 39 1 40 1 50 1 51 16P291a3f1f1ebb322f 0 4 0 1 28 1 36 1 37 1P292a904774d69222 0 4 0 1 28 1 36 1 37 1P295ab9f89e1cbcfc 0 4 0 1 34 1 44 1 45 1P298ea138dbbf6334 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P2ac944697ad00c56 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P2b7b9edcecc5bc33 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P2c708b6c5b55a57b 0 4 0 1 34 1 44 1 45 1P2db642f07faf2746 1 1 16 2 1 1 37 1 4 29 1 30 1 38 1 39 16P2dbdc07c1ac47e08 0 4 0 1 28 1 36 1 37 1P2ddf7ee293588d85 1 1 16 2 1 1 37 1 4 29 1 30 1 38 1 39 16P2eb6be8c0107591b 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P2ecc2a47d8097e4b 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P2ed7c83657dd36d1 0 4 0 1 38 1 48 1 49 1P2f1bb538b6c99771 0 4 0 1 34 1 44 1 45 1P314c3239a1282c27 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P31c6c6bb9f5c178e 0 4 0 1 34 1 44 1 45 1P327c48bde9031672 0 4 0 1 38 1 48 1 49 1P3440b326f5e152bb 1 1 16 2 0 1 49 1 4 39 1 40 1 50 1 51 16P34997bf3fa788511 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16P34f3a0c0df365892 0 4 0 1 28 1 36 1 37 1P350646493b0f2a03 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16P359587167c60cf0b 0 4 0 1 34 1 44 1 45 1P3626fc6cb23309ff 0 4 0 1 34 1 44 1 45 1P382548f88a93df07 0 4 0 1 34 1 44 1 45 1P38402f5b0f748b4f 0 4 0 1 34 1 44 1 45 1P38bd802020716b3d 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16P39302f1023967ede 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16P3a7457f0fe5ad4a0 0 4 0 1 34 1 44 1 45 1P3ac516c3c23db649 0 4 0 1 28 1 36 1 37 1P3b474f84c136c95f 1 1 16 2 1 1 37 1 4 29 1 30 1 38 1 39 16P3bd2473a8f9a1194 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16P3ceb14856e214469 0 4 0 1 28 1 36 1 37 1P3cefe006c457ae8c 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P3d741c83dec38c36 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P3eaa9b1981de479e 1 1 16 2 1 1 37 1 4 29 1 30 1 38 1 39 16P3ec33a9f14924ed4 1 1 16 2 1 1 37 1 4 29 1 30 1 38 1 39 16P3fb65a39c7b7d679 1 2 16 2 0 1 46 1 16 2 1 1 45 1 2 47 1 48 1P3fe3e98cf34c2c51 1 1 16 2 1 1 45 1 4 35 1 36 1 46 1 47 16N02d4eebf90a897dcN2d253c4bdcc9adabN31b62e5a9bd8665eN39cea62b75cb441dN3c8befde9324b904"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_IAInit () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA_INIT"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.option"; "ARUN_1.IAInit.ia_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.IAInit.ia_post"; "ARUN_1.IAInit.ia_W"; "ARUN_1.A_INTERNAL_ALLOCATOR"].

Section ARUN_1. Context {hAR : arun}.
Definition A_INTERNAL_ALLOCATOR : Z := 0x74e44.  (* [comment removed for export] *)

Section IAInit.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac bytes_eq := vm_compute; repeat (first [reflexivity | apply f_equal2; [apply bv_eq; vm_compute; reflexivity|] ]).

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition ia_W (lo SP : Z) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AW_IAInit ()) "(0.(1.$2.$2.)(3.$2.$2.O2.O1.)(0.(1.$2.$2.)(3.$2.$2.$4.(5.$4.+4.))(0.(1.$2.$2.)(3.$2.$2.$6.(5.$6.+1.))(0.(1.$2.$2.)(3.$2.$2.(5.$6.+8.)(5.(5.$6.+8.)+40000.))(0.(1.$2.$2.)(3.$2.$2.(5.$6.+40040.)(5.(5.$6.+40040.)+=80.))(0.(1.$2.$2.)(3.$2.$2.(5.$6.+40=<0.)(5.(5.$6.+40=<0.)+40248.))(0.(1.$2.$2.)(3.$2.$2.(5.$6.+81008.)(5.(5.$6.+81008.)+28.))(7.(1.$2.$2.)))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition ia_cells (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_IAInit ()) "(8.(9.$:.O1.$4.(0.$;.(<.(=.&8.+1.))(0.$;.(<.(=.&8.=))(0.$;.(>.(=.&40.=))(7.$;.)))))(8.(9.$:.O1.$6.(0.$;.(<.(=.&8.=))(7.$;.)))(8.(9.$:.O1.(5.$6.+8.)(0.$;.(?.(10.+40000.)(11.(12.&8.)(=.&8.=)(10.+40000.)))(7.$;.)))(8.(13.(14.$;.)Lcs,(14.$;.)(8.(9.$:.O1.(5.$6.+40040.)R1.)(15.$2.(16.(17.R1.))+=80.)))(8.(9.$:.O1.(5.$6.+40=<0.)(0.$;.(18.(=.&40.+1000.))(0.$;.(18.(=.&40.(5.$6.+40==0.)))(7.$;.))))(8.(13.(14.$;.)Lcs,(14.$;.)(8.(9.$:.O1.(5.$6.+40==0.)R1.)(15.$2.(16.(17.R1.))(19.+40248.+10.))))(13.(14.$;.)Lcs,(14.$;.)(8.(9.$:.O1.(5.$6.+81008.)R1.)(15.$1:.(17.R1.)#28.)))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L18670367311.27L18671441103.27L18928664212.27L33217704527.27L37506855281.10L45475402533.27L4627565775.27 L50604877861.27L51746356389.27L51853030192.27L54067406127.27L60759087782.27L61297945551.27L63269508979.2700000@00P00`01001B01U01e02802H02X02h03803H03XS3cs23cs63cs72S7S3cs23cs63cs72S7S3cs23cs63cs72S7S3cs23cs63cs72S7S1u1v2D11a1n2Ha2HnS3cs22S43cs63cs72S7S3cs23cs63cs72S7S3cs23cs62S63cs72S7S3cs23cs63cs72S7S3cs23cs63cs72S7S3cs23cs63cs72S7S3cs23cs63cs72S7S3cs23cs63cs72S7S3cs23cs63cs72S7". (* [comment removed for export] *)
  Lemma ia_cells_transport : ltac2:(CDefT.buildp (gd_tbl_AW_IAInit ()) "PW,(14.$1;.)Pm,P,(12.&40.)(1<.(12.&8.))Pm',P,(12.&40.)(1<.(12.&8.))P,(1=.R2.)P,(1>.R4.R3.R2.)P,(1?.$:.R4.R3.)P,(20.R6.$6.+81030.)P,(20.R7.$4.+4.)(1=.R6.)")
(* [comment removed for export] *).
  Proof.
    intros W m m' (H1 & H2 & H3 & (cs2 & H4 & S4) & H5 & (cs6 & H6 & S6) & (cs7 & H7 & S7)) MU WM D1 D2.
    assert (DJ : forall a n, A_IA <= a -> a + n <= A_IA + 0x81030 -> disjoint_from W a n).
    { intros a n Ha Hn. clear -D1 Ha Hn. induction W as [|[u v] W IH]; cbn in *; [exact I|]. destruct D1 as [D1 DR]. split; [lia| apply IH; exact DR]. }
    unfold ia_cells. unfold A_IA, A_IA_INIT in *.
    split. { eapply rw_cells_transport; [exact H1| exact MU| exact WM| exact D2]. }
    split. { eapply rw_cells_transport; [exact H2| exact MU| exact WM| apply DJ; cbn; lia]. }
    split. { eapply rw_cells_transport; [exact H3| exact MU| exact WM| apply DJ; cbn [cells_size csize]; rewrite ?Nat.add_0_r, ?Z2Nat.id; lia]. }
    split. { exists cs2. split; [|exact S4]. eapply rw_cells_transport; [exact H4| exact MU| exact WM| apply DJ; lia]. }
    split. { eapply rw_cells_transport; [exact H5| exact MU| exact WM| apply DJ; cbn; lia]. }
    split. { exists cs6. split; [|exact S6]. eapply rw_cells_transport; [exact H6| exact MU| exact WM| apply DJ; lia]. }
    exists cs7. split; [|exact S7]. eapply rw_cells_transport; [exact H7| exact MU| exact WM| apply DJ; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ia_cells_open : ltac2:(CDefT.buildp (gd_tbl_AW_IAInit ()) "Pm,P,(12.&40.)(1<.(12.&8.))P,(1=.R1.)(13.(14.$;.)Lcs2,(14.$;.)(13.(14.$;.)Lcs4,(14.$;.)(13.(14.$;.)Lcs5,(14.$;.)(8.(9.$:.R5.$4.(0.$;.(<.(=.&8.+1.))(0.$;.(<.(=.&8.=))(0.$;.(>.(=.&40.=))(7.$;.)))))(8.(9.$:.R5.$6.(0.$;.(<.(=.&8.=))(7.$;.)))(8.(9.$:.R5.(5.$6.+8.)(0.$;.(?.(10.+40000.)(11.(12.&8.)(=.&8.=)(10.+40000.)))(7.$;.)))(8.(9.$:.R5.(5.$6.+40040.)R3.)(8.(15.$2.(16.(17.R3.))+=80.)(8.(9.$:.R5.(5.$6.+40=<0.)(0.$;.(18.(=.&40.+1000.))(0.$;.(18.(=.&40.(5.$6.+40==0.)))(7.$;.))))(8.(9.$:.R5.(5.$6.+40==0.)R2.)(8.(15.$2.(16.(17.R2.))(19.+40248.+10.))(8.(9.$:.R5.(5.$6.+81008.)R1.)(15.$2.(16.(17.R1.))+28.)))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros m (H1 & H2 & H3 & (cs2 & H4 & S4) & H5 & (cs6 & H6 & S6) & (cs7 & H7 & S7)).
    exists cs2, cs6, cs7. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact S4|].
    split; [exact H5|]. split; [exact H6|]. split; [exact S6|]. split; [exact H7|]. rewrite S7. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition ia_post (ra : word) (SP : Z) (gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (W : list (Z * Z)) (lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_IAInit ()) "Lms',$21.(13.(12.&40.)La1,(12.&40.)(13.(12.&40.)La2,(12.&40.)(13.(12.&40.)La3,(12.&40.)(13.(12.&40.)La4,(12.&40.)(13.(12.&40.)La5,(12.&40.)(13.(12.&40.)La6,(12.&40.)(13.P,(12.&40.)(1<.(12.&8.))Lm',P,(12.&40.)(1<.(12.&8.))(8.(15.$21.R8.(22.(23.O1=.(=.&40.O1<.)O1;.O1:.O19.O18.O17.O16.O15.(=.&40.$6.)R7.R6.R5.R4.R3.R2.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.)O5.(24.O1=.)O4.(25.(12.&40.))R1.(26.$:.)))(8.(1>.O3.O1.R1.)(8.(1?.$:.O1.R1.)(8.(27.$:.R1.)(8.(1=.R1.)(28.$:.R1.O2.O1<.)))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac ia_hideZ := repeat match goal with H : rw_cells _ _ _ [CB (Z.to_nat _) (repeat _ _)] |- _ => lx_hide H end.
  Ltac ia_unhideZ := repeat match goal with H : id (rw_cells _ _ _ [CB (Z.to_nat _) (repeat _ _)]) |- _ => lx_unhide1 H end.
  Ltac ia_run m W pl :=
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mp _) =>
      let MUr := fresh "MUr" in let WMr := fresh "WMr" in
      pose proof (munch_refl W mp) as MUr;
      pose proof (wmono_refl asegs mp) as WMr;
      ia_hideZ; lx_run pl; ia_unhideZ;
      lazymatch goal with MUl : munch _ mp ?mx, WMl : wmono _ mp ?mx' |- _ =>
        transport_after_call asegs mp mx MUl WMl; lx_acc_run m mp end end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "02;0@L11572981577.0  L13322586518.107L13324683698.95 L13422859893.95 L13424957009.107L14286730093.95 L14288827209.107L14330515701.83 L15122598696.2  L15461411025.107L15463508213.95 L15612028680.86 L17110762578.127L1733952373.95  L1736049489.107 L19448231916.87 L21980516378.0  L2198896849.107 L2200994037.95  L22140756587.2  L22704466501.166L22706564033.129L22706564033.97 L22706564936.109L23311785748.164L2354577745.107 L2356674933.95  L23603513570.83 L24564465360.93 L24568579564.230L24570676206.162L24570676579.125L24570676846.105L24572773100.85 L25261323219.164L28262370540.87 L28551966801.107L28554063989.95 L28690141127.87 L29590434037.83 L30339722322.127L31134854380.87 L31425267717.162L31425269125.105L31425269125.106L31425269384.125L31425269384.126L31427365127.85 L31435699515.93 L31439949319.230L32663140042.127L3456301766.159 L35625402368.81 L35625403654.73 L35625403787.71 L35625403915.78 L35625404032.76 L35627501063.85 L36018531482.0  L36850670828.87 L37012058348.87 L38330469153.0  L38820635861.0  L39108778451.164L39750072511.83 L4021271762.127 L40767932181.127L41122746630.126L41122746891.106L41122748299.163L41133173429.94 L41137426825.231L42716553077.95 L42718650193.107L42760359962.0  L44067157458.127L44694064082.127L45313116626.127L46022314220.87 L4639797970.127 L46756659669.0  L48548665045.0  L49188069067.164L49826522313.0  L49861101673.83 L50581482732.87 L50978525769.0  L51874528457.0  L53137630291.164L53520213848.83 L55588686165.0  L55977486197.95 L55979583313.107L56089870193.85 L5672554629.162 L5672555781.105 L5672556040.125 L5674652039.85  L5683113403.93  L5687236231.231 L57177720455.85 L57179816200.125L57179816453.105L57179817861.162L57186187963.93 L57190302087.230L57636692309.0  L58856235016.125L58856235781.105L58856236677.162L58858334087.85 L58866785211.93 L58870915207.230L6106346273.0   L63183256717.94 L63187371953.231L63193661875.163L63193662515.106L63193663294.126L64664554195.164L65995878322.84 L6639002489.84  L66399587411.164L66522741506.162L66522742159.125L66522742402.105L66524838400.85 L66533279292.93 L66537422080.230L66556976263.85 L66559072261.105L66559073032.125L66559073669.163L66565431483.93 L66569558919.230L66846182867.164L8190532385.0   L8453145377.0   L978298522.0    00000100R01301K01c02H02m03J03S03k04G04h05@05X06006_06`07807P07W08?08`09A09b0:I0:a0;90;:0;;0;<0;=0;>0;?0;@0;^0<I0<a0==0>10>F0>^0?E0?f0@K0@l0AM0An0BW0C@0Cg0DL0Dd0ED0Ed0FD0Fd0GD0Gj0Gk0HR0I90I:0I;0IY0J60JN0Jo0K00K10K20K30K40KP0Kh0Ki0LA0LY0M10MX0N00N10N20N]0N^0O30O^0O_0O`0P>0P\0P]0Q50QM0Qh0RM0S20SW0T<0Ta0UH0Ui0VJ0Vk0WL0Wm0XT0XU0Y60YW0Z80ZY0[:0[a0[b0[c0[d0[e0[f0[g0\E0\n0]F0]d0]e0]f0]g0]h0]i0]j0^O0_40_Y0`:0`_0aF0ad0ae0af0agSS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs5S3hAR2SP2lo3cs13cs23cs43cs55LOIMG3SPLS3hAR2SP2lo3cs13cs23cs43cs55LOIMG3SPLS3hAR2AL3cs13cs23cs43cs54IMG'S3cs43SZ4S3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs53SZ1S3hAR2SP3cs13cs23cs43cs52HB5Ha_stS3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs53SZ52HB5Ha_st5Hl_st3SZ1SS3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs5S2cs2HsS3hAR2SP2lo3cs13cs23cs43cs52p02p12x73H14S3hAR2SP2lo3cs13cs23cs43cs52x52H0S3hAR2SP2lo3cs13cs23cs43cs52x12H0S3hAR2SP2lo3cs13cs23cs43cs52x32H7S3hAR2SP2lo3cs13cs23cs43cs52p02p15LOIMGS3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs5FFFFFFFS3hAR2SP3cs13cs23cs43cs52p02p1S3hAR2SP3cs13cs23cs43cs53SZ22HB5Ha_st5Hl_stS3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs53SZ4S3hAR2SP2lo3cs13cs23cs43cs55LOIMG3SPL2HB5Ha_st5Hl_stS3hAR3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs52HB5Ha_st5Hl_stS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs53SZ15LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs53SZ55LOIMG3SZ1S3hAR2SP2lo3cs13cs23cs43cs53SZ55LOIMG3SZ1S3hAR2SP2lo3cs13cs23cs43cs52p02p15LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMG3SPLS3hAR2SP3cs13cs23cs43cs5S3hAR2SP2lo3cs13cs23cs43cs51y2HyS3hAR2SP2lo3cs13cs23cs43cs51y2HyS3hAR2SP2lo3cs13cs23cs43cs51y2HyS3hAR2SP2lo3cs13cs23cs43cs51y2HyS3hAR2SP2lo3cs13cs23cs43cs51y2HyS3hAR2SP2lo3cs13cs23cs43cs52p02p11y2HySS3hAR2SP3cs13cs23cs43cs52HB5Ha_st5Hl_stS3hAR2SP3cs13cs23cs43cs52HB5Ha_st5Hl_stSSS3hAR2SP3cs13cs23cs43cs52p02p1S3hAR2AL3cs13cs23cs43cs54IMG'S3hAR2SP3cs13cs23cs43cs5S3hAR2SP2lo3cs13cs23cs43cs55LOIMGFFFFFS3hAR2SP3cs13cs23cs43cs53SZ2S3hAR2SP3cs13cs23cs43cs5SS3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs52HB5Ha_st5Hl_stS3hAR2SP3cs13cs23cs43cs5SSS3hAR2SP2lo3cs13cs23cs43cs52p02p15LOIMG3SPLSS3hAR3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs53SZ42HB5Ha_st5Hl_stSSS3hAR2SP3cs13cs23cs43cs52p02p1S3hAR2AL3cs13cs23cs43cs55ALWF'SS3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs52HBS3hAR2SP2lo3cs13cs23cs43cs53SZ45LOIMGS3hAR2SP2lo3cs13cs23cs43cs53SZ45LOIMGS3hAR2SP2lo3cs13cs23cs43cs53SZ45LOIMGS3hAR2SP2lo3cs13cs23cs43cs53SZ45LOIMGS3hAR2SP2lo3cs13cs23cs43cs53SZ45LOIMGS3hAR2SP2lo3cs13cs23cs43cs52p02p15LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs52p02p15LOIMGSS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs52p02p15LOIMGSFFFFFS3hAR2SP3cs13cs23cs43cs52p02p1S3hAR2SP2lo3cs13cs23cs43cs55LOIMG3SPL3SPAS3hAR2SP3cs13cs23cs43cs5S3hAR2SP3cs13cs23cs43cs52p02p1FFFFFFS3hAR2SP2lo3cs13cs23cs43cs53SZ25LOIMGS3hAR2SP2lo3cs13cs23cs43cs53SZ25LOIMGS3hAR2SP2lo3cs13cs23cs43cs53SZ25LOIMGS3hAR2SP2lo3cs13cs23cs43cs55LOIMGS3hAR2SP2lo3cs13cs23cs43cs53SZ25LOIMGS3hAR2SP2lo3cs13cs23cs43cs52p02p15LOIMGS3hAR2SP3cs13cs23cs43cs52p02p1SSS". (* [comment removed for export] *)
  Lemma ia_init_first : ltac2:(CDefT.buildp (gd_tbl_AW_IAInit ()) "Pra,(12.&40.)Pgp,(12.&40.)Ptp,(12.&40.)Pt0,(12.&40.)Pt1,(12.&40.)Pt2,(12.&40.)Ps0,(12.&40.)Ps1,(12.&40.)Pa0,(12.&40.)Pa1,(12.&40.)Pa2,(12.&40.)Pa3,(12.&40.)Pa4,(12.&40.)Pa5,(12.&40.)Pa6,(12.&40.)Pa7,(12.&40.)Ps2,(12.&40.)Ps3,(12.&40.)Ps4,(12.&40.)Ps5,(12.&40.)Ps6,(12.&40.)Ps7,(12.&40.)Ps8,(12.&40.)Ps9,(12.&40.)Ps10,(12.&40.)Ps11,(12.&40.)Pt3,(12.&40.)Pt4,(12.&40.)Pt5,(12.&40.)Pt6,(12.&40.)PSP,$2.PF,(29.&5.(12.&40.))Pfc,(12.&20.)Pm,P,(12.&40.)(1<.(12.&8.))Plo,$2.Pb0,(12.&8.)Pcs1,(14.$;.)Pcs2,(14.$;.)Pcs4,(14.$;.)Pcs5,(14.$;.)Pp0,(12.&40.)Pp1,(12.&40.)P,(9.$:.R9.$4.(0.$;.(<.(=.&8.=))(0.$;.(<.(=.&8.=))(0.$;.(>.(=.&40.=))(7.$;.)))))P,(9.$:.R:.$6.(0.$;.(<.R8.)(7.$;.)))P,(9.$:.R;.(5.$6.+8.)R8.)P,(15.$2.(16.(17.R9.))+40000.)P,(9.$:.R=.(5.$6.+40040.)R9.)P,(15.$2.(16.(17.R:.))+=80.)P,(9.$:.R?.(5.$6.+40=<0.)(0.$;.(18.R8.)(0.$;.(18.R7.)(7.$;.))))P,(9.$:.R10.(5.$6.+40==0.)R;.)P,(15.$2.(16.(17.R<.))(19.+40248.+10.))P,(9.$:.R12.(5.$6.+81008.)R<.)P,(15.$2.(16.(17.R=.))+28.)P,(2:.$:.R14.$2;.(0.$;.(18.(=.&40.$2<.))(7.$;.)))P,(2:.$:.R15.$2<.(0.$;.(18.(=.&40.+1000.))(7.$;.)))P,(28.$:.R16.R15.R19.)P,(2=.+65?000.R16.)P,(2=.R17.(19.R1;.+30.))P,(2=.R1<.(2>.+2.+3?.))P,(15.$2.(2?.R1=.+10.)=)P,(30.VCS,R1:.(19.R1>.R1:.))P,(27.$:.R1<.)(31.$:.VAL,VCS,(32.R3>.R20.R3=.R3<.R3;.R3:.R39.R38.R37.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1?.R1>.(33.R1<.R20.)R1<.R1=.)(22.(23.R3>.(=.&40.R20.)R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R1?.(=.&40.$34.)R1>.(25.(12.&40.))R1=.(26.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m lo b0 cs1 cs2 cs4 cs5 p0 p1
      IAW IA0 IA1 SZ1 IA2 SZ2 IA3 IA4 SZ4 IA5 SZ5 GOT PGS ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold ia_post, ia_W. unfold A_INTERNAL_ALLOCATOR, A_IA, A_IA_INIT, A_GOT_PAGESZ, A_PAGESZ_CELL in *.
    change (1092608 + 8) with 1092616 in *. change (1092608 + 262208) with 1354816 in *.
    change (1092608 + 265664) with 1358272 in *. change (1092608 + 265680) with 1358288 in *.
    change (1092608 + 528392) with 1621000 in *.
    change (1676424 + 4) with 1676428 in *. change (1092608 + 1) with 1092609 in *.
    change (1092616 + 262144) with 1354760 in *. change (1354816 + 3456) with 1358272 in *.
    change (1358272 + 262728) with 1621000 in *. change (1621000 + 40) with 1621040 in *.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, SP); (1676424, 1676428); (1092608, 1092609); (1092616, 1354760);
                            (1354816, 1358272); (1358272, 1621000); (1621000, 1621040)] m) as MUA.
    pose proof (wmono_refl asegs m) as WMA. lx_hide MUA. lx_hide WMA.
    (* [comment removed for export] *)
    lx_c1_norm. lx_aceil.
    (* [comment removed for export] *)
    ia_run m [(lo, SP); (1676424, 1676428); (1092608, 1092609); (1358272, 1358288)] (PLAN [0x74e90] [] 40%N).
    (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mp _) =>
      match goal with H : rw_cells _ mp 1676424 _ |- _ => apply (rw_cells_reshape asegs mp 1676424 _ [C4 (Z_to_bv 64 0)]) in H; [| cbn; tauto | vm_compute; reflexivity] end;
      pose proof (munch_refl [(lo, SP); (1676424, 1676428); (1092608, 1092609); (1092616, 1354760); (1354816, 1358272); (1358272, 1621000); (1621000, 1621040)] mp) as MUi;
      pose proof (wmono_refl asegs mp) as WMi end.
    zstep. rewrite (sx32_small 0) by lia.
    do 6 zstep.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with H : rw_cells _ mx 1676424 [C4 _] |- _ =>
        apply (rw_cells_reshape asegs mx 1676424 _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (Z_to_bv 64 0)]) in H; [| cbn; tauto | bytes_eq] end;
      lazymatch type of MUi with munch _ ?mp _ => lx_acc_run m mp end end.
    (* [comment removed for export] *)
    ia_run m [(lo, SP); (1676424, 1676428); (1092608, 1092609); (1358272, 1358288)] (PLAN [0x7aa58] [] 40%N).
    (* [comment removed for export] *)
    match goal with M : id (munch _ m _), Wm : id (wmono _ m _) |- _ => lx_unhide1 M; lx_unhide1 Wm end.
    callxA (eapply (imemset_spec AL IMG ALWF CS CSOK 40 1621000); [clear; lia| exact IA5| exact SZ5| clear; lia| clear; lia| assumption]).
    match goal with Z : izeros ?mx 1621000 40 |- _ => apply izeros_e in Z end.
    match goal with M : munch _ m ?mx, Wm : wmono _ m ?mx |- _ => lx_hide M; lx_hide Wm end.
    (* [comment removed for export] *)
    ia_run m [(lo, SP); (1676424, 1676428); (1092608, 1092609); (1358272, 1358288)] (PLAN [0x7aa58] [] 20%N).
    match goal with M : id (munch _ m _), Wm : id (wmono _ m _) |- _ => lx_unhide1 M; lx_unhide1 Wm end.
    callxA (eapply (imemset_spec AL IMG ALWF CS CSOK 262144 1092616); [clear; lia| exact IA1| exact SZ1| clear; lia| clear; lia| assumption]).
    match goal with Z : izeros ?mx 1092616 262144 |- _ => apply izeros_e in Z end.
    match goal with M : munch _ m ?mx, Wm : wmono _ m ?mx |- _ => lx_hide M; lx_hide Wm end.
    (* [comment removed for export] *)
    ia_run m [(lo, SP); (1676424, 1676428); (1092608, 1092609); (1358272, 1358288)] (PLAN [0x7aa58] [] 20%N).
    match goal with M : id (munch _ m _), Wm : id (wmono _ m _) |- _ => lx_unhide1 M; lx_unhide1 Wm end.
    callxA (eapply (imemset_spec AL IMG ALWF CS CSOK 3456 1354816); [clear; lia| exact IA2| exact SZ2| clear; lia| clear; lia| assumption]).
    match goal with Z : izeros ?mx 1354816 3456 |- _ => apply izeros_e in Z end.
    match goal with M : munch _ m ?mx, Wm : wmono _ m ?mx |- _ => lx_hide M; lx_hide Wm end.
    (* [comment removed for export] *)
    ia_run m [(lo, SP); (1676424, 1676428); (1092608, 1092609); (1358272, 1358288)] (PLAN [0x7aa58] [] 20%N).
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      match goal with IA3' : rw_cells _ mc 1358272 [C8 _; C8 _] |- _ => chunk_join IA3' IA4 IA34 end end.
    assert (SZ34 : Z.of_nat (cells_size ([C8 p0; C8 p1] ++ cs4)) = 262728).
    { rewrite cells_size_app, Nat2Z.inj_add. cbn [cells_size csize Nat.add]. clear -SZ4. lia. }
    cbn [app] in SZ34. cbn [app] in IA34.
    match goal with M : id (munch _ m _), Wm : id (wmono _ m _) |- _ => lx_unhide1 M; lx_unhide1 Wm end.
    callxA (eapply (imemset_spec AL IMG ALWF CS CSOK 262728 1358272); [clear; lia| exact IA34| exact SZ34| clear; lia| clear; lia| assumption]).
    match goal with Z : izeros ?mx 1358272 262728 |- _ => destruct (izeros_split16 _ _ _ Z ltac:(clear; lia)) as [IA3x ZB4]; clear Z; apply izeros_e in ZB4 end.
    change (1358272 + 16) with 1358288 in ZB4. change (262728 - 16) with 262712 in ZB4.
    match goal with M : munch _ m ?mx, Wm : wmono _ m ?mx |- _ => lx_hide M; lx_hide Wm end.
    (* [comment removed for export] *)
    ia_run m [(lo, SP); (1676424, 1676428); (1092608, 1092609); (1358272, 1358288)] (PLAN [] [] 40%N).
    lx_unhide. apply evtA_done. lx_exs.
    lx_ands; [> lx_mseq | lx_close | lx_close | lx_close | | lx_close ].
    unfold ia_cells, A_IA, A_IA_INIT.
    change (1092608 + 8) with 1092616. change (1092608 + 262208) with 1354816.
    change (1092608 + 265664) with 1358272. change (1092608 + 265680) with 1358288. change (1092608 + 528392) with 1621000.
    lx_ands;
      [ lx_close | lx_close | lx_close
      | eapply izeros_ex; [clear; lia|]; apply izeros_i; match goal with K : rw_cells _ _ 1354816 _ |- _ => exact K end
      | lx_close
      | change (262728 - 16) with 262712; eapply izeros_ex; [clear; lia|]; apply izeros_i; match goal with K : rw_cells _ _ 1358288 _ |- _ => exact K end
      | match goal with K : rw_cells _ _ 1621000 _ |- _ =>
          destruct (izeros_ex _ 1621000 40 ltac:(clear; lia) K) as (cs & Hc & Hs); exists cs; split; [exact Hc| clear -Hs; lia] end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L21668619708.73L35080768828.73L35389770812.73L61812694883.73L63118266428.73L64048592643.2 L66524839053.73L7644510268.73 L8423177660.73 00000Q01201O01P02102:02;02X035S3hAR2SP2lo3cs23cs43cs53SZ55LOIMGS3hAR2SP2lo3cs23cs43cs53SZ45LOIMGS3hAR2SP2lo3cs23cs43cs55LOIMGFS3hAR2SP2lo3cs23cs43cs53SZ25LOIMGS3cs53SZ5FS3hAR2SP2lo3cs23cs43cs55LOIMGS3hAR2SP2lo3cs23cs43cs55LOIMG". (* [comment removed for export] *)
  Lemma ia_init_again : ltac2:(CDefT.buildp (gd_tbl_AW_IAInit ()) "Pra,(12.&40.)Pgp,(12.&40.)Ptp,(12.&40.)Pt0,(12.&40.)Pt1,(12.&40.)Pt2,(12.&40.)Ps0,(12.&40.)Ps1,(12.&40.)Pa0,(12.&40.)Pa1,(12.&40.)Pa2,(12.&40.)Pa3,(12.&40.)Pa4,(12.&40.)Pa5,(12.&40.)Pa6,(12.&40.)Pa7,(12.&40.)Ps2,(12.&40.)Ps3,(12.&40.)Ps4,(12.&40.)Ps5,(12.&40.)Ps6,(12.&40.)Ps7,(12.&40.)Ps8,(12.&40.)Ps9,(12.&40.)Ps10,(12.&40.)Ps11,(12.&40.)Pt3,(12.&40.)Pt4,(12.&40.)Pt5,(12.&40.)Pt6,(12.&40.)PSP,$2.PF,(29.&5.(12.&40.))Pfc,(12.&20.)Pm,P,(12.&40.)(1<.(12.&8.))Plo,$2.Pcs2,(14.$;.)Pcs4,(14.$;.)Pcs5,(14.$;.)P,(9.$:.R5.$4.(0.$;.(<.(=.&8.+1.))(0.$;.(<.(=.&8.=))(0.$;.(>.(=.&40.=))(7.$;.)))))P,(9.$:.R6.$6.(0.$;.(<.(=.&8.=))(7.$;.)))P,(9.$:.R7.(5.$6.+8.)(0.$;.(?.(10.+40000.)(11.(12.&8.)(=.&8.=)(10.+40000.)))(7.$;.)))P,(9.$:.R8.(5.$6.+40040.)R6.)P,(15.$2.(16.(17.R7.))+=80.)P,(9.$:.R:.(5.$6.+40=<0.)(0.$;.(18.(=.&40.+1000.))(0.$;.(18.(=.&40.(5.$6.+40==0.)))(7.$;.))))P,(9.$:.R;.(5.$6.+40==0.)R8.)P,(15.$2.(16.(17.R9.))(19.+40248.+10.))P,(9.$:.R=.(5.$6.+81008.)R9.)P,(15.$2.(16.(17.R:.))+28.)P,(28.$:.R?.R>.R12.)P,(2=.+65?000.R?.)P,(2=.R10.(19.R14.+30.))P,(2=.R15.(2>.+2.+3?.))P,(15.$2.(2?.R16.+10.)=)P,(30.VCS,R13.(19.R17.R13.))P,(27.$:.R15.)(31.$:.VAL,VCS,(32.R37.R19.R36.R35.R34.R33.R32.R31.R30.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R18.R17.(33.R15.R19.)R15.R16.)(22.(23.R37.(=.&40.R19.)R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R18.(=.&40.$34.)R17.(25.(12.&40.))R16.(26.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m lo cs2 cs4 cs5
      IAW IA0 IA1 IA2 SZ2 IA3 IA4 SZ4 IA5 SZ5 ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold ia_post, ia_W. unfold A_INTERNAL_ALLOCATOR, A_IA, A_IA_INIT in *.
    change (1092608 + 8) with 1092616 in *. change (1092608 + 262208) with 1354816 in *.
    change (1092608 + 265664) with 1358272 in *. change (1092608 + 265680) with 1358288 in *.
    change (1092608 + 528392) with 1621000 in *.
    change (1676424 + 4) with 1676428 in *. change (1092608 + 1) with 1092609 in *.
    change (1092616 + 262144) with 1354760 in *. change (1354816 + 3456) with 1358272 in *.
    change (1358272 + 262728) with 1621000 in *. change (1621000 + 40) with 1621040 in *.
    lx_hide IA1. pose proof (munch_refl [(lo, SP)] m) as MUf. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N). lx_unhide.
    lazymatch goal with MUl : munch _ m lxm, WMl : wmono _ m lxm |- _ => transport_after_call asegs m lxm MUl WMl end.
    apply evtA_done. lx_exs.
    lx_ands; [> lx_mseq | lx_munchx | lx_close | lx_close | | lx_close ].
    unfold ia_cells, A_IA, A_IA_INIT.
    change (1092608 + 8) with 1092616. change (1092608 + 262208) with 1354816.
    change (1092608 + 265664) with 1358272. change (1092608 + 265680) with 1358288. change (1092608 + 528392) with 1621000.
    lx_ands; [ lx_close | lx_close | lx_close
             | exists cs2; split; [lx_close| exact SZ2]
             | lx_close
             | exists cs4; split; [lx_close| exact SZ4]
             | exists cs5; split; [lx_close| clear -SZ5; lia] ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L55588686165.0000001S". (* [comment removed for export] *)
  Lemma ia_init_spec : forall (ia : bool)
      (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (SP : Z)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (cs2 cs4 cs5 : list cell) (p0 p1 : word),
      rw_cells asegs m A_IA_INIT [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)] ->
      rw_cells asegs m A_IA [C1 (Z_to_bv 8 0)] ->
      rw_cells asegs m (A_IA + 8) [CB (Z.to_nat 0x40000) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))] ->
      rw_cells asegs m (A_IA + 0x40040) cs2 -> Z.of_nat (cells_size cs2) = 0xd80 ->
      rw_cells asegs m (A_IA + 0x40dc0) [C8 p0; C8 p1] ->
      (ia = true -> p0 = Z_to_bv 64 4096 /\ p1 = Z_to_bv 64 (A_IA + 0x40dd0)) ->
      rw_cells asegs m (A_IA + 0x40dd0) cs4 -> Z.of_nat (cells_size cs4) = 0x40248 - 16 ->
      rw_cells asegs m (A_IA + 0x81008) cs5 -> Z.of_nat (cells_size cs5) = 40 ->
      ro_cells asegs m A_GOT_PAGESZ [C8 (Z_to_bv 64 A_PAGESZ_CELL)] ->
      ro_cells asegs m A_PAGESZ_CELL [C8 (Z_to_bv 64 4096)] ->
      stk asegs m lo SP -> 0x65f000 <= lo -> lo <= SP - 48 -> SP <= 2^63 -> SP mod 16 = 0 ->
      crange CS lo (SP - lo) -> mem_inv asegs m ->
      evtA asegs AL CS (ia_post ra SP gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (ia_W lo SP) lo m)
        (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_INTERNAL_ALLOCATOR) fc None m (seg_rom asegs)).
  Proof.
    intros ia ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m lo cs2 cs4 cs5 p0 p1
      IAW IA0 IA1 IA2 SZ2 IA3 HP IA4 SZ4 IA5 SZ5 GOT PGS ST LOIMG SPL SPH SPA SCS MI.
    destruct ia; cbn [Z_to_bv] in IAW.
    - destruct (HP eq_refl) as [-> ->].
      exact (ia_init_again ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m lo cs2 cs4 cs5
               IAW IA0 IA1 IA2 SZ2 IA3 IA4 SZ4 IA5 SZ5 ST LOIMG SPL SPH SPA SCS MI).
    - assert (SZ1 : Z.of_nat (cells_size [CB (Z.to_nat 0x40000) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))]) = 0x40000).
      { cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear; lia). reflexivity. }
      exact (ia_init_first ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m lo
               (Z_to_bv 8 0) _ cs2 cs4 cs5 p0 p1
               IAW IA0 IA1 SZ1 IA2 SZ2 IA3 IA4 SZ4 IA5 SZ5 GOT PGS ST LOIMG SPL SPH SPA SCS MI).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End IAInit.
End ARUN_1.
#[global] Opaque ia_cells.
