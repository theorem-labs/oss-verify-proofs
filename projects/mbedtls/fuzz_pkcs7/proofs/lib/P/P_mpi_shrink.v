(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_platform_zeroize P_mpi_free P_mpi_addsub P_mpi_grow P_mpi_copy.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P005b84e9be08ed8b 0 2 0 1 12 1P0176430646231a9a 0 2 0 1 13 1P02b96344664ad855 0 2 0 1 12 1P08fa3eae93ee35f4 0 5 0 1 25 1 26 1 35 1 36 1P0a6734c125b32585 0 2 0 1 2 1P0cc72c07c661d259 0 5 0 1 29 1 30 1 39 1 40 1P1214ae2338e5350e 0 10 0 16 11 64 12 16 14 16 20 64 30 16 31 16 32 16 41 16 42 16P1526cc8faf773248 2 16 1 1 8 3 2 1 37 1 38 1 6 0 1 26 1 27 1 36 1 39 1 40 8 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P154ba0f4533fc7de 0 2 0 1 41 1P169c9aca84aafd8a 1 1 16 2 15 1 42 1 3 0 1 41 1 43 16P17125c6cad1f6173 0 2 0 1 8 1P1a1e8086e4e1b4c1 1 2 16 2 0 1 41 1 16 2 15 1 42 1 2 43 1 44 1P1a3d167ffb43de11 2 16 1 1 8 3 2 1 37 1 38 1 6 0 1 26 1 27 1 36 1 39 1 40 8 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P1ce3d60cea13136e 0 2 0 1 11 1P20746cefe1de72fe 2 16 1 1 8 3 2 1 37 1 38 1 6 0 1 26 1 27 1 36 1 39 1 40 8 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P21262d5ee5aefb0b 2 16 1 1 8 3 2 1 37 1 38 1 6 0 1 26 1 27 1 36 1 39 1 40 8 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P21e37920f434dbe9 0 2 0 1 10 1P22621dab2b8903da 0 2 0 1 11 1P290ec8be0b030e2c 0 5 0 1 27 1 28 1 37 1 38 1P2928ee6619ba4cd6 0 2 0 1 9 1P2c401877e8ba077f 0 2 0 1 11 1P310d390e9fd8a25f 2 16 1 1 8 3 2 1 37 1 38 1 6 0 1 26 1 27 1 36 1 39 1 40 8 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P31c6dbb260c1878b 0 2 0 1 1 1P35fe9dbf58b84383 0 2 0 1 11 1P3f3da2fa57969f2e 0 2 0 1 12 1N01732f5cbf3ff9f8N0303b5f475a49dccN045a8ea69ab16212N0489b5df1e45d16dN05188fc4bfa7504fN051ec424e4009740N076716a3132b5b34N07d4e8ce8a929c1dN083eca5c437b3651N08661d969a4e9430N092b8a10db89c3ecN0978e9fa0f20303cN09c4eeeb8d65e25eN0b6e7195f03d2566N0c68d35c3f9e7a50N0f530be19414bdbbN12cbf71dfcd98e0aN134f56fb68a3a45aN18445a5abafef158N19be99ccf1232d4eN19fc63667e576e5eN1a3c66af0d07f874N1b4343eb1c017cf6N1e2a77b6d42a011dN21e08c187ba120c1N2437d361d3b1778aN253e79b56fcb14f8N2ac6c0b9f5ea233eN302d0069535aa640N3244363f0bc1082cN3258cb21139d3d56N35e74ffc6ccd1cd8N36c12824a2e5fe46N383d06a009406d80N39ca83fd9397d240N3fbae083c4058b7b"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_shrink () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.P.P_mpi_addsub.mpd_writable"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.HeapIface.hl_stack"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.HeapIface.hl_tp"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.Lib.AStep.const_at"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.P.P_mpi_addsub.mpi_binop_post"; "shrink_R"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.P.P_mpi_copy.zeros_above"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.P.PImg.psegs"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.Rep.limbs_val"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "OSSVerify.KrLib.Spec.MpiVal.mpd_out"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "OSSVerify.KrLib.Lib.HeapIface.client_waddr"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "OSSVerify.KrLib.Spec.MpiVal.mpd_ivs"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "Corelib.Lists.ListDef.repeat"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "Corelib.Init.Datatypes.nat"].


Definition P_MPI_SHRINK : Z := 0x1ee9c.
Notation MPI_SHRINK_STACK := 80 (only parsing).

Definition shrink_R (nb : Z) (dX : mpd) (LB : list blk) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_shrink ()) "(0.(1.(0.(2.$3.O2.=)(0.(2.$3.(4.O1.)(4.O4.))(0.(2.(5.&40.)(6.O1.)(6.O4.))(0.(2.$3.(7.O1.)(7.O4.))(0.(8.O5.(9.O1.))P,(2.$3.O5.(9.O4.))(2.$:.O1.O4.))))))(0.(2.$3.O2.$;.)(2.$:.O1.O4.)))Pb,$<.P,(=.$<.R1.(>.O1.))(1.(=.$<.R2.(>.O4.))(?.(=.$<.R2.O3.))))")
(* [comment removed for export] *).

Definition mpi_shrink_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_shrink ()) "Pra,(5.&40.)Psp,(5.&40.)Pgp,(5.&40.)Ptp,(5.&40.)Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Ps0,(5.&40.)Ps1,(5.&40.)Pa0,(5.&40.)Pa1,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Ps2,(5.&40.)Ps3,(5.&40.)Ps4,(5.&40.)Ps5,(5.&40.)Ps6,(5.&40.)Ps7,(5.&40.)Ps8,(5.&40.)Ps9,(5.&40.)Ps10,(5.&40.)Ps11,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)PF,(10.&5.(5.&40.))Pfc,(5.&20.)Pm,P,(5.&40.)(11.(5.&8.))Pmo,$12.Ph,(13.O5.O4.O3.)PLB,(14.$<.)PdX,$:.Pnb,$3.Plo,$3.P,(15.O5.O4.O3.R5.R4.R7.R6.)P,(16.O5.R8.R5.R4.)P,(?.(2.$17.(18.R5.)$19.))P,(1:.O4.R7.(1;.&40.R2:.)(1<.O5.O4.O3.R8.)R6.)P,(0.(8.=R6.)(1=.R6.(1>.+2.+40.)))P,(1?.O5.R<.R6.(1;.&40.R2<.))P,(8.R7.(20.(20.(1;.&40.R2=.)+50.)(21.O4.)))P,(8.(22.O4.)R8.)P,(8.(1;.&40.R2?.)(1<.O5.O4.O3.R=.))P,(2.$3.(23.(1;.&40.R30.)+10.)=)P,(8.(24.O4.)(22.O4.))P,(2.(5.&40.)R30.(25.&40.(26.O4.)))P,(27.O5.R13.)P,(28.O5.O4.R14.)P,(29.O4.O1.+8.)P,(2.(5.&40.)R2>.(25.&40.(2:.R12.)))P,(2.(5.&40.)R2>.(25.&40.R12.))(2;.O5.R17.(2<.O5.O4.O3.R39.R38.R37.R36.R32.R31.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1:.R19.R16.R15.R14.(2=.R13.R14.R15.)R12.R18.R17.)(2>.(2?.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(25.&40.O2.)R19.(30.(5.&40.))R18.(31.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>D26153483537.900000>S1i1j3Hij1k2Hk". (* [comment removed for export] *)
Lemma zeros_above_mono : forall ys i j, 0 <= i <= j -> zeros_above ys i -> zeros_above ys j.
Proof. intros ys i j Hij HZ k w Hk HN. eapply HZ; [| exact HN]. dlia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>D62811875910.700000>S2ys1n2HL1k2Hk". (* [comment removed for export] *)
Lemma zeros_above_all : forall ys n, Z.of_nat (length ys) = n -> zeros_above ys n.
Proof.
  intros ys n HL k w Hk HN. exfalso. assert (HN' : nth_error ys k = None) by (apply (proj2 (nth_error_None ys k)); dlia).
  rewrite HN' in HN. discriminate.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L11497235722.1200000@S1j1w2Hj1k2Hk2NE". (* [comment removed for export] *)
Lemma zeros_above_down' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shrink ()) "Pzs,(14.(5.&40.))Pj,$3.Pw,(5.&40.)P,(8.=R2.)P,(32.R4.(33.R3.+1.))P,(2.(11.(5.&40.))(34.(5.&40.)R5.(35.R4.))(36.(5.&40.)R3.))P,(2.$3.(23.(1;.&40.R4.)(1>.+2.+20.))=)(32.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros zs j w Hj HZ HN HW k w' Hk HN'.
  destruct (Nat.eq_dec k (Z.to_nat j)) as [->|NE]; [rewrite HN in HN'; injection HN' as <-; exact HW|].
  eapply HZ; [| exact HN']. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L38557618280.2L42111638888.200000600<S1z2HzS1z2Hz". (* [comment removed for export] *)
Lemma zx16_lit : forall z, 0 <= z < 2^16 -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx16. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section ShrinkP.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).

  (* [comment removed for export] *)
  Ltac flia := first [clear_disj; lia | lia].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12779162959.12L18926747689.12L18926759668.1200000:00;00@S1a1b1k2HkSS1a1b". (* [comment removed for export] *)
  Lemma zbv_mod64 : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    apply Z.mod_divide in H; [| lia]. flat constr:(H) 2%nat. flclear H. intros k Hk. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Ltac fix_regs :=
    repeat match goal with |- context [Z_to_bv 64 (Zpos ?p)] =>
      let z := constr:(Zpos p) in
      lazymatch eval compute in (Z.leb (2^63) z) with
      | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod64; reflexivity)
      end end.

  Lemma frame_junk8' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shrink ()) "Pmq,P,(5.&40.)(11.(5.&8.))PA,$3.Pbs,(14.(5.&8.))Prest,(14.$37.)P,(38.$39.R4.R3.(3:.$37.(3;.#8.R2.)R1.))(38.$39.R5.R4.(3:.$37.(3<.(3=.R3.))R2.))")
(* [comment removed for export] *).
  Proof.
    intros mq A bs rest H. flat constr:(H) 2%nat. intros ((LEN & WF) & _) _. cbn [cell_wf] in LEN.
    eapply rw_cells_reshape; [exact H| split; [exact I| exact WF]|].
    cbn [cells_bytes cbytes]. rewrite le8_le_bytes_to_word by exact LEN. reflexivity.
  Qed.

  Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST psegs L HI) (LB : list blk) (lo : Z)
            (X sgX nX pX : Z) (xs : list word) (padX : word) (ownX : limb_own) (nb : Z).
  Let dX := mkMPD X sgX nX pX xs padX ownX.
  Hypothesis HH0 : HEAP psegs L HI h LB m mo.
  Hypothesis MAX : mpd_at psegs m LB dX.
  Hypothesis NST : ownX <> LStatic.
  Hypothesis XW : mpd_writable L LB (bv_unsigned sp) (heap_top psegs L HI h) dX.
  Hypothesis NB : 0 <= nb < 2^64.
  Hypothesis SLO : lo <= bv_unsigned sp - MPI_SHRINK_STACK - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top psegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv psegs m.
  Hypothesis SOK0 : statics_ok psegs L m.
  Hypothesis CA : const_at L P_MEMSET_FUNC 8.

  Notation POST := (mpi_binop_post psegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX (shrink_R nb dX LB) lo m mo).
  (* [comment removed for export] *)
  Notation FRAME8 x := ([C8 x; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?D45374714661.62D60457363775.62D63308361819.62D65500065799.61D774846548.61  00000<00O00b00n01JS2sp1X2xs2XBS2sp1X2nX2xs3NRX2XBS2sp1X2nX2xs3NRX2XBS2sp1X2xs2XBS1L3HLS2sp2lo1X2xs3SLO2X02XB". (* [comment removed for export] *)
  Lemma facts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shrink ()) "(0.(2.$3.(23.VX,+8.)=)(0.(1=.=VX,)(0.(2.$3.(3>.(3?.(5.&40.)Vxs,))VnX,)(0.(0.(8.=VnX,)(8.VnX,+2710.))(0.(1.(2.$3.VsgX,+1.)(2.$3.VsgX,-1.))(0.(8.(33.VX,+10.)(1>.+2.+40.))(1.(8.(33.VX,+10.)Vlo,)(8.(1;.&40.Vsp,)VX,))))))))")
(* [comment removed for export] *).
  Proof.
    flat constr:(MAX) 2%nat. flclear MAX. intros FLt1 SGX. flat constr:(FLt1) 2%nat. flclear FLt1. intros CHX FLt2. flat constr:(FLt2) 5%nat. flclear FLt2. intros XAL X0 LENX NRX _.
    cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold MPI_MAX_LIMBS in NRX.
    pose proof (rw_cells_bound _ _ _ _ CHX) as XB. unfold mpi_cells in XB. cbn [cells_size csize Nat.add] in XB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH0)) 2%nat. intros HBR _. flat constr:(XW) 3%nat. flclear XW. intros XCW _ _. cbn [dX md_addr] in XCW.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(dlia) HBR DHI ACL ltac:(dlia)) as XS.
    (flsplit; repeat split); try assumption; dlia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0@D34825983172.127D36470197463.122D39409836362.127D52101704109.129D52101733636.125D52101802538.135D52103794831.127D54391985784.127D54398282304.126D64836515237.122D65065560810.127L11741095640.121L1599948709.126 L23100341967.122L26924648792.121L27905185800.123L28767740167.125L28767740167.126L43654564952.121L44046804688.125L44046804688.126L49578233423.122L51709126249.122L59499841752.121L62965564504.126L7510805464.121 L7897711517.126 00000100L00i01_02V03R03l04h05c06>06?06U06V06l07B07l0920:60:L0;]0<n0=D0=Z0>00>X0>n0?VFS2sp1X2xs1i1A2la2Hi3PA03PABS2sp1X2xs1A2la3PA03PAB1a1H2H0S1L3HLS2sp2lo1X2xs3SLO3ACL3DHI1A2la2X03SPB3PA03PAB1a1CS1L3HLS2sp2lo1X2xs3SLO3ACL3DHI1A2la2X03SPB3PA03PAB1a2HaS1L3HLS2sp2lo1X2xs3SLO3ACL1A2la2X03SPB3PA03PAB1a1B1k1R2B02B4S2sp1X2xs1A2la3PA03PAB1a1CS1L2HI3HLS2sp1h2lo1X2xs3SLO4HTOP1A2la2X03SPB3PA03PAB1a2NO2H0S1L2HI3HLS2sp1h2lo1X2xs3SLO4HTOP1A2la2X03SPB3PA03PAB1a2NO1HS2sp1X2xs1i1A2la2Hi3PA03PABFS2sp1X2xs1A2la3PA03PABFS2sp1X2xs1A2la3PA03PABS2sp1X2xs1A2la3PA03PABS1L3HLS2sp2lo1X2xs3SLO1A2la2X03SPB3PA03PABS1L3HLS2sp2lo1X2xs3SLO3SPA1i1A2la3XAL2X02XS3SPB3PA03PAB2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2xs3SLO3SPA1A2la3XAL2X02XS3SPB3PA03PAB2HB5Ha_st5Hl_stS2sp1X2xs1A2la3PA03PABS1L3HLS2sp2lo1X2xs3SLO3ACL1i1A2la2HL3A162XA3AAC3XAL2X03SPB3PA03PAB2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2xs3SLO3ACL1i1A2la2HL3A162XA3AAC3XAL2X03SPB3PA03PAB2HB5Ha_st5Hl_stS2sp1X2xs1A2la3PA03PABS2sp1X2xs1A2la3PA03PABS2sp1X2xs1A2la3PA03PABS2sp1X2xs1A2la2XB3PA03PAB2HB5Ha_st5Hl_stS2sp1X2xs1A2la3PA03PABS2sp1X2xs1A2la2X03PA03PAB2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  Lemma store_tail : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shrink ()) "Pi,$3.PA,$3.Pla,(14.(5.&40.))Pmc,P,(5.&40.)(11.(5.&8.))Pmoc,$12.Phc,(13.$39.VL,VHI,)PLBc,(14.$<.)Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa0,(5.&40.)Pa1,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Pxs1,(5.&40.)Pys1,(5.&40.)Pxs5,(5.&40.)ZdXc,$:.(40.VX,VsgX,R19.R18.R17.VpadX,$41.)P,(0.(8.+1.R1:.)(8.R1:.+2710.))P,(2.$3.(3>.(3?.(5.&40.)R19.))R1;.)P,(2.$3.(42.R1:.)(42.Vxs,))P,(8.Vnb,R1=.)P,(?.(2.$3.Vnb,VnX,))P,(15.$39.VL,VHI,R1:.R19.R1<.R1;.)P,(2.$3.(1<.$39.VL,VHI,R1;.)(1<.$39.VL,VHI,Vh,))P,(43.Vmo,R1=.)P,(=.(44.$3.$3.)(45.$3.$3.R21.(46.+4.R22.))R1<.)P,(2.$3.(23.R22.+10.)=)P,(47.$39.R21.R23.R22.)P,(1.(8.(33.VX,+10.)R24.)(8.(33.R24.(46.+4.R25.))VX,))P,(1=.=R25.)P,(8.(33.R26.(46.+4.R27.))(22.VL,))P,(48.VLB,VdX,R22.R?.)P,Pb,$<.P,(=.$<.R1.(>.R11.))(1.(=.$<.R2.(>.VdX,))(?.(=.$<.R2.VLB,)))P,(38.$39.R27.VX,(49.VpX,(25.&40.VsgX,)VnX,VpadX,))P,Pa,$3.P,(0.(8.VX,R1.)(1=.R1.(33.VX,+10.)))(4:.VL,R27.Vlo,(1<.$39.VL,VHI,Vh,)R2.)P,(4;.$39.VL,VLB,(1;.&40.Vsp,)(4<.VdX,)Vm,R29.)P,(28.$39.VL,R2:.)P,(27.$39.R2;.)P,(1?.$39.R2<.Vlo,(33.(1;.&40.Vsp,)-30.))P,(38.$39.R2=.(33.(1;.&40.Vsp,)-30.)(3:.$37.(3<.R18.)(3:.$37.(3<.Vs3,)(3:.$37.(3<.Vs2,)(3:.$37.(3<.Vs1,)(3:.$37.(3<.Vs0,)(3:.$37.(3<.Vra,)(4=.$37.))))))))(2;.$39.R2=.(2<.$39.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(2=.Vnb,VdX,VLB,)Vlo,Vm,Vmo,)(2>.(2?.R1;.(25.&40.(33.(1;.&40.Vsp,)-30.))Vgp,Vtp,R2:.R29.R28.(25.&40.VX,)R1:.R27.R26.R25.R24.R23.R22.R21.R20.(25.&40.R30.)(25.&40.R31.)Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1?.R1>.R1=.R1<.)VF,(25.&40.+1>?68.)Vfc,(30.(5.&40.))R2>.(31.$39.)))")
(* [comment removed for export] *).
  Proof.
    intros until xs5. intros dXc Hi HL HV HNB NBX HHc HTc MFc AIN A16 PA XA A0 AAC OUTc FRc CHX XCWc PXc SOKc MIc STc FRM.
    flat constr:(facts) 7%nat. intros XAL X0 LENX NRX SGX XB XS. pose proof alloc_ceiling_pos as ACP.
    pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MKc. flat constr:((heap_blocks _ _ HI _ _ _ _ HHc)) 2%nat. intros HBRc HAPc.
    flat constr:(XW) 3%nat. intros XCW XD XP. cbn [dX md_addr md_own md_p md_n] in XCW, XD, XP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    unfold mpi_cells in CHX. flat constr:((proj1 PA)) 3%nat. intros PA0 PAB _. rewrite u32s_length in PAB.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (X, X + 16)] mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    pose proof (conj HHc I) as HHc0. pose proof (conj SOKc I) as SOKc0.
    zstep. zstep. zstep. zstep.
    do 7 zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => match goal with H : stk psegs mx _ _ |- _ => release_frame FRM H (bv_unsigned sp) end end.
    zstep.
    flat constr:(HHc0) 2%nat. flclear HHc0. intros HHc0 _. flat constr:(SOKc0) 2%nat. flclear SOKc0. intros SOKc0 _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : u32arr psegs m5 A la |- _ => rename H into PA5 end.
    match goal with H : rw_cells psegs m5 X _ |- _ => rename H into CHX5 end.
    apply aevtM_done. unfold mpi_binop_post. flexi 16%nat. exists hc, LBc. exists dXc, 0.
    split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact MFc|]. split; [exact HTc|].
    split. { eapply (Asn1AuxA.HEAP_munch psegs L HI) with (SP := lo); [exact HHc0| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO. rewrite HTc.
      destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [apply XCWc; dlia|]|]; left; dlia. }
    split. { split; [| cbn; exact SGX]. cbn [dXc md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CHX5|]. split; [exact XAL|]. split; [exact X0|]. split; [exact HL|]. split; [unfold MPI_MAX_LIMBS; dlia|].
      split; [dlia|]. split; [exact AIN|]. split; [exact A16|]. exact PA5. }
    split; [exact OUTc|].
    split. { eapply heap_presx_trans; [exact PXc|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn. unfold mpd_ivs, dX in Ho. cbn in Ho. flat constr:(Ho) 2%nat. flclear Ho. intros O1 _. split; [| split; [exact O1| exact I]].
      flat constr:((heap_blocks _ _ HI _ _ _ _ HH0)) 2%nat. intros HBR _.
      destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| destruct DIMG; dlia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (B0 & B1 & B2 & B4 & B5); cbn in R, B4; dlia]. }
    split. { eapply statics_ok_munch; [exact SOKc0| exact MU|]. intros a Ha NW. cbn. split; [dlia|]. split; [| exact I]. intros HX. exact (NW (XD a HX Ha)). }
    unfold shrink_R. cbn [dX dXc md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk].
    split; [| exact FRc]. left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold mpd_val; cbn; rewrite HV; reflexivity|].
    split; [exact HNB|]. intros E. exfalso. exact (NBX E).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01<0@D11566314080.173D14788761187.148D14792959895.167D15226557382.173D16611400004.165D16626163093.132D1662731162.126 D17330745161.148D19646181967.176D19652550953.175D19652659704.171D21033315414.148D24457664479.132D24459827253.131D25514701578.173D28812073579.132D28814103937.131D346233660.127  D36243493956.148D37738322230.173D38232103310.148D39409830041.175D39409836362.143D41411666715.148D42868180853.126D43646788288.165D43881655583.132D44403128807.148D46288017929.144D46288018056.145D46288024153.175D4632852750.174 D47961590503.148D52101704109.180D52101720239.178D52101802921.182D52476392461.131D52478557159.132D54391985784.143D54391986042.145D54391986171.144D54398102733.144D54398102733.167D57751154346.181D57751203752.180D58304623070.148D59308562897.5  D59315317366.129D60668600941.173D60675325052.132D60675325052.175D60675325052.177D60681178462.132D60681178462.175D65500066615.126D66952896442.132D6739948970.178 D67494351642.165D68341490923.148D68394880291.165D68418607539.173D7331155503.165 D818916129.148  L1227220751.147 L1227220751.148 L12292857614.145L12292857614.146L22700267513.146L23100341967.142L35419500961.0  L40238812268.147L44154063980.146L44154063980.147L44154063980.148L61263218231.145R22706564033.15100000Z01J02:02l03U04>04k04l05H05[05m06>06f07N07_08S09G09k0:W0:e0;<0;O0;d0<20<R0=<0=`0>50>M0>e0?T0@B0@W0AK0A]0BT0CI0D>0EF0FE0GP0HA0I20IW0J?0Jm0K;0L70LW0M>0Mc0NH0O20OZ0Oh0PR0QG0Qf0RK0Rb0SK0So0Tc0Td0Te0U70Un0WG0WU0WV0Y40ZG0ZH0ZI0[80\<S2sp1X2nX2pX2xs1i1c1A3HcR3Hci2X03SPB2P02A0S1L3HLS2sp2lo1X2pX2xs3SLO3ACL1A2X03ACP3SPB2P02A0S1L3HLS2sp2lo1X2pX2xs3SLO3ACL1A2X03ACP3SPB2P02A0S1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL1A2X03SPB2P02P42A0S2sp1X2nX2pX2xs1c1A3HcR2X04LENX3SPB2P02A0S2sp1X2nX2pX2xs1c1A3HcR2X04LENX3SPB2P02A0S2sp1X2nX2pX2xs1i1c1A2Hi3HcR3Hci2X03SPB2P02A0FS1L2HI2sp1h1X2pX2xs1A1a2Ha1CS2sp1X2pX2xs1A1a2HaS2sp1X2pX2xs1A1a1CS2sp1X2nX2pX2xs1AS2sp1X2nX2pX2xs1c1A3HcR2X03NRX3SPB2P02A0S2sp1X2nX2pX2xs1c1A3HcR2X03NRX3SPB2P02A0S2sp1X2nX2pX2xs1AS1L3HLS2sp2lo1X2pX2xs3SLO3ACL1i1A2Hi2X03SPB2P02A02A4S1L3HLS2sp2lo1X2pX2xs3SLO3ACL1i1A2Hi2X03SPB2P02A02A4S2sp1X2nX2pX2xs1c1A3HcR2X03SPB2P02A0S2sp1X2nX2pX2xs1c1A3HcR2X04LENX3SPB2N12P02A0S2sp1X2pX2xs1AS1L2sp2lo1X2pX2xs3SLO1AS2sp1X2pX2xs1A1a2HaS2sp1X2pX2xs1A1a1H2H0S2sp1X2pX2xs1AS2sp1X2pX2xs1i1A2Hi2X03SPB2P02A0S2sp1X2nX2pX2xs1i1c1A3HcR3Hci2X03SPB2P02A0S2sp1X2nX2pX2xs1c1A3HcR2X03SPB2P02A0S2sp1X2nX2pX2xs1A3NRXS2sp1X2pX2xs1i1A1a2H02H1S2sp1X2pX2xs1i1A1a2H12H2S2sp1X2pX2xs1i1c1A3Hci2X03SPB2P02A01a2Ha2nX3HcRS2sp2LB1X2nX2pX2xs1i1c1A2Hi3HcR2X03SPB2P02A01eS2sp1X2nX2pX2xs1A3NRXS1L3HLS2sp2lo1X2pX2xs3SLO3ACL3DHI1A2X03SPB2P02A01a1CS2sp1X2pX2xs1A1a1CS1L3HLS2sp2lo1X2pX2xs3SLO3ACL1A2X03SPB2P02A01a1B1k1R2B4S1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL1A2X03SPB2N12P02P42A0S1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL1A2X03SPB2N12P02P42A0S1L2HI3HLS2sp1h2lo1X2pX2xs3SLO3ACL4HTOP1i1A2Hi2X03SPB2P02A02A41a2NO1H2H0S1L2HI3HLS2sp1h2lo1X2pX2xs3SLO4HTOP1i1A2X03SPB2P02A01a2NO2H02H2S1L2HI3HLS2sp1h2lo1X2pX2xs3SLO3ACL4HTOP1i1A2Hi2X03SPB2P02A02A41a2NO2H02H11HS1L2HI3HLS2sp1h2lo1X2pX2xs3SLO1A2X03SPB2P02A01a1CS1L2HI3HLS2sp1h2lo1X2pX2xs3SLO1A2X03SPB2P02A01a1CS2sp1X2pX2xs1i1A2X03SPB2P02A01a1B1k1RS1L2sp1X2pX2xs1i1A2X03SPB2P02A01a1C1H2H0S1L2HI2sp1h1X2pX2xs4HTOP1A2h23HT22X03SPB2P02A0S2nX2pX1a1R2O2S1L2HI3HLS2sp1h2lo1X2pX2xs3SLO3ACL1i1A2X03SPB2P02A02A41a1C1SS2sp1X2pX2xs1i1A2Hi2X03SPB2P02A0S2sp1X2pX2xs1i1A2X03SPB2P02A01a1C1B1k1RS2sp1X2nX2pX2xs1A2X03SPB2P02A01a2Ha1RS2sp1X2nX2pX2xs1A2X03SPB2P02A01a2Ha1RS1L2sp1X2pX2xs1i1A2X03SPB2P02A01a1C1D1H2H0S2sp1X2nX2pX2xs1i1A2Hi2X03SPB2P02A01H2H0S2sp1X2pX2xs1AS2sp1X2nX2pX2xs1i1c1A3HcR3Hci2X03SPB2P02A0S1L3HLS2sp2lo1X2pX2xs3SLO3ACL1i1A2X03SPB2P02A02A41a1CS2sp1X2pX2xs1i1c1A2X03SPB2P02A0S2sp1X2nX2pX2xs1A2X03NRX3SPB2N12P02A0S2sp1X2nX2pX2xs1c1A3HcRS2sp1X2nX2pX2xs1i1c1A2Hi3Hci2X03SPB2P02A0S2sp1X2nX2pX2xs1c1A3HcR2X03SPB2P02A0S1L3HLS2sp2lo1X2pX2xs3SLO3ACL3SPA1A2X03ACP3SPB2P02A0FFS2sp1X2pX2xs1i1c1AS1L3HLS2sp2lo1X2pX2xs3SLO3ACL1i1c1A3Hci2X03SPB2P02A02A4S1L3HLS2sp2lo1X2nX2pX2xs2nb3SLO3ACL1i1c1A2Hi4HNBI3NBX3HcR3Hci2X03SPB2P02P42A02A42XA3x141HS2sp1X2pX2xs1ASS1L3HLS2sp2lo1X2nX2pX2xs2nb3SLO3ACL1i1c1A2Hi4HNBI3NBX3HcR3Hci3XAL2X03SPB2N12P02P42A03A162A42XAS2sp1X2nX2pX2xs2nb1i1c1A2Hi4HNBI3NBX3HcR3Hci2X04LENX2XP3SPB2N13PAL2P02A03A163APA2XAFFS1L2sp2lo1X2pX2xs3ACL1i1c1A3Hci2X03SPB2P02A02A4S1L4DIMG2sp1X2nX2pX2xs2nb1i1c1A4HNBI3NBX3HcR3Hci2X03SPB2P02A02A51a1H". (* [comment removed for export] *)
  Lemma tail9c : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shrink ()) "Pi,$3.Pc,$3.PA,$3.Pm2,P,(5.&40.)(11.(5.&8.))Pmo2,$12.Ph2,(13.$39.VL,VHI,)Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa0,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Pxs1,(5.&40.)Pys1,(5.&40.)Pxs5,(5.&40.)P,(2.$17.VownX,$41.)P,(0.(8.+1.R17.)(8.R17.+2710.))P,(8.Vnb,R18.)P,(?.(2.$3.Vnb,VnX,))P,(0.(8.+1.R19.)(8.R19.VnX,))P,(8.R1:.R1;.)P,(32.Vxs,R1;.)P,(15.$39.VL,VHI,R18.(3:.(44.$3.$3.)(45.$3.$3.R1;.(46.+4.R1=.))VLB,)R1:.R19.)P,(2.$3.(1<.$39.VL,VHI,R19.)(1<.$39.VL,VHI,Vh,))P,(43.Vmo,R1;.)P,(4>.VL,R1>.(46.+4.R20.))P,(38.$39.R1>.R1?.(3:.$37.(3;.(35.(46.+4.R21.))(4?.(5.&8.)(25.&8.=)(35.(46.+4.R21.))))(4=.$37.)))P,(47.$39.R1?.VpX,Vxs,)P,(38.$39.R20.VX,(49.VpX,(25.&40.VsgX,)VnX,VpadX,))P,(4;.$39.VL,VLB,(1;.&40.Vsp,)(4<.VdX,)Vm,R21.)P,(28.$39.VL,R22.)P,(27.$39.R23.)P,(1?.$39.R24.Vlo,(33.(1;.&40.Vsp,)-30.))P,(38.$39.R25.(33.(1;.&40.Vsp,)-30.)(3:.$37.(3<.R13.)(3:.$37.(3<.Vs3,)(3:.$37.(3<.Vs2,)(3:.$37.(3<.Vs1,)(3:.$37.(3<.Vs0,)(3:.$37.(3<.Vra,)(4=.$37.))))))))(2;.$39.R25.(2<.$39.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(2=.Vnb,VdX,VLB,)Vlo,Vm,Vmo,)(2>.(2?.R16.(25.&40.(33.(1;.&40.Vsp,)-30.))Vgp,Vtp,R23.R22.R21.(25.&40.VX,)R15.R20.(25.&40.VpX,)(25.&40.(46.+4.R28.))R1?.R1>.R1=.R1<.R1;.(25.&40.R27.)(25.&40.R29.)Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1:.R19.R18.R17.)VF,(25.&40.+1>?50.)Vfc,(30.(5.&40.))R26.(31.$39.)))")
(* [comment removed for export] *).
  Proof.
    intros until xs5. intros EO Hi HNBI NBX HcR Hci ZX HH2 HT2 MF2 HBA HNEW PX2 CHX HPX2 SOK2 MI2 ST2 FRM.
    flat constr:(facts) 7%nat. intros XAL X0 LENX NRX SGX XB XS. pose proof alloc_ceiling_pos as ACP.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2. flat constr:((heap_blocks _ _ HI _ _ _ _ HH0)) 2%nat. intros HBR HAP. pose proof (HND _ _ _ _ HH0) as ND.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 HAP2. pose proof (HND _ _ _ _ HH2) as ND2.
    flat constr:(XW) 3%nat. intros XCW XD XP. cbn [dX md_addr md_own md_p md_n] in XCW, XD, XP. specialize (XP EO).
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(MAX) 2%nat. intros FLt3 _. flat constr:(FLt3) 2%nat. flclear FLt3. intros _ FLt4. flat constr:(FLt4) 5%nat. flclear FLt4. intros _ _ _ _ OX. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX. rewrite EO in OX.
    flat constr:(OX) 4%nat. flclear OX. intros N1 PIN PAL _.
    flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5.
    pose proof HBA as HBA'. flat constr:(HBA') 5%nat. flclear HBA'. intros A0 A16 _ A4 A5. flat constr:(HAP2) 2%nat. flclear HAP2. intros HAPA _.
    pose proof (HAPA pX (4 * nX) PIN) as APA.
    assert (XA' : forall a, X <= a < X + 16 -> ~ (A <= a < A + 4 * i)).
    { intros a Ha C. destruct (XCW a Ha) as [S|[[D NS]|([B k] & Hb & R)]]; [dlia| generalize A5; destruct DIMG; dlia| generalize (HAPA B k Hb); cbn in R; dlia]. }
    pose proof (pointwise_apart X 16 A (4 * i) ltac:(dlia) ltac:(dlia) XA') as XA. clear XA'.
    unfold mpi_cells in CHX.
    (* [comment removed for export] *)
    assert (HN2 : rw_cells psegs m2 A ([CB (4 * Z.to_nat c) (repeat (Z_to_bv 8 0) (4 * Z.to_nat c))] ++ [CB (Z.to_nat (4 * (i - c))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * (i - c))))])).
    { eapply rw_cells_reshape; [exact HNEW| |].
      - cbn. rewrite !repeat_length; (flsplit; repeat split); reflexivity.
      - cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- repeat_app. f_equal. dlia. }
    apply rw_cells_app in HN2. flat constr:(HN2) 2%nat. flclear HN2. intros HNA HNB. cbn [cells_size csize Nat.add] in HNB. clear HNEW.
    replace (A + Z.of_nat (4 * Z.to_nat c + 0)) with (A + 4 * c) in HNB by dlia.
    pose proof PX2 as PX2'. rewrite <- (firstn_skipn (Z.to_nat c) xs) in PX2'. apply u32arr_app in PX2'. flat constr:(PX2') 2%nat. flclear PX2'. intros PXA _.
    pose proof (proj1 PXA) as PBA.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A, A + 4 * i); (X, X + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. zstep.
    pose proof P_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPc with (src := u32s (firstn (Z.to_nat c) xs)); rewrite ?unsigned_lit by dlia;
      [ exact PBA | rewrite u32s_length, firstn_length_le by dlia; dlia | replace (Z.to_nat (4 * c)) with (4 * Z.to_nat c)%nat by dlia; exact HNA | generalize APA; dlia | exact MI2 ] | ].
    clear SPc. unfold memcpy_post. rewrite !unsigned_lit by dlia. post_call psegs m2.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : mem_inv psegs m3 |- _ => rename H into MI3 end.
    match goal with H : rw_cells psegs m3 A _ |- _ => rename H into PA end.
    assert (HH3 : HEAP psegs L HI h2 ((A, 4 * i) :: LB) m3 mo2).
    { clear_disj. eapply (Asn1AuxA.HEAP_munch psegs L HI) with (SP := lo); [exact HH2| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO. rewrite HT2.
      destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [destruct (XCW a ltac:(dlia)) as [C|[C|([B k] & Hb & R)]]; [left; dlia| right; left; exact C| right; right; exists (B, k); split; [right; exact Hb| exact R]] |] |].
      all: destruct (Z.le_gt_cases A a); [destruct (Z.lt_ge_cases a (A + 4 * i)); [right; right; exists (A, 4 * i); split; [left; reflexivity| cbn; dlia] |] |].
      all: left; dlia. }
    pose proof PX2 as PX2c. apply u32arr_cells in PX2c. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    match goal with H : u32arr psegs m3 pX xs |- _ => clear PX2c; pose proof H as PX2c; apply u32arr_cells in PX2c | _ => idtac end.
    zstep. zstep. zstep. zstep.
    replace (bv_unsigned (zx16 (Z_to_bv 64 nX)) ≪ 2) with (4 * nX)
      by (rewrite (zx16_lit nX) by dlia; rewrite unsigned_lit by dlia; rewrite Z.shiftl_mul_pow2 by dlia; dlia).
    eapply aevtM_cut.
    { eapply (P_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := pX) (len := 4 * nX) (lo := lo) (junk := u32s xs);
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by dlia; try eassumption; try reflexivity; try dlia.
      right. split; [right; exact PIN|]. replace (Z.to_nat (4 * nX)) with (4 * length xs)%nat by dlia. exact PX2c. }
    cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
    flat constr:(PO) 20%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m4 mo4 h4 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by dlia.
    flat constr:(PO) 7%nat. flclear PO. intros MI4 ST4 MF4 HT4 HH4 PX4 SOK4.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ dlia | reflexivity ]) end.
    assert (LBR : lb_remove pX ((A, 4 * i) :: LB) = (A, 4 * i) :: lb_remove pX LB) by (cbn; destruct (Z.eqb_spec A pX); [generalize APA; dlia| reflexivity]).
    rewrite LBR in HH4, PX4. clear LBR.
    apply (heap_presx_rw_cells psegs L _ _ _ m3 m4 _ _ PX4) in FRM; [| cbn [cells_size csize Nat.add]; intros a Ha; left; dlia | cbn; split; [dlia| exact I] ].
    apply (heap_presx_rw_cells psegs L _ _ _ m3 m4 _ _ PX4) in PA; [| cbn [cells_size csize Nat.add]; intros a Ha; right; right; exists (A, 4 * i); split; [left; reflexivity| cbn; dlia] | cbn; split; [generalize APA; dlia| exact I] ].
    apply (heap_presx_rw_cells psegs L _ _ _ m3 m4 _ _ PX4) in HNB; [| cbn [cells_size csize Nat.add]; intros a Ha; right; right; exists (A, 4 * i); split; [left; reflexivity| cbn; dlia] | cbn; split; [generalize APA; dlia| exact I] ].
    apply (heap_presx_rw_cells psegs L _ _ _ m3 m4 _ _ PX4) in CHX;
      [| cbn [cells_size csize Nat.add]; intros a Ha;
         destruct (XCW a ltac:(dlia)) as [C|[C|([B k] & Hb & R)]]; [left; dlia| right; left; exact C| right; right; exists (B, k); split; [|exact R]];
         right; apply (in_lb_remove_other LB pX (4 * nX) B k ND PIN Hb); intros E; injection E as -> ->; cbn in R; generalize XP; dlia
       | cbn; split; [generalize XP; dlia| exact I] ].
    assert (HPX4 : heap_presx psegs L LB (bv_unsigned sp) (mpd_ivs dX) m m4).
    { eapply heap_presx_trans; [exact HPX2|]. eapply heap_presx_trans.
      - eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. unfold mpd_ivs, dX in Ho. rewrite EO in Ho. cbn in Ho |- *. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _.
        split; [| split; [| split; [exact O1| exact I]]].
        + destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| destruct DIMG; dlia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (_ & _ & _ & B4 & _); cbn in R, B4; dlia].
        + destruct Hc as [C|[C|([B k] & Hb & R)]]; [dlia| generalize A5; destruct DIMG; dlia| generalize (HAPA B k Hb); cbn in R; dlia].
      - intros a Ha Hc Ho. unfold mpd_ivs, dX in Ho. rewrite EO in Ho. cbn in Ho. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _.
        apply PX4; [exact Ha| | cbn; split; [exact O2| exact I]].
        destruct Hc as [C|[C|([B k] & Hb & R)]]; [left; clear_disj; dlia| right; left; exact C| right; right; exists (B, k); split; [|exact R]].
        right. apply (in_lb_remove_other LB pX (4 * nX) B k ND PIN Hb). intros E; injection E as -> ->; cbn in R; clear -R O2; dlia. }
    clear HPX2 PX4 MU WM.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH4)) 2%nat. intros HBR4 _.
    assert (XCW4 : forall a, X <= a < X + 16 -> client_waddr L ((A, 4 * i) :: lb_remove pX LB) lo (heap_top psegs L HI h) a).
    { intros a Ha. destruct (XCW a Ha) as [C|[C|([B k] & Hb & R)]]; [left; clear_disj; dlia| right; left; exact C| right; right; exists (B, k); split; [|exact R]].
      right. apply (in_lb_remove_other LB pX (4 * nX) B k ND PIN Hb). intros E; injection E as -> ->; cbn in R; generalize XP; dlia. }
    eapply (store_tail i A (firstn (Z.to_nat c) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (i - c))) m4 mo4 h4 ((A, 4 * i) :: lb_remove pX LB)); try eassumption; try reflexivity.
    + rewrite length_app, firstn_length_le, repeat_length by (clear_disj; dlia). clear_disj; dlia.
    + rewrite limbs_val_app, limbs_val_repeat0, Z.mul_0_r, Z.add_0_r. apply limbs_val_firstn; [clear_disj; dlia| exact ZX].
    + rewrite HT4. exact HT2.
    + eapply mo_frame_trans; [exact MF2| exact MF4].
    + left; reflexivity.
    + apply u32arr_app. split; [eapply u32arr_of_cells; [exact PA| reflexivity]|].
      rewrite firstn_length_le by (clear_disj; dlia). replace (A + 4 * Z.of_nat (Z.to_nat c)) with (A + 4 * c) by (clear_disj; dlia).
      eapply u32arr_of_cells; [exact HNB|]. rewrite u32s_repeat0. f_equal. clear_disj; dlia.
    + unfold dX. rewrite EO. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
      split. { intros b [<-|Hb]; [right; left; reflexivity| left; eapply In_lb_remove; exact Hb]. }
      split. { intros [B k] Hb Hn. right. apply (in_lb_remove_other LB pX (4 * nX) B k ND PIN Hb). intros E. apply Hn. left. symmetry. exact E. }
      intros b [<-|[]] [E|HinR]; [injection E; intros; exfalso; generalize APA; dlia| exfalso; exact (lb_remove_notin LB pX (4 * nX) ND HinR)].
    + unfold dX. rewrite EO. cbn [mpd_blk md_own md_p md_n]. intros b [<-|[]]. right. intros HinA. generalize (HAPA A (4 * i) HinA). dlia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@D12996432337.133D14679438397.108D14792955057.108D14792959895.126D16320246039.136D1649790441.127 D25188048531.129D2780666493.128 D29110695509.134D34592623507.130D36052405171.129D37940080267.128D3826792822.136 D4022475859.136 D40825677417.108D41415938670.136D49643072906.129D51286046306.108D59308632307.136D59308633593.135D63530131802.108D7591738523.108 D9072270588.128 L11741095640.125L23100341967.131L26924648792.125L27907150090.128L28814040852.130L43654564952.125L51709126206.127L52476066706.131L59499841752.125L67564210050.131L7510805464.125 R2113957450.128 00000S01601a02L03403G03S03_04004<04c04d05I05Z05f06406@06U06i07=07U07j07k08708E08Q09409l0:80:D0;90;E0<=0<I0<US2sp1X2nX2pX2xs2X04LENX3SPB2P01a2HaS2sp1X2nX2pX2xs2i22Hi2X03NRX3SPB2P0S1L3HLS2sp2lo1X2pX2xs3SLO3ACL2X03ACP3SPB2P0S1L3HLS2sp2lo1X2pX2xs3SLO3ACL2X03ACP3SPB2P0S2sp1X2nX2pX2xs2i22Hi2X03NRX3SPB2P01A2A0S2sp1X2nX2pX2xs3NRXS2sp1X2pX2xsS2sp1X2pX2xsS2sp1X2pX2xs2i21AS2sp1X2pX2xsS1L3HLS2sp2lo1X2pX2xs3SLO3ACL2X03SPB2P0FS2sp1X2nX2pX2xs2nb3NBX2X03SPB2P01A2A0S2sp1X2pX2xs2i21AS2sp1X2pX2xsS2sp1X2pX2xs1AS2sp1X2pX2xsS1L2sp2lo1X2pX2xs3SLOS2sp1X2pX2xs2P01A2KPS2sp1X2pX2xs1A2A02KZS1L2HI2sp1h1X2pX2xs4HTOPS2sp1X2nX2pX2xs2i22HiFS2sp1X2pX2xsS2sp1X2pX2xs1AS2sp1X2pX2xsS1L3HLS2sp2lo1X2pX2xs3SLO2X03SPB2P0S1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL2i22Hi2X03SPB2P01A2A02A4S2sp1X2pX2xsS2sp1X2pX2xsS1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL2X03SPB2N12P02P41A2A0S2sp1X2pX2xsS1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL2i22Hi2X03SPB2P01A2A02A4S2sp1X2pX2xsS2sp1X2pX2xs". (* [comment removed for export] *)
  Lemma from3c : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shrink ()) "Pi2,$3.Pm1,P,(5.&40.)(11.(5.&8.))Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa0,(5.&40.)Pa1,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Pxs5,(5.&40.)P,(2.$17.VownX,$41.)P,(0.(8.+1.R13.)(8.R13.VnX,))P,(8.Vnb,R14.)P,(1=.Vnb,VnX,)P,(32.Vxs,R16.)P,(38.$39.R16.VX,(49.VpX,(25.&40.VsgX,)VnX,VpadX,))P,(47.$39.R17.VpX,Vxs,)P,(15.$39.VL,VHI,Vh,VLB,R18.Vmo,)P,(50.(3:.(44.$3.$3.)(45.$3.$3.(20.(1;.&40.Vsp,)+30.)(1;.&40.Vsp,))(4=.(44.$3.$3.)))Vm,R19.)P,(51.$39.Vm,R1:.)P,(28.$39.VL,R1;.)P,(27.$39.R1<.)P,(1?.$39.R1=.Vlo,(33.(1;.&40.Vsp,)-30.))P,(38.$39.R1>.(33.(1;.&40.Vsp,)-30.)(3:.$37.(3<.R>.)(3:.$37.(3<.Vs3,)(3:.$37.(3<.Vs2,)(3:.$37.(3<.Vs1,)(3:.$37.(3<.Vs0,)(3:.$37.(3<.Vra,)(4=.$37.))))))))(2;.$39.Vmo,(2<.$39.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(2=.Vnb,VdX,VLB,)Vlo,Vm,Vmo,)(2>.(2?.Vra,(25.&40.(33.(1;.&40.Vsp,)-30.))Vgp,Vtp,R1>.R1=.R1<.(25.&40.VX,)(25.&40.$;.)R1;.R1:.R19.R18.R17.R16.R15.R14.Vs2,(25.&40.R20.)Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R13.R12.R11.R10.)VF,(25.&40.+1>?00.)Vfc,(30.(5.&40.))R1?.(31.$39.)))")
(* [comment removed for export] *).
  Proof.
    intros until xs5. intros EO Hi HNB NBX ZX CHX PX HH1 MU WM SOK1 MI1 ST1 FRM.
    flat constr:(facts) 7%nat. intros XAL X0 LENX NRX SGX XB XS. pose proof alloc_ceiling_pos as ACP.
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1. flat constr:((heap_blocks _ _ HI _ _ _ _ HH1)) 2%nat. intros HBR HAP. pose proof (HND _ _ _ _ HH1) as ND.
    flat constr:(XW) 3%nat. intros XCW XD XP. cbn [dX md_addr md_own md_p md_n] in XCW, XD, XP. specialize (XP EO).
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(MAX) 2%nat. intros FLt5 _. flat constr:(FLt5) 2%nat. flclear FLt5. intros _ FLt6. flat constr:(FLt6) 5%nat. flclear FLt6. intros _ _ _ _ OX. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX. rewrite EO in OX.
    flat constr:(OX) 4%nat. flclear OX. intros N1 PIN PAL _.
    flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5.
    unfold mpi_cells in CHX.
    zstep. zstep. zstep.
    replace (Z_to_bv 64 0x3c268) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc psegs L HI) with (cnt := i2) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by dlia; try eassumption; try reflexivity; try dlia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by dlia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ dlia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match goal with H : heap_pres _ _ _ _ m1 m2 |- _ => rename H into HPc end.
    match goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
    match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    match goal with H : mo_frame mo mo2 |- _ => rename H into MF2 end.
    clear ST1 MI1. heap_transport HPc.
    assert (SOK2 : statics_ok psegs L m2) by (eapply statics_ok_heap_pres; [exact SOK1| exact HPc| exact SW]).
    assert (HPX2 : heap_presx psegs L LB (bv_unsigned sp) (mpd_ivs dX) m m2).
    { eapply heap_presx_trans; [| eapply heap_presx_of_pres_sub; [exact HPc| intros b Hb; exact Hb| dlia| dlia]].
      eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| dlia]. }
    assert (PX2 : u32arr psegs m2 pX xs).
    { pose proof PX as U. apply u32arr_cells in U.
      apply (heap_pres_rw_cells psegs L LB _ m1 m2 _ _ HPc) in U.
      2: { cbn [cells_size csize Nat.add]. intros a Ha. right; right. exists (pX, 4 * nX). split; [exact PIN| cbn; dlia]. }
      eapply u32arr_of_cells; [exact U| reflexivity]. }
    clear HH1 SOK1 MU WM HPc PX.
    destruct PO as (h2 & HT2 & [[-> HH2] | (A & -> & HBA & HH2 & HNEW)]).
    { (* [comment removed for export] *)
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      zstep; if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      do 7 zstep. release_frame FRM ST2 (bv_unsigned sp). zstep.
      apply aevtM_done. unfold mpi_binop_post. flexi 16%nat. exists h2, LB. exists dX, MBEDTLS_ERR_MPI_ALLOC_FAILED.
      split; [reflexivity|]. split; [assumption|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|].
      split; [exact HH2|].
      split. { split; [| cbn; exact SGX]. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own]. rewrite EO.
        split; [exact CHX|]. split; [exact XAL|]. split; [exact X0|]. split; [exact LENX|]. split; [unfold MPI_MAX_LIMBS; dlia|].
        split; [exact N1|]. split; [exact PIN|]. split; [exact PAL| exact PX2]. }
      split; [apply mpd_out_refl; exact NST|].
      split; [exact HPX2|]. split; [exact SOK2|].
      unfold shrink_R. split; [right; split; reflexivity| intros b Hb; left; exact Hb]. }
    (* [comment removed for export] *)
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    pose proof HBA as HBA'. flat constr:(HBA') 5%nat. flclear HBA'. intros A0 A16 _ A4 A5.
    replace (i2 * 4) with (4 * i2) in * by dlia.
    zstep; if_cases KZ; zify_cond KZ; [exfalso; dlia|].
    zstep. zstep.
    zstep; if_cases KP; zify_cond KP; [exfalso; dlia|].
    zstep. replace (Z.shiftl i2 2) with (4 * i2) by (rewrite Z.shiftl_mul_pow2 by dlia; dlia).
    zstep.
    eapply (tail9c i2 i2 A m2 mo2 h2); try eassumption; try reflexivity; try dlia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?D15450681962.93D27151043260.93D27756144151.93D4089920618.93 D55758763098.93L66259998979.9100000@00V00b00c01@01XS2sp1X2xs2nb1i1KS2sp1X2nX2xs2nb1i2Hi1KS2sp1X2xs2nbFS2sp1X2nX2xs2nb1i2Hi3NBX2X01KS2sp1X2nX2xs1i2Hi2X03NRX". (* [comment removed for export] *)
  Lemma from34 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shrink ()) "Pi,$3.Pm1,P,(5.&40.)(11.(5.&8.))Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa0,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Pxs5,(5.&40.)P,(2.$17.VownX,$41.)P,(0.(8.+1.R12.)(8.R12.VnX,))P,(1=.Vnb,VnX,)P,(32.Vxs,R14.)P,(38.$39.R14.VX,(49.VpX,(25.&40.VsgX,)VnX,VpadX,))P,(47.$39.R15.VpX,Vxs,)P,(15.$39.VL,VHI,Vh,VLB,R16.Vmo,)P,(50.(3:.(44.$3.$3.)(45.$3.$3.(20.(1;.&40.Vsp,)+30.)(1;.&40.Vsp,))(4=.(44.$3.$3.)))Vm,R17.)P,(51.$39.Vm,R18.)P,(28.$39.VL,R19.)P,(27.$39.R1:.)P,(1?.$39.R1;.Vlo,(33.(1;.&40.Vsp,)-30.))P,(38.$39.R1<.(33.(1;.&40.Vsp,)-30.)(3:.$37.(3<.R=.)(3:.$37.(3<.Vs3,)(3:.$37.(3<.Vs2,)(3:.$37.(3<.Vs1,)(3:.$37.(3<.Vs0,)(3:.$37.(3<.Vra,)(4=.$37.))))))))(2;.$39.Vmo,(2<.$39.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(2=.Vnb,VdX,VLB,)Vlo,Vm,Vmo,)(2>.(2?.Vra,(25.&40.(33.(1;.&40.Vsp,)-30.))Vgp,Vtp,R1<.R1;.R1:.(25.&40.VX,)(25.&40.$;.)R19.(25.&40.Vnb,)R18.R17.R16.R15.R14.R13.Vs2,(25.&40.R1>.)Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.R10.R?.)VF,(25.&40.+1>>?8.)Vfc,(30.(5.&40.))R1=.(31.$39.)))")
(* [comment removed for export] *).
  Proof.
    intros until xs5. intros EO Hi NBX ZX CHX PX HH1 MU WM SOK1 MI1 ST1 FRM.
    flat constr:(facts) 7%nat. intros XAL X0 LENX NRX SGX XB XS.
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    zstep; if_cases K; zify_cond K.
    - eapply (from3c i m1); try eassumption; dlia.
    - zstep. eapply (from3c nb m1); try eassumption; try dlia. eapply zeros_above_mono; [| exact ZX]. dlia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@D13013243394.108D13567925957.109D27693303193.106D27694993293.108D2966766138.109 D42470608619.107D48711786379.109D49317795049.109D59310778860.84 D59314841581.105L16586317501.101L23100341967.10200000M01J01l02P03703T04104N04^05a06b07=S2sp1X2pX2xs1k1j2Hj3PX03PXB1wS1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL1k1j2Hj2X03PX03PXB2N12P02P41wS2sp1X2nX2pX2xs1k1j2Hj3Hjr3PX03PXBS2sp1X2nX2pX2xs1k1j2Hj3Hjr3PX03PXB1wS2sp1X2nX2pX2xs1k1j2Hj3Hjr3PX03PXB2K11wS2sp1X2pX2xs1k1j2Hj3PX03PXB1wS2sp1X2pX2xs1k1j2Hj3PX03PXB1wS2sp1X2pX2xs1k1j2Hj3PX03PXB1wS2sp2nX1j2Hj3HjrS1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL1k1j2Hj3Hjr2X04LENX3PX03PXB2P02P41NS1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL1k1j2Hj3Hjr2X04LENX3PX03PXB2P02P4S2sp1X2pX2xs1k1j2Hj3PX03PXB". (* [comment removed for export] *)
  Lemma scan_loop : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shrink ()) "Pk,$52.Pj,$3.Pm1,P,(5.&40.)(11.(5.&8.))Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Pys3,(5.&40.)Pxs5,(5.&40.)P,(2.$3.R10.(3>.R11.))P,(2.$17.VownX,$41.)P,(0.(8.+1.R12.)(8.R12.VnX,))P,(1=.Vnb,VnX,)P,(32.Vxs,R14.)P,(38.$39.R14.VX,(49.VpX,(25.&40.VsgX,)VnX,VpadX,))P,(47.$39.R15.VpX,Vxs,)P,(15.$39.VL,VHI,Vh,VLB,R16.Vmo,)P,(50.(3:.(44.$3.$3.)(45.$3.$3.(20.(1;.&40.Vsp,)+30.)(1;.&40.Vsp,))(4=.(44.$3.$3.)))Vm,R17.)P,(51.$39.Vm,R18.)P,(28.$39.VL,R19.)P,(27.$39.R1:.)P,(1?.$39.R1;.Vlo,(33.(1;.&40.Vsp,)-30.))P,(38.$39.R1<.(33.(1;.&40.Vsp,)-30.)(3:.$37.(3<.R>.)(3:.$37.(3<.Vs3,)(3:.$37.(3<.Vs2,)(3:.$37.(3<.Vs1,)(3:.$37.(3<.Vs0,)(3:.$37.(3<.Vra,)(4=.$37.))))))))(2;.$39.Vmo,(2<.$39.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(2=.Vnb,VdX,VLB,)Vlo,Vm,Vmo,)(2>.(2?.Vra,(25.&40.(33.(1;.&40.Vsp,)-30.))Vgp,Vtp,R1<.R1;.R1:.(25.&40.VX,)(25.&40.$;.)(25.&40.R1>.)(25.&40.Vnb,)(25.&40.(46.+4.(20.R1>.+1.)))R19.R18.R17.R16.R15.Vs2,R10.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(25.&40.+1>>=8.)Vfc,(30.(5.&40.))R1=.(31.$39.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xs5; intros Hj EO Hjr NBX ZX CHX PX HH1 MU WM SOK1 MI1 ST1 FRM; [exfalso; dlia|].
    flat constr:(facts) 7%nat. intros XAL X0 LENX NRX SGX XB XS.
    flat constr:((proj1 PX)) 3%nat. intros PX0 PXB _. rewrite u32s_length in PXB.
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    flat constr:(MAX) 2%nat. intros FLt7 _. flat constr:(FLt7) 2%nat. flclear FLt7. intros _ FLt8. flat constr:(FLt8) 5%nat. flclear FLt8. intros _ _ _ _ OX. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX. rewrite EO in OX.
    flat constr:(OX) 4%nat. flclear OX. intros N1 PIN PAL _.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH1)) 2%nat. intros HBR _. flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5.
    unfold mpi_cells in CHX.
    zstep. zstep.
    zstep; if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      eapply (from34 j m1); try eassumption; try dlia.
    - zstep. zstep.
      destruct (nth_error xs (Z.to_nat (j - 1))) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; dlia].
      pose proof (u32arr_read psegs m1 pX xs (j - 1) w _ PX N ltac:(dlia) ltac:(f_equal; dlia)) as RD.
      zstep. clear RD. zstep.
      zstep; if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (WZ : bv_unsigned w mod 2^32 = 0).
        { rewrite bv_unsigned_sx32 in K2. pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(dlia)) as H.
          exact (proj1 (sxz_zero_iff _ H) K2). }
        pose proof (zeros_above_down' xs (j - 1) w ltac:(dlia) ltac:(replace (j - 1 + 1) with j by dlia; exact ZX) N WZ) as ZY'.
        replace (Z_to_bv 64 (4 * (j - 1) + -4)) with (Z_to_bv 64 (4 * (j + -1 - 1))) by (f_equal; dlia).
        replace (j - 1) with (j + -1) in ZY' by dlia.
        eapply (IH (j + -1)); try eassumption; try dlia.
      + (* [comment removed for export] *)
        eapply (from34 j); try eassumption; try dlia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01G0@D12996432337.138D13179664147.129D14791076277.107D14792959895.125D1651690435.134 D19832347127.151D19832479605.154D2160772278.139 D21901036283.151D25188048531.129D26405856937.107D2780666493.129 D32954357680.105D32954357680.109D33556456785.151D34474615098.151D36052405171.129D36052405241.105D36052405241.109D3829201878.151 D3829333332.154 D39409836620.114D39409837249.119D39409837378.117D39409837378.118D39569586757.151D40823233389.107D41951788519.154D44396825738.92 D47955312522.92 D48794105081.107D48794105081.111D48796192577.114D49643072906.129D51284118374.107D52101720110.114D52101720110.117D52101720110.118D52101720110.119D54391984752.117D54391984752.118D54391984881.116D54391984881.117D54391985139.119D54391985534.114D54391985663.113D54398102733.115D54398102733.118D54398102733.119D54398102733.120D54398102733.154D59297271176.151D59308546259.152D59315317366.142D59333019090.154D60209613394.151D60618577829.154D60668600941.152D60675325052.145D60681178462.145D629612293.151  D63528475742.107D6384891599.107 D63936232904.151D64918450769.151D65500066615.139D67875112133.135D68108421313.139D8927508506.92  D9072270588.129 L21146014332.115L22704459656.3  L27339528970.112L31378308326.96 L41953885645.112L41953885645.115L43059660732.94 L45287401080.112L45291547800.106L52478593451.147L59308546259.106L59311069898.147L59336114942.100L59336114942.98 L60616480655.112L64706837497.129R2113957450.129 00000P00Y01>01c02302W03A03d03e03n04D04M04j05G05H05i06J06k07L07`08708H08Y08j09;09<09E09F09V09f0:P0;:0;d0;m0<?0<i0=S0>=0>g0?c0@_0A[0BW0CS0DO0EK0F10FW0G=0Gc0HN0HO0Hn0Ie0J<0JT0Jh0KI0Kk0LP0LQ0Lf0M50M60M70MB0N10N?0NR0NS0Nb0Nm0OF0OO0OP0OQ0On0PC0PU0QN0Qm0RB0RQ0Rg0S90S:0SCS2sp1X2nX2pX2xs2X04LENX3SPB1a2HaS2sp1X2xsS1L3HLS2sp2lo1X2xs3SLO3ACL2X03ACP3SPBS1L3HLS2sp2lo1X2xs3SLO3ACL2X03ACP3SPBS2sp1X2nX2xs3NRXS2sp1X2nX2xs2nb2X03SPB2H22H41A2A02N0S2sp1X2nX2pX2xs2nb2X03SPB2H22H41A2A02N12P0S2sp1X2nX2xs2nb2X04LENX3SPB2H21A2A0FS2sp1X2xsS2sp1X2xs2nb2X03SPB2H4S2sp1X2xsS1L3HLS2sp2lo1X2xs3SLO2X03SPBS1L3HLS2sp2lo1X2xs3SLO2X03SPBFS2sp1X2nX2xs2nb2X03SPB2H21A2A02N0S1L3HLS2sp2lo1X2xs3SLO3ACL2X03SPBS1L3HLS2sp2lo1X2xs3SLO3ACL2X03SPBS1L3HLS2sp2lo1X2xs3SLO3ACL2X03SPBS2sp1X2nX2xs2nb2H21AS2sp1X2nX2pX2xs2nb2H21AS2sp1X2xs1a2H52H6S2sp1X2xs1a2H82H9S2sp1X2xs1a2H72H8S2sp1X2xs1a2H72H8FS2sp1X2xsFS2sp1X2nX2xs3NRXS2sp1X2nX2xs3NRXS1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL2X03SPB2P4S1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL2X03SPB2P4S1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL2X03SPB2P4S2sp1X2xsS1L2sp2lo1X2xs3SLOS1L3HLS2sp2lo1X2xs3SLO3ACL3DHI2X03SPB1a2HaS1L3HLS2sp2lo1X2xs3SLO3ACL3DHI2X03SPB1a2HaS1L3HLS2sp2lo1X2xs3SLO3ACL3DHI2X03SPB1a2HaS1L3HLS2sp2lo1X2xs3SLO3ACL3DHI2X03SPB1a2HaS1L2HI3HLS2sp1h2lo1X2nX2pX2xs4ownX3SLO4HTOP2X03SPB4PRNG1a2NOS1L2HI3HLS2sp1h2lo1X2nX2pX2xs4ownX3SLO4HTOP2X03SPB4PRNG1a2NOS1L2HI3HLS2sp1h2lo1X2nX2pX2xs4ownX3SLO4HTOP2X03SPB4PRNG1a2NOS1L2HI3HLS2sp1h2lo1X2nX2pX2xs4ownX3SLO4HTOP2X03SPB4PRNG1a2NOS1L2HI3HLS2sp1h2lo1X2nX2pX2xs4ownX3SLO4HTOP2X03SPB4PRNG1a2NOS1L2HI3HLS2sp1h2lo1X2nX2pX2xs4ownX3SLO4HTOP2X03SPB4PRNG1a2NOS1L2HI3HLS2sp1h2lo1X2nX2pX2xs4ownX3SLO4HTOP2X03SPB4PRNG1a2NOS1L2HI3HLS2sp1h2lo1X2xs3SLO2X03SPB1a1CS1L2HI3HLS2sp1h2lo1X2xs3SLO2X03SPB1a1CS1L2HI3HLS2sp1h2lo1X2xs3SLO2X03SPB1a1CS1L2HI3HLS2sp1h2lo1X2xs3SLO2X03SPB1a1CS1L2HI3HLS2sp1h2lo1X2xs3SLO2X03SPB1A2A01a1CFS2sp1X2nX1l2X04LENX3SPB1A2A02N0S1L2HI3HLS2sp1h2lo1X2xs2nb3SLO3ACL2X03SPB1A2A02A41a1C1SS2sp1X2nX2pX2xs2nb2H21AS2sp1X2xs2nb2X03SPB1A2A0S2sp1X2nX2pX2xs1A2N1S2sp1X2nX2xs2nb2X03SPB2H21A2A02N0S2sp1X2xs2nb2X03SPB1A2A01a1C1B1k1RS1L2sp1X2xs2nb2X03SPB1A2A01a1C1D1H2H0FS1L2HI2sp1h1X2xs4HTOPS2sp1X2xs2nb2NBFFS2sp1X2xs1AS1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL2X04LENX3SPB2P4S2sp1X2xs2nb1AS2sp1X2nX2xs2X03SPBFS2sp1X2nX2pX2xsS2sp2xw3HxwS2sp1X2nX2pX2xs2X03SPB2N1S2sp1X2xsFFS1L3HLS2sp2lo1X2xs3SLO2X03SPBS2sp1X2nX2pX2xs2nb2H2S2sp1X2nX2xs2nb2H1S1L3HLS2sp2lo1X2nX2pX2xs3SLO3ACL2X04LENX3SPB1A2A03P0'3P4'S2sp1X2nX2xs2nb2NB2X03SPB2H22N0S2sp1X2pX2xs1A2H53P0'S2sp1X2pX2xs2P0S2sp1X2pX2xs2X03SPB2P0S2sp1X2nX2pX2xs2N1FS2sp1X2xs". (* [comment removed for export] *)
  Lemma body : ltac2:(CDefT.buildp (gd_tbl_P_mpi_shrink ()) "Pm1,P,(5.&40.)(11.(5.&8.))Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(38.$39.R>.VX,(49.VpX,(25.&40.VsgX,)VnX,VpadX,))P,(15.$39.VL,VHI,Vh,VLB,R?.Vmo,)P,(50.(3:.(44.$3.$3.)(45.$3.$3.(20.(1;.&40.Vsp,)+30.)(1;.&40.Vsp,))(4=.(44.$3.$3.)))Vm,R10.)P,(51.$39.Vm,R11.)P,(28.$39.VL,R12.)P,(27.$39.R13.)P,(1?.$39.R14.Vlo,(1;.&40.Vsp,))(2;.$39.Vmo,(2<.$39.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(2=.Vnb,VdX,VLB,)Vlo,Vm,Vmo,)(2>.(2?.Vra,Vsp,Vgp,Vtp,R14.R13.R12.Vs0,Vs1,(25.&40.VX,)(25.&40.Vnb,)R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(25.&40.+1>>9<.)Vfc,(30.(5.&40.))R15.(31.$39.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CHX HH MU WM SOK MI ST.
    flat constr:(facts) 7%nat. intros XAL X0 LENX NRX SGX XB XS. pose proof alloc_ceiling_pos as ACP.
    pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MK0. flat constr:((heap_blocks _ _ HI _ _ _ _ HH0)) 2%nat. intros HBR HAP. pose proof (HND _ _ _ _ HH0) as ND.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    unfold mpi_cells in CHX.
    flat constr:(XW) 3%nat. intros XCW XD XP. cbn [dX md_addr md_own md_p md_n] in XCW, XD, XP.
    assert (PXH : ownX = LHeap -> u32arr psegs m pX xs /\ pX + 4 * nX <= alloc_ceiling /\ In (pX, 4 * nX) LB /\ 1 <= nX /\ pX mod 16 = 0).
    { intros EO. flat constr:(MAX) 2%nat. intros FLt9 _. flat constr:(FLt9) 2%nat. flclear FLt9. intros _ FLt10. flat constr:(FLt10) 5%nat. flclear FLt10. intros _ _ _ _ OX'. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX'. rewrite EO in OX'.
      flat constr:(OX') 4%nat. flclear OX'. intros N1 PIN PAL PX. flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5. split; [exact PX|]. split; [exact P4|]. split; [exact PIN|]. split; [exact N1| exact PAL]. }
    assert (NNX : bv_unsigned (zx16 (Z_to_bv 64 nX)) = nX) by (unfold zx16; rewrite !unsigned_lit by dlia; apply Z.mod_small; dlia).
    assert (OC : ownX = LNull \/ ownX = LHeap) by (clear -NST; destruct ownX; [left| right| exfalso; exact (NST eq_refl)]; reflexivity).
    carve_frame 48%nat ST.
    lazymatch type of FR with rw_cells ?sg ?mx ?Aa [CB 48 ?j] =>
      set (JJ := j) in FR; clearbody JJ; change (rw_cells sg mx Aa ([] ++ CB 48 JJ :: [])) in FR;
      apply (rw_cells_split_CB sg mx Aa [] 48 JJ [] [8; 40]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
      cb8_to_c8 FR (@nil cell) end.
    assert (PRNG : 0 <= pX /\ (ownX = LHeap -> 0 < pX /\ pX + 4 * nX <= alloc_ceiling)).
    { destruct OC as [EO|EO].
      - flat constr:(MAX) 2%nat. intros FLt11 _. flat constr:(FLt11) 2%nat. flclear FLt11. intros _ FLt12. flat constr:(FLt12) 5%nat. flclear FLt12. intros _ _ _ _ OX'. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX'. rewrite EO in OX'.
        flat constr:(OX') 2%nat. flclear OX'. intros P0 _. split; [lia|]. intros C; rewrite EO in C; discriminate.
      - flat constr:((PXH EO)) 4%nat. intros _ P4 PIN _. flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 2%nat. intros P0 _. cbn in P0. split; [lia|]. intros _; split; [lia| exact P4]. }
    lazymatch type of MU with ?T => change (lx_hidden T) in MU end. lazymatch type of WM with ?T => change (lx_hidden T) in WM end.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG psegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt psegs mo _ _ MK0).
    lx_run_tac (PLANS [0x3c268; 0x1eed8] [] 60%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
    all: unfold lx_hidden in MU, WM.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hm : munch ?W1 ?mq mx, Hw : wmono _ ?mq' mx |- _ =>
           let MUf := fresh "MUf" in let WMf := fresh "WMf" in
           first [ assert (MUf : munch [(bv_unsigned sp - 48, bv_unsigned sp)] m mx)
                     by (eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact Hm]]; intros xw Hxw; clear -Hxw; cbn in Hxw |- *; lia)
                 | assert (MUf : munch [(bv_unsigned sp - 48, bv_unsigned sp); (X, X + 16)] m mx)
                     by (eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact Hm]]; intros xw Hxw; clear -Hxw; cbn in Hxw |- *; lia) ];
           assert (WMf : wmono psegs m mx) by (eapply wmono_trans; [exact WM| exact Hw]);
           pose proof (Asn1AuxA.HEAP_munch psegs L HI _ _ _ _ _ lo _ HH ACL Hm Hw
             ltac:(intros a Ha NO; cbn in NO; destruct (Z.le_gt_cases X a); [destruct (Z.lt_ge_cases a (X + 16)); [destruct (XCW a ltac:(dlia)) as [C|[C|C]]; [left; dlia| right; left; exact C| right; right; exact C] |]|]; left; dlia)) as HHx;
           pose proof (statics_ok_munch psegs L _ _ _ SOK Hm ltac:(intros a Ha NW; cbn; assert (O1 : ~ (X <= a < X + 16)) by (intros HX; exact (NW (XD a HX Ha))); (flsplit; repeat split); try exact I; dlia)) as SOKx;
           clear Hm Hw HH SOK MU WM
         end end.
    (* [comment removed for export] *)
    1: { apply aevtM_done. unfold mpi_binop_post. flexi 17%nat. exists LB, dX, MBEDTLS_ERR_MPI_ALLOC_FAILED.
         split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [apply mo_frame_refl|]. split; [reflexivity|].
         split; [exact HHx|].
         split; [eapply mpd_at_munch; [exact MAX| exact NST| exact MUf| exact WMf| cbn; split; [generalize XS; dlia| exact I]| intros EO; (flat constr:((PXH EO)) 3%nat; intros _ P4 _); cbn; split; [left; dlia| exact I]]|].
         split; [apply mpd_out_refl; exact NST|].
         split; [eapply heap_presx_frame; [exact MUf| exact WMf| exact HBR| exact DHI| dlia]|].
         split; [exact SOKx|].
         unfold shrink_R. split; [right; split; reflexivity| intros b Hb; left; exact Hb]. }
    (* [comment removed for export] *)
    1: { apply aevtM_done. unfold mpi_binop_post. flexi 17%nat. exists LB, dX, 0.
         split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [apply mo_frame_refl|]. split; [reflexivity|].
         split; [exact HHx|].
         split; [eapply mpd_at_munch; [exact MAX| exact NST| exact MUf| exact WMf| cbn; split; [generalize XS; dlia| exact I]| intros EO; (flat constr:((PXH EO)) 3%nat; intros _ P4 _); cbn; split; [left; dlia| exact I]]|].
         split; [apply mpd_out_refl; exact NST|].
         split; [eapply heap_presx_frame; [exact MUf| exact WMf| exact HBR| exact DHI| dlia]|].
         split; [exact SOKx|].
         unfold shrink_R. split; [| intros b Hb; left; exact Hb]. left. cbn [dX md_sg md_pad md_n]. (flsplit; repeat split); try reflexivity; flia. }
    (* [comment removed for export] *)
    2: { lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
         assert (EO : ownX = LHeap).
         { flat constr:(MAX) 2%nat. intros FLt13 _. flat constr:(FLt13) 2%nat. flclear FLt13. intros _ FLt14. flat constr:(FLt14) 5%nat. flclear FLt14. intros _ _ _ _ OX'. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX'.
           destruct ownX; [exfalso; (flat constr:(OX') 2%nat; flclear OX'; intros _ N0); flia| reflexivity| exfalso; exact (NST eq_refl)]. }
         flat constr:((PXH EO)) 5%nat. intros PXm P4 PIN N1 PAL.
         assert (PX : u32arr psegs m2 pX xs) by (eapply u32arr_transport; [exact PXm| exact MUf| exact WMf|]; cbn; rewrite LENX; split; [left; dlia| exact I]).
         replace (Z_to_bv 64 (4 * nX + -4)) with (Z_to_bv 64 (4 * (nX - 1))) by (f_equal; lia).
         eapply (scan_loop (Z.to_nat nX) nX); try eassumption; try flia.
         apply zeros_above_all. exact LENX. }
    (* [comment removed for export] *)
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1' end.
    clear CHX FR ST MI.
    lazymatch goal with Hc : rw_cells _ m1' X _, Hf : rw_cells _ m1' (bv_unsigned sp + -48) _, Hs : stk _ m1' _ _, Hi : mem_inv _ m1' |- _ =>
      rename Hc into CHX; rename Hf into FR; rename Hs into ST1; rename Hi into MI1 end.
    pose proof (heap_mok _ _ HI _ _ _ _ HHx) as MK1.
    replace (Z_to_bv 64 0x3c268) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc psegs L HI) with (cnt := nb) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by dlia; try eassumption; try reflexivity; try dlia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by dlia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ dlia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match goal with H : heap_pres _ _ _ _ _ m2 |- _ => rename H into HPc end.
    match goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
    match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    match goal with H : mo_frame mo mo2 |- _ => rename H into MF2 end.
    heap_transport HPc.
    lazymatch type of HPc with heap_pres _ _ _ _ ?mb m2 => rename mb into mB end.
    assert (SOK2 : statics_ok psegs L m2) by (eapply statics_ok_heap_pres; [exact SOKx| exact HPc| exact SW]).
    assert (HPX2 : heap_presx psegs L LB (bv_unsigned sp) (mpd_ivs dX) m m2).
    { eapply heap_presx_trans; [| eapply heap_presx_of_pres_sub; [exact HPc| intros b Hb; exact Hb| dlia| dlia]].
      eapply heap_presx_frame; [exact MUf| exact WMf| exact HBR| exact DHI| dlia]. }
    assert (PXH2 : ownX = LHeap -> u32arr psegs m2 pX xs).
    { intros EO. flat constr:((PXH EO)) 4%nat. intros PXm P4 PIN _. pose proof PXm as U. apply u32arr_cells in U.
      assert (U1 : rw_cells psegs mB pX [CB (4 * length xs) (u32s xs)]).
      { eapply rw_cells_transport; [exact U| exact MUf| exact WMf|]. cbn [cells_size csize Nat.add]. cbn. split; [left; dlia| exact I]. }
      apply (heap_pres_rw_cells psegs L LB _ mB m2 _ _ HPc) in U1.
      2: { cbn [cells_size csize Nat.add]. intros a Ha. right; right. exists (pX, 4 * nX). split; [exact PIN| cbn; dlia]. }
      eapply u32arr_of_cells; [exact U1| reflexivity]. }
    clear HHx SOKx MK1 HPc. try clear ST1. try clear MI1.
    destruct PO as (h2 & HT2 & [[-> HH2] | (A & -> & HBA & HH2 & HNEW)]); pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    { (* [comment removed for export] *)
      rewrite TP. apply (lxp_aevtM_of_evt psegs mo2 _ _ MK2).
      lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
      all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
      apply aevtM_done. unfold mpi_binop_post. flexi 16%nat. exists h2, LB. exists dX, MBEDTLS_ERR_MPI_ALLOC_FAILED.
      split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact MF2|]. split; [exact HT2|].
      split; [exact HH2|].
      split. { split; [| cbn; exact SGX]. flat constr:(MAX) 2%nat. intros FLt15 _. flat constr:(FLt15) 2%nat. flclear FLt15. intros _ FLt16. flat constr:(FLt16) 5%nat. flclear FLt16. intros _ _ _ _ OX. cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX |- *.
        split; [assumption|]. split; [exact XAL|]. split; [exact X0|]. split; [exact LENX|]. split; [unfold MPI_MAX_LIMBS; dlia|].
        destruct ownX; [exact OX| | exfalso; exact (NST eq_refl)]. flat constr:(OX) 4%nat. flclear OX. intros N1 PIN PAL _. split; [exact N1|]. split; [exact PIN|]. split; [exact PAL| exact (PXH2 eq_refl)]. }
      split; [apply mpd_out_refl; exact NST|].
      split; [exact HPX2|]. split; [exact SOK2|].
      unfold shrink_R. split; [right; split; reflexivity| intros b Hb; left; exact Hb]. }
    (* [comment removed for export] *)
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 HAP2. pose proof (HND _ _ _ _ HH2) as ND2.
    pose proof HBA as HBA'. flat constr:(HBA') 5%nat. flclear HBA'. intros A0 A16 _ A4 A5. flat constr:(HAP2) 2%nat. flclear HAP2. intros HAPA _.
    assert (XA' : forall a, X <= a < X + 16 -> ~ (A <= a < A + nb * 4)).
    { intros a Ha C. destruct (XCW a Ha) as [S|[[D NS]|([B k] & Hb & R)]]; [dlia| generalize A5; destruct DIMG; dlia| generalize (HAPA B k Hb); cbn in R; dlia]. }
    pose proof (pointwise_apart X 16 A (nb * 4) ltac:(dlia) ltac:(dlia) XA') as XA. clear XA'.
    replace (nb * 4) with (4 * nb) in * by dlia.
    lazymatch type of HNEW with ?T => change (lx_hidden T) in HNEW end.
    rewrite TP. apply (lxp_aevtM_of_evt psegs mo2 _ _ MK2).
    lx_run_tac (PLANS [0x1ef68; 0x1ef50] [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs; unfold lx_hidden in HNEW.
    all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
    all: pose proof MAX as [[_ (_ & _ & _ & _ & OX)] _]; cbn [dX md_addr md_sg md_n md_p md_limbs md_pad md_own] in OX.
    { (* [comment removed for export] *)
      destruct OC as [EO|EO]; rewrite EO in OX.
      2: { exfalso. flat constr:((proj2 PRNG EO)) 2%nat. intros P0' P4'. lazymatch goal with Hz : 0 <= - zlow 64 _ |- _ => unfold zlow in Hz; rewrite Z.mod_small in Hz by flia end. flia. }
      flat constr:(OX) 2%nat. flclear OX. intros P0 N0.
      assert (XS0 : xs = []) by (destruct xs; [reflexivity| cbn [length] in LENX; exfalso; dlia]).
      eapply (store_tail nb A (repeat (Z_to_bv 64 0) (Z.to_nat nb)) m2 mo2 h2 ((A, 4 * nb) :: LB)); try eassumption; try reflexivity; try dlia.
      + rewrite repeat_length. dlia.
      + rewrite XS0, limbs_val_repeat0. reflexivity.
      + left; reflexivity.
      + eapply u32arr_of_cells; [exact HNEW|]. rewrite u32s_repeat0. f_equal. dlia.
      + unfold dX. rewrite P0, EO. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
        split. { intros b [<-|Hb]; [right; left; reflexivity| left; exact Hb]. }
        split. { intros b Hb Hn. right. exact Hb. }
        intros b [].
      + unfold dX. rewrite EO. cbn [mpd_blk md_own md_p md_n]. intros b [<-|[]]. right. intros HinA. generalize (HAPA A (4 * nb) HinA). dlia.
      + intros a Ha. destruct (XCW a Ha) as [C|[C|([B k] & Hb & R)]]; [left; dlia| right; left; exact C| right; right; exists (B, k); split; [right; exact Hb| exact R]]. }
    (* [comment removed for export] *)
    destruct OC as [EO|EO]; rewrite EO in OX.
    { exfalso. flat constr:(OX) 2%nat. flclear OX. intros P0 _. lazymatch goal with Hz : (zlow 64 _ =? zlow 64 0) = false |- _ => rewrite P0 in Hz; cbv in Hz; discriminate Hz end. }
    flat constr:(OX) 4%nat. flclear OX. intros N1 PIN PAL _. flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5.
    pose proof (PXH2 EO) as PX2.
    eapply (tail9c nb nX A m2 mo2 h2); try eassumption; try reflexivity; try dlia.
    apply zeros_above_all. exact LENX.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Walk.

  Lemma P_mpi_shrink_spec : mpi_shrink_stmt psegs L HI P_MPI_SHRINK P_MEMSET_FUNC.
  Proof.
    unfold mpi_shrink_stmt, P_MPI_SHRINK. intros until lo. intros HH MAX NST XW NB ST SLO ACL HTOP SPA DHI TP MI SOK CA -> ->.
    destruct dX as [X sgX nX pX xs padX ownX].
    eapply body; try eassumption.
    - exact (proj1 (proj1 MAX)).
    - apply munch_refl.
    - apply wmono_refl.
  Qed.

End ShrinkP.
