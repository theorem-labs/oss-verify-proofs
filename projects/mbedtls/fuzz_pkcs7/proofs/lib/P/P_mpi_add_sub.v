(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux HeapIface ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiJourney.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_platform_zeroize P_mpi_free P_mpi_addsub P_mpi_cmp
     P_mpi_sub_abs P_mpi_add_abs_W P_mpi_add_abs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_add_sub () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sgn"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.P.P_mpi_cmp.SIGF"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.MpiVal.mpd_out"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "OSSVerify.KrLib.Spec.MpiVal.mpd_ivs"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.P.P_mpi_addsub.binop_keep"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Main.as_frame"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Main.Body.after"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Spec.MpiVal.mpd_abs"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.Spec.MpiOpnd.opnd_at"; "Main.Body.at1"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "OSSVerify.KrLib.P.P_mpi_addsub.mpi_binop_post"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.P.P_mpi_addsub.mpd_writable"; "OSSVerify.KrLib.Spec.Rep.LNull"; "OSSVerify.KrLib.Lib.HeapIface.hl_stack"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_tp"; "OSSVerify.KrLib.Lib.AStep.const_at"; "OSSVerify.KrLib.P.P_mpi_addsub.add_sub_mpi_R"; "OSSVerify.KrLib.P.P_platform_zeroize.P_MEMSET_FUNC"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CmpWalk.
  Variables (raj sp' gp tp t0 t1 t2 s1v a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (X Aa pA nA : Z) (ys : list word) (sAw padA : word).
  Variables (Ba pB nB : Z) (zs : list word) (sBw padB : word).
  Hypothesis CEA : rw_cells psegs m Aa [C8 (Z_to_bv 64 pA); C2 sAw; C2 (Z_to_bv 64 nA); C4 padA].
  Hypothesis HA : bytes_at psegs m pA (u32s ys).
  Hypothesis LA : Z.of_nat (length ys) = nA.
  Hypothesis HnA : 0 <= nA <= 10000.
  Hypothesis ABD : 0 <= Aa /\ Aa + 16 <= 2^64.
  Hypothesis PAB : nA = 0 \/ 0 < pA /\ pA mod 4 = 0.
  Hypothesis CEB : rw_cells psegs m Ba [C8 (Z_to_bv 64 pB); C2 sBw; C2 (Z_to_bv 64 nB); C4 padB].
  Hypothesis HB : bytes_at psegs m pB (u32s zs).
  Hypothesis LB_ : Z.of_nat (length zs) = nB.
  Hypothesis HnB : 0 <= nB <= 10000.
  Hypothesis BBD : 0 <= Ba /\ Ba + 16 <= 2^64.
  Hypothesis PBB : nB = 0 \/ 0 < pB /\ pB mod 4 = 0.
  Hypothesis MI : mem_inv psegs m.

  (* [comment removed for export] *)
  Definition cmpw_post (c : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Lms',$0.(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)Lw,(2.&40.)(1.$3.Lpc,$3.(4.(5.$0.R7.(6.(7.Vraj,Vsp',Vgp,Vtp,Vt0,Vt1,Vt2,(8.&40.VX,)R2.R6.(8.&40.VAa,)(8.&40.VBa,)R5.R4.R3.Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.R1.)Vfc,(9.(2.&40.))Vm,(:.$;.)))(4.(<.(=.$>.)Vm,Vm,)(4.(?.$;.Vm,Vm,)(4.(10.$;.Vm,)(11.(4.(5.$3.R1.+1??60.)(11.(4.(5.$3.O1.+1.)(5.(2.&40.)R2.Vs1v,))(4.(5.$3.O1.=)(5.(2.&40.)R2.(8.&40.+1.)))))(4.(5.$3.R1.+1??:<.)(4.(5.$3.O1.-1.)(5.(2.&40.)R2.Vs1v,))))))))))))))")
(* [comment removed for export] *).

  Let CMP := Z.sgn (lval ys nA - lval zs nB).
  Let POST := cmpw_post CMP.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0@L10199556340.75 L11014201954.78 L11014202083.77 L11962491140.75 L14561275693.78 L16256852529.73 L1966108301.77  L21734144936.78 L21750432760.78 L23355682316.78 L23917382008.78 L25572164514.78 L29010565666.66 L30163642507.103L37737165979.75 L42000496269.69 L42000496398.71 L42468637227.74 L42470501281.75 L54425554052.72 L54425647149.78 L54427583239.73 L55515195535.75 L56834426490.78 L59308628179.1  L59308628179.4  L59435147825.73 L66151422254.63 00000N01501\02:02b03=04>04e05I06J07@08D08`08a08b0;?0=]0>A0>e0?F0?m0@N0@O0A30A70AB0A]0B?S2pA2nA2ys2pB2nB2zs3CMP1k1r2HkS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2HT2wx2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2HT2wx2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2HkS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk3Rn'2wx2wyS2nA2ys2Ba2nB2zs3CMP1k1r2HkS2pA2nA2ys2pB2nB2zs3PAB3PBB3CMP1k1r2Hk2Rn3Rn'2HT2wx2wy3LXr3LYr2K1S2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Rn2wx2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2wx2wyS2pA2nA2ys2pB2nB2zs3PAB3PBB3CMP1k1r2Hk2Rn3Rn'2HT2wx2wy3LXr3LYr2K2S2pA2nA2ys2pB2nB2zs3PAB3PBB3CMP1k1r2Hk2Rn3Rn'2HT2wx2wyS2pA2nA2ys2pB2nB2zs3PAB3PBB3CMP1k1r2Hk2Rn3Rn'2HT2wx2wy3LXr3LYr2K12K2S2ys2nB2zs3HnB1k1r2Hk2Hr3Rn'FFS3raj3sp'2gp2tp2t02t12t23s1v2a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X2Aa2pA2nA2ys2Ba2pB2nB2zs2LA3PAB3PBB3CMP4POST1k1r2a42a52Hk2Rn3Rn'2HT2NXS3raj3sp'2gp2tp2t02t12t23s1v2a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X2Aa2pA2nA2ys2Ba2pB2nB2zs3PAB3LB_3PBB3CMP4POST1k1r2a42a52Hk2Rn3Rn'2HT2NYS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2wx2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2wx2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2HTS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2HT2wx2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2HTFS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2wx2wyS2K0S1k1r2Hk2K0S2Aa2nA2ys2nB2zs3CMP1k1r2HkS2pA2nA2ys2pB2nB2zs3CMP1r2Hk2Hr2HT". (* [comment removed for export] *)
  #[using="pA sAw padA pB sBw padB CEA HA LA PAB CEB HB LB_ HnB PBB MI"] Lemma as_loop3 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pk,$12.Pr,$3.Pw10,(2.&40.)Pw13,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)P,(5.$12.(13.R5.)R6.)P,(14.=R6.)P,(14.R7.VnA,)P,(14.R8.VnB,)P,(5.$3.VCMP,(15.(16.(17.Vys,R9.)(17.Vzs,R9.))))P,(5.(2.&40.)R9.(8.&40.(18.R:.+1.)))P,(5.(2.&40.)R9.(8.&40.(16.(19.+4.R;.)+4.)))(1:.$;.VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,Vt0,Vt1,Vt2,(8.&40.VX,)Vs1v,R;.(8.&40.VAa,)(8.&40.VBa,)R:.R9.R8.Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+1??80.)Vfc,(9.(2.&40.))Vm,(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w10 w13 a4 a5 Hk Hr Rn Rn' HT -> ->.
    - assert (r = 0) as -> by lia.
      pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
      zstep. zstep. if_cases K0; zify_cond K0; [| exfalso; clear - K0; lia].
      zstep. zstep. apply evt_done. unfold POST, cmpw_post. deexists 6. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      left. split; [reflexivity|]. right. split; [| reflexivity]. rewrite HT, !lval_0. reflexivity.
    - pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
      zstep. zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0 Hk; lia|].
      destruct (nth_error ys (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; lia].
      destruct (nth_error zs (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; lia].
      pose proof (u32ro_read psegs m pA ys (r - 1) wx _ HA NX ltac:(lia) eq_refl) as RDX.
      pose proof (u32ro_read psegs m pB zs (r - 1) wy _ HB NY ltac:(lia) eq_refl) as RDY.
      zstep. zstep. zstep. zstep. zstep. zstep. clear RDX RDY.
      pose proof (limb32_of_read ys r wx NX) as LXr. pose proof (limb32_of_read zs r wy NY) as LYr.
      pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(lia)) as Bx.
      pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(lia)) as By.
      zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
      + (* [comment removed for export] *)
        apply (proj1 (sxz_lt_iff _ _ By Bx)) in K1.
        apply evt_done. unfold POST, cmpw_post. deexists 6. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
        left. split; [reflexivity|]. left. split; [| reflexivity]. rewrite HT. apply (cmp_step_gt ys zs r); lia.
      + apply (proj1 (sxz_le_iff _ _ Bx By)) in K1.
        zstep. zstep. if_cases K2; zify_cond K2; rewrite ?bv_unsigned_sx32 in K2.
        * (* [comment removed for export] *)
          apply (proj1 (sxz_le_iff _ _ By Bx)) in K2.
          eapply (IH (r - 1)); [lia| lia| lia| lia| rewrite HT; apply (cmp_step_eq ys zs r); lia| f_equal; lia| f_equal; lia].
        * (* [comment removed for export] *)
          apply (proj1 (sxz_lt_iff _ _ Bx By)) in K2.
          apply evt_done. unfold POST, cmpw_post. deexists 6. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
          right. split; [reflexivity|]. split; [| reflexivity]. rewrite HT. apply (cmp_step_lt ys zs r); lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L10351954010.70L10352001614.69L10907032063.73L13151177730.73L2005344302.74 L23444100755.70L27601760771.73L32954672704.69L32954672833.68L41415825381.70L44872450572.72L45272398924.70L51202549169.70L63517537406.70L66253296149.66L66253710909.68L66253711036.6900000L00h01F01c02@02\03=03R03g04@04^05<05U06106D06Y077S2pA2nA2ys2pB2nB2zs3CMP1i2I1S2pA2nA2ys2pB2nB2zs3CMP1i2I1S2pA2nA2ys2pB2nB2zs3CMP1i1j2K2S2pA2nA2ys2pB2nB2zs3CMP1i1j1HS2pA2nA2ys2pB2nB2zs3CMP1i1j1HS2pA2nA2ys2pB2nB2zs3CMP1i2I1S2pA2nA2ys2pB2nB2zs3CMP1i1j2K12K2S2ys2nB2zs3HnB1i1j2J1S2ys2nB2zs3HnB1i1j2J1S2pA2nA2ys2pB2nB2zs3CMP1iS2pA2nA2ys2pB2nB2zs3CMP1i1j2K1S2pA2nA2ys2pB2nB2zs3CMP1i1j2J1S2pA2nA2ys2pB2nB2zs3CMP1iS2pA2nA2ys2pB2nB2zs3CMP1i2J1S2nA2ys2zs3HnA1i2I1S2nA2ys2zs3HnA1i1j2I1S2nA2ys2nB2zs3HnB1i1j2I12J12K1". (* [comment removed for export] *)
  #[using="pA sAw padA pB sBw padB CEA HA LA HnA PAB CEB HB LB_ HnB PBB MI"] Lemma as_decide : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pi,$3.Pj,$3.Pa4,(2.&40.)Pa5,(2.&40.)P,(1;.Vys,VnA,R4.)P,(1;.Vzs,VnB,R4.)(1:.$;.VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,Vt0,Vt1,Vt2,(8.&40.VX,)Vs1v,(8.&40.R6.)(8.&40.VAa,)(8.&40.VBa,)(8.&40.R5.)R4.R3.Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+1??5<.)Vfc,(9.(2.&40.))Vm,(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros i j a4 a5 SX SY. dpose SX as (I1 & I2 & I3). dpose SY as (J1 & J2 & J3).
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (lval_range ys i ltac:(lia)) as RX. pose proof (lval_range zs j ltac:(lia)) as RY.
    zstep. if_cases K1; zify_cond K1.
    2:{ (* [comment removed for export] *)
        apply evt_done. unfold POST, cmpw_post. deexists 6. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
        left. split; [reflexivity|]. left. split; [| reflexivity]. unfold CMP. apply Z.sgn_pos. pose proof (SIGF_lt ys nA i zs nB j SX SY ltac:(lia)). lia. }
    zstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      apply evt_done. unfold POST, cmpw_post. deexists 6. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      right. split; [reflexivity|]. split; [| reflexivity]. unfold CMP. apply Z.sgn_neg. pose proof (SIGF_lt zs nB j ys nA i SY SX ltac:(lia)). lia. }
    assert (j = i) as -> by lia. clear K1 K2.
    zstep. zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    eapply (as_loop3 (Z.to_nat i) i); [reflexivity| lia| lia| lia| | f_equal; lia| f_equal; lia].
    unfold CMP. rewrite I2, J2. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11014116938.72L11014201954.72L13036769295.72L19168960846.70L23917382008.72L23970764156.70L26188898998.72L27579345746.72L31326834835.72L34825717398.62L34827897883.67L42468637227.69L54425554052.68L59906749071.72L64930767917.72L66607535575.7200000T01801_02=02e03@03a04S05:07?09Q0:20:S0;80;_0<CS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wy2K2S2pA2nA2ys2pB2nB2zs3CMP1k1r2HkS2pA2nA2ys2pB2nB2zs3PBB3CMP1k1r2Hk2Hr2wyS2ys2nB2zs3HnB1k1r2Hk2Hr2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wy3LYr2K13PBB2K2S2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wy2K2S3raj3sp'2gp2tp2t02t12t23s1v2a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X2Aa2pA2nA2ys2Ba2pB2nB2zs3CMP4POST1i1r2a52Hk2HrS3raj3sp'2gp2tp2t02t12t23s1v2a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X2Aa2pA2nA2ys2Ba2pB2nB2zs3LB_3PBB3CMP4POST1k1i1r2a52Hk2Hr2NYS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2HrS2pA2nA2ys2pB2nB2zs3HnB3CMP1k1r2Hk2wyS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wy2K2S2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wy". (* [comment removed for export] *)
  #[using="pA sAw padA sBw padB CEA HA LA HnA PAB CEB HB LB_ HnB PBB MI"] Lemma as_loop2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pk,$12.Pi,$3.Pr,$3.Pw13,(2.&40.)Pw14,(2.&40.)Pa5,(2.&40.)P,(5.$12.(13.R4.)R6.)P,(4.(14.+1.R5.)(14.R5.VnB,))P,(1;.Vys,VnA,R7.)P,(5.$3.(17.Vzs,VnB,)(17.Vzs,R7.))P,(5.(2.&40.)R7.(8.&40.R8.))P,(5.(2.&40.)R7.(8.&40.(16.(18.VpB,(19.+4.R9.))+4.)))(1:.$;.VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,Vt0,Vt1,Vt2,(8.&40.VX,)Vs1v,(8.&40.R;.)(8.&40.VAa,)(8.&40.VBa,)R9.R8.R7.Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+1??48.)Vfc,(9.(2.&40.))Vm,(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i r w13 w14 a5 Hk Hr SX INV -> ->; [lia|].
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct (nth_error zs (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; lia].
    pose proof (u32ro_read psegs m pB zs (r - 1) wy _ HB NY ltac:(lia) eq_refl) as RDY.
    zstep. clear RDY. pose proof (limb32_of_read zs r wy NY) as LYr.
    pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(lia)) as By.
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - assert (NZ : limb32 zs (Z.to_nat (r - 1)) <> 0) by (rewrite LYr; intros E; apply K1; rewrite E; reflexivity).
      apply as_decide; [exact SX|]. split; [lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [lia| exact NZ].
    - apply (proj1 (sxz_zero_iff _ By)) in K1.
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply (IH i (r - 1)); [lia| lia| exact SX| rewrite INV; apply lval_drop_zero; lia| f_equal; lia| f_equal; lia].
      + replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; lia).
        apply as_decide; [exact SX|]. split; [lia|]. split; [| left; reflexivity].
        rewrite INV, (lval_drop_zero zs r) by lia. replace (r - 1) with 0 by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L16256852529.62L38258112413.63L41415942734.63L43665079170.61L4475845362.63 L47221911869.62L65775916289.6300000D00_01601D01[02602TS2nA2ys2Ba2nB2zs3CMPS2pA2nA2ys2pB2nB2zs3HnB3CMPS2pA2nA2ys2pB2nB2zs3CMPS2ys2nB2zs3HnBS2pA2nA2ys2pB2nB2zs3CMPS2pA2nA2ys2pB2nB2zs3HnB3CMPS2pA2nA2ys2pB2nB2zs3HnB3CMP2K0". (* [comment removed for export] *)
  #[using="pA sAw padA pB sBw padB CEA HA LA HnA PAB CEB HB LB_ HnB PBB MI"] Lemma as_stage2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pi,$3.Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)P,(1;.Vys,VnA,R4.)(1:.$;.VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,Vt0,Vt1,Vt2,(8.&40.VX,)Vs1v,(8.&40.R5.)(8.&40.VAa,)(8.&40.VBa,)R4.R3.R2.Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+1??30.)Vfc,(9.(2.&40.))Vm,(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros i a3 a4 a5 SX.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. rewrite zx16_small by lia. zstep. if_cases K0; zify_cond K0.
    - apply as_decide; [exact SX|]. split; [lia|]. split; [reflexivity| left; exact K0].
    - zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      eapply (as_loop2 (Z.to_nat nB) i nB); [reflexivity| lia| exact SX| reflexivity| reflexivity| f_equal; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11014116938.71L11014201954.71L1615606892.66 L1617821538.61 L1962781522.71 L23917382008.71L23970764156.69L31022272840.71L31326834835.71L31686774790.69L42468637611.68L49887215376.71L50962858877.71L54425554183.67L64912137160.71L64930767917.7100000T01803J05P06B06j07E07j08Q08o09P0:40:U0;60;]0<DS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wxS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wxS3raj3sp'2gp2tp2t02t12t23s1v2a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X2Aa2pA2nA2ys2Ba2pB2nB2zs2LA3PAB3CMP4POST1k1r2a42a52Hk2Hr2NXS3raj3sp'2gp2tp2t02t12t23s1v2a62a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m1X2Aa2pA2nA2ys2Ba2pB2nB2zs3CMP4POST1r2a42a52Hk2HrS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wx3LXr2K13PAB2K2S2pA2nA2ys2pB2nB2zs3PAB3CMP1k1r2Hk2Hr2wxS2nA2ys2zs3HnA1k1r2Hk2Hr2wxS2pA2nA2ys2pB2nB2zs3HnA3CMP1k1r2Hk2wxS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wx2K2S2pA2nA2ys2pB2nB2zs3CMP1k1r2HkS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2wxS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wxS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2wxS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2HrS2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wx2K2S2pA2nA2ys2pB2nB2zs3CMP1k1r2Hk2Hr2wx2K2". (* [comment removed for export] *)
  #[using="sAw padA pB sBw padB CEA HA LA HnA PAB CEB HB LB_ HnB PBB MI"] Lemma as_loop1 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pk,$12.Pr,$3.Pw10,(2.&40.)Pw13,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)P,(5.$12.(13.R5.)R6.)P,(4.(14.+1.R6.)(14.R6.VnA,))P,(5.$3.(17.Vys,VnA,)(17.Vys,R7.))P,(5.(2.&40.)R7.(8.&40.R8.))P,(5.(2.&40.)R7.(8.&40.(16.(18.VpA,(19.+4.R9.))+4.)))(1:.$;.VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,Vt0,Vt1,Vt2,(8.&40.VX,)Vs1v,R9.(8.&40.VAa,)(8.&40.VBa,)R8.R7.R6.Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+1??1<.)Vfc,(9.(2.&40.))Vm,(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros r w10 w13 a4 a5 Hk Hr INV -> ->; [lia|].
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct (nth_error ys (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; lia].
    pose proof (u32ro_read psegs m pA ys (r - 1) wx _ HA NX ltac:(lia) eq_refl) as RDX.
    zstep. clear RDX. pose proof (limb32_of_read ys r wx NX) as LXr.
    pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(lia)) as Bx.
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - assert (NZ : limb32 ys (Z.to_nat (r - 1)) <> 0) by (rewrite LXr; intros E; apply K1; rewrite E; reflexivity).
      apply as_stage2. split; [lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [lia| exact NZ].
    - apply (proj1 (sxz_zero_iff _ Bx)) in K1.
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply (IH (r - 1)); [lia| lia| rewrite INV; apply lval_drop_zero; lia| f_equal; lia| f_equal; lia].
      + replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; lia).
        apply as_stage2. split; [lia|]. split; [| left; reflexivity].
        rewrite INV, (lval_drop_zero ys r) by lia. replace (r - 1) with 0 by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L32980531841.61L35693574334.62L41415942734.62L47608523970.62L5290576834.62 L59435147825.61L61814434366.6000000K00f01=01[02202F02TS2pA2nA2ys2pB2nB2zs3HnA3CMPS2pA2nA2ys2pB2nB2zs3HnA3CMPS2pA2nA2ys2pB2nB2zs3CMPS2pA2nA2ys2pB2nB2zs3HnA3CMP2K0S2pA2nA2ys2pB2nB2zs3CMPS2Aa2nA2ys2nB2zs3CMPS2nA2ys2zs3HnA". (* [comment removed for export] *)
  #[using="pA sAw padA pB sBw padB CEA HA LA HnA PAB CEB HB LB_ HnB PBB MI"] Lemma as_cmp : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pa0,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)(1:.$;.VPOST,(6.(7.Vraj,Vsp',Vgp,Vtp,Vt0,Vt1,Vt2,(8.&40.VX,)Vs1v,R4.(8.&40.VAa,)(8.&40.VBa,)R3.R2.R1.Va6,Va7,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(8.&40.+1??04.)Vfc,(9.(2.&40.))Vm,(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros a0 a3 a4 a5.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. rewrite zx16_small by lia. zstep. if_cases K0; zify_cond K0.
    - apply as_stage2. split; [lia|]. split; [reflexivity| left; exact K0].
    - zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      eapply (as_loop1 (Z.to_nat nA) nA); [reflexivity| lia| reflexivity| reflexivity| f_equal; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End CmpWalk.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L24059859474.3000009S2d12d21D". (* [comment removed for export] *)
Lemma mpd_sep_sym : forall d1 d2, mpd_sep d1 d2 -> mpd_sep d2 d1.
Proof. intros d1 d2 [E|D]; [left; symmetry; exact E| right; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
Definition P_ADD_SUB_MPI' : Z := 0x1fec4.

(* [comment removed for export] *)
Section Main.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr psegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Variable MSF : Z.
  Hypothesis HADD : mpi_add_abs_stmt' psegs L HI P_MPI_ADD_ABS MSF.
  Hypothesis HSUB : mpi_sub_abs_stmt' psegs L HI P_MPI_SUB_ABS MSF.

  (* [comment removed for export] *)
  Definition as_frame (j0 : list byte) (ra s0 s1 : word) : list cell := [CB 8 j0; C8 s1; C8 s0; C8 ra].

  Section Body.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m : mem) (mo : Model) (h : HST psegs L HI) (LB : list blk) (lo : Z) (flip : Z)
              (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own)
              (Aa sA nA pA : Z) (ys : list word) (padA : word) (ownA : limb_own)
              (Ba sB nB pB : Z) (zs : list word) (padB : word) (ownB : limb_own).
    Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
    Local Notation dA := (mkMPD Aa sA nA pA ys padA ownA).
    Local Notation dB := (mkMPD Ba sB nB pB zs padB ownB).
    Hypothesis FLIP : flip = 1 \/ flip = -1.
    Hypothesis HH : HEAP psegs L HI h LB m mo.
    Hypothesis MX : mpd_at psegs m LB dX.
    Hypothesis MA : mpd_at psegs m LB dA.
    Hypothesis MB : opnd_at psegs m LB (bv_unsigned sp) dB.
    Hypothesis SXA : mpd_sep dX dA.
    Hypothesis SXB : mpd_sep dX dB.
    Hypothesis SAB : mpd_sep dA dB.
    Hypothesis NST : ownX <> LStatic.
    Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
    Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
    Hypothesis CRA : client_range L LB lo Aa 16.
    Hypothesis CRAL : ownA = LHeap -> client_range L LB lo pA (4 * nA).
    Hypothesis CRB : client_range L LB lo Ba 16.
    Hypothesis CRBL : ownB = LHeap -> client_range L LB lo pB (4 * nB).
    Hypothesis XW : mpd_writable L LB (bv_unsigned sp) (heap_top psegs L HI h) dX.
    Hypothesis XLS : ownX <> LNull -> pX + 4 * nX <= lo \/ bv_unsigned sp <= pX.
    Hypothesis SLO : lo <= bv_unsigned sp - 224 - hl_stack L.
    Hypothesis ACL : alloc_ceiling <= lo.
    Hypothesis HTOP : bv_unsigned sp <= heap_top psegs L HI h.
    Hypothesis SPA : bv_unsigned sp mod 16 = 0.
    Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
    Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
    Hypothesis SOK : statics_ok psegs L m.
    Hypothesis CA : const_at L MSF 8.
    Hypothesis MI0 : mem_inv psegs m.
    Hypothesis ST0 : stk psegs m lo (bv_unsigned sp).

    Let POST := mpi_binop_post psegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX (add_sub_mpi_R flip LB dX dA dB) lo m mo.
    Let VAL := mpd_val dA + flip * mpd_val dB.

    (* [comment removed for export] *)
    Definition after (j0 : list byte) (m1 m' : mem) (mo' : Model) (h' : HST psegs L HI) (LB' : list blk) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "(4.(10.$;.O5.)(4.(1<.$;.O5.Vlo,(16.(1=.&40.Vsp,)+20.))(4.(1>.Vmo,O4.)(4.(5.$3.(1?.$;.VL,VHI,O3.)(1?.$;.VL,VHI,Vh,))(4.(20.$;.VL,VHI,O3.O2.O5.O4.)(4.(21.$;.O5.O2.O1.)(4.(22.VLB,(23.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)O2.O1.)(4.(24.$;.VL,VLB,(16.(1=.&40.Vsp,)+20.)(25.(23.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))O6.O5.)(4.(26.$;.VL,O5.)(4.(27.VLB,(23.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)O1.)(4.(28.$;.O5.(16.(1=.&40.Vsp,)+20.)(29.O7.Vra,Vs0,Vs1,))(4.(<.(2:.(2;.$3.$3.)(2<.$3.$3.(16.(1=.&40.Vsp,)+20.)(1=.&40.Vsp,))(=.(2;.$3.$3.)))Vm,O6.)(?.$;.Vm,O6.)))))))))))))")
(* [comment removed for export] *).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L22219771718.1 L26825553190.4 L32436940338.1 L38948636245.0 L39409930731.3 L41560720338.7 L46602796124.7 L48076008077.6 L52437843788.6 L54398102733.9 L59314873579.11L59656785403.11L59696753857.1 L774765788.5   00000400?00C00D00L00]01301H01[02502R02l03003AS2spS1X2n'2p'1HS2spSS1X1a2NOS1L3HLS2sp2lo3SLOS1L3HLS2sp2lo1X3SLO2XSS1L3HLS2sp2lo3SLO3ACLS1X2nX2pX4ownX1a2HoS1L2HI3HLS2sp1h2lo3SLO1a1CS1X2nX2pX1a3Ha'1q1k1R2E12E21HS1L2HI3HLS2sp1h2lo3SLO1a1CS2spS1L3HLS2sp2lo3SLO". (* [comment removed for export] *)
    #[using="HLS DIMG HH MX SXA SXB NST OA OB XW XLS SLO ACL DHI"] Lemma as_FIN : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pj0,(2=.(2.&8.))Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Px9,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pm1,P,(2.&40.)(2>.(2.&8.))Pm',P,(2.&40.)(2>.(2.&8.))Pmo',$2?.Ph',(30.$;.VL,VHI,)PLB',(2=.$31.)PdX',$32.Pw,$3.Psg,$3.P,(33.R1:.R8.R7.R6.R5.R4.R3.)P,(5.(2.&40.)R16.(8.&40.R3.))P,(5.$3.(34.R4.(35.+2.+10.))(34.R3.(35.+2.+10.)))P,(11.(5.$3.R4.+1.)(5.$3.R4.-1.))P,(5.$3.(19.R5.(36.R7.))VVAL,)(37.$;.R;.VPOST,(6.(7.R1;.(8.&40.(16.(1=.&40.Vsp,)+20.))Vgp,Vtp,R1>.R1=.R1<.(8.&40.VX,)R1:.R19.R18.R17.R16.R15.R14.R13.R12.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(8.&40.+1??<8.)Vfc,(9.(2.&40.))R<.(:.$;.)))")
(* [comment removed for export] *).
    Proof.
      intros until sg. intros AF -> WS SG HV.
      ddestruct AF as (MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & BK2 & FR2 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
      ddestruct XW as (XCW & XDW & XP). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in XCW, XDW, XP.
      pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR DHI ACL ltac:(clear - SLO HLS; lia)) as XS.
      destruct dX' as [X' sg' n' p' xs' pad' own']. ddestruct BK2 as (EA & EP & FRS & NMO). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in EA, EP, NMO. subst X' pad'.
      pose proof MX2 as [(CX2 & XAL & X0 & LEN2 & NR2 & OWN2) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold mpi_cells in CX2.
      dpose OUT2 as (_ & NS2 & O3 & O4 & O5). cbn [md_addr md_own] in NS2.
      pose proof (conj HH2 I) as HH2c. clear HH2. pose proof (conj SOK2 I) as SOK2c. clear SOK2. pose proof (conj FR2 I) as FR2c. clear FR2.
      pose proof (munch_refl [(X, X + 16)] m') as MU. pose proof (wmono_refl psegs m') as WM.
      zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m'' end.
      (* [comment removed for export] *)
      match goal with CX : rw_cells psegs m'' X [C8 _; C2 (Z_to_bv 64 ?v); _; _] |- _ =>
        pose proof (rw_cells_C2_congr psegs m'' X [C8 (Z_to_bv 64 p')] v sg [C2 (Z_to_bv 64 n'); C4 padX] CX) as CX3 end.
      cbn [app] in CX3.
      match goal with MI3 : mem_inv psegs m'' |- _ => rename MI3 into MIq end.
      destruct HH2c as [HH2 _]. destruct SOK2c as [SOK2 _]. destruct FR2c as [FR2 _].
      assert (FR3 : rw_cells psegs m'' (bv_unsigned sp - 32) (as_frame j0 ra s0 s1)).
      { eapply rw_cells_transport; [exact FR2| exact MU| exact WM|]. unfold as_frame. cbn. clear - XS SLO HLS. lia. }
      unfold as_frame in FR3.
      zstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 (bv_unsigned sp - 32 + 32)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; clear; lia). rewrite Z_to_bv_bv_unsigned.
      zstep.
      apply aevtM_done. unfold POST, mpi_binop_post. deexists 14. dexists m'', mo', h', LB', (mkMPD X sg n' p' xs' padX own'), 0.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [reflexivity|]. split; [exact MIq|].
      split; [eapply stk_release in FR3; [| exact ST2| clear - SLO HLS ACL ACP; lia];
              cbn [cells_size csize Nat.add] in FR3; replace (bv_unsigned sp - 32 + Z.of_nat 32) with (bv_unsigned sp) in FR3 by (clear; lia); exact FR3|].
      split; [exact MF2|]. split; [exact HT2|].
      split. { eapply (HEAP_munch psegs L HI) with (SP := lo); [exact HH2| exact MU| exact WM| exact ACL|].
               intros a Ha NO. cbn in NO. rewrite HT2. assert (Ha' : X <= a < X + 16) by (clear - NO; lia).
               destruct (XCW a Ha') as [C|[C|([q k] & Hq & R)]]; [left; clear - C SLO HLS; lia| right; left; exact C| right; right].
               exists (q, k). split; [| exact R]. apply O4; [exact Hq|]. cbn in R. unfold mpd_blk; cbn [md_own md_p md_n].
               destruct ownX; try (intros []; fail). intros [E|[]]. injection E as E1 E2. pose proof (XP eq_refl). clear - H Ha' R E1 E2. lia. }
      split. { split; [| exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [apply CX3; rewrite WS; reflexivity|].
               split; [exact XAL|]. split; [exact X0|]. split; [exact LEN2|]. split; [exact NR2|].
               destruct own'; [exact OWN2| | exfalso; exact (NS2 eq_refl)]. ddestruct OWN2 as (Q1 & Q2 & Q3 & Q4).
               split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. eapply u32arr_transport; [exact Q4| exact MU| exact WM|]. cbn.
               pose proof (new_limbs_apart_range psegs L HI h' LB LB' m' m' mo' lo dX (mkMPD X sg' n' p' xs' padX LHeap) X 16 HH2 MX2 OUT2 FRS ACL (proj1 DIMG) (proj2 DIMG)) as NL.
               cbn [md_addr md_own md_p md_n] in NL. rewrite LEN2.
               destruct (NL ltac:(intros a Ha; destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C HTOP SLO HLS ACL; lia| right; left; exact C| right; right; exact C]) ltac:(clear; lia) XP eq_refl);
                 clear - H; lia. }
      split; [eapply mpd_out_ext; [exact OUT2| reflexivity| cbn; exact NS2| reflexivity]|].
      split. { eapply heap_presx_trans; [eapply heap_presx_frame; [exact MU1| exact WM1| exact HBR| exact DHI| clear - ACL SLO HLS; lia]|].
               eapply heap_presx_trans; [eapply heap_presx_weaken; [exact HPX2| clear; lia| intros a Ho; exact Ho]|].
               eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. unfold mpd_ivs in Ho. cbn in Ho |- *. split; [| exact I]. clear - Ho. lia. }
      split; [eapply statics_ok_munch; [exact SOK2| exact MU|]; intros a Hd NW; cbn; split; [| exact I]; intros C; exact (NW (XDW a C Hd))|].
      split; [| split; [reflexivity| split; [reflexivity| split; [exact FRS| cbn [md_n]; exact NMO]]]].
      left. split; [reflexivity|]. unfold mpd_val, mpd_abs in *. cbn [md_sg md_limbs] in *. exact HV.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L22219771718.1L32436940338.1L41560720338.7L48076008077.6L59696753857.100000400800I00^00bS2spS2spS1L3HLS2sp2lo3SLOS1L3HLS2sp2lo3SLO3ACLS2sp". (* [comment removed for export] *)
    #[using="HLS HH SLO ACL DHI"] Lemma as_ERR : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pj0,(2=.(2.&8.))Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Px9,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pm1,P,(2.&40.)(2>.(2.&8.))Pm',P,(2.&40.)(2>.(2.&8.))Pmo',$2?.Ph',(30.$;.VL,VHI,)PLB',(2=.$31.)PdX',$32.P,(33.R17.R6.R5.R4.R3.R2.R1.)(37.$;.R5.VPOST,(6.(7.R14.(8.&40.(16.(1=.&40.Vsp,)+20.))Vgp,Vtp,R17.R16.R15.(8.&40.VX,)R13.(8.&40.$38.)R12.R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(8.&40.+1??=0.)Vfc,(9.(2.&40.))R6.(:.$;.)))")
(* [comment removed for export] *).
    Proof.
      intros until dX'. intros AF.
      ddestruct AF as (MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & BK2 & FR2 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
      unfold as_frame in FR2.
      pose proof (munch_refl ([] : list ivl) m') as MU. pose proof (wmono_refl psegs m') as WM.
      zstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 (bv_unsigned sp - 32 + 32)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; clear; lia). rewrite Z_to_bv_bv_unsigned.
      zstep.
      apply aevtM_done. unfold POST, mpi_binop_post. deexists 14. dexists m', mo', h', LB', dX', MBEDTLS_ERR_MPI_ALLOC_FAILED.
      split; [reflexivity|]. split; [exact MI2|].
      split; [eapply stk_release in FR2; [| exact ST2| clear - SLO HLS ACL ACP; lia]; cbn [cells_size csize Nat.add] in FR2;
              replace (bv_unsigned sp - 32 + Z.of_nat 32) with (bv_unsigned sp) in FR2 by (clear; lia); exact FR2|].
      split; [exact MF2|]. split; [exact HT2|]. split; [exact HH2|]. split; [exact MX2|]. split; [exact OUT2|].
      split. { eapply heap_presx_trans; [eapply heap_presx_frame; [exact MU1| exact WM1| exact HBR| exact DHI| clear - ACL SLO HLS; lia]|].
               eapply heap_presx_weaken; [exact HPX2| clear; lia| intros a Ho; exact Ho]. }
      split; [exact SOK2|]. split; [right; reflexivity| exact BK2].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition at1 (j0 : list byte) (m1 : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "(4.(10.$;.O1.)(4.(1<.$;.O1.Vlo,(16.(1=.&40.Vsp,)+20.))(4.(28.$;.O1.(16.(1=.&40.Vsp,)+20.)(29.O2.Vra,Vs0,Vs1,))(4.(20.$;.VL,VHI,Vh,VLB,O1.Vmo,)(4.(26.$;.VL,O1.)(4.(21.$;.O1.VLB,(23.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))(4.(21.$;.O1.VLB,(23.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,))(4.(39.$;.O1.VLB,(1=.&40.Vsp,)(23.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,))(4.(<.(2:.(2;.$3.$3.)(2<.$3.$3.(16.(1=.&40.Vsp,)+20.)(1=.&40.Vsp,))(=.(2;.$3.$3.)))Vm,O1.)(?.$;.Vm,O1.))))))))))")
(* [comment removed for export] *).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L38948636245.0L45871104164.8L51809538089.7L55595827568.1L774765788.5  00000100J00`00d015SS1L3HLS2sp2lo2nX2pX3SLO1HS1L3HLS2sp2lo1X3SLO2XSS2spS1L3HLS2sp2lo3SLO". (* [comment removed for export] *)
    #[using="HLS gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flip HH MX SXA SXB NST OA OB XW XLS SLO ACL DHI"] Lemma after_of_post : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pj0,(2=.(2.&8.))Pm1,P,(2.&40.)(2>.(2.&8.))Pm',P,(2.&40.)(2>.(2.&8.))Pmo',$2?.Ph',(30.$;.VL,VHI,)PLB',(2=.$31.)PdX',$32.P,(3:.R7.R6.)P,(10.$;.R6.)P,(1<.$;.R7.Vlo,(16.(1=.&40.Vsp,)+20.))P,(1>.Vmo,R7.)P,(5.$3.(1?.$;.VL,VHI,R7.)(1?.$;.VL,VHI,Vh,))P,(20.$;.VL,VHI,R8.R7.R:.R9.)P,(21.$;.R;.R8.R7.)P,(22.VLB,(23.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R9.R8.)P,(24.$;.VL,VLB,(16.(1=.&40.Vsp,)+20.)(25.(23.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))R>.R=.)P,(26.$;.VL,R>.)P,(27.VLB,(23.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R;.)(33.R12.R11.R10.R?.R>.R=.R<.)")
(* [comment removed for export] *).
    Proof.
      (intros j0 m1 m' mo' h' LB' dX' dd_H; ddestruct dd_H as (MI1 & ST1 & FR1 & HH1 & SOK1 & MX1 & MA1 & MB1 & MU1 & WM1); intros MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 BK2).
      destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _]. ddestruct XW as (XCW & XDW & XP). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in XCW, XP.
      pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR DHI ACL ltac:(clear - SLO HLS; lia)) as XS.
      split; [exact MI2|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|]. split; [exact HH2|]. split; [exact MX2|]. split; [exact OUT2|].
      split; [exact HPX2|]. split; [exact SOK2|]. split; [exact BK2|]. split; [| split; [exact MU1| exact WM1]].
      eapply heap_presx_rw_cells; [exact HPX2| exact FR1| apply client_range_stack; clear; lia|].
      unfold as_frame, mpd_ivs. cbn. split; [clear - XS SLO HLS; lia|]. destruct ownX; [exact I| |]; (split; [| exact I]); destruct (XLS ltac:(discriminate)); clear - H SLO HLS; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac pre_call MX1 MA1 MB1 :=
      try exact MX1; try exact MA1; try exact MB1;
      try (eapply (opnd_at_SP_le _ _ _ (bv_unsigned sp)); [first [exact MB1| apply opnd_at_mpd; first [exact MA1| exact MB1]]| clear; lia]);
      try assumption; try (apply mpd_sep_sym; assumption);
      try (clear - SLO SPA HLS ACL HTOP; rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by lia; lia).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L11552774173.10 L12523502953.3  L17808963163.5  L18971972328.10 L22135776033.0  L22219771718.1  L29010569984.163L2957332846.13  L30541916126.4  L35203110434.8  L35868225284.10 L38340890227.3  L43480590174.4  L43592699947.6  L45445358076.3  L58354988821.5  L59308632561.1  L61386272733.16 L6186700885.5   L63060358698.24 L63509712077.24 L7358958502.18  L8574640155.5   00000800A00H00U00V00Z00[00\00j01G01W01`01n02=02F02M02Q03J03Q03R03S03T03[S2sp3SPAS2sp2pB1HS2ys2zsS1L2sp2lo3SLOSS2spFFS2sp2lo2Ba3OB4S1L3HLS2sp2lo3SLO3ACL3SPB3ACPS1L2HI2sp1h4HTOPS2sp2pX1HS2sp2lo2Aa3OA4S1L2HI2sp1h1a1CS2sp2pA1HS2ys2zsS2KRS2Aa2sA2nA2pA2ys4padA4ownA2Ba2sB2nB2pB2zs4padB4ownB2NA2NBS2ys2zsFFFS2ys2zs". (* [comment removed for export] *)
    #[using="HLS DIMG MSF HADD FLIP HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS SLO ACL HTOP SPA DHI TP CA VAL"] Lemma as_KADD : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pj0,(2=.(2.&8.))Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Pa0,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pm1,P,(2.&40.)(2>.(2.&8.))Pw,$3.P,(3:.R11.R2.)P,(5.$3.(34.R2.(35.+2.+10.))(34.VsA,(35.+2.+10.)))P,(5.$3.(19.Vflip,VsB,)VsA,)(37.$;.Vmo,VPOST,(6.(7.R10.(8.&40.(16.(1=.&40.Vsp,)+20.))Vgp,Vtp,R13.R12.R11.(8.&40.VX,)(8.&40.R4.)R?.(8.&40.VAa,)(8.&40.VBa,)R>.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(8.&40.+1?>?4.)Vfc,(9.(2.&40.))R5.(:.$;.)))")
(* [comment removed for export] *).
    Proof.
      intros until w. intros AT WS SGN. dpose AT as (MI1 & ST1 & FR1 & HH1 & SOK1 & MX1 & MA1 & MB1 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      pose proof MA as [_ SGA]. pose proof (opnd_view _ _ _ _ _ MB) as [_ SGB]. cbn [md_sg] in SGA, SGB.
      destruct XW as (XCW & XDW & XP) eqn:EXW. clear EXW. dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl psegs m1) as WM.
      zstep. zstep.
      pose proof HADD as SPc. unfold mpi_add_abs_stmt', mpi_binop_stmtB', P_MPI_ADD_ABS in SPc.
      eapply aevtM_cut.
      { eapply SPc with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (h := h) (LB := LB); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
          rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity; pre_call MX1 MA1 MB1.
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OA1|]. split; [exact OA2|]. split; [exact OA3|]. split; [clear - OA4; lia| intros AN; destruct (OA5 AN); [left; assumption| right; clear - H; lia]].
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OB1|]. split; [exact OB2|]. split; [exact OB3|]. split; [clear - OB4; lia| intros BN; destruct (OB5 BN); [left; assumption| right; clear - H; lia]].
        - split; [| split; [exact XDW| exact XP]]. intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C; lia| right; left; exact C| right; right; exact C].
        - intros XN. destruct (XLS XN); [left; assumption| right; clear - H; lia]. }
      cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & mo1 & h1 & LB1 & dX1 & r & E & PO). injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
      ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & [CR1 BK]).
      replace (ret_pc (Z_to_bv 64 130812)) with (Z_to_bv 64 130812) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (after_of_post j0 m1 m' mo1 h1 LB1 dX1 AT MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 BK) as AF.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      clear MU WM. pose proof (munch_refl ([] : list ivl) m') as MU. pose proof (wmono_refl psegs m') as WM.
      zstep. if_cases KR; zify_cond KR.
      - destruct CR1 as [(Er & _ & _)|Er]; rewrite Er in KR |- *; [exfalso; apply KR; reflexivity|]. eapply as_ERR. exact AF.
      - destruct CR1 as [(Er & CV & CS)|Er]; rewrite Er in KR |- *; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
        zstep. eapply as_FIN; [exact AF| reflexivity| exact WS| exact SGA|].
        unfold VAL. pose proof (mpd_val_abs dX1 (proj2 MX2)) as VA. rewrite CV in VA.
        pose proof (mpd_abs_nonneg dA) as NA. pose proof (mpd_abs_nonneg dB) as NB. rewrite Z.abs_eq in VA by (clear - NA NB; lia).
        rewrite <- VA. unfold mpd_val, mpd_abs. cbn [md_sg md_limbs]. rewrite <- SGN. clear - SGA SGB FLIP. destruct SGB as [-> | ->]; destruct FLIP as [-> | ->]; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L11552774173.10 L12523502953.3  L21175842280.10 L22219771718.1  L29010569984.166L2957332846.13  L30541916126.4  L35203110434.8  L35868225284.10 L38340890227.3  L40015233486.6  L43480590174.4  L43592699947.6  L45445358076.3  L59308518135.16 L59308632561.1  L61171887184.6  L61386304856.15 L63060358698.24 L63509712077.24 L66000499105.0  L7358958502.18  00000800A00N00R00S00T00b01?01O01X01f02402C02L03E03I03W04M04N04O04P04QS2sp3SPAS2sp2pB1HS1L2sp2lo3SLOS2spFFS2sp2lo2Ba3OB4S1L3HLS2sp2lo3SLO3ACL3SPB3ACPS1L2HI2sp1h4HTOPS2sp2pX1HS2sA2ys2zs3SGNS2sp2lo2Aa3OA4S1L2HI2sp1h1a1CS2sp2pA1HS2Aa2sA2nA2pA2ys4padA4ownA2Ba2sB2nB2pB2zs4padB4ownB2LE2LTS2KRS2sA2ys2zs3SGNS2Aa2sA2nA2pA2ys4padA4ownA2Ba2sB2nB2pB2zs4padB4ownB2LEFFSF". (* [comment removed for export] *)
    #[using="HLS DIMG MSF HSUB FLIP HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS SLO ACL HTOP SPA DHI TP CA VAL"] Lemma as_KSUBAB : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pj0,(2=.(2.&8.))Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Pa0,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pm1,P,(2.&40.)(2>.(2.&8.))Pw,$3.Psg,$3.P,(3:.R12.R3.)P,(5.$3.(34.R3.(35.+2.+10.))(34.R2.(35.+2.+10.)))P,(11.(5.$3.R3.+1.)(5.$3.R3.-1.))P,(5.$3.(19.Vflip,VsB,)(3;.VsA,))P,(14.(36.(23.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,))(36.(23.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)))P,(5.$3.(19.R6.(16.(36.(23.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,))(36.(23.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,))))(19.VsA,(16.(36.(23.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,))(36.(23.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)))))(37.$;.Vmo,VPOST,(6.(7.R14.(8.&40.(16.(1=.&40.Vsp,)+20.))Vgp,Vtp,R17.R16.R15.(8.&40.VX,)(8.&40.R8.)R13.(8.&40.VAa,)(8.&40.VBa,)R12.R11.R10.R?.R>.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(8.&40.+1??60.)Vfc,(9.(2.&40.))R9.(:.$;.)))")
(* [comment removed for export] *).
    Proof.
      intros until sg. intros AT WS SG SGN LE HVS. dpose AT as (MI1 & ST1 & FR1 & HH1 & SOK1 & MX1 & MA1 & MB1 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      pose proof MA as [_ SGA]. pose proof (opnd_view _ _ _ _ _ MB) as [_ SGB]. cbn [md_sg] in SGA, SGB.
      destruct XW as (XCW & XDW & XP) eqn:EXW. clear EXW. dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl psegs m1) as WM.
      zstep. zstep.
      pose proof HSUB as SPc. unfold mpi_sub_abs_stmt', mpi_binop_stmt', P_MPI_SUB_ABS in SPc.
      eapply aevtM_cut.
      { eapply SPc with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (h := h) (LB := LB); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
          rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity; pre_call MX1 MA1 MB1.
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OA1|]. split; [exact OA2|]. split; [exact OA3|]. split; [clear - OA4; lia| intros AN; destruct (OA5 AN); [left; assumption| right; clear - H; lia]].
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OB1|]. split; [exact OB2|]. split; [exact OB3|]. split; [clear - OB4; lia| intros BN; destruct (OB5 BN); [left; assumption| right; clear - H; lia]].
        - split; [| split; [exact XDW| exact XP]]. intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C; lia| right; left; exact C| right; right; exact C].
        - intros XN. destruct (XLS XN); [left; assumption| right; clear - H; lia]. }
      cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & mo1 & h1 & LB1 & dX1 & r & E & PO). injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
      ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & [CR1 BK]).
      replace (ret_pc (Z_to_bv 64 130920)) with (Z_to_bv 64 130920) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (after_of_post j0 m1 m' mo1 h1 LB1 dX1 AT MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 BK) as AF.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      clear MU WM. pose proof (munch_refl ([] : list ivl) m') as MU. pose proof (wmono_refl psegs m') as WM.
      zstep. if_cases KR; zify_cond KR.
      - destruct CR1 as [(Er & _ & _)|[Er|[Er LT]]]; rewrite Er in KR |- *; [exfalso; apply KR; reflexivity| eapply as_ERR; exact AF| exfalso; clear - LT LE; lia].
      - destruct CR1 as [(Er & CV & CS)|[Er|[Er LT]]]; rewrite Er in KR |- *;
          [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia| exfalso; clear - LT LE; lia].
        zstep. eapply as_FIN; [exact AF| reflexivity| exact WS| exact SG|].
        unfold VAL. pose proof (mpd_val_abs dX1 (proj2 MX2)) as VA. rewrite CV in VA. rewrite Z.abs_eq in VA by (clear - LE; lia).
        rewrite <- VA, HVS. unfold mpd_val, mpd_abs. cbn [md_sg md_limbs]. clear - SGA SGB FLIP SGN. destruct SGB as [-> | ->]; destruct FLIP as [-> | ->]; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L11552774173.10 L12523502953.3  L21175842280.10 L22219771718.1  L28893959834.6  L29010569984.165L2957332846.13  L30541916126.4  L35203110434.8  L35868225284.10 L38340890227.3  L43480590174.4  L43592699947.6  L45445358076.3  L48709637724.2  L5231095820.168 L52331515492.6  L59308632561.1  L59310615242.16 L61386302667.15 L63060358698.24 L63509712077.24 L7021056161.0   L7358958502.18  00000800A00N00R00`00a00b01001M01]01f02402C02L02T02`02n03203l04b04c04d04e04fS2sp3SPAS2sp2pB1HS1L2sp2lo3SLOS2spS2sA2ys2zs3SGNFFS2sp2lo2Ba3OB4S1L3HLS2sp2lo3SLO3ACL3SPB3ACPS1L2HI2sp1h4HTOPS2sp2pX1HS2sp2lo2Aa3OA4S1L2HI2sp1h1a1CS2sp2pA1HS2sA3SGAS2sp2sA1w2WBS2sA2ys2zs3SGNS2KRS2Aa2sA2nA2pA2ys4padA4ownA2Ba2sB2nB2pB2zs4padB4ownB2LT3LT'S2Aa2sA2nA2pA2ys4padA4ownA2Ba2sB2nB2pB2zs4padB4ownB2LTFFSF". (* [comment removed for export] *)
    #[using="HLS DIMG MSF HSUB FLIP HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS SLO ACL HTOP SPA DHI TP CA VAL"] Lemma as_KSUBBA : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pj0,(2=.(2.&8.))Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Pa0,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pm1,P,(2.&40.)(2>.(2.&8.))Pw,$3.P,(3:.R11.R2.)P,(5.$3.(34.R2.(35.+2.+10.))(34.VsA,(35.+2.+10.)))P,(4.(14.=R3.)(3<.R3.(35.+2.+10.)))P,(5.$3.(19.Vflip,VsB,)(3;.VsA,))P,(3<.(36.(23.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,))(36.(23.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)))(37.$;.Vmo,VPOST,(6.(7.R12.(8.&40.(16.(1=.&40.Vsp,)+20.))Vgp,Vtp,R15.R14.R13.(8.&40.VX,)(8.&40.R6.)R11.(8.&40.VAa,)(8.&40.VBa,)R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(8.&40.+1??:<.)Vfc,(9.(2.&40.))R7.(:.$;.)))")
(* [comment removed for export] *).
    Proof.
      intros until w. intros AT WS WB SGN LT. dpose AT as (MI1 & ST1 & FR1 & HH1 & SOK1 & MX1 & MA1 & MB1 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      pose proof MA as [_ SGA]. pose proof (opnd_view _ _ _ _ _ MB) as [_ SGB]. cbn [md_sg] in SGA, SGB.
      destruct XW as (XCW & XDW & XP) eqn:EXW. clear EXW. dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl psegs m1) as WM.
      zstep. zstep. zstep. zstep. zstep.
      pose proof HSUB as SPc. unfold mpi_sub_abs_stmt', mpi_binop_stmt', P_MPI_SUB_ABS in SPc.
      eapply aevtM_cut.
      { eapply SPc with (dX := dX) (dA := dB) (dB := dA) (lo := lo) (h := h) (LB := LB); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
          rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity; pre_call MX1 MA1 MB1.
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OB1|]. split; [exact OB2|]. split; [exact OB3|]. split; [clear - OB4; lia| intros BN; destruct (OB5 BN); [left; assumption| right; clear - H; lia]].
        - unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. split; [exact OA1|]. split; [exact OA2|]. split; [exact OA3|]. split; [clear - OA4; lia| intros AN; destruct (OA5 AN); [left; assumption| right; clear - H; lia]].
        - split; [| split; [exact XDW| exact XP]]. intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C; lia| right; left; exact C| right; right; exact C].
        - intros XN. destruct (XLS XN); [left; assumption| right; clear - H; lia]. }
      cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & mo1 & h1 & LB1 & dX1 & r & E & PO). injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
      ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & [CR1 BK]).
      replace (ret_pc (Z_to_bv 64 131008)) with (Z_to_bv 64 131008) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (after_of_post j0 m1 m' mo1 h1 LB1 dX1 AT MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 BK) as AF.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      clear MU WM. pose proof (munch_refl ([] : list ivl) m') as MU. pose proof (wmono_refl psegs m') as WM.
      zstep. if_cases KR; zify_cond KR.
      - destruct CR1 as [(Er & _ & _)|[Er|[Er LT']]]; rewrite Er in KR |- *; [exfalso; apply KR; reflexivity| eapply as_ERR; exact AF| exfalso; clear - LT LT'; lia].
      - destruct CR1 as [(Er & CV & CS)|[Er|[Er LT']]]; rewrite Er in KR |- *;
          [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia| exfalso; clear - LT LT'; lia].
        zstep.
        eapply (as_FIN j0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (0 - w) (- sA)); [exact AF| reflexivity| | clear - SGA; lia|].
        + rewrite Zminus_mod, WS, <- Zminus_mod. reflexivity.
        + unfold VAL. pose proof (mpd_val_abs dX1 (proj2 MX2)) as VA. rewrite CV in VA. rewrite Z.abs_eq in VA by (clear - LT; lia).
          rewrite <- VA. unfold mpd_val, mpd_abs. cbn [md_sg md_limbs]. clear - SGA SGB FLIP SGN. destruct SGB as [-> | ->]; destruct FLIP as [-> | ->]; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00=0>L136446722.6  L14622494633.2L22366621351.0L24962925985.0L25523630113.0L32223618336.4L43315511802.6L5212562720.4 L59308628179.1L59663971895.5L635310052.2  L6419290535.0 L7688565214.2 00000E00M00N00O00P00Z00o01<01@01M01U01V01]S4flip2sA2sB2EA2EB2EFS2nB3NRBSSSS2ys2zs2CmS4flip2sA2sB2EA2EB2EFS2ys2zs2C02C1S2K0S2sA2ys2zs2C0S2nA3NRASS2sA2EA". (* [comment removed for export] *)
    #[using="HLS DIMG MSF HADD HSUB FLIP HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS SLO ACL HTOP SPA DHI TP CA VAL"] Lemma as_body : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pj0,(2=.(2.&8.))Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pm1,P,(2.&40.)(2>.(2.&8.))P,(3:.R=.R1.)(37.$;.Vmo,VPOST,(6.(7.Vra,(8.&40.(16.(1=.&40.Vsp,)+20.))Vgp,Vtp,R=.R<.R;.Vs0,Vs1,(8.&40.VX,)(8.&40.VAa,)(8.&40.VBa,)(8.&40.Vflip,)R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(8.&40.+1?>=4.)Vfc,(9.(2.&40.))R2.(:.$;.)))")
(* [comment removed for export] *).
    Proof.
      intros until m1. intros AT. dpose AT as (MI & ST & FR & HH1 & SOK1 & MX1 & MA1 & MB1 & MU1 & WM1).
      pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
      pose proof MA as [_ SGA]. pose proof (opnd_view _ _ _ _ _ MB) as [_ SGB]. cbn [md_sg] in SGA, SGB.
      destruct (mpd_raw _ _ _ _ MA1 ltac:(cbn [md_own md_p]; intros EO; rewrite EO in MA; pose proof MA as [(_ & _ & _ & _ & _ & OW) _]; ddestruct OW as (_ & IN & _);
                 pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (R0 & _); exact R0)) as (CEA & ABY & LENA & NRA & _ & ABD & PAB).
      destruct (opnd_raw _ _ _ _ _ MB1 ltac:(cbn [md_own md_p]; intros EO; pose proof (opnd_view _ _ _ _ _ MB) as [(_ & _ & _ & _ & _ & OW) _]; cbn [md_own] in OW; rewrite EO in OW; ddestruct OW as (_ & IN & _);
                 pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (R0 & _); exact R0)) as (CEB & BBY & LENB & NRB & _ & BBD & PBB).
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEA, ABY, LENA, NRA, ABD, PAB, CEB, BBY, LENB, NRB, BBD, PBB.
      pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl psegs m1) as WM.
      zstep.
      pose proof FLIP as FL. destruct SGA as [EA|EA]; rewrite EA in CEA; destruct SGB as [EB|EB]; rewrite EB in CEB; (destruct FL as [EF|EF];
        [replace (Z_to_bv 64 flip) with (Z_to_bv 64 1) by (rewrite EF; reflexivity) | replace (Z_to_bv 64 flip) with (Z_to_bv 64 (-1)) by (rewrite EF; reflexivity)]).
      all: zstep; rewrite sx16_small by (clear; lia); zstep; rewrite sx16_small by (clear; lia); zstep; zstep; zstep; zstep; zstep; if_cases K0; zify_cond K0.
      all: try (exfalso; clear - K0; lia).
      (* [comment removed for export] *)
      all: lazymatch goal with
           | |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x1fef4) _ _ _ _) =>
               eapply (as_KADD j0); [exact AT| rewrite EA; vm_compute; reflexivity| clear - EA EB EF; lia]
           | |- _ => idtac end.
      (* [comment removed for export] *)
      all: eapply aevtM_cut_evt;
        [ exact MK
        | eapply as_cmp; [exact CEA| exact ABY| exact LENA| clear - NRA; lia| exact PAB| exact CEB| exact BBY| exact LENB| clear - NRB; lia| exact PBB| exact MI]
        | ].
      all: cbv beta; intros ms' PC; unfold cmpw_post in PC; ddestruct PC as (b0 & b3 & b4 & b5 & w & pc & -> & _ & _ & _ & CASES).
      all: pose proof (mpd_abs_lval dA LENA) as EVA; pose proof (mpd_abs_lval dB LENB) as EVB; unfold mpd_abs in EVA, EVB; cbn [md_limbs md_n] in EVA, EVB;
           rewrite <- EVA, <- EVB in CASES; clear EVA EVB.
      all: pose proof (limbs_val_nonneg ys) as NYA; pose proof (limbs_val_nonneg zs) as NZB.
      all: destruct CASES as [(-> & [[C1 ->]|[C0 ->]])|(-> & Cm & ->)].
      all: try (eapply (as_KSUBBA j0); [exact AT| rewrite EA; vm_compute; reflexivity| clear; lia| clear - EA EB EF; lia| unfold mpd_abs; cbn [md_limbs]; pose proof (Z.sgn_spec (limbs_val ys - limbs_val zs)); clear - Cm H; lia]).
      all: try (eapply (as_KSUBAB j0) with (sg := 1); [exact AT| vm_compute; reflexivity| left; reflexivity| clear - EA EB EF; lia
              | unfold mpd_abs; cbn [md_limbs]; pose proof (Z.sgn_spec (limbs_val ys - limbs_val zs)); clear - C0 H; lia
              | unfold mpd_abs; cbn [md_limbs]; pose proof (Z.sgn_spec (limbs_val ys - limbs_val zs)); clear - C0 H; lia]).
      all: try (eapply (as_KSUBAB j0) with (sg := sA); [exact AT| rewrite EA; vm_compute; reflexivity| clear - EA; lia| clear - EA EB EF; lia
              | unfold mpd_abs; cbn [md_limbs]; pose proof (Z.sgn_spec (limbs_val ys - limbs_val zs)); clear - C1 H; lia
              | reflexivity]).
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Body.
  (* [comment removed for export] *)
  #[using="Type"] Lemma binop_post_mono : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)PF,(3=.&5.(2.&40.))Pfc,(2.&20.)Ph,(30.$;.VL,VHI,)PLB,(2=.$31.)PdX,$32.PR1,P,$3.P,$32.SpPR2,P,$3.P,$32.SpPlo,$3.Pm,P,(2.&40.)(2>.(2.&8.))Pmo,$2?.Pc,$3>.P,Pr,$3.Pd,$32.P,A2.R8.R2.R1.A2.R8.R3.R2.P,(3?.$;.VL,VHI,R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R5.R4.R3.R2.)(3?.$;.VL,VHI,R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros until c. intros HR P. unfold mpi_binop_post in *.
    ddestruct P as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & mo' & h' & LB' & dX' & r & P).
    dexists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m', mo', h', LB', dX', r.
    ddestruct P as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
    repeat (split; [assumption|]). apply HR. exact P10.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@D10463954377.125D10463954377.126D27668705378.125D27668705378.126L15962907669.8  L21765854580.118L21887662552.117L27775132660.118L33160662877.7  L33510041944.118L34290115814.117L34496295996.7  L35312475779.7  L35754698159.125L35754698159.126L38948636245.0  L43061432074.115L44622288685.125L44622288685.126L49698585326.125L49698585326.126L53028994992.1  L66083662040.118L774765788.5    L9716869748.117 00000R01701^02H02a02e02i02m03B03F03J03`04804N04g04h05=05l06^07807U07Y07]07n082S1L2HI2ra2sp1h4HTOP2HB5Ha_st5Hl_stS1L2HI2sp2s01h4HTOP2HB5Ha_st5Hl_st2s1S1L3HLS2ra2sp2lo3SLO3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2s02lo3SLO3SPB2HB5Ha_st5Hl_st2s1S1L3HLS2sp2nB2pB2lo3SLO1HS2spS2spS2spS1L3HLS2sp2lo3SLO1d1HS2spS2spS1L3HLS2sp2lo3SLO1d2D1S1L3HLS2sp2Ba2lo3SLO3OB4S2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_st2s1SS1L3HLS2sp2lo3SLO3SPBS1L3HLS2ra2sp2lo3SLO3ACL3DHI3SPB2HB5Ha_st5Hl_stS1L3HLS2sp2s02lo3SLO3ACL3DHI3SPB2HB5Ha_st5Hl_st2s1S2ra2sp3SPB2HB5Ha_st5Hl_stS2sp2s03SPB2HB5Ha_st5Hl_st2s1S2spS2spS1L3HLS2sp2lo3SLOS2sp". (* [comment removed for export] *)
  #[using="HLS DIMG HADD HSUB"] Lemma P_add_sub_mpi_spec : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "Pflip,$3.P,(11.(5.$3.R1.+1.)(5.$3.R1.-1.))Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3=.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(2>.(2.&8.))Pmo,$2?.Ph,(30.$;.VL,VHI,)PLB,(2=.$31.)PdX,$32.PdA,$32.PdB,$32.Plo,$3.P,(20.$;.VL,VHI,R6.R5.R8.R7.)P,(21.$;.R9.R6.R5.)P,(21.$;.R:.R7.R5.)P,(39.$;.R;.R8.(1=.&40.R2:.)R5.)P,(40.R8.R7.)P,(40.R9.R7.)P,(40.R9.R8.)P,(41.(5.$42.(43.R;.)$44.))P,(45.R<.R;.R9.(1=.&40.R2?.))P,(45.R=.R;.R:.(1=.&40.R30.))P,(46.VL,R?.R;.(47.R=.)+10.)P,P,(5.$42.(43.R>.)$48.)(46.VL,R11.R=.(49.R?.)(19.+4.(4:.R?.)))P,(46.VL,R11.R=.(47.R>.)+10.)P,P,(5.$42.(43.R?.)$48.)(46.VL,R13.R?.(49.R10.)(19.+4.(4:.R10.)))P,(4;.VL,R13.(1=.&40.R35.)(1?.$;.VL,VHI,R14.)R12.)P,P,(41.(5.$42.(43.R13.)$4<.))(11.(14.(18.(49.R14.)(19.+4.(4:.R14.)))R11.)(14.(1=.&40.R37.)(49.R14.)))P,(1<.$;.R18.R11.(1=.&40.R37.))P,(14.R12.(16.(16.(1=.&40.R38.)+>0.)(4=.VL,)))P,(14.(4>.VL,)R13.)P,(14.(1=.&40.R3:.)(1?.$;.VL,VHI,R19.))P,(5.$3.(34.(1=.&40.R3;.)+10.)=)P,(14.(4?.VL,)(4>.VL,))P,(5.(2.&40.)R3;.(8.&40.(50.VL,)))P,(10.$;.R1?.)P,(26.$;.VL,R20.)P,(51.VL,VMSF,+8.)P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))(37.$;.R24.(3?.$;.VL,VHI,R45.R44.R43.R42.R3>.R3=.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R23.R22.R21.(52.R47.R22.R21.R20.R1?.)R1>.R25.R24.)(6.(7.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.(8.&40.R47.)R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(8.&40.+1?><4.)R26.(9.(2.&40.))R25.(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros flip FLIP. intros until lo.
    intros HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    destruct dX as [X sX nX pX xs0 padX ownX]. destruct dA as [Aa sA nA pA ys padA ownA]. destruct dB as [Ba sB nB pB zs padB ownB].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5). dpose XW as (XCW & XDW & XP).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OA4, OA5, OB4, OB5, XCW.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR DHI ACL ltac:(clear - SLO HLS; lia)) as XS.
    pose proof ST as ST1. carve_frame 32%nat ST1.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (conj HH I) as HHc. pose proof (conj SOK I) as SOKc. pose proof MI as MI1.
    do 4 zstep.
    replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in * by (clear; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match type of FR with rw_cells _ _ _ (CB _ ?jk :: _) => set (j0 := jk) in FR end.
    destruct HHc as [HH0 _]. destruct SOKc as [SOK0 _].
    assert (OPM : forall d, mpd_at psegs m LB d -> (md_addr d + 16 <= lo \/ bv_unsigned sp <= md_addr d) ->
                  (md_own d <> LNull -> md_p d + 4 * md_n d <= lo \/ bv_unsigned sp <= md_p d) -> mpd_at psegs m1 LB d).
    { intros d Md D1 D2. eapply mpd_at_munch_any; [exact Md| exact MU| exact WM| cbn; split; [clear - D1 SLO HLS; lia| exact I]|].
      intros ON. cbn. split; [destruct (D2 ON); clear - H SLO HLS; lia| exact I]. }
    eapply (as_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB lo flip X sX nX pX xs0 padX ownX Aa sA nA pA ys padA ownA Ba sB nB pB zs padB ownB);
      try assumption.
    split; [exact MI1|]. split; [exact ST1|]. split; [exact FR|].
    split; [first [exact HH| eapply (HEAP_munch psegs L HI) with (SP := lo); [exact HH0| exact MU| exact WM| exact ACL|]; intros a Ha NO; cbn in NO; left; clear - NO HTOP SLO HLS; lia]|].
    split; [first [exact SOK| eapply statics_ok_munch; [exact SOK0| exact MU|]; intros a Hd NW; cbn; split; [clear - Hd DHI ACL SLO HLS; lia| exact I]]|].
    split; [exact (OPM _ MX XS XLS)|]. split; [exact (OPM _ MA OA4 OA5)|].
    split. { eapply opnd_at_munch_any; [exact MB| exact MU| exact WM| cbn; split; [clear - OB4 SLO HLS; lia| exact I]|].
             intros ON. cbn. split; [destruct (OB5 ON); clear - H SLO HLS; lia| exact I]. }
    split; [exact MU| exact WM].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L65106939752.8300000:S2sp2dA2dB". (* [comment removed for export] *)
  #[using="HLS DIMG HADD HSUB"] Theorem P_mpi_add_mpi_spec' : mpi_add_mpi_stmt psegs L HI P_MPI_ADD_MPI MSF.
  Proof.
    unfold mpi_add_mpi_stmt, mpi_binop_stmt, P_MPI_ADD_MPI. intros until lo.
    intros HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. zstep.
    eapply aevtM_mono; [eapply (P_add_sub_mpi_spec 1 ltac:(left; reflexivity)) with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (h := h) (LB := LB); try eassumption; try reflexivity; apply opnd_at_mpd; assumption|].
    cbv beta. intros c. apply binop_post_mono. intros r d [V K]. split; [| exact K].
    destruct V as [[-> E]|E]; [left; split; [reflexivity| rewrite E; lia]| right; exact E].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L52849495742.8300000:S2sp2dA2dB". (* [comment removed for export] *)
  #[using="HLS DIMG HADD HSUB"] Theorem P_mpi_sub_mpi_spec' : mpi_sub_mpi_stmt psegs L HI P_MPI_SUB_MPI MSF.
  Proof.
    unfold mpi_sub_mpi_stmt, mpi_binop_stmt, P_MPI_SUB_MPI. intros until lo.
    intros HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. zstep.
    eapply aevtM_mono; [eapply (P_add_sub_mpi_spec (-1) ltac:(right; reflexivity)) with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (h := h) (LB := LB); try eassumption; try reflexivity; apply opnd_at_mpd; assumption|].
    cbv beta. intros c. apply binop_post_mono. intros r d [V K]. split; [| exact K].
    destruct V as [[-> E]|E]; [left; split; [reflexivity| rewrite E; lia]| right; exact E].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Main.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Spec.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr psegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem P_mpi_add_mpi_spec : forall MSF, MSF = P_MEMSET_FUNC -> mpi_add_mpi_stmt psegs L HI P_MPI_ADD_MPI MSF.
  Proof.
    intros MSF E. apply P_mpi_add_mpi_spec'; try assumption.
    - apply P_mpi_add_abs_spec_o; assumption.
    - apply P_mpi_sub_abs_spec_o; assumption.
  Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem P_mpi_sub_mpi_spec : forall MSF, MSF = P_MEMSET_FUNC -> mpi_sub_mpi_stmt psegs L HI P_MPI_SUB_MPI MSF.
  Proof.
    intros MSF E. apply P_mpi_sub_mpi_spec'; try assumption.
    - apply P_mpi_add_abs_spec_o; assumption.
    - apply P_mpi_sub_abs_spec_o; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem P_add_sub_mpi_spec_o : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_sub ()) "PMSF,$3.P,(5.$3.R1.$53.)Pflip,$3.P,(11.(5.$3.R1.+1.)(5.$3.R1.-1.))Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3=.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(2>.(2.&8.))Pmo,$2?.Ph,(30.$;.VL,VHI,)PLB,(2=.$31.)PdX,$32.PdA,$32.PdB,$32.Plo,$3.P,(20.$;.VL,VHI,R6.R5.R8.R7.)P,(21.$;.R9.R6.R5.)P,(21.$;.R:.R7.R5.)P,(39.$;.R;.R8.(1=.&40.R2:.)R5.)P,(40.R8.R7.)P,(40.R9.R7.)P,(40.R9.R8.)P,(41.(5.$42.(43.R;.)$44.))P,(45.R<.R;.R9.(1=.&40.R2?.))P,(45.R=.R;.R:.(1=.&40.R30.))P,(46.VL,R?.R;.(47.R=.)+10.)P,P,(5.$42.(43.R>.)$48.)(46.VL,R11.R=.(49.R?.)(19.+4.(4:.R?.)))P,(46.VL,R11.R=.(47.R>.)+10.)P,P,(5.$42.(43.R?.)$48.)(46.VL,R13.R?.(49.R10.)(19.+4.(4:.R10.)))P,(4;.VL,R13.(1=.&40.R35.)(1?.$;.VL,VHI,R14.)R12.)P,P,(41.(5.$42.(43.R13.)$4<.))(11.(14.(18.(49.R14.)(19.+4.(4:.R14.)))R11.)(14.(1=.&40.R37.)(49.R14.)))P,(1<.$;.R18.R11.(1=.&40.R37.))P,(14.R12.(16.(16.(1=.&40.R38.)+>0.)(4=.VL,)))P,(14.(4>.VL,)R13.)P,(14.(1=.&40.R3:.)(1?.$;.VL,VHI,R19.))P,(5.$3.(34.(1=.&40.R3;.)+10.)=)P,(14.(4?.VL,)(4>.VL,))P,(5.(2.&40.)R3;.(8.&40.(50.VL,)))P,(10.$;.R1?.)P,(26.$;.VL,R20.)P,(51.VL,R45.+8.)P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))P,(5.(2.&40.)R39.(8.&40.(47.R1>.)))(37.$;.R24.(3?.$;.VL,VHI,R45.R44.R43.R42.R3>.R3=.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R23.R22.R21.(52.R47.R22.R21.R20.R1?.)R1>.R25.R24.)(6.(7.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.(8.&40.R47.)R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(8.&40.+1?><4.)R26.(9.(2.&40.))R25.(:.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros MSF E. apply P_add_sub_mpi_spec; try assumption.
    - apply P_mpi_add_abs_spec_o; assumption.
    - apply P_mpi_sub_abs_spec_o; assumption.
  Qed.
End Spec.
