(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P04f82ad7b5e292aa 0 2 0 1 59 1P064e8822692f21dd 0 2 0 1 6 1P076f08170ecb9922 0 2 0 1 15 1P081258a307e70e2d 0 3 0 1 60 1 62 1P096465e7759fb86a 0 2 0 1 59 1P0d811c31c2c6b9d9 0 2 0 1 59 1P10dcf3b7bca724a3 0 2 0 1 5 1P115517b4092fc8ed 0 4 0 1 29 4 48 1 53 1P11e9fa2b12693cb3 0 4 0 1 20 4 21 1 47 1P11f9c1bc2c5d8e70 0 3 0 1 59 1 61 1P1212d15b7f78ed0a 0 2 0 1 59 1P161cb7c8bfc415fb 1 1 4 3 0 1 22 1 48 1 2 19 1 61 1P173f37ca67d037e7 0 2 0 1 6 1P1f12125ff6789c9c 0 4 0 1 29 4 48 1 53 1P1f62a046afeb0025 0 2 0 1 15 1P208448470f25dd56 0 2 0 1 5 1P30c4600533023cd7 0 3 0 1 30 1 59 1P3391590aa7e7dbcc 0 2 0 1 15 1P3a7816a37fd101b2 0 2 0 1 14 1P3d0b0726f112f535 0 2 0 1 59 1P3f868de01f03c0af 0 2 0 1 6 1P3fcc7784f9e65153 0 2 0 1 59 1N020c8abf9fbb3278N023ee181e8edb8f6N032a0d684ec1afddN04370fa874d413d5N047229d1f4a96234N04fcb1ae5d57a57aN0555f10bd848e251N098b68ae04e31691N0a5d994c4a7fa013N0b0c8aabaa0c92ccN0bc21642e34b168aN0cac48a42974c793N0cb799bd0ddd85b6N0cdf42c3447c91d2N1017e2699b055be6N10d727366c822e4cN11ca6c057dc9d4e3N125d5a2dacb08795N12629281b8a160acN130cb3c728512c59N1440d4025f9ba91dN148c1f8b7ad6b3f7N166834882b1b441bN186dbd9875975271N1944940c1f2c0a2aN194516b80cab9034N1aec6a9f38de1a20N1c087b1cdc92a7d2N1c12f9bf10f85f0eN1e48ffce1c23e25fN1e8a209498485a9dN22dc5cb3ec22e52fN24dc69a84efdcaa2N25f9375571d809baN26fa658d8c840a35N2911e1d08ca47f5cN2998b86c05f6dadaN29fe8132668c252dN2a42e80d605b63baN2ee5103d6e8ba1d7N2f2136a6f345e5a7N319edba736f4327fN348bf27918f10b01N36021d771059cf5cN36faf1da0e2ee883N36ff072630ed8f33N3835956fd285d015N3aad052079f71a44N3c12a27b5be97b0fN3c88e5b07c290f50N3dbda27ece0752f1N3e0ad18d0e92a2afN3efebbcf040621c3N3f9ad85363e19833"%lxh.
Ltac2 gd_tbl_P_mpi_core_add () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_ADD_STACK"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.Exec.evt"; "mpi_core_add_post"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.MpiCoreAux.same_from"; "OSSVerify.KrLib.Lib.MpiCoreAux.add_inv"].


Definition P_MPI_CORE_ADD : Z := 0x22908.

(* [comment removed for export] *)
Definition MPI_CORE_ADD_STACK : Z := 48.

Definition mpi_core_add_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n : Z) (xs ys zs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_add ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lc,$4.(1.(5.(2.&40.))Lxs',(5.(2.&40.))(6.(7.$0.R13.(8.(9.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(:.O19.)O8.(;.(2.&40.))R3.(<.O1:.)))(6.(=.(>.(?.$4.$4.)(10.$4.$4.O7.(11.O7.(12.+4.O6.)))(>.(?.$4.$4.)(10.$4.$4.(13.(14.&40.O18.)$15.)(14.&40.O18.))(16.(?.$4.$4.))))O1.R3.)(6.(17.O1:.O1.R3.)(6.(18.O1:.R3.)(6.(7.(2.&40.)R?.(19.&40.R2.))(6.(6.(1:.=R2.)(1:.R2.+1.))(6.(1;.O1:.R3.O7.R1.)(6.(7.$1<.(1=.(2.&40.)R1.)(1=.(2.&40.)O5.))(6.(7.(5.(2.&40.))(1>.(2.&40.)(1?.O6.)R1.)(1>.(2.&40.)(1?.O6.)O5.))(6.(7.$4.(11.(20.R1.O6.)(12.R2.(21.+2.(12.+20.O6.))))(11.(20.O4.O6.)(20.O3.O6.)))(22.O1:.R3.O2.(14.&40.O18.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_add_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_add ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(23.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$4.PA,$4.PB,$4.Pn,$4.Plo,$4.Pxs,(5.(2.&40.))Pys,(5.(2.&40.))Pzs,(5.(2.&40.))P,(1;.O2.R9.R8.R3.)P,(24.O2.R:.R8.(25.R3.))P,(24.O2.R;.R8.(25.R3.))P,(6.(1:.=R8.)(1:.R8.+2710.))P,(1:.R9.(26.(1=.(2.&40.)R7.)))P,(1:.R:.(26.(1=.(2.&40.)R7.)))P,(1:.R;.(26.(1=.(2.&40.)R7.)))P,(27.(6.(7.$4.R>.R?.)(7.(5.(2.&40.))R9.R:.))(27.(1:.(11.R>.(12.+4.(26.(1=.(2.&40.)R9.))))R?.)(1:.(11.R?.(12.+4.(26.(1=.(2.&40.)R:.))))R>.)))P,(27.(6.(7.$4.R>.R10.)(7.(5.(2.&40.))R9.R;.))(27.(1:.(11.R>.(12.+4.(26.(1=.(2.&40.)R9.))))R10.)(1:.(11.R10.(12.+4.(26.(1=.(2.&40.)R;.))))R>.)))P,(7.$4.(28.R11.+4.)=)P,(7.$4.(28.R11.+4.)=)P,(7.$4.(28.R11.+4.)=)P,(29.=R14.)P,(29.=R14.)P,(29.=R14.)P,(22.O2.R18.R13.(14.&40.R38.))P,(1:.R14.(13.(14.&40.R39.)$15.))P,(7.$4.(28.(14.&40.R3:.)+10.)=)P,(27.(1:.(11.R1:.(12.+4.(26.(1=.(2.&40.)R15.))))R16.)(1:.(14.&40.R3;.)R1:.))P,(27.(1:.(11.R1:.(12.+4.(26.(1=.(2.&40.)R15.))))R17.)(1:.(14.&40.R3<.)R1:.))P,(27.(1:.(11.R1:.(12.+4.(26.(1=.(2.&40.)R15.))))R18.)(1:.(14.&40.R3=.)R1:.))P,(18.O2.R1>.)P,(7.(2.&40.)R37.(19.&40.R1>.))P,(7.(2.&40.)R37.(19.&40.R1>.))P,(7.(2.&40.)R37.(19.&40.R1>.))P,(7.(2.&40.)R37.(19.&40.R1>.))(2:.O2.(2;.O2.R44.R43.R42.R41.R3=.R3<.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R25.R24.R22.R1?.R1=.R1<.R1;.R1>.R23.)(8.(9.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R25.(19.&40.O1.)R24.(;.(2.&40.))R23.(<.O2.)))")
(* [comment removed for export] *).


Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A B n lx la lb lo : Z) (xs0 ys0 zs0 : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= lx /\ n <= la /\ n <= lb.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  (* [comment removed for export] *)
  Hypothesis DA : (A = X /\ la = lx /\ ys0 = xs0) \/ A + 4 * la <= X \/ X + 4 * lx <= A.
  Hypothesis DB : (B = X /\ lb = lx /\ zs0 = xs0) \/ B + 4 * lb <= X \/ X + 4 * lx <= B.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
  Hypothesis AB : 0 < A /\ A + 4 * la <= 2^64.
  Hypothesis BB : 0 < B /\ B + 4 * lb <= 2^64.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis ALB : B mod 4 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - MPI_CORE_ADD_STACK.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis SA : A + 4 * la <= lo \/ bv_unsigned sp <= A.
  Hypothesis SB' : B + 4 * lb <= lo \/ bv_unsigned sp <= B.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.

  Notation POST := (mpi_core_add_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n xs0 ys0 zs0 lo m).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - MPI_CORE_ADD_STACK, bv_unsigned sp)].

  (* [comment removed for export] *)
  Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_add ()) "Pk,$1<.Pi,$4.Pc,$4.Pxs,(5.(2.&40.))Pys,(5.(2.&40.))Pzs,(5.(2.&40.))Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pex,$4.Pea,$4.Peb,$4.Pe3,$4.P,(7.$1<.(1?.(13.Vn,R=.))R>.)P,(6.(1:.=R>.)(29.R>.Vn,))P,(6.(1:.=R>.)(1:.R>.+1.))P,(7.$4.R7.(11.VX,(12.+4.R10.)))P,(7.$4.R7.(11.VA,(12.+4.R11.)))P,(7.$4.R7.(11.VB,(12.+4.R12.)))P,(7.$4.R7.(11.VX,(12.+4.Vn,)))P,(1;.$2<.R<.VX,R12.)P,(24.$2<.R=.VA,(25.R12.))P,(24.$2<.R>.VB,(25.R12.))P,(7.$4.(26.(1=.(2.&40.)R15.))Vlx,)P,(7.$4.(26.(1=.(2.&40.)R15.))Vla,)P,(7.$4.(26.(1=.(2.&40.)R15.))Vlb,)P,(2=.(2.&40.)(1?.R1:.)R18.Vxs0,)P,(2=.(2.&40.)(1?.R1;.)R18.Vys0,)P,(2=.(2.&40.)(1?.R1<.)R18.Vzs0,)P,(2>.R1;.R1=.R1<.Vys0,Vzs0,)P,(22.$2<.R16.Vlo,(14.&40.Vsp,))P,(=.(>.(?.$4.$4.)(10.$4.$4.VX,(11.VX,(12.+4.Vn,)))(>.(?.$4.$4.)(10.$4.$4.(13.(14.&40.Vsp,)$15.)(14.&40.Vsp,))(16.(?.$4.$4.))))Vm,R17.)P,(17.$2<.Vm,R18.)P,(18.$2<.R19.)(2:.$2<.(2;.$2<.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vxs0,Vys0,Vzs0,Vlo,Vm,)(8.(9.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(19.&40.R19.)(19.&40.R18.)(19.&40.R17.)(19.&40.R16.)(19.&40.R21.)R1=.R1<.R1;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(19.&40.+22918.)Vfc,(;.(2.&40.))R1:.(<.$2<.)))")
(* [comment removed for export] *).
  Proof.
    unfold MPI_CORE_ADD_STACK in *.
    induction k as [|k IH]; intros i c xs ys zs x15 x16 x17 mm ex ea eb e3 Hk Hi Hc Ex Ea Eb E3 HX HA HB LX LA LB FX FA FB INV
      ST MU WM MI; [exfalso; xlia Hk Hi|].
    (* [comment removed for export] *)
    lx_limb_ro HA FA i Ea (proj1 Hi) ltac:(xlia Hi LA Ln) wa VA. lx_limb_ro HB FB i Eb (proj1 Hi) ltac:(xlia Hi LB Ln) wb VB.
    lx_limb_rw HX i Ex (proj1 Hi) ltac:(xlia Hi LX Ln) wx NX.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM. lx_hide HX.
    pose proof (munch_refl ([] : list ivl) mm) as MUl0. pose proof (wmono_refl psegs mm) as WMl0.
    lx_run_tac (PLAN [0x22918] [] 40%N); lx_tree.
    all: lx_unhide; lx_gc; try clear MUl0; try clear WMl0.
    (* [comment removed for export] *)
    all: lazymatch goal with DEF : ?cv = Z.b2z _ + Z.b2z _ |- _ =>
           first [ destruct (lx_core_add_exact wa wb c cv Hc DEF) as [Hc' V]
                 | rewrite Z.add_comm in DEF; destruct (lx_core_add_exact wa wb c cv Hc DEF) as [Hc' V] ]; clear DEF end.
    all: lx_rn_rw ex CX'; lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'.
    all: pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX (proj1 Hi) Ex MUl WMl CX') as HX';
         pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(xlia Ex Hi) ltac:(xlia Ex Hi)) as MU';
         pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22918) _ _ _ _) =>
      (* [comment removed for export] *)
      (let xe3 := constr:(e3) in let xex := constr:(ex) in
       match goal with K : 0 <= xe3 + _ |- _ => rename K into BR | K : 0 <= - xex + _ |- _ => rename K into BR | _ => idtac end);
      destruct (u32ro_next _ _ _ _ _ _ _ _ _ _ _ _ _ DA HX' LX FX HA LA FA ltac:(xlia Hi Ln) Ex MUl) as (ys' & HA' & LA' & FA');
      destruct (u32ro_next _ _ _ _ _ _ _ _ _ _ _ _ _ DB HX' LX FX HB LB FB ltac:(xlia Hi Ln) Ex MUl) as (zs' & HB'' & LB'' & FB');
      eapply (IH (i + 1)); [xlia Hk Hi | klia | exact Hc' | xlia Ex | xlia Ea | xlia Eb | xlia E3
        | exact HX' | exact HA' | exact HB''
        | exact (upd_length_Z _ _ _ _ LX) | exact LA' | exact LB''
        | exact (same_from_upd_Z _ _ _ _ FX (proj1 Hi)) | exact (same_from_S_Z _ _ _ FA' (proj1 Hi)) | exact (same_from_S_Z _ _ _ FB' (proj1 Hi))
        | exact (add_inv_next _ _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VA VB V)
        | exact ST' | exact MU' | exact WM' | exact MI' ]
    | |- _ =>
      (* [comment removed for export] *)
      lx_post;
      lazymatch goal with
           | |- munch _ _ _ => exact MU'
           | |- wmono _ _ _ => exact WM'
           | |- u32arr _ _ _ _ => exact HX'
           | |- @eq nat (length _) _ => rewrite upd_length; xlia LX L0
           | |- skipn _ _ = skipn _ _ => eapply skipn_upd_Z; [exact FX | xlia Hi | klia | xlia LX L0]
           | |- lval _ ?nn + _ = _ => replace nn with (i + 1) by klia; exact (add_inv_next _ _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VA VB V)
           | |- _ => first [reflexivity | assumption | xlia Hc']
           end
    end.
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
End Walk.

Lemma P_mpi_core_add_spec : mpi_core_add_stmt psegs P_MPI_CORE_ADD.
Proof.
  unfold mpi_core_add_stmt, P_MPI_CORE_ADD.
  intros until zs. intros HX HA HB Hn LX LA LB DA DB ALX ALA ALB NZX NZA NZB ST LO SPA SX SA SB MI -> -> -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  unfold MPI_CORE_ADD_STACK in *.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (u32ro_bound _ _ _ _ HA) as AB. pose proof (u32ro_bound _ _ _ _ HB) as BB.
  pose proof (proj1 ST) as LO0.
  (* [comment removed for export] *)
  lx_run_tac (PLAN [0x22918] [] 20%N); lx_tree.
  all: lx_gc; try lx_same_mem.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22918) _ _ _ _) =>
    (let xn := constr:(n) in match goal with K : 0 <= xn + _ |- _ => rename K into BR | _ => idtac end);
    eapply (@loop_walk) with (X := X) (A := A) (B := B) (n := n) (lo := lo)
             (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (lb := Z.of_nat (length zs))
             (xs0 := xs) (ys0 := ys) (zs0 := zs) (k := Z.to_nat (n - 0)) (i := 0) (c := 0) (xs := xs) (ys := ys) (zs := zs);
    try assumption;
    lazymatch goal with
         | |- _ \/ _ => first [ destruct DA as [[EA EY]|DA']; [left; subst; repeat split; reflexivity | right; exact DA']
                              | destruct DB as [[EB EZ]|DB']; [left; subst; repeat split; reflexivity | right; exact DB'] ]
         | |- same_from _ _ _ => apply same_from_refl
         | |- add_inv _ _ _ _ _ => apply add_inv_0
         | |- 0 <= 0 < _ => klia
         | |- _ /\ _ => first [xlia LX LA LB | xlia XB NZX | xlia AB NZA | xlia BB NZB | xlia0]
         | |- munch _ _ _ => first [exact MU | apply munch_refl]
         | |- wmono _ _ _ => first [exact WM | apply wmono_refl]
         | |- _ => first [ eassumption | reflexivity | xlia0 | klia ]
         end
  | |- _ =>
    (* [comment removed for export] *)
    (let xn := constr:(n) in match goal with K : 0 <= - xn |- _ => rename K into BR | _ => idtac end);
    lx_post; first [reflexivity | eassumption | apply munch_refl | apply wmono_refl | xlia Hn BR | rewrite !lval_nonpos by xlia Hn BR; xlia0 | idtac]
  end.
  all: match goal with |- ?g => idtac "LEFT:" g end.
Qed.
