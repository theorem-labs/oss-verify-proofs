(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01aba9d0f1dc5b8f 0 2 0 1 4 1P02339c0e20c10485 0 2 0 1 20 1P02a73cab91a561d9 0 2 0 1 6 1P0857f649539487c7 0 2 0 1 38 1P089faef77e744770 0 2 0 1 7 1P12a51d5aeeda8805 0 2 0 1 4 1P16315c00417396fa 0 2 0 1 3 1P1964ac67f9c9f1b6 1 1 4 3 0 1 15 1 31 1 2 9 1 38 1P1ec0d755544d69a2 0 2 0 1 38 1P1f9b94bef8673915 0 2 0 1 38 1P26c1d70bb09705d1 0 2 0 1 7 1P2836e880c6ec69a9 0 2 0 1 21 1P29d3e78c57295c54 0 2 0 1 3 1P2a303a3ce3fb2978 0 2 0 1 7 1P2cac2a4e2956998f 0 4 0 1 13 4 14 1 30 1P3247d1503f5a47f3 0 2 0 1 4 1P375c3d0070e6ed7d 0 4 0 1 18 4 31 1 34 1P382aac8a50976c81 0 4 0 1 18 4 31 1 34 1N004add96c913b959N05114901e19421c3N0698813291e7463aN0795ad65e11799ccN0ad0052eccd1053cN131c8deadb943a92N131f4b46f5595617N13f9fd747b478907N144f9e76f45ea9a0N1599f0f54f005cdfN17a9ea633db9132eN1ab7cd7eec8a8fe6N2445232b1b1fbd4aN27fd64e90abe3500N29f8266cd598fd0bN2b0bf5c1d1c32b59N2f103c2acdd9d017N2fc0607eacba5fc8N31ccb3e2f676f972"%lxh.
Ltac2 gd_tbl_P_mpi_core_sub_int () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_sub_int_post"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.sub_int_inv"].


Definition U_MPI_CORE_SUB_INT : Z := 0x24b28.

Definition mpi_core_sub_int_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n c : Z) (xs ys : list word) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_sub_int ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lc',$4.(1.(5.(2.&40.))Lxs',(5.(2.&40.))(6.(7.$0.R13.(8.(9.O18.O17.O16.O15.R12.R11.R10.O14.O13.R?.R>.R=.R<.R;.R:.R9.R8.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R7.R6.R5.R4.)O8.(:.O18.)O7.(;.(2.&40.))R3.(<.O19.)))(6.(=.(>.(?.$4.$4.)(10.$4.$4.O6.(11.O6.(12.+4.O5.)))(13.(?.$4.$4.)))O1.R3.)(6.(14.O19.O1.R3.)(6.(15.O19.R3.)(6.(7.(2.&40.)R?.(16.&40.R2.))(6.(17.=R2.)(6.(18.(17.R2.+1.)(7.$4.R2.O4.))(6.(19.O19.R3.O6.R1.)(6.(7.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)O3.))(6.(7.(5.(2.&40.))(1<.(2.&40.)(1=.O5.)R1.)(1<.(2.&40.)(1=.O5.)O3.))(7.$4.(1>.(1?.R1.O5.)(12.R2.(20.+2.(12.+20.O5.))))(1>.(1?.O2.O5.)O4.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_sub_int_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_sub_int ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(21.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$4.PA,$4.Pn,$4.Pc,$4.Pxs,(5.(2.&40.))Pys,(5.(2.&40.))P,(19.O2.R7.R6.R2.)P,(22.O2.R8.R6.(23.R2.))P,(6.(17.=R6.)(17.R6.+2710.))P,(6.(17.=R6.)(24.R6.(20.+2.+1?.)))P,(17.R8.(25.(1;.(2.&40.)R6.)))P,(17.R9.(25.(1;.(2.&40.)R6.)))P,(18.(6.(7.$4.R;.R<.)(7.(5.(2.&40.))R7.R8.))(18.(17.(11.R;.(12.+4.(25.(1;.(2.&40.)R7.))))R<.)(17.(11.R<.(12.+4.(25.(1;.(2.&40.)R8.))))R;.)))P,(7.$4.(26.R=.+4.)=)P,(7.$4.(26.R=.+4.)=)P,(24.=R?.)P,(24.=R?.)P,(15.O2.R12.)P,(7.(2.&40.)R2;.(16.&40.R12.))P,(7.(2.&40.)R2;.(16.&40.R12.))P,(7.(2.&40.)R2;.(16.&40.R11.))P,(7.(2.&40.)R2;.(16.&40.R13.))(27.O2.(28.O2.R38.R37.R36.R35.R31.R30.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R19.R18.R16.R14.R13.R12.R11.R17.)(8.(9.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(16.&40.O1.)R18.(;.(2.&40.))R17.(<.O2.)))")
(* [comment removed for export] *).


Section Walk.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A n c lx la : Z) (xs0 ys0 : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Hc : 0 <= c < 2^31.
  Hypothesis Ln : n <= lx /\ n <= la.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis DA : (A = X /\ la = lx /\ ys0 = xs0) \/ A + 4 * la <= X \/ X + 4 * lx <= A.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
  Hypothesis AB : 0 < A /\ A + 4 * la <= 2^64.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis ALA : A mod 4 = 0.

  Notation POST := (mpi_core_sub_int_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n c xs0 ys0 m).
  Notation W := [(X, X + 4 * n)].

  (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (i ci : Z) (xs ys : list word) (x30 x31 : word) (mm : mem) (ex ea : Z),
    Z.to_nat (n - i) = k -> 0 <= i < n -> 0 <= ci < 2^31 -> ci <= 1 \/ ci = c ->
    ex = X + 4 * i -> ea = A + 4 * i ->
    u32arr usegs mm X xs -> bytes_at usegs mm A (u32s ys) -> Z.of_nat (length xs) = lx -> Z.of_nat (length ys) = la ->
    same_from (Z.to_nat i) xs xs0 -> same_from (Z.to_nat i) ys ys0 -> sub_int_inv xs i ci ys0 c ->
    munch W m mm -> wmono usegs m mm -> mem_inv usegs mm ->
    evt usegs POST
      (MS (mkR ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 ex) (Z_to_bv 64 ea) s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 A)
              (Z_to_bv 64 ci) (Z_to_bv 64 n) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1)
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 ea) (Z_to_bv 64 ex) x30 x31)
          F (Z_to_bv 64 0x24b60) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i ci xs ys x30 x31 mm ex ea Hk Hi Hci1 Hci2 Ex Ea HX HA LX LA FX FA INV MU WM MI;
      [exfalso; xlia Hk Hi|].
    lx_limb_ro HA FA i Ea (proj1 Hi) ltac:(xlia Hi LA Ln) wa VA.
    lx_limb_rw HX i Ex (proj1 Hi) ltac:(xlia Hi LX Ln) wx NX.
    lx_hide MU. lx_hide WM. lx_hide HX.
    pose proof (munch_refl ([] : list ivl) mm) as MUl0. pose proof (wmono_refl usegs mm) as WMl0.
    lx_run_tac (PLAN [0x24b60] [] 60%N); lx_tree.
    all: lx_unhide; lx_gc; try clear MUl0; try clear WMl0.
    (* [comment removed for export] *)
    all: destruct (lx_core_sub_int_exact wa ci _ Hci1 eq_refl) as [Hc' V].
    all: lx_rn_rw ex CX'; lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'.
    all: pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX (proj1 Hi) Ex MUl WMl CX') as HX';
         pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(xlia Ex Hi) ltac:(xlia Ex Hi)) as MU';
         pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24b60) _ _ _ _) =>
      (* [comment removed for export] *)
      destruct (u32ro_next _ _ _ _ _ _ _ _ _ _ _ _ _ DA HX' LX FX HA LA FA ltac:(xlia Hi Ln) Ex MUl) as (ys' & HA' & LA' & FA');
      eapply (IH (i + 1)); [xlia Hk Hi | klia | xlia Hc' | left; xlia Hc' | xlia Ex | xlia Ea
        | exact HX' | exact HA' | exact (upd_length_Z _ _ _ _ LX) | exact LA'
        | exact (same_from_upd_Z _ _ _ _ FX (proj1 Hi)) | exact (same_from_S_Z _ _ _ FA' (proj1 Hi))
        | exact (sub_int_inv_next _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VA V)
        | exact MU' | exact WM' | exact MI' ]
    | |- _ =>
      (* [comment removed for export] *)
      lx_post;
      lazymatch goal with
           | |- munch _ _ _ => exact MU'
           | |- wmono _ _ _ => exact WM'
           | |- u32arr _ _ _ _ => exact HX'
           | |- @eq nat (length _) _ => rewrite upd_length; xlia LX L0
           | |- skipn _ _ = skipn _ _ => eapply skipn_upd_Z; [exact FX | xlia Hi | klia | xlia LX L0]
           | |- lval _ ?nn - _ = _ => replace nn with (i + 1) by klia; exact (sub_int_inv_next _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VA V)
           | |- _ <= 1 \/ _ = _ => left; xlia Hc'
           | |- _ => first [reflexivity | assumption | xlia Hc']
           end
    end.
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
End Walk.

Lemma U_mpi_core_sub_int_spec : mpi_core_sub_int_stmt usegs U_MPI_CORE_SUB_INT.
Proof.
  unfold mpi_core_sub_int_stmt, U_MPI_CORE_SUB_INT.
  intros until ys. intros HX HA Hn Hc LX LA DA ALX ALA NZX NZA MI -> -> -> ->.
  pose proof (munch_refl [(X, X + 4 * n)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (u32ro_bound _ _ _ _ HA) as AB.
  (* [comment removed for export] *)
  lx_run_tac (PLAN [0x24b60] [] 30%N); lx_tree.
  all: lx_gc; try lx_same_mem.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24b60) _ _ _ _) =>
    eapply (@loop_walk) with (X := X) (A := A) (n := n) (c := c)
             (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys))
             (xs0 := xs) (ys0 := ys) (k := Z.to_nat (n - 0)) (i := 0) (ci := c) (xs := xs) (ys := ys);
    try assumption;
    lazymatch goal with
         | |- (_ = _ /\ _) \/ _ => first [ destruct DA as [[EA EY]|DA']; [left; subst; repeat split; reflexivity | right; exact DA'] ]
         | |- _ <= 1 \/ _ = _ => right; reflexivity
         | |- same_from _ _ _ => apply same_from_refl
         | |- sub_int_inv _ _ _ _ _ => apply sub_int_inv_0
         | |- 0 <= 0 < _ => klia
         | |- _ /\ _ => first [xlia LX LA | xlia XB NZX | xlia AB NZA | xlia0 | klia]
         | |- munch _ _ _ => first [exact MU | apply munch_refl]
         | |- wmono _ _ _ => first [exact WM | apply wmono_refl]
         | |- _ => first [ eassumption | reflexivity | xlia0 | klia ]
         end
  | |- _ =>
    (* [comment removed for export] *)
    (let xn := constr:(n) in match goal with K : 0 <= - xn |- _ => rename K into BR | _ => idtac end);
    lx_post; first [reflexivity | eassumption | apply munch_refl | apply wmono_refl | xlia Hc | right; reflexivity
                   | replace n with 0 by xlia Hn BR; rewrite !lval_0; change (2 ^ (32 * 0)) with 1; xlia0 | idtac]
  end.
  all: match goal with |- ?g => idtac "LEFT:" g end.
Qed.
