(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_shift_l () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_SHIFT_L_STACK"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_shift_l_post"; "Stdlib.ZArith.BinInt.Z.div"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.negb"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lseg"; "Corelib.Init.Peano.le"; "Stdlib.Lists.List.nth_error"; "shl_inv"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.w32"; "ltp2"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.repeat"; "shl_vz"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limb32"; "Corelib.Init.Nat.sub"].


Definition U_MPI_CORE_SHIFT_L : Z := 0x23550.
Definition MPI_CORE_SHIFT_L_STACK : Z := 48.

Definition mpi_core_shift_l_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n cnt : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R12.(7.(8.O18.O17.O16.O15.R11.R10.R?.O14.O13.R>.R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(9.O18.)O7.(:.(2.&40.))R2.(;.O19.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.O6.(11.O6.(12.+4.O5.)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.O17.)$15.)(14.&40.O17.))(16.(>.$?.$?.))))O1.R2.)(5.(17.O19.O1.R2.)(5.(18.O19.R2.)(5.(19.O19.R2.O6.R1.)(5.(6.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1<.(2.&40.)(1=.O5.)R1.)(1<.(2.&40.)(1=.O5.)O3.))(5.(6.$?.(1>.R1.O5.)(1?.(12.(1>.O3.O5.)(20.+2.O4.))(20.+2.(12.+20.O5.))))(21.O19.R2.O2.(14.&40.O17.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_shift_l_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$?.Pn,$?.Pcnt,$?.Plo,$?.Pxs,(4.(2.&40.))P,(19.O2.R6.R5.R1.)P,(5.(23.=R5.)(23.R5.+2710.))P,(23.R6.(24.(1;.(2.&40.)R3.)))P,(5.(23.=R6.)(25.R6.(20.+2.+40.)))P,(6.$?.(1?.R9.+4.)=)P,(26.(6.$?.R9.=)(25.=R:.))P,(25.R;.(20.+2.+40.))P,(21.O2.R=.R9.(14.&40.R2=.))P,(23.R:.(13.(14.&40.R2>.)$15.))P,(6.$?.(1?.(14.&40.R2?.)+10.)=)P,(26.(23.(11.R?.(12.+4.(24.(1;.(2.&40.)R;.))))R<.)(23.(14.&40.R30.)R?.))P,(18.O2.R11.)P,(6.$?.(1?.(14.&40.R33.)+2.)=)P,(6.(2.&40.)R2;.(27.&40.R12.))P,(6.(2.&40.)R2;.(27.&40.R12.))P,(6.(2.&40.)R2;.(27.&40.R12.))(28.O2.(29.O2.R37.R36.R35.R34.R30.R2?.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R18.R17.R15.R14.R13.R11.R12.R16.)(7.(8.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(27.&40.O1.)R17.(:.(2.&40.))R16.(;.O2.)))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L30628020411.8L40780903386.8L42837678768.700000100800CFS1j1a1HS1T1l1v1a1H". (* [comment removed for export] *)
Lemma skipn_upd : forall {T} (l : list T) j v a, (a <= j)%nat -> skipn a (upd l j v) = upd (skipn a l) (j - a) v.
Proof.
  intros T l. induction l as [|x l IH]; intros [|j] v [|a] H; cbn; try reflexivity; try lia.
  rewrite IH by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L51714592737.8L61075372852.8L65382987841.800000<00H00WS1a1b1j2Hj1HS1a1b1j2Hj1HS1a1b1j2Ha2Hj1H". (* [comment removed for export] *)
Lemma lseg_upd_hi : forall ws a b j v, 0 <= a -> (Z.to_nat b <= j)%nat -> lseg (upd ws j v) a b = lseg ws a b.
Proof.
  intros ws a b j v Ha Hj. unfold lseg.
  destruct (Nat.le_gt_cases (Z.to_nat a) j).
  - rewrite skipn_upd by lia. apply lval_upd_ge. lia.
  - rewrite skipn_upd_lt by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shl_inv_step : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "PLys,$?.PLzs,$?.PM,$?.Px,$?.Pr0,$?.Pr1,$?.Pv1,$?.P,(5.(25.=R1.)(25.R1.+20.))P,(23.=R5.)P,(23.=R7.)P,(6.$?.(11.R:.(12.R6.R8.))(12.R9.(20.+2.R4.)))P,(6.$?.R6.(2:.R8.(20.+2.(13.+20.R5.))))(6.$?.(11.(11.R<.(12.R:.(11.(1?.(12.R9.(20.+2.R6.))(20.+2.+20.))R8.)))(12.R7.(12.R:.(20.+2.+20.))))(12.(11.R;.(12.R:.R9.))(20.+2.R6.)))")
(* [comment removed for export] *).
Proof.
  intros Lys Lzs M x r0 r1 v1 Hv Hx HM INV ->.
  pose proof (shl_step_arith v1 x Hv Hx) as E. nia.
Qed.

(* [comment removed for export] *)
Definition shl_inv (ys zs : list word) (v0 i r v1 : Z) : Prop :=
  lseg ys v0 i + r * 2^(32 * (i - v0)) = lseg zs v0 i * 2^v1.
Definition ltp2 (a k : Z) : Prop := a < 2^k.
Definition shl_vz (zs xs0 : list word) (n v0 : Z) : Prop :=
  lval zs n = (lval xs0 n * 2^(32 * v0)) mod 2^(32 * n).

Lemma upd_firstn_app : forall (l r : list word) j v, (j < length l)%nat ->
  upd (firstn (S j) l ++ r) j v = firstn j l ++ v :: r.
Proof.
  induction l as [|x l IH]; intros r j v H; [cbn in H; lia|].
  destruct j as [|j]; [reflexivity|].
  cbn [firstn app upd]. rewrite IH by (cbn in H; lia). reflexivity.
Qed.

Lemma zero_step : forall (l : list word) (zc j : Z) (v : word), 1 <= j <= zc -> (Z.to_nat zc <= length l)%nat ->
  upd (firstn (Z.to_nat j) l ++ repeat v (Z.to_nat (zc - j)) ++ skipn (Z.to_nat zc) l) (Z.to_nat (j - 1)) v
  = firstn (Z.to_nat (j + -1)) l ++ repeat v (Z.to_nat (zc - (j + -1))) ++ skipn (Z.to_nat zc) l.
Proof.
  intros l zc j v Hj Hl.
  replace (Z.to_nat j) with (S (Z.to_nat (j - 1))) by lia.
  replace (Z.to_nat (j + -1)) with (Z.to_nat (j - 1)) by lia.
  replace (Z.to_nat (zc - (j + -1))) with (S (Z.to_nat (zc - j))) by lia.
  rewrite upd_firstn_app by lia. reflexivity.
Qed.

Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X n cnt v0 v1 lx lo : Z) (xs0 : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= lx.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis XB : 0 <= X /\ X + 4 * lx <= 2^64.
  Hypothesis NZX : n = 0 \/ 0 < X.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis Hcnt : 0 <= cnt < 2^64.
  Hypothesis Ecnt : cnt = 32 * v0 + v1.
  Hypothesis Rv : 0 <= v0 /\ 0 <= v1 < 32.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 48.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.

  Notation POST := (mpi_core_shift_l_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n cnt xs0 lo m).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - 48, bv_unsigned sp)].

  Local Ltac one_x := first [ reflexivity | lia
    | match goal with E : ?e = 1 |- context [?e] => is_var e; rewrite E; reflexivity end
    | match goal with |- context [0 <? ?t] =>
        let XP := fresh "XP" in
        assert (XP : 0 < t) by (destruct NZX; [lia|]; try unfold zlow; rewrite ?Z.mod_small by lia; lia);
        rewrite (proj2 (Z.ltb_lt 0 t) XP); reflexivity end ].

  Section WithZs.
    (* [comment removed for export] *)
    Variable zs : list word.
    Hypothesis LZ : length zs = length xs0.
    Hypothesis TZ : skipn (Z.to_nat n) zs = skipn (Z.to_nat n) xs0.
    Hypothesis ZZ : v0 < n -> lval zs v0 = 0.
    Hypothesis VZ : shl_vz zs xs0 n v0.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L11007443802.50L20755138719.50L23674927613.50L32362477456.50L37443001423.50L39543232498.50L51692035399.50L57868128085.50L68322786029.5000000R00n01X02702P02f03E03j04OS2ra1n2v02v13xs02Rv2zs2LZ2ys2Hv2E0S2ra1n2v02v13xs02Rv2zs2LZ2HvS2ra1n3cnt2v02v13xs04Hcnt4Ecnt2Rv2zs2LZ2HvS2ra1n2v02v13xs02Rv2zs2LZ2ZZ2HvS2ra1n2v02v13xs02Rv2zs2LZS2ra1n2v02v13xs02zs2LZS2ra1n2v02v13xs02Hn2Rv2zs2LZ2HvS2ra1n3cnt2v02v13xs04Ecnt2Rv2zs2LZ2HvS2ra1n2v02v13xs02Rv2zs2LZ2ys1r2Hv3INV". (* [comment removed for export] *)
    #[using="ra Hn Hcnt Ecnt Rv LZ ZZ VZ"] Lemma final_value : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "Pys,(4.(2.&40.))Pr,$?.P,(25.Vv0,Vn,)P,(6.$?.(1>.R3.Vv0,)(1>.Vzs,Vv0,))P,(6.$?.(11.(34.R4.Vv0,Vn,)(12.R3.(20.+2.(12.+20.(13.Vn,Vv0,)))))(12.(34.Vzs,Vv0,Vn,)(20.+2.Vv1,)))(6.$?.(1>.R5.Vn,)(1?.(12.(1>.Vxs0,Vn,)(20.+2.Vcnt,))(20.+2.(12.+20.Vn,))))")
(* [comment removed for export] *).
    Proof.
      intros ys r Hv E0 INV.
      rewrite (shl_phase2_value zs ys n v0 v1 r) by first [lia | apply ZZ; lia | exact E0 | exact INV].
      unfold shl_vz in VZ. rewrite VZ. rewrite Z.mul_mod_idemp_l by (apply Z.pow_nonzero; lia).
      rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. f_equal. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Section Phase2.
    Hypothesis Hv1 : 0 < v1 < 32.
    Hypothesis Hv0 : v0 < n.

    (* [comment removed for export] *)
    #[using="ra lx Hn Ln L0 XB NZX ALX Hcnt Ecnt Rv SPR LO SX RA LZ TZ ZZ VZ Hv1 Hv0"] Lemma loop2_walk :
      forall (k : nat) (i : Z) (ys : list word) (r0w : word) (mm : mem) (xt2 xt3 xt4 xt5 xt6 : word)
             (ep ec0 ec5 ev1 esh : Z),
      Z.to_nat (n - i) = k -> v0 <= i < n ->
      ep = X + 4 * i -> ec0 = 1 -> ec5 = 1 -> ev1 = v1 -> esh = 32 - v1 ->
      u32arr usegs mm X ys -> length ys = length xs0 ->
      (forall q, (Z.to_nat i <= q)%nat -> nth_error ys q = nth_error zs q) ->
      lval ys v0 = lval zs v0 ->
      shl_inv ys zs v0 i (w32 r0w) v1 -> ltp2 (w32 r0w) v1 ->
      munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp) ->
      evt usegs POST
        (MS (mkR ra sp gp tp (Z_to_bv 64 ec0) (Z_to_bv 64 ep) xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 ev1)
                 (Z_to_bv 64 i) (Z_to_bv 64 esh) (Z_to_bv 64 ec5) (Z_to_bv 64 ep) r0w s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x23650) fc None mm (seg_rom usegs)).
    Proof.
      induction k as [|k IH]; intros i ys r0w mm xt2 xt3 xt4 xt5 xt6 ep ec0 ec5 ev1 esh
        Hk Hi Ep Ec0 Ec5 Ev1 Esh HX LX FY E0 INV HR MU WM MI ST; [exfalso; lia|].
      subst ev1 esh.
      assert (XP : 0 < X) by (destruct NZX; lia).
      lx_limb_rw HX i Ep ltac:(lia) ltac:(lia) w NX.
      lx_hide HX. lx_hide MU. lx_hide WM.
      lx_run_tac (PLAN [0x23670] [] 40%N). lx_tree.
      all: lx_unhide; lx_same_mem; lx_gc.
      rewrite lx_sx32. replace (- v1 + 32) with (32 - v1) by lia.
      zstep. zstep. zstep.
      lx_mkR. lx_hide HX. lx_hide MU. lx_hide WM.
      pose proof (munch_refl ([] : list ivl) mm) as MUl0. pose proof (wmono_refl usegs mm) as WMl0.
      lx_run_tac (PLAN [0x23650] [] 40%N). lx_tree.
      all: lx_unhide; lx_gc; try clear MUl0; try clear WMl0.
      all: lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'.
      all: match goal with CX' : rw_cells usegs ?m2 ?e [C4 ?vn] |- context [MS _ _ _ _ _ ?m2 _] =>
             pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX ltac:(lia) Ep MUl WMl CX') as HX' end.
      all: pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(lia) ltac:(lia)) as MU'.
      all: pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
      all: match goal with K : u32arr _ _ X (upd _ _ ?vn) |- _ =>
             pose proof (limb32_upd_same ys (Z.to_nat i) vn ltac:(lia)) as VX;
             assert (LX' : length (upd ys (Z.to_nat i) vn) = length xs0) by (rewrite upd_length; exact LX) end.
      all: assert (VW : limb32 zs (Z.to_nat i) = w32 w) by (apply limb32_nth_error; rewrite <- FY by lia; exact NX).
      all: pose proof (w32_range w) as WR.
      all: lazymatch type of HX' with u32arr _ ?m1 _ (upd _ _ ?v) =>
        assert (INV' : shl_inv (upd ys (Z.to_nat i) v) zs v0 (i + 1)
                         (w32 (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 w))) ((32 - v1) mod 32))))) v1)
          by (unfold shl_inv; rewrite !lseg_snoc, lseg_upd_hi, VX, VW, shl_carry_bits by lia;
              rewrite (shl_limb_bits w r0w v1 Hv1 HR);
              replace (32 * (i + 1 - v0)) with (32 * (i - v0) + 32) by lia; rewrite Z.pow_add_r by lia;
              apply shl_inv_step; [exact Hv1 | lia | apply Z.pow_nonneg; lia | exact INV | reflexivity]) end.
      all: assert (HR' : ltp2 (w32 (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 w))) ((32 - v1) mod 32))))) v1)
        by (unfold ltp2; rewrite shl_carry_bits by exact Hv1; apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|];
            rewrite <- Z.pow_add_r by lia; replace (32 - v1 + v1) with 32 by lia; lia).
      all: lazymatch goal with
      | |- context [MS _ _ (Z_to_bv 64 0x23650) _ _ _ _] =>
        (* [comment removed for export] *)
        eapply (IH (i + 1));
          [ lia | klia | lia | exact Ec0 | exact Ec5 | lia | lia | exact HX' | exact LX'
          | intros q Hq; rewrite nth_error_upd_other by lia; apply FY; lia
          | unfold lseg in E0 |- *; rewrite lval_upd_ge by lia; exact E0
          | exact INV' | exact HR' | exact MU' | exact WM' | exact MI' | exact ST' ]
      | |- _ =>
        (* [comment removed for export] *)
        assert (EI : i + 1 = n) by klia;
        lx_post;
        lazymatch goal with
        | |- munch _ _ _ => exact MU'
        | |- wmono _ _ _ => exact WM'
        | |- mem_inv _ _ => exact MI'
        | |- u32arr _ _ _ _ => exact HX'
        | |- @eq nat (length _) _ => exact LX'
        | |- skipn _ _ = skipn _ _ =>
            rewrite skipn_upd_lt, <- TZ by lia; apply same_from_skipn; [| rewrite LZ; exact LX]; intros q Hq; apply FY; lia
        | |- lval _ _ = _ =>
            eapply (final_value _ _ ltac:(lia));
              [ unfold lseg in E0 |- *; rewrite lval_upd_ge by lia; exact E0 | rewrite <- EI; exact INV' ]
        | |- stk _ _ _ _ => exact ST'
        end
      end.
    Qed.
  End Phase2.

    (* [comment removed for export] *)
    #[using="ra lx Hn Ln L0 XB NZX ALX Hcnt Ecnt Rv SPR LO SX RA LZ TZ ZZ VZ"] Lemma phase2_walk :
      forall (mm : mem) (xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      u32arr usegs mm X zs ->
      munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp) ->
      evt usegs POST
        (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 cnt)
                 (Z_to_bv 64 v0) (Z_to_bv 64 0) xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0x23620) fc None mm (seg_rom usegs)).
    Proof.
      intros mm xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HX MU WM MI ST.
      assert (EV1 : Z.land cnt 31 = v1) by (rewrite land_31_mod; symmetry; apply (Z.mod_unique cnt 32 v0 v1); lia).
      lx_run_tac (PLAN [0x23650] [] 40%N). lx_tree.
      all: lx_same_mem; lx_gc.
      all: rewrite ?EV1 in *.
      all: lazymatch goal with
      | |- context [MS _ _ (Z_to_bv 64 0x23650) _ _ _ _] =>
        eapply (loop2_walk ltac:(klia) ltac:(klia) (Z.to_nat (n - v0)) v0 zs (Z_to_bv 64 0));
          [ reflexivity | klia | lia | one_x | one_x | lia | lia | exact HX | exact LZ
          | intros; reflexivity | reflexivity
          | unfold shl_inv; rewrite !lseg_empty; reflexivity
          | unfold ltp2; apply Z.pow_pos_nonneg; lia
          | exact MU | exact WM | exact MI | exact ST ]
      | |- _ =>
        (* [comment removed for export] *)
        lx_post;
        lazymatch goal with
        | |- munch _ _ _ => exact MU
        | |- wmono _ _ _ => exact WM
        | |- mem_inv _ _ => exact MI
        | |- u32arr _ _ _ _ => exact HX
        | |- @eq nat (length _) _ => exact LZ
        | |- skipn _ _ = skipn _ _ => exact TZ
        | |- stk _ _ _ _ => exact ST
        | |- lval _ _ = _ =>
            unfold shl_vz in VZ; rewrite VZ;
            first [ assert (V1 : v1 = 0) by klia; f_equal; f_equal; f_equal; lia
                  | rewrite <- !shl_all_out by lia; reflexivity ]
        end
      end.
    Qed.
  End WithZs.

  (* [comment removed for export] *)
  #[using="ra lx Hn Ln L0 XB NZX ALX Hcnt Ecnt Rv SPR LO SX RA"] Lemma zero_walk : forall (zc : Z) (ys0 : list word),
    1 <= zc <= n -> length ys0 = length xs0 -> skipn (Z.to_nat n) ys0 = skipn (Z.to_nat n) xs0 ->
    (v0 < n -> lval (repeat (Z_to_bv 64 0) (Z.to_nat zc) ++ skipn (Z.to_nat zc) ys0) v0 = 0) ->
    shl_vz (repeat (Z_to_bv 64 0) (Z.to_nat zc) ++ skipn (Z.to_nat zc) ys0) xs0 n v0 ->
    forall (k : nat) (j : Z) (ys : list word) (mm : mem) (xt2 xt3 xt4 xt5 xt6 : word) (c0 c5 p1 p7 : Z),
    Z.to_nat j = k -> 1 <= j <= zc -> c0 = 1 -> c5 = 1 -> p1 = X + 4 * j - 4 -> p7 = X + 4 * (j - 1) ->
    u32arr usegs mm X ys ->
    ys = firstn (Z.to_nat j) ys0 ++ repeat (Z_to_bv 64 0) (Z.to_nat (zc - j)) ++ skipn (Z.to_nat zc) ys0 ->
    munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp) ->
    evt usegs POST
      (MS (mkR ra sp gp tp (Z_to_bv 64 c0) (Z_to_bv 64 p1) xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 cnt)
               (Z_to_bv 64 v0) (Z_to_bv 64 0) (Z_to_bv 64 c5) (Z_to_bv 64 j) (Z_to_bv 64 p7) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x235F8) fc None mm (seg_rom usegs)).
  Proof.
    intros zc ys0 ZC LY0 TY0 ZZ0 VZ0 k. induction k as [|k IH];
      intros j ys mm xt2 xt3 xt4 xt5 xt6 c0 c5 p1 p7 Hk Hj Ec0 Ec5 Ep1 Ep7 HX EY MU WM MI ST; [exfalso; lia|].
    assert (XP : 0 < X) by (destruct NZX; lia).
    assert (LY : length ys = length xs0) by (rewrite EY, !app_length, firstn_length, repeat_length, skipn_length; lia).
    lx_limb_rw HX (j - 1) Ep7 ltac:(lia) ltac:(lia) w NX.
    lx_hide HX. lx_hide MU. lx_hide WM.
    pose proof (munch_refl ([] : list ivl) mm) as MUl0. pose proof (wmono_refl usegs mm) as WMl0.
    lx_run_tac (PLAN [0x235F8; 0x23620] [] 40%N). lx_tree.
    all: lx_unhide; lx_gc; try clear MUl0; try clear WMl0.
    all: lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'.
    all: match goal with CX' : rw_cells usegs ?m2 ?e [C4 ?vn] |- context [MS _ _ _ _ _ ?m2 _] =>
           pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX ltac:(lia) Ep7 MUl WMl CX') as HX' end.
    all: pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(lia) ltac:(lia)) as MU'.
    all: pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    all: rewrite EY, zero_step in HX' by lia.
    all: lazymatch goal with
    | |- context [MS _ _ (Z_to_bv 64 0x235F8) _ _ _ _] =>
      eapply (IH (j + -1)); [lia | klia | exact Ec0 | exact Ec5 | lia | lia | exact HX' | reflexivity
        | exact MU' | exact WM' | exact MI' | exact ST']
    | |- _ =>
      (* [comment removed for export] *)
      assert (J1 : j + -1 = 0) by klia; rewrite J1, Z.sub_0_r in HX'; cbn [firstn app Z.to_nat] in HX';
      assert (LZ' : length (repeat (Z_to_bv 64 0) (Z.to_nat zc) ++ skipn (Z.to_nat zc) ys0) = length xs0)
        by (rewrite app_length, repeat_length, skipn_length; lia);
      assert (TZ' : skipn (Z.to_nat n) (repeat (Z_to_bv 64 0) (Z.to_nat zc) ++ skipn (Z.to_nat zc) ys0) = skipn (Z.to_nat n) xs0)
        by (rewrite skipn_app, repeat_length, skipn_skipn; rewrite (skipn_all2 (repeat _ _)) by (rewrite repeat_length; lia);
            replace (Z.to_nat n - Z.to_nat zc + Z.to_nat zc)%nat with (Z.to_nat n) by lia; exact TY0);
      eapply (phase2_walk (repeat (Z_to_bv 64 0) (Z.to_nat zc) ++ skipn (Z.to_nat zc) ys0) LZ' TZ' ZZ0 VZ0);
        [exact HX' | exact MU' | exact WM' | exact MI' | exact ST']
    end.
  Qed.

  (* [comment removed for export] *)
  #[using="ra lx Hn Ln L0 XB NZX ALX Hcnt Ecnt Rv SPR LO SX RA"] Lemma loop1_walk :
    forall (k : nat) (i : Z) (ys : list word) (mm : mem) (xt5 xt6 : word) (e0 e1 e2 e3 e4 e5 e7 : Z),
    Z.to_nat (i - v0) = k -> v0 < i <= n -> 1 <= v0 ->
    e0 = 2305843009213693951 -> e1 = 1 -> e2 = X - 4 * v0 -> e3 = 2305843009213693951 - v0 -> e4 = 4 * i - 4 ->
    e5 = 1 -> e7 = 18446744073709551615 - X ->
    u32arr usegs mm X ys -> length ys = length xs0 ->
    (forall q, (q < Z.to_nat i)%nat -> nth_error ys q = nth_error xs0 q) ->
    (forall q, (Z.to_nat i <= q < Z.to_nat n)%nat -> limb32 ys q = limb32 xs0 (q - Z.to_nat v0)%nat) ->
    skipn (Z.to_nat n) ys = skipn (Z.to_nat n) xs0 ->
    munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp) ->
    evt usegs POST
      (MS (mkR ra sp gp tp (Z_to_bv 64 e0) (Z_to_bv 64 e1) (Z_to_bv 64 e2) s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 cnt)
               (Z_to_bv 64 v0) (Z_to_bv 64 0) (Z_to_bv 64 e5) (Z_to_bv 64 i) (Z_to_bv 64 e7) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               (Z_to_bv 64 e3) (Z_to_bv 64 e4) xt5 xt6)
          F (Z_to_bv 64 0x23594) fc None mm (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros i ys mm xt5 xt6 e0 e1 e2 e3 e4 e5 e7
      Hk Hi Hv0 E0 E1 E2 E3 E4 E5 E7 HX LX FY HP TX MU WM MI ST; [exfalso; lia|].
    assert (XP : 0 < X) by (destruct NZX; lia).
    destruct (nth_error ys (Z.to_nat (i - 1 - v0))) as [w|] eqn:NXs; [| exfalso; apply nth_error_None in NXs; lia].
    pose proof (u32ro_cell_at mm X ys (i - 1 - v0) (e2 + e4) w (u32arr_ro _ _ _ _ HX) NXs ltac:(lia) ltac:(lia)) as CS.
    assert (Ew : X + e4 = X + 4 * (i - 1)) by lia.
    lx_limb_rw HX (i - 1) Ew ltac:(lia) ltac:(lia) wd NX.
    lx_hide HX. lx_hide MU. lx_hide WM.
    pose proof (munch_refl ([] : list ivl) mm) as MUl0. pose proof (wmono_refl usegs mm) as WMl0.
    lx_run_tac (PLAN [0x23594; 0x235F8] [] 60%N). lx_tree.
    all: lx_unhide; lx_gc; try clear MUl0; try clear WMl0.
    all: lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'.
    all: match type of MUl with munch [(?a, ?b)] _ _ => replace b with (a + 4) in MUl by lia end.
    all: match goal with CX' : rw_cells usegs ?m2 ?e [C4 ?vn] |- context [MS _ _ _ _ _ ?m2 _] =>
           rewrite lx_sx32 in CX';
           pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX ltac:(lia) Ew MUl WMl CX') as HX' end.
    all: pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(lia) ltac:(lia)) as MU'.
    all: pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    all: assert (VW : limb32 xs0 (Z.to_nat (i - 1 - v0)) = w32 w) by (apply limb32_nth_error; rewrite <- FY by lia; exact NXs).
    all: assert (HP' : forall q, (Z.to_nat (i - 1) <= q < Z.to_nat n)%nat ->
                         limb32 (upd ys (Z.to_nat (i - 1)) (sx32 w)) q = limb32 xs0 (q - Z.to_nat v0)%nat)
      by (intros q Hq; destruct (Nat.eq_dec q (Z.to_nat (i - 1))) as [->|NE];
          [ rewrite limb32_upd_same, w32_of_sx32, <- VW by lia; f_equal; lia
          | rewrite limb32_upd_other by lia; apply HP; lia ]).
    all: assert (LX' : length (upd ys (Z.to_nat (i - 1)) (sx32 w)) = length xs0) by (rewrite upd_length; exact LX).
    all: lazymatch goal with
    | |- context [MS _ _ (Z_to_bv 64 0x23594) _ _ _ _] =>
      eapply (IH (i + -1)); [lia | klia | exact Hv0 | exact E0 | exact E1 | exact E2 | exact E3 | lia | exact E5 | exact E7
        | exact HX' | exact LX'
        | intros q Hq; rewrite nth_error_upd_other by lia; apply FY; lia
        | exact HP'
        | rewrite skipn_upd_lt by lia; exact TX
        | exact MU' | exact WM' | exact MI' | exact ST' ]
    | |- _ =>
      (* [comment removed for export] *)
      assert (EI : i - 1 = v0) by klia;
      eapply (zero_walk v0 (upd ys (Z.to_nat (i - 1)) (sx32 w)));
        [ lia | exact LX' | rewrite skipn_upd_lt by lia; exact TX | | | reflexivity | lia | one_x | one_x | lia | lia
        | exact HX' | | exact MU' | exact WM' | exact MI' | exact ST' ];
        [ intros _; apply lval_repeat0_app; lia
        | unfold shl_vz; apply shl_phase1_value; [lia | |];
          [ intros q Hq; unfold limb32; rewrite app_nth1 by (rewrite repeat_length; lia); rewrite nth_repeat; reflexivity
          | intros q Hq; unfold limb32 at 1; rewrite app_nth2 by (rewrite repeat_length; lia); rewrite repeat_length, nth_skipn;
            replace (Z.to_nat v0 + (q - Z.to_nat v0))%nat with q by lia;
            change (limb32 (upd ys (Z.to_nat (i - 1)) (sx32 w)) q = limb32 xs0 (q - Z.to_nat v0)); apply HP'; lia ]
        | match goal with |- _ = firstn (Z.to_nat ?jj) _ ++ _ => replace jj with v0 by lia end;
          rewrite Z.sub_diag; cbn [repeat app Z.to_nat]; symmetry; apply firstn_skipn ]
    end.
  Qed.

  (* [comment removed for export] *)
  #[using="ra lx Hn Ln L0 XB NZX ALX Hcnt Ecnt Rv SPR LO SX RA"] Lemma phase1_walk :
    forall (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    u32arr usegs m X xs0 -> stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m ->
    evt usegs POST
      (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 cnt) xa3 xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x23550) fc None m (seg_rom usegs)).
  Proof.
    intros xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HX ST MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (EV0 : Z.shiftr cnt 5 = v0)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 5) with 32; symmetry; apply (Z.div_unique cnt 32 v0 v1); lia).
    lx_run_tac (PLAN [0x23594; 0x235F8; 0x23620] [] 60%N). lx_tree.
    all: lx_same_mem; lx_gc.
    all: rewrite ?EV0 in *.
    all: lazymatch goal with
    | |- context [MS _ _ (Z_to_bv 64 0x23594) _ _ _ _] =>
      eapply (loop1_walk (Z.to_nat (n - v0)) n xs0);
        [ reflexivity | klia | klia | one_x | one_x | lia | lia | lia | one_x | lia
        | exact HX | reflexivity | intros; reflexivity | intros; lia | reflexivity
        | exact MU | exact WM | exact MI | exact ST ]
    | |- context [MS _ _ (Z_to_bv 64 0x235F8) _ _ _ _] =>
      (* [comment removed for export] *)
      eapply (zero_walk n xs0);
        [ klia | reflexivity | reflexivity | intros; lia | | reflexivity | klia | one_x | one_x | lia | lia | exact HX
        | | exact MU | exact WM | exact MI | exact ST ];
        [ unfold shl_vz; rewrite lval_repeat0_app by lia; apply shl_all_out; lia
        | replace (Z.to_nat (n - n)) with 0%nat by lia; cbn [repeat app]; symmetry; apply firstn_skipn ]
    | |- _ =>
      (* [comment removed for export] *)
      eapply (phase2_walk xs0 eq_refl eq_refl); [ | | exact HX | exact MU | exact WM | exact MI | exact ST ];
        [ intros HV; apply lval_nonpos; lia
        | unfold shl_vz; destruct (Z.eq_dec v0 0) as [V0|V0];
          [ rewrite V0, Z.mul_0_r, Z.pow_0_r, Z.mul_1_r; symmetry; apply Z.mod_small; apply lval_range; lia
          | rewrite !lval_nonpos by lia; reflexivity ] ]
    end.
  Qed.
End Walk.

Lemma U_mpi_core_shift_l_spec : mpi_core_shift_l_stmt usegs U_MPI_CORE_SHIFT_L.
Proof.
  unfold mpi_core_shift_l_stmt, U_MPI_CORE_SHIFT_L.
  intros until xs. intros HX Hn LX Hcnt ALX NZX XLT ST LO SPA SX MI RA -> -> ->.
  unfold MPI_CORE_SHIFT_L_STACK in *.
  pose proof (u32arr_bound _ _ _ _ HX) as XB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2 ^ 64) in SPR.
  pose proof (Z.div_mod cnt 32 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound cnt 32 ltac:(lia)) as MB.
  pose proof (Z.div_pos cnt 32 ltac:(lia) ltac:(lia)) as DP.
  eapply (@phase1_walk) with (v0 := cnt / 32) (v1 := cnt mod 32) (lx := Z.of_nat (length xs));
    try eassumption; try reflexivity; try lia.
Qed.

