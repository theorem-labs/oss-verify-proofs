(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux CellsX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_shift_l () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_SHIFT_L_STACK"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.Exec.evt"; "mpi_core_shift_l_post"; "Stdlib.ZArith.BinInt.Z.div"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.negb"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "Corelib.Init.Datatypes.false"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.MpiCoreAux.lseg"; "Corelib.Init.Peano.le"; "Stdlib.Lists.List.nth_error"; "shl_inv"; "OSSVerify.KrLib.Lib.MpiCoreAux.w32"; "ltp2"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.repeat"; "shl_vz"; "Corelib.Init.Peano.lt"; "OSSVerify.KrLib.Lib.MpiCoreAux.limb32"; "Corelib.Init.Nat.sub"].


Definition P_MPI_CORE_SHIFT_L : Z := 0x22830.
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
Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L11303476357.7L11303623813.7L18926536614.7L18926716838.7L48033298669.7L48033380589.7L50363111753.700000;00D00G00J00W00j01:S1a1b2Ha2NaS1a2Ha2NaS1aS1bS1a1b2Hb1E2EaS1a1b2Ha2Hb2Ea2Eb1ES1b2Hb2Nb1a2Ha1E". (* [comment removed for export] *)
Lemma mod64_eq_cancel : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "Pa,$?.Pb,$?.P,(5.(25.=R2.)(23.R2.+10000000000000000.))P,(5.(25.=R2.)(23.R2.+10000000000000000.))P,(6.$?.(1?.R4.+10000000000000000.)(1?.R3.+10000000000000000.))(6.$?.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros a b Ha Hb E.
  destruct (Z.eq_dec a 18446744073709551616) as [Ea|Na]; destruct (Z.eq_dec b 18446744073709551616) as [Eb|Nb].
  - lia.
  - rewrite Ea, Z.mod_same, Z.mod_small in E by lia. lia.
  - rewrite Eb, Z.mod_same, Z.mod_small in E by lia. lia.
  - rewrite !Z.mod_small in E by lia. exact E.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bveqb_lit_ne : forall a b, negb (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b)) = true -> a <> b.
Proof. intros a b H E. subst. unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L11303443589.5L50363210057.500000800@S1a1b2HaS1a1b2Hb". (* [comment removed for export] *)
Lemma bveqb_lit_eq : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "Pa,$?.Pb,$?.P,(6.$2;.(2<.(2=.&40.(27.&40.R2.)(27.&40.R1.)))$2>.)P,(5.(25.=R3.)(23.R3.+10000000000000000.))P,(5.(25.=R3.)(23.R3.+10000000000000000.))(6.$?.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros a b H Ha Hb. unfold bv_eqb in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616 in H.
  apply mod64_eq_cancel; [lia|lia|]. destruct (Z.eqb_spec (a mod 18446744073709551616) (b mod 18446744073709551616)); [assumption| discriminate].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Ltac ptr_cases K := if_cases K; [ apply bveqb_lit_ne in K | apply bveqb_lit_eq in K; [|lia|lia] ].

(* [comment removed for export] *)
Definition shl_inv (ys zs : list word) (v0 i r v1 : Z) : Prop :=
  lseg ys v0 i + r * 2^(32 * (i - v0)) = lseg zs v0 i * 2^v1.
Definition ltp2 (a k : Z) : Prop := a < 2^k.
Definition shl_vz (zs xs0 : list word) (n v0 : Z) : Prop :=
  lval zs n = (lval xs0 n * 2^(32 * v0)) mod 2^(32 * n).

Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X n cnt v0 v1 lx lo : Z) (xs0 : list word) (junk : list byte).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= lx.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis XB : 0 <= X /\ X + 4 * lx <= 2^64.
  Hypothesis NZX : n = 0 \/ 0 < X.
  Hypothesis Hcnt : 0 <= cnt < 2^64.
  Hypothesis Ecnt : cnt = 32 * v0 + v1.
  Hypothesis Rv : 0 <= v0 /\ 0 <= v1 < 32.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 48.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.

  Notation POST := (mpi_core_shift_l_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n cnt xs0 lo m).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells psegs mm (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L27907200258.71L51711223320.7000000M00dS2ra2sp1n3cnt2lo3xs02LO2ys2LXS2ra2sp1n3cnt3xs02ys2LX". (* [comment removed for export] *)
  #[using="LO"] Lemma tail_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "Pys,(4.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxs0_,(2.&40.)Pxs1,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxs2,(2.&40.)Pxs3,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(19.$2?.R15.VX,R16.)P,(6.$1:.(1;.(2.&40.)R17.)(1;.(2.&40.)Vxs0,))P,(6.(4.(2.&40.))(1<.(2.&40.)(1=.Vn,)R18.)(1<.(2.&40.)(1=.Vn,)Vxs0,))P,(6.$?.(1>.R19.Vn,)(1?.(12.(1>.Vxs0,Vn,)(20.+2.Vcnt,))(20.+2.(12.+20.Vn,))))P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+30.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R19.)P,(17.$2?.Vm,R1:.)P,(18.$2?.R1;.)P,(21.$2?.R1<.Vlo,(11.(14.&40.Vsp,)-30.))P,(30.$2?.R1=.(11.(14.&40.Vsp,)-30.)(=.$31.(32.#8.Vjunk,)(=.$31.(33.Vs3,)(=.$31.(33.Vs2,)(=.$31.(33.Vs1,)(=.$31.(33.Vs0,)(=.$31.(33.Vra,)(16.$31.))))))))(28.$2?.(29.$2?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.R1=.(27.&40.(11.(14.&40.Vsp,)-30.))Vgp,Vtp,R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(27.&40.+228><.)Vfc,(:.(2.&40.))R1>.(;.$2?.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HX LX TX VX MU WM MI ST FR.
    do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish. 1: exact HX. all: assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
    Local Ltac2 Set LiaOrc.tbl := fun () => "00]0?L10351626713.82L10898104775.88L14396841314.88L14948245562.82L1723297284.85 L19524687937.82L19526868180.83L20456613186.84L21919096203.88L22029607652.88L22798285110.82L23239301274.85L23292657606.78L23292787404.81L23719047656.88L2523079385.88 L28767740167.90L29375259546.88L33045003426.88L33526306177.87L33526306177.88L35878354381.85L35878369479.85L36838947057.86L37432512624.86L37869634479.85L40474015293.86L41411776855.86L41415742316.85L43320478707.85L44015411340.85L44331378039.90L44960413355.87L46085742718.88L48108002736.85L51715542588.90L5208367034.90 L52674227083.88L54397113557.85L54401537774.86L54987412219.88L56632386087.86L62068247658.82L62965564504.89L62965564766.8700000o02O03C03D03l05406<07D08d09j0:P0;50=[0@`0AI0BO0Ch0Di0EM0FZ0Gg0HI0Hk0IM0J50Jd0KL0Kn0LP0M<0M^0Nd0P<0QB0R10R20S=0TC0To0U[0Va0WM0X30YR0[1S2ra1n3cnt2v02v13xs04Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LXS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2L02XB3NZX4Hcnt4Ecnt2Rv3SPR2LO2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1wS2ra1X1n2v02v13xs02Rv2zs2LZ3Hv01k1i2ys2Hk2Hi2LX1w2KlFS2ra1n2v02v13xs02Rv2zs2LZ1k1i2ys2Hk2LX1wS2ra1n3cnt2v02v12lx3xs02Ln2L04Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LXS2ra1n3cnt2v02v12lx3xs02Ln2L04Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LXS2ra1n3cnt2v02v12lx3xs02Ln2L04Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LXS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2L02XB3NZX4Hcnt4Ecnt2Rv3SPR2LO2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1wS2ra1X1n3cnt2v02v13xs04Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1w2KlS2ra1n2v02v13xs02Rv2zs2LZ1k1i2ys2Hk2LXS2ra1n2v02v13xs02zs2LZ1k1i2ys2Hk2LX1wS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1X1n3cnt2v02v12lo3xs02zs2LZ3Hv01i2ys3r0w2mm3xra3xt03xt13xt23xa33xa43xa53xa63xa73xs33xt33xt43xt53xt62Hk2Hi2LXS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1X1n3cnt2v02v12lx2lo3xs02Ln2L04Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys3r0w2mm3xra3xt03xt13xt23xa33xa43xa53xa63xa73xs33xt33xt43xt53xt62Hk2Hi2LX2NXS2ra1n2v02v13xs02zs2LZ3Hv01k1i2ys2Hk2LX1wS2ra1X1n3cnt2v02v13xs04Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1w2KlS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln4Hcnt4Ecnt2Rv2LO2SX2zs2LZ3Hv13Hv01k1i2ys3r0w2Hk2Hi2LX1wS2ra1n3cnt2v02v13xs04Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1wS2ra1X1n2v13xs02zs2LZ1k1i2ys2Hk2LX1wS2ra1X1n3cnt2v02v13xs03NZX4Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1w5HBarrS2ra1X1n3cnt2v02v13xs03NZX4Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1w5HBarrS2ra1n2v13xs02zs2LZ1k1i2ys2Hk2LX1wS2ra1n2v13xs02zs2LZ1k1i2ys2Hk2LX1wS2ra1n2v13xs02zs2LZ1k1i2ys2Hk2LX1wS2ra1n2v02v13xs02Rv2zs2LZ1k1i2ys2Hk2LX1wS2ra1n2v02v13xs02Rv2zs2LZ3Hv01k1i2ys2Hk2Hi2LX1wS2ra1n2v02v13xs02Rv2zs2LZ1k1i2ys2Hk2LX1wS2ra1n2v13xs02zs2LZ1k1i2ys2Hk2LX1wS2ra1n2v13xs02zs2LZ1k1i2ys2Hk2LX1wS2ra1n2v02v13xs02zs2LZ3Hv01k1i2ys2Hk2LX1w2WRS2ra1n2v13xs02zs2LZ1k1i2ys2Hk2LX1wS2ra1n3cnt2v02v13xs04Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1w1q2HqS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2L04Hcnt4Ecnt2Rv2LO2SX2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1wS2ra1n2v02v13xs02Rv2zs2LZ3Hv01k1i2ys2Hk2Hi2LX1w1X3cnt4Hcnt4Ecnt3Hv12KlS2ra1n2v02v13xs02Rv2zs2LZ3Hv01k1i2ys2Hk2Hi2LX1wFS2ra1n2v02v13xs02Rv2zs2LZ3Hv01k1i2ys2Hk2Hi2LX1w1q2Hq1X3cnt4Hcnt4Ecnt3Hv12KlS2ra1X1n3cnt2v02v13xs04Hcnt4Ecnt2Rv2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1w2KlS2ra1n2v02v13xs02Rv2zs2LZ3Hv11k1i2ys2Hk2LX1wS2ra1n2v02v13xs02Rv2zs2LZ3Hv11k1i2ys2Hk2LX1wS2ra1n2v02v13xs02Rv2zs2LZ3Hv01k1i2ys2Hk2Hi2LX1w1X3cnt4Hcnt4Ecnt3Hv12KlS2ra1n2v02v13xs02zs2LZ3Hv01k1i2ys2Hk2LX1w2WRS2ra1n2v02v13xs02Rv2zs2LZ1k1i2ys2Hk2LXS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2L04Hcnt4Ecnt2Rv3SPR2LO2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1w5HBarrS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2L04Hcnt4Ecnt2Rv3SPR2LO2zs2LZ3Hv13Hv01k1i2ys2Hk2Hi2LX1w5HBarr". (* [comment removed for export] *)
    #[using="lx Hn Ln L0 XB NZX Hcnt Ecnt Rv SPR LO SX LZ TZ ZZ VZ Hv1 Hv0"] Lemma loop2_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "Pk,$1:.Pi,$?.Pys,(4.(2.&40.))Pr0w,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxs3,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwp,(2.&40.)Pwe,(2.&40.)Pw4n,(2.&40.)P,(6.$1:.(1=.(13.Vn,R15.))R16.)P,(5.(23.Vv0,R16.)(25.R16.Vn,))P,(6.(2.&40.)R5.(27.&40.(11.VX,(12.+4.R17.))))P,(6.(2.&40.)R5.(27.&40.(11.VX,(12.+4.Vn,))))P,(6.(2.&40.)R5.(27.&40.(12.+4.Vn,)))P,(19.$2?.R17.VX,R19.)P,(6.$1:.(1;.(2.&40.)R1:.)(1;.(2.&40.)Vxs0,))P,Pq,$1:.P,(35.(1=.R1=.)R1.)(6.(3.(2.&40.))(36.(2.&40.)R1=.R2.)(36.(2.&40.)Vzs,R2.))P,(6.$?.(1>.R1<.Vv0,)(1>.Vzs,Vv0,))P,(37.R1=.Vzs,Vv0,R1>.(38.R1<.)Vv1,)P,(39.(38.R1=.)Vv1,)P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+30.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R1=.)P,(17.$2?.Vm,R1>.)P,(18.$2?.R1?.)P,(21.$2?.R20.Vlo,(11.(14.&40.Vsp,)-30.))P,(30.$2?.R21.(11.(14.&40.Vsp,)-30.)(=.$31.(32.#8.Vjunk,)(=.$31.(33.Vs3,)(=.$31.(33.Vs2,)(=.$31.(33.Vs1,)(=.$31.(33.Vs0,)(=.$31.(33.Vra,)(16.$31.))))))))(28.$2?.(29.$2?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.R21.(27.&40.(11.(14.&40.Vsp,)-30.))Vgp,Vtp,R20.R1?.R1>.R12.R11.R23.R13.(27.&40.(13.+20.Vv1,))R1=.R1<.R1;.R1:.R19.(27.&40.Vv1,)R18.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(27.&40.+228<<.)Vfc,(:.(2.&40.))R22.(;.$2?.)))")
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i ys r0w mm xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 wp we w4n
        Hk Hi -> -> -> HX LX FY E0 INV HR MU WM MI ST FR; [lia|].
      destruct (nth_error ys (Z.to_nat i)) as [w|] eqn:NX; [| apply nth_error_None in NX; lia].
      pose proof (u32arr_read psegs mm X ys i w _ HX NX ltac:(lia) eq_refl) as RDX.
      zstep. clear RDX.
      zstep. zstep. zstep.
      pose proof (u32arr_store_ok psegs mm X ys i _ HX ltac:(lia) eq_refl) as SOK.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
        pose proof (u32arr_write psegs mm X ys i v HX ltac:(lia)) as HX';
        pose proof (limb32_upd_same ys (Z.to_nat i) v ltac:(lia)) as VX end.
      assert (VW : limb32 zs (Z.to_nat i) = w32 w).
      { apply limb32_nth_error. rewrite <- FY by lia. exact NX. }
      pose proof (w32_range w) as WR.
      store_done. try clear HX.
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      lazymatch type of HX' with u32arr _ ?m1 _ (upd _ _ ?v) =>
      assert (INV' : shl_inv (upd ys (Z.to_nat i) v) zs v0 (i + 1)
                       (w32 (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 w))) ((32 - v1) mod 32))))) v1) end.
      { unfold shl_inv. rewrite !lseg_snoc, lseg_upd_hi, VX, VW, shl_carry_bits by lia.
        rewrite (shl_limb_bits w r0w v1 Hv1 HR).
        replace (32 * (i + 1 - v0)) with (32 * (i - v0) + 32) by lia. rewrite Z.pow_add_r by lia.
        apply shl_inv_step; [lia | lia | apply Z.pow_nonneg; lia | exact INV | reflexivity]. }
      assert (HR' : ltp2 (w32 (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 w))) ((32 - v1) mod 32))))) v1).
      { unfold ltp2. rewrite shl_carry_bits by lia. apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; lia.
        rewrite <- Z.pow_add_r by lia. replace (32 - v1 + v1) with 32 by lia. lia. }
      ptr_cases Kl.
      - (* [comment removed for export] *)
        eapply (IH (i + 1));
          [ lia | lia | f_equal; lia | reflexivity | reflexivity | exact HX' | rewrite upd_length; lia
          | intros q Hq; rewrite nth_error_upd_other by lia; apply FY; lia
          | unfold lseg in E0 |- *; rewrite lval_upd_ge by lia; exact E0
          | exact INV' | exact HR'
          | exact MU | exact WM | exact MI | exact ST | exact FR ].
      - (* [comment removed for export] *)
        eapply tail_walk; [ exact HX' | rewrite upd_length; lia | | | exact MU | exact WM | exact MI | exact ST | exact FR ].
        + rewrite skipn_upd_lt, <- TZ by lia. apply same_from_skipn; [| lia]. intros q Hq. apply FY. lia.
        + eapply (final_value _ _ ltac:(lia)).
          * unfold lseg in E0 |- *. rewrite lval_upd_ge by lia. exact E0.
          * replace n with (i + 1) by lia. exact INV'.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Phase2.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L14083214898.70L18890663664.70L22798355484.70L22798355613.69L23719042742.70L2424904290.70 L25876950088.70L35153059218.70L36572819330.69L37445067371.70L41415942988.70L42976763.70   L438856255.70  L54397314293.70L57080487208.70L61929812368.7000000C00m01D01[02102G03103C03j04A04O05905O05i06906LS2ra1X2v03xs02zs2LZS2ra3cnt2v02v13xs04Hcnt4Ecnt2Rv2zs2LZ1n2K2S2ra2v02v13xs02Rv2zs2LZS2ra2v02v13xs02Rv2zs2LZS2ra1n2v03xs02zs2LZ2K2S2ra1n2v03xs02Hn2zs2LZS2ra1n3cnt2v02v13xs04Hcnt4Ecnt2Rv2zs2LZ2K2S2ra1X1n3xs02zs2LZS2ra1n3cnt2v02v13xs04Hcnt4Ecnt2zs2LZ2K1S2ra2v02v13xs02Rv2zs2LZS2ra3xs02zs2LZS2ra1n3cnt2v02v13xs04Hcnt4Ecnt2Rv2zs2LZ2K2S2ra1n2v03xs02zs2LZ2K2S2ra2v02v13xs02Rv2zs2LZ2K1S2ra1n3xs02zs2LZS2ra1n3xs02Hn2zs2LZ". (* [comment removed for export] *)
    #[using="lx Hn Ln L0 XB NZX Hcnt Ecnt Rv SPR LO SX LZ TZ ZZ VZ"] Lemma phase2_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(19.$2?.R11.VX,Vzs,)P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+30.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R12.)P,(17.$2?.Vm,R13.)P,(18.$2?.R14.)P,(21.$2?.R15.Vlo,(11.(14.&40.Vsp,)-30.))P,(30.$2?.R16.(11.(14.&40.Vsp,)-30.)(=.$31.(32.#8.Vjunk,)(=.$31.(33.Vs3,)(=.$31.(33.Vs2,)(=.$31.(33.Vs1,)(=.$31.(33.Vs0,)(=.$31.(33.Vra,)(16.$31.))))))))(28.$2?.(29.$2?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.R16.(27.&40.(11.(14.&40.Vsp,)-30.))Vgp,Vtp,R15.R14.R13.(27.&40.VX,)(27.&40.Vn,)R12.R11.R10.R?.R>.R=.R<.R;.(27.&40.Vv1,)(27.&40.Vv0,)Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(27.&40.+228:8.)Vfc,(:.(2.&40.))R17.(;.$2?.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HX MU WM MI ST FR.
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
      { (* [comment removed for export] *)
        eapply tail_walk; [exact HX | exact LZ | exact TZ | | exact MU | exact WM | exact MI | exact ST | exact FR].
        unfold shl_vz in VZ. rewrite VZ. f_equal. f_equal. f_equal. lia. }
      zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      { (* [comment removed for export] *)
        eapply tail_walk; [exact HX | exact LZ | exact TZ | | exact MU | exact WM | exact MI | exact ST | exact FR].
        unfold shl_vz in VZ. rewrite VZ. rewrite <- !shl_all_out by lia. reflexivity. }
      zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
      zstep. zstep. zstep. zstep.
      eapply (loop2_walk ltac:(lia) ltac:(lia) (Z.to_nat (n - v0)) v0 zs (Z_to_bv 64 0));
        [ reflexivity | lia | f_equal; lia | f_equal; lia | f_equal; lia | exact HX | exact LZ
        | intros; reflexivity | reflexivity
        | unfold shl_inv; rewrite !lseg_empty; reflexivity
        | unfold ltp2; apply Z.pow_pos_nonneg; lia
        | exact MU | exact WM | exact MI | exact ST | exact FR ].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End WithZs.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L22213173504.74L22700267513.93L25954546496.70L29803481095.86L30819402487.71L39269347824.72L39269529826.74L41415943117.70L46598470749.91L51655972118.87L5259869074.74 L5259981440.72 L53519092896.72L56352191324.86L57419144261.70L57894741895.86L59906210512.87L64294415842.91L8365480468.87 00000D01>01R01l02L02i03F03T04E04Y05Q06I06]07707j08M08c09Q09eS2ra3xs02zc2ys2LX2LBS2ra2sp1X1n2lx2lo3xs02Ln2L02LO2SX2zc2ys3Hzc2LX2K12LB3x141HS2ra3xs02zc2ys2LX2K1S2ra1n3xs02zc2ys3Hzc2LX2LBS2ra1n2lx3xs02Ln2L02zc2ys3Hzc2LXS2ra1n3xs02Hn2zc2ys3Hzc2LX2LBS2ra1n3xs02Hn2zc2ys3Hzc2LX2LBS2ra3xs02ys2LXS2ra2sp1X1n2lx2lo3xs02Ln2L02LO2SX2zc2ys3Hzc2LX2LBS2ra3xs02zc2ys2LX2LBS2ra2sp1X1n2lx2lo3xs02Ln2L02XB3SPR2LO2zc2ys3Hzc2LX2K12LBS2ra2sp1X1n2lx2lo3xs02Ln2L02XB3SPR2LO2zc2ys3Hzc2LX2K12LBS2ra3xs02zc2ys2LX2LBS2ra1n3xs02zc2ys3Hzc2LX2LBS2ra2sp1X1n2lx2lo3xs02Ln2XB3NZX3SPR2LO2zc2ys3Hzc2LXS2ra1n2lx3xs02Ln2L02zc2ys3Hzc2LX2LBS2ra1X3xs02zc2ys2LX2LBS2ra2sp1X1n2lx2lo3xs02Ln2L02SX2zc2ys3Hzc2LX2LBS2ra3xs02zc2ys2LX2LB". (* [comment removed for export] *)
  #[using="lx Hn Ln L0 XB NZX Hcnt Ecnt Rv SPR LO SX"] Lemma zero_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "Pzc,$?.Pys,(4.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwzc,(2.&40.)P,(5.(23.=R13.)(23.R13.Vn,))P,(6.(2.&40.)R2.(27.&40.R14.))P,(19.$2?.R13.VX,R14.)P,(6.$1:.(1;.(2.&40.)R15.)(1;.(2.&40.)Vxs0,))P,(6.(4.(2.&40.))(1<.(2.&40.)(1=.Vn,)R16.)(1<.(2.&40.)(1=.Vn,)Vxs0,))P,P,(25.Vv0,Vn,)(6.$?.(1>.(3:.(2.&40.)(3;.(2.&40.)(27.&40.=)(1=.R19.))(1<.(2.&40.)(1=.R19.)R18.))Vv0,)=)P,(3<.(3:.(2.&40.)(3;.(2.&40.)(27.&40.=)(1=.R19.))(1<.(2.&40.)(1=.R19.)R18.))Vxs0,Vn,Vv0,)P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+30.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R18.)P,(17.$2?.Vm,R19.)P,(18.$2?.R1:.)P,(21.$2?.R1;.Vlo,(11.(14.&40.Vsp,)-30.))P,(30.$2?.R1<.(11.(14.&40.Vsp,)-30.)(=.$31.(32.#8.Vjunk,)(=.$31.(33.Vs3,)(=.$31.(33.Vs2,)(=.$31.(33.Vs1,)(=.$31.(33.Vs0,)(=.$31.(33.Vra,)(16.$31.))))))))(28.$2?.(29.$2?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.R1<.(27.&40.(11.(14.&40.Vsp,)-30.))Vgp,Vtp,R1;.R1:.R19.(27.&40.VX,)(27.&40.Vn,)R18.R17.R=.R16.R15.R14.R13.R12.(27.&40.Vv1,)(27.&40.Vv0,)Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(27.&40.+22894.)Vfc,(:.(2.&40.))R1=.(;.$2?.)))")
(* [comment removed for export] *).
  Proof.
    intros until wzc. intros Hzc -> HX LX TX ZZ VZ MU WM MI ST FR.
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    { (* [comment removed for export] *)
      replace (Z.to_nat zc) with 0%nat in ZZ, VZ by lia. cbn [repeat app] in ZZ, VZ. rewrite skipn_O in ZZ, VZ.
      eapply (phase2_walk ys LX TX ZZ VZ); [exact HX | exact MU | exact WM | exact MI | exact ST | exact FR]. }
    zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4. zstep. zstep. zstep.
    pose proof (firstn_skipn (Z.to_nat zc) ys) as EY. symmetry in EY.
    assert (LB : length (firstn (Z.to_nat zc) ys) = Z.to_nat zc) by (rewrite firstn_length; lia).
    rewrite EY in HX. apply u32arr_app in HX. destruct HX as [HXB HXC]. rewrite LB in HXC.
    apply u32arr_cells in HXB. rewrite LB in HXB.
    pose proof P_memset_spec as SP. unfold memset_stmt in SP.
    eapply evt_cut; [ eapply SP; [|exact MI]; rewrite !unsigned_lit by lia;
                      replace (Z.to_nat (zc * 4)) with (4 * Z.to_nat zc)%nat by lia; exact HXB | ].
    clear SP HXB. unfold memset_post. rewrite !unsigned_lit by lia.
    post_call psegs mm.
    match goal with H : rw_cells psegs ?m2 X [CB _ (repeat _ _)] |- _ =>
      apply (u32arr_of_cells psegs m2 _ _ _ (repeat (Z_to_bv 64 0) (Z.to_nat zc))) in H;
      [| rewrite u32s_repeat0; replace (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 by reflexivity; f_equal; lia ];
      rename H into HXB
    end.
    lazymatch type of HXB with u32arr _ ?m2 _ _ =>
      assert (HX' : u32arr psegs m2 X (repeat (Z_to_bv 64 0) (Z.to_nat zc) ++ skipn (Z.to_nat zc) ys)) end.
    { apply u32arr_app. split; [exact HXB|]. rewrite repeat_length.
      lazymatch type of HXC with u32arr _ _ ?a _ => replace (X + 4 * Z.of_nat (Z.to_nat zc)) with a by lia end. exact HXC. }
    clear HXB HXC.
    eapply (phase2_walk _ _ _ ZZ VZ); [exact HX' | assumption | assumption | assumption | assumption | assumption ].
    Unshelve.
    - rewrite app_length, repeat_length, skipn_length. lia.
    - rewrite skipn_app, repeat_length, skipn_skipn. rewrite (skipn_all2 (repeat _ _)) by (rewrite repeat_length; lia).
      replace (Z.to_nat n - Z.to_nat zc + Z.to_nat zc)%nat with (Z.to_nat n) by lia. exact TX.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00U0?L15783377971.75L18890656174.76L19435299363.77L20757273061.76L21118055638.76L21256647947.75L24181221586.76L2523079385.76 L26625438527.72L28767740167.80L32193124171.77L32867407698.76L3432239224.74 L34328786283.78L3434386669.73 L35900490670.76L36193842442.75L38775064854.76L40663109092.76L4487926645.77 L44960413355.77L45308908277.79L51406363094.78L51715542588.80L53380123103.79L53380753436.78L54987412219.76L62371162269.78L62965564504.79L62965564766.77L65035946358.77L65035946358.78L65577466249.76L7572214554.76 L8237819813.73 L8965110418.69 L9290789269.78 00000Q01B01f02M02g03A03a04A06c07Z08G09D09n0:W0;A0;]0<70<[0=<0=V0>e0?N0?m0?n0@W0A40AX0BA0CT0Dg0EP0F90FZ0G>0G[0Io0JUS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LXS2ra1n3cnt2v02v13xs04Hcnt4Ecnt2Rv1k1i2ys2Hk2Hi2LXS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LX2HqS2ra1n2v02v13xs02Rv1k1i2ys2Hk2Hi3Hv02LXS2ra1X2v03xs01k1i2ys2Hk2LXS2ra1X2v03xs01k1i2ys2Hk2LXS2ra1n2v03xs01k1i2ys2Hk2Hi2LX2KlS2ra1n2v03xs01k1i2ys2Hk2Hi2LX2KlS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1X1n3cnt2v02v12lx2lo3xs02Ln2L01k1i2ys2mm3xra3xt03xt13xt23xa43xa53xa63xa73xt33xt43xt53xt62Hk2Hi3Hv02LX2NXS2ra2sp1X1n2v02lx2lo3xs02Ln2LO2SX1k1i2ys2Hk2Hi3Hv02LX1wS2ra1n2v02lx3xs02Ln2L01k1i2ys2Hk2Hi3Hv02LX2HqS2ra2sp1X1n2v02lx2lo3xs02Ln2XB3NZX3SPR2LO1k1i2ys2Hk2Hi3Hv02LXS2ra1n2v02lx3xs02Ln2L01k1i2ys2Hk2Hi3Hv02LXS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LX2Kl1q2HqS2ra1n2v02lx3xs02Ln2L01k1i2ys2Hk2Hi3Hv02LXS2ra2v03xs01k1i2ys2Hk3Hv02LXS2ra1X2v03xs01k1i2ys2Hk2LXS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LX2KlS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LXS2ra1X2v03xs01k1i2ys2Hk2LXS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Hn2Ln2L04Hcnt4Ecnt2Rv2LO2SX1k1i2ys2Hk2Hi3Hv02LXS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LX1q2Hq2n0S2ra2v03xs01k1i2ys2Hk2LX1q2Hq1nFS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LX1q2Hq2n0S2ra2v03xs01k1i2ys2Hk2LX1q2HqS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LX2KlS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LX2Kl1q2HqS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2L04Hcnt4Ecnt2Rv3SPR2LO1k1i2ys2Hk2Hi3Hv02LX5HBarrS2ra2sp1X1n3cnt2v02v12lx2lo3xs02Ln2L04Hcnt4Ecnt2Rv3SPR2LO1k1i2ys2Hk2Hi3Hv02LX5HBarrS2ra1X1n2v03xs01k1i2ys2Hk2Hi3Hv02LX5HBarrS2ra1X1n2v03xs01k1i2ys2Hk2Hi3Hv02LX5HBarrS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LXS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LX2KlS2ra1n2v03xs01k1i2ys2Hk2Hi2LXS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1X1n3cnt2v02v12lo3xs01i2ys2mm3xra3xt03xt13xt23xa33xa43xa53xa63xa73xt33xt43xt53xt62Hk2Hi2LXS2ra1n2v03xs01k1i2ys2Hk2Hi3Hv02LX1q2Hq". (* [comment removed for export] *)
  #[using="lx Hn Ln L0 XB NZX Hcnt Ecnt Rv SPR LO SX"] Lemma loop1_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "Pk,$1:.Pi,$?.Pys,(4.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwp,(2.&40.)Pwi,(2.&40.)Pwneg,(2.&40.)P,(6.$1:.(1=.(13.R13.Vv0,))R14.)P,(5.(25.Vv0,R14.)(23.R14.Vn,))P,(23.+1.Vv0,)P,(6.(2.&40.)R6.(27.&40.(13.(11.VX,(12.+4.R16.))+4.)))P,(6.(2.&40.)R6.(27.&40.R17.))P,(6.(2.&40.)R6.(27.&40.(13.=(12.+4.Vv0,))))P,(19.$2?.R17.VX,R18.)P,(6.$1:.(1;.(2.&40.)R19.)(1;.(2.&40.)Vxs0,))P,Pq,$1:.P,(3=.R1.(1=.R1<.))(6.(3.(2.&40.))(36.(2.&40.)R1<.R2.)(36.(2.&40.)Vxs0,R2.))P,Pq,$1:.P,(5.(35.(1=.R1=.)R1.)(3=.R1.(1=.Vn,)))(6.$?.(3>.R1=.R2.)(3>.Vxs0,(3?.R2.(1=.Vv0,))))P,(6.(4.(2.&40.))(1<.(2.&40.)(1=.Vn,)R1<.)(1<.(2.&40.)(1=.Vn,)Vxs0,))P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+30.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R1<.)P,(17.$2?.Vm,R1=.)P,(18.$2?.R1>.)P,(21.$2?.R1?.Vlo,(11.(14.&40.Vsp,)-30.))P,(30.$2?.R20.(11.(14.&40.Vsp,)-30.)(=.$31.(32.#8.Vjunk,)(=.$31.(33.Vs3,)(=.$31.(33.Vs2,)(=.$31.(33.Vs1,)(=.$31.(33.Vs0,)(=.$31.(33.Vra,)(16.$31.))))))))(28.$2?.(29.$2?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.R20.(27.&40.(11.(14.&40.Vsp,)-30.))Vgp,Vtp,R1?.R1>.R1=.(27.&40.VX,)(27.&40.Vn,)R13.R11.R12.R1<.R1;.R1:.R19.R18.(27.&40.Vv1,)(27.&40.Vv0,)Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(27.&40.+2287<.)Vfc,(:.(2.&40.))R21.(;.$2?.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i ys mm xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wp wi wneg
      Hk Hi Hv0 -> -> -> HX LX FY HP TX MU WM MI ST FR; [lia|].
    zstep.
    destruct (nth_error ys (Z.to_nat (i - 1 - v0))) as [w|] eqn:NX; [| apply nth_error_None in NX; lia].
    pose proof (u32arr_read psegs mm X ys (i - 1 - v0) w _ HX NX ltac:(lia) ltac:(f_equal; lia)) as RDX.
    zstep. clear RDX.
    zstep.
    pose proof (u32arr_store_ok psegs mm X ys (i - 1) _ HX ltac:(lia) ltac:(f_equal; lia)) as SOK.
    zstep.
    pose proof (u32arr_write psegs mm X ys (i - 1) (sx32 w) HX ltac:(lia)) as HX'.
    assert (VW : limb32 xs0 (Z.to_nat (i - 1 - v0)) = w32 w).
    { apply limb32_nth_error. rewrite <- FY by lia. exact NX. }
    assert (HP' : forall q, (Z.to_nat (i - 1) <= q < Z.to_nat n)%nat -> limb32 (upd ys (Z.to_nat (i - 1)) (sx32 w)) q = limb32 xs0 (q - Z.to_nat v0)%nat).
    { intros q Hq. destruct (Nat.eq_dec q (Z.to_nat (i - 1))) as [->|].
      - rewrite limb32_upd_same, w32_of_sx32, <- VW by lia. f_equal. lia.
      - rewrite limb32_upd_other by lia. apply HP. lia. }
    replace (wa (X + 4 * i - 4 + 0)) with (wa (X + 4 * (i - 1))) by (f_equal; lia).
    store_done. try clear HX.
    zstep. zstep.
    if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    - eapply (IH (i - 1)); [lia | lia | lia | f_equal; lia | f_equal; lia | reflexivity | exact HX' | rewrite upd_length; lia
        | intros q Hq; rewrite nth_error_upd_other by lia; apply FY; lia
        | exact HP'
        | rewrite skipn_upd_lt by lia; exact TX
        | assumption | assumption | assumption | assumption | assumption ].
    - (* [comment removed for export] *)
      eapply (zero_walk v0 (upd ys (Z.to_nat (i - 1)) (sx32 w))); [lia | f_equal; lia | exact HX' | rewrite upd_length; lia
        | rewrite skipn_upd_lt by lia; exact TX | | | assumption | assumption | assumption | assumption | assumption ].
      + intros _. apply lval_repeat0_app. lia.
      + unfold shl_vz. apply shl_phase1_value; [lia | |].
        * intros q Hq. unfold limb32. rewrite app_nth1 by (rewrite repeat_length; lia). rewrite nth_repeat. reflexivity.
        * intros q Hq. unfold limb32 at 1. rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length, nth_skipn.
          replace (Z.to_nat v0 + (q - Z.to_nat v0))%nat with q by lia. change (limb32 (upd ys (Z.to_nat (i - 1)) (sx32 w)) q = limb32 xs0 (q - Z.to_nat v0)).
          apply HP'. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L18685880975.62L18890663537.61L18890663664.62L2211929308.62 L2424904290.62 L2424904419.61 L25876950088.62L30193599405.61L31787730492.61L3390647672.62 L35900501232.62L41415942988.62L45710574872.62L49584543722.62L58796971099.62L59289085858.62L61929812368.62L7393588011.64 L8548997424.63 00000@00_01>01]01j02702[02i03703C03W03_03l04604C04N04[04l05>S2ra1n2v03xs02K2S2ra3cnt2v02v13xs04Hcnt4Ecnt2RvS2ra3cnt2v02v13xs04Hcnt4Ecnt2RvS2ra3cnt2v02v13xs04Hcnt4Ecnt2RvS2ra1n3xs02HnS2ra1n3xs02HnS2ra1n3cnt2v02v13xs04Hcnt4Ecnt2Rv2K2S2ra2v03xs02K1S2ra2v03xs02K1S2ra1X1n3xs0S2ra2v02v13xs02Rv2K1S2ra3xs0S2ra1n2v03xs0S2ra1n3xs0S2ra1n3xs02HnS2ra2v03xs0S2ra1n3xs02HnS2ra1n2v03xs01q1HS2ra1n2v03xs02K21H". (* [comment removed for export] *)
  #[using="lx Hn Ln L0 XB NZX Hcnt Ecnt Rv SPR LO SX"] Lemma phase1_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_l ()) "Pmm,P,(2.&40.)(3.(2.&8.))Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)P,(19.$2?.R>.VX,Vxs0,)P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Vn,)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+30.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R?.)P,(17.$2?.Vm,R10.)P,(18.$2?.R11.)P,(21.$2?.R12.Vlo,(11.(14.&40.Vsp,)-30.))P,(30.$2?.R13.(11.(14.&40.Vsp,)-30.)(=.$31.(32.#8.Vjunk,)(=.$31.(33.Vs3,)(=.$31.(33.Vs2,)(=.$31.(33.Vs1,)(=.$31.(33.Vs0,)(=.$31.(33.Vra,)(16.$31.))))))))(28.$2?.(29.$2?.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Vn,Vcnt,Vxs0,Vlo,Vm,)(7.(8.Vra,(27.&40.(11.(14.&40.Vsp,)-30.))Vgp,Vtp,R13.R12.R11.(27.&40.VX,)(27.&40.Vn,)(27.&40.VX,)(27.&40.Vn,)R10.R?.R>.R=.R<.R;.(27.&40.Vv1,)(27.&40.Vv0,)Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(27.&40.+22858.)Vfc,(:.(2.&40.))R14.(;.$2?.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HX MU WM MI ST FR.
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    { (* [comment removed for export] *)
      eapply (phase2_walk xs0 eq_refl eq_refl); [ | | exact HX | assumption | assumption | assumption | assumption | assumption ].
      - intros _. apply lval_nonpos. lia.
      - unfold shl_vz. replace (32 * v0) with 0 by lia. rewrite Z.pow_0_r, Z.mul_1_r. symmetry. apply Z.mod_small. apply lval_range. lia. }
    zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    { (* [comment removed for export] *)
      eapply (zero_walk n xs0); [lia | reflexivity | exact HX | reflexivity | reflexivity | | | assumption | assumption | assumption | assumption | assumption ].
      - intros; lia.
      - unfold shl_vz. rewrite lval_repeat0_app by lia. apply shl_all_out; lia. }
    zstep. rewrite !Z.shiftl_mul_pow2 by lia. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
    zstep. zstep. zstep. zstep.
    eapply (loop1_walk (Z.to_nat (n - v0)) n xs0); [lia | lia | lia | f_equal; lia | reflexivity | f_equal; lia | exact HX | reflexivity
      | intros; reflexivity | intros; lia | reflexivity | assumption | assumption | assumption | assumption | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L29317478364.59L31378308326.58L37722846299.59L42585448788.61L42585448788.62L43059547433.56L44015103505.54L44015249564.55L46608153814.53L53816989440.5500000D00X01201n03603P03d04804H04aS2ra2sp1X3cnt2xs3SPRS2ra2sp1X3cnt2xs3SPRS2ra2sp1X3cnt2xs3SPR2MB2DPS2ra2sp1X3cnt2lo2xs4Hcnt3ALX2LO3SPA2SX2XB3SPR2HB5Ha_st5Hl_stS2ra2sp2s01X3cnt2lo2xs4Hcnt3ALX2LO3SPA2SX2XB3SPR2HB5Ha_st5Hl_st2s12s22s3S2ra2sp1X3cnt2lo2xs2LO3SPRS2ra2sp1X3cnt2xs3SPRS2ra2sp1X3cnt2xs3SPRS2ra2sp1X2xs3SPRS2ra2sp1X3cnt2xs4Hcnt3SPR". (* [comment removed for export] *)
Lemma P_mpi_core_shift_l_spec : mpi_core_shift_l_stmt psegs P_MPI_CORE_SHIFT_L.
Proof.
  unfold mpi_core_shift_l_stmt, P_MPI_CORE_SHIFT_L.
  intros until xs. intros HX Hn LX Hcnt ALX NZX XLT ST LO SPA SX MI RA -> -> ->.
  unfold MPI_CORE_SHIFT_L_STACK in *.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (u32arr_bound _ _ _ _ HX) as XB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  pose proof (Z.div_mod cnt 32 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound cnt 32 ltac:(lia)) as MB.
  pose proof (Z.div_pos cnt 32 ltac:(lia) ltac:(lia)) as DP.
  carve_frame 48%nat ST.
  do 8 zstep.
  zstep. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
  zstep. rewrite land_31_mod.
  eapply (@phase1_walk) with (v0 := cnt / 32) (v1 := cnt mod 32) (lx := Z.of_nat (length xs));
    try eassumption; try reflexivity; try lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
