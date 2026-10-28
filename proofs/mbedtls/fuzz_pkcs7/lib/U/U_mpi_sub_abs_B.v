(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_cmp U_mpi_sub_abs_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_sub_abs_B () : Init.string Init.list := ["Corelib.Init.Datatypes.app"; "stdpp.bitvector.definitions.bv"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Lists.ListDef.skipn"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.eq"; "splice3"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limb32"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_sub_abs_C.sub_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_sub_abs_C.sub_C1_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_cmp.SIGF"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.USpec.MpiOpnd.opnd_at"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"].


Definition U_CALLOC : Z := 0x3f960.
Definition U_MEMCPY : Z := 0x46a40.
Definition U_MEMSET : Z := 0x46e44.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition splice3 (xs ys : list word) (n nA n1 : Z) : list word := ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_B ()) "(0.(1.&40.)(2.(1.&40.)(3.O3.)O5.)(0.(1.&40.)(2.(1.&40.)(3.(4.O2.O3.))(5.(1.&40.)(3.O3.)O4.))(6.(1.&40.)(7.&40.=)(3.(4.O1.O2.)))))")
(* [comment removed for export] *).

Lemma limb32_app_l : forall (a b : list word) k, (k < length a)%nat -> limb32 (a ++ b) k = limb32 a k.
Proof. intros. unfold limb32. rewrite app_nth1 by assumption. reflexivity. Qed.
Lemma limb32_app_r : forall (a b : list word) k, (length a <= k)%nat -> limb32 (a ++ b) k = limb32 b (k - length a).
Proof. intros. unfold limb32. rewrite app_nth2 by assumption. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L3397252380.500000<S1a1m1k1H2H0". (* [comment removed for export] *)
Lemma limb32_firstn : forall (a : list word) m k, (k < m)%nat -> limb32 (firstn m a) k = limb32 a k.
Proof. intros a m k H. unfold limb32. rewrite nth_firstn. destruct (Nat.ltb_spec k m); [reflexivity| lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L39167884333.3000007S1m1k1H". (* [comment removed for export] *)
Lemma limb32_repeat0 : forall m k, limb32 (repeat (Z_to_bv 64 0) m) k = 0.
Proof.
  intros m k. unfold limb32. destruct (Nat.lt_ge_cases k m).
  - rewrite nth_repeat_lt by assumption. reflexivity.
  - rewrite nth_overflow by (rewrite repeat_length; lia). reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L13632882778.17L14083774679.12L14775407236.18L15354766658.17L3191970541.18 L35696711465.15L49106898702.17L53358380200.18L58434376815.11L61953425476.1300000W00n01W02:02g03O04604f05805QS2xs2ys1n2nA2n12Hn1a1c2La2Lb2Lc1k2H12H2S2xs2ys1n2nA2Hn2Ly1a2LaS2xs2ys1n2nA2n12Hn1a1b1c2La2Lb2Lc1k2H12H2S2xs2ys1n2nA2n11a1b1c2La2Lb2Lc1k2HkS2xs2ys1n2nA2n12Hn3HnA1a1b1c2La2Lb2Lc1k2H12H2S2xs2ys1n2nA2n12Hn3HnA2Ly1a1b1c2La2Lb2LcS2xs2ys1n2nA2n12Hn1a1c2La2Lb2Lc1k2H12H2S2xs2ys1n2nA2n12Hn1a1b1c2La2Lb2Lc1k2H12H23HnA2LyS2xs2ys1n2nA2Hn2LxS2xs2ys1n2nA2n11a1b2La2Lb". (* [comment removed for export] *)
Lemma splice3_facts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_B ()) "Pxs,(8.(1.&40.))Pys,(8.(1.&40.))Pn,$9.PnA,$9.Pn1,$9.P,(:.(;.=R3.)(;.R3.R2.))P,(;.R3.R2.)P,(;.R5.(<.(=.(1.&40.)R7.)))P,(>.$9.(<.(=.(1.&40.)R7.))R5.)(:.(>.$9.(<.(=.(1.&40.)(?.R9.R8.R7.R6.R5.)))R5.)(:.Pk,$10.P,(11.R1.(3.R8.))(>.$9.(12.(?.R;.R:.R9.R8.R7.)R2.)(12.R;.R2.))(:.Pk,$10.P,(13.(3.R8.)R1.)P,(11.R2.(3.R8.))(>.$9.(12.(?.R<.R;.R:.R9.R8.)R3.)(12.R;.R3.))Pk,$10.P,(13.(3.R7.)R1.)P,(11.R2.(3.R7.))(>.$9.(12.(?.R<.R;.R:.R9.R8.)R3.)=))))")
(* [comment removed for export] *).
Proof.
  intros xs ys n nA n1 Hn HnA Lx Ly. unfold splice3.
  set (a := firstn (Z.to_nat n) xs). set (b := firstn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) ys)). set (c := repeat (Z_to_bv 64 0) (Z.to_nat (n1 - nA))).
  assert (La : length a = Z.to_nat n) by (subst a; rewrite length_firstn; lia).
  assert (Lb : length b = Z.to_nat (nA - n)) by (subst b; rewrite length_firstn, length_skipn; lia).
  assert (Lc : length c = Z.to_nat (n1 - nA)) by (subst c; rewrite repeat_length; lia).
  split; [rewrite !length_app, La, Lb, Lc; lia|]. split; [| split].
  - intros k Hk. rewrite limb32_app_l by lia. subst a. apply limb32_firstn. exact Hk.
  - intros k H1 H2. rewrite limb32_app_r by lia. rewrite limb32_app_l by lia. subst b. rewrite La, limb32_firstn by lia.
    rewrite limb32_skipn. f_equal. lia.
  - intros k H1 H2. rewrite limb32_app_r by lia. rewrite limb32_app_r by lia. subst c. apply limb32_repeat0.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L19054464270.10L7229274831.10 00000>00QS2ys1n1k2Hn2HlS1A2ys1n1k2Hn2Hk2Hl". (* [comment removed for export] *)
Lemma bytes_at_u32s_slice : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_B ()) "Psegs,(8.$14.)Pm,P,(1.&40.)(15.(1.&8.))PA,$9.Pys,(8.(1.&40.))Pn,$9.Pk,$9.P,(16.R6.R5.R4.(17.R3.))P,(;.=R3.)P,(;.=R3.)P,(;.(18.R5.R4.)(<.(=.(1.&40.)R6.)))(:.(16.R:.R9.(18.R8.(19.+4.R6.))(17.(2.(1.&40.)(3.R5.)(5.(1.&40.)(3.R6.)R7.))))(>.$10.(=.(1.&8.)(17.(2.(1.&40.)(3.R5.)(5.(1.&40.)(3.R6.)R7.))))(3.(19.+4.R5.))))")
(* [comment removed for export] *).
Proof.
  intros segs m A ys n k H Hn Hk Hl.
  rewrite <- (firstn_skipn (Z.to_nat n) ys) in H. rewrite u32s_app in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite u32s_length, length_firstn in H. replace (A + Z.of_nat (4 * Nat.min (Z.to_nat n) (length ys))) with (A + 4 * n) in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat n) ys)) in H. rewrite u32s_app in H. apply bytes_at_app in H. destruct H as [H _].
  split; [exact H|]. rewrite u32s_length, length_firstn, length_skipn. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition seg2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (X p1 n1 n nA Aa Ba : Z) (padX : word) (sX : Z) (xs ys : list word) (s3j : word) : machine_state -> Prop :=
  fun ms' => exists (raj t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 p1) (Z_to_bv 64 Aa) (Z_to_bv 64 Ba)
               a3 a4 a5 a6 a7 (Z_to_bv 64 nA) s3j (Z_to_bv 64 (4 * n)) (Z_to_bv 64 Ba) (Z_to_bv 64 Aa) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x20974) fc None m' (seg_rom usegs)
    /\ munch [(p1 + 4 * n, p1 + 4 * n1)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' X [C8 (Z_to_bv 64 p1); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 n1); C4 padX]
    /\ rw_cells usegs m' (bv_unsigned sp - 64) (sub_frame ra s0 s1 s2 s3 s4 s5 s6)
    /\ (1 <= n1 -> u32arr usegs m' p1 (splice3 xs ys n nA n1)).

Lemma sab_lor_land3_0 : forall a b, a mod 4 = 0 -> b mod 4 = 0 -> Z.land (Z.lor a b) 3 = 0.
Proof.
  intros a b Ha Hb. rewrite Z.land_lor_distr_l. change 3 with (Z.ones 2).
  rewrite !Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Ha, Hb. reflexivity.
Qed.

Section Seg2Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (X p1 n1 n sX lo : Z) (padX : word) (xs : list word).
  Variables (Aa pA nA : Z) (sAw padA : word) (ys : list word) (Ba : Z).
  Hypothesis CX : rw_cells usegs m X [C8 (Z_to_bv 64 p1); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 n1); C4 padX].
  Hypothesis CA : rw_cells usegs m Aa [C8 (Z_to_bv 64 pA); C2 sAw; C2 (Z_to_bv 64 nA); C4 padA].
  Hypothesis FR : rw_cells usegs m (bv_unsigned sp - 64) (sub_frame ra s0 s1 s2 s3 s4 s5 s6).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis XB : 0 < X /\ X + 16 <= 2^64 /\ X mod 8 = 0.
  Hypothesis AB : 0 < Aa /\ Aa + 16 <= 2^64.
  Hypothesis Hn : 0 <= n <= nA /\ nA <= n1 /\ n1 <= 10000.
  Hypothesis LEN : Z.of_nat (length xs) = n1.
  Hypothesis LENA : Z.of_nat (length ys) = nA.
  Hypothesis SLO : lo <= bv_unsigned sp - 160.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis XV : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_B ()) "P,(;.+1.Vn1,)(:.(2?.$21.Vm,Vp1,Vxs,)(:.(30.=Vp1,)(:.(>.$9.(31.Vp1,+10.)=)(:.(;.(18.Vp1,(19.+4.Vn1,))Vlo,)(:.(32.(;.(18.VX,+10.)Vp1,)(;.(18.Vp1,(19.+4.Vn1,))VX,))(32.(;.(18.VAa,+10.)Vp1,)(;.(18.Vp1,(19.+4.Vn1,))VAa,)))))))")
(* [comment removed for export] *).
  Hypothesis AV : n < nA -> bytes_at usegs m pA (u32s ys) /\ (pA + 4 * nA <= p1 \/ p1 + 4 * n1 <= pA) /\ 0 < pA /\ pA mod 4 = 0.

  Let SPOST (s6j : word) := seg2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m X p1 n1 n nA Aa Ba padX sX xs ys s6j.

  Local Ltac no_vars z := match z with | context [?v] => is_var v; fail 1 | _ => idtac end.
  Local Ltac chk_lia K :=
    exfalso;
    repeat match type of K with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in K by lia end;
    revert K;
    repeat match goal with
      | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
      | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
      end;
    cbn [Z.b2z]; intros K;
    repeat match type of K with context [bv_unsigned (Z_to_bv 64 ?z)] =>
      no_vars z; let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in change (bv_unsigned (Z_to_bv 64 z)) with v in K end;
    repeat match type of K with context [Z.lxor ?x ?y] =>
      no_vars x; no_vars y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v in K end;
    lia.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00j0@L11803442431.97 L11803484826.8  L11803680532.11 L1280003711.6   L15151859676.3  L16722370502.18 L16722652097.12 L18259764001.0  L18470896439.5  L18749673298.9  L18966192929.0  L18992914663.4  L23037199269.8  L23100341967.100L23100341967.111L23560022193.7  L23566313790.7  L23839954081.6  L2424960062.4   L27934816625.5  L28082071494.18 L32980675168.4  L35690414181.12 L35909624880.18 L35909865527.12 L38859492177.5  L39172636981.0  L40616120490.8  L41040106238.5  L49001269754.84 L50229894473.4  L50533262130.5  L53511296320.4  L53987884925.2  L54086258172.5  L5546446441.2   L57064009931.97 L57067916445.89 L57120518496.9  L58925150462.5  L58925150589.5  L59227895449.6  L59227895449.7  L59380032137.5  L59435147825.85 L61814434366.68 L61814434749.89 L61818378219.97 L61818491010.84 L61929812114.68 L61933865518.84 L62755351461.7  L64723145009.2  L64817412619.6  L65521953830.6  L66509834987.8  L811966425.8    L9782245380.8   00001401@01]02002:02m03X03Y03c04<04=04I04_05<05W05k06<06J06V06h07N07Z08?08Y08k09:09;09P09c0;30;@0;I0;U0;[0;g0;n0<e0=U0=k0>:0>I0>Z0>k0?:0?X0@U0AV0Bb0D70Do0F>0FU0F\0G10GF0G\0H30HJS2sp1X2p12n11n2lo2xs2Aa2nA2ys2XB2AB2Hn4LENA3SLO3SPB4ABND3xsC3P103P1CS2p11n2xs2nAS2sp2p12n12lo2nA3SLO3P1C1n2HnS2n11n2xs2nA2Hn3LENS2n12nA2E1S2sp2p12n11n2lo2Aa2nA2ys2Hn3SLO3SPB4ABND2K03P103P1CS2sp2p12n11n2lo2nA2Hn3SLO3SPB2K13P103P1C2K0SS2n12nA2K1S1n2xs2nA2ys2K03LLO5LMID'SS2n11n2nA2HnS2p12n11n2pA2nA2Hn3ADJS1X2p11n2xs2Aa2nA2ys4ABND3xsCS1X2p12xs2Aa2nA2ys4ABND3xsCS2n12nA3xsC4LENc3LHIS1n2xs2nA2K04LMIDS1n2nA2ys4LENAS2n11n2nA2HnS2p11n2nA2ys5LMID'S2n11n2Aa2pA2nA2ys2Hn4LENA4ABND2K03AYBS2n11n2nA2HnS2n11n2xs2nA2ys3LEN3LLO3LMH3LHI5LMID'S2n11n2Aa2nA2ys2Hn4ABND2K0S2n11n2nA2Hn2K12K0S2n11n2nA2Hn2K0SS1X2p12n11n2nA2Hn3XS1S2n12nA3xsC4LENc2E1S2sp1X2p12n11n2lo2xs2Aa2nA2ys2XB2AB2Hn3LEN3SLO3SPB4ABND3P103P1C3LLO3LMH3LHI4SRCLS2p11n2xs3LLOS1n2nA2K0S2n11n2nA2HnS1n2nAS2n11n2nA2HnS2p12nAS1X2p12n11n2xs2Aa2nA2ys2XB2Hn4LENA4ABND3xsC4LENc2K13P10S1X2p12n11n2xs2Aa2nA2ys2XB2Hn4LENA4ABND3xsC4LENcS1n2xs2nA2ys3LLO5LMID'S2n11n2nA2Hn2K1S2n11n2nA2Hn2K0S2p12n11n2nA2Hn1xS2p12n11n2nA2Hn1xS2n11n2nA2Hn2K1S1X2p11n2xs2Aa2nA2ys4ABND4SRCLS2sp1m1X2p12n11n2lo2xs2Aa2nA2ys2XB2AB2Hn4LENA3SLO2XV3SPB4ABNDS2sp1m1X2p12n11n2lo2xs2Aa2nA2ys2XB2AB2Hn4LENA3SLO2XV3SPB4ABND3xsCS2sp1m1X2p12n11n2lo2xs2Aa2nA2ys2XB2AB2Hn4LENA3SLO2XV3SPB4ABND3xsC2K13P103P1CS2sp1X2p12n11n2lo2xs2Aa2nA2ys2XB2AB3LEN4LENA3SLO3SPB4ABND2K03P103P1C3LLO3LMH3LHI4SRCLS2sp1m1X2p12n11n2lo2xs2Aa2nA2ys2XB2AB2Hn3SLO2XV3SPB4ABNDS2sp1X2p12n11n2lo2xs2Aa2nA2ys2XB2AB2Hn3LEN3SLO3SPB4ABND2K03P103P1C3LMH3LHI4SRCLS2n11n2nA2ys2Hn4LENA2K0S2p12nAS2n11n2nA2Hn3xsC4LENcS2n11n2nA2Hn3xsC4LENcS2p12n11n2Aa2nA2Hn3AS1S2p12n12nA3xsC3LLO1n2xsS2n11n2xs2nA2Hn3LEN3LMH". (* [comment removed for export] *)
  #[using="lo pA sAw padA CX CA FR MI XB AB Hn LEN LENA SLO XV AV"] Lemma seg2_walk :
    forall (raj t0 t1 t2 a0 a3 a4 a5 a6 a7 s3j t3 t4 t5 t6 : word),
    evt usegs (SPOST s3j) (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 n) a0 (Z_to_bv 64 Aa) (Z_to_bv 64 Ba)
      a3 a4 a5 a6 a7 (Z_to_bv 64 nA) s3j (Z_to_bv 64 (4 * n)) (Z_to_bv 64 Ba) (Z_to_bv 64 Aa) s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x208c4) fc None m (seg_rom usegs)).
  Proof.
    intros. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (rw_cells_bound _ _ _ _ CA) as ABND. cbn [cells_size csize Nat.add] in ABND.
    pose proof (munch_refl [(p1 + 4 * n, p1 + 4 * n1)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold sub_frame in FR.
    assert (CLR : forall mC (xsC : list word) (raj' q0 q1 q2 b0 b3 b4 b5 b6 b7 q3 q4 q5 q6 : word),
      rw_cells usegs mC X [C8 (Z_to_bv 64 p1); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 n1); C4 padX] ->
      rw_cells usegs mC Aa [C8 (Z_to_bv 64 pA); C2 sAw; C2 (Z_to_bv 64 nA); C4 padA] ->
      rw_cells usegs mC (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      mem_inv usegs mC -> (1 <= n1 -> u32arr usegs mC p1 xsC) -> Z.of_nat (length xsC) = n1 ->
      firstn (Z.to_nat nA) xsC = firstn (Z.to_nat n) xs ++ firstn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) ys) ->
      munch [(p1 + 4 * n, p1 + 4 * n1)] m mC -> wmono usegs m mC ->
      evt usegs (SPOST s3j)
        (MS (mkR raj' (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp q0 q1 q2 (Z_to_bv 64 X) (Z_to_bv 64 n) b0 (Z_to_bv 64 Aa) (Z_to_bv 64 Ba)
                b3 b4 b5 b6 b7 (Z_to_bv 64 nA) s3j (Z_to_bv 64 (4 * n)) (Z_to_bv 64 Ba) (Z_to_bv 64 Aa) s7 s8 s9 s10 s11 q3 q4 q5 q6)
            F (Z_to_bv 64 0x20928) fc None mC (seg_rom usegs))).
    { intros mC xsC raj' q0 q1 q2 b0 b3 b4 b5 b6 b7 q3 q4 q5 q6 CXc CAc FRc MIc XAc LENc PFX MUc WMc.
      clear MU WM. rename MUc into MU. rename WMc into WM.
      zstep. rewrite zx16_small by (clear - Hn; lia). zstep. rewrite zx16_small by (clear - Hn; lia). zstep.
      zstep. if_cases K1; zify_cond K1.
      - assert (n1 = nA) as E1 by (clear - K1 Hn; lia).
        apply evt_done. unfold SPOST, seg2_post. deexists 13. exists mC.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact CXc|]. split; [exact FRc|].
        intros H1. unfold splice3. replace (Z.to_nat (n1 - nA)) with 0%nat by (clear - E1; lia). cbn [repeat]. rewrite app_nil_r, <- PFX.
        replace (Z.to_nat nA) with (length xsC) by (clear - LENc E1; lia). rewrite firstn_all. exact (XAc H1).
      - specialize (XAc ltac:(clear - K1 Hn; lia)). ddestruct (XV ltac:(clear - K1 Hn; lia)) as (_ & P10 & PAL1 & P1C & XS1 & AS1).
        destruct (u32arr_split_at _ _ _ _ nA XAc ltac:(clear - Hn; lia) ltac:(clear - Hn LENc; lia)) as (XLO & XHI & LLO & LHI).
        pose proof (u32arr_cells _ _ _ _ XHI) as XHIc.
        zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
        zstep; if_cases KW; zify_cond KW; [chk_lia KW|].
        zstep. zstep. zstep. zstep; if_cases KN; zify_cond KN; [chk_lia KN|].
        zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep.
        try replace (nA * 4 + p1) with (p1 + nA * 4) in * by (clear; lia).
        pose proof U_memset_spec as SPm. unfold memset_stmt in SPm.
        eapply evt_cut; [eapply SPm with (junk := u32s (skipn (Z.to_nat nA) xsC)); clear SPm | clear SPm].
        { rewrite !unsigned_lit by (clear - Hn K1 P10 P1C SLO SPB; lia).
          replace (Z.to_nat ((n1 - nA) * 4)) with (4 * length (skipn (Z.to_nat nA) xsC))%nat by (clear - LHI LENc Hn; lia).
          replace (p1 + nA * 4) with (p1 + 4 * nA) by (clear; lia). exact XHIc. }
        { exact MIc. }
        unfold memset_post. cbv beta. intros ms' PO.
        ddestruct PO as (z0 & z1 & z2 & za1 & za2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & m2 & E & MUd & WMd & MI2 & ZCH). subst ms'.
        rewrite !unsigned_lit in MUd, ZCH by (clear - Hn K1 P10 P1C SLO SPB; lia).
        replace (ret_pc (Z_to_bv 64 0x20968)) with (Z_to_bv 64 0x20968) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
        assert (CX2 : rw_cells usegs m2 X [C8 (Z_to_bv 64 p1); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 n1); C4 padX]).
        { eapply rw_cells_transport; [exact CXc| exact MUd| exact WMd|]. cbn. clear - XS1 Hn K1. lia. }
        assert (FR2 : rw_cells usegs m2 (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply rw_cells_transport; [exact FRc| exact MUd| exact WMd|]. cbn. clear - P1C Hn K1 SLO SPB. lia. }
        assert (XLO2 : u32arr usegs m2 p1 (firstn (Z.to_nat nA) xsC)).
        { eapply u32arr_transport; [exact XLO| exact MUd| exact WMd|]. cbn. clear - LLO Hn K1. lia. }
        assert (XHI2 : u32arr usegs m2 (p1 + 4 * nA) (repeat (Z_to_bv 64 0) (Z.to_nat (n1 - nA)))).
        { eapply u32arr_of_cells; [replace (p1 + 4 * nA) with (p1 + nA * 4) by (clear; lia); exact ZCH|].
          rewrite u32s_repeat0. change (0 mod 256) with 0. f_equal. clear - Hn K1. lia. }
        assert (MU2 : munch [(p1 + 4 * n, p1 + 4 * n1)] m m2).
        { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUd]. intros x. cbn. clear - Hn. lia. }
        assert (WM2 : wmono usegs m m2) by (eapply wmono_trans; [exact WM| exact WMd]).
        clear MU WM XLO XHI XHIc MUd WMd ZCH CXc FRc XAc MIc. rename MU2 into MU. rename WM2 into WM.
        zstep. zstep. zstep.
        apply evt_done. unfold SPOST, seg2_post. deexists 13. exists m2.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact CX2|]. split; [exact FR2|].
        intros _. unfold splice3. rewrite app_assoc, <- PFX. apply u32arr_app. split; [exact XLO2|].
        rewrite length_firstn. replace (4 * Z.of_nat (Nat.min (Z.to_nat nA) (length xsC))) with (4 * nA) by (clear - Hn LENc; lia). exact XHI2. }
    zstep. if_cases K0; zify_cond K0.
    { eapply (CLR m xs); try eassumption; [intros H1; exact (proj1 (XV H1))| ].
      replace (Z.to_nat (nA - n)) with 0%nat by (clear - K0 Hn; lia). cbn [firstn]. rewrite app_nil_r. f_equal. clear - K0 Hn; lia. }
    ddestruct (XV ltac:(clear - K0 Hn; lia)) as (XA & P10 & PAL1 & P1C & XS1 & AS1). destruct (AV K0) as (AY & ADJ & PA0 & PAAL).
    pose proof (u32ro_bound _ _ _ _ AY) as AYB.
    destruct (u32arr_split_at _ _ _ _ n XA ltac:(clear - Hn; lia) ltac:(clear - Hn LEN; lia)) as (XLO & XMH & LLO & LMH).
    destruct (u32arr_split_at _ _ _ _ (nA - n) XMH ltac:(clear - Hn K0; lia) ltac:(clear - Hn K0 LMH LEN; lia)) as (XMID & XHI & LMID & LHI).
    pose proof (u32arr_cells _ _ _ _ XMID) as XMIDc.
    destruct (bytes_at_u32s_slice _ _ _ _ n (nA - n) AY ltac:(clear - Hn; lia) ltac:(clear - Hn K0; lia) ltac:(clear - Hn LENA; lia)) as [SRC SRCL].
    zstep. zstep. zstep; if_cases KW1; zify_cond KW1; [chk_lia KW1|].
    zstep. zstep. zstep. zstep; if_cases KN1; zify_cond KN1; [chk_lia KN1|].
    zstep. zstep. zstep; if_cases KW2; zify_cond KW2; [chk_lia KW2|].
    zstep. zstep. zstep. zstep; if_cases KN2; zify_cond KN2; [chk_lia KN2|].
    zstep. zstep. zstep.
    assert (LORA : Z.land (Z.lor (p1 + 4 * n) (pA + 4 * n)) 3 = 0)
      by (apply sab_lor_land3_0; clear - PAL1 PAAL; Z.div_mod_to_equations; Stdlib.micromega.Lia.lia).
    zstep. rewrite LORA. zstep. if_false. clear LORA.
    zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
    pose proof U_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    eapply evt_cut; [eapply SPc with (src := u32s (firstn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) ys))) (junk := u32s (firstn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) xs))); clear SPc | clear SPc].
    all: rewrite ?unsigned_lit by (clear - Hn K0 P10 P1C SLO SPB ABND AYB LENA; lia).
    { exact SRC. } { rewrite SRCL. f_equal. clear; lia. }
    { replace (Z.to_nat ((nA - n) * 4)) with (4 * length (firstn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) xs)))%nat by (clear - LMID Hn K0; lia). exact XMIDc. }
    { clear - ADJ Hn K0. lia. } { exact MI. }
    unfold memcpy_post. cbv beta. intros ms' PO.
    ddestruct PO as (z0 & z1 & z2 & za1 & za2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & m2 & E & MUd & WMd & MI2 & ZCH & _). subst ms'.
    rewrite !unsigned_lit in MUd, ZCH by (clear - Hn K0 P10 P1C SLO SPB; lia).
    replace (ret_pc (Z_to_bv 64 0x20920)) with (Z_to_bv 64 0x20920) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (CX2 : rw_cells usegs m2 X [C8 (Z_to_bv 64 p1); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 n1); C4 padX]).
    { eapply rw_cells_transport; [exact CX| exact MUd| exact WMd|]. cbn. clear - XS1 Hn K0. lia. }
    assert (CA2 : rw_cells usegs m2 Aa [C8 (Z_to_bv 64 pA); C2 sAw; C2 (Z_to_bv 64 nA); C4 padA]).
    { eapply rw_cells_transport; [exact CA| exact MUd| exact WMd|]. cbn. clear - AS1 Hn K0. lia. }
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR| exact MUd| exact WMd|]. cbn. clear - P1C Hn K0 SLO SPB. lia. }
    assert (XLO2 : u32arr usegs m2 p1 (firstn (Z.to_nat n) xs)).
    { eapply u32arr_transport; [exact XLO| exact MUd| exact WMd|]. cbn. clear - LLO Hn K0. lia. }
    assert (XHI2 : u32arr usegs m2 (p1 + 4 * n + 4 * (nA - n)) (skipn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) xs))).
    { eapply u32arr_transport; [exact XHI| exact MUd| exact WMd|]. cbn. clear - LHI Hn K0. lia. }
    assert (XMID2 : u32arr usegs m2 (p1 + 4 * n) (firstn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) ys))).
    { eapply u32arr_of_cells; [exact ZCH| reflexivity]. }
    set (xsC := firstn (Z.to_nat n) xs ++ firstn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) ys) ++ skipn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) xs)).
    assert (LMID' : Z.of_nat (length (firstn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) ys))) = nA - n) by (rewrite length_firstn, length_skipn; clear - Hn K0 LENA; lia).
    assert (XAC : u32arr usegs m2 p1 xsC).
    { subst xsC. apply u32arr_app. split; [exact XLO2|]. replace (p1 + 4 * Z.of_nat (length (firstn (Z.to_nat n) xs))) with (p1 + 4 * n) by (clear - LLO; lia).
      apply u32arr_app. split; [exact XMID2|]. replace (p1 + 4 * n + 4 * Z.of_nat (length (firstn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) ys)))) with (p1 + 4 * n + 4 * (nA - n)) by (clear - LMID'; lia). exact XHI2. }
    assert (LENC : Z.of_nat (length xsC) = n1) by (subst xsC; rewrite !length_app; clear - LLO LMID' LHI LMH LEN Hn K0; lia).
    assert (PFX : firstn (Z.to_nat nA) xsC = firstn (Z.to_nat n) xs ++ firstn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) ys)).
    { subst xsC. rewrite app_assoc, firstn_app, firstn_all2 by (rewrite length_app; clear - LLO LMID' Hn K0; lia).
      rewrite length_app. replace (Z.to_nat nA - (length (firstn (Z.to_nat n) xs) + length (firstn (Z.to_nat (nA - n)) (skipn (Z.to_nat n) ys))))%nat with 0%nat by (clear - LLO LMID' Hn K0; lia).
      cbn [firstn]. rewrite app_nil_r. reflexivity. }
    assert (MU2 : munch [(p1 + 4 * n, p1 + 4 * n1)] m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUd]. intros x. cbn. clear - Hn K0. lia. }
    assert (WM2 : wmono usegs m m2) by (eapply wmono_trans; [exact WM| exact WMd]).
    clearbody xsC. clear XLO XMH XMID XHI XMIDc SRC SRCL ZCH XLO2 XHI2 XMID2 MUd WMd CX FR MU WM XA. rename MU2 into MU. rename WM2 into WM.
    zstep. zstep.
    eapply (CLR m2 xsC); try eassumption. intros _; exact XAC.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Seg2Walk.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mpd_at_munch_any : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_B ()) "Psegs,(8.$14.)Pm,P,(1.&40.)(15.(1.&8.))Pm',P,(1.&40.)(15.(1.&8.))PLB,(8.$34.)Pd,$35.PW,(8.$36.)P,(37.R6.R5.R3.R2.)P,(22.R2.R6.R5.)P,(27.R8.R7.R6.)P,(38.R4.(39.R5.)+10.)P,P,(3:.(>.$3;.(3<.R6.)$3=.))(38.R6.(3>.R7.)(19.+4.(3?.R7.)))(37.R;.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' LB d W [HA HS] MU WM HD1 HD2. split; [| exact HS].
  ddestruct HA as (HR & HAL & HPOS & HL & HN & HO).
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply rw_cells_transport; [exact HR| exact MU| exact WM| exact HD1].
  - destruct (md_own d); [exact HO| |].
    + ddestruct HO as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      eapply u32arr_transport; [exact H4| exact MU| exact WM|]. rewrite HL. apply HD2. discriminate.
    + ddestruct HO as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| exact H5].
      eapply u32ro_transport; [exact H4| exact MU|]. rewrite HL. apply HD2. discriminate.
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L35140152015.26L56470958949.2800000;00NS1d4HPOS2HLS1d4HPOS2HL2H31i2Hi". (* [comment removed for export] *)
Lemma mpd_at_heap_pres0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_B ()) "Psegs,(8.$14.)PL,$40.Pm,P,(1.&40.)(15.(1.&8.))Pm',P,(1.&40.)(15.(1.&8.))PLB,(8.$34.)PLB',(8.$34.)PSP,$9.Pd,$35.P,(37.R8.R6.R4.R1.)P,(41.R9.R8.R5.R3.R7.R6.)P,(28.R:.R8.)P,(28.R;.R8.)P,(42.R;.R8.R6.(39.R5.)+10.)P,P,(>.$3;.(3<.R6.)$43.)(42.R=.R:.R8.(3>.R7.)(19.+4.(3?.R7.)))P,Pb,$34.P,(44.$34.R1.(45.R8.))(44.$34.R2.R;.)(37.R?.R<.R:.R8.)")
(* [comment removed for export] *).
Proof.
  intros segs L m m' LB LB' SP d [HA HS] HP MI MI' CR CRL HBL. split; [| exact HS].
  ddestruct HA as (HR & HAL & HPOS & HL & HN & HO).
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply heap_pres_rw_cells; [exact HP| exact HR| exact CR].
  - destruct (md_own d) eqn:EO; [exact HO| |].
    + ddestruct HO as (H1 & H2 & H3 & [H4 H5]). split; [exact H1|]. split; [apply HBL; unfold mpd_blk; rewrite EO; left; reflexivity|]. split; [exact H3|].
      split; [eapply heap_pres_bytes_at; [exact HP| exact H4| rewrite u32s_length; replace (Z.of_nat (4 * length (md_limbs d))) with (4 * md_n d) by lia; exact (CRL eq_refl)]|].
      eapply heap_pres_wr_at; [exact HP| exact H5| rewrite HL; exact (CRL eq_refl)].
    + ddestruct HO as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| exact H5].
      eapply static_limbs_any_mem; [exact MI| exact MI'| exact H4|]. rewrite u32s_length. intros i Hi. apply H5. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)

Section J1.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (dX dA dB : mpd) (lo : Z) (MSF : Z).
  Hypothesis HH : HEAP usegs L HI h LB m mo.
  Hypothesis MX : mpd_at usegs m LB dX.
  Hypothesis MA : opnd_at usegs m LB (bv_unsigned sp) dA.
  Hypothesis MB : opnd_at usegs m LB (bv_unsigned sp) dB.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis SXB : mpd_sep dX dB.
  Hypothesis SAB : mpd_sep dA dB.
  Hypothesis NST : md_own dX <> LStatic.
  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
  Hypothesis CRA : client_range L LB lo (md_addr dA) 16.
  Hypothesis CRAL : md_own dA = LHeap -> client_range L LB lo (md_p dA) (4 * md_n dA).
  Hypothesis CRB : client_range L LB lo (md_addr dB) 16.
  Hypothesis CRBL : md_own dB = LHeap -> client_range L LB lo (md_p dB) (4 * md_n dB).
  Hypothesis XW : mpd_writable L LB (bv_unsigned sp) (heap_top usegs L HI h) dX.
  Hypothesis XLS : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX.
  Hypothesis SLO : lo <= bv_unsigned sp - 160 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis CA : const_at L MSF 8.
  Hypothesis MSFE : MSF = U_MEMSET_FUNC.

  Let POST := mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX (sub_abs_R LB dX dA dB) lo m mo.
  Let FRAME := sub_frame ra s0 s1 s2 s3 s4 s5 s6.

  Hypothesis KC : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_B ()) "Pn,$9.(46.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VdX,VdA,VdB,Vlo,R1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition sub_J1_stmt (n : Z) : Prop :=
    forall (m1 : mem) (raj t0 t1 t2 a0 a3 a4 a5 a6 a7 s3j s5j s6j t3 t4 t5 t6 : word),
    SIGF (md_limbs dB) (md_n dB) n -> n <= md_n dA ->
    mem_inv usegs m1 -> stk usegs m1 lo (bv_unsigned sp - 64) -> rw_cells usegs m1 (bv_unsigned sp - 64) FRAME ->
    HEAP usegs L HI h LB m1 mo -> statics_ok usegs L m1 ->
    mpd_at usegs m1 LB dX -> opnd_at usegs m1 LB (bv_unsigned sp) dA -> opnd_at usegs m1 LB (bv_unsigned sp) dB ->
    heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m1 ->
    aevtM usegs mo POST (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 n) a0
      (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dB)) a3 a4 a5 a6 a7 (Z_to_bv 64 (md_n dA)) s3j (Z_to_bv 64 (4 * n)) s5j s6j
      s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20830) fc None m1 (seg_rom usegs))
(* [comment removed for export] *).

  Local Ltac no_vars z := match z with | context [?v] => is_var v; fail 1 | _ => idtac end.
  Local Ltac chk_lia K :=
    exfalso;
    repeat match type of K with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in K by lia end;
    revert K;
    repeat match goal with
      | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
      | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
      end;
    cbn [Z.b2z]; intros K;
    repeat match type of K with context [bv_unsigned (Z_to_bv 64 ?z)] =>
      no_vars z; let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in change (bv_unsigned (Z_to_bv 64 z)) with v in K end;
    repeat match type of K with context [Z.lxor ?x ?y] =>
      no_vars x; no_vars y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v in K end;
    lia.
  Local Ltac landk_chk k H :=
    lazymatch goal with |- context [Z.land ?p k] =>
      let E := fresh "E" in
      assert (E : Z.land p k = 0)
        by (first [change k with (Z.ones 3) | change k with (Z.ones 2)]; rewrite Z.land_ones by lia;
            first [change (2 ^ 3) with 8 | change (2 ^ 2) with 4]; clear - H; Z.div_mod_to_equations; lia);
      rewrite E; clear E end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "02n0@L10264981820.6  L10875810347.4  L11041888906.7  L12752657784.7  L12755629547.9  L12996331683.7  L13667842338.6  L13668090517.6  L13938249145.6  L13969895251.5  L15024340921.2  L15026212793.2  L1519646453.8   L15638030791.7  L15821996009.4  L1595052933.4   L1597150190.11  L159770940.2    L18995052170.13 L19134330989.1  L19615223586.15 L19615223715.15 L20662456646.1  L21359803778.6  L21682153356.4  L2214067944.13  L23100341967.152L23100341967.193L23100341967.221L23100341967.235L23435672735.3  L23466092803.1  L23919484151.4  L24131374784.5  L2454817466.7   L2454883510.12  L24912882372.1  L26443301720.7  L26466616993.0  L27229550539.11 L27466736915.5  L27855044840.3  L28082072438.6  L2912763434.13  L31485105776.3  L32303174625.6  L32303442006.6  L32952606703.7  L32982742029.2  L33004136903.7  L33786752539.4  L33920126134.12 L33920322234.7  L3446086797.6   L34566920600.6  L35193494542.4  L35925021705.243L35925021705.244L36241950397.9  L36244077318.12 L37041033664.6  L37574767333.1  L3796477212.4   L38027450911.9  L38027467422.13 L38033760680.9  L38033934975.9  L38045094488.187L38221604602.4  L38545653143.6  L38858302196.244L38858302196.245L38948636245.0  L39122916916.9  L39172636981.0  L39201402395.4  L39409930731.3  L39542883542.2  L39810665913.6  L40231054960.186L40823280861.13 L41266447170.7  L41302442785.0  L42500461139.4  L43359788350.3  L43744978743.7  L4399511325.6   L44397119898.2  L44483022151.8  L44483105499.10 L44611170703.6  L44611170703.7  L44611266813.7  L44611266813.8  L44993469759.3  L46754384436.7  L46756382136.192L47955359031.220L47957477687.160L47957477937.151L47959455079.201L47963023916.2  L47965379116.2  L48105379999.7  L4909589198.7   L4909622720.3   L4941632620.4   L49578233423.235L51167346105.235L51167346492.152L51451970418.2  L51850007537.3  L51852340524.4  L52101694457.10 L52101695852.8  L52101785646.10 L52101933485.10 L52102091798.10 L52108071704.14 L52108186521.10 L52212382159.4  L52437843788.6  L52476066706.193L52478325012.7  L5259986997.235 L5259987632.152 L52663381392.3  L5287801372.9   L52987799593.9  L53066822865.3  L53066822865.6  L53066822865.7  L53072825569.10 L53134281077.4  L54324727969.0  L54398102733.9  L56254917914.4  L56321849304.8  L56357691564.3  L5704949328.11  L5705098598.12  L5711078758.5   L57608476237.9  L58307024458.1  L58980375728.8  L58991812240.12 L58993894187.9  L59124574031.6  L59308518135.7  L59308546384.4  L59308579281.7  L59308586510.4  L59308628179.3  L59308628566.5  L59308628820.4  L59308661201.9  L59308873939.11 L59308873939.7  L59310826101.12 L59310826101.8  L59314873579.11 L59314873579.6  L59314873579.9  L59314938599.4  L59321149435.6  L61245306294.7  L61814433979.160L61814434366.151L61814434749.151L61929812241.151L61932029127.234L62915414477.4  L63171214473.5  L635310052.2    L63684545666.2  L64506844115.6  L64822964236.2  L65502311324.157L65575152201.5  L67482084893.4  L67705272931.6  L67966210416.1  L68344074685.3  L772373455.157  L788407815.9    L8695580055.5   L8701969412.13  L8704533520.243 L8704533520.244 L919211136.6    00000E00Q00i01A01^02302K02d03803I03Q03X04104I04Y04c05H05P05X05\06R07H07L07c08008=08Y09809Z0:=0:G0:K0:Y0:l0;A0;U0;X0;m0;n0<S0<e0<o0=F0=N0=[0>40>L0>`0>h0?@0?L0?`0@50@J0@a0@o0B^0DJ0Db0E:0EN0ER0E]0F40F]0G:0GW0HM0HZ0Hl0K<0ML0MM0Md0Me0N10N90NA0NU0O10O20OG0OH0OS0O]0P20PE0PM0P`0Q90QK0Q`0R60RQ0R[0S40TG0U00US0V60V_0Vg0Vn0WG0W]0Wh0X30XV0Y<0Y[0Ya0Yk0Z50ZU0Zl0[L0[a0\@0\e0]?0]M0]`0]a0^90^_0_>0_K0_l0`J0`R0`a0a=0a`0an0ao0bI0bY0c40c>0cY0dA0dP0dm0e10eN0ef0f;0fN0fj0g90gL0gY0gd0h20h?0hW0ho0iH0iS0il0jR0je0k<0kG0kZ0ko0lR0m50mX0nN0o]0oa10310;10A10U10]11911J11T11f11j12612l13H13X13h14j15i16<S2nA2nB1n3NLE3NRA3SB1S2nX2pX2Aa1HS2nX2pX2nA3NX12K12An3APXS2nX2pX2nA3NX12K12An3APXS2nX2pX3xs02nA4LENX2K12An3APXS2nX2pX2nB1n3SB11a2NOS1L2nB2pB4ACV'2R02R33ACVS2nB2pB2zs3LB03BP02BB3LB'S2nX2Aa2nA2K12An3ASnS1L3HLS2sp2lo3SLOS2pA3AP0S2pA2R0S1L3HLS2sp2lo3SLO3ACL3ACPS2Aa2nA2nB1n3SB12An4ASn'S2nX3xs04LENX2AnS2nX2nA2AnS1L3HLS2sp2lo2nX2nA3SLO3ACL2K12An3AnCS2nA3A1'S2nA3NRAS2spS1X2sX2nX2pX3xs04padX4ownX2Aa2sA2nA2pA2ys4padA4ownA2K2S1X2sX2nX2pX3xs04padX4ownX2Aa2sA2nA2pA2ys4padA4ownA2K1S2spS2nX3xs02nA4LENX3NX12K1S1X3XAL2X02XBS1L2sp2lo3SLOS2sp1X3xs02Aa2ys2Ba2zs2XB2ABS2sp1X3xs02Aa2ys2Ba2zs2XB2AB2AnS2sp1X2pX3xs02Aa2ys2Ba2zs2XB2AB2AnS2sp1X3xs02Aa2ys2Ba2zs2XB2AB2An3xsbS2Aa2A02ABS2nAS2nX2nA3NRX2K1S2nA1n3NLE3xsb4LENbS2nX2pX2Ba2nB1n3SB11DS2nX2pX2Ba1n2B02Z01HS1nS2nA2nB2pB1n3SB12An1DSS1L3HLS2sp2lo2nA3SLO3ACL2An3AnC1p3HSPS2nX3xs04LENX1k2HkS2nX2nA2K1S2nA2pA2ys4LENA3A1'3AB2S2nA3NRAS2nX3xs04LENXS2nA2pA2ys3LA03AP02BB3LA'S1L2nA2pA4ACV'2R02R33ACVS2nX2pX2nA2K12An3APXS2nA3NRAS2nA2Ba2nB1n3SB12An4BSn'S2nX2pX2Aa1HS2nX2pX2Aa1n2A02Z01HS2nX2pX2Aa2nB1n3SB11DS1L3HLS2sp2lo3SLO3ACLS2nA2pA2ys4LENA3A1'3AB2S2nX2nA3NRX2K1S1L3HLS2sp2lo1X2pX3xs02Aa2nA2pA2ys2Ba2pB2zs3SLO3SPA3SPB3XAL2X02A02B03OA42XB2AB2XS2An3An03xsb3DXA2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2pX3xs02Aa2pA2ys2Ba2pB2zs3SLO3SPA3SPB3XAL2X02A02B03OA42XB2AB2XS2An3An03xsb3DXA2HB5Ha_st5Hl_stS2nX2pX2nA2pA2nB1n3SB11CS2nX2pX2nA2pA1n3PA02Z01HS2nX2Aa2nA2K12An3ASnS2nAS1p1k2Hk2HbS2nX2nA2K12An1a1q1k1R1DS1L3HLS2sp2lo2nX2nA3SLO3ACL2K12An3AnC1a1CS1L4DIMG2nX2nA2K12An3AnI1a2C1S1L4DIMG2nX2nA2K12An3AnI1a2HdS1L3HLS2sp2lo1X3xs02Aa2ys2Ba2zs3SLO3SPB2X02A02B02XB2ABS1L2sp2lo3SLOS1L2nX2pX2R02R32R4S1L3HLS2sp2lo1X2nX2pX3xs02Aa2nA2pA2ys2Ba2pB2zs3SLO3ACL3SPB3XAL2X04LENX2A04LENA2B02XB2AB2K12An3An04An163AnC3xsb4LENb3DXA4XSn'4ASn'2HB5Ha_st5Hl_stS1L3HLS2sp2lo1X2nX2pX3xs02Aa2nA2pA2ys2Ba2pB2zs3SLO3ACL3SPB3XAL2X04LENX2A04LENA2B02XB2AB2K12An3An04An163AnC3xsb4LENb3DXA4XSn'4ASn'2HB5Ha_st5Hl_stSS1L2nA2An3AnI1p1k2I02I1SS2nX2pX2Ba1HS1X1a2NOS2nX3NRXS2nX2nA2Ba2K12An3BSnS2sp1X3xs02Aa2ys2Ba2zs2XB2ABSS2nX2nB1n3SB12En1k2HkSS1X2nX2pX1HS1X2Aa3DXAS2nX2nB2pB2An1D2nA2K1S1X2nX2nA2K12An3XSnS2nX3NRXS2sp2lo2nX2pX1n3LOWS1L2sp2lo2nA3ACL1n2An3AnCS2nX2nA2K12An1a2NOS2nA2nB1n3SB12An1a2NOS2nX2nA3NX12K12An1a2HaS2nX3xs02nA4LENX2K12An1a2HaS1X2Ba3DXBS1L2nA3NRA2An3An03AnC3ACVS1L3HLS2sp2lo1X2nX3xs02Aa2nA2ys2Ba2zs3SLO3ACL3SPB2X04LENX2A02B02XB2AB2K12An3An03AnCS2sp1X2nX2pX3xs02Aa2ys2Ba2zs3NRX2XB2AB2AnS2sp1X2nX3xs02Aa2ys2Ba2zs3NRX2XB2ABS2sp1X2nX3xs02Aa2ys2Ba2zs3NRX2XB2ABS2sp1X2nX2pX3xs02Aa2ys2Ba2zs3NRX2XB2AB2AnS2pB3BP0S2pB2R0S2nX3xs02nA1n3NLE4LENX2K1S2nX2nA2nB1n3SB12K12LTS2nX3NRX2NZS1p1k2Hk2HbS2sp1X3xs02Aa2ys2Ba2zs2XB2AB2An3xsbS2sp1X3xs02Aa2ys2Ba2zs2A02XB2AB2An3xsbS2sp1X3xs02Aa2ys2Ba2zs2A02XB2ABS1k2HkS2nX2nA2K1S2nX2nA2K1S1L4DIMG2nA2nB1n3SB12An3AnI1a2HdS1X2nX2pX2nB1n3SB11a2HoS1L4DIMG2nA2nB1n3SB12An3AnI1a2C1S2nX2pX2nB1n3SB11a2Z0S1L4DIMG2nX2pX2nB1n3SB11a2Hd2PIS1L3HLS2sp2lo2nA3SLO3ACL1n2An3AnC1a1CS2nA2nB1n3SB12An1a1q1k1R1DS2nX2nA3NRX2K1S1X2nX2pX4ownX1a2HoFS1L2nX2pX3NRX3X0'2XC3ACVS2sp1X3xs02Aa2ys2Ba2zs2X02XB2AB2An3xsbS2sp1X3xs02Aa2ys2Ba2zs2X02XB2ABS2nX3xs04LENXS1L3HLS2sp2lo3SLO3ACL3SPA3ACP3SPBS1L3HLS2sp2lo2nX2pX3SLO3ACL2XCS2sp1a1CS1L2HI2sp1h1a1CS2sp2lo2Aa3OA41a2Ha1C2Ba3OB4S1L2sp2lo2nA2pA3ACL1a2Ha1C2R32nB2pBS1L2lo3ACL3ACPSS1L2HI3HLS2sp1h2lo3SLO1a1CS2nX3xs04LENX2AnS2nX2nA2nB1n3NLE3NRX3SB12K1S2nX2nA2K1S1L2nX2pX2nA2pA2ys2PI2I02I1S1L3HLS2sp2lo2nX2pX2nA2pA3SLO3ACL3ASP2PCS2nX2pX2nA2pA1CS1L2sp2lo2nX2nA3ACL2K12An3AnCS2nXS1L3HLS2sp2lo3SLO3ACL3ACP3SPBS2nX2pX2nB2pB1n3PB02Z01HS2nX2pX2nB2pB1n3SB11CS2nX3xs02nA4LENX2K1S2nA2pA2nB1n4OWNA3SB12LT3OA0S2nX2pX4OWNX2N1S2nX2nA3ENn1k2H12H2S2nX3EN01k2HkS2nA3NRA2K0S2nX2nA3ENn2K3S1X2Aa3DXA2K5S2nX2pX1a1q1k1R2O22E12E2S2nX2pX2nB1n3SB11a2NO2Z0S2LB2nX2pX3xs02m14OWNX2Z0S2An3An02KZS1L2nX2pX2KP2R02R22R33ACVS1X2pX1a3Ha'1q1k1R2E11H2nX2E22Ha2Aa2BaS2nX2nA3NRX2K12An1HS2nX2pX3NX11p2Ep1H1k2EkS1X2Aa2K21DS2LB2pX3xs02m14OWNXS2nA2pA2nB1n3SB12An1HS2sp1X3xs02Aa2nA2ys2Ba2zs3NRA2XB2ABS2sp1X3xs02Aa2nA2ys2Ba2zs3NRA2XB2ABS2sp1X3xs02Aa2nA2ys2Ba2zs3NRA2XB2ABS2sp1X3xs02Aa2ys2Ba2nB2zs1n3SPB2X02A02B03NRB3SB12XB2ABS1L2sp1X3xs02Aa2nA2ys2Ba2nB2zs1n3NLE3SPB2X02A02B03SB12XB2AB2An3An03AnC3xsb4ACV'S2nAS1L4DIMG2nA2An3AnIS2nA3NRAS1k2HkS1L2lo2nA3ACL2An3AnCS2nA3A1'S2sp1X3xs02Aa2ys2Ba2zs2XB2ABS2nA2nB1n3NLE3SB1S2nX2nA2K1S2nX2nA2pA2An1D2K1S2spS2nX3NRX3NX1S1L3HLS2sp2lo1X3xs02Aa2ys2Ba2zs3SLO3SPB2X02A02B02XB2ABS2nX2pX3xs02nA3NX12K12An3APXS1L2HI2sp1h4HTOPS1L2HI2sp1h4HTOPS2sp1X2pX3xs02Aa2nA2pA2ys2Ba2pB2zs2XB2AB2An3xsb3DXA2HB5Ha_st5Hl_stS2sp1X2pX3xs02Aa2pA2ys2Ba2pB2zs2XB2AB2An3xsb3DXA2HB5Ha_st5Hl_stS1L2lo2nX2pX3ACL2PC". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG MSF MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS SLO ACL HTOP SPA DHI TP CA MSFE KC"] Lemma sub_J1_proof : forall n, sub_J1_stmt n.
  Proof.
    intros n. unfold sub_J1_stmt. intros until t6.
    intros SB NLE MI1 ST1 FR1 HH1 SOK1 MX1 MA1 MB1 HPX1.
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR HAP]. pose proof (HND _ _ _ _ HH1) as ND.
    destruct dX as [X sX nX pX xs0 padX ownX]. destruct dA as [Aa sA nA pA ys padA ownA]. destruct dB as [Ba sB nB pB zs padB ownB].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof MX1 as [(CX1 & XAL & X0 & LENX & NRX & OWNX) SGX]. unfold mpi_cells in CX1. unfold MPI_MAX_LIMBS in NRX.
    pose proof (opnd_view _ _ _ _ _ MA1) as [(CA1 & AAL & A0 & LENA & NRA & OWNA) SGA]. unfold mpi_cells in CA1. unfold MPI_MAX_LIMBS in NRA.
    pose proof (opnd_view _ _ _ _ _ MB1) as [(_ & BAL & B0 & LENB & NRB & OWNB) SGB]. unfold MPI_MAX_LIMBS in NRB.
    dpose SB as (SB1 & SB2 & SB3).
    ddestruct XW as (XCW & XD & XP). dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof (rw_cells_bound _ _ _ _ CX1) as XB. pose proof (rw_cells_bound _ _ _ _ CA1) as AB. cbn [cells_size csize Nat.add] in XB, AB.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as XS.
    subst FRAME. unfold sub_frame in FR1.
    assert (APF : n < nA -> 0 < pA /\ pA mod 4 = 0).
    { intros LT. destruct ownA; [exfalso; clear - OWNA LT SB1; lia| |].
      - ddestruct OWNA as (_ & AIN & APAL & _). pose proof (proj1 (Forall_forall _ _) HBR _ AIN) as (R0 & R1 & R2 & R3 & R4). cbn in R0, R1, R2, R3, R4.
        split; [clear - R0 R3 R4; lia| clear - APAL; Z.div_mod_to_equations; lia].
      - ddestruct OWNA as (_ & APAL & AP0 & _). split; [exact AP0| exact APAL]. }
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0 NRA; lia| clear K0].
    zstep; if_cases KX0; zify_cond KX0; [clear - KX0 X0 XB; chk_lia KX0|].
    zstep. landk_chk 7 XAL. zstep. if_false.
    zstep. rewrite zx16_small by (clear - NRX; lia). zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        assert (EXA : mkMPD X sX nX pX xs0 padX ownX = mkMPD Aa sA nA pA ys padA ownA).
        { destruct SXA as [E|D]; [exact E|]. exfalso. cbn [md_addr] in D. clear - D K2. lia. }
        injection EXA as EXa ESg ENn EPp ELs EPd EOw.
        zstep. rewrite zx16_small by (clear - NRX NRA; lia). zstep. rewrite zx16_small by (clear - NRX NRA; lia). zstep. zstep.
        if_cases K3; zify_cond K3; [| exfalso; clear - K3 K1 ENn; lia].
        eapply (KC n (Z_to_bv 64 Ba) s3j (Z_to_bv 64 nA) m1 mo h LB xs0 pX nX ownX _ _ _ _ (Z_to_bv 64 Aa) (Z_to_bv 64 Ba)); try eassumption; try reflexivity.
        all: cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        - apply mo_frame_refl.
        - apply mpd_out_refl. cbn. exact NST.
        - intros b Hb. left. exact Hb.
        - intros _. exact MA1.
        - intros _. exact MB1.
        - clear - K1 ENn. lia.
        - intros k _ _. rewrite ELs. reflexivity.
        - intros _ k _. rewrite ELs. reflexivity.
        - intros E k _. injection E as _ _ _ _ EL' _ _. rewrite EL'. reflexivity.
        - intros k H1 H2. exfalso. clear - H1 H2 K1 ENn. lia. }
      (* [comment removed for export] *)
      assert (NEQA : mkMPD X sX nX pX xs0 padX ownX <> mkMPD Aa sA nA pA ys padA ownA) by (intros E; injection E; clear - K2; lia).
      (* [comment removed for export] *)
      assert (XF : 1 <= nX -> ownX = LHeap /\ In (pX, 4 * nX) LB /\ pX mod 16 = 0 /\ u32arr usegs m1 pX xs0
                              /\ 0 < pX /\ pX + 4 * nX <= alloc_ceiling /\ (pX + 4 * nX <= hl_img_lo L \/ hl_img_hi L <= pX)).
      { intros N1. destruct ownX; [exfalso; clear - OWNX N1; lia| | exfalso; exact (NST eq_refl)].
        ddestruct OWNX as (O1 & O2 & O3 & O4). pose proof (proj1 (Forall_forall _ _) HBR _ O2) as (R0 & R1 & R2 & R3 & R4). cbn in R0, R1, R2, R3, R4.
        split; [reflexivity|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|]. clear - R0 R3 R4. lia. }
      assert (PX0 : nX = 0 -> pX = 0).
      { intros Z0. destruct ownX; [exact (proj1 OWNX)| exfalso; clear - OWNX Z0; lia| exfalso; exact (NST eq_refl)]. }
      (* [comment removed for export] *)
      assert (AVF : n < nA -> bytes_at usegs m1 pA (u32s ys) /\ (pA + 4 * nA <= pX \/ pX + 4 * nX <= pA)).
      { intros LT. ddestruct (XF ltac:(clear - LT K1 SB1; lia)) as (EO & XIN & _ & _ & P0 & PC & PI).
        destruct ownA; [exfalso; clear - OWNA LT SB1; lia| |].
        - ddestruct OWNA as (A1' & AIN & APAL & AARR). split; [apply u32arr_ro; exact AARR|].
          destruct OA3 as [C|[C|[C|C]]]; [exfalso; exact (NEQA C)| exfalso; exact (C EO)| discriminate| clear - C; lia].
        - ddestruct OWNA as (A1' & APAL & AP0 & ABY & AW). split; [exact ABY|].
          destruct AW as [ARO|[ASP _]]; [| clear - ASP PC ACL SLO HLS; lia].
          pose proof (u32ro_bound _ _ _ _ ABY) as AB2.
          pose proof (ROIMG (pA + 0) (ARO 0 ltac:(clear - A1'; lia)) ltac:(clear - AB2 LENA A1'; lia)) as I0.
          pose proof (ROIMG (pA + (4 * nA - 1)) (ARO (4 * nA - 1) ltac:(clear - A1'; lia)) ltac:(clear - AB2 LENA A1'; lia)) as I1.
          clear - I0 I1 PI LENA A1'. lia. }
      eapply aevtM_cut_evt; [exact MK1| |].
      { eapply (seg2_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 X pX nX n sX lo padX xs0 Aa pA nA (Z_to_bv 64 sA) padA ys Ba);
          try eassumption.
        - clear - X0 XB XAL. lia.
        - clear - A0 AB. lia.
        - clear - SB1 NLE K1 NRX. lia.
        - clear - SLO HLS. lia.
        - intros N1. ddestruct (XF N1) as (EO & XIN & XPAL & XARR & P0 & PC & PI). split; [exact XARR|]. split; [exact P0|]. split; [exact XPAL|].
          split; [clear - PC ACL; lia|]. split; [exact (XP EO)| exact (OA2 EO)].
        - intros LT. destruct (AVF LT) as [AV1 AV2]. split; [exact AV1| split; [exact AV2| exact (APF LT)]]. }
      cbv beta. intros ms' SP2. unfold seg2_post in SP2.
      ddestruct SP2 as (raj' & q0 & q1 & q2 & b3 & b4 & b5 & b6 & b7 & q3 & q4 & q5 & q6 & m' & -> & MU2 & WM2 & MI2 & CX2 & FR2 & XA2).
      ddestruct (splice3_facts xs0 ys n nA nX ltac:(clear - SB1 NLE; lia) ltac:(clear - K1; lia) ltac:(clear - NLE K1 LENX; lia) LENA) as (SL & SPRE & SMID & SZERO).
      assert (LOW : pX + 4 * nX <= lo).
      { destruct (Z.eq_dec nX 0) as [->|NZ]; [destruct ownX; [destruct OWNX as [-> _]; clear - ACL ACP; lia| clear - OWNX; exfalso; lia| exfalso; exact (NST eq_refl)]|].
        ddestruct (XF ltac:(clear - NZ NRX; lia)) as (_ & _ & _ & _ & _ & PC & _). clear - PC ACL. lia. }
      eapply (KC n (Z_to_bv 64 Ba) s3j (Z_to_bv 64 nA) m' mo h LB (splice3 xs0 ys n nA nX) pX nX ownX _ _ _ _ (Z_to_bv 64 Aa) (Z_to_bv 64 Ba)); try eassumption; try reflexivity.
      all: cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      - eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]. cbn. clear - LOW SB1. lia.
      - eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH1| exact ACL| exact MU2| exact WM2|].
        intros a Ha NO. cbn in NO. destruct (Z.eq_dec nX 0) as [Z0|NZ]; [exfalso; clear - NO Z0 SB1 NLE K1; lia|].
        ddestruct (XF ltac:(clear - NZ NRX; lia)) as (_ & XIN & _). right; right. exists (pX, 4 * nX). split; [exact XIN|]. cbn. clear - NO SB1. lia.
      - apply mo_frame_refl.
      - eapply statics_ok_munch; [exact SOK1| exact MU2|]. intros a Hd NW. cbn. split; [| exact I].
        destruct (Z.eq_dec nX 0) as [Z0|NZ]; [clear - Z0 SB1 NLE K1; lia|]. ddestruct (XF ltac:(clear - NZ NRX; lia)) as (_ & _ & _ & _ & _ & _ & PI). clear - PI Hd DIMG SB1. lia.
      - (* [comment removed for export] *)
        split; [| exact SGX]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        split; [exact CX2|]. split; [exact XAL|]. split; [exact X0|]. split; [exact SL|]. split; [unfold MPI_MAX_LIMBS; exact NRX|].
        destruct ownX; [exact OWNX| | exfalso; exact (NST eq_refl)].
        ddestruct OWNX as (O1 & O2 & O3 & O4). split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. apply XA2. exact O1.
      - eapply mpd_out_same_blocks; [reflexivity| cbn; exact NST| reflexivity].
      - intros b Hb. left. exact Hb.
      - eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_munch; [exact MU2| exact WM2|].
        intros a Ha Hc Ho. cbn in Ho |- *. split; [| exact I].
        destruct (Z.eq_dec nX 0) as [Z0|NZ]; [clear - Z0 SB1 NLE K1; lia|]. destruct (XF ltac:(clear - NZ NRX; lia)) as (EO & _). rewrite EO in Ho. cbn in Ho.
        clear - Ho SB1. lia.
      - intros _. eapply opnd_at_munch_any; [exact MA1| exact MU2| exact WM2| |]; cbn [md_addr md_own md_p md_n].
        + cbn. split; [| exact I]. destruct (Z.eq_dec nX 0) as [Z0|NZ]; [pose proof (PX0 Z0); clear - H Z0 SB1 NLE K1 A0; lia|].
          destruct (XF ltac:(clear - NZ NRX; lia)) as (EO & _). pose proof (OA2 EO) as D. clear - D SB1. lia.
        + intros AN. cbn. split; [| exact I].
          assert (PA0 : 0 <= pA) by (destruct ownA; [exfalso; exact (AN eq_refl)| ddestruct OWNA as (_ & AIN & _); pose proof (proj1 (Forall_forall _ _) HBR _ AIN) as (R0 & _); cbn in R0; clear - R0; lia| ddestruct OWNA as (_ & _ & AP0 & _); clear - AP0; lia]).
          destruct (Z.eq_dec nX 0) as [Z0|NZ]; [pose proof (PX0 Z0); clear - H Z0 SB1 NLE K1 PA0; lia|].
          destruct (XF ltac:(clear - NZ NRX; lia)) as (EO & _).
          destruct OA3 as [C|[C|[C|C]]]; [exfalso; exact (NEQA C)| exfalso; exact (C EO)| exfalso; exact (AN C)| clear - C SB1 K1; lia].
      - (* [comment removed for export] *)
        intros NEQB. eapply opnd_at_munch_any; [exact MB1| exact MU2| exact WM2| |]; cbn [md_addr md_own md_p md_n].
        + cbn. split; [| exact I]. destruct (Z.eq_dec nX 0) as [Z0|NZ]; [pose proof (PX0 Z0); clear - H Z0 SB1 NLE K1 B0; lia|].
          destruct (XF ltac:(clear - NZ NRX; lia)) as (EO & _). pose proof (OB2 EO) as D. clear - D SB1. lia.
        + intros BN. cbn. split; [| exact I].
          assert (PB0 : 0 <= pB) by (destruct ownB; [exfalso; exact (BN eq_refl)| ddestruct OWNB as (_ & BIN & _); pose proof (proj1 (Forall_forall _ _) HBR _ BIN) as (R0 & _); cbn in R0; clear - R0; lia| ddestruct OWNB as (_ & _ & BP0 & _); clear - BP0; lia]).
          destruct (Z.eq_dec nX 0) as [Z0|NZ]; [pose proof (PX0 Z0); clear - H Z0 SB1 NLE K1 PB0; lia|].
          destruct (XF ltac:(clear - NZ NRX; lia)) as (EO & _).
          destruct OB3 as [C|[C|[C|C]]]; [exfalso; exact (NEQB C)| exfalso; exact (C EO)| exfalso; exact (BN C)| clear - C SB1 K1; lia].
      - clear - K1. lia.
      - intros E. exfalso. exact (NEQA E).
      - intros E k Hk. rewrite (SPRE k Hk). injection E as _ _ _ _ EL _ _. rewrite EL. reflexivity. }
    (* [comment removed for export] *)
    assert (NEQA : mkMPD X sX nX pX xs0 padX ownX <> mkMPD Aa sA nA pA ys padA ownA) by (intros E; injection E; clear - K1; lia).
    zstep. zstep. zstep.
    replace (Z_to_bv 64 0x3f960) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := nA) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity;
      clear - SLO HLS ACL ACP HTOP NRA SPB; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HPc & h2 & HT2 & RES2).
    replace (ret_pc (Z_to_bv 64 133224)) with (Z_to_bv 64 133224) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    (* [comment removed for export] *)
    assert (XCR : client_range L LB (bv_unsigned sp - 64) X 16).
    { intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C; lia| right; left; exact C| right; right; exact C]. }
    assert (ACR' : client_range L LB (bv_unsigned sp - 64) Aa 16).
    { intros a Ha. destruct (CRA a Ha) as [C|[C|C]]; [left; clear - C Ha OA4; lia| right; left; exact C| right; right; exact C]. }
    assert (BCR' : client_range L LB (bv_unsigned sp - 64) Ba 16).
    { intros a Ha. destruct (CRB a Ha) as [C|[C|C]]; [left; clear - C Ha OB4; lia| right; left; exact C| right; right; exact C]. }
    apply (heap_pres_rw_cells usegs L LB _ m1 m2 _ _ HPc) in CX1; [| exact XCR].
    apply (heap_pres_rw_cells usegs L LB _ m1 m2 _ _ HPc) in CA1; [| exact ACR'].
    apply (heap_pres_rw_cells usegs L LB _ m1 m2 _ _ HPc) in FR1; [| apply client_range_stack; clear; lia].
    assert (SOK2 : statics_ok usegs L m2) by (eapply statics_ok_heap_pres; [exact SOK1| exact HPc| exact SW]).
    assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sX nX pX xs0 padX ownX)) m m2).
    { eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_pres_sub; [exact HPc| intros b Hb; exact Hb| clear; lia| clear; lia]. }
    clear MU WM ST1 SOK1 HPX1.
    destruct RES2 as [[-> HH2] | (An & -> & HBA & HH2 & HNEW)].
    { (* [comment removed for export] *)
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      zstep. zstep. zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      eapply aevtM_cut_evt; [exact MK2| eapply sub_epilogue; [exact FR1| exact MI2| clear - SPB SLO HLS ACL ACP; lia] |].
      cbv beta. intros ms' (-> & _).
      apply aevtM_done. subst POST. unfold mpi_binop_post. deexists 14. dexists m2, mo2, h2, LB, (mkMPD X sX nX pX xs0 padX ownX), MBEDTLS_ERR_MPI_ALLOC_FAILED.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [reflexivity|]. split; [exact MI2|]. split; [release_frame FR1 ST2 (bv_unsigned sp); exact ST2|]. split; [exact MF2|]. split; [exact HT2|].
      split; [exact HH2|].
      assert (XBL : forall b, In b (mpd_blk (mkMPD X sX nX pX xs0 padX ownX)) -> In b LB).
      { intros b Hb. unfold mpd_blk in Hb; cbn [md_own md_p md_n] in Hb. destruct ownX; try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (proj2 OWNX)). }
      split; [eapply mpd_at_heap_pres0; [exact MX1| exact HPc| exact MI1| exact MI2| exact XCR| | exact XBL]|].
      { cbn [md_own md_p md_n]. intros EO. rewrite EO in OWNX. ddestruct OWNX as (_ & XIN & _). intros a Ha. right; right. exists (pX, 4 * nX). split; [exact XIN| cbn; exact Ha]. }
      split; [apply mpd_out_refl; cbn; exact NST|].
      split; [exact HPX2|]. split; [exact SOK2|].
      split; [right; left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros b Hb; left; exact Hb| cbn [md_n]; reflexivity]. }
    (* [comment removed for export] *)
    replace (nA * 4) with (4 * nA) in * by (clear; lia).
    dpose HBA as (An0 & An16 & _ & AnC & AnI).
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 HAP2]. pose proof (HND _ _ _ _ HH2) as ND2.
    destruct HAP2 as [HAPA _].
    assert (ANEW : ~ In (An, 4 * nA) LB) by (intros Hin; pose proof (HAPA An (4 * nA) Hin); clear - H K1 NRX; lia).
    (* [comment removed for export] *)
    assert (CONT : forall mc moc (hc : HST usegs L HI) LBc (xsb : list word) (q0 q1 q2 b0 b1 b3 b4 b5 b6 b7 q3 q4 q5 q6 zra : word),
      mem_inv usegs mc -> stk usegs mc lo (bv_unsigned sp - 64) ->
      rw_cells usegs mc (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs mc X [C8 (Z_to_bv 64 pX); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 nX); C4 padX] ->
      rw_cells usegs mc Aa [C8 (Z_to_bv 64 pA); C2 (Z_to_bv 64 sA); C2 (Z_to_bv 64 nA); C4 padA] ->
      HEAP usegs L HI hc LBc mc moc -> heap_top usegs L HI hc = heap_top usegs L HI h -> mo_frame mo moc -> statics_ok usegs L mc ->
      u32arr usegs mc An xsb -> Z.of_nat (length xsb) = nA -> (forall k, (k < Z.to_nat nX)%nat -> limb32 xsb k = limb32 xs0 k) ->
      In (An, 4 * nA) LBc -> (forall b, In b LBc -> In b LB \/ b = (An, 4 * nA)) ->
      (forall b, In b LB -> ~ In b (mpd_blk (mkMPD X sX nX pX xs0 padX ownX)) -> In b LBc) ->
      (forall b, In b (mpd_blk (mkMPD X sX nX pX xs0 padX ownX)) -> ~ In b LBc) ->
      heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sX nX pX xs0 padX ownX)) m mc ->
      opnd_at usegs mc LBc (bv_unsigned sp) (mkMPD Aa sA nA pA ys padA ownA) ->
      (mkMPD X sX nX pX xs0 padX ownX <> mkMPD Ba sB nB pB zs padB ownB -> opnd_at usegs mc LBc (bv_unsigned sp) (mkMPD Ba sB nB pB zs padB ownB)) ->
      aevtM usegs moc POST
        (MS (mkR zra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp q0 q1 q2 (Z_to_bv 64 X) (Z_to_bv 64 n)
                b0 b1 (Z_to_bv 64 Ba) b3 b4 b5 b6 b7 (Z_to_bv 64 nA) (Z_to_bv 64 An) (Z_to_bv 64 (4 * n)) (Z_to_bv 64 Ba) (Z_to_bv 64 Aa) s7 s8 s9 s10 s11 q3 q4 q5 q6)
            F (Z_to_bv 64 0x208b0) fc None mc (seg_rom usegs))).
    { intros mc moc hc LBc xsb q0 q1 q2 b0 b1 b3 b4 b5 b6 b7 q3 q4 q5 q6 zra MIc STc FRc CXc CAc HHc HTc MFc SOKc XAb LENb PFXb INc SUBc KEEPc OLDc HPXc MAc MBc.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MKc.
      destruct (heap_blocks _ _ HI _ _ _ _ HHc) as [HBRc HAPc].
      assert (DXA : X + 16 <= Aa \/ Aa + 16 <= X) by (destruct SXA as [E|D]; [exfalso; exact (NEQA E)| cbn [md_addr] in D; exact D]).
      assert (XSn' : X + 16 <= An \/ An + 4 * nA <= X).
      { destruct (client_range_apart L LB (bv_unsigned sp - 64) X 16 An (4 * nA) XCR); [clear; lia| clear - K1 NRX; lia| clear - ACL SLO HLS; lia| exact AnC| clear - AnI DIMG; lia| exact HAPA| right; assumption| left; assumption]. }
      assert (ASn' : Aa + 16 <= An \/ An + 4 * nA <= Aa).
      { destruct (client_range_apart L LB (bv_unsigned sp - 64) Aa 16 An (4 * nA) ACR'); [clear; lia| clear - K1 NRX; lia| clear - ACL SLO HLS; lia| exact AnC| clear - AnI DIMG; lia| exact HAPA| right; assumption| left; assumption]. }
      assert (BSn' : Ba + 16 <= An \/ An + 4 * nA <= Ba).
      { destruct (client_range_apart L LB (bv_unsigned sp - 64) Ba 16 An (4 * nA) BCR'); [clear; lia| clear - K1 NRX; lia| clear - ACL SLO HLS; lia| exact AnC| clear - AnI DIMG; lia| exact HAPA| right; assumption| left; assumption]. }
      assert (LAn' : forall own (p k : Z), 1 <= k ->
                match own with LNull => False | LHeap => In (p, 4 * k) LB | LStatic => (forall i, 0 <= i < 4 * k -> ro_addr usegs (wa (p + i)) = true) \/ (bv_unsigned sp <= p /\ p + 4 * k < 2^64) end ->
                0 <= p /\ p + 4 * k <= 2^64 -> p + 4 * k <= An \/ An + 4 * nA <= p).
      { intros [| |] p k Hk Ho Hb; [destruct Ho| destruct (HAPA p (4 * k) Ho); [right| left]; assumption|].
        destruct Ho as [Ho|[HSP _]]; [| right; clear - HSP AnC ACL SLO HLS; lia].
        pose proof (ROIMG (p + 0) (Ho 0 ltac:(clear - Hk; lia)) ltac:(clear - Hb Hk; lia)) as I0.
        pose proof (ROIMG (p + (4 * k - 1)) (Ho (4 * k - 1) ltac:(clear - Hk; lia)) ltac:(clear - Hb Hk; lia)) as I1. clear - I0 I1 AnI Hk. lia. }
      pose proof alloc_ceiling_bounds as ACV'.
      pose proof (conj HHc I) as HHcc. pose proof (conj SOKc I) as SOKcc. clear HHc SOKc.
      try clear MU WM. pose proof (munch_refl [(X, X + 16)] mc) as MU. pose proof (wmono_refl usegs mc) as WM.
      zstep. zstep. zstep. rewrite zx16_small by (clear - NRA; lia). zstep.
      zstep. if_cases K5; zify_cond K5; [exfalso; clear - K5 DXA XB AB; lia|].
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      pose proof (opnd_view _ _ _ _ _ MA) as [(_ & _ & _ & LA0 & _ & OA0) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in LA0, OA0.
      pose proof (opnd_view _ _ _ _ _ MB) as [(_ & _ & _ & LB0 & _ & OB0) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in LB0, OB0.
      (* [comment removed for export] *)
      assert (MA5 : opnd_at usegs m5 LBc (bv_unsigned sp) (mkMPD Aa sA nA pA ys padA ownA)).
      { eapply opnd_at_munch_any; [exact MAc| exact MU| exact WM| cbn; split; [clear - DXA; lia| exact I]|].
        cbn [md_own md_p md_n]. intros AN. cbn. split; [| exact I]. destruct (OA1 AN); [right| left]; assumption. }
      assert (MB5 : mkMPD X sX nX pX xs0 padX ownX <> mkMPD Ba sB nB pB zs padB ownB -> opnd_at usegs m5 LBc (bv_unsigned sp) (mkMPD Ba sB nB pB zs padB ownB)).
      { intros NEQB. assert (DXB : X + 16 <= Ba \/ Ba + 16 <= X) by (destruct SXB as [E|D]; [exfalso; exact (NEQB E)| cbn [md_addr] in D; exact D]).
        eapply opnd_at_munch_any; [exact (MBc NEQB)| exact MU| exact WM| cbn; split; [clear - DXB; lia| exact I]|].
        cbn [md_own md_p md_n]. intros BN. cbn. split; [| exact I]. destruct (OB1 BN); [right| left]; assumption. }
      assert (ALAn : ownA <> LNull -> pA + 4 * nA <= An \/ An + 4 * nA <= pA).
      { intros AN. apply (LAn' ownA pA nA); [destruct ownA; [exfalso; exact (AN eq_refl)| exact (proj1 OA0)| exact (proj1 OA0)]| |].
        - destruct ownA; [exact (AN eq_refl)| exact (proj1 (proj2 OA0))| exact (proj2 (proj2 (proj2 (proj2 OA0))))].
        - destruct ownA; [exfalso; exact (AN eq_refl)| |].
          + ddestruct OA0 as (_ & AIN & _). pose proof (proj1 (Forall_forall _ _) HBR _ AIN) as (R0 & _ & _ & R3 & _). cbn in R0, R3. clear - R0 R3 ACV'. lia.
          + ddestruct OA0 as (_ & _ & AP0 & ABY & _). pose proof (u32ro_bound _ _ _ _ ABY) as BB. clear - AP0 BB LA0. lia. }
      eapply aevtM_cut_evt; [exact MKc| |].
      { eapply (seg2_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m5 X An nA n sX lo padX xsb Aa pA nA (Z_to_bv 64 sA) padA ys Ba);
          try eassumption.
        - clear - X0 XB XAL. lia.
        - clear - A0 AB. lia.
        - clear - SB1 NLE NRA. lia.
        - clear - SLO HLS. lia.
        - intros _. split; [exact XAb|]. split; [exact An0|]. split; [exact An16|]. split; [clear - AnC ACL; lia|]. split; [exact XSn'| exact ASn'].
        - intros LT. pose proof (opnd_view _ _ _ _ _ MA5) as [(_ & _ & _ & _ & _ & OAm) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OAm.
          destruct ownA; [exfalso; clear - OA0 LT SB1; lia| |].
          + ddestruct OAm as (_ & _ & _ & AARR). split; [apply u32arr_ro; exact AARR| split; [apply ALAn; discriminate| exact (APF LT)]].
          + ddestruct OAm as (_ & _ & _ & ABY & _). split; [exact ABY| split; [apply ALAn; discriminate| exact (APF LT)]]. }
      cbv beta. intros ms' SP2. unfold seg2_post in SP2.
      ddestruct SP2 as (raj' & w0 & w1 & w2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m6 & -> & MU6 & WM6 & MI6 & CX6 & FR6 & XA6).
      ddestruct (splice3_facts xsb ys n nA nA ltac:(clear - SB1 NLE; lia) ltac:(clear; lia) ltac:(clear - NLE LENb; lia) LENA) as (SL & SPRE & SMID & SZERO).
      eapply (KC n (Z_to_bv 64 Ba) (Z_to_bv 64 An) (Z_to_bv 64 nA) m6 moc hc LBc (splice3 xsb ys n nA nA) An nA LHeap _ _ _ _ (Z_to_bv 64 Aa) (Z_to_bv 64 Ba)); try eassumption; try reflexivity.
      all: cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      - eapply stk_transport_disjoint; [exact STc| exact MU6| exact WM6|]. cbn. clear - AnC ACL SB1. lia.
      - destruct HHcc as [HHc _].
        assert (HH5 : HEAP usegs L HI hc LBc m5 moc).
        { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HHc| exact ACL| exact MU| exact WM|].
          intros a Ha NO. cbn in NO. rewrite HTc. assert (Ha' : X <= a < X + 16) by (clear - NO; lia).
          destruct (XCW a Ha') as [C|[C|([q k] & Hq & R)]]; [left; clear - C SLO HLS; lia| right; left; exact C| right; right].
          exists (q, k). split; [| exact R]. apply KEEPc; [exact Hq|]. cbn in R.
          unfold mpd_blk; cbn [md_own md_p md_n]. destruct ownX; try (intros []; fail). intros [E|[]]. injection E as E1 E2.
          destruct (XP eq_refl); clear - H Ha' R E1 E2; lia. }
        eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH5| exact ACL| exact MU6| exact WM6|].
        intros a Ha NO. cbn in NO. right; right. exists (An, 4 * nA). split; [exact INc| cbn; clear - NO SB1; lia].
      - destruct SOKcc as [SOKc _].
        eapply statics_ok_munch; [eapply statics_ok_munch; [exact SOKc| exact MU|]| exact MU6|].
        + intros a Hd NW. cbn. split; [intros C; exact (NW (XD a C Hd))| exact I].
        + intros a Hd NW. cbn. split; [clear - Hd AnI DIMG SB1; lia| exact I].
      - split; [| exact SGX]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        split; [exact CX6|]. split; [exact XAL|]. split; [exact X0|]. split; [exact SL|]. split; [unfold MPI_MAX_LIMBS; clear - NRA; lia|].
        split; [clear - K1 NRX; lia|]. split; [exact INc|]. split; [exact An16|]. apply XA6. clear - K1 NRX; lia.
      - discriminate.
      - unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
        split; [intros b Hb; destruct (SUBc b Hb) as [H1| ->]; [left; exact H1| right; left; reflexivity]|].
        split; [exact KEEPc|].
        intros b Hb Hin. exfalso. exact (OLDc b Hb Hin).
      - unfold mpd_blk; cbn [md_own md_p md_n]. intros b [<-|[]]. right. exact ANEW.
      - eapply heap_presx_trans; [exact HPXc|]. eapply heap_presx_trans.
        + eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn in Ho |- *. split; [| exact I]. clear - Ho. lia.
        + eapply heap_presx_of_munch; [exact MU6| exact WM6|]. intros a Ha Hc Ho. cbn. split; [| exact I].
          destruct Hc as [C|[[C1 C2]|([q k] & Hq & R)]]; [clear - C AnC ACL SLO HLS SB1; lia| clear - C1 AnI DIMG SB1; lia|]. cbn in R.
          pose proof (HAPA q k Hq) as D. clear - D R SB1. lia.
      - intros _. eapply opnd_at_munch_any; [exact MA5| exact MU6| exact WM6| cbn; split; [clear - ASn' SB1; lia| exact I]|].
        cbn [md_own md_p md_n]. intros AN. cbn. split; [| exact I]. destruct (ALAn AN); clear - H SB1; lia.
      - intros NEQB. eapply opnd_at_munch_any; [exact (MB5 NEQB)| exact MU6| exact WM6| cbn; split; [clear - BSn' SB1; lia| exact I]|].
        cbn [md_own md_p md_n]. intros BN. cbn. split; [| exact I].
        enough (D : pB + 4 * nB <= An \/ An + 4 * nA <= pB) by (clear - D SB1; lia).
        apply (LAn' ownB pB nB); [destruct ownB; [exfalso; exact (BN eq_refl)| exact (proj1 OB0)| exact (proj1 OB0)]| |].
        + destruct ownB; [exact (BN eq_refl)| exact (proj1 (proj2 OB0))| exact (proj2 (proj2 (proj2 (proj2 OB0))))].
        + destruct ownB; [exfalso; exact (BN eq_refl)| |].
          * ddestruct OB0 as (_ & BIN & _). pose proof (proj1 (Forall_forall _ _) HBR _ BIN) as (R0 & _ & _ & R3 & _). cbn in R0, R3. clear - R0 R3 ACV'. lia.
          * ddestruct OB0 as (_ & _ & BP0 & BBY & _). pose proof (u32ro_bound _ _ _ _ BBY) as BB. clear - BP0 BB LB0. lia.
      - clear - K1. lia.
      - intros E. exfalso. exact (NEQA E).
      - intros E k Hk. rewrite (SPRE k Hk). injection E as _ _ En _ El _ _. rewrite (PFXb k) by (clear - Hk En SB1; lia). rewrite El. reflexivity. }
    assert (MA2 : opnd_at usegs m2 ((An, 4 * nA) :: LB) (bv_unsigned sp) (mkMPD Aa sA nA pA ys padA ownA)).
    { eapply opnd_at_heap_pres; [exact MA1| exact HPc| exact MI1| exact MI2| exact ACR'| | intros b Hb; right; unfold mpd_blk in Hb; cbn in Hb; destruct ownA; try (destruct Hb; fail); destruct Hb as [<-|[]]; exact (proj1 (proj2 OWNA))| clear; lia].
      cbn [md_own md_p md_n]. intros EO a Ha. destruct (CRAL EO a Ha) as [C|[C|C]]; [left| right; left; exact C| right; right; exact C].
      rewrite EO in OWNA. ddestruct OWNA as (_ & AIN & _). pose proof (proj1 (Forall_forall _ _) HBR _ AIN) as (_ & _ & _ & R3 & _). cbn in R3. clear - C R3 Ha ACL. lia. }
    assert (MB2 : opnd_at usegs m2 ((An, 4 * nA) :: LB) (bv_unsigned sp) (mkMPD Ba sB nB pB zs padB ownB)).
    { eapply opnd_at_heap_pres; [exact MB1| exact HPc| exact MI1| exact MI2| exact BCR'| | intros b Hb; right; unfold mpd_blk in Hb; cbn in Hb; destruct ownB; try (destruct Hb; fail); destruct Hb as [<-|[]]; exact (proj1 (proj2 OWNB))| clear; lia].
      cbn [md_own md_p md_n]. intros EO a Ha. destruct (CRBL EO a Ha) as [C|[C|C]]; [left| right; left; exact C| right; right; exact C].
      rewrite EO in OWNB. ddestruct OWNB as (_ & BIN & _). pose proof (proj1 (Forall_forall _ _) HBR _ BIN) as (_ & _ & _ & R3 & _). cbn in R3. clear - C R3 Ha ACL. lia. }
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep. zstep. if_cases KZ; zify_cond KZ; [exfalso; pose proof alloc_ceiling_bounds as ACV; clear - KZ An0 AnC ACV K1 SB1; lia|].
    zstep. zstep. zstep. if_cases KP; zify_cond KP.
    { (* [comment removed for export] *)
      assert (ownX = LNull) as EO.
      { destruct ownX; [reflexivity| | exfalso; exact (NST eq_refl)]. exfalso. ddestruct OWNX as (_ & XIN & _).
        pose proof (proj1 (Forall_forall _ _) HBR _ XIN) as (R0 & _ & R2 & R3 & _). cbn in R0, R2, R3.
        pose proof alloc_ceiling_bounds as ACV. clear - KP R0 R2 R3 ACV. lia. }
      subst ownX. destruct OWNX as [EP EN0].
      eapply (CONT m2 mo2 h2 ((An, 4 * nA) :: LB) (repeat (Z_to_bv 64 0) (Z.to_nat nA))); try eassumption.
      - eapply u32arr_of_cells; [exact HNEW|]. rewrite u32s_repeat0. f_equal. clear - K1 NRX; lia.
      - rewrite repeat_length. clear - K1 NRX; lia.
      - intros k Hk. exfalso. clear - Hk EN0. lia.
      - left. reflexivity.
      - intros b [<-|Hb]; [right; reflexivity| left; exact Hb].
      - intros b Hb _. right. exact Hb.
      - intros b [].
      - intros _. exact MB2. }
    (* [comment removed for export] *)
    assert (EO : ownX = LHeap) by (destruct ownX; [exfalso; apply KP; rewrite (proj1 OWNX); reflexivity| reflexivity| exfalso; exact (NST eq_refl)]).
    subst ownX. ddestruct OWNX as (NX1 & XIN & XPAL & _).
    pose proof (proj1 (Forall_forall _ _) HBR _ XIN) as (X0' & _ & _ & XC & XI). cbn in X0', XC, XI.
    pose proof (HAPA pX (4 * nX) XIN) as APX.
    assert (MX2 : mpd_at usegs m2 ((An, 4 * nA) :: LB) (mkMPD X sX nX pX xs0 padX LHeap)).
    { eapply mpd_at_heap_pres0; [exact MX1| exact HPc| exact MI1| exact MI2| exact XCR| | intros b Hb; right; unfold mpd_blk in Hb; cbn in Hb; destruct Hb as [<-|[]]; exact XIN].
      cbn [md_own md_p md_n]. intros _ a Ha. right; right. exists (pX, 4 * nX). split; [exact XIN| cbn; exact Ha]. }
    dpose MX2 as [(_ & _ & _ & _ & _ & (_ & _ & _ & XARR2)) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in XARR2.
    pose proof (u32arr_cells _ _ _ _ XARR2) as XCH2.
    (* [comment removed for export] *)
    assert (HN2 : rw_cells usegs m2 An ([CB (4 * length xs0) (repeat (Z_to_bv 8 0) (4 * length xs0))] ++ [CB (Z.to_nat (4 * (nA - nX))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * (nA - nX))))])).
    { eapply rw_cells_reshape; [exact HNEW| |].
      - cbn. rewrite !repeat_length; repeat split; reflexivity.
      - cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- repeat_app. f_equal. clear - LENX K1 NX1. lia. }
    apply rw_cells_app in HN2. destruct HN2 as [HNA HNB]. cbn [cells_size csize Nat.add] in HNB. clear HNEW.
    replace (An + Z.of_nat (4 * length xs0 + 0)) with (An + 4 * nX) in HNB by (clear - LENX; lia).
    (* [comment removed for export] *)
    assert (XSn : X + 16 <= An \/ An + 4 * nA <= X).
    { destruct (client_range_apart L LB (bv_unsigned sp - 64) X 16 An (4 * nA) XCR); [clear; lia| clear - K1 NRX; lia| clear - ACL SLO HLS; lia| exact AnC| clear - AnI DIMG; lia| exact HAPA| right; assumption| left; assumption]. }
    assert (ASn : Aa + 16 <= An \/ An + 4 * nA <= Aa).
    { destruct (client_range_apart L LB (bv_unsigned sp - 64) Aa 16 An (4 * nA) ACR'); [clear; lia| clear - K1 NRX; lia| clear - ACL SLO HLS; lia| exact AnC| clear - AnI DIMG; lia| exact HAPA| right; assumption| left; assumption]. }
    assert (BSn : Ba + 16 <= An \/ An + 4 * nA <= Ba).
    { destruct (client_range_apart L LB (bv_unsigned sp - 64) Ba 16 An (4 * nA) BCR'); [clear; lia| clear - K1 NRX; lia| clear - ACL SLO HLS; lia| exact AnC| clear - AnI DIMG; lia| exact HAPA| right; assumption| left; assumption]. }
    (* [comment removed for export] *)
    assert (LAn : forall own (p k : Z), 1 <= k ->
              match own with LNull => False | LHeap => In (p, 4 * k) LB | LStatic => (forall i, 0 <= i < 4 * k -> ro_addr usegs (wa (p + i)) = true) \/ (bv_unsigned sp <= p /\ p + 4 * k < 2^64) end ->
              0 <= p /\ p + 4 * k <= 2^64 -> p + 4 * k <= An \/ An + 4 * nA <= p).
    { intros [| |] p k Hk Ho Hb; [destruct Ho| destruct (HAPA p (4 * k) Ho); [right| left]; assumption|].
      destruct Ho as [Ho|[HSP _]]; [| right; clear - HSP AnC ACL SLO HLS; lia].
      pose proof (ROIMG (p + 0) (Ho 0 ltac:(clear - Hk; lia)) ltac:(clear - Hb Hk; lia)) as I0.
      pose proof (ROIMG (p + (4 * k - 1)) (Ho (4 * k - 1) ltac:(clear - Hk; lia)) ltac:(clear - Hb Hk; lia)) as I1. clear - I0 I1 AnI Hk. lia. }
    clear MU WM. pose proof (munch_refl [(An, An + 4 * nA)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof (conj HH2 I) as HH2c. clear HH2. pose proof (conj SOK2 I) as SOK2c. clear SOK2.
    pose proof alloc_ceiling_bounds as ACV.
    assert (U1 : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; clear - An0 AnC ACV NRA; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 pX) = pX) by (apply unsigned_lit; clear - X0' XC ACV NRX; lia).
    assert (LORA : Z.land (Z.lor pX An) 3 = 0) by (apply sab_lor_land3_0; clear - XPAL An16; Z.div_mod_to_equations; lia).
    zstep. zstep. rewrite ?U1, ?U2. rewrite LORA. zstep. if_false. clear LORA.
    zstep. rewrite ?zx16_small by (clear - NRX; lia). zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof U_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    assert (U3 : bv_unsigned (Z_to_bv 64 (nX * 4)) = nX * 4) by (apply unsigned_lit; clear - NRX; lia).
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPc with (src := u32s xs0); rewrite ?U1, ?U2, ?U3;
      [ eapply u32arr_ro; exact XARR2 | rewrite u32s_length; clear - LENX; lia | replace (Z.to_nat (nX * 4)) with (4 * length xs0)%nat by (clear - LENX; lia); exact HNA | clear - APX NX1 K1; lia | exact MI2 ] | ].
    clear SPc. unfold memcpy_post. cbv beta. intros ms' PO.
    ddestruct PO as (z0 & z1 & z2 & za1 & za2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & m3 & E & MUd & WMd & MI3 & PA3 & _). subst ms'.
    rewrite ?U1, ?U2, ?U3 in MUd. rewrite ?U1, ?U2, ?U3 in PA3.
    replace (ret_pc (Z_to_bv 64 133276)) with (Z_to_bv 64 133276) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    (* [comment removed for export] *)
    assert (CX3 : rw_cells usegs m3 X [C8 (Z_to_bv 64 pX); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 nX); C4 padX]).
    { eapply rw_cells_transport; [exact CX1| exact MUd| exact WMd|]. cbn. clear - XSn K1. lia. }
    assert (CA3 : rw_cells usegs m3 Aa [C8 (Z_to_bv 64 pA); C2 (Z_to_bv 64 sA); C2 (Z_to_bv 64 nA); C4 padA]).
    { eapply rw_cells_transport; [exact CA1| exact MUd| exact WMd|]. cbn. clear - ASn K1. lia. }
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR1| exact MUd| exact WMd|]. cbn. clear - AnC ACL SLO HLS K1. lia. }
    assert (HNB3 : rw_cells usegs m3 (An + 4 * nX) [CB (Z.to_nat (4 * (nA - nX))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * (nA - nX))))]).
    { eapply rw_cells_transport; [exact HNB| exact MUd| exact WMd|]. cbn. clear - K1. lia. }
    assert (ST3 : stk usegs m3 lo (bv_unsigned sp - 64)).
    { eapply stk_transport_disjoint; [exact ST2| exact MUd| exact WMd|]. cbn. clear - AnC ACL K1. lia. }
    assert (XCH3 : rw_cells usegs m3 pX [CB (4 * length xs0) (u32s xs0)]).
    { eapply rw_cells_transport; [exact XCH2| exact MUd| exact WMd|]. cbn. rewrite ?u32s_length. clear - APX K1 NX1 LENX. lia. }
    assert (HH3 : HEAP usegs L HI h2 ((An, 4 * nA) :: LB) m3 mo2).
    { destruct HH2c as [HH2 _]. eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH2| exact ACL| exact MUd| exact WMd|].
      intros a Ha NO. cbn in NO. right; right. exists (An, 4 * nA). split; [left; reflexivity| cbn; clear - NO K1; lia]. }
    assert (SOK3 : statics_ok usegs L m3).
    { destruct SOK2c as [SOK2 _]. eapply statics_ok_munch; [exact SOK2| exact MUd|]. intros a Hd NW. cbn. split; [clear - Hd AnI DIMG K1; lia| exact I]. }
    assert (MA3 : opnd_at usegs m3 ((An, 4 * nA) :: LB) (bv_unsigned sp) (mkMPD Aa sA nA pA ys padA ownA)).
    { eapply opnd_at_munch_any; [exact MA2| exact MUd| exact WMd| cbn; split; [clear - ASn K1; lia| exact I]|].
      cbn [md_own md_p md_n]. intros AN. cbn. split; [| exact I].
      pose proof (opnd_view _ _ _ _ _ MA1) as [(_ & _ & _ & LA' & _ & OA') _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in LA', OA'.
      destruct (LAn ownA pA nA) as [D|D]; [| destruct ownA; [exact (AN eq_refl)| exact (proj1 (proj2 OA'))| exact (proj2 (proj2 (proj2 (proj2 OA'))))]| | clear - D K1; lia| clear - D K1; lia].
      - destruct ownA; [exfalso; exact (AN eq_refl)| exact (proj1 OA')| exact (proj1 OA')].
      - destruct ownA; [exfalso; exact (AN eq_refl)| |].
        + ddestruct OA' as (_ & AIN & _). pose proof (proj1 (Forall_forall _ _) HBR _ AIN) as (R0 & _ & _ & R3 & _). cbn in R0, R3. clear - R0 R3 ACV. lia.
        + ddestruct OA' as (_ & _ & AP0 & ABY & _). pose proof (u32ro_bound _ _ _ _ ABY) as BB. clear - AP0 BB LA'. lia. }
    assert (MB3 : opnd_at usegs m3 ((An, 4 * nA) :: LB) (bv_unsigned sp) (mkMPD Ba sB nB pB zs padB ownB)).
    { eapply opnd_at_munch_any; [exact MB2| exact MUd| exact WMd| cbn; split; [clear - BSn K1; lia| exact I]|].
      cbn [md_own md_p md_n]. intros BN. cbn. split; [| exact I].
      pose proof (opnd_view _ _ _ _ _ MB1) as [(_ & _ & _ & LB' & _ & OB') _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in LB', OB'.
      destruct (LAn ownB pB nB) as [D|D]; [| destruct ownB; [exact (BN eq_refl)| exact (proj1 (proj2 OB'))| exact (proj2 (proj2 (proj2 (proj2 OB'))))]| | clear - D K1; lia| clear - D K1; lia].
      - destruct ownB; [exfalso; exact (BN eq_refl)| exact (proj1 OB')| exact (proj1 OB')].
      - destruct ownB; [exfalso; exact (BN eq_refl)| |].
        + ddestruct OB' as (_ & BIN & _). pose proof (proj1 (Forall_forall _ _) HBR _ BIN) as (R0 & _ & _ & R3 & _). cbn in R0, R3. clear - R0 R3 ACV. lia.
        + ddestruct OB' as (_ & _ & BP0 & BBY & _). pose proof (u32ro_bound _ _ _ _ BBY) as BB. clear - BP0 BB LB'. lia. }
    assert (HPX3 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sX nX pX xs0 padX LHeap)) m m3).
    { eapply heap_presx_trans; [exact HPX2|]. eapply heap_presx_of_munch; [exact MUd| exact WMd|].
      intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [C|[[C1 C2]|([q k] & Hq & R)]]; [clear - C AnC ACL SLO HLS K1; lia| clear - C1 AnI DIMG K1; lia|]. cbn in R.
      pose proof (HAPA q k Hq) as D. clear - D R K1. lia. }
    clear CX1 CA1 FR1 HNB ST2 XCH2 XARR2 HH2c SOK2c MA2 MB2 HPX2 MUd WMd MI2 MU WM HNA.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    (* [comment removed for export] *)
    zstep. rewrite ?zx16_small by (clear - NRX; lia). zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
    eapply aevtM_cut.
    { eapply (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := pX) (len := 4 * nX) (lo := lo) (junk := u32s xs0);
        rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity.
      - right. split; [right; exact XIN|]. replace (Z.to_nat (4 * nX)) with (4 * length xs0)%nat by (clear - LENX; lia). exact XCH3.
      - clear - NX1 NRX. lia.
      - clear - SLO. lia.
      - rewrite HT2. clear - HTOP. lia.
      - clear - SPA SPB SLO HLS ACL ACP. lia.
      - rewrite <- MSFE. exact CA.
      - f_equal. clear. lia. }
    cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & mo4 & h4 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    ddestruct PO as (MI4 & ST4 & MF4 & HT4 & HH4 & PX4 & SOK4).
    replace (ret_pc (Z_to_bv 64 133292)) with (Z_to_bv 64 133292) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (NEAP : An <> pX) by (clear - APX NX1 K1; lia).
    assert (LBR : lb_remove pX ((An, 4 * nA) :: LB) = (An, 4 * nA) :: lb_remove pX LB) by (cbn; destruct (Z.eqb_spec An pX); [exfalso; exact (NEAP ltac:(assumption))| reflexivity]).
    rewrite LBR in HH4, PX4. clear LBR.
    (* [comment removed for export] *)
    assert (KEEP : forall q k, In (q, k) LB -> (q, k) <> (pX, 4 * nX) -> In (q, k) (lb_remove pX LB)).
    { intros q k Hq NE. apply In_lb_remove_keep; [exact Hq|]. exact (nodup_fst_neq LB pX (4 * nX) q k ND XIN Hq NE). }
    (* [comment removed for export] *)
    assert (XCR4 : client_range L ((An, 4 * nA) :: lb_remove pX LB) (bv_unsigned sp - 64) X 16).
    { intros a Ha. destruct (XCW a Ha) as [C|[C|([q k] & Hq & R)]]; [left; clear - C; lia| right; left; exact C| right; right].
      exists (q, k). split; [| exact R]. right. apply KEEP; [exact Hq|]. intros E. injection E as E1 E2. cbn in R. destruct (XP eq_refl); clear - H Ha R E1 E2; lia. }
    apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in CX3; [| exact XCR4| cbn; split; [destruct (XP eq_refl); clear - H; lia| exact I]].
    apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in FR3; [| apply client_range_stack; clear; lia| cbn; split; [clear - XC ACL SLO HLS; lia| exact I]].
    apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in PA3;
      [| intros a Ha; right; right; exists (An, 4 * nA); split; [left; reflexivity| cbn; cbn in Ha; rewrite ?u32s_length in Ha; clear - Ha K1 LENX; lia]
       | cbn; rewrite ?u32s_length; split; [clear - APX K1 LENX NX1; lia| exact I]].
    apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in HNB3;
      [| intros a Ha; right; right; exists (An, 4 * nA); split; [left; reflexivity| cbn; cbn in Ha; clear - Ha K1 NX1; lia]
       | cbn; split; [clear - APX K1 NX1; lia| exact I]].
    assert (ACR4 : client_range L ((An, 4 * nA) :: lb_remove pX LB) (bv_unsigned sp - 64) Aa 16).
    { intros a Ha. destruct (ACR' a Ha) as [C|[C|([q k] & Hq & R)]]; [left; exact C| right; left; exact C| right; right].
      exists (q, k). split; [| exact R]. right. apply KEEP; [exact Hq|]. intros E. injection E as E1 E2. cbn in R. destruct (OA2 eq_refl); clear - H Ha R E1 E2; lia. }
    apply (heap_presx_rw_cells usegs L _ _ _ m3 m4 _ _ PX4) in CA3; [| exact ACR4| cbn; split; [destruct (OA2 eq_refl); clear - H; lia| exact I]].
    (* [comment removed for export] *)
    assert (LBK : forall own (p k : Z) (d : mpd), md_own d = own -> md_p d = p -> md_n d = k ->
              mkMPD X sX nX pX xs0 padX LHeap <> d -> opnd_at usegs m LB (bv_unsigned sp) d ->
              (mkMPD X sX nX pX xs0 padX LHeap = d \/ LHeap <> LHeap \/ own = LNull \/ pX + 4 * nX <= p \/ p + 4 * k <= pX) ->
              (own = LHeap -> In (p, 4 * k) ((An, 4 * nA) :: lb_remove pX LB) /\ (pX + 4 * nX <= p \/ p + 4 * k <= pX))
              /\ (own <> LNull -> pX + 4 * nX <= p \/ p + 4 * k <= pX)).
    { intros own p k d E1 E2 E3 NE Md SEP.
      assert (D : own <> LNull -> pX + 4 * nX <= p \/ p + 4 * k <= pX).
      { intros ON. destruct SEP as [C|[C|[C|C]]]; [exfalso; exact (NE C)| exfalso; apply C; reflexivity| exfalso; exact (ON C)| exact C]. }
      split; [| exact D]. intros EO. split; [| apply D; rewrite EO; discriminate].
      destruct (opnd_view _ _ _ _ _ Md) as [(_ & _ & _ & _ & Nd & Od) _]. rewrite E1, EO, E2, E3 in Od. ddestruct Od as (K1' & IN & _).
      right. apply KEEP; [exact IN|]. intros E. injection E as Ep Ek. destruct (D ltac:(rewrite EO; discriminate)); clear - H Ep Ek K1' NX1; lia. }
    destruct (LBK ownA pA nA (mkMPD Aa sA nA pA ys padA ownA) eq_refl eq_refl eq_refl NEQA MA OA3) as [AK1 AK2].
    assert (MA4 : opnd_at usegs m4 ((An, 4 * nA) :: lb_remove pX LB) (bv_unsigned sp) (mkMPD Aa sA nA pA ys padA ownA)).
    { eapply opnd_at_heap_presx; [exact MA3| exact PX4| exact MI3| exact MI4| | | | | | clear; lia]; cbn [md_addr md_own md_p md_n].
      - exact ACR4.
      - intros EO a Ha. right; right. exists (pA, 4 * nA). split; [exact (proj1 (AK1 EO))| cbn; exact Ha].
      - cbn. split; [destruct (OA2 eq_refl); clear - H; lia| exact I].
      - intros AN. cbn. split; [destruct (AK2 AN); [right| left]; assumption| exact I].
      - intros b Hb. unfold mpd_blk in Hb; cbn [md_own md_p md_n] in Hb. destruct ownA; try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (AK1 eq_refl)). }
    assert (MB4 : mkMPD X sX nX pX xs0 padX LHeap <> mkMPD Ba sB nB pB zs padB ownB -> opnd_at usegs m4 ((An, 4 * nA) :: lb_remove pX LB) (bv_unsigned sp) (mkMPD Ba sB nB pB zs padB ownB)).
    { intros NEQB. destruct (LBK ownB pB nB (mkMPD Ba sB nB pB zs padB ownB) eq_refl eq_refl eq_refl NEQB MB OB3) as [BK1 BK2].
      eapply opnd_at_heap_presx; [exact MB3| exact PX4| exact MI3| exact MI4| | | | | | clear; lia]; cbn [md_addr md_own md_p md_n].
      - intros a Ha. destruct (BCR' a Ha) as [C|[C|([q k] & Hq & R)]]; [left; exact C| right; left; exact C| right; right].
        exists (q, k). split; [| exact R]. right. apply KEEP; [exact Hq|]. intros E. injection E as E1 E2. cbn in R. destruct (OB2 eq_refl); clear - H Ha R E1 E2; lia.
      - intros EO a Ha. right; right. exists (pB, 4 * nB). split; [exact (proj1 (BK1 EO))| cbn; exact Ha].
      - cbn. split; [destruct (OB2 eq_refl); clear - H; lia| exact I].
      - intros BN. cbn. split; [destruct (BK2 BN); [right| left]; assumption| exact I].
      - intros b Hb. unfold mpd_blk in Hb; cbn [md_own md_p md_n] in Hb. destruct ownB; try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (BK1 eq_refl)). }
    assert (HPX4 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sX nX pX xs0 padX LHeap)) m m4).
    { eapply heap_presx_trans; [exact HPX3|]. intros a Ha Hc Ho. cbn in Ho. ddestruct Ho as (O1 & O2 & _).
      apply PX4; [exact Ha| | cbn; split; [exact O2| exact I]].
      destruct Hc as [C|[C|([q k] & Hq & R)]]; [left; clear - C; lia| right; left; exact C| right; right; exists (q, k); split; [|exact R]].
      right. apply KEEP; [exact Hq|]. intros E. injection E as E1 E2. cbn in R. clear - R O2 E1 E2. lia. }
    clear CX_dummy || idtac.
    pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    zstep.
    eapply (CONT m4 mo4 h4 ((An, 4 * nA) :: lb_remove pX LB) (xs0 ++ repeat (Z_to_bv 64 0) (Z.to_nat (nA - nX)))); try eassumption.
    - rewrite HT4. exact HT2.
    - eapply mo_frame_trans; [exact MF2| exact MF4].
    - apply u32arr_app. split; [eapply u32arr_of_cells; [exact PA3| reflexivity]|].
      replace (An + 4 * Z.of_nat (length xs0)) with (An + 4 * nX) by (clear - LENX; lia).
      eapply u32arr_of_cells; [exact HNB3|]. rewrite u32s_repeat0. f_equal. clear - K1 NRX. lia.
    - rewrite length_app, repeat_length. clear - LENX K1 NRX. lia.
    - intros k Hk. apply limb32_app_l. clear - Hk LENX. lia.
    - left. reflexivity.
    - intros b [<-|Hb]; [right; reflexivity| left; eapply In_lb_remove; exact Hb].
    - intros [q k] Hq Hn. right. apply KEEP; [exact Hq|]. intros E. apply Hn. rewrite E. left. reflexivity.
    - intros b [<-|[]] [E|Hin]; [injection E as E1 E2; apply NEAP; exact E1| exact (lb_remove_notin LB pX (4 * nX) ND Hin)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End J1.
