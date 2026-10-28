(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_core_mla U_mpi_mul_int_W.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_mla_v1 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.sxz"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.zx32"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sx32"; "Stdlib.ZArith.BinInt.Z.b2z"; "Stdlib.ZArith.BinInt.Z.ltb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.w32"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limb32"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Peano.le"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_int_W.mpi_core_mla_vpost"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L8931307546.2000003S1w". (* [comment removed for export] *)
Lemma zx32_val : forall w : word, bv_unsigned (zx32 w) = w32 w.
Proof. intros w. unfold zx32, w32. apply unsigned_lit. pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32)). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L38715782812.2L44015171709.2000001002SS". (* [comment removed for export] *)
Lemma shl32_shr32 : forall a, 0 <= a -> Z.shiftr ((Z.shiftl a 32) mod 18446744073709551616) 32 = a mod 2^32.
Proof.
  intros a Ha. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change 18446744073709551616 with (2^32 * 2^32).
  rewrite Zmult_mod_distr_r. rewrite Z.div_mul by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00T0?L10283289232.32L11901755012.28L11901780990.21L13039274160.36L13570767458.21L16039673958.24L16046136858.13L16046136858.14L16046136858.31L16046136858.32L1954282746.19 L21908260128.30L21908260257.29L27163916913.31L29520084561.29L29520387478.24L29520387728.28L3002272248.32 L35212933531.19L35821357223.32L36834527243.15L38715777780.17L38715908983.21L38717875063.31L38717875063.32L42470587853.23L42470588107.26L42470797781.19L42470798813.18L44015300113.16L44891823404.32L51196457344.36L51677037936.31L64591821213.38L7575817642.31 L7981543758.32 00000T01701T02502O02n03B03V04K05=05T06=06c07G07m08L08o09S09j0:N0:e0;90;Q0<50<Y0=50=S0=g0>;0>O0?30@40@X0AY0BK0C=S2ws2wd2wc1b1c1P1T1R2hi2lo2PH1t1r2E2S2ws2wd2wc1b1c2HC1P1T1R1E2hi2lo1t1rS2ws2wd2wc1b1c2HC1P1R1E2hi2loS2ws2wd2wc1b1c1P1T1R2hi2lo2PH1t1rS2ws2wd2wc1b1c1P1R1E2hi2loS2ws2wd2wc1b1c1P1T1E2HP2hi2lo1tS2ws2wd2wc1b1P1T1R1ES2ws2wd2wc1b1P1T1R1ES2ws2wd2wc1b1c2HC1P1T1R1E2Rd2HP2hi2lo2PL2Rt1r2E12E21HS2ws2wd2wc1b1c1P1T1R1E2Rd2HP2hi2lo1t2Rt2Rr2E12E21HS2ws2wd2wc1b1P1T1R1E2HPS2ws2wd2wc1b1c1P1T1R1E2hi2lo1t1r2Rr2E12E2S2ws2wd2wc1b1c1P1T1R1E2hi2lo1t1r2Rr2E1S2ws2wd2wc1b1c1P1T1R1E2hi2lo1r2E12E2S2ws2wd2wc1b1c1P1T1R1E2hi2lo1t2Rt1r2E1S2ws2wd2wc1b1c1P1T1E2hi2lo1t2RtS2ws2wd2wc1b1c1P1T1R1E2hi2lo1t2Rt1rS2ws2wd2wc1b1c1P1T1R2hi2lo2PH1t1r2E2S2ws2wd2wc1b1P1T1R1E2HPS2ws2wd2wc1b1c1P1T1R1E2hi2lo1t2E12E2S2ws2wd2wc1b1P1T1R1E2HPS2ws2wd2wc1b1P1T1R1ES2ws2wd2wc1b1P1R1E2hi2loS2ws2wd2wc1b1c1P1T1R1E2hi2lo1r2E12E2S2ws2wd2wc1b1c1P1T1R1E2hi2lo1t2E12E2S2ws2wd2wc1b1c1P1T1R1E2hi2loS2ws2wd2wc1b1c1P1T1R1E2hi2lo1tS2ws2wd2wc1b1P1T1R1ES2ws2wd2wc1b1P1T1R1ES2ws2wd2wc1b1P1T1R1ES2ws2wd2wc1b1c1P1T1R1E2hi2lo1t2E12E2S2ws2wd2wc1b1c1P1T1R2HP2hi2lo2PH1t1r2Et1H2H22HC2PD2Rr2H02H12Rd2ErS2ws2wd2wc1b1c1P1T1R1E2hi2lo1r2E12E2S2ws2wd2wc1b1c1T1R1E2HP2hi2lo2PD1t1r2Rr2Et2Er1H2H02Rd2H22H12HC2PLS2ws2wd2wc1b1c2HC1P1T1R1E2HP2hi2lo2Rt1r2Rr2E12E21HS2ws2wd2wc1b1c1P1T1R1E2Rd2HP2hi2lo1t2Rt2Rr2E12E21H". (* [comment removed for export] *)
Lemma mla_step : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v1 ()) "Pws,(0.&40.)Pwd,(0.&40.)Pwc,(0.&40.)Pb,$1.Pc,$1.P,(2.(3.=R2.)(4.R2.(5.+2.+20.)))P,(2.(3.=R2.)(4.R2.(5.+2.+20.)))P,(6.$1.(7.&40.R5.)(8.R3.))ZP,$1.(9.(7.&40.(:.R8.))R5.)ZT,$1.(;.(<.&20.(=.(7.&40.R7.)(;.R1.+10000000000000000.)))+10000000000000000.)ZR,$1.(<.&20.(=.R1.(7.&40.(>.R9.))))ZE,$1.(=.(;.(=.(?.(10.R2.(7.&40.R9.)))(11.(;.R3.+10000000000000000.)+20.))+10000000000000000.)(?.(10.(;.R1.+10000000000000000.)R2.)))(2.(2.(3.=R1.)(4.R1.(5.+2.+20.)))(2.(6.$1.(=.(12.(13.&40.R2.))(9.(5.+2.+20.)R1.))(=.(=.(12.R;.)(9.(12.R<.)R9.))R8.))(6.$1.(7.&40.(13.&40.(<.&20.R1.)))(8.R1.))))")
(* [comment removed for export] *).
Proof.
  intros ws wd wc b c HB HC WC P T R E.
  assert (Rd : 0 <= w32 wd < 2^32) by (unfold w32; pose proof (Z.mod_pos_bound (bv_unsigned wd) (2^32)); lia).
  assert (Rs : 0 <= w32 ws < 2^32) by (unfold w32; pose proof (Z.mod_pos_bound (bv_unsigned ws) (2^32)); lia).
  assert (HP : 0 <= P /\ P < 2^64 - 2^33 + 2) by (subst P; rewrite zx32_val; nia).
  assert (PM : P mod 18446744073709551616 = P) by (apply Z.mod_small; lia).
  assert (HI : Z.shiftr P 32 = P / 2^32) by (apply Z.shiftr_div_pow2; lia).
  pose proof (Z.div_mod P (2^32) ltac:(lia)) as PD. pose proof (Z.mod_pos_bound P (2^32) ltac:(lia)) as PL.
  assert (PH : 0 <= P / 2^32 < 2^32 - 1) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  set (lo := P mod 2^32) in *. set (hi := P / 2^32) in *.
  assert (ET : T = sxz ((c + lo) mod 2^32)).
  { subst T. rewrite PM. change 18446744073709551616 with (2^64). rewrite swrap32_mod64, WC, sxz_add_mod32 by lia.
    f_equal. rewrite PD. replace (c + (2^32 * hi + lo)) with (c + lo + hi * 2^32) by lia. apply Z.mod_add. lia. }
  pose proof (Z.mod_pos_bound (c + lo) (2^32) ltac:(lia)) as Rt. set (t := (c + lo) mod 2^32) in *.
  assert (ER : R mod 18446744073709551616 = sxz ((t + w32 wd) mod 2^32)).
  { subst R. rewrite ET. change 18446744073709551616 with (2^64). rewrite swrap32_mod64, bv_unsigned_sx32, sxz_add_mod32, sxz_add_mod32_r by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (t + w32 wd) (2^32) ltac:(lia)) as Rr. set (r := (t + w32 wd) mod 2^32) in *.
  assert (E1 : (T <? bv_unsigned wc) = (t <? c)) by (rewrite ET, WC; apply sxz_ltb; lia).
  assert (E2 : (R mod 18446744073709551616 <? T) = (r <? t)) by (rewrite ER, ET; apply sxz_ltb; lia).
  assert (WR : w32 (Z_to_bv 64 R) = r).
  { unfold w32. rewrite Z_to_bv_unsigned. change (bv_wrap 64 R) with (R mod 2^64). change (2^64) with 18446744073709551616. rewrite ER. apply sxz_mod32. lia. }
  assert (Et : t = c + lo - (if c + lo <? 2^32 then 0 else 2^32)).
  { subst t. destruct (Z.ltb_spec (c + lo) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  assert (Er : r = t + w32 wd - (if t + w32 wd <? 2^32 then 0 else 2^32)).
  { subst r. destruct (Z.ltb_spec (t + w32 wd) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  assert (EE : E = Z.b2z (t <? c) + hi + Z.b2z (r <? t) /\ 0 <= E < 2^32).
  { subst E. rewrite E1, E2, PM, HI. change 18446744073709551616 with (2^64).
    rewrite (Z.mod_small (Z.b2z (t <? c) + hi)) by (destruct (t <? c); cbn [Z.b2z]; lia).
    destruct (Z.ltb_spec t c); destruct (Z.ltb_spec r t); destruct (Z.ltb_spec (c + lo) (2^32)); destruct (Z.ltb_spec (t + w32 wd) (2^32)); cbn [Z.b2z]; lia. }
  destruct EE as [EE ER2]. split; [exact ER2|]. split.
  - rewrite WR, EE. subst P. rewrite zx32_val in PD.
    destruct (Z.ltb_spec t c); destruct (Z.ltb_spec r t); destruct (Z.ltb_spec (c + lo) (2^32)); destruct (Z.ltb_spec (t + w32 wd) (2^32)); cbn [Z.b2z]; lia.
  - rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64). rewrite swrap32_mod64. f_equal. apply Z.mod_small. exact ER2.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00B0?L10066802384.14L11353324184.13L11901752722.7 L14847554966.13L14978897786.16L16039676022.7 L16046136858.13L16046136858.8 L21907924320.10L21908260257.12L23400220222.10L26935920655.13L32458126542.16L38717875063.13L42470588107.9 L52514119280.14L53519242448.14L59633169520.1400000?00T00b00o01L01U01j02502E02W02g03403Q03^03k04:04I04XS2wd2wc1c1R1E1rS2wd2wc1c2HC1R1E2Rd1HS2wd2wc1c2HC1ES2wd2wc1c1R1ES2wd2wc1c1R1E1r2Rr2Er2HC1H2H0S2wd2wc1ES2wd2wc1c2HC1R1E2Rd1HS2wd2wc1R1ES2wd2wc1c1R1r2RrS2wd2wc1c1R1E1r2RrS2wd2wc1c1R2Rd1rS2wd2wc1c1R1ES2wd2wc1c2HC1R1E1r2Rr2Er1H2H0S2wd2wc1c1R1ES2wd2wc1c1R1ES2wd2wc1c1R1E1rS2wd2wc1c1R1E1rS2wd2wc1c1R1E1r". (* [comment removed for export] *)
Lemma exc_step : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v1 ()) "Pwd,(0.&40.)Pwc,(0.&40.)Pc,$1.P,(2.(3.=R1.)(4.R1.(5.+2.+20.)))P,(6.$1.(7.&40.R3.)(8.R2.))ZR,$1.(<.&20.(=.(7.&40.(>.R5.))(7.&40.R4.)))ZE,$1.(?.(10.(;.R1.+10000000000000000.)(7.&40.(>.R6.))))(2.(2.(3.=R1.)(4.R1.(5.+2.+20.)))(2.(6.$1.(=.(12.(13.&40.R2.))(9.(5.+2.+20.)R1.))(=.(12.R7.)R5.))(6.$1.(7.&40.(13.&40.R1.))(8.R1.))))")
(* [comment removed for export] *).
Proof.
  intros wd wc c HC WC R E.
  assert (Rd : 0 <= w32 wd < 2^32) by (unfold w32; pose proof (Z.mod_pos_bound (bv_unsigned wd) (2^32)); lia).
  assert (ER : R mod 18446744073709551616 = sxz ((w32 wd + c) mod 2^32)).
  { subst R. change 18446744073709551616 with (2^64). rewrite swrap32_mod64, WC, bv_unsigned_sx32, sxz_add_mod32, sxz_add_mod32_r by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (w32 wd + c) (2^32) ltac:(lia)) as Rr. set (r := (w32 wd + c) mod 2^32) in *.
  assert (E1 : E = Z.b2z (r <? w32 wd)) by (subst E; rewrite ER, bv_unsigned_sx32; fold (w32 wd); rewrite sxz_ltb by lia; reflexivity).
  assert (WR : w32 (Z_to_bv 64 R) = r).
  { unfold w32. rewrite Z_to_bv_unsigned. change (bv_wrap 64 R) with (R mod 2^64). change (2^64) with 18446744073709551616. rewrite ER. apply sxz_mod32. lia. }
  assert (Er : r = w32 wd + c - (if w32 wd + c <? 2^32 then 0 else 2^32)).
  { subst r. destruct (Z.ltb_spec (w32 wd + c) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  rewrite E1, WR. split; [destruct (r <? w32 wd); cbn; lia|]. split.
  - destruct (Z.ltb_spec r (w32 wd)); destruct (Z.ltb_spec (w32 wd + c) (2^32)); cbn [Z.b2z]; lia.
  - rewrite unsigned_lit by (destruct (r <? w32 wd); cbn; lia). unfold sxz. destruct (r <? w32 wd); reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma exc_step_c : forall (wd wc : word) (c : Z), 0 <= c < 2^32 -> bv_unsigned wc = sxz c ->
  let R := bv_swrap 32 (bv_unsigned (sx32 wd) + bv_unsigned wc) in
  let E := Z.b2z (R mod 18446744073709551616 <? bv_unsigned wc) in
  (0 <= E < 2^32) /\ w32 (Z_to_bv 64 R) + 2^32 * E = w32 wd + c /\ bv_unsigned (Z_to_bv 64 E) = sxz E.
Proof.
  intros wd wc c HC WC R E.
  assert (Rd : 0 <= w32 wd < 2^32) by (unfold w32; pose proof (Z.mod_pos_bound (bv_unsigned wd) (2^32)); lia).
  assert (ER : R mod 18446744073709551616 = sxz ((w32 wd + c) mod 2^32)).
  { subst R. change 18446744073709551616 with (2^64). rewrite swrap32_mod64, WC, bv_unsigned_sx32, sxz_add_mod32, sxz_add_mod32_r by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (w32 wd + c) (2^32) ltac:(lia)) as Rr. set (r := (w32 wd + c) mod 2^32) in *.
  assert (E1 : E = Z.b2z (r <? c)) by (subst E; rewrite ER, WC, sxz_ltb by lia; reflexivity).
  assert (WR : w32 (Z_to_bv 64 R) = r).
  { unfold w32. rewrite Z_to_bv_unsigned. change (bv_wrap 64 R) with (R mod 2^64). change (2^64) with 18446744073709551616. rewrite ER. apply sxz_mod32. lia. }
  assert (Er : r = w32 wd + c - (if w32 wd + c <? 2^32 then 0 else 2^32)).
  { subst r. destruct (Z.ltb_spec (w32 wd + c) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  rewrite E1, WR. split; [destruct (r <? c); cbn; lia|]. split.
  - destruct (Z.ltb_spec r c); destruct (Z.ltb_spec (w32 wd + c) (2^32)); cbn [Z.b2z]; lia.
  - rewrite unsigned_lit by (destruct (r <? c); cbn; lia). unfold sxz. destruct (r <? c); reflexivity.
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L10351939541.12L35878420171.1200000<00ES2ds1i2Hi2HlS2ds1i2Hl". (* [comment removed for export] *)
Lemma vi_mul_step : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v1 ()) "Pds,(14.(0.&40.))Pds0,(14.(0.&40.))Pss,(14.(0.&40.))Pi,$1.Pb,$1.Pc,$1.Pc',$1.Pwv,(0.&40.)P,(3.=R5.)P,(15.(16.R6.)(17.(0.&40.)R9.))P,(6.$1.(=.(18.R:.R7.)(9.(5.+2.(9.+20.R7.))R5.))(=.(18.R9.R7.)(9.(18.R8.R7.)R6.)))P,(6.$1.(=.(12.R4.)(9.(5.+2.+20.)R5.))(=.(=.(19.R:.(16.R8.))(9.(19.R9.(16.R8.))R7.))R6.))(6.$1.(=.(18.(1:.(0.&40.)R<.(16.R9.)R5.)(=.R9.+1.))(9.(5.+2.(9.+20.(=.R9.+1.)))R6.))(=.(18.R;.(=.R9.+1.))(9.(18.R:.(=.R9.+1.))R8.)))")
(* [comment removed for export] *).
Proof.
  intros ds ds0 ss i b c c' wv Hi Hl INV ST. rewrite !lval_succ, pow2_32_succ by lia.
  rewrite lval_upd_ge by lia. rewrite limb32_upd_same by exact Hl. set (M := 2 ^ (32 * i)) in *. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L10351939541.11L35878420171.1100000<00ES2ds1i2Hi2HlS2ds1i2Hl". (* [comment removed for export] *)
Lemma vi_exc_step : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v1 ()) "Pds,(14.(0.&40.))Pds0,(14.(0.&40.))Pi,$1.Pc,$1.Pc',$1.PK,$1.Pwv,(0.&40.)P,(3.=R5.)P,(15.(16.R6.)(17.(0.&40.)R8.))P,(6.$1.(=.(18.R9.R7.)(9.(5.+2.(9.+20.R7.))R6.))(=.(18.R8.R7.)R4.))P,(6.$1.(=.(12.R4.)(9.(5.+2.+20.)R6.))(=.(19.R9.(16.R8.))R7.))(6.$1.(=.(18.(1:.(0.&40.)R;.(16.R9.)R5.)(=.R9.+1.))(9.(5.+2.(9.+20.(=.R9.+1.)))R7.))(=.(18.R:.(=.R9.+1.))R6.))")
(* [comment removed for export] *).
Proof.
  intros ds ds0 i c c' K wv Hi Hl INV ST. rewrite !lval_succ, pow2_32_succ by lia.
  rewrite lval_upd_ge by lia. rewrite limb32_upd_same by exact Hl. set (M := 2 ^ (32 * i)) in *. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac absc_tac ws wd wc b c HB HC WC cN wcN wvN RN VN WCN :=
  let K := fresh "K" in
  pose proof (mla_step ws wd wc b c HB HC WC) as K; cbv zeta in K;
  lazymatch type of K with _ /\ w32 (Z_to_bv 64 ?r) + _ = _ /\ bv_unsigned (Z_to_bv 64 (bv_swrap 32 ?e)) = _ =>
    set (cN := e) in *; clearbody cN; set (wcN := Z_to_bv 64 (bv_swrap 32 cN)) in *; clearbody wcN;
    set (wvN := Z_to_bv 64 r) in *; clearbody wvN end;
  destruct K as (RN & VN & WCN).

(* [comment removed for export] *)
Ltac absx_tac wd wc c HC WC cN wcN wvN RN VN WCN :=
  let K := fresh "K" in
  pose proof (exc_step_c wd wc c HC WC) as K; cbv zeta in K;
  lazymatch type of K with _ /\ w32 (Z_to_bv 64 ?r) + _ = _ /\ bv_unsigned (Z_to_bv 64 ?e) = _ =>
    set (cN := e) in *; clearbody cN; set (wcN := Z_to_bv 64 cN) in *; clearbody wcN;
    set (wvN := Z_to_bv 64 r) in *; clearbody wvN end;
  destruct K as (RN & VN & WCN).

(* [comment removed for export] *)
Ltac rdv_tac H i w V :=
  let N := fresh "N" in let RD := fresh "RD" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia];
      pose proof (u32arr_read sg mm A l i w _ H N ltac:(lia) ltac:(f_equal; lia)) as RD;
      pose proof (limb32_nth_error _ _ _ N) as V
  | bytes_at ?sg ?mm ?A (u32s ?l) =>
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia];
      pose proof (u32ro_read sg mm A l i w _ H N ltac:(lia) ltac:(f_equal; lia)) as RD;
      pose proof (limb32_nth_error _ _ _ N) as V
  end;
  zstep; clear RD N.

(* [comment removed for export] *)
Ltac rdd_tac H FS i w U :=
  let N := fresh "N" in let RD := fresh "RD" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia];
      pose proof (u32arr_read sg mm A l i w _ H N ltac:(lia) ltac:(f_equal; lia)) as RD;
      pose proof (fun HLE : (_ <= _)%nat => same_from_limb32 _ _ _ _ _ FS HLE N) as U; specialize (U ltac:(lia))
  end;
  zstep; clear RD N.

(* [comment removed for export] *)
Ltac wrv_tac H L L1 i :=
  let SOK := fresh "SOK" in let H' := fresh "HX'" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      pose proof (u32arr_store_ok sg mm A l i _ H ltac:(lia) ltac:(f_equal; lia)) as SOK;
      zstep;
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
        pose proof (u32arr_write sg mm A l i v H ltac:(lia)) as H';
        lazymatch type of L with _ = ?r =>
          assert (L1 : Z.of_nat (length (upd l (Z.to_nat i) v)) = r) by (rewrite upd_length; exact L) end;
        store_done; try clear H; rename H' into H
      end
  end.

Tactic Notation "absc" constr(ws) constr(wd) constr(wc) constr(b) constr(c) constr(HB) constr(HC) constr(WC)
    ident(cN) ident(wcN) ident(wvN) ident(RN) ident(VN) ident(WCN) := absc_tac ws wd wc b c HB HC WC cN wcN wvN RN VN WCN.
Tactic Notation "absx" constr(wd) constr(wc) constr(c) constr(HC) constr(WC)
    ident(cN) ident(wcN) ident(wvN) ident(RN) ident(VN) ident(WCN) := absx_tac wd wc c HC WC cN wcN wvN RN VN WCN.
Tactic Notation "rdv" constr(H) constr(i) ident(w) ident(V) := rdv_tac H i w V.
Tactic Notation "rdd" constr(H) constr(FS) constr(i) ident(w) ident(U) := rdd_tac H FS i w U.
Tactic Notation "wrv" constr(H) constr(L) ident(L1) constr(i) := wrv_tac H L L1 i.
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L10357916367.30L10357916367.34L32394982834.34L59314841581.29L59314841581.3300000D00[01Q02D02gS2sl3ds01l1k1i2Hk2HiS2sl3ds02ss1l1k1i2Hk2HiS2sp1D2dl1S2ld2ls2lo3ds02ss1l1k1i3DIS2LS3Hdl2LO3SSX2HkS2dl2sl2ld2ls3ds01l1k1i1L2L02LS3Hdl3Hsl3Hsd2Hk2Hi1NS2sl2ls3ds02ss1l1k1i2LS3Hsl2Hk2Hi1N". (* [comment removed for export] *)
Lemma s_read_fact : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v1 ()) "Psegs,(14.$1;.)Pm,P,(0.&40.)(1<.(0.&8.))Pmm,P,(0.&40.)(1<.(0.&8.))Psp,(0.&40.)PD,$1.Pdl,$1.PS,$1.Psl,$1.Pld,$1.Pls,$1.Plo,$1.Pds0,(14.(0.&40.))Pss,(14.(0.&40.))Pl,(14.(0.&40.))Pk,$1=.Pi,$1.P,(1>.(2.(6.$1.R:.R<.)(6.(14.(0.&40.))R4.R5.))(2.(1?.R10.R?.R:.(20.R4.))(1>.(3.(=.R:.(9.+4.R7.))R<.)(3.(=.R<.(9.+4.R8.))R:.))))P,(21.(22.(23.$1.$1.)(24.$1.$1.R=.(=.R=.(9.+4.R<.)))(22.(23.$1.$1.)(24.$1.$1.(25.(7.&40.R>.)+30.)(7.&40.R>.))(26.(23.$1.$1.))))R10.R?.)P,(27.R12.R11.R10.)P,(28.R13.R11.R?.R6.)P,(29.(0.&40.)R6.R7.R9.)P,(6.$1.(2:.(17.(0.&40.)R8.))R=.)P,(6.$1.(2:.(17.(0.&40.)R;.))R>.)P,(6.$1.(2:.(17.(0.&40.)R;.))R>.)P,(3.R13.R10.)P,(3.R12.R10.)P,(3.R13.R15.)P,(3.R11.(25.(7.&40.R18.)+30.))P,(1>.(3.(=.R16.(9.+4.R13.))R12.)(3.(7.&40.R19.)R16.))P,(2;.R?.(16.R>.))P,(2.(3.=R?.)(4.R?.R17.))(2<.(0.&40.)Lw,(0.&40.)(2.(6.(1<.(0.&40.))(2=.(0.&40.)R14.(16.R11.))(2>.(0.&40.)R1.))(6.(1<.(14.(0.&8.)))(2?.R20.R1>.(30.(=.R1:.(9.+4.R11.)))#4.)(2>.(14.(0.&8.))(31.R1.)))))")
(* [comment removed for export] *).
Proof.
  intros segs m mm sp D dl S sl ld ls lo ds0 ss l k i AS MU WM HX FS L L0 LS Hdl Hsl Hsd LO SSX Hk Hi.
  destruct AS as [[ES ESS]|[HS DIS]].
  - subst S ss. destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia].
    exists w. split; [rewrite <- (FS _ Hk); exact N|]. eapply u32arr_read; [exact HX| exact N| lia| reflexivity].
  - destruct (nth_error ss (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia].
    exists w. split; [reflexivity|]. eapply u32ro_read; [| exact N| lia| reflexivity].
    eapply bytes_at_transport; [exact HS| exact MU|]. rewrite u32s_length. cbn. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rdsf_tac AS MU WM HX FS LX L0 LS LO SSX sl i w U :=
  let N := fresh "N" in let RD := fresh "RD" in
  lazymatch type of LO with ?lo <= _ =>
  destruct (s_read_fact _ _ _ _ _ _ _ sl _ _ lo _ _ _ _ i AS MU WM HX FS LX L0 LS ltac:(lia) ltac:(lia) ltac:(lia) LO SSX ltac:(lia) ltac:(lia)) as (w & N & RD) end;
  pose proof (limb32_nth_error _ _ _ N) as U; zstep; clear RD N.
Tactic Notation "rdsf" constr(AS) constr(MU) constr(WM) constr(HX) constr(FS) constr(LX) constr(L0) constr(LS) constr(LO) constr(SSX) constr(sl) constr(i) ident(w) ident(U) :=
  rdsf_tac AS MU WM HX FS LX L0 LS LO SSX sl i w U.

(* [comment removed for export] *)
Ltac adv_tac ds1 LX1 FS1 VI Ud Us V VI1 inext :=
  lazymatch type of V with w32 ?wv + 2 ^ 32 * ?c' = _ =>
  lazymatch type of VI with lval ?l ?i + _ * ?c = lval ?l0 _ + lval ?lss _ * ?bb =>
    assert (VI1 : lval (upd l (Z.to_nat i) wv) (i + 1) + 2^(32*(i + 1)) * c' = lval l0 (i + 1) + lval lss (i + 1) * bb)
      by (rewrite <- Ud, <- Us in V; eapply vi_mul_step; [lia| lia| exact VI| exact V]);
    replace (i + 1) with inext in VI1 by lia;
    replace (Datatypes.S (Z.to_nat i)) with (Z.to_nat inext) in FS1 by lia;
    set (ds1 := upd l (Z.to_nat i) wv) in *; clearbody ds1
  end end.
Tactic Notation "adv" ident(ds1) constr(LX1) constr(FS1) constr(VI) constr(Ud) constr(Us) constr(V) ident(VI1) constr(inext) :=
  adv_tac ds1 LX1 FS1 VI Ud Us V VI1 inext.

Lemma Z_to_bv_eqm : forall x y, x mod 18446744073709551616 = y mod 18446744073709551616 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. rewrite <- (Z_to_bv_mod64 x), <- (Z_to_bv_mod64 y). change (2^64) with 18446744073709551616. rewrite H. reflexivity. Qed.

Ltac zb_split K := repeat match type of K with
  | context [Z.b2z (?x <? ?y)] => revert K; destruct (Z.ltb_spec x y); cbn [Z.b2z]; intro K
  | context [Z.b2z (?x <=? ?y)] => revert K; destruct (Z.leb_spec x y); cbn [Z.b2z]; intro K
  | context [Z.b2z (?x =? ?y)] => revert K; destruct (Z.eqb_spec x y); cbn [Z.b2z]; intro K
  end.
Ltac chk := lazymatch goal with
  | |- _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
    let K := fresh "K" in if_cases K;
    [ zify_cond K; rewrite ?unsigned_lit, ?signed_lit_small in K by lia;
      rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2, ?land_3_mod' in K by lia; zb_split K;
      exfalso; lia | clear K ]
  | |- _ => idtac
  end.
Ltac bveq := first [ reflexivity | f_equal; rewrite ?land_3_mod', ?land_7_mod'; lia
                   | apply Z_to_bv_eqm; rewrite ?Z.add_mod_idemp_l by lia; f_equal; lia
                   | apply Z_to_bv_eqm; rewrite ?land_3_mod', ?land_7_mod'; lia ].

(* [comment removed for export] *)
Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (D dl S sl ld ls lo b : Z) (ds0 ss : list word).
  Hypothesis Hdl : 0 <= dl <= 10000.
  Hypothesis Hsl : 0 <= sl <= dl.
  Hypothesis Ln : dl <= ld /\ sl <= ls.
  Hypothesis L0 : Z.of_nat (length ds0) = ld.
  Hypothesis LS : Z.of_nat (length ss) = ls.
  Hypothesis DB : 0 < D /\ D + 4 * ld < 2^64.
  Hypothesis SB : 0 <= S /\ S + 4 * ls < 2^64.
  Hypothesis ALD : D mod 4 = 0.
  Hypothesis ALS : S mod 4 = 0.
  Hypothesis NZS : sl = 0 \/ 0 < S.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 48.
  Hypothesis SX : D + 4 * ld <= lo \/ bv_unsigned sp <= D.
  Hypothesis SSX : S + 4 * ls <= lo \/ bv_unsigned sp <= S.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis HB : 0 <= b < 2^32.

  Notation POST := (mpi_core_mla_vpost usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dl ds0 sl ss b lo m).
  Notation W := [(D, D + 4 * dl); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells usegs mm (bv_unsigned sp + -48) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0]).
  (* [comment removed for export] *)
  Notation SFACT0 := ((S = D /\ ss = ds0) \/ (bytes_at usegs m S (u32s ss) /\ (S + 4 * ls <= D \/ D + 4 * ld <= S))).
  Notation DINV mm ds := (u32arr usegs mm D ds /\ Z.of_nat (length ds) = ld
                          /\ munch W m mm /\ wmono usegs m mm /\ mem_inv usegs mm /\ stk usegs mm lo (bv_unsigned sp + -48)).
  (* [comment removed for export] *)
  Notation VINV ds i k c wc := (same_from (Z.to_nat i) ds ds0 /\ 0 <= c < 2^32 /\ bv_unsigned wc = sxz c
                                /\ lval ds i + 2^(32*i) * c = lval ds0 i + lval ss k * b).
  Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="S L0 LO"] Lemma vtail_walk : forall (ds : list word) (mm : mem) (c : Z)
      (wc xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 : word),
    DINV mm ds -> FRAME mm -> VINV ds dl sl c wc ->
    evt usegs POST (MS (mkR ra SP gp tp xt0 xt1 xt2 xs0 xs1 wc xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5
                          s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x23cec) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. (intros dd_H; ddestruct dd_H as (HX & LX & MU & WM & MI & ST); intros FR dd_H; ddestruct dd_H as (FS & HC & WC & VI)).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold mpi_core_mla_vpost. deexists 15. dexists mm, ds, c.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HX|]. split; [clear - LX L0; lia|].
    split; [apply same_from_skipn; [exact FS| clear - LX L0; lia]|]. split; [exact HC|]. split; [exact VI| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Hdl Hsl Ln L0 LS DB SB ALD ALS NZS SPR LO SX SSX RA HB"] Lemma vexcess_walk : forall (k : nat) (i : Z) (ds : list word) (mm : mem) (c : Z) (wc : word)
      (xt0 xt1 xt2 xs0 xs1 xa3 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 : word) (wn wf wz wp : word),
    Z.to_nat (dl - i) = k -> sl <= i < dl ->
    wn = Z_to_bv 64 (i - dl) -> wf = Z_to_bv 64 (-5) -> wz = Z_to_bv 64 0 -> wp = Z_to_bv 64 (D + 4 * i) ->
    DINV mm ds -> FRAME mm -> VINV ds i sl c wc ->
    evt usegs POST (MS (mkR ra SP gp tp xt0 xt1 xt2 xs0 xs1 wc wn wf xa3 wz xa5 xa6 xa7 xs2 xs3 xs4 xs5
                          s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 wp) F (Z_to_bv 64 0x23cc4) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; (intros i ds mm c wc xt0 xt1 xt2 xs0 xs1 xa3 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 wn wf wz wp Hk Hi -> -> -> -> dd_H;
      ddestruct dd_H as (HX & LX & MU & WM & MI & ST); intros FR dd_H; ddestruct dd_H as (FS & HC & WC & VI)); [lia|].
    zstep. chk. zstep. chk.
    rdd HX FS (i + 0) w U0. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    wrv HX LX LX1 (i + 0). (* [comment removed for export] *)
    zstep. chk. (* [comment removed for export] *) zstep. (* [comment removed for export] *) zstep. zstep.
    absx w wc c HC WC c1 wc1 wv1 R1 V1 WC1.
    match goal with MUx : munch _ m ?mx, WMx : wmono _ m ?mx, MIx : mem_inv _ ?mx, STx : stk _ ?mx _ _ |- _ =>
      rename MUx into MU1; rename WMx into WM1; rename MIx into MI1; rename STx into ST1 end.
    assert (FS1 : same_from (Z.to_nat (i + 1)) (upd ds (Z.to_nat (i + 0)) wv1) ds0).
    { replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat (i + 0))) by lia. apply same_from_upd. replace (i + 0) with i by lia. exact FS. }
    assert (VI1 : lval (upd ds (Z.to_nat (i + 0)) wv1) (i + 1) + 2^(32*(i + 1)) * c1 = lval ds0 (i + 1) + lval ss sl * b).
    { replace (i + 0) with i in U0 |- * by lia. eapply vi_exc_step; [lia| lia| exact VI| rewrite U0; exact V1]. }
    zstep. (* [comment removed for export] *)
    if_cases Kl; zify_cond Kl; rewrite ?Z.add_mod_idemp_l in Kl by lia.
    - eapply (IH (i + 1)); [lia | lia | bveq | reflexivity | reflexivity | bveq
        | exact (conj HX (conj LX1 (conj MU1 (conj WM1 (conj MI1 ST1))))) | exact FR| exact (conj FS1 (conj R1 (conj WC1 VI1)))].
    - eapply vtail_walk; [exact (conj HX (conj LX1 (conj MU1 (conj WM1 (conj MI1 ST1))))) | exact FR|]. replace dl with (i + 1) by lia. exact (conj FS1 (conj R1 (conj WC1 VI1))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Hdl Hsl Ln L0 LS DB SB ALD ALS NZS SPR LO SX SSX RA HB"] Lemma vexcess_entry : forall (ds : list word) (mm : mem) (c : Z) (wc : word)
      (xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa5 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 : word) (wa1 wa4 wa6 wp : word),
    wa1 = Z_to_bv 64 dl -> wa4 = Z_to_bv 64 (D + 4 * sl) -> wa6 = Z_to_bv 64 sl -> wp = Z_to_bv 64 (D + 4 * sl) -> sl < dl ->
    DINV mm ds -> FRAME mm -> VINV ds sl sl c wc ->
    evt usegs POST (MS (mkR ra SP gp tp xt0 xt1 xt2 xs0 xs1 wc wa1 xa2 xa3 wa4 xa5 wa6 xa7 xs2 xs3 xs4 xs5
                          s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 wp) F (Z_to_bv 64 0x23cb8) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until wp. intros -> -> -> -> Hlt DI FR VI.
    zstep. zstep. zstep.
    eapply (vexcess_walk (Z.to_nat (dl - sl)) sl); [lia | lia | bveq | bveq | bveq | bveq | exact DI | exact FR| exact VI].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Hdl Hsl Ln L0 LS DB SB ALD ALS NZS SPR LO SX SSX RA HB"] Lemma vjoin_walk : forall (ds : list word) (mm : mem) (c : Z) (wc : word)
      (xt0 xt1 xt2 xs0 xs1 xa2 xa7 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 : word) (wa1 wa3 wa4 wpd wa6 : word),
    wa1 = Z_to_bv 64 dl -> wa3 = Z_to_bv 64 sl -> wa4 = Z_to_bv 64 (D + 4 * sl) -> wpd = Z_to_bv 64 (D + 4 * sl) -> wa6 = Z_to_bv 64 sl ->
    DINV mm ds -> FRAME mm -> VINV ds sl sl c wc ->
    evt usegs POST (MS (mkR ra SP gp tp xt0 xt1 xt2 xs0 xs1 wc wa1 xa2 wa3 wa4 wpd wa6 xa7 xs2 xs3 xs4 xs5
                          s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x23cb0) fc None mm (seg_rom usegs)).
  Proof.
    intros until wa6. intros -> -> -> -> -> DI FR VI.
    zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    all: first [ eapply vexcess_entry; [bveq | bveq | bveq | bveq | lia | exact DI | exact FR| exact VI]
               | eapply vtail_walk; [exact DI | exact FR|]; replace dl with sl by lia; exact VI ].
  Qed.

  Section WithB.
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    #[using="Hdl Hsl Ln L0 LS DB SB ALD ALS NZS SPR LO SX SSX RA HB"] Lemma vx1_walk : forall (k : nat) (i : Z) (ds : list word) (mm : mem) (c : Z) (wc : word)
        (xs0 xs1 xs2 xs3 xs4 xs5 xt6 : word) (wt0 wn wt2 wa1 wps wa3 wa4 wpd wa6 wa7 wt3 wt4 wt5 : word),
      Z.to_nat (sl - i) = k -> 0 <= i < sl ->
      wt0 = Z_to_bv 64 0 -> wn = Z_to_bv 64 (sl - i) -> wt2 = Z_to_bv 64 0 -> wa1 = Z_to_bv 64 dl ->
      wps = Z_to_bv 64 (S + 4 * i) -> wa3 = Z_to_bv 64 sl -> wa4 = Z_to_bv 64 (D + 4 * i) -> wpd = Z_to_bv 64 (D + 4 * i) ->
      wa6 = Z_to_bv 64 sl -> wa7 = Z_to_bv 64 b -> wt3 = Z_to_bv 64 5 -> wt4 = Z_to_bv 64 (-5) -> wt5 = Z_to_bv 64 (S + 4 * i) ->
      DINV mm ds -> SFACT0 -> FRAME mm -> VINV ds i i c wc ->
      evt usegs POST (MS (mkR ra SP gp tp wt0 wn wt2 xs0 xs1 wc wa1 wps wa3 wa4 wpd wa6 wa7 xs2 xs3 xs4 xs5
                            s6 s7 s8 s9 s10 s11 wt3 wt4 wt5 xt6) F (Z_to_bv 64 0x23c38) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; (intros i ds mm c wc xs0 xs1 xs2 xs3 xs4 xs5 xt6 wt0 wn wt2 wa1 wps wa3 wa4 wpd wa6 wa7 wt3 wt4 wt5 Hk Hi
        -> -> -> -> -> -> -> -> -> -> -> -> -> dd_H; ddestruct dd_H as (HX & LX & MU & WM & MI & ST); intros AS FR dd_H; ddestruct dd_H as (FS & HC & WC & VI)); [lia|].
      zstep. zstep. chk. zstep. chk. zstep. chk. zstep. chk. zstep. chk. zstep. chk.
      rdsf AS MU WM HX FS LX L0 LS LO SSX sl (i + 0) w Us. zstep. zstep. rdd HX FS (i + 0) w0 Ud.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      wrv HX LX LX1 (i + 0). zstep.
      absc w w0 wc b c HB HC WC c1 wc1 wv1 R1 V1 WC1.
      zstep. zstep.
      pose proof (same_from_upd _ _ _ wv1 FS) as FS1. replace (i + 0) with i in * by lia.
      adv ds1 LX1 FS1 VI Ud Us V1 VI1 (i + 1).
      match goal with MUx : munch _ m ?mx, WMx : wmono _ m ?mx, MIx : mem_inv _ ?mx, STx : stk _ ?mx _ _ |- _ =>
        rename MUx into MU1; rename WMx into WM1; rename MIx into MI1; rename STx into ST1 end.
      zstep. if_cases Kl; zify_cond Kl.
      - eapply (IH (i + 1)); [lia | lia | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq
          | exact (conj HX (conj LX1 (conj MU1 (conj WM1 (conj MI1 ST1))))) | exact AS | exact FR| exact (conj FS1 (conj R1 (conj WC1 VI1)))].
      - replace (i + 1) with sl in FS1, VI1 by lia.
        zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
        all: first [ eapply vexcess_entry; [bveq | bveq | bveq | bveq | lia | exact (conj HX (conj LX1 (conj MU1 (conj WM1 (conj MI1 ST1))))) | exact FR
                                         | exact (conj FS1 (conj R1 (conj WC1 VI1)))]
                   | zstep; eapply vtail_walk; [exact (conj HX (conj LX1 (conj MU1 (conj WM1 (conj MI1 ST1))))) | exact FR|];
                     replace dl with sl by lia; exact (conj FS1 (conj R1 (conj WC1 VI1))) ].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    #[using="Hdl Hsl Ln L0 LS DB SB ALD ALS NZS SPR LO SX SSX RA HB"] Lemma vx1_entry : forall (i0 : Z) (ds : list word) (mm : mem) (c : Z) (wc : word)
        (xt2 xs0 xs1 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 : word) (wt0 wn wa1 wps wa3 wa4 wpd wa6 wa7 : word),
      0 <= i0 < sl ->
      wt0 = Z_to_bv 64 (S + 4 * i0) -> wn = Z_to_bv 64 (sl - i0) -> wa1 = Z_to_bv 64 dl -> wps = Z_to_bv 64 (S + 4 * i0) ->
      wa3 = Z_to_bv 64 sl -> wa4 = Z_to_bv 64 (D + 4 * i0) -> wpd = Z_to_bv 64 (D + 4 * i0) -> wa6 = Z_to_bv 64 sl ->
      Z.shiftr (bv_unsigned wa7) 32 = b ->
      DINV mm ds -> SFACT0 -> FRAME mm -> VINV ds i0 i0 c wc ->
      evt usegs POST (MS (mkR ra SP gp tp wt0 wn xt2 xs0 xs1 wc wa1 wps wa3 wa4 wpd wa6 wa7 xs2 xs3 xs4 xs5
                            s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x23c1c) fc None mm (seg_rom usegs)).
    Proof.
      intros until wa7. intros Hi0 -> -> -> -> -> -> -> -> HA7 DI AS FR VI.
      zstep. rewrite HA7. zstep. zstep. zstep. zstep. zstep. zstep.
      eapply (vx1_walk (Z.to_nat (sl - i0)) i0); [lia | lia | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq
        | exact DI | exact AS | exact FR| exact VI].
    Qed.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    #[using="Hdl Hsl Ln L0 LS DB SB ALD ALS NZS SPR LO SX SSX RA HB"] Lemma vafter_x8_walk : forall (i0 : Z) (ds : list word) (mm : mem) (c : Z) (wc : word)
        (xt1 xt2 xa2 xa5 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 : word) (wt0 wpd wps wa1 wa3 wa4 wa6 wa7 : word),
      8 <= i0 <= sl -> i0 = 8 * (sl / 8) ->
      wt0 = Z_to_bv 64 (S + 4 * i0) -> wpd = Z_to_bv 64 (D + 4 * i0 - 32) -> wps = Z_to_bv 64 (S + 4 * i0 - 32) ->
      wa1 = Z_to_bv 64 dl -> wa3 = Z_to_bv 64 sl -> wa4 = Z_to_bv 64 (D + 4 * i0) -> wa6 = Z_to_bv 64 sl ->
      Z.shiftr (bv_unsigned wa7) 32 = b ->
      DINV mm ds -> SFACT0 -> FRAME mm -> VINV ds i0 i0 c wc ->
      evt usegs POST (MS (mkR ra SP gp tp wt0 xt1 xt2 wpd wps wc wa1 xa2 wa3 wa4 xa5 wa6 wa7 xs2 xs3 xs4 xs5
                            s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x23c0c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
    Proof.
      intros until wa7. intros Hi0 Hr -> -> -> -> -> -> -> HA7 DI AS FR VI.
      zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1; rewrite ?land_7_mod' in K1.
      - assert (E0 : i0 = sl) by lia. clear Hr. subst i0.
        eapply vjoin_walk; [bveq | bveq | bveq | bveq | bveq | exact DI | exact FR| exact VI].
      - eapply (vx1_entry i0); [lia | bveq | bveq | bveq | bveq | bveq | bveq | bveq | bveq | exact HA7 | exact DI | exact AS | exact FR| exact VI].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End WithB.
End Walk.
