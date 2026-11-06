(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_mpi_core_mla P_mpi_mul_int_W.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_mla_v1 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.MpiCoreAux.sxz"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Lib.Mem.zx32"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.Mem.sx32"; "Stdlib.ZArith.BinInt.Z.b2z"; "Stdlib.ZArith.BinInt.Z.ltb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.Lib.MpiCoreAux.w32"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "OSSVerify.KrLib.Lib.MpiCoreAux.limb32"; "OSSVerify.KrLib.Lib.Arr.upd"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "OSSVerify.KrLib.Lib.MpiCoreAux.same_from"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Peano.le"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "OSSVerify.KrLib.Lib.Mem.wa"; "OSSVerify.KrLib.Lib.Mem.le4"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.P.P_mpi_mul_int_W.mpi_core_mla_vpost"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].


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
  pose proof (exc_step wd wc c HC WC) as K; cbv zeta in K;
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

(* [comment removed for export] *)
Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (D dl S sl ld ls lo b : Z) (ds0 ss : list word) (junk : list byte).
  Hypothesis Hdl : 0 <= dl <= 10000.
  Hypothesis Hsl : 0 <= sl <= dl.
  Hypothesis Ln : dl <= ld /\ sl <= ls.
  Hypothesis L0 : Z.of_nat (length ds0) = ld.
  Hypothesis LS : Z.of_nat (length ss) = ls.
  Hypothesis DB : 0 < D /\ D + 4 * ld <= 2^64.
  Hypothesis SB : 0 <= S /\ S + 4 * ls <= 2^64.
  Hypothesis NZS : sl = 0 \/ 0 < S.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 48.
  Hypothesis SX : D + 4 * ld <= lo \/ bv_unsigned sp <= D.
  Hypothesis SSX : S + 4 * ls <= lo \/ bv_unsigned sp <= S.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis HB : 0 <= b < 2^32.

  Notation POST := (mpi_core_mla_vpost psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dl ds0 sl ss b lo m).
  Notation W := [(D, D + 4 * dl); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells psegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 s0]).
  (* [comment removed for export] *)
  Notation SFACT0 := ((S = D /\ ss = ds0) \/ (bytes_at psegs m S (u32s ss) /\ (S + 4 * ls <= D \/ D + 4 * ld <= S))).
  Notation DINV mm ds := (u32arr psegs mm D ds /\ Z.of_nat (length ds) = ld
                          /\ munch W m mm /\ wmono psegs m mm /\ mem_inv psegs mm /\ stk psegs mm lo (bv_unsigned sp + -16)).
  (* [comment removed for export] *)
  Notation VINV ds i k c wc := (same_from (Z.to_nat i) ds ds0 /\ 0 <= c < 2^32 /\ bv_unsigned wc = sxz c
                                /\ lval ds i + 2^(32*i) * c = lval ds0 i + lval ss k * b).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L31399144472.73L32049487064.72L3830162331.74 L43172907151.5 00000D00X01201CS2ra2sp2dl3ds02ss2dsS2ra2sp2dl3ds02ss2dsS2ra2sp2dl2lo3ds02ss2LO2dsS2ld3ds02L02ds2LX". (* [comment removed for export] *)
  #[using="L0 LO"] Lemma vtail_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v1 ()) "Pds,(14.(0.&40.))Pmm,P,(0.&40.)(1<.(0.&8.))Pc,$1.Pwc,(0.&40.)Pxt0,(0.&40.)Pxt1,(0.&40.)Pxt2,(0.&40.)Pxs0,(0.&40.)Pxa1,(0.&40.)Pxa2,(0.&40.)Pxa3,(0.&40.)Pxa4,(0.&40.)Pxa5,(0.&40.)Pxa6,(0.&40.)Pxa7,(0.&40.)Pxt3,(0.&40.)Pxt4,(0.&40.)Pxt5,(0.&40.)Pxt6,(0.&40.)P,(2.(28.$32.R12.VD,R13.)(2.(6.$1.(2:.(17.(0.&40.)R13.))Vld,)(2.(21.(22.(23.$1.$1.)(24.$1.$1.VD,(=.VD,(9.+4.Vdl,)))(22.(23.$1.$1.)(24.$1.$1.(25.(7.&40.Vsp,)+30.)(7.&40.Vsp,))(26.(23.$1.$1.))))Vm,R12.)(2.(27.$32.Vm,R12.)(2.(33.$32.R12.)(34.$32.R12.Vlo,(=.(7.&40.Vsp,)-10.)))))))P,(35.$32.R13.(=.(7.&40.Vsp,)-10.)(22.$36.(37.#8.Vjunk,)(22.$36.(38.Vs0,)(26.$36.))))P,(2.(29.(0.&40.)(16.Vdl,)R15.Vds0,)(2.(2.(3.=R13.)(4.R13.(5.+2.+20.)))(2.(6.$1.(7.&40.R12.)(8.R13.))(6.$1.(=.(18.R15.Vdl,)(9.(5.+2.(9.+20.Vdl,))R13.))(=.(18.Vds0,Vdl,)(9.(18.Vss,Vsl,)Vb,))))))(39.$32.(3:.$32.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VD,Vdl,Vds0,Vsl,Vss,Vb,Vlo,Vm,)(3;.(3<.Vra,(13.&40.(=.(7.&40.Vsp,)-10.))Vgp,Vtp,R12.R11.R10.R?.Vs1,R13.R>.R=.R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(13.&40.+22<30.)Vfc,(3=.(0.&40.))R15.(3>.$32.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. (intros dd_H; ddestruct dd_H as (HX & LX & MU & WM & MI & ST); intros FR dd_H; ddestruct dd_H as (FS & HC & WC & VI)).
    zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold mpi_core_mla_vpost. deexists 15. dexists mm, ds, c.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HX|]. split; [clear - LX L0; lia|].
    split; [apply same_from_skipn; [exact FS| clear - LX L0; lia]|]. split; [exact HC|]. split; [exact VI| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L10353856370.87L10500443539.89L10898104775.89L13434842651.84L14002381941.79L14004442312.80L14946181137.77L18045970546.82L18045970546.83L22798223438.87L22798467150.86L24050514656.83L24101615269.81L24101615269.82L25088156662.81L29295750739.89L3447022552.87 L35796633558.75L36681779008.89L45593372576.79L50590728892.82L50590729146.80L53315723119.81L59314841581.78L6300383024.89 L67717333530.89L68091861558.8600000V01f03:04804f05T05U06\07c08?08[08\09609P09n0:]0;O0=f0>P0?20@:0AB0B@0C00CW0D50D[S2ra2dl2sl3ds02ss3Hsl1k1i2ds2Hk2Hi3wv1S2ra2sp1D2dl1S2sl2ld2ls2lo3ds02ss3Hsl2Ln2LS2DB2SB3NZS3SPR2LO2SX1k1i2ds2Hk2Hi3wv1S2ra2sp1D2dl1S2sl2ld2ls2lo3ds02ss3Hsl2Ln2LS2DB2SB3NZS3SPR2LO2SX1k1i2ds2Hk2Hi3wv13LX1S2ra2sp1D2dl2sl2ld2ls2lo3ds02ss3Hsl2Ln2LO2SX1k1i2ds2wc2Hk2Hi1wS2ra2dl2sl2ld2ls3ds02ss3Hsl2Ln1k1i2ds2Hk2Hi2LXS2ra2dl2sl2ld2ls3ds02ss3Hsl2Ln1k1i2ds2Hk2Hi2LXFS2ra2sp1D2dl1S2sl2ld2ls2lo3ds02ss3Hsl2LS2DB2SB3NZS2LO1k1i2ds2wc2Hk2Hi1wS2ra2sp1D2dl1S2sl2ld2ls2lo3ds02ss3Hsl2LS2DB2SB3NZS2LO1k1i2ds2wc2Hk2Hi1wS2ra2dl3ds02ss1k1i2ds2Hk3wv1S2ra2dl3ds02ss1k1i2ds2Hk3wv1FS2ra1D2dl3ds02ss1k1i2ds2HkS2ra1D2dl3ds02ss1k1i2ds2HkS2ra2dl2sl3ds02ss1k1i2ds2Hk2HiS2ra1D2dl2sl3ds02ss3Hdl3Hsl1k1i2ds2Hk2Hi3wv12KlS2ra2dl2sl2ld2ls3ds02ss3Hsl2Ln1k1i2ds2Hk2Hi2LX3wv1S2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1D2dl2sl2lo1b3ds02ss3Hdl1i2ds2mm2wc3xt03xt13xt23xs03xa23xa43xa53xa63xa73xt33xt43xt53xt62Hk2HiS2ra2dl2sl3ds02ss3Hdl3Hsl1k1i2ds2Hk2Hi3wv1S2ra2dl2sl3ds02ss3Hsl1k1i2ds2Hk2HiS2ra2sp1D2dl2sl2ld2ls2lo3ds02ss3Hsl2Ln3SPR2LO1k1i2ds2wc2Hk2Hi2LX1w5HBarrS2ra2sp1D2dl2sl2ld2ls2lo3ds02ss3Hsl2Ln3SPR2LO1k1i2ds2wc2Hk2Hi2LX1w5HBarrS2ra2sp1D2dl2sl2ld2ls2lo3ds02ss3Hsl2Ln2LO2SX1k1i2ds2wc2Hk2Hi1wS2ra2dl2sl2ld2ls3ds02ss3Hsl2Ln1k1i2ds2Hk2Hi2LX1NS2ra1D2dl2sl3ds02ss1k1i2ds2Hk2Hi3wv12KlS2ra1D2dl3ds02ss1k1i2ds2Hk3wv1S2ra2dl2sl3ds02ss3Hsl1k1i2ds2Hk2Hi3wv1". (* [comment removed for export] *)
  #[using="S ls Hdl Hsl Ln L0 LS DB SB NZS SPR LO SX"] Lemma vexcess_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v1 ()) "Pk,$1=.Pi,$1.Pds,(14.(0.&40.))Pmm,P,(0.&40.)(1<.(0.&8.))Pc,$1.Pwc,(0.&40.)Pxt0,(0.&40.)Pxt1,(0.&40.)Pxt2,(0.&40.)Pxs0,(0.&40.)Pxa2,(0.&40.)Pxa4,(0.&40.)Pxa5,(0.&40.)Pxa6,(0.&40.)Pxa7,(0.&40.)Pxt3,(0.&40.)Pxt4,(0.&40.)Pxt5,(0.&40.)Pxt6,(0.&40.)Pwp,(0.&40.)Pwe,(0.&40.)P,(6.$1=.(16.(25.Vdl,R14.))R15.)P,(2.(3.Vsl,R15.)(4.R15.Vdl,))P,(6.(0.&40.)R4.(13.&40.(=.VD,(9.+4.R16.))))P,(6.(0.&40.)R4.(13.&40.(=.VD,(9.+4.Vdl,))))P,(2.(28.$32.R16.VD,R17.)(2.(6.$1.(2:.(17.(0.&40.)R17.))Vld,)(2.(21.(22.(23.$1.$1.)(24.$1.$1.VD,(=.VD,(9.+4.Vdl,)))(22.(23.$1.$1.)(24.$1.$1.(25.(7.&40.Vsp,)+30.)(7.&40.Vsp,))(26.(23.$1.$1.))))Vm,R16.)(2.(27.$32.Vm,R16.)(2.(33.$32.R16.)(34.$32.R16.Vlo,(=.(7.&40.Vsp,)-10.)))))))P,(35.$32.R17.(=.(7.&40.Vsp,)-10.)(22.$36.(37.#8.Vjunk,)(22.$36.(38.Vs0,)(26.$36.))))P,(2.(29.(0.&40.)(16.R1:.)R19.Vds0,)(2.(2.(3.=R17.)(4.R17.(5.+2.+20.)))(2.(6.$1.(7.&40.R16.)(8.R17.))(6.$1.(=.(18.R19.R1:.)(9.(5.+2.(9.+20.R1:.))R17.))(=.(18.Vds0,R1:.)(9.(18.Vss,Vsl,)Vb,))))))(39.$32.(3:.$32.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VD,Vdl,Vds0,Vsl,Vss,Vb,Vlo,Vm,)(3;.(3<.Vra,(13.&40.(=.(7.&40.Vsp,)-10.))Vgp,Vtp,R16.R15.R14.R13.Vs1,R17.R8.R12.R9.R11.R10.R?.R>.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(13.&40.+22<18.)Vfc,(3=.(0.&40.))R19.(3>.$32.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; (intros i ds mm c wc xt0 xt1 xt2 xs0 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wp we Hk Hi -> -> dd_H; ddestruct dd_H as (HX & LX & MU & WM & MI & ST); intros FR dd_H; ddestruct dd_H as (FS & HC & WC & VI)); [lia|].
    rdd HX FS (i + 0) w U0. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    wrv HX LX LX1 (i + 0). (* [comment removed for export] *)
    zstep. (* [comment removed for export] *) zstep. (* [comment removed for export] *)
    absx w wc c HC WC c1 wc1 wv1 R1 V1 WC1.
    match goal with MUx : munch _ m ?mx, WMx : wmono _ m ?mx, MIx : mem_inv _ ?mx, STx : stk _ ?mx _ _ |- _ =>
      rename MUx into MU1; rename WMx into WM1; rename MIx into MI1; rename STx into ST1 end.
    assert (FS1 : same_from (Z.to_nat (i + 1)) (upd ds (Z.to_nat (i + 0)) wv1) ds0).
    { replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat (i + 0))) by lia. apply same_from_upd. replace (i + 0) with i by lia. exact FS. }
    assert (VI1 : lval (upd ds (Z.to_nat (i + 0)) wv1) (i + 1) + 2^(32*(i + 1)) * c1 = lval ds0 (i + 1) + lval ss sl * b).
    { replace (i + 0) with i in U0 |- * by lia. eapply vi_exc_step; [lia| lia| exact VI| rewrite U0; exact V1]. }
    zstep. (* [comment removed for export] *)
    ptr_cases Kl.
    - eapply (IH (i + 1)); [lia | lia | f_equal; lia | reflexivity | exact (conj HX (conj LX1 (conj MU1 (conj WM1 (conj MI1 ST1))))) | exact FR| exact (conj FS1 (conj R1 (conj WC1 VI1)))].
    - eapply vtail_walk; [exact (conj HX (conj LX1 (conj MU1 (conj WM1 (conj MI1 ST1))))) | exact FR|]. replace dl with (i + 1) by lia. exact (conj FS1 (conj R1 (conj WC1 VI1))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L18456115372.64L26555529445.61L33777652057.64L40836957225.61L41415761909.64L4701258793.61 L49488902373.61L62958130312.6400000E00F00W01>01I01[01\02;S2ra2dl2sl3ds02ss3HltFS2ra2dl2sl3ds02ssS2ra1D2dl2sl2ld2ls3ds02ss3Hsl2Ln2DB3HltS2ra3ds02ssS2ra2dl3ds02ss3HdlFS2ra1D2dl2sl3ds02ss3Hdl3Hsl3Hlt". (* [comment removed for export] *)
  #[using="S ls Hdl Hsl Ln L0 LS DB SB NZS SPR LO SX"] Lemma vexcess_entry : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v1 ()) "Pds,(14.(0.&40.))Pmm,P,(0.&40.)(1<.(0.&8.))Pc,$1.Pwc,(0.&40.)Pxt0,(0.&40.)Pxt1,(0.&40.)Pxt2,(0.&40.)Pxs0,(0.&40.)Pxa2,(0.&40.)Pxa4,(0.&40.)Pxa5,(0.&40.)Pxa7,(0.&40.)Pxt3,(0.&40.)Pxt4,(0.&40.)Pxt5,(0.&40.)Pxt6,(0.&40.)Pwp,(0.&40.)P,(6.(0.&40.)R1.(13.&40.(=.VD,(9.+4.Vsl,))))P,(4.Vsl,Vdl,)P,(2.(28.$32.R12.VD,R13.)(2.(6.$1.(2:.(17.(0.&40.)R13.))Vld,)(2.(21.(22.(23.$1.$1.)(24.$1.$1.VD,(=.VD,(9.+4.Vdl,)))(22.(23.$1.$1.)(24.$1.$1.(25.(7.&40.Vsp,)+30.)(7.&40.Vsp,))(26.(23.$1.$1.))))Vm,R12.)(2.(27.$32.Vm,R12.)(2.(33.$32.R12.)(34.$32.R12.Vlo,(=.(7.&40.Vsp,)-10.)))))))P,(35.$32.R13.(=.(7.&40.Vsp,)-10.)(22.$36.(37.#8.Vjunk,)(22.$36.(38.Vs0,)(26.$36.))))P,(2.(29.(0.&40.)(16.Vsl,)R15.Vds0,)(2.(2.(3.=R13.)(4.R13.(5.+2.+20.)))(2.(6.$1.(7.&40.R12.)(8.R13.))(6.$1.(=.(18.R15.Vsl,)(9.(5.+2.(9.+20.Vsl,))R13.))(=.(18.Vds0,Vsl,)(9.(18.Vss,Vsl,)Vb,))))))(39.$32.(3:.$32.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VD,Vdl,Vds0,Vsl,Vss,Vb,Vlo,Vm,)(3;.(3<.Vra,(13.&40.(=.(7.&40.Vsp,)-10.))Vgp,Vtp,R12.R11.R10.R?.Vs1,R13.(13.&40.Vdl,)R>.R6.R=.R<.(13.&40.Vsl,)R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(13.&40.+22<08.)Vfc,(3=.(0.&40.))R15.(3>.$32.)))")
(* [comment removed for export] *).
  Proof.
    intros until wp. intros -> Hlt DI FR VI.
    zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
    eapply (vexcess_walk (Z.to_nat (dl - sl)) sl); [lia | lia | f_equal; lia | f_equal; lia | exact DI | exact FR| exact VI].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  Section WithB.
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00Y0?L10353856370.85L10898104775.88L13434842651.88L14004442312.84L14004510454.83L14124098967.86L14948171334.73L16699335585.88L18045970546.86L18045970546.87L22798223438.85L23505094718.88L24050514656.87L24101615269.80L24101615269.85L25088106061.73L25088149922.79L26260356014.89L27738507013.78L32506420635.88L33502054376.89L3447022552.85 L43275568960.88L45593372576.77L4616541109.71 L48109791025.73L50590728892.86L50590729146.84L50776364546.73L51979595820.85L52003340808.88L52094852868.73L53315723119.85L58046200496.89L58046400009.73L58931929174.73L59314841581.76L6384611436.73 L67717333530.88L8929650294.73 L954237987.86  00000O01c02d03V04H04d04e06907:08;08W09509609P09j0:E0:`0;F0;`0=10=W0>I0>o0?J0AK0Ao0C:0DE0DF0E:0E^0FB0GG0Gm0HL0Hi0IY0J40JR0JS0K2S2ra2sl3ds02ss1k1i2ds2Hk2Hi3wv1S2ra2sp1D2dl1S2sl2ld2ls2lo3ds02ss3Hdl2Ln2L02LS2DB2SB3NZS3SPR2LO3SSX1k1i2ds2Hk2Hi3ds1S2ra2sp1D2dl2sl2ld2ls2lo3ds02ss3Hsl2Ln2LO2SX1k1i2ds2Hk2Hi3wv13LX1S2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln1k1i2ds2Hk2Hi2LXS2ra2dl2sl2ld2ls3ds02ss3Hdl3Hsl2Ln1k1i2ds2Hk2Hi2LXS2ra2sl3ds02ss1k1i2ds2Hk3wv1FS2ra2sp1D2dl1S2sl2ld2ls2lo3ds02ss3Hdl2Ln2L02LS2DB2SB3NZS3SPR2LO3SSX1k1i2ds2Hk2Hi3ds1S2ra2sp1D2dl1S2sl2ld2ls2lo3ds02ss2Ln2LS2DB2SB2LO1k1i2ds2Hk2Hi3wv1S2ra2sp1D2dl1S2sl2ld2ls2lo3ds02ss2Ln2LS2DB2SB2LO1k1i2ds2Hk2Hi3wv1S2ra2sl3ds02ss1k1i2ds2Hk3wv1S2ra1S2sl3ds02ss1k1i2ds2Hk3ds1FS2ra1D2sl3ds02ss1k1i2ds2HkS2ra1D2sl3ds02ss1k1i2ds2HkS2ra2sl3ds02ss1k1i2ds2Hk2HiS2ra2sl3ds02ss1k1i2ds2Hk2HiS2ra2dl2sl3ds02ss3Hsl1k1i2ds2Hk3ds12K2S2ra1S2sl3ds02ss1k1i2ds2HkS2ra2sp1m1D2dl1S2sl2ld2ls2lo3ds02ss3Hdl2Ln2L02LS2LO2SX3SSX1k1i2ds2Hk2Hi2AS3ds12KlS2ra1D1S2sl3ds02ss1k1i2ds2Hk2Hi3ds12KlS2ra2dl2sl2ld2ls3ds02ss3Hsl2Ln1k1i2ds2Hk2Hi2LX3wv1S2ra2dl2sl3ds02ss3Hsl1k1i2ds2Hk2Hi3ds1S2ra2sl3ds02ss1k1i2ds2Hk2HiS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1D2dl1S2sl2lo1b3ds02ss1i2ds2mm2wc3xt13xt23xs03xa33xt33xt43xt53xt62Hk2HiS2ra2dl2sl2ld2ls3ds02ss2Ln1k1i2ds2HkS2ra2sp1D2dl2sl2ld2ls2lo3ds02ss3Hsl2Ln3SPR2LO1k1i2ds2Hk2Hi2LX3wv13LX15HBarrS2ra2sp1D2dl2sl2ld2ls2lo3ds02ss3Hsl2Ln3SPR2LO1k1i2ds2Hk2Hi2LX3wv13LX15HBarrFS2ra1D2dl2sl2ld2ls3ds02ss3Hsl2Ln2DB1k1i2ds2Hk2Hi3ds1S2ra1S2sl3ds02ss1k1i2ds2Hk2Hi3ds12KlS2ra2dl2sl2ld2ls3ds02ss2Ln1k1i2ds2HkS2ra2sp1D2dl2sl2ld2ls2lo3ds02ss3Hdl3Hsl2Ln2LO2SX1k1i2ds2Hk2Hi3wv13LX1S2ra2dl2sl3ds02ss3Hsl1k1i2ds2Hk3ds12K2S2ra2dl2sl3ds02ss3Hsl1k1i2ds2HkS2ra2sl1b3ds02ss2HB1k1i2ds2HkS2ra2dl2sl2ld2ls3ds02ss3Hsl2Ln1k1i2ds2Hk2Hi2LX1NS2ra2sl3ds02ss1k1i2ds2Hk2HiS2ra1D2sl3ds02ss1k1i2ds2Hk3ds1FS2ra2sl3ds02ss1k1i2ds2Hk2Hi3wv1". (* [comment removed for export] *)
    #[using="Hdl Hsl Ln L0 LS DB SB NZS SPR LO SX SSX HB"] Lemma vx1_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v1 ()) "Pk,$1=.Pi,$1.Pds,(14.(0.&40.))Pmm,P,(0.&40.)(1<.(0.&8.))Pc,$1.Pwc,(0.&40.)Pxt1,(0.&40.)Pxt2,(0.&40.)Pxs0,(0.&40.)Pxa3,(0.&40.)Pxt3,(0.&40.)Pxt4,(0.&40.)Pxt5,(0.&40.)Pxt6,(0.&40.)Pwps,(0.&40.)Pwpd,(0.&40.)Pwe,(0.&40.)P,(6.$1=.(16.(25.Vsl,R10.))R11.)P,(2.(3.=R11.)(4.R11.Vsl,))P,(6.(0.&40.)R5.(13.&40.(=.VS,(9.+4.R12.))))P,(6.(0.&40.)R5.(13.&40.(=.VD,(9.+4.R13.))))P,(6.(0.&40.)R5.(13.&40.(=.VS,(9.+4.Vsl,))))P,(2.(28.$32.R13.VD,R14.)(2.(6.$1.(2:.(17.(0.&40.)R14.))Vld,)(2.(21.(22.(23.$1.$1.)(24.$1.$1.VD,(=.VD,(9.+4.Vdl,)))(22.(23.$1.$1.)(24.$1.$1.(25.(7.&40.Vsp,)+30.)(7.&40.Vsp,))(26.(23.$1.$1.))))Vm,R13.)(2.(27.$32.Vm,R13.)(2.(33.$32.R13.)(34.$32.R13.Vlo,(=.(7.&40.Vsp,)-10.)))))))P,(1>.(2.(6.$1.VS,VD,)(6.(14.(0.&40.))Vss,Vds0,))(2.(1?.$32.Vm,VS,(20.Vss,))(1>.(3.(=.VS,(9.+4.Vls,))VD,)(3.(=.VD,(9.+4.Vld,))VS,))))P,(35.$32.R15.(=.(7.&40.Vsp,)-10.)(22.$36.(37.#8.Vjunk,)(22.$36.(38.Vs0,)(26.$36.))))P,(2.(29.(0.&40.)(16.R18.)R17.Vds0,)(2.(2.(3.=R15.)(4.R15.(5.+2.+20.)))(2.(6.$1.(7.&40.R14.)(8.R15.))(6.$1.(=.(18.R17.R18.)(9.(5.+2.(9.+20.R18.))R15.))(=.(18.Vds0,R18.)(9.(18.Vss,R18.)Vb,))))))(39.$32.(3:.$32.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VD,Vdl,Vds0,Vsl,Vss,Vb,Vlo,Vm,)(3;.(3<.Vra,(13.&40.(=.(7.&40.Vsp,)-10.))Vgp,Vtp,R:.R14.R13.R12.Vs1,R15.(13.&40.Vdl,)R<.R11.(13.&40.Vb,)R;.(13.&40.Vsl,)(13.&40.(25.Vdl,Vsl,))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(13.&40.+22;;8.)Vfc,(3=.(0.&40.))R17.(3>.$32.)))")
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; (intros i ds mm c wc xt1 xt2 xs0 xa3 xt3 xt4 xt5 xt6 wps wpd we Hk Hi -> -> -> dd_H; ddestruct dd_H as (HX & LX & MU & WM & MI & ST); intros AS FR dd_H; ddestruct dd_H as (FS & HC & WC & VI)); [lia|].
      rdsf AS MU WM HX FS LX L0 LS LO SSX sl (i + 0) w Us. rdd HX FS (i + 0) w0 Ud.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      absc w w0 wc b c HB HC WC c1 wc1 wv1 R1 V1 WC1.
      zstep. wrv HX LX LX1 (i + 0). zstep. zstep.
      pose proof (same_from_upd _ _ _ wv1 FS) as FS1. replace (i + 0) with i in * by lia.
      adv ds1 LX1 FS1 VI Ud Us V1 VI1 (i + 1).
      match goal with MUx : munch _ m ?mx, WMx : wmono _ m ?mx, MIx : mem_inv _ ?mx, STx : stk _ ?mx _ _ |- _ =>
        rename MUx into MU1; rename WMx into WM1; rename MIx into MI1; rename STx into ST1 end.
      zstep. ptr_cases Kl.
      - eapply (IH (i + 1)); [lia | lia | f_equal; lia | f_equal; lia | reflexivity | exact (conj HX (conj LX1 (conj MU1 (conj WM1 (conj MI1 ST1)))))
          | exact AS | exact FR| exact (conj FS1 (conj R1 (conj WC1 VI1)))].
      - replace (i + 1) with sl in FS1, VI1 by lia.
        zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
        + eapply vexcess_entry; [f_equal; lia | lia | exact (conj HX (conj LX1 (conj MU1 (conj WM1 (conj MI1 ST1))))) | exact FR| exact (conj FS1 (conj R1 (conj WC1 VI1)))].
        + zstep. eapply vtail_walk; [exact (conj HX (conj LX1 (conj MU1 (conj WM1 (conj MI1 ST1))))) | exact FR|].
          replace dl with sl by lia. exact (conj FS1 (conj R1 (conj WC1 VI1))).
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L18490958385.67L26260356014.67L27196081286.67L36091208531.67L37675132972.67L40836957225.62L41415943117.67L4701258793.62 L51979595820.63L58046200496.67L66675698381.6300000A00Y00l01D01_02B02M02_03F03a049S2ra2sl3ds02ss2i0S2ra2dl2sl3ds02ss3Hsl2K2S2ra1S2sl3ds02ss2i0S2ra2sl3ds02ss2i03Hi02K1S2ra2sl3ds02ss2i02ds3Hi02K1S2ra1D2dl2sl2ld2ls3ds02ss3Hsl2Ln2DBS2ra3ds02ssS2ra2dl3ds02ss3HdlS2ra1D2dl2sl2ld2ls3ds02ss3Hsl2Ln2DB3Hi0S2ra2dl2sl3ds02ss3Hsl2ds2K2S2ra2sl3ds02ss2i03Hi02Hr". (* [comment removed for export] *)
    #[using="Hdl Hsl Ln L0 LS DB SB NZS SPR LO SX SSX HB"] Lemma vafter_x8_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla_v1 ()) "Pi0,$1.Pds,(14.(0.&40.))Pmm,P,(0.&40.)(1<.(0.&8.))Pc,$1.Pwc,(0.&40.)Pxt0,(0.&40.)Pxt1,(0.&40.)Pxt2,(0.&40.)Pxt3,(0.&40.)Pxt4,(0.&40.)Pxt5,(0.&40.)Pxt6,(0.&40.)Pxs0,(0.&40.)Pxa4,(0.&40.)Pxa7,(0.&40.)Pwps,(0.&40.)Pwpd,(0.&40.)P,(2.(3.=R11.)(3.R11.Vsl,))P,(4.(25.Vsl,R12.)+8.)P,(6.(0.&40.)R4.(13.&40.(=.VS,(9.+4.R13.))))P,(6.(0.&40.)R4.(13.&40.(=.VD,(9.+4.R14.))))P,(6.$1.(11.(7.&40.R8.)+20.)Vb,)P,(2.(28.$32.R14.VD,R15.)(2.(6.$1.(2:.(17.(0.&40.)R15.))Vld,)(2.(21.(22.(23.$1.$1.)(24.$1.$1.VD,(=.VD,(9.+4.Vdl,)))(22.(23.$1.$1.)(24.$1.$1.(25.(7.&40.Vsp,)+30.)(7.&40.Vsp,))(26.(23.$1.$1.))))Vm,R14.)(2.(27.$32.Vm,R14.)(2.(33.$32.R14.)(34.$32.R14.Vlo,(=.(7.&40.Vsp,)-10.)))))))P,(1>.(2.(6.$1.VS,VD,)(6.(14.(0.&40.))Vss,Vds0,))(2.(1?.$32.Vm,VS,(20.Vss,))(1>.(3.(=.VS,(9.+4.Vls,))VD,)(3.(=.VD,(9.+4.Vld,))VS,))))P,(35.$32.R16.(=.(7.&40.Vsp,)-10.)(22.$36.(37.#8.Vjunk,)(22.$36.(38.Vs0,)(26.$36.))))P,(2.(29.(0.&40.)(16.R19.)R18.Vds0,)(2.(2.(3.=R16.)(4.R16.(5.+2.+20.)))(2.(6.$1.(7.&40.R15.)(8.R16.))(6.$1.(=.(18.R18.R19.)(9.(5.+2.(9.+20.R19.))R16.))(=.(18.Vds0,R19.)(9.(18.Vss,R19.)Vb,))))))(39.$32.(3:.$32.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VD,Vdl,Vds0,Vsl,Vss,Vb,Vlo,Vm,)(3;.(3<.Vra,(13.&40.(=.(7.&40.Vsp,)-10.))Vgp,Vtp,R15.R14.R13.R>.Vs1,R16.(13.&40.Vdl,)R;.(13.&40.(25.Vsl,R1:.))R=.R:.(13.&40.Vsl,)R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.R10.R?.)VF,(13.&40.+22;:4.)Vfc,(3=.(0.&40.))R18.(3>.$32.)))")
(* [comment removed for export] *).
    Proof.
      intros until wpd. intros Hi0 Hr -> -> HA4 DI AS FR VI.
      zstep. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
      - (* [comment removed for export] *)
        assert (i0 = sl) as -> by lia.
        zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
        + eapply vtail_walk; [exact DI | exact FR|]. replace dl with sl by lia. exact VI.
        + eapply vexcess_entry; [f_equal; lia | lia | exact DI | exact FR| exact VI].
      - zstep. rewrite HA4. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
        eapply (vx1_walk (Z.to_nat (sl - i0)) i0); [lia | lia | reflexivity | reflexivity | f_equal; lia | exact DI | exact AS | exact FR| exact VI].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End WithB.
End Walk.
