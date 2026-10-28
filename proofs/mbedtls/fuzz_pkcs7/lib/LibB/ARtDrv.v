(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame HeapIface Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow AUnw ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_exit_lib.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ARtDrv () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KBATCH : Z := 24.
(* [comment removed for export] *)
Definition AVOL_SPLIT : Z := 2^32.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition drv_static (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_ARtDrv ()) "(0.(1.(2.+?:360.O1.)(3.O1.+?:400.))(0.(1.(2.+?:460.O1.)(3.O1.+?:780.))(0.(4.$5.O1.+106390.)(0.(1.(2.+62<050.O1.)(3.O1.+63<080.))(0.(1.(2.+63<084.O1.)(3.O1.+63<0:0.))(0.(1.(2.+63<180.O1.)(3.O1.+63<9><.))(0.(1.(2.+63<9?0.O1.)(3.O1.+63<:38.))(0.(1.(2.+63<:40.O1.)(3.O1.+63<:88.))(0.(1.(2.+63<::4.O1.)(3.O1.+63<:;0.))(0.(1.(2.+63<:<0.O1.)(3.O1.+65<=50.))(1.(2.+65<=58.O1.)(3.O1.+65=:;0.))))))))))))")
(* [comment removed for export] *).
(* [comment removed for export] *)

Section WithR.
Variable segs : list Segment.
Variable R : art_layout.
Variable HIA : artA segs R.
Let L := arl_L R.
#[local] Existing Instance L.   (* [comment removed for export] *)
Let AL := arl_AL R.

Record artD := ARTD {
  hfresh : HST segs R HIA -> Z -> Prop;       (* [comment removed for export] *)
  pclass : Z -> Z;                            (* [comment removed for export] *)

  (* [comment removed for export] *)
  hd_rtc : forall m, arl_rtc R m -> asan_rtc m;
  hd_static : forall a, drv_static a -> cstatic R a;
  hd_needs : 0 <= arl_need_malloc R <= 4096 /\ 0 <= arl_need_free R <= 4096 /\ 0 <= arl_need_amem R <= 4096;
  hd_ceil : alloc_ceiling + 8 <= 0x7fffffffffff;
  (* [comment removed for export] *)
  hd_blk_band : forall h LB LF m A n, HM segs R HIA h LB LF m -> In (A, n) LB ->
      0x65f000 <= A /\ A + n <= alloc_ceiling /\ (A + n <= 0x7fff7000 \/ 0x10007fff8000 <= A);
  hd_lowsh : forall h LB LF m, HM segs R HIA h LB LF m -> mapped m 0x7fffa000 0x800d3000;
  (* [comment removed for export] *)
  hd_pclass_batch : forall n, pclass n = KBATCH -> 5889 <= n <= 7936;

  (* [comment removed for export] *)
  heapA_malloc_split : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST segs R HIA) (LB LF : list blk) (n lo d : Z) (A B : TSet),
      HM segs R HIA h LB LF m -> HK segs R HIA h mo ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_malloc R ->
      bv_unsigned sp <= htop segs R HIA h -> bv_unsigned sp mod 16 = 0 ->
      mem_inv segs m -> tp = Z_to_bv 64 (arl_tp R) ->
      a0 = Z_to_bv 64 n -> 0 <= n < AMAX -> (AMAX_SEC <= n \/ hfresh h (pclass n)) ->
      havol segs R HIA h + (2 * n + AVOL_CALL) <= AVOL_MAX ->
      havol segs R HIA h + (2 * n + AVOL_CALL) <= AVOL_SPLIT ->                (* [comment removed for export] *)
      uwc segs m (arl_stklo R) (hstkhi segs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d -> hfr segs R HIA h + fr_charge d <= FR_MAX ->   (* [comment removed for export] *)
      (win24 n = true -> cnt24 LB < C24MAX) ->                                             (* [comment removed for export] *)
      A [] -> B [] ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' mo' h',
          mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> mo_frame mo mo' -> wmono segs m m' ->
          presA segs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi segs R HIA h) [] m m' ->
          htop segs R HIA h' = htop segs R HIA h -> hstkhi segs R HIA h' = hstkhi segs R HIA h -> hflag segs R HIA h' = hflag segs R HIA h ->
          HK segs R HIA h' mo' -> (forall x, hcs segs R HIA h x -> hcs segs R HIA h' x) ->
          havol segs R HIA h' <= havol segs R HIA h + (2 * n + AVOL_CALL) -> hfr segs R HIA h' <= hfr segs R HIA h + fr_charge d ->
          (forall c, (AMAX_SEC <= n \/ c <> pclass n) -> hfresh h c -> hfresh h' c) ->   (* [comment removed for export] *)
          HM segs R HIA h' LB LF m' ->
          srealizesJ segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) mo') A) ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' mo' h' (Ab : Z) (junk : list byte),
          mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> mo_frame mo mo' -> wmono segs m m' ->
          presA segs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi segs R HIA h) [] m m' ->
          htop segs R HIA h' = htop segs R HIA h -> hstkhi segs R HIA h' = hstkhi segs R HIA h -> hflag segs R HIA h' = hflag segs R HIA h ->
          HK segs R HIA h' mo' -> (forall x, hcs segs R HIA h x -> hcs segs R HIA h' x) ->
          havol segs R HIA h' <= havol segs R HIA h + (2 * n + AVOL_CALL) -> hfr segs R HIA h' <= hfr segs R HIA h + fr_charge d ->
          (forall c, (AMAX_SEC <= n \/ c <> pclass n) -> hfresh h c -> hfresh h' c) ->
          Ab mod 16 = 0 -> fresh_apart R LB LF Ab n -> (Ab + n <= arl_stklo R \/ hstkhi segs R HIA h <= Ab) ->
          HM segs R HIA h' ((Ab, n) :: LB) LF m' -> rw_cells segs m' Ab [CB (Z.to_nat n) junk] ->
          srealizesJ segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Ab) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) mo') B) ->
      srealizesJ segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (arl_malloc R)) fc None m (seg_rom segs)) mo) (t_alt2 A B);

  (* [comment removed for export] *)
  heapA_freeD : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST segs R HIA) (LB LF : list blk) (A n lo d : Z),
      HM segs R HIA h LB LF m -> HK segs R HIA h mo -> In (A, n) LB ->
      stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_free R ->
      bv_unsigned sp <= htop segs R HIA h -> bv_unsigned sp mod 16 = 0 ->
      mem_inv segs m -> tp = Z_to_bv 64 (arl_tp R) ->
      a0 = Z_to_bv 64 A ->
      havol segs R HIA h + AVOL_CALL <= AVOL_MAX ->
      uwc segs m (arl_stklo R) (hstkhi segs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d -> hfr segs R HIA h + fr_charge d <= FR_MAX ->   (* [comment removed for export] *)
      aevtS segs
        (fun c => exists ms' mo', c = mkCfg ms' mo' /\
           call_postA segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun _ m' =>
             mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ mo_frame mo mo'
             /\ presA segs R (lb_remove A LB) LF (bv_unsigned sp) (arl_stklo R) (hstkhi segs R HIA h) [] m m'
             /\ exists h', htop segs R HIA h' = htop segs R HIA h /\ hstkhi segs R HIA h' = hstkhi segs R HIA h /\ hflag segs R HIA h' = hflag segs R HIA h
                /\ HK segs R HIA h' mo'
                /\ (forall x, hcs segs R HIA h x -> hcs segs R HIA h' x)   (* [comment removed for export] *)
                /\ havol segs R HIA h' <= havol segs R HIA h + AVOL_CALL /\ hfr segs R HIA h' <= hfr segs R HIA h + fr_charge d
                /\ (forall c, c <> KBATCH -> hfresh h c -> hfresh h' c)
                /\ HM segs R HIA h' (lb_remove A LB) LF m') ms')
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (arl_free R)) fc None m (seg_rom segs)) mo)
}.
End WithR.
