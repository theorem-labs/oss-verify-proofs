(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr ItAPure IfAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import U2AObj U2AIface ItA_base U2AIface_fit2_draft IfA_base IfAKit IfA_pro IfA_err IfA_exit IfA_loop.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma djf_ifW : forall SP Zs S OB osz a k,
  disjoint_from (ifast_W SP Zs S OB osz) a k -> disjoint_from (ifW SP Zs S OB osz) a k.
Proof. intros SP Zs S OB osz a k H. unfold ifast_W, IFAST_STACK, ifW in *. cbn [disjoint_from] in *. repeat split; try exact I; lia. Qed.

Lemma sub_fp_pro : forall SP Zs S OB osz, sub_fp [(SP - 240, SP)] (ifast_W SP Zs S OB osz).
Proof. intros SP Zs S OB osz a Ha. unfold ifast_W, IFAST_STACK in Ha. cbn [outside] in *. repeat split; try exact I; lia. Qed.
Lemma sub_fp_body : forall SP Zs S OB osz, sub_fp (ifW SP Zs S OB osz ++ [(SP - 104, SP)]) (ifast_W SP Zs S OB osz).
Proof. intros SP Zs S OB osz a Ha. unfold ifast_W, IFAST_STACK, ifW in *. cbn [outside app] in *. repeat split; try exact I; lia. Qed.

Theorem inflate_fast_proofA : inflate_fast_stmtA.
Proof.
  unfold inflate_fast_stmtA. intros until pad.
  intros MI GOT SHB ST LOC LOS SPT A0 A1 STRM SSC TAIL Z8 S16 SHZ RZ RSZ (SHS & RS & RSS) TABL TABD LB DB TOKL TOKD
         PAYB PAYR PAYN D1 D8 NR UNP RD RSD OUT FOR OB8 OSZ SHO ROB RSOB WINC FWR
         Z0 ZL S0 SL DL OB0 OBL LAL DAL WDL DJTL DJTD DJD DJW ZSD ZOD SOD BZ BS BO CIN CIN6 COUT COUT258 BITS HOLD B8 OUTR OUTB
         WH0 WN0 WD0 WDN RI RSTK.
  subst a0 a1. unfold IFAST_STACK in LOS. unfold KHIGH in LOC. unfold KEND in SPT.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64) with (2^64) in RSP.
  set (wsz := if Wd =? 0 then 0 else 32768) in *.
  set (bo := cout - (out - (osz - cout))).
  assert (WSZC : (Wd = 0 /\ wsz = 0) \/ (Wd <> 0 /\ wsz = 32768)).
  { subst wsz. destruct (Z.eqb_spec Wd 0); [left| right]; lia. }
  assert (WHB : 0 <= whave <= wsz /\ 0 <= wnext <= wsz /\ (wnext = 0 \/ whave = wsz \/ wnext = whave)).
  { destruct WSZC as [[E1 E2]|[E1 E2]]; [destruct (WD0 E1)| destruct (WDN E1) as (X1 & X2 & X3)]; lia. }
  assert (WDR : 0 <= Wd < 2 ^ 47).
  { destruct WDL as [->|[X1 X2]]; lia. }
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (if_pro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo RNG Zs S ltac:(lia) ltac:(unfold KHIGH; lia) ltac:(unfold KEND; lia) RSTK RI Z8 S16
                   ltac:(lia) ltac:(lia) RZ RSZ RS RSS
                   t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m D OB n osz cin cout out hold bits whave wnext Wd wsz lb db la da bo
                   zti zto zmsg zalloc zfree zopq zdt zadl zres zp1 zp2 zp3
                   strm (Z_to_bv 64 LEN) last wrap havedict flags dmax check total head wbits length_ offset extra ncode nlen ndist have next
                   ST MI GOT SHB STRM SSC SHZ SHS); try lia; try reflexivity.
    all: destruct TABL as (_ & _ & X & X' & _); destruct TABD as (_ & _ & Y & Y' & _); lia. }
  cbv beta. intros ms1 (m1 & x1 & x6 & x10 & x11 & x13 & x15 & x16 & x21 & v0 & v24 & v48 & v56 & -> & MU1 & WM1 & MI1 & STK1 & SAV1 & FRM1 & STRM1 & SSC1).
  (* [comment removed for export] *)
  set (SP := bv_unsigned sp) in *.
  assert (DJ1 : forall a k, a + k <= lo -> disjoint_from [(SP - 240, SP)] a k) by (intros a k H; cbn [disjoint_from]; split; [lia| exact I]).
  assert (BAND : forall s k, 2147446784 <= s -> s + k <= 17594333495296 -> disjoint_from (ifW SP Zs S OB osz) s k).
  { intros s k B1 B2. clear - BZ BS BO LOC LOS B1 B2. unfold ifW, app_band in *. cbn [disjoint_from]. repeat split; try exact I; lia. }
  assert (SHB1 : forall X k, 0 <= X -> X + 8 * k <= lo -> 0 <= k ->
                 2147446784 <= Z.shiftr X 3 + 2147450880 /\ Z.shiftr X 3 + 2147450880 + k <= 17594333495296).
  { intros X k X0 XL K0. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  assert (TABX : forall A na rd, ctab_at RNG m A na rd -> A + 4 * na <= lo -> disjoint_from (ifast_W SP Zs S OB osz) A (4 * na) ->
                 if_tab RNG (ifW SP Zs S OB osz) m1 A na rd).
  { intros A na0 rd (TB & T4 & T0 & TN0 & RT & TR & t1' & t2' & SHT & RST & SB1 & SB2 & TS1 & TS2) AL DJT.
    unfold if_tab.
    split. { eapply bytes_at_transport; [exact TB| exact MU1|]. apply DJ1. rewrite u32s_length, fws_length. lia. }
    split; [exact T4|]. split; [exact T0|]. split; [exact TN0|]. split; [lia|]. split; [exact RT|]. split; [exact TR|].
    split; [apply djf_ifW; exact DJT|].
    exists t1', t2'. split. { eapply sh0_mu; [exact SHT| exact MU1|]. apply DJ1. lia. }
    split; [exact RST|]. split; [apply BAND; lia|]. split; [exact TS1| exact TS2]. }
  assert (CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1).
  { unfold if_ctx. cbv zeta.
    split. { repeat split; try assumption; try lia. }
    split. { subst bo. repeat split; try assumption; try lia. }
    split. { split; [eapply rng_sub'; [exact RSTK| lia]|]. split; [exact RZ|]. split; [exact RSZ|]. split; [exact RS|]. split; [exact RSS|].
             split; [exact RD|]. split; [exact RSD|]. split; [exact ROB|]. split; [exact RSOB| exact RI]. }
    split.
    { destruct (SHB1 Zs 14 ltac:(lia) ltac:(lia) ltac:(lia)) as [BZ1 BZ2].
      destruct (SHB1 S 897 ltac:(lia) ltac:(lia) ltac:(lia)) as [BS1 BS2].
      assert (BOX : 2147446784 <= Z.shiftr OB 3 + 2147450880 /\ Z.shiftr OB 3 + 2147450880 + (osz + 7) / 8 <= 17594333495296)
        by (clear - OB0 OBL LOS SPT RSP OSZ; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
      destruct BOX as [BO1 BO2].
      split; [eapply sh0_mu; [exact SHZ| exact MU1| apply DJ1; lia]|].
      split; [eapply sh0_mu; [exact SHS| exact MU1| apply DJ1; lia]|].
      split; [eapply sh0_mu; [exact SHO| exact MU1| apply DJ1; lia]|].
      split; [apply BAND; lia|]. split; [apply BAND; lia|]. apply BAND; lia. }
    split; [apply TABX; assumption|]. split; [apply TABX; assumption|]. split; [exact TOKL|]. split; [exact TOKD|].
    split. { eapply bytes_at_transport; [exact PAYB| exact MU1|]. apply DJ1. rewrite length_map. lia. }
    split; [exact PAYR|]. split; [exact PAYN|].
    assert (SHD : 2147446784 <= shad D /\ shad (D + n - 1) + 1 <= 17594333495296 /\ shad D <= shad (D + n - 1) + 1).
    { unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
    split. { eapply unpoisoned_munch; [exact UNP| exact MU1|]. replace (D + n - 1) with (D + n - 1) by lia. apply DJ1; lia. }
    split; [apply djf_ifW; exact DJD|].
    split; [apply BAND; lia|].
    split.
    { unfold itail_cells in TAIL. rw_split TAIL 1%nat T1 T2. eapply rw_cells_transport; [exact T1| exact MU1| exact WM1|].
      apply DJ1. cbn [cells_size csize Nat.add]. lia. }
    split; [exact FWR|].
    intros WNZ. destruct WSZC as [[E1 E2]|[E1 E2]]; [lia|].
    destruct WINC as [->|(WARR & W16 & RW & RSW & SHW)]; [lia|].
    destruct WDL as [->|[W0 WL]]; [lia|]. destruct DJW as [->|DJW]; [lia|].
    assert (E32 : Z.of_nat 32768 = 32768) by reflexivity.
    destruct (SHB1 Wd 4096 ltac:(lia) ltac:(lia) ltac:(lia)) as [BW1 BW2].
    split. { eapply f8arr_transport; [exact WARR| exact MU1| exact WM1|]. apply DJ1; lia. }
    split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [exact RW|]. split; [exact RSW|].
    split; [apply djf_ifW; exact DJW|].
    split; [eapply sh0_mu; [exact SHW| exact MU1| apply DJ1; lia]|]. apply BAND; lia. }
  pose (sd := SDC zti zto zalloc zfree zopq zdt zadl zres zp1 zp2 zp3).
  pose (id := IDC strm last wrap havedict flags dmax check total head wbits length_ offset extra ncode nlen ndist have next).
  assert (INV1 : if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m1 v0 v24 v48 v56 sd id
                        (Z_to_bv 64 (D + cin)) (Z_to_bv 64 (n - cin)) (Z_to_bv 64 (OB + cout)) (Z_to_bv 64 (osz - cout)) zmsg (Z_to_bv 64 LEN)
                        (Z_to_bv 64 hold) (Z_to_bv 64 bits) fo).
  { unfold if_inv. split; [exact MI1|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact FRM1|].
    split; [exact STRM1|]. split; [exact SSC1|].
    split; [| exact FOR]. eapply f8arr_transport; [exact OUT| exact MU1| exact WM1|]. apply DJ1. lia. }
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (if_loop RNG FR fc gp tp sp lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1 sd id _ _ _ _ _ _ _ _ CX
                    (Z.to_nat (fW n osz cin bits cout)) m1 v0 v24 v48 v56 fo x1 x6 x10 x11 x13 x15 x16 x21 cin cout hold bits INV1); subst bo; lia. }
  cbv beta. intros ms2 (mode' & ci2 & co2 & hold2 & bits2 & HE & CI2 & CO2 & BITS2 & HOLD2 & A2 & Q2 & MODE').
  destruct HE as (m2 & y1 & y6 & y10 & y11 & y13 & y15 & y16 & y21 & w0 & w24 & w48 & w56 & msg' & fo2 & -> & INV2).
  (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (if_exit RNG FR fc gp tp ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1
                    sd id _ _ _ _ _ _ CX m2 w0 w24 w48 w56 msg' mode' fo2 y1 y6 y10 y11 y13 y15 y16 y21 ci2 co2 hold2 bits2 INV2 SAV1 STK1); subst bo; lia. }
  cbv beta. intros ms3 (m3 & q0 & q1 & q2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & msg3 & fo3 & -> & MI3 & MU3 & WM3 & ST3 & STRM3 & SSC3 & OUT3 & FOR3).
  assert (QF : 0 <= bits2 / 8 /\ 0 <= bits2 mod 8 <= 7 /\ bits2 = 8 * (bits2 / 8) + bits2 mod 8) by (clear - BITS2; Z.div_mod_to_equations; lia).
  pose proof (mod_pow2_bound hold2 (bits2 mod 8) ltac:(lia)) as HB3.
  assert (MUF : munch (ifast_W SP Zs S OB osz) m m3).
  { eapply munch_trans; [eapply munch_weaken; [apply sub_fp_pro| exact MU1] | eapply munch_weaken; [apply sub_fp_body| exact MU3]]. }
  assert (WMF : wmono asegs m m3) by (eapply wmono_trans; eassumption).
  unfold ifast_post.
  assert (FIN : forall modeZ : Z, mode' = Z_to_bv 64 modeZ -> (modeZ = LEN \/ modeZ = TYPE \/ modeZ = BAD) ->
            exists (cin' cout' hold' bits' mode'0 : Z) (fo' : Z -> Z) (zmsg' t7 t8 t9 a0 a1 a8 a9 a10 a11 a12 a13 t10 t11 t12 t13 : word) (m' : amem),
              MS (mkR ra sp gp tp q0 q1 q2 s0 s1 r0 r1 r2 r3 r4 r5 r6 r7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6) FR (ret_pc ra) fc None m3 (seg_rom asegs) =
              MS (mkR ra sp gp tp t7 t8 t9 s0 s1 a0 a1 a8 a9 a10 a11 a12 a13 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t10 t11 t12 t13) FR (ret_pc ra) fc None m' (seg_rom asegs)
              /\ munch (ifast_W (bv_unsigned sp) Zs S OB osz) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
              /\ 0 <= cin' <= n /\ cout <= cout' <= osz /\ 0 <= bits' <= 7 /\ 0 <= hold' < 2 ^ bits' /\ bits' <= 8 * cin'
              /\ 8 * (n - cin') + bits' + (osz - cout') < 8 * (n - cin) + bits + (osz - cout)
              /\ 8 * (n - cin') + bits' <= 8 * (n - cin) + bits
              /\ (mode'0 = LEN \/ mode'0 = TYPE \/ mode'0 = BAD)
              /\ rw_cells asegs m' Zs (strm_cells (Z_to_bv 64 (D + cin')) (Z_to_bv 64 (n - cin')) zti (Z_to_bv 64 (OB + cout'))
                                                  (Z_to_bv 64 (osz - cout')) zto zmsg' (Z_to_bv 64 S) zalloc zfree zopq zdt zadl zres zp1 zp2 zp3)
              /\ rw_cells asegs m' S (istate_cells strm (Z_to_bv 64 mode'0) last wrap havedict flags dmax check total head wbits (Z_to_bv 64 wsz)
                                                   (Z_to_bv 64 whave) (Z_to_bv 64 wnext) (Z_to_bv 64 Wd) (Z_to_bv 64 hold') (Z_to_bv 64 bits') length_ offset extra
                                                   (Z_to_bv 64 la) (Z_to_bv 64 da) (Z_to_bv 64 lb) (Z_to_bv 64 db) ncode nlen ndist have next)
              /\ f8arr asegs m' OB (Z.to_nat osz) fo' /\ (forall i, 0 <= i < osz -> 0 <= fo' i < 256)).
  { intros modeZ EM MZ. subst mode'.
    exists (ci2 - bits2 / 8), co2, (hold2 mod 2 ^ (bits2 mod 8)), (bits2 mod 8), modeZ, fo3, msg3.
    exists q0, q1, q2, r0, r1, r2, r3, r4, r5, r6, r7, q3, q4, q5, q6, m3.
    split; [reflexivity|]. split; [exact MUF|]. split; [exact WMF|]. split; [exact MI3|]. split; [exact ST3|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HB3|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact MZ|].
    split; [exact STRM3|]. split; [exact SSC3|]. split; [exact OUT3| exact FOR3]. }
  destruct MODE' as [E|[E|E]].
  - apply (FIN LEN E). left. reflexivity.
  - apply (FIN TYPE E). right. left. reflexivity.
  - apply (FIN BAD E). right. right. reflexivity.
Qed.
End CANSEC1.
