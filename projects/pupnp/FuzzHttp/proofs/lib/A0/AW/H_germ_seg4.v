(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H_ListFind H_UpnpPrintf H2Kit.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import H_germ_seg1.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_3 : stack_malloc_stmt FI 3.
Hypothesis STACK_MALLOC_2 : stack_malloc_stmt FI 2.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Variables (P lo q kq kP : Z) (st : fsstate FI).
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).

Variables (meth rm sc isreq maj min A len cap cur csz : Z) (canary : word).

Variables (first last size flh fk ffree : Z) (hvs : list hv).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= q - GERM_DEPTH_A.
Hypothesis AL16 : q = 16 * kq.
Hypothesis QHI : q < 2^64.
Hypothesis Q63 : q < 2^63.
Hypothesis RF0 : RFAKE FI st m0.
Hypothesis FCO : fs_call_ok FI st tp 2.
Hypothesis FE0 : FSENV FI m0.

Local Notation F := (germF FI st).  Local Notation FL := (germFL FI st).  Local Notation SF := (germSF FI st).  Let st1 := fs_next FI st 3.

Notation WPg := [(P + 384, P + 400); (P + 440, P + 480); (ERRNO_G, ERRNO_G + 4)]%Z.

Notation W0c VWc := ((lo, q) :: FSIV (WPg ++ VWc))%Z.

Notation gshadow w1 w2 w3 :=
  ([C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
   C1 (Z_to_bv 8 w1); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
   C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2);
   C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2); C1 (Z_to_bv 8 w2);
   C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
   C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3);
   C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3); C1 (Z_to_bv 8 w3);
   C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).

Hypothesis PAL : P = 8 * kP.
Hypothesis PLO : 0x609000 <= P.
Hypothesis PHI : P + 504 <= alloc_ceiling.
Hypothesis SHWP : shw m0 P 504.
Hypothesis SHWCH : shw m0 A0_CHUNKED 8.
Hypothesis SHWERR : shw m0 ERRNO_G 4.
Hypothesis TPV : tp = Z_to_bv 64 6187376.
Hypothesis CURR : 0 <= cur <= len.
Hypothesis METHR : 0 <= meth <= 11.
Hypothesis RMR : 0 <= rm <= 11.
Hypothesis SCR : - 2^31 <= sc < 2^31.
Hypothesis ISR : 0 <= isreq <= 1.
Hypothesis ARNG : 0 <= A /\ A + cur < 2^64.

Notation GSTP pc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q') x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 F) (Z_to_bv 64 SF) x20 x21 x22 x23 x24 x25 (Z_to_bv 64 F) (Z_to_bv 64 2147450880)
           x28 x29 x30 x31)
      F_ (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Local Notation minvG := (H_germ_seg1.minvG FI P lo q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
Local Notation plbG := (H_germ_seg1.plbG FI P st).
Local Notation pinvG := (H_germ_seg1.pinvG P meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree).
Local Notation hview := (H_germ_seg1.hview P first hvs).
Local Notation hreg := (H_germ_seg1.hreg FI).
Local Notation hpure := (H_germ_seg1.hpure FI).
Local Notation vwc_ok := (H_germ_seg1.vwc_ok hvs).
Local Notation WEG := (H_germ_seg1.WEG FI lo q st).
Local Notation rframeG := (H_germ_seg1.rframeG FI lo q st).
Local Notation postG := (H_germ_seg1.postG FI P lo q st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0).
Local Notation hsafeW := (H_germ_seg1.hsafeW FI).
Local Notation hsafe_iv := (H_germ_seg1.hsafe_iv FI).
Local Notation vw_ok := (H_germ_seg1.vw_ok hvs).
Local Notation vw_ok_nil := (H_germ_seg1.vw_ok_nil hvs).

Hypothesis PLB : plbG.
Local Notation PLBv := (PLB : lb (fs_live FI st) P 504).
Hypothesis HPURE : forall h, In h hvs -> hpure h.

Hypothesis HAPART : forall h h', In h hvs -> In h' hvs ->
  (hvN h' + 24 <= hvA h \/ ru8G (hvA h + (hvCap h + 1)) <= hvN h') /\ (hvIt h' + 88 <= hvA h \/ ru8G (hvA h + (hvCap h + 1)) <= hvIt h')
  /\ ((hvA h = hvA h' /\ hvLen h = hvLen h' /\ hvCap h = hvCap h') \/ ru8G (hvA h' + (hvCap h' + 1)) <= hvA h \/ ru8G (hvA h + (hvCap h + 1)) <= hvA h').
Hypothesis HV0 : hview m0.

Hypothesis FEV : forall m, munch (W0c (hvW hvs)) m0 m -> wmono asegs m0 m -> FSENV FI m.

Local Notation geomG := (H_germ_seg1.geomG FI P st m0 A cur RF0 ARNG PLB).
Local Notation WPg_app := (H_germ_seg1.WPg_app P m0 A cur SHWP ARNG).
Local Notation WPg_out := (H_germ_seg1.WPg_out FI P m0 A cur SHWP ARNG).
Local Notation shwP_now := (H_germ_seg1.shwP_now FI P st m0 A cur RF0 SHWP ARNG PLB).
Local Notation liveG := (H_germ_seg1.liveG FI P st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_cons2 := (H_germ_seg1.sub_fp_cons2 meth rm sc isreq A len cur CURR METHR RMR SCR ISR ARNG).
Local Notation sub_fp_stk := (H_germ_seg1.sub_fp_stk FI P lo q A cur ARNG).
Local Notation sub_fp_F := (H_germ_seg1.sub_fp_F FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_SF := (H_germ_seg1.sub_fp_SF FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_ent := (H_germ_seg1.sub_fp_ent FI P lo q A cur ARNG).
Local Notation sub_fp_ctl := (H_germ_seg1.sub_fp_ctl FI P lo q A cur ARNG).
Local Notation sub_fp_errno := (H_germ_seg1.sub_fp_errno FI P lo q A cur ARNG).
Local Notation prologueG := (H_germ_seg1.prologueG FI STACK_MALLOC_3 P lo q kq st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 A cur CLO LO AL16 QHI Q63 RF0 FCO FE0 PLO PHI SHWP ARNG PLB).
Local Notation sub_fp_WEG := (H_germ_seg1.sub_fp_WEG FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation exitG := (H_germ_seg1.exitG FI SET_SHADOW_F5 P lo q kq st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 A cur CLO LO AL16 Q63 RF0 ARNG PLB).
Local Notation blockA := (H_germ_seg1.blockA FI P lo q kq kP st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree CLO LO AL16 RF0 PAL PLO PHI SHWP METHR RMR SCR ISR ARNG PLB).
Local Notation hview_frame := (H_germ_seg1.hview_frame FI P A cur first hvs ARNG HPURE).
Local Notation hsafe_of := (H_germ_seg1.hsafe_of FI A cur ARNG).
Local Notation hsafe_W0 := (H_germ_seg1.hsafe_W0 FI P lo q st m0 A cur CLO RF0 ARNG PLB).
Local Notation hview_now0 := (H_germ_seg1.hview_now0 FI P lo q st m0 A cur first hvs CLO RF0 ARNG PLB HPURE HV0).
Local Notation W0c_fsw := (H_germ_seg1.W0c_fsw FI P lo q st m0 A cur hvs CLO RF0 ARNG PLB HPURE).

Ltac mv_tacG := unfold H_germ_seg1.minvG; split; [eexists; eassumption|]; split; [assumption|];
  repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]); eexists; split; eassumption.

Ltac pv_tacG := unfold H_germ_seg1.pinvG; split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|];
  split; [eassumption|]; split; [eassumption| eassumption].

Ltac shwP_here SHWPs MU0 N :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    first [ lazymatch goal with H : shw mm P 504 |- _ => idtac end
          | (try clear N); assert (N : shw mm P 504) by (eapply (shw_frame WPg); [exact SHWPs| exact MU0| exact WPg_app]) ] end.

Ltac wPA SHWPs MU0 N pc :=
  repeat first [ (is_ms; tryif at_pc pc then fail else (shwP_here SHWPs MU0 N; cstep)) | (is_if; br_auto) ].

Definition linvG (vbs vbs' : list byte) (i : nat) : Prop :=
  length vbs' = length vbs /\ (forall j, (i <= j)%nat -> nth_error vbs' j = nth_error vbs j)
  /\ (forall j b, (j < i)%nat -> nth_error vbs' j = Some b -> bv_unsigned b <> 0)
  /\ (forall j, nth_error vbs j = Some zbG -> nth_error vbs' j = Some zbG).

#[using="A cur ARNG"] Lemma le1_smallG : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.
#[using="A cur ARNG"] Lemma to_lower_nzG : forall c, 0 < c < 256 -> 0 < to_lower c < 256.
Proof. intros c Hc. unfold to_lower, is_upper. destruct (_ && _)%bool eqn:E; [apply andb_true_iff in E; destruct E as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2|]; lia. Qed.

#[using="IC A cur ARNG HPURE"] Lemma te_loopA : forall (h : hv) (vbs str rest : list byte) (m : mem) (Q : machine_state -> Prop) q' x21 x22,
  In h hvs -> vbs = str ++ zbG :: rest -> ~ In zbG str -> Z.of_nat (length vbs) = hvCap h + 1 ->
  shw m (hvA h) (hvCap h + 1) ->
  (forall m' vbs' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y23 y25 y28 y29 y30 y31,
     u8arr asegs m' (hvA h) vbs' -> linvG vbs vbs' (length str) -> mem_inv asegs m' ->
     munch [(hvA h, hvA h + (hvCap h + 1))]%Z m m' -> wmono asegs m m' ->
     evt asegs Q (GSTP 0x895e8 q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 P) x21 x22 y23 (Z_to_bv 64 (hvA h)) y25 y28 y29 y30 y31 m')) ->
  forall (k i : nat) (vbs' : list byte) (bc : byte) (m' : mem) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  (length str - i < k)%nat -> (i < length str)%nat -> nth_error vbs i = Some bc ->
  munch [(hvA h, hvA h + (hvCap h + 1))]%Z m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  u8arr asegs m' (hvA h) vbs' -> linvG vbs vbs' i ->
  evt asegs Q (GSTP 0x89588 q' x1 x5 x6 x7 (Z_to_bv 64 (bv_unsigned bc)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) x21 x22
                 (Z_to_bv 64 (hvA h + Z.of_nat i + 1)) (Z_to_bv 64 (hvA h)) (Z_to_bv 64 (hvA h + Z.of_nat i)) x28 x29 x30 x31 m').
Proof.
  intros h vbs str rest m Q q' x21 x22 Hh EV NI LVB SHV KX k.
  destruct (HPURE h Hh) as (LC & CAPB & _ & _ & (RV1 & RV2 & RV3 & RV4)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (APV : app_ivs [(hvA h, hvA h + (hvCap h + 1))]%Z).
  { unfold app_ivs. apply Forall_cons; [| apply Forall_nil]. unfold app_iv, SH_HI. cbn [fst snd]. clear - RV1 RV4. lia. }
  assert (LS : (length str < length vbs)%nat) by (rewrite EV, length_app; cbn [length]; lia).
  induction k as [|k IH]; intros i vbs' bc m' x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK HI Hbc MUb WMb MI' WB LI; [lia|].
  pose proof LI as (LL & LGE & LLT & LZ). pose proof (byte_lt256 bc) as BR.
  set (f := length str) in *.
  assert (FZ : nth_error vbs f = Some zbG). { rewrite EV. rewrite nth_error_app2 by lia. subst f. rewrite Nat.sub_diag. reflexivity. }
  assert (CNZ : bv_unsigned bc <> 0).
  { intros E0. apply NI. assert (bc = zbG) as <- by (apply bv_eq; rewrite E0; reflexivity).
    rewrite EV, nth_error_app1 in Hbc by lia. eapply nth_error_In. exact Hbc. }
  pose proof (to_lower_nzG (bv_unsigned bc) ltac:(lia)) as TL.
  destruct (nth_error vbs (S i)) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. lia. }
  pose proof (byte_lt256 b1) as BR1.
  assert (Hb1' : nth_error vbs' (S i) = Some b1) by (rewrite (LGE (S i)) by lia; exact Hb1).
  assert (SHWc : shw m' (hvA h) (hvCap h + 1)) by (eapply shw_frame; [exact SHV| exact MUb| exact APV]).
  zstep.
  replace (Z.land (bv_unsigned bc) 255) with (bv_unsigned bc) by (change 255%Z with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  step.
  eapply evt_cut; [eapply (ic_tolower IC) with (c := bv_unsigned bc); [lia| reflexivity| exact MI']|].
  intros msT PT. unfold leaf_post in PT. destruct PT as (e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & e12 & e13 & -> & _ & _ & _).
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  step. step.
  assert (CONT1 : forall y11 y12, evt asegs Q (GSTP 0x895a0 q' (Z_to_bv 64 562576) e0 e1 e2 (Z_to_bv 64 (to_lower (bv_unsigned bc))) y11 y12 e5 e6 e7 e8 e9 (Z_to_bv 64 P) x21 x22
                 (Z_to_bv 64 (hvA h + Z.of_nat i + 1)) (Z_to_bv 64 (hvA h)) (Z_to_bv 64 (hvA h + Z.of_nat i)) e10 e11 e12 e13 m')).
  { intros y11 y12.
    pose proof (u8arr_store_ok asegs _ _ _ (Z.of_nat i) (Z_to_bv 64 (hvA h + Z.of_nat i + 1 + -1)) WB ltac:(rewrite LL; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    rewrite (le1_smallG (to_lower (bv_unsigned bc))) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?e) ?x) _) =>
      replace (write_to_mem mm (Z_to_bv 64 e) x) with (write_to_mem mm (wa (hvA h + Z.of_nat i)) x) by (unfold wa; f_equal; f_equal; lia) end.
    pose proof (u8arr_write asegs _ _ _ (Z.of_nat i) (Z_to_bv 8 (to_lower (bv_unsigned bc))) WB ltac:(rewrite LL; lia)) as WB2. clear WB. store_done.
    rewrite Nat2Z.id in WB2. set (vbs2 := upd vbs' i (Z_to_bv 8 (to_lower (bv_unsigned bc)))) in WB2.
    assert (LI2 : linvG vbs vbs2 (S i)).
    { subst vbs2. split; [| split; [| split]].
      - rewrite upd_length. exact LL.
      - intros j Hj. rewrite nth_error_upd_other by lia. apply LGE. lia.
      - intros j b Hj Hb. destruct (Nat.eq_dec j i) as [->|NE].
        + rewrite nth_error_upd_same in Hb by (rewrite LL; lia). injection Hb as <-. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256%Z. rewrite Z.mod_small by lia. lia.
        + rewrite nth_error_upd_other in Hb by lia. exact (LLT j b ltac:(lia) Hb).
      - intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [rewrite Hbc in Hj; injection Hj as E0; exfalso; apply CNZ; rewrite E0; reflexivity|].
        rewrite nth_error_upd_other by lia. apply LZ. exact Hj. }
    clearbody vbs2. clear LI LL LGE LLT LZ SHWc.
    assert (SHWc : shw m1 (hvA h) (hvCap h + 1)) by (eapply shw_frame; [exact SHV| exact MUb| exact APV]).
    zstep. step. step.
    assert (CONT2 : forall y10 z12, evt asegs Q (GSTP 0x895b8 q' (Z_to_bv 64 562576) e0 e1 e2 y10 (Z_to_bv 64 (hvA h + Z.of_nat i + 1)) z12 e5 e6 e7 e8 e9 (Z_to_bv 64 P) x21 x22
                   (Z_to_bv 64 (hvA h + Z.of_nat i + 1)) (Z_to_bv 64 (hvA h)) (Z_to_bv 64 (hvA h + Z.of_nat i)) e10 e11 e12 e13 m1)).
    { intros y10 z12.
      assert (Hb2 : nth_error vbs2 (S i) = Some b1) by (destruct LI2 as (_ & LGE2 & _); rewrite (LGE2 (S i)) by lia; exact Hb1).
      pose proof (u8arr_read asegs _ _ vbs2 (Z.of_nat (S i)) b1 (Z_to_bv 64 (hvA h + Z.of_nat i + 1)) WB2 ltac:(rewrite Nat2Z.id; exact Hb2) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. cbv beta. zstep. zstep.
      zstep. if_cases K0; zify_cond K0.
      -
        assert (S i <> f). { intros E. rewrite E, FZ in Hb1. injection Hb1 as <-. apply K0. reflexivity. }
        replace (hvA h + Z.of_nat i + 2) with (hvA h + Z.of_nat (S i) + 1) by lia.
        replace (hvA h + Z.of_nat i + 1) with (hvA h + Z.of_nat (S i)) by lia.
        eapply (IH (S i) vbs2 b1 m1); [lia| lia| exact Hb1| exact MUb| exact WMb| exact MI'| exact WB2| exact LI2].
      -
        assert (EF : S i = f).
        { destruct (Nat.eq_dec (S i) f) as [E|NE]; [exact E|]. exfalso. assert (S i < f)%nat as LT by lia.
          rewrite EV, nth_error_app1 in Hb1 by lia. apply NI. assert (b1 = zbG) as <- by (apply bv_eq; rewrite K0; reflexivity). eapply nth_error_In. exact Hb1. }
        rewrite EF in LI2.
        zstep.
        eapply KX; [exact WB2| exact LI2| exact MI'| exact MUb| exact WMb]. }
    chkbN 10 (hvA h + Z.of_nat i + 1) SHWc kk2 SHRk2 Hk2.
    destruct Hk2 as [-> | [G1 G2]].
    - step. step. lit_branch. apply CONT2.
    - step. rewrite (sxb_small kk2) by lia.
      step. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep.
      step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONT2. }
  chkbN 11 (hvA h + Z.of_nat i) SHWc kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT1.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT1.
Qed.

Definition VW1 (h : hv) : list ivl := [(hvA h, hvA h + (hvCap h + 1))]%Z.
Definition blockCf_stmt : Prop :=
  forall (h : hv) q' m v0 v8 v16 v24 eb el errw hackw posw entpw clenw espw
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31,
  In h hvs -> minvG [] q' m 248 248 0 v0 v8 v16 v24 -> pinvG m eb el errw hackw posw entpw clenw espw -> hview m ->
  forall (Q : machine_state -> Prop),

  (forall m' w0 w8 w16 w24 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y23 y24 y25 y28 y29 y30 y31,
     minvG (VW1 h) q' m' 248 248 248 w0 w8 w16 w24 -> pinvG m' eb el errw hackw posw (wz 3) clenw espw -> hview m' ->
     evt asegs Q (GSTP 0x89370 q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 6) y21 y22 y23 y24 y25 y28 y29 y30 y31 m')) ->

  (forall m' w0 w8 w16 w24 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y25 y28 y29 y30 y31,
     minvG (VW1 h) q' m' 248 248 248 w0 w8 w16 w24 -> pinvG m' eb el errw hackw posw entpw clenw espw -> hview m' ->
     evt asegs Q (GSTP 0x896a4 q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) (Z_to_bv 64 (P + 288)) y24 y25 y28 y29 y30 y31 m')) ->
  evt asegs Q (GSTP 0x894c4 q' x1 x5 x6 x7 (Z_to_bv 64 (hvN h)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) (Z_to_bv 64 (P + 288)) x24 x25 x28 x29 x30 x31 m).

#[using="A cur ARNG"] Lemma sub_fp_vw : forall VWc, vw_ok VWc -> sub_fp (W0c VWc) (W0c (hvW hvs)).
Proof.
  intros VWc OK xo Ho. cbn [app outside] in *. destruct Ho as (H1 & H2 & H3 & H4 & H5 & H6 & HV).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  clear H1 H2 H3 H4 H5 H6. induction VWc as [|[a b] VWc IH]; cbn [outside]; [exact I|].
  inversion_clear OK as [|? ? (h & Hh & A1 & A2) OK']. cbn [fst snd] in A1, A2. split; [| exact (IH OK')].
  intros Hx. assert (OUT : outside (hvW hvs) xo -> ~ (hvA h <= xo < hvA h + (hvCap h + 1))).
  { clear - Hh. unfold hvW. induction hvs as [|h' l IHl]; [destruct Hh|]. cbn [map outside]. intros (O1 & O2).
    destruct Hh as [->|Hh]; [exact O1| exact (IHl Hh O2)]. }
  apply (OUT HV). lia.
Qed.
#[using="A cur ARNG"] Lemma vw_ok_1 : forall h, In h hvs -> vw_ok (VW1 h).
Proof. intros h Hh. unfold H_germ_seg1.vw_ok, VW1. apply Forall_cons; [exists h; cbn [fst snd]; split; [exact Hh| lia]| apply Forall_nil]. Qed.

#[using="Type"] Lemma hv_eq_dec : forall a b : hv, {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Qed.

#[using="A cur ARNG HPURE"] Lemma hview_upd : forall (h0 : hv) W m m', In h0 hvs -> hview m -> munch W m m' -> wmono asegs m m' -> Forall (fsw_iv FI) W ->
  (forall h, In h hvs -> disjoint_from W (hvN h) 24 /\ disjoint_from W (hvIt h) 88) ->
  (forall h, In h hvs -> (hvA h = hvA h0 /\ hvLen h = hvLen h0 /\ hvCap h = hvCap h0) \/ disjoint_from W (hvA h) (ru8G (hvA h + (hvCap h + 1)) - hvA h)) ->
  disjoint_from W (hvA h0 + (hvCap h0 + 1)) (ru8G (hvA h0 + (hvCap h0 + 1)) - (hvA h0 + (hvCap h0 + 1))) ->
  (exists vbs', rw_cells asegs m' (hvA h0) [CB (Z.to_nat (hvCap h0 + 1)) vbs'] /\ nth_error vbs' (Z.to_nat (hvLen h0)) = Some zbG) ->
  hview m'.
Proof.
  intros h0 W m m' Hh0 (LS & HI) MU WM FSW DJN DJV DJS NEWV. split.
  - eapply lsegA_transport; [exact LS| exact MU| exact WM|].
    intros N it id Hin. apply in_map_iff in Hin as (h & E & Hh). unfold hv3 in E. injection E as <- <- <-.
    destruct (DJN h Hh) as [D1 D2]. split; [exact D1| eapply disjoint_from_sub; [exact D2| lia| lia]].
  - intros h Hh. destruct (HI h Hh) as ((N1 & N2 & N3 & N4) & (I1 & I2 & I3 & I4) & VC & SHV & (vbs & VB & VN) & (sl & SL & SE)).
    destruct (HPURE h Hh) as (LC & CAPB & RN & RI & RV). destruct (DJN h Hh) as [D1 D2].
    pose proof (ru8G_spec (hvA h + (hvCap h + 1))) as (U3 & _).
    pose proof RN as (_ & _ & FN & _). pose proof RI as (_ & _ & FI2 & _). pose proof RV as (_ & _ & FV & _).
    split. { split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. apply (shw_frame_fs FI W m m' _ _ N4 MU FSW). clear - FN. lia. }
    split. { split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. apply (shw_frame_fs FI W m m' _ _ I4 MU FSW). clear - FI2. lia. }
    split. { eapply rw_cells_transport; [exact VC| exact MU| exact WM|]. unfold mbuf_cells. cbn [cells_size csize Nat.add].
             eapply disjoint_from_sub; [exact D2| lia| lia]. }
    split. { apply (shw_frame_fs FI W m m' _ _ SHV MU FSW). clear - FV. lia. }
    destruct (DJV h Hh) as [(E1 & E2 & E3)|D3].
    + rewrite E1, E2, E3 in *. split; [exact NEWV|]. exists sl. split; [| exact SE]. eapply bytes_at_transport; [exact SL| exact MU|].
      eapply disjoint_from_sub; [exact DJS| lia| lia].
    + split. { exists vbs. split; [| exact VN]. eapply rw_cells_transport; [exact VB| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
               eapply disjoint_from_sub; [exact D3| lia| lia]. }
      exists sl. split; [| exact SE]. eapply bytes_at_transport; [exact SL| exact MU|].
      eapply disjoint_from_sub; [exact D3| lia| lia].
Qed.

End W.
