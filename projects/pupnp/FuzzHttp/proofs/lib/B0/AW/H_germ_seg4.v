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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H_ListFind H_UpnpPrintf H2Kit AWUb.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import H_germ_seg1.

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
Hypothesis Q47 : q <= 2^47 - 64.
Hypothesis SHZ : shz m0 (sh lo) (sh q).
Hypothesis SHR : shr m0 (sh lo - sh lo mod 8) (sh q + 8).
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
Hypothesis TPV : tp = Z_to_bv 64 6190512.
Hypothesis CURR : 0 <= cur <= len.
Hypothesis METHR : 0 <= meth <= 11.
Hypothesis RMR : 0 <= rm <= 11.
Hypothesis SCR : - 2^31 <= sc < 2^31.
Hypothesis ISR : 0 <= isreq <= 1.
Hypothesis ARNG : 0 <= A /\ A + cur < 2^64.
Hypothesis ANZ : 0 < cur -> 0 < A.

Notation GSTP pc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q') x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 SF) (Z_to_bv 64 F) x20 x21 x22 (Z_to_bv 64 F) (Z_to_bv 64 2147450880) x25 s10 s11
           x28 x29 x30 x31)
      F_ (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Local Notation minvG := (H_germ_seg1.minvG FI P lo q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m0).
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

Local Notation geomG := (H_germ_seg1.geomG FI P lo st m0 A cur RF0 ARNG PLB).
Local Notation WPg_app := (H_germ_seg1.WPg_app P lo m0 A cur SHWP ARNG).
Local Notation WPg_out := (H_germ_seg1.WPg_out FI P lo m0 A cur SHWP ARNG).
Local Notation shwP_now := (H_germ_seg1.shwP_now FI P lo st m0 A cur RF0 SHWP ARNG PLB).
Local Notation liveG := (H_germ_seg1.liveG FI P lo st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_cons2 := (H_germ_seg1.sub_fp_cons2 meth rm sc isreq A len cur CURR METHR RMR SCR ISR ARNG).
Local Notation sub_fp_stk := (H_germ_seg1.sub_fp_stk FI P lo q A cur ARNG).
Local Notation sub_fp_F := (H_germ_seg1.sub_fp_F FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_SF := (H_germ_seg1.sub_fp_SF FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation sub_fp_ent := (H_germ_seg1.sub_fp_ent FI P lo q A cur ARNG).
Local Notation sub_fp_ctl := (H_germ_seg1.sub_fp_ctl FI P lo q A cur ARNG).
Local Notation sub_fp_errno := (H_germ_seg1.sub_fp_errno FI P lo q A cur ARNG).
Local Notation prologueG := (H_germ_seg1.prologueG FI STACK_MALLOC_3 P lo q kq st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 A cur CLO LO AL16 QHI Q47 RF0 FCO FE0 ARNG PLB).
Local Notation sub_fp_WEG := (H_germ_seg1.sub_fp_WEG FI P lo q st m0 A cur RF0 ARNG PLB).
Local Notation exitG := (H_germ_seg1.exitG FI SET_SHADOW_F5 P lo q kq st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 A cur CLO LO AL16 Q47 RF0 ARNG PLB).
Local Notation blockA := (H_germ_seg1.blockA FI P lo q kq kP st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 meth rm sc isreq maj min A len cap cur csz canary first last size flh fk ffree CLO LO AL16 RF0 PAL PLO PHI SHWP CURR METHR RMR SCR ISR ARNG ANZ PLB).
Local Notation hview_frame := (H_germ_seg1.hview_frame FI P lo A cur first hvs ARNG HPURE).
Local Notation hsafe_of := (H_germ_seg1.hsafe_of FI lo A cur ARNG).
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

Ltac wPAU SHWPs MU0 N pc :=
  repeat first [ (is_ms; tryif at_pc pc then fail else (shwP_here SHWPs MU0 N; cstep)) | (has_b2z_if; ub_b2z; lit_branch_safe) | (is_if; first [ br_auto | ubr2 | ubr3 ]) ].

Definition linvG (vbs vbs' : list byte) (i : nat) : Prop :=
  length vbs' = length vbs /\ (forall j, (i <= j)%nat -> nth_error vbs' j = nth_error vbs j)
  /\ (forall j b, (j < i)%nat -> nth_error vbs' j = Some b -> bv_unsigned b <> 0)
  /\ (forall j, nth_error vbs j = Some zbG -> nth_error vbs' j = Some zbG).

#[using="lo A cur ARNG"] Lemma le1_smallG : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.
#[using="lo A cur ARNG"] Lemma to_lower_nzG : forall c, 0 < c < 256 -> 0 < to_lower c < 256.
Proof. intros c Hc. unfold to_lower, is_upper. destruct (_ && _)%bool eqn:E; [apply andb_true_iff in E; destruct E as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2|]; lia. Qed.

Notation RSTP pc p x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
      F_ (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

#[using="FI IC lo A cur ARNG HPURE"] Lemma te_loopB : forall (h : hv) (vbs str rest : list byte) (m : mem) (Q : machine_state -> Prop) (p MP kM : Z) (x18 x23 : word),
  In h hvs -> vbs = str ++ zbG :: rest -> ~ In zbG str -> Z.of_nat (length vbs) = hvCap h + 1 ->
  shw m (hvA h) (hvCap h + 1) -> shw m MP 16 -> alloc_ceiling <= MP -> MP + 16 <= 2^47 -> MP = 8 * kM ->
  (forall m' vbs' y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y25 y28 y29 y30 y31,
     u8arr asegs m' (hvA h) vbs' -> linvG vbs vbs' (length str) -> mem_inv asegs m' ->
     rw_cells asegs m' MP [C8 (Z_to_bv 64 (hvA h)); C8 (Z_to_bv 64 (hvLen h))] ->
     munch [(hvA h, hvA h + (hvCap h + 1))]%Z m m' -> wmono asegs m m' ->
     evt asegs Q (RSTP 0x89e74 p y1 y5 y6 y7 (Z_to_bv 64 MP) x18 y10 (Z_to_bv 64 (hvA h)) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (MP + 8)) (Z_to_bv 64 (hvA h + Z.of_nat (length str)))
                  (Z_to_bv 64 (MP ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((MP + 8) ≫ 3 + 2147450880)) x23 (Z_to_bv 64 (Z.of_nat (length str))) y25 y28 y29 y30 y31 m')) ->
  forall (k i : nat) (vbs' : list byte) (m' : mem) (s3v : Z) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31,
  (length str - i < k)%nat -> (i <= length str)%nat ->
  munch [(hvA h, hvA h + (hvCap h + 1))]%Z m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  rw_cells asegs m' MP [C8 (Z_to_bv 64 (hvA h)); C8 (Z_to_bv 64 (hvLen h))] ->
  u8arr asegs m' (hvA h) vbs' -> linvG vbs vbs' i -> s3v = hvA h + Z.of_nat i ->
  evt asegs Q (RSTP 0x89de8 p x1 x5 x6 x7 (Z_to_bv 64 MP) x18 (Z_to_bv 64 1) (Z_to_bv 64 (hvA h)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (MP + 8)) (Z_to_bv 64 s3v)
                 (Z_to_bv 64 (MP ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((MP + 8) ≫ 3 + 2147450880)) x23 (Z_to_bv 64 (Z.of_nat i)) x25 x28 x29 x30 x31 m').
Proof.
  intros h vbs str rest m Q p MP kM x18 x23 Hh EV NI LVB SHV SHM MPLO MPHI MPAL KX k.
  destruct (HPURE h Hh) as (LC & CAPB & _ & _ & (RV1 & RV2 & RV3 & RV4)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (APV : app_ivs [(hvA h, hvA h + (hvCap h + 1))]%Z).
  { unfold app_ivs. apply Forall_cons; [| apply Forall_nil]. unfold app_iv, SH_HI. cbn [fst snd]. clear - RV1 RV4. lia. }
  assert (LS : (length str < length vbs)%nat) by (rewrite EV, length_app; cbn [length]; lia).
  induction k as [|k IH]; intros i vbs' m' s3v x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 HK HI MUb WMb MI' MPC WB LI ES3; [lia|]. subst s3v.
  pose proof LI as (LL & LGE & LLT & LZ).
  set (f := length str) in *.
  assert (FZ : nth_error vbs f = Some zbG). { rewrite EV. rewrite nth_error_app2 by lia. subst f. rewrite Nat.sub_diag. reflexivity. }
  destruct (nth_error vbs i) as [bc|] eqn:Hbc. 2:{ exfalso. apply nth_error_None in Hbc. lia. }
  pose proof (byte_lt256 bc) as BR.
  assert (Hbc' : nth_error vbs' i = Some bc) by (rewrite (LGE i) by lia; exact Hbc).
  assert (SHWc : shw m' (hvA h) (hvCap h + 1)) by (eapply shw_frame; [exact SHV| exact MUb| exact APV]).
  assert (SHMc : shw m' MP 16) by (eapply shw_frame; [exact SHM| exact MUb| exact APV]).
  zstep.
  step. lit_branch.
  zstep. zstep.
  gen2 CONT1 0x89e00 10%nat 12%nat.
  2:{ chkbN 25 (hvA h + Z.of_nat i) SHWc kk SHRk Hk.
      destruct Hk as [-> | [G1 G2]].
      - step. step. lit_branch. apply CONT1.
      - step. rewrite (sxb_small kk) by lia.
        step. if_cases G3; zify_cond G3; [| exfalso; lia].
        zstep.
        step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
        apply CONT1. }
  intros yi yj.
  pose proof (u8arr_read asegs _ _ vbs' (Z.of_nat i) bc (Z_to_bv 64 (hvA h + Z.of_nat i)) WB ltac:(rewrite Nat2Z.id; exact Hbc') ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. cbv beta. clear RD.
  zstep. if_cases K0; zify_cond K0.
  -
    assert (EF : i = f).
    { destruct (Nat.eq_dec i f) as [E|NE]; [exact E|]. exfalso. assert (i < f)%nat as LT by lia.
      rewrite EV, nth_error_app1 in Hbc by lia. apply NI. assert (bc = zbG) as <- by (apply bv_eq; rewrite K0; reflexivity). eapply nth_error_In. exact Hbc. }
    rewrite EF in *. subst f.
    eapply KX; [exact WB| exact LI| exact MI'| exact MPC| exact MUb| exact WMb].
  - assert (IF : (i < f)%nat).
    { destruct (Nat.eq_dec i f) as [E|NE]; [| lia]. exfalso. rewrite E, FZ in Hbc. injection Hbc as <-. apply K0. reflexivity. }
    pose proof (to_lower_nzG (bv_unsigned bc) ltac:(lia)) as TL.
    step.
    eapply evt_cut; [eapply (ic_tolower IC) with (c := bv_unsigned bc); [lia| reflexivity| exact MI']|].
    intros msT PT. unfold leaf_post in PT. destruct PT as (e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & e12 & e13 & -> & _ & _ & _).
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    gen2 CONT2 0x89e14 11%nat 12%nat.
    2:{ chkbN 25 (hvA h + Z.of_nat i) SHWc kk SHRk Hk.
        destruct Hk as [-> | [G1 G2]].
        - step. step. lit_branch. apply CONT2.
        - step. rewrite (sxb_small kk) by lia.
          step. if_cases G3; zify_cond G3; [| exfalso; lia].
          zstep.
          step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
          apply CONT2. }
    intros zi zj.
    zstep.
    rewrite swrap32_id by (clear - IF LS LVB CAPB; lia).
    pose proof (u8arr_store_ok asegs _ _ _ (Z.of_nat i) (Z_to_bv 64 (hvA h + Z.of_nat i + 0)) WB ltac:(rewrite LL; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    rewrite (le1_smallG (to_lower (bv_unsigned bc))) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?e) ?x) _) =>
      replace (write_to_mem mm (Z_to_bv 64 e) x) with (write_to_mem mm (wa (hvA h + Z.of_nat i)) x) by (unfold wa; f_equal; f_equal; lia) end.
    pose proof (u8arr_write asegs _ _ _ (Z.of_nat i) (Z_to_bv 8 (to_lower (bv_unsigned bc))) WB ltac:(rewrite LL; lia)) as WB2. clear WB. store_done.
    rewrite Nat2Z.id in WB2. set (vbs2 := upd vbs' i (Z_to_bv 8 (to_lower (bv_unsigned bc)))) in WB2.
    assert (CNZ : bv_unsigned bc <> 0) by exact K0.
    assert (LI2 : linvG vbs vbs2 (S i)).
    { subst vbs2. split; [| split; [| split]].
      - rewrite upd_length. exact LL.
      - intros j Hj. rewrite nth_error_upd_other by lia. apply LGE. lia.
      - intros j b Hj Hb. destruct (Nat.eq_dec j i) as [->|NE].
        + rewrite nth_error_upd_same in Hb by (rewrite LL; lia). injection Hb as <-. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256%Z. rewrite Z.mod_small by lia. lia.
        + rewrite nth_error_upd_other in Hb by lia. exact (LLT j b ltac:(lia) Hb).
      - intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [rewrite Hbc in Hj; injection Hj as E0; exfalso; apply CNZ; rewrite E0; reflexivity|].
        rewrite nth_error_upd_other by lia. apply LZ. exact Hj. }
    clearbody vbs2. clear LI LL LGE LLT LZ SHWc SHMc.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHMc : shw mm MP 16) by (eapply shw_frame; [exact SHM| exact MUb| exact APV]) end.
    step. ubr_by ltac:(rewrite ?signed_lit in KU by lia; lia).
    chk8N 20 MP SHMc. step. lit_branch.
    step.
    step.
    zstep. zstep.
    ub_b2z. step. lit_branch_safe.
    zstep. zstep. zstep. zstep.
    assert (SLT : forall x, 0 <= x < 2^63 -> (Z.lxor x 9223372036854775808 <? 9223372036854775808) = false)
      by (intros x Hx; change 9223372036854775808 with (2^63); rewrite zb_lxor_pow2_small by lia; apply Z.ltb_ge; lia).
    rewrite ?SLT by lia. clear SLT. ub_b2z. cbn [Z.b2z]. change (Z.lxor (Z.lxor 0 0) 1) with 1.
    step.
    step. lit_branch_safe.
    replace (hvA h + (Z.of_nat i + 1)) with (hvA h + Z.of_nat (S i)) by lia.
    replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
    eapply (IH (S i) vbs2 m1 _); [lia| lia| exact MUb| exact WMb| exact MI'| exact MPC| exact WB2| exact LI2| reflexivity].
Qed.

#[using="IC kq A cur CLO LO AL16 QHI Q47 ARNG HPURE"] Lemma rfsB : forall (h : hv) (vbs sl : list byte) (kE ret q' kq' : Z) (m : mem) (Q : machine_state -> Prop)
    x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x28 x29 x30 x31,
  In h hvs -> q + -144 <= q' <= q + -128 -> q' = 32 * kq' -> ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
  stk asegs m lo q' -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m (q' + 24) [C8 (Z_to_bv 64 (hvA h)); C8 (Z_to_bv 64 (hvLen h))] ->
  rw_cells asegs m (hvA h) [CB (Z.to_nat (hvCap h + 1)) vbs] -> nth_error vbs (Z.to_nat (hvLen h)) = Some zbG ->
  bytes_at asegs m (hvA h + (hvCap h + 1)) sl -> hvA h + (hvCap h + 1) + Z.of_nat (length sl) = 8 * kE -> Z.of_nat (length sl) <= 8 ->
  shw m (hvA h) (hvCap h + 1) -> shw m (q' + 24) 16 -> shw m A0_CHUNKED 8 ->
  rw_cells asegs m got_sspG [C8 (wz ssp_guardG)] -> rw_cells asegs m ssp_guardG [C8 canary] ->
  (forall m' vbs' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     munch [(lo, q'); (hvA h, hvA h + (hvCap h + 1))]%Z m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo q' -> asan_env asegs m' ->
     rw_cells asegs m' (q' + 24) [C8 (Z_to_bv 64 (hvA h)); C8 (Z_to_bv 64 (hvLen h))] ->
     rw_cells asegs m' (hvA h) [CB (Z.to_nat (hvCap h + 1)) vbs'] -> nth_error vbs' (Z.to_nat (hvLen h)) = Some zbG ->
     rw_cells asegs m' got_sspG [C8 (wz ssp_guardG)] -> rw_cells asegs m' ssp_guardG [C8 canary] ->
     evt asegs Q (GSTP ret q' (Z_to_bv 64 ret) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x20 x21 x22 x25 y28 y29 y30 y31 m')) ->
  evt asegs Q (GSTP 0x89d24 q' (Z_to_bv 64 ret) x5 x6 x7 (Z_to_bv 64 (q' + 24)) (Z_to_bv 64 A0_CHUNKED) x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros Hh Hq Hq32 ERET ST MI AG MPC VB VN SL SE SLL SHV SHM SHWC PGOT PCAN K.
  destruct (HPURE h Hh) as (LC & CAPB & _ & _ & RV). unfold H_germ_seg1.hreg in RV.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AG as AE. apply asan_env_globals in AG. ag_split AG.
  pose proof (munch_refl [(lo, q'); (hvA h, hvA h + (hvCap h + 1))]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  carve_frame 96%nat ST.
  step. do 11 (step; fix_lit_store).
  ub_null.
  step.
  assert (MPM : (q' + 24) mod 8 = 0) by (clear - Hq32; Z.div_mod_to_equations; lia).
  ub_align. clear MPM.
  step. step. step.
  assert (APV : app_ivs [(lo, q'); (hvA h, hvA h + (hvCap h + 1))]%Z).
  { apply Forall_cons; [apply app_iv_stack; exact CLO|]. apply Forall_cons; [| apply Forall_nil]. unfold app_iv, SH_HI. cbn [fst snd]. clear - RV. lia. }
  zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHM1 : shw mm (q' + 24) 16) by (eapply shw_frame; [exact SHM| exact MU0| exact APV]) end.
  chk8N 20 (q' + 24) SHM1. step. lit_branch.
  step. zstep. zstep.
  chk8N 22 (q' + 24 + 8) SHM1. step. lit_branch.
  step.
  step. step.
  step.
  step. ubr.
  zstep. zstep. zstep. ub_b2z. step. lit_branch_safe.
  ub_null.
  zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHV1 : shw mm (hvA h) (hvCap h + 1)) by (eapply shw_frame; [exact SHV| exact MU0| exact APV]) end.
  gen2 CONT 0x89dcc 11%nat 12%nat.
  2:{ chkbN 11 (hvA h + hvLen h) SHV1 kk SHRk Hk.
      destruct Hk as [-> | [G1 G2]].
      - step. step. lit_branch. apply CONT.
      - step. rewrite (sxb_small kk) by lia.
        step. if_cases G3; zify_cond G3; [| exfalso; lia].
        zstep.
        step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
        apply CONT. }
  intros yi yj.
  chk8N 20 (q' + 24) SHM1. step. lit_branch.
  step.
  step.
  pose proof (u8arr_read asegs _ _ vbs (hvLen h) zbG (Z_to_bv 64 (hvA h + hvLen h)) (u8arr_of_rw_cells asegs _ _ _ _ VB) VN ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. cbv beta. clear RD.
  zstep. ub_b2z.
  step.
  pose proof VN as VN2. apply List.nth_error_split in VN2 as (l1 & l2 & EV0 & LL1).
  assert (NS : exists str rest, vbs = str ++ zbG :: rest /\ ~ In zbG str /\ (length str <= length l1)%nat).
  { rewrite EV0. clear. induction l1 as [|a l IH]; [exists [], l2; split; [reflexivity|]; split; [intros []| cbn; lia]|].
    destruct (bv_eq_dec 8 a zbG) as [->|NE]; [exists [], (l ++ zbG :: l2); split; [reflexivity|]; split; [intros []| cbn; lia]|].
    destruct IH as (s & r & E & NIs & LE). exists (a :: s), r. split; [cbn; rewrite E; reflexivity|].
    split; [intros [E1|E1]; [apply NE; exact E1| exact (NIs E1)]| cbn; lia]. }
  destruct NS as (str & rest & EV & NI & LSTR).
  assert (LVB : Z.of_nat (length vbs) = hvCap h + 1) by (destruct VB as [[WF _] _]; cbn in WF; destruct WF as (W0 & _); rewrite W0; clear - LC; lia).
  pose proof (u8arr_of_rw_cells asegs _ _ _ _ VB) as WBX.
  replace (Z_to_bv 64 (q' + 32)) with (Z_to_bv 64 (q' + 24 + 8)) by (f_equal; lia).
  replace (Z_to_bv 64 ((q' + 32) ≫ 3 + 2147450880)) with (Z_to_bv 64 ((q' + 24 + 8) ≫ 3 + 2147450880)) by (do 3 f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mX end.
  unshelve eapply (te_loopB h vbs str rest mX Q (q' + -96) (q' + 24) (4 * kq' + 3) _ _ Hh EV NI LVB SHV1 SHM1 ltac:(clear - CLO LO Hq; lia) ltac:(clear - Q47 Hq; lia) ltac:(clear - Hq32; lia)
            _ (S (length str)) 0%nat vbs mX (hvA h)).
  2: lia.
  2: lia.
  2: apply munch_refl.
  2: apply wmono_refl.
  2: eassumption.
  2: exact MPC.
  2: exact WBX.
  2: (split; [reflexivity| split; [intros; reflexivity| split; [intros j b Hj; lia| intros j Hj; exact Hj]]]).
  2: lia.
  intros m' vbs' y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y25 y28 y29 y30 y31 WB' LI' MI' MPC' MUv WMv.
  clear VB WBX SHV1 SHM1 MPC. try clear MI.
  replace (Z_to_bv 64 (q' + 24 + 8)) with (Z_to_bv 64 (q' + 32)) by (f_equal; lia).
  replace (Z_to_bv 64 ((q' + 24 + 8) ≫ 3 + 2147450880)) with (Z_to_bv 64 ((q' + 32) ≫ 3 + 2147450880)) by (do 3 f_equal; lia).
  transport_after_call asegs mX m' MUv WMv. clear MUv WMv.
  assert (SHV' : shw m' (hvA h) (hvCap h + 1)) by (eapply shw_frame; [exact SHV| exact MU0| exact APV]).
  assert (SHM' : shw m' (q' + 24) 16) by (eapply shw_frame; [exact SHM| exact MU0| exact APV]).
  chk8N 22 (q' + 24 + 8) SHM'. step. lit_branch.
  step.
  zstep.
  step. ubr.
  step.
  zstep. zstep.
  gen2 CONT2 0x89e9c 11%nat 12%nat.
  2:{ chkbN 11 (hvA h + hvLen h) SHV' kk SHRk Hk.
      destruct Hk as [-> | [G1 G2]].
      - step. step. lit_branch. apply CONT2.
      - step. rewrite (sxb_small kk) by lia.
        step. if_cases G3; zify_cond G3; [| exfalso; lia].
        zstep.
        step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
        apply CONT2. }
  intros u10 u11.
  pose proof LI' as (LL & LGE & LLT & LZ).
  assert (LVB' : Z.of_nat (length vbs') = hvCap h + 1) by (rewrite LL; exact LVB).
  pose proof (u8arr_store_ok asegs _ _ _ (hvLen h) (Z_to_bv 64 (hvA h + hvLen h + 0)) WB' ltac:(rewrite LVB'; clear - LC; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep.
  assert (LE10 : le1 (Z_to_bv 64 0) = [zbG]) by (unfold le1; rewrite unsigned_lit by lia; reflexivity).
  rewrite LE10.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?e) ?x) _) =>
    change (write_to_mem mm (Z_to_bv 64 e) x) with (write_to_mem mm (wa (hvA h + hvLen h)) x) end.
  replace (hvA h + hvLen h + 0) with (hvA h + hvLen h) in SOK by lia.
  pose proof (u8arr_write asegs _ _ _ (hvLen h) zbG WB' ltac:(rewrite LVB'; clear - LC; lia)) as WB2. clear WB'.
  store_done.
  assert (UPDID : forall (l : list byte) i x, nth_error l i = Some x -> upd l i x = l).
  { clear. induction l as [|y l IH]; intros [|i] x Hx; cbn in *; try discriminate; [injection Hx as ->; reflexivity| rewrite (IH i x Hx); reflexivity]. }
  rewrite (UPDID vbs' _ zbG (LZ _ VN)) in WB2.
  assert (FZ : nth_error vbs (length str) = Some zbG) by (rewrite EV, nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
  pose proof (LZ _ FZ) as SP. apply List.nth_error_split in SP as (hay & rest' & EV' & LHAY).
  assert (NIH : ~ In zbG hay).
  { intros HIn. apply In_nth_error in HIn as (j & Hj). assert (j < length hay)%nat by (apply nth_error_Some; rewrite Hj; discriminate).
    refine (LLT j zbG ltac:(lia) _ eq_refl). rewrite EV', nth_error_app1 by lia. exact Hj. }
  assert (LR' : Z.of_nat (length hay) + 1 + Z.of_nat (length rest') = hvCap h + 1).
  { rewrite <- LVB', EV', length_app. cbn [length]. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
  assert (SL1 : bytes_at asegs mS (hvA h + (hvCap h + 1)) sl) by assumption.
  assert (SHMs : shw mS (q' + 24) 16) by (eapply shw_frame; [exact SHM| exact MU0| exact APV]).
  assert (SHVs : shw mS (hvA h) (hvCap h + 1)) by (eapply shw_frame; [exact SHV| exact MU0| exact APV]).
  assert (SHCs : shw mS A0_CHUNKED 8) by (eapply shw_frame; [exact SHWC| exact MU0| exact APV]).
  chk8N 20 (q' + 24) SHMs. step. lit_branch.
  step.
  step. step.
  step.
  assert (BYH : bytes_at asegs mS (hvA h) (hay ++ zbG :: (rest' ++ sl))).
  { replace (hay ++ zbG :: rest' ++ sl) with (vbs' ++ sl) by (rewrite EV', <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact (proj1 WB2)|]. rewrite LVB'. exact SL1. }
  assert (LHC : Z.of_nat (length hay) <= hvCap h) by (clear - LR'; lia).
  destruct (shw_sub _ _ _ (hvA h) (Z.of_nat (length hay) + 1) SHVs ltac:(lia) ltac:(clear - LHC; lia) ltac:(lia)) as (ACS & RDS & _).
  destruct SHCs as (ACN & RDN & _).
  env_sync AE MU0 WM0.
  eapply evt_cut.
  { eapply (ic_strstr_chunked IC) with (H := hvA h) (hay := hay) (slack := rest' ++ sl) (canary := canary) (lo := lo) (q := q' + -96);
      [ exact BYH | exact NIH
      | rewrite length_app, Nat2Z.inj_add; clear - LR' SE SLL; Z.div_mod_to_equations; lia
      | eassumption | eassumption
      | exact ACS | exact RDS | unfold icpt_win; clear - LHC RV ACR; lia | clear - LHC CAPB; lia
      | exact ACN | exact RDN
      | eassumption | eassumption | exact CLO | unfold A0_STRSTR_DEPTH; clear - LO Hq; lia | clear - QHI Hq; lia
      | clear - RV; lia | rewrite length_app, Nat2Z.inj_add; clear - LR' SLL RV; lia
      | eassumption | reflexivity | reflexivity ]. }
  intros msS PS0. unfold strstr_chunked_post_A in PS0.
  destruct PS0 as (d0 & d1 & d2 & d4 & d5 & d6 & d7 & d8 & d9 & d10 & d11 & d12 & d13 & d14 & m2 & r & -> & MUc & WMc & MI2 & ST2 & AE2 & BYH2 & PGOT2 & PCAN2 & RR).
  clear BYH ACS RDS ACN RDN SHVs SHMs MI'. try clear AE. try clear PGOT PCAN.
  transport_after_call asegs mS m2 MUc WMc.
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  clear MUc WMc. unfold A0_got_ssp in PGOT2. unfold A0_ssp_guard in PGOT2, PCAN2.
  assert (SHV2 : shw m2 (hvA h) (hvCap h + 1)) by (eapply shw_frame; [exact SHV| exact MU0| exact APV]).
  assert (SHM2 : shw m2 (q' + 24) 16) by (eapply shw_frame; [exact SHM| exact MU0| exact APV]).
  clear BYH2. change (hid2 (r = 0 \/ hvA h <= r <= hvA h + Z.of_nat (length hay))) in RR.
  chk8N 22 (q' + 24 + 8) SHM2. step. lit_branch.
  step.
  step.
  step. ubr.
  zstep. zstep. zstep. ub_b2z. step. lit_branch_safe.
  ub_null.
  zstep. zstep.
  gen2 CONT3 0x89ef0 12%nat 13%nat.
  2:{ chkbN 12 (hvA h + hvLen h) SHV2 kk SHRk Hk.
      destruct Hk as [-> | [G1 G2]].
      - step. step. lit_branch. apply CONT3.
      - step. rewrite (sxb_small kk) by lia.
        step. if_cases G3; zify_cond G3; [| exfalso; lia].
        zstep.
        step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
        apply CONT3. }
  intros t12 t13.
  pose proof (u8arr_store_ok asegs _ _ _ (hvLen h) (Z_to_bv 64 (hvA h + hvLen h + 0)) WB2 ltac:(rewrite LVB'; clear - LC; lia) ltac:(unfold wa; f_equal; lia)) as SOK2.
  pose proof (munch_refl [(hvA h, hvA h + (hvCap h + 1))]%Z m2) as MUr. pose proof (wmono_refl asegs m2) as WMr.
  zstep.
  rewrite LE10.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?e) ?x) _) =>
    change (write_to_mem mm (Z_to_bv 64 e) x) with (write_to_mem mm (wa (hvA h + hvLen h)) x) end.
  replace (hvA h + hvLen h + 0) with (hvA h + hvLen h) in SOK2 by lia.
  pose proof (u8arr_write asegs _ _ _ (hvLen h) zbG WB2 ltac:(rewrite LVB'; clear - LC; lia)) as WB4. clear WB2.
  store_done.
  rewrite (UPDID vbs' _ zbG (LZ _ VN)) in WB4.
  pose proof (rw_cells_of_u8arr asegs _ _ _ WB4) as VB4. clear WB4.
  replace (length vbs') with (Z.to_nat (hvCap h + 1)) in VB4 by (clear - LVB'; lia).
  env_sync AE2 MUr WMr. clear MUr WMr.
  gen2 EPI 0x89f10 10%nat 11%nat.
  { intros yr ys.
    do 11 step.
    step.   step.
    rewrite ERET.
    release_frame FR ST2 q'.
    eapply K; [exact MU0| exact WM0| exact MI2| exact ST2| exact AE2| eassumption| exact VB4| exact (LZ _ VN)| exact PGOT2| exact PCAN2]. }
  step.   if_cases KF; zify_cond KF.
  - step.   apply EPI.
  - assert (SHM3 : shw m1 (q' + 24) 16) by (eapply shw_frame; [exact SHM| exact MU0| exact APV]).
    chk8N 20 (q' + 24) SHM3. step. lit_branch.
    step. step.
    step.   apply EPI.
Qed.

Definition VW1 (h : hv) : list ivl := [(hvA h, hvA h + (hvCap h + 1))]%Z.
Definition blockCf_stmt : Prop :=
  forall (h : hv) q' m v24 v32 eb el errw hackw posw entpw clenw espw
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  In h hvs -> minvG [] q' m 248 248 0 v24 v32 -> pinvG m eb el errw hackw posw entpw clenw espw -> hview m ->
  forall (Q : machine_state -> Prop),

  (forall m' w24 w32 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y25 y28 y29 y30 y31,
     minvG (VW1 h) q' m' 248 248 248 w24 w32 -> pinvG m' eb el errw hackw posw (wz 3) clenw espw -> hview m' ->
     evt asegs Q (GSTP 0x89730 q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 6) y21 y22 y25 y28 y29 y30 y31 m')) ->

  (forall m' w24 w32 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     minvG (VW1 h) q' m' 248 248 248 w24 w32 -> pinvG m' eb el errw hackw posw entpw clenw espw -> hview m' ->
     evt asegs Q (GSTP 0x89998 q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 (P + 288)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) y28 y29 y30 y31 m')) ->
  evt asegs Q (GSTP 0x8987c q' x1 x5 x6 x7 (Z_to_bv 64 (hvN h)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 (P + 288)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) x28 x29 x30 x31 m).

#[using="kq st A cur hvs CLO LO AL16 Q47 SHZ SHR RF0 ARNG PLB HPURE"] Lemma shwStk_nowG : forall m X n, munch (W0c []) m0 m -> lo <= X -> X + n <= q -> 0 <= n -> shw m X n.
Proof.
  intros m X n MU HX1 HX2 Hn.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (W0c_fsw [] vw_ok_nil) as FSW.
  pose proof (shz_stack_fs FI (W0c []) m0 m lo (sh lo) (sh q) SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - Q47; lia)) MU FSW) as SHZm.
  pose proof (shr_stack_fs FI (W0c []) m0 m lo _ _ SHR CLO (Z.le_refl _) (sh_hi_ok8 q Q47) MU FSW) as SHRm.
  assert (SW : shw m lo (q - lo)).
  { apply (shw_of_shz_shr m (sh lo) (sh q) (sh lo - sh lo mod 8) (sh q + 8) lo (q - lo) SHZm SHRm).
    - unfold win_ok. split; [clear - LO; lia|]. right. clear - CLO ACR LO Q47. lia.
    - clear - LO. lia.
    - unfold sh, SHADOW_OFF. clear - LO CLO ACR Q47 AL16. Z.div_mod_to_equations. lia.
    - clear - LO. lia.
    - unfold sh, SHADOW_OFF. clear - LO CLO ACR Q47 AL16. Z.div_mod_to_equations. lia. }
  eapply shw_sub; [exact SW| lia| lia| lia].
Qed.

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
#[using="lo A cur ARNG"] Lemma vw_ok_1 : forall h, In h hvs -> vw_ok (VW1 h).
Proof. intros h Hh. unfold H_germ_seg1.vw_ok, VW1. apply Forall_cons; [exists h; cbn [fst snd]; split; [exact Hh| lia]| apply Forall_nil]. Qed.

#[using="Type"] Lemma hv_eq_dec : forall a b : hv, {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Qed.

#[using="lo A cur ARNG HPURE"] Lemma hview_upd : forall (h0 : hv) W m m', In h0 hvs -> hview m -> munch W m m' -> wmono asegs m m' -> Forall (fsw_iv FI) W ->
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
