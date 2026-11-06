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

Definition germ_entryA : Z := 0x89068.
Notation GERM_DEPTH_A := 16384%Z.
Notation ERRNO_G := 0x5e68cc%Z.
Notation got_sspG := 0xaad68%Z.
Notation ssp_guardG := 0x6069b0%Z.
Notation zbG := (Z_to_bv 8 0).

Record hv := mkHv { hvN : Z; hvIt : Z; hvId : Z; hvA : Z; hvLen : Z; hvCap : Z }.
Definition hv3 (h : hv) : Z * Z * Z := (hvN h, hvIt h, hvId h).
Definition hvW (hvs : list hv) : list ivl := map (fun h => (hvA h, hvA h + (hvCap h + 1))) hvs.

Definition germF {HC : HasCeiling} (FI : fs_if) (st : fsstate FI) : Z := fs_F FI st 3.
Definition germFL {HC : HasCeiling} (FI : fs_if) (st : fsstate FI) : Z := fs_FL FI st 3.
Definition germSF {HC : HasCeiling} (FI : fs_if) (st : fsstate FI) : Z := sh (germF FI st).
Arguments germF : simpl never.
Arguments germFL : simpl never.
Arguments germSF : simpl never.

Definition ru8G (x : Z) : Z := 8 * ((x + 7) / 8).
Lemma ru8G_spec : forall x, x <= ru8G x <= x + 7 /\ exists k, ru8G x = 8 * k.
Proof. intros x. unfold ru8G. split; [Z.div_mod_to_equations; lia| eexists; reflexivity]. Qed.
Arguments ru8G : simpl never.

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

Definition minvG (VWc : list ivl) (q' : Z) (m : mem) (w1 w2 w3 : Z) (v0 v8 v16 v24 : word) : Prop :=
  (exists k', q' = 32 * k') /\ q + -176 <= q' <= q + -160
  /\ stk asegs m lo q'
  /\ (exists j32 j40, rw_cells asegs m q' [C8 v0; C8 v8; C8 v16; C8 v24; CB 8 j32; CB 8 j40; C8 (wz F)])
  /\ (exists je, rw_cells asegs m (F + 32) [CB 8 je])
  /\ (exists j1, rw_cells asegs m (F + 40) [CB 24 j1])
  /\ (exists k2 i2w, rw_cells asegs m (F + 64) [CB 16 k2; C4 i2w])
  /\ (exists r2, rw_cells asegs m (F + 84) [CB 108 r2])
  /\ (exists k1 i1w, rw_cells asegs m (F + 192) [CB 16 k1; C4 i1w])
  /\ (exists r1, rw_cells asegs m (F + 212) [CB 76 r1])
  /\ stk asegs m (q' + 56) (q + -104)
  /\ rw_cells asegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ rw_cells asegs m F [C8 (wz 0x41b58ab3); C8 (wz 0x113e7); C8 (wz 0x89068); C8 (wz q')]
  /\ (exists j216, rw_cells asegs m (F + 288) [CB 216 j216; C8 (wz FL)])
  /\ rw_cells asegs m SF (gshadow w1 w2 w3)
  /\ rw_cells asegs m FL [C1 (Z_to_bv 8 1)]
  /\ mem_inv asegs m
  /\ munch (W0c VWc) m0 m /\ wmono asegs m0 m
  /\ fkeep FI WPg st m0 m /\ asan_env asegs m
  /\ (exists stc, RFAKE FI stc m /\ fs_live FI stc = fs_newff FI st 3 :: fs_live FI st).

Definition plbG : Prop := lb (fs_live FI st) P 504.

Definition pinvG (m : mem) (eb el errw hackw posw entpw clenw espw : word) : Prop :=
  rw_cells asegs m P [C4 (wz 1); C4 (wz meth)]
  /\ rw_cells asegs m (P + 224) [C4 (wz rm); C4 (wz sc)]
  /\ (exists pad, rw_cells asegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad])
  /\ rw_cells asegs m (P + 288) (llist_cells first last size flh fk ffree httpmsg_compare_entryA)
  /\ rw_cells asegs m (P + 384) [C8 eb; C8 el]
  /\ rw_cells asegs m (P + 400) (mbuf_cells A len cap)
  /\ rw_cells asegs m (P + 440) [C4 errw; C4 hackw; C4 posw; C4 entpw; C4 clenw; C4 (wz 0); C8 (wz csz); C8 espw]
  /\ rw_cells asegs m (P + 480) [C8 (wz (P + 400)); C8 (wz cur); C4 (wz 0)]
  /\ (exists ev, rw_cells asegs m ERRNO_G [C4 ev])
  /\ rw_cells asegs m got_sspG [C8 (wz ssp_guardG)] /\ rw_cells asegs m ssp_guardG [C8 canary]
  /\ rw_cells asegs m INITWASCALLED_A [C1 (Z_to_bv 8 0)].

Definition hitem (m : mem) (h : hv) : Prop :=
  objA m (hvN h) 24 /\ objA m (hvIt h) 88
  /\ rw_cells asegs m (hvIt h + 24) (mbuf_cells (hvA h) (hvLen h) (hvCap h))
  /\ shw m (hvA h) (hvCap h + 1)
  /\ (exists vbs, rw_cells asegs m (hvA h) [CB (Z.to_nat (hvCap h + 1)) vbs] /\ nth_error vbs (Z.to_nat (hvLen h)) = Some zbG)
  /\ (exists sl, bytes_at asegs m (hvA h + (hvCap h + 1)) sl /\ hvA h + (hvCap h + 1) + Z.of_nat (length sl) = ru8G (hvA h + (hvCap h + 1))).
Definition hview (m : mem) : Prop :=
  lsegA m (map hv3 hvs) first (P + 288) (P + 312) /\ (forall h, In h hvs -> hitem m h).

Definition hreg (X n : Z) : Prop :=
  0x609000 <= X /\ X + n + 16 <= alloc_ceiling /\ (X + n <= FSB FI \/ FSB FI + A0_FS_SIZE <= X) /\ (X + n + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= X).
Definition hpure (h : hv) : Prop :=
  1 <= hvLen h <= hvCap h /\ hvCap h + 1 < 2^31 /\ hreg (hvN h) 24 /\ hreg (hvIt h) 88 /\ hreg (hvA h) (hvCap h + 1).

Definition vwc_ok (VWc : list ivl) (h0 : hv) : Prop := In h0 hvs /\ forall iv, In iv VWc -> hvA h0 <= fst iv /\ snd iv <= hvA h0 + (hvCap h0 + 1).

Hypothesis PLB : plbG.
Local Notation PLBv := (PLB : lb (fs_live FI st) P 504).
Hypothesis HPURE : forall h, In h hvs -> hpure h.

Hypothesis HAPART : forall h h', In h hvs -> In h' hvs ->
  (hvN h' + 24 <= hvA h \/ ru8G (hvA h + (hvCap h + 1)) <= hvN h') /\ (hvIt h' + 88 <= hvA h \/ ru8G (hvA h + (hvCap h + 1)) <= hvIt h')
  /\ ((hvA h = hvA h' /\ hvLen h = hvLen h' /\ hvCap h = hvCap h') \/ ru8G (hvA h' + (hvCap h' + 1)) <= hvA h \/ ru8G (hvA h + (hvCap h + 1)) <= hvA h').
Hypothesis HV0 : hview m0.

Hypothesis FEV : forall m, munch (W0c (hvW hvs)) m0 m -> wmono asegs m0 m -> FSENV FI m.

Ltac mv_tacG := unfold minvG; split; [eexists; eassumption|]; split; [assumption|];
  repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]); eexists; split; eassumption.

Ltac pv_tacG := unfold pinvG; split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|];
  split; [eassumption|]; split; [eassumption| eassumption].

#[using="m0 A cur RF0 ARNG PLB"] Lemma geomG : exists kF kB,
  F = 64 * kF /\ SF = 8 * kF + 2147450880 /\ FSB FI = 4096 * kB /\ sh (FSB FI) = 512 * kB + 2147450880
  /\ FSB FI + 36864 <= F /\ F + 512 <= FSB FI + 11571200 /\ FSB FI + 4096 <= FL /\ FL + 1 <= FSB FI + 36864
  /\ (P + 504 <= F \/ F + 512 <= P) /\ FSB FI + 36864 <= P /\ P + 504 <= FSB FI + 11571200
  /\ 6328320 <= FSB FI /\ FSB FI + 11571200 <= alloc_ceiling
  /\ (FSB FI + 11571200 <= 2147446784 \/ 17594333495296 <= FSB FI).
Proof.
  destruct (new_frame_facts FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
  cbn [FB_of SB_of] in FHI.
  pose proof (lb_apart_new FI st 3 m0 F SF FL P 504 RF0 ltac:(lia) eq_refl eq_refl eq_refl PLBv) as PFAP. cbn [FB_of] in PFAP.
  destruct PLBv as (g & Hg & G1 & G2). pose proof (live_wf FI st m0 RF0) as LW. rewrite Forall_forall in LW.
  destruct (LW g Hg) as (KR & GLO & GHI & _). unfold ff_size in *.
  pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
  exists (F / 64), (FSB FI / 4096).
  split; [clear - FAL; Z.div_mod_to_equations; lia|].
  split; [unfold germSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia|].
  split; [clear - FSB4; Z.div_mod_to_equations; lia|].
  split; [unfold sh, SHADOW_OFF; clear - FSB4; Z.div_mod_to_equations; lia|].
  repeat (split; [first [assumption | lia]|]). first [assumption | lia].
Qed.

#[using="m0 A cur SHWP ARNG"] Lemma WPg_app : app_ivs WPg.
Proof.
  pose proof (shw_win_ok _ _ _ SHWP) as WK. unfold app_ivs.
  apply Forall_cons; [eapply app_iv_of_win_ok; [exact WK| lia| lia]|].
  apply Forall_cons; [eapply app_iv_of_win_ok; [exact WK| lia| lia]|].
  apply Forall_cons; [apply app_iv_low; lia|]. apply Forall_nil.
Qed.
#[using="m0 A cur SHWP ARNG"] Lemma WPg_out : forall a, sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE -> outside WPg a.
Proof.
  intros a Ha. apply (app_ivs_outside WPg a WPg_app).
  pose proof (fsb_ok FI) as FSBOK. destruct FSBOK as (F1 & F2 & F3 & F4 & F5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  unfold shband, SH_LO, SH_HI. unfold sh, SHADOW_OFF in Ha. Z.div_mod_to_equations. lia.
Qed.

#[using="A cur RF0 SHWP ARNG PLB"] Lemma shwP_now : forall m, fkeep FI WPg st m0 m -> shw m P 504.
Proof.
  intros m FK.
  eapply (shw_fkeep FI WPg st m0 m P 504); [exact SHWP| exact FK| exact RF0| exact PLBv| exact WPg_out].
Qed.

#[using="m0 A cur RF0 ARNG PLB"] Lemma liveG : forall stc, fs_live FI stc = fs_newff FI st 3 :: fs_live FI st ->
  lb (fs_live FI stc) F 512 /\ ls (fs_live FI stc) SF 64 /\ lf (fs_live FI stc) FL /\ lb (fs_live FI stc) P 504
  /\ (forall g, In g (fs_live FI st) -> In g (fs_live FI stc)).
Proof.
  intros stc LIVE1.
  destruct (new_frame_facts FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
  assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
  pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
  unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
  change (ff_addr (fs_newff FI st 3)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 3)) with FL in LVL. change (sh F) with SF in LVS.
  split; [exact LVF|]. split; [exact LVS|]. split; [exact LVL|]. split; [exact (lb_mono _ _ _ _ PLBv LSUB)| exact LSUB].
Qed.

#[using="meth rm sc isreq A len cur CURR METHR RMR SCR ISR ARNG"] Lemma sub_fp_cons2 : forall (a b : ivl) (W : list ivl), sub_fp [a] W -> sub_fp [b] W -> sub_fp [a; b] W.
Proof. intros [a1 a2] [b1 b2] W HA HB xo Ho. specialize (HA xo Ho). specialize (HB xo Ho). cbn [outside] in *. tauto. Qed.
#[using="A cur ARNG"] Lemma sub_fp_stk : forall VWc a b, lo <= a -> b <= q -> sub_fp [(a, b)] (W0c VWc).
Proof. intros VWc a b H1 H2 xo Ho. cbn [outside app] in *. destruct Ho as (H0 & _). split; [lia| exact I]. Qed.
#[using="m0 A cur RF0 ARNG PLB"] Lemma sub_fp_F : forall VWc a b, F <= a -> b <= F + 512 -> sub_fp [(a, b)] (W0c VWc).
Proof.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & _).
  intros VWc a b H1 H2 xo Ho. cbn [outside app] in *. destruct Ho as (_ & H2' & _). split; [lia| exact I].
Qed.
#[using="m0 A cur RF0 ARNG PLB"] Lemma sub_fp_SF : forall VWc, sub_fp [(SF, SF + 64)]%Z (W0c VWc).
Proof.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  intros VWc xo Ho. cbn [outside app] in *. destruct Ho as (_ & _ & H3 & _). split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia| exact I].
Qed.
#[using="A cur ARNG"] Lemma sub_fp_ent : forall VWc a b, P + 384 <= a -> b <= P + 400 -> sub_fp [(a, b)] (W0c VWc).
Proof. intros VWc a b H1 H2 xo Ho. cbn [outside app] in *. destruct Ho as (_ & _ & _ & H4 & _). split; [lia| exact I]. Qed.
#[using="A cur ARNG"] Lemma sub_fp_ctl : forall VWc a b, P + 440 <= a -> b <= P + 480 -> sub_fp [(a, b)] (W0c VWc).
Proof. intros VWc a b H1 H2 xo Ho. cbn [outside app] in *. destruct Ho as (_ & _ & _ & _ & H5 & _). split; [lia| exact I]. Qed.
#[using="A cur ARNG"] Lemma sub_fp_errno : forall VWc, sub_fp [(ERRNO_G, ERRNO_G + 4)]%Z (W0c VWc).
Proof. intros VWc xo Ho. cbn [outside app] in *. destruct Ho as (_ & _ & _ & _ & _ & H6 & _). split; [lia| exact I]. Qed.

#[using="STACK_MALLOC_3 kq A cur CLO LO AL16 QHI Q63 RF0 FCO FE0 st1 PLO PHI SHWP ARNG PLB"] Lemma prologueG : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 ->
  forall (Q : machine_state -> Prop),
  (forall q' m v0 v8 v16 v24 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
     minvG [] q' m 248 248 248 v0 v8 v16 v24 ->
     munch ((lo, q) :: FSIV [])%Z m0 m -> fkeep FI [] st m0 m ->
     evt asegs Q (GSTP 0x89204 q' x1 x5 x6 x7 (Z_to_bv 64 (P + 480)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) s5 s6 s7 s8 s9 x28 x29 x30 x31 m)) ->
  evt asegs Q
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (Z_to_bv 64 germ_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AG Q K. unfold germ_entryA.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AG as AE. apply asan_env_globals in AG. ag_split AG.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (new_frame_facts FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _ & _ & _ & _ & _ & APART).
  cbn [FB_of SB_of] in APART.
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  pose proof (munch_refl (W0c []) m0) as MU. pose proof (wmono_refl asegs m0) as WM.
  pose proof (munch_refl ((lo, q) :: FSIV [])%Z m0) as MUP.
  pose proof (munch_refl [(lo, q)]%Z m0) as MU0. pose proof (wmono_refl asegs m0) as WM0.
  pose proof (fkeep_refl FI [] st m0) as FK. assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st)) by (intros g Hg; exact Hg).
  pose proof RF0 as RF. pose proof (fs_call_ok_le FI st tp 2 1 FCO ltac:(lia)) as FCO1.
  carve_frame 160%nat ST.
  step. do 14 (step; fix_lit_store).
  step.
  step.
  rewrite (unsigned_lit (q + -160)) by lia. rewrite land_align32 by lia.
  remember (q + -160 - (q + -160) mod 32)%Z as q' eqn:Eq0.
  assert (Hq : q' = q + -160 \/ q' = q + -160 - 16) by (subst q'; apply align32_cases; clear - AL16; Z.div_mod_to_equations; lia).
  assert (Hq32 : exists k', q' = 32 * k') by (exists ((q + -160) / 32); clear - Eq0; Z.div_mod_to_equations; lia).
  assert (QL : q + -176 <= q' <= q + -160) by (clear - Hq; lia).
  clear Eq0.
  lazymatch goal with FRx : rw_cells asegs ?mm (q + -160) (?c0 :: ?c1 :: ?rest) |- _ =>
    destruct (align_frame_gen mm lo (q + -160) q' [c0; c1] rest 56%nat ST ltac:(lia) FRx eq_refl ltac:(lia) Hq) as (STq & (jq & QC) & GAP & FRhi);
    clear FRx end.
  clear Hq.
  clear ST. rename STq into ST. change (Z.of_nat 56) with 56 in GAP, FRhi. replace (q + -160 + 56) with (q + -104) in GAP, FRhi by lia.
  step.
  step. step. step. step.
  step. step.
  step.
  step.   lit_branch.
  step.
  step.
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  call (STACK_MALLOC_3 st lo q' 320 F SF FL 512 472%nat 64%nat).
  all: side (try (first [ assumption | reflexivity | (unfold A0_RT_STACK in *; lia) ])).
  match goal with A : asan_env asegs _ |- _ => try clear AE; rename A into AE end.
  match goal with R : RFAKE FI (fs_next FI st 3) _ |- _ => rename R into RF end.
  match goal with E : fs_live FI _ = _ :: _ |- _ => rename E into LIVE1 end. fold st1 in LIVE1, RF.
  match goal with K0 : fkeep FI [] st _ _ |- _ => rename K0 into FKc end.
  match goal with P0 : rw_cells asegs _ F _ |- _ => rename P0 into FRF end.
  match goal with P0 : rw_cells asegs _ SF _ |- _ => rename P0 into SHF; shadow_cells_lit SHF end.
  match goal with P0 : rw_cells asegs _ FL _ |- _ => rename P0 into FLG end.
  fs_after_call FI FK FKc LSUB LIVE1 [(lo, q); (F, F + 512); (SF, SF + 64)]%Z.
  pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
  unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
  change (ff_addr (fs_newff FI st 3)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 3)) with FL in LVL. change (sh F) with SF in LVS.
  step. step.
  step.   if_cases K0; zify_cond K0. 2:{ exfalso. lia. } clear K0.
  do 10 step.
  step; fix_lit_store. step; fix_lit_store. step; fix_lit_store.
  step. step.
  replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 F)) 3 + 2147450880)) with (Z_to_bv 64 SF)
    by (f_equal; rewrite unsigned_lit by lia; rewrite shiftr3_div; reflexivity).

  hideW MU WM. lazymatch type of MUP with ?T => change (hid2 T) in MUP end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 64)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 4 sstep.
  step.
  do 12 sstep.
  step.
  do 24 sstep.
  unhide_transport MUs WMs.
  assert (SUBP : sub_fp [(SF, SF + 64)]%Z ((lo, q) :: FSIV [])%Z).
  { intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & H3 & _). split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia| exact I]. }
  unfold hid2 in MUP.
  lazymatch type of MUs with munch _ ?ma ?mf => pose proof (munch_absorb _ _ m0 ma mf MUP MUs SUBP) as MUP' end. clear MUP. rename MUP' into MUP.
  absorbW MU WM MUs WMs (sub_fp_SF []). clear MUs WMs SUBP.
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(lo, q)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
  step.
  lazymatch type of FK with fkeep _ _ _ _ ?mm => assert (FKW : fkeep FI WPg st m0 mm) by (eapply fkeep_weaken; [exact FK| intros a Ha; exact I| intros g Hg; exact Hg]) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWPn : shw mm P 504) by exact (shwP_now mm FKW) end.
  chk8N 12 (P + 480) SHWPn. clear SHWPn FKW.
  step; fix_lit_store.
  step. lit_branch.

  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  splitcb QC 0%nat [8; 8; 8; 8; 8; 8]%nat. recell QC 0%nat. recell QC 1%nat. recell QC 2%nat. recell QC 3%nat. name_junk QC.
  splitcb FRF 4%nat [8; 24; 16; 4; 108; 16; 4; 76; 216]%nat. name_junk FRF.
  split_chunk FRF 4%nat FH R1. split_chunk R1 1%nat LE R2. split_chunk R2 1%nat LJ1 R3. split_chunk R3 2%nat LK2 R4.
  split_chunk R4 1%nat LR2 R5. split_chunk R5 2%nat LK1 R6. split_chunk R6 1%nat LR1 FT.
  recell LK2 1%nat. recell LK1 1%nat.
  lazymatch type of FK with fkeep _ _ _ _ ?mm => assert (FKW : fkeep FI WPg st m0 mm) by (eapply fkeep_weaken; [exact FK| intros a Ha; exact I| intros g Hg; exact Hg]) end.
  destruct Hq32 as (kq' & Hq32).
  eapply K; [mv_tacG| exact MUP| exact FK].
Qed.

Definition WEG : list ivl := [(lo, q); (F, F + 512); (SF, SF + 64); (FL, FL + 1)]%Z.
Definition rframeG (R : mem -> Prop) : Prop := forall m m', R m -> munch WEG m m' -> wmono asegs m m' -> R m'.
#[using="m0 A cur RF0 ARNG PLB"] Lemma sub_fp_WEG : forall VWc, sub_fp WEG (W0c VWc).
Proof.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  intros VWc xo Ho. unfold WEG. cbn [outside app] in *. destruct Ho as (H1 & H2 & H3 & _).
  split; [exact H1|]. split; [clear - H2 GF1 GF2; lia|]. split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia|]. split; [clear - H2 GF4 GF5; lia| exact I].
Qed.

Definition postG (VWc : list ivl) (X : Z -> mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (r : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (W0c VWc) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
    /\ fkeep FI WPg st m0 m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ X r m'.

#[using="SET_SHADOW_F5 kq A cur CLO LO AL16 Q63 RF0 ARNG PLB"] Lemma exitG : forall (r : Z) (VWc : list ivl) (X : Z -> mem -> Prop) q' m w1 w2 w3 v0 v8 v16 v24
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31,
  minvG VWc q' m w1 w2 w3 v0 v8 v16 v24 -> X r m -> rframeG (X r) ->
  evt asegs (postG VWc X) (GSTP 0x89370 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x21 x22 x23 x24 x25 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV HX RFR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j32 & j40 & QC) & (je & LE) & (j1 & LJ1) & (k2 & i2w & LK2) & (r2 & LR2) & (k1 & i1w & LK1) & (r1 & LR1) & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (new_frame_facts FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveG stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  clear PFAP PFS1 PFS2. hideW MU WM.
  pose proof (munch_refl WEG m) as MUE. pose proof (wmono_refl asegs m) as WME. unfold WEG in MUE.
  pose proof (munch_refl [(lo, q); (F, F + 512); (SF, SF + 64)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  step. step. step; fix_lit_store.
  step.   if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
  step. step.
  step.
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  eapply evt_cut.
  { eapply (SET_SHADOW_F5 SF 64 lo q'); [exact SHF| reflexivity| lia| clear - ESF EKF GF1 FSB1; lia| clear - ESF EKF GF2 FSB2 ACR; lia| exact AE| exact ST| exact CLO| unfold A0_RT_STACK; lia| lia| exact MI| reflexivity| reflexivity]. }
  intros ms' PO. unfold set_shadow_f5_post in PO.
  destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MUc & WMc & MI' & SHF' & ST' & AE').
  unfold shadow_cells in SHF'. cbv [repeat map Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in SHF'.
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  clear SHF ST AE MI.
  transport_after_call asegs m1 m' MUt WMt. clear MUt WMt.
  replace (ret_pc (Z_to_bv 64 562060)) with (Z_to_bv 64 562060) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(FL, FL + 1)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
  sstep.
  env_sync AE' MU0 WM0. fk_sync FI RF MU0 FK LSUB.

  join_chunks LR1 FT R6. join_chunks LK1 R6 R5. join_chunks LR2 R5 R4. join_chunks LK2 R4 R3. join_chunks LJ1 R3 R2. join_chunks LE R2 R1.
  join_chunks FH R1 FRF.
  lazymatch type of RF with RFAKE _ ?st2 ?mb2 =>
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (SHF2 : rw_cells asegs mc (sh (ff_addr (fs_newff FI st 3))) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize (fs_newff FI st 3))))))
      by (change (ff_addr (fs_newff FI st 3)) with F; change (sh F) with SF; unfold ff_shsize; rewrite FCLS; exact SHF');
    destruct (release FI st2 (fs_newff FI st 3) (fs_live FI st) mb2 mc _ RF LIVE1 MU0 WM0 FLG SHF2 FRF
                ltac:(unfold ff_size; rewrite FCLS; reflexivity)) as [RF3 LIVE3]
  end end.
  clear RF MU0 WM0 SHF2.
  step.   step.   step.
  do 13 step.
  step.   step.

  release_frame QC ST' (q' + 56)%Z.
  pose proof (stk_merge asegs _ _ _ _ ST' GAP ltac:(lia)) as STm. clear ST' GAP.
  release_frame FRhi STm q.
  absorbW MU WM MUE WME (sub_fp_WEG VWc).
  apply evt_done. unfold postG. exists r. do 14 eexists.
  lazymatch goal with |- exists _ _, MS _ _ _ _ _ ?mm _ = _ /\ _ => exists mm, (fs_after_release FI stc) end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FK|]. split; [exact LIVE3|]. split; [exact RF3|].
  split; [exact STm|]. split; [assumption|]. exact (RFR m _ HX MUE WME).
Qed.

Ltac shwP_here SHWPs MU0 N :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    first [ lazymatch goal with H : shw mm P 504 |- _ => idtac end
          | (try clear N); assert (N : shw mm P 504) by (eapply (shw_frame WPg); [exact SHWPs| exact MU0| exact WPg_app]) ] end.

Ltac wPA SHWPs MU0 N pc :=
  repeat first [ (is_ms; tryif at_pc pc then fail else (shwP_here SHWPs MU0 N; cstep)) | (is_if; br_auto) ].

#[using="kq kP CLO LO AL16 RF0 PAL PLO PHI SHWP METHR RMR SCR ISR ARNG PLB"] Lemma blockA : forall q' m v0 v8 v16 v24 eb el errw hackw posw entpw clenw espw
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x28 x29 x30 x31,
  minvG [] q' m 248 248 248 v0 v8 v16 v24 -> pinvG m eb el errw hackw posw entpw clenw espw ->
  forall (Q : machine_state -> Prop),

  (forall m' y10 y11 y12 y13 y14 y15 y16 y17 y21 y22,
     minvG [] q' m' 248 248 248 v0 v8 v16 v24 -> pinvG m' (wz (A + cur)) (wz 0) errw hackw (wz 4) entpw clenw (wz cur) ->
     evt asegs Q (GSTP 0x89370 q' x1 x5 x6 x7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 0) y21 y22 x23 x24 x25 x28 x29 x30 x31 m')) ->

  (forall m' y10 y11 y12 y13 y14 y15 y16 y17,
     minvG [] q' m' 248 248 248 v0 v8 v16 v24 -> pinvG m' (wz (A + cur)) (wz 0) errw hackw posw entpw clenw (wz cur) ->
     evt asegs Q (GSTP 0x8947c q' x1 x5 x6 x7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) x23 x24 x25 x28 x29 x30 x31 m')) ->
  evt asegs Q (GSTP 0x89204 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) x21 x22 x23 x24 x25 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV Q K1 K2.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j32 & j40 & QC) & (je & LE) & (j1 & LJ1) & (k2 & i2w & LK2) & (r2 & LR2) & (k1 & i1w & LK1) & (r1 & LR1) & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (PM & PRS & (pad & PV) & PL & PE & PMB & PC & PS & (ev & PERR) & PGOT & PCAN & PIWC).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveG stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (shwP_now m FK) as SHWPs.
  pose proof (munch_refl WPg m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  unfold mbuf_cells in PMB. unfold llist_cells in PL.
  wPA SHWPs MU0 SHWPn 0x89294.
  cstep.
  assert (J2 : forall y10 y11 y12, evt asegs Q (GSTP 0x8947c q' x1 x5 x6 x7 y10 y11 y12 (Z_to_bv 64 0) x14 x15 x16 x17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) x23 x24 x25 x28 x29 x30 x31 m3)).
  { intros y10 y11 y12. env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    eapply K2; [mv_tacG| pv_tacG]. }
  assert (J0 : forall y11 y12, evt asegs Q (GSTP 0x89364 q' x1 x5 x6 x7 (Z_to_bv 64 (P + 448)) y11 y12 (Z_to_bv 64 0) x14 x15 x16 x17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) x23 x24 x25 x28 x29 x30 x31 m3)).
  { intros y11 y12. wPA SHWPs MU0 SHWPn 0x89370.
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    eapply K1; [mv_tacG| pv_tacG]. }
  assert (J1 : forall y10 y11 y12, evt asegs Q (GSTP 0x89350 q' x1 x5 x6 x7 y10 y11 y12 (Z_to_bv 64 0) x14 x15 x16 x17 (Z_to_bv 64 P) (Z_to_bv 64 (P + 272)) (Z_to_bv 64 ((P + 272) ≫ 3 + 2147450880)) x23 x24 x25 x28 x29 x30 x31 m3)).
  { intros y10 y11 y12. wPA SHWPs MU0 SHWPn 0x89364. apply J0. }
  cstep. if_cases KI; zify_cond KI.
  -
    wPA SHWPs MU0 SHWPn 0x89350.
    if_cases KS1; zify_cond KS1; [apply J1|].
    wPA SHWPs MU0 SHWPn 0x89350.
    if_cases KS2; zify_cond KS2; [apply J1|].
    wPA SHWPs MU0 SHWPn 0x89350.
    if_cases KS3; zify_cond KS3; [apply J1|]. clear KS3.
    wPA SHWPs MU0 SHWPn 0x89350.
    if_cases KR1; zify_cond KR1; [apply J1|]. clear KR1.
    wPA SHWPs MU0 SHWPn 0x89350.
    if_cases KR2; zify_cond KR2; [apply J2| apply J1].
  -
    wPA SHWPs MU0 SHWPn 0x89364.
    if_cases KM; zify_cond KM; [apply J2|]. clear KM.
    wPA SHWPs MU0 SHWPn 0x89364.
    if_cases KB; zify_cond KB; [apply J2|]. clear KB.
    wPA SHWPs MU0 SHWPn 0x89364.
    apply J0.
Qed.

Definition hsafeW (W : list ivl) : Prop := Forall (fsw_iv FI) W /\ forall X n, hreg X n -> disjoint_from W X (ru8G (X + n) - X).

#[using="A cur ARNG HPURE"] Lemma hview_frame : forall W m m', hview m -> munch W m m' -> wmono asegs m m' -> hsafeW W -> hview m'.
Proof.
  intros W m m' (LS & HI) MU WM (FSW & DJ). split.
  - eapply lsegA_transport; [exact LS| exact MU| exact WM|].
    intros N it id Hin. apply in_map_iff in Hin as (h & E & Hh). unfold hv3 in E. injection E as <- <- <-.
    destruct (HPURE h Hh) as (_ & _ & RN & RI & _).
    pose proof (DJ _ _ RN) as D1. pose proof (DJ _ _ RI) as D2.
    pose proof (ru8G_spec (hvN h + 24)) as (U1 & _). pose proof (ru8G_spec (hvIt h + 88)) as (U2 & _).
    split; [eapply disjoint_from_sub; [exact D1| lia| lia]| eapply disjoint_from_sub; [exact D2| lia| lia]].
  - intros h Hh. destruct (HI h Hh) as ((N1 & N2 & N3 & N4) & (I1 & I2 & I3 & I4) & VC & SHV & (vbs & VB & VN) & (sl & SL & SE)).
    destruct (HPURE h Hh) as (LC & CAPB & RN & RI & RV).
    pose proof (DJ _ _ RN) as D1. pose proof (DJ _ _ RI) as D2. pose proof (DJ _ _ RV) as D3.
    pose proof (ru8G_spec (hvN h + 24)) as (U1 & _). pose proof (ru8G_spec (hvIt h + 88)) as (U2 & _). pose proof (ru8G_spec (hvA h + (hvCap h + 1))) as (U3 & _).
    pose proof RN as (_ & _ & FN & _). pose proof RI as (_ & _ & FI2 & _). pose proof RV as (_ & _ & FV & _).
    split. { split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. apply (shw_frame_fs FI W m m' _ _ N4 MU FSW). clear - FN. lia. }
    split. { split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. apply (shw_frame_fs FI W m m' _ _ I4 MU FSW). clear - FI2. lia. }
    split. { eapply rw_cells_transport; [exact VC| exact MU| exact WM|]. unfold mbuf_cells. cbn [cells_size csize Nat.add].
             eapply disjoint_from_sub; [exact D2| lia| lia]. }
    split. { apply (shw_frame_fs FI W m m' _ _ SHV MU FSW). clear - FV. lia. }
    split. { exists vbs. split; [| exact VN]. eapply rw_cells_transport; [exact VB| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
             eapply disjoint_from_sub; [exact D3| lia| lia]. }
    exists sl. split; [| exact SE]. eapply bytes_at_transport; [exact SL| exact MU|].
    eapply disjoint_from_sub; [exact D3| lia| lia].
Qed.

Definition hsafe_iv (iv : ivl) : Prop :=
  alloc_ceiling <= fst iv \/ (FSB FI <= fst iv /\ snd iv <= FSB FI + A0_FS_SIZE)
  \/ (sh (FSB FI) <= fst iv /\ snd iv <= sh (FSB FI) + A0_FS_SHSIZE) \/ (0 <= fst iv /\ snd iv <= 0x609000).
#[using="A cur ARNG"] Lemma hsafe_of : forall W, Forall hsafe_iv W -> hsafeW W.
Proof.
  intros W FA. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4 & B5).
  assert (SHB : 2147450880 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 17594333495296).
  { unfold app_mem in B3. unfold sh, SHADOW_OFF. clear - B1 B2 B3. Z.div_mod_to_equations. lia. }
  split.
  - eapply Forall_impl; [| exact FA]. intros [a b] H. unfold hsafe_iv in H. cbn [fst snd] in H. unfold fsw_iv, app_iv, SH_HI. cbn [fst snd].
    destruct H as [H|[H|[H|H]]]; [left; right; lia| left; lia| right; lia| left; left; lia].
  - intros X n (R1 & R2 & R3 & R4). pose proof (ru8G_spec (X + n)) as (U1 & kU & U2).
    assert (B8 : FSB FI = 8 * (FSB FI / 8)) by (clear - B4; Z.div_mod_to_equations; lia).
    induction W as [|[a b] W IH]; cbn [disjoint_from]; [exact I|].
    inversion_clear FA as [|x l F1 F2]. split; [| apply IH; exact F2]. unfold hsafe_iv in F1. cbn [fst snd] in F1.
    destruct F1 as [H|[H|[H|H]]]; lia.
Qed.
#[using="st m0 A cur CLO RF0 ARNG PLB"] Lemma hsafe_W0 : hsafeW (W0c []).
Proof.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomG as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  apply hsafe_of. cbn [app]. unfold hsafe_iv.
  apply Forall_cons; [left; cbn [fst]; exact CLO|]. apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [right; right; left; cbn [fst snd]; lia|].
  apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia|]. apply Forall_cons; [right; left; cbn [fst snd]; clear - PFS1 PFS2; lia|].
  apply Forall_cons; [right; right; right; cbn [fst snd]; lia| apply Forall_nil].
Qed.
#[using="st A cur CLO RF0 ARNG PLB HPURE HV0"] Lemma hview_now0 : forall m, munch (W0c []) m0 m -> wmono asegs m0 m -> hview m.
Proof. intros m MU WM. exact (hview_frame (W0c []) m0 m HV0 MU WM hsafe_W0). Qed.

Definition vw_ok (VWc : list ivl) : Prop := Forall (fun iv : ivl => exists h, In h hvs /\ hvA h <= fst iv /\ snd iv <= hvA h + (hvCap h + 1)) VWc.
#[using="Type"] Lemma vw_ok_nil : vw_ok []. Proof. constructor. Qed.
#[using="st m0 A cur CLO RF0 ARNG PLB HPURE"] Lemma W0c_fsw : forall VWc, vw_ok VWc -> Forall (fsw_iv FI) (W0c VWc).
Proof.
  intros VWc OK. pose proof (proj1 hsafe_W0) as F0. cbn [app] in F0 |- *.
  inversion_clear F0 as [|? ? A1 F1]. inversion_clear F1 as [|? ? A2 F2]. inversion_clear F2 as [|? ? A3 F3].
  inversion_clear F3 as [|? ? A4 F4]. inversion_clear F4 as [|? ? A5 F5]. inversion_clear F5 as [|? ? A6 _].
  repeat (apply Forall_cons; [assumption|]).
  eapply Forall_impl; [| exact OK]. intros [a b] (h & Hh & H1 & H2). cbn [fst snd] in *.
  destruct (HPURE h Hh) as (LC & _ & _ & _ & (R1 & R2 & R3 & R4)). left. unfold app_iv, SH_HI. cbn [fst snd]. lia.
Qed.

End W.
