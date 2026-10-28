(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac RzCPS NodesA SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow IcptSpec SegRw.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s I_consts I_qck I_lkit RT_iface D_defs D_kit I_read I_lift F_achk
     FX_lib FX_Layout F_snpf_common F_snpf_pop_arg F_snpf_iface I_pck I_pchead I_vprintfw I_vsnfront I_vsnstmt I_vsnevt I_vprintf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wr_at_sub_ : forall (m : mem) a n a' n', wr_at ctasegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at ctasegs m a' n'.
Proof.
  intros m a n a' n' (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma guard_cell_ex : forall m : mem, exists g, ro_cells ctasegs m ssp_guard [C8 g].
Proof.
  intros m. destruct (seg_rw_ok_sound ctasegs ssp_guard 8 ltac:(vm_compute; reflexivity) m) as [W S].
  destruct (stk_bytes_n ctasegs m ssp_guard 8 S) as (bs & Hl & B).
  exists (le_bytes_to_word bs). split; [cbn; tauto|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r, (le8_of_bytes bs Hl). exact B.
Qed.

(* [comment removed for export] *)
Lemma evargs_lo_mono : forall m lo lo' bnd D dn slots args covs,
  evargs_ok m lo bnd D dn slots args covs -> lo <= lo' -> evargs_ok m lo' bnd D dn slots args covs.
Proof.
  intros m lo lo' bnd D dn slots args. revert slots.
  induction args as [|a args IH]; intros slots covs H LE; [destruct slots; exact I|].
  destruct slots as [|w slots]; [exact H|]. destruct H as [H1 H2]. split; [| exact (IH _ _ H2 LE)].
  destruct a as [str| |i|u|u|d]; cbn [evarg_ok] in H1 |- *; try exact H1.
  destruct H1 as [(sl & BY & FB & PAD & P0 & HI & SEP & SEPD & CK) | (p & Ep & Hp & BY & FB & P0 & HI & SEP & SEPD & CK)].
  - left. exists sl. repeat (split; [first [assumption | lia]|]). exact CK.
  - right. exists p. repeat (split; [first [assumption | lia]|]). exact CK.
Qed.

Section Lift.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_PF : forall Σ m, ART RT Σ m -> pf_consts m.
Hypothesis AF_VSN : forall Σ m, ART RT Σ m -> vsncells m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, STATIC_SPLIT, kHighShadowEnd, SHADOW_LO, SHADOW_HI in *; lia.

(* [comment removed for export] *)
Lemma ssp_of_art : forall Σ m, ART RT Σ m -> exists g, FX_Layout.ssp_cells m g.
Proof using AF.
  intros Σ m H. destruct (guard_cell_ex m) as (g & G). exists g. split; [| exact G].
  exact (proj1 (af_got_lib RT AF Σ m H)).
Qed.

(* [comment removed for export] *)
Lemma evargs_of_vargs : forall Σ m sp lo D n dn slots args covs, ART RT Σ m -> dn <= n ->
  vargs_okx RT Σ m sp lo D n slots args covs -> evargs_ok m lo (bv_unsigned sp) D dn slots args covs.
Proof using AF_SHW.
  intros Σ m sp lo D n dn slots args covs ART0 LE. revert slots covs.
  induction args as [|a args IH]; intros slots covs H; [destruct slots; exact I|].
  destruct slots as [|w slots]; [exact H|]. destruct H as [H1 H2]. split; [| exact (IH _ _ H2)].
  destruct a as [str| |i|u|u|d]; cbn [varg_okx varg_ok evarg_ok] in H1 |- *; try exact H1.
  pose proof (zlength_nonneg_ str) as S0.
  destruct H1 as [(sl & BY & FB & L40 & PAD & P0 & HI & SEP & SEPD & AC & RC) | (p & Ep & Hp & BY & FB & L40 & P0 & HI & SEP & SEPD & AC & RC)].
  - left. exists sl. repeat (split; [first [assumption | lia]|]).
    apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia | exact AC | exact RC].
  - right. exists p. repeat (split; [first [assumption | lia]|]).
    apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia | exact AC | exact RC].
Qed.

(* [comment removed for export] *)
Lemma vsn_lift : forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (D n A : Z) (fmt : list Z) (slots : list word) (args : list parg) (o : list Z) (lo : Z) (pc : Z) (X : Z),
  mat_stable PMc ->
  vfmt_ok m A fmt args o ->
  vargs_okx RT Σ m sp lo D n slots args (vcovs fmt args) ->
  1 <= n -> n < 2^31 -> zlength o <= n - 1 -> 0 < D -> D + n <= USTACK_TOP - 16 -> (D + n <= 0x10000 \/ SEGTOP_A <= D) ->
  checked_dst RT Σ m sp D n ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> X + 64 <= RT_STACK ->
  (* [comment removed for export] *)
  (forall (body : list Z) (junk : list byte) (g : word) (lo' : Z), let usp := bv_unsigned sp in
     fmt = body ++ [0] -> Forall (fun c => 0 < c < 256) body -> (1 <= length body)%nat ->
     stk ctasegs m lo' usp -> lo' <= usp - X -> kHighShadowEnd + 8 <= lo' -> usp <= USTACK_TOP - 16 -> usp mod 16 = 0 ->
     chkr m A (zlength fmt) -> evargs_ok m lo' usp D (zlength o + 1) slots args (vcovs fmt args) ->
     rw_cells ctasegs m D [CB (Z.to_nat (zlength o + 1)) junk] -> chkr m D (zlength o + 1) -> (D + (zlength o + 1) <= lo' \/ usp <= D) ->
     ictx m -> (forall p k, lo' <= p -> p + k <= usp -> chkr m p k) -> rod_chk m -> pfcells m -> vsncells m -> FX_Layout.ssp_cells m g ->
     evt ctasegs (ivsn_post usp D o ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo' m)
       (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 pc) fc None m (seg_rom ctasegs))) ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc pc m)))
    (vsn_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 D o lo m).
Proof using AF RIP AF_SHW AF_PF AF_VSN.
  intros until X. intros MST VF VARGS Hn N31 OLE D0 DH DNS CDST ART0 MI0 CALL XS RUN.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_PF Σ m ART0) as (PFC & IC & ACCF & ACCP & ACCX & ACCN & _).
  pose proof (AF_VSN Σ m ART0) as VSN.
  destruct (ssp_of_art Σ m ART0) as (g & SSP).
  destruct VF as (BY & HF & HA0 & HA & ACCA & P1 & MODEL & FPC & OK & FZ).
  destruct (fmtz_ok_body fmt FZ) as (body & EF & FB & L1).
  pose proof (zlength_nonneg_ o) as O0.
  assert (LZF : zlength fmt = Z.of_nat (length body) + 1) by (rewrite EF; unfold zlength; rewrite length_app; cbn [length]; lia).
  destruct CDST as (CD & DCL & DWR).
  (* [comment removed for export] *)
  assert (CHDn : chkr m D n) by (destruct (CD ltac:(lia)) as (AC & RC); apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| exact AC| exact RC]).
  assert (CHD : chkr m D (zlength o + 1)) by (apply (chkr_sub m D n D (zlength o + 1) CHDn); lia).
  destruct (wr_at_rw_CB m D (zlength o + 1) (wr_at_sub_ m D n D (zlength o + 1) DWR ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (junk & DST).
  assert (SEPD : D + (zlength o + 1) <= lo \/ usp <= D).
  { destruct (range_side D n lo usp); [| ul| lia| right; lia| left; lia].
    intros i Hi. destruct (aclient_split RT AF Σ m usp (D + i) ART0 (DCL i Hi)); [left; lia| right; ul]. }
  (* [comment removed for export] *)
  assert (FMTC : chkr m A (zlength fmt)).
  { apply (chkr_of RT AF_SHW Σ m _ _ ART0); [ul| exact ACCA| right; right; right; ul]. }
  (* [comment removed for export] *)
  assert (ROD : rod_chk m).
  { split; [| split]; (apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]). }
  (* [comment removed for export] *)
  pose proof (stk_split ctasegs m lo (lo + 64) usp ST ltac:(ul)) as (STa & STb).
  assert (STKC : forall p k, lo + 64 <= p -> p + k <= usp -> chkr m p k).
  { intros p k H1 H2. destruct (Z_lt_le_dec 0 k) as [NP|NN].
    - apply (chkr_of RT AF_SHW Σ m p k ART0); [ul| | ].
      + apply (af_acc_stack RT AF Σ m p k ART0); ul.
      + right; right; left. ul.
    - split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul. }
  assert (EV : evargs_ok m (lo + 64) usp D (zlength o + 1) slots args (vcovs fmt args)).
  { apply (evargs_lo_mono m lo (lo + 64)); [| lia]. exact (evargs_of_vargs Σ m sp lo D n (zlength o + 1) slots args _ ART0 ltac:(lia) VARGS). }
  assert (W1 : evt ctasegs (ivsn_post usp D o ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (lo + 64) m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc pc m)).
  { unfold entry_st. rewrite ESP.
    apply (RUN body junk g (lo + 64) EF FB L1 STb); first [assumption | ul | (destruct SEPD; [left; lia| right; lia])]. }
  lazymatch type of W1 with evt ctasegs _ ?XX =>
    assert (W1' : forall ms, eq XX ms -> evt ctasegs _ ms) by (intros ms <-; exact W1) end.
  clear W1 RUN.
  apply (cps_realizes ctasegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  unfold vsn_post. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  destruct PO as (m' & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & -> & MU & WM & MI & ST' & DC).
  destruct (icpt_after RT AF Σ m m' usp lo _ D (zlength o + 1) ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [right; ul| left; lia]. }
  { intros i Hi. apply DCL. lia. }
  assert (ST2 : stk ctasegs m' lo usp).
  { apply (stk_merge ctasegs m' lo (lo + 64) usp); [| exact ST'| ul].
    apply (stk_transport_disjoint ctasegs _ _ _ _ _ STa MU WM). cbn [disjoint_from].
    split; [left; lia|]. split; [| exact I].
    destruct SEPD as [DS|DS]; [right; lia| left; unfold RT_STACK in *; lia]. }
  exists m'. split; [rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST2]]]|].
  split; [exact PRES|].
  destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB.
Qed.

Theorem vsnprintf_ok : vsnprintf_icontract RT.
Proof using AF RIP AF_SHW AF_PF AF_VSN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D n A VA fmt slots args o lo
    FDO MST -> -> -> -> VF VAA QVA VAH DVA VARGS Hn N31 OLE D0 DH DNS CDST ART0 MI0 CALL.
  pose proof (zlength_nonneg_ o) as O0. pose proof (u64s_length slots) as LU.
  apply (vsn_lift Σ PMc ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 VA) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D n A
           fmt slots args o lo e_vsnprintf 8064 MST VF VARGS Hn N31 OLE D0 DH DNS CDST ART0 MI0 CALL ltac:(unfold RT_STACK; lia)).
  intros body junk g lo'. cbv zeta. intros EF FB L1 ST LO LOLO UHI U16 FMTC EV DST CHD SEPD IC STKC ROD PFC VSN SSP.
  destruct VF as (BY & HF & HA0 & HA & ACCA & P1 & MODEL & FPC & OK & FZ). subst fmt.
  apply (ivsn_evt RIP (bv_unsigned sp) D n A VA lo' body args slots o junk) with (g := g); try assumption.
  all: unfold USTACK_TOP, zlength in *; lia.
Qed.

Theorem snprintf_ok : snprintf_icontract RT.
Proof using AF RIP AF_SHW AF_PF AF_VSN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D n A fmt stw args o lo
    FDO MST -> -> -> VF VST STH STD VARGS Hn N31 OLE D0 DH DNS CDST ART0 MI0 CALL.
  apply (vsn_lift Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D n A
           fmt ([a3; a4; a5; a6; a7] ++ stw) args o lo e_snprintf 8160 MST VF VARGS Hn N31 OLE D0 DH DNS CDST ART0 MI0 CALL ltac:(unfold RT_STACK; lia)).
  intros body junk g lo'. cbv zeta. intros EF FB L1 ST LO LOLO UHI U16 FMTC EV DST CHD SEPD IC STKC ROD PFC VSN SSP.
  destruct VF as (BY & HF & HA0 & HA & ACCA & P1 & MODEL & FPC & OK & FZ). subst fmt.
  apply (isn_evt RIP (bv_unsigned sp) D n A lo' body stw args o junk) with (g := g); try assumption.
  all: unfold USTACK_TOP, zlength in *; lia.
Qed.

Theorem printf_contracts_ok : printf_contracts RT.
Proof using AF RIP AF_SHW AF_PF AF_VSN. exact (mkPFC RT vsnprintf_ok snprintf_ok). Qed.
End Lift.
