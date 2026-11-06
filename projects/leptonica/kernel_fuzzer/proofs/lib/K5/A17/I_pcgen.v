(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import I_pck I_pcrr I_pcbits I_pcseg I_pchead I_pcdint I_pcdstr I_pcdzu I_pcfmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive pdir : Type := PDint (c : Z) | PDstr (Sa : Z) (str : list byte) | PDzu.

Definition pdir_bytes (d : pdir) : list Z :=
  match d with PDint c => [37; c] | PDstr _ _ => [37; 115] | PDzu => [37; 122; 117] end.

(* [comment removed for export] *)
Definition pitem : Type := (pdir * Z * list Z)%type.

Fixpoint ptail (ds : list pitem) : list Z :=
  match ds with
  | [] => []
  | (d, nx, t) :: r => pdir_bytes d ++ nx :: t ++ ptail r
  end.

Definition pitem_ok (it : pitem) : Prop :=
  let '(d, nx, t) := it in
  txt_ok (nx :: t) = true /\ match d with PDint c => c = 100 \/ c = 117 | _ => True end.

(* [comment removed for export] *)
Fixpoint pargs (m : mem) (q lo ap : Z) (ds : list pitem) : Prop :=
  match ds with
  | [] => True
  | (d, _, _) :: r =>
      match d with
      | PDstr Sa str =>
          ro_cells asegs m ap [C8 (Z_to_bv 64 Sa)] /\ cstr_at m Sa str /\ 0 < Sa
          /\ (Sa + Z.of_nat (length str) + 1 <= lo \/ q <= Sa) /\ Sa + Z.of_nat (length str) + 1 < 2^47
          /\ chk_ok m Sa (Z.of_nat (length str) + 1)
      | _ => True
      end /\ pargs m q lo (ap + 8) r
  end.

(* [comment removed for export] *)
Lemma pargs_munch : forall ds W m m' q lo ap, pargs m q lo ap ds -> munch W m m' ->
  (forall x, (x < lo \/ q <= x) -> outside W x) -> q <= ap -> kHighShadowEnd + 8 <= lo -> q <= 2^47 ->
  pargs m' q lo ap ds.
Proof.
  induction ds as [|[[d nx] t] r IH]; intros W m m' q lo ap H MU HW QAP LOLO Q47; [exact I|].
  cbn [pargs] in *. destruct H as [Hd Hr]. split; [| apply (IH W m m' q lo (ap + 8) Hr MU HW); lia].
  destruct d as [c|Sa str|]; [exact I| |exact I].
  destruct Hd as (SL & CS & S0 & SEP & SH & CHK).
  split; [apply (ro_cells_agree asegs m m' _ _ SL); apply (agree_of_munch _ _ _ _ MU); intros x Hx; apply HW;
          cbn [cells_size csize Nat.add] in Hx; lia|].
  split; [apply (cstr_agree m m' _ _ CS); apply (agree_of_munch _ _ _ _ MU); intros x Hx; apply HW; lia|].
  split; [exact S0|]. split; [exact SEP|]. split; [exact SH|].
  eapply chk_ok_agree; [exact CHK | lia | lia |].
  apply (agree_of_munch _ _ _ _ MU). intros x Hx. apply HW. unfold kHighShadowEnd in LOLO. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ptail_cons_bytes : forall m p d nx t r,
  bytes_at asegs m p (zb8 (ptail ((d, nx, t) :: r)) ++ [z8]) ->
  bytes_at asegs m p (zb8 (pdir_bytes d ++ [nx]))
  /\ bytes_at asegs m (p + Z.of_nat (length (pdir_bytes d))) (zb8 (nx :: t))
  /\ bytes_at asegs m (p + Z.of_nat (length (pdir_bytes d)) + Z.of_nat (length (nx :: t))) (zb8 (ptail r) ++ [z8]).
Proof.
  intros m p d nx t r H. cbn [ptail] in H.
  replace (pdir_bytes d ++ nx :: t ++ ptail r) with (pdir_bytes d ++ (nx :: t) ++ ptail r) in H by reflexivity.
  rewrite !zb8_app, <- !app_assoc in H.
  pose proof H as H'.
  apply (proj1 (bytes_at_app asegs m p _ _)) in H. destruct H as [_ H]. rewrite length_zb8 in H.
  apply (proj1 (bytes_at_app asegs m _ _ _)) in H. destruct H as [H2 H3]. rewrite length_zb8 in H3.
  split; [| split; [exact H2 | exact H3]].
  rewrite zb8_app.
  replace (zb8 (pdir_bytes d) ++ zb8 (nx :: t) ++ zb8 (ptail r) ++ [z8])
    with ((zb8 (pdir_bytes d) ++ zb8 [nx]) ++ zb8 t ++ zb8 (ptail r) ++ [z8]) in H'
    by (rewrite <- app_assoc; reflexivity).
  apply (proj1 (bytes_at_app asegs m p _ _)) in H'. exact (proj1 H').
Qed.

Lemma ptail_length_cons : forall d nx t r,
  Z.of_nat (length (ptail ((d, nx, t) :: r)))
  = Z.of_nat (length (pdir_bytes d)) + Z.of_nat (length (nx :: t)) + Z.of_nat (length (ptail r)).
Proof. intros. cbn [ptail]. rewrite length_app. cbn [length]. rewrite length_app. lia. Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Notation PCW q := [(q + -2320, q + -2240); (q + -2216, q + -2176)]%Z.

Definition pct_post (q : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (PCW q) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q + -2240)
    /\ (exists junk, rw_cells asegs m' (q + -2216) [CB 40 junk]).

(* [comment removed for export] *)
Lemma pcom_tail_spec : forall (ds : list pitem) (q p ap lo : Z) (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  Forall pitem_ok ds ->
  sp = Z_to_bv 64 (q + -2240) -> s0 = Z_to_bv 64 q -> s2 = Z_to_bv 64 10 -> s3 = Z_to_bv 64 p -> s4 = Z_to_bv 64 88672 ->
  s5 = Z_to_bv 64 ap -> s7 = Z_to_bv 64 9 -> s8 = Z_to_bv 64 (q + -2184) -> s9 = Z_to_bv 64 12297829382473034410 ->
  s10 = Z_to_bv 64 (-1) -> s11 = Z_to_bv 64 37 ->
  bytes_at asegs m p (zb8 (ptail ds) ++ [z8]) -> p + Z.of_nat (length (ptail ds)) + 1 <= lo -> 0 <= p ->
  rw_cells asegs m (q + -2216) DIR0 ->
  rw_cells asegs m (q + -104) (pcom_saved ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11') ->
  pargs m q lo ap ds -> q <= ap -> ap + 8 * Z.of_nat (length ds) < 2^63 ->
  pctx m ->
  stk asegs m lo (q + -2240) -> lo <= q + -2320 -> kHighShadowEnd + 8 <= lo -> q <= 2^47 -> q mod 16 = 0 ->
  mem_inv asegs m ->
  evt asegs (pct_post q ra0 gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4fdec) fc None m (seg_rom asegs)).
Proof using RIP.
  induction ds as [|[[d nx] t] r IH]; intros until m;
    intros OK -> -> -> -> -> -> -> -> -> -> -> BY AB P0 DIR FRh PA QAP APH PCX ST LO LOLO Q47 Q16 MI.
  - (* [comment removed for export] *)
    cbn [ptail zb8 map app] in BY.
    pose proof (munch_refl (PCW q) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold kHighShadowEnd in LOLO.
    call (pcom_end_spec q p ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11');
      [ reflexivity | reflexivity | reflexivity | reflexivity | exact BY
      | eapply (cells_byte _ _ _ 36%nat z8); [exact DIR | reflexivity | lia] | exact FRh | lia | assumption | ].
    apply evt_done. unfold pct_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    eexists. apply rw_forget in DIR. exact DIR.
  - (* [comment removed for export] *)
    inversion OK as [|x l OKd OKr]; subst x l. destruct OKd as [OKT CC].
    destruct (ptail_cons_bytes m p d nx t r BY) as (B1 & B2 & B3).
    rewrite ptail_length_cons in AB.
    pose proof (munch_refl (PCW q) m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NX : 0 < nx < 256).
    { cbn [txt_ok forallb] in OKT. apply andb_prop in OKT. destruct OKT as [H _]. apply andb_prop in H. destruct H as [H _].
      apply andb_prop in H. destruct H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. }
    cbn [pargs] in PA. destruct PA as [PAd PAr]. cbn [length] in APH.
    assert (HW : forall x, x < lo \/ q <= x -> outside (PCW q) x) by (intros x Hx; cbn [outside]; lia).
    (* [comment removed for export] *)
    assert (STEP : evt asegs (pcd_post q (p + Z.of_nat (length (pdir_bytes d))) (ap + 8) gp tp (Z_to_bv 64 q) (Z_to_bv 64 10)
                                (Z_to_bv 64 88672) (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184)) (Z_to_bv 64 12297829382473034410)
                                (Z_to_bv 64 (-1)) (Z_to_bv 64 37) F fc lo m)
              (MS (mkR ra (Z_to_bv 64 (q + -2240)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 10) (Z_to_bv 64 p)
                       (Z_to_bv 64 88672) (Z_to_bv 64 ap) s6 (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184)) (Z_to_bv 64 12297829382473034410)
                       (Z_to_bv 64 (-1)) (Z_to_bv 64 37) t3 t4 t5 t6)
                  F (Z_to_bv 64 0x4fdec) fc None m (seg_rom asegs))).
    { destruct d as [c|Sa str|]; cbn [pdir_bytes length app] in *.
      - replace (p + Z.of_nat 2) with (p + 2) by lia.
        apply (pcom_dint_spec q p ap c nx lo); first [reflexivity | exact CC | exact NX | exact B1 | exact DIR | exact ST | exact MI | lia].
      - destruct PAd as (SL & CS & S0 & SEP & SH & CHK). replace (p + Z.of_nat 2) with (p + 2) by lia.
        apply (pcom_dstr_spec RIP q p ap nx Sa str lo);
          first [reflexivity | exact NX | exact B1 | exact DIR | exact SL | exact CS | exact S0 | exact SEP | exact SH | exact CHK
                | exact PCX | exact ST | exact LOLO | exact MI | lia].
      - replace (p + Z.of_nat 3) with (p + 3) by lia.
        apply (pcom_dzu_spec q p ap nx lo); first [reflexivity | exact NX | exact B1 | exact DIR | exact ST | exact MI | lia]. }
    eapply evt_cut; [exact STEP|]. clear STEP. cbv beta.
    intros ms1 (ra1 & u0 & u1 & u2 & v1 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v6 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & (jd & DIR1)).
    set (p1 := p + Z.of_nat (length (pdir_bytes d))) in *.
    assert (P1R : p <= p1 <= p + 3) by (unfold p1; destruct d; cbn [pdir_bytes length]; lia).
    (* [comment removed for export] *)
    eapply evt_cut.
    { apply (pcom_setup_spec q jd); first [reflexivity | exact DIR1 | exact Q16 | exact MI1 | lia]. }
    cbv beta. intros ms2 (ra2 & w0 & w1 & w2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m2 & -> & MU2 & WM2 & MI2 & DIR2).
    assert (MU12 : munch (PCW q) m m2).
    { apply (munch_trans _ m m1 m2); [exact MU1|]. eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside] in *. lia. }
    assert (WM12 : wmono asegs m m2) by exact (wmono_trans _ _ _ _ WM1 WM2).
    assert (B2' : bytes_at asegs m2 p1 (zb8 (nx :: t))).
    { apply (bytes_at_agree asegs m m2 _ _ B2). apply (agree_of_munch _ _ _ _ MU12). intros x Hx. apply HW.
      rewrite length_zb8 in Hx. unfold p1 in *. lia. }
    eapply evt_cut; [eapply (pcom_scan_spec (nx :: t) p1); [reflexivity | reflexivity | exact OKT | exact B2' | exact MI2] |].
    cbv beta. intros ms3 (a0' & ->).
    (* [comment removed for export] *)
    assert (B3' : bytes_at asegs m2 (p1 + Z.of_nat (length (nx :: t))) (zb8 (ptail r) ++ [z8])).
    { apply (bytes_at_agree asegs m m2 _ _ B3). apply (agree_of_munch _ _ _ _ MU12). intros x Hx. apply HW.
      rewrite length_app, length_zb8 in Hx. change (length [z8]) with 1%nat in Hx. unfold p1 in *. lia. }
    assert (FRh2 : rw_cells asegs m2 (q + -104) (pcom_saved ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11')).
    { apply (rw_cells_transport asegs _ m m2 _ _ FRh MU12 WM12). unfold pcom_saved. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (PA2 : pargs m2 q lo (ap + 8) r) by (apply (pargs_munch r _ m m2 q lo (ap + 8) PAr MU12 HW); lia).
    assert (PCX2 : pctx m2).
    { apply (pctx_munch _ m m2 PCX MU12 WM12). intros x Hx. unfold in_PCR in Hx. apply HW. unfold kHighShadowEnd in LOLO. lia. }
    assert (ST2 : stk asegs m2 lo (q + -2240)).
    { apply (stk_transport asegs _ m1 m2 lo (q + -2240) ST1 MU2 WM2). intros x Hx. left. cbn [outside]. lia. }
    eapply evt_mono.
    { eapply (IH q (p1 + Z.of_nat (length (nx :: t))) (ap + 8) lo ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11');
        first [reflexivity | exact OKr | exact B3' | exact DIR2 | exact FRh2 | exact PA2 | exact PCX2 | exact ST2 | exact LOLO
              | exact Q16 | exact MI2 | unfold p1 in *; lia ]. }
    cbv beta. intros ms4 (y0 & y1 & y2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & DIR3).
    unfold pct_post. do 16 eexists. split; [reflexivity|].
    split; [exact (munch_trans _ _ _ _ MU12 MU3)|]. split; [exact (wmono_trans _ _ _ _ WM12 WM3)|].
    split; [exact MI3|]. split; [exact ST3 | exact DIR3].
Qed.

(* [comment removed for export] *)
Lemma pcom_gen_spec : forall (A : Z) (t0 : list Z) (ds : list pitem) (ap lo : Z)
    ra sp gp tp t0' t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
  txt_ok t0 = true -> Forall pitem_ok ds -> (1 <= length (t0 ++ ptail ds))%nat ->
  cstr_at m A (zb8 (t0 ++ ptail ds)) -> A + Z.of_nat (length t0) + Z.of_nat (length (ptail ds)) + 1 <= lo ->
  pargs m (bv_unsigned sp) lo ap ds -> bv_unsigned sp <= ap -> ap + 8 * Z.of_nat (length ds) < 2^63 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 ->
  chk_ok m A (Z.of_nat (length t0) + Z.of_nat (length (ptail ds)) + 1) -> pctx m -> mem_inv asegs m ->
  evt asegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4fcac) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until m. intros -> -> OK0 OKD L1 CS AB PA QAP APH ST LO LOLO SPH S16 CHK PCX MI.
  set (q := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (cstr_bound _ _ _ CS) as (A0 & _).
  assert (LF : Z.of_nat (length (zb8 (t0 ++ ptail ds))) = Z.of_nat (length t0) + Z.of_nat (length (ptail ds)))
    by (rewrite length_zb8, length_app; lia).
  pose proof CS as (BYA & _). rewrite zb8_app, <- app_assoc in BYA.
  apply (proj1 (bytes_at_app asegs m A _ _)) in BYA. rewrite length_zb8 in BYA. rename BYA into BYP.
  (* [comment removed for export] *)
  pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HW : forall x, x < lo \/ q <= x -> outside [(q - PCOM_DEPTH, q)] x) by (intros x Hx; cbn [outside]; lia).

  call (pcom_head_spec RIP q A ap (zb8 (t0 ++ ptail ds)) lo);
    [ reflexivity | reflexivity | reflexivity | exact ST | lia | exact LOLO | lia | exact S16
    | exact CS | rewrite length_zb8; exact L1 | rewrite LF; lia | rewrite LF; exact CHK
    | exact PCX | exact MI | ].
  destruct PC1 as (jb & FRb). destruct PC2 as (jd & DIR). destruct POST as (ja & FRa). rename PC into ST, PC0 into FRh.
  call (pcom_setup_spec q jd); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR | exact S16 | lia | assumption | ].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BY0' : bytes_at asegs mm A (zb8 t0)) by
      (apply (bytes_at_agree asegs m mm _ _ (proj1 BYP)); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; apply HW;
       rewrite length_zb8 in Hx; lia);
    assert (BYT' : bytes_at asegs mm (A + Z.of_nat (length t0)) (zb8 (ptail ds) ++ [z8])) by
      (apply (bytes_at_agree asegs m mm _ _ (proj2 BYP)); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; apply HW;
       rewrite length_app, length_zb8 in Hx; change (length [z8]) with 1%nat in Hx; lia);
    assert (PA' : pargs mm q lo ap ds) by (apply (pargs_munch ds _ m mm q lo ap PA MU HW); lia);
    assert (PCX' : pctx mm) by
      (apply (pctx_munch _ m mm PCX MU); [assumption | intros ?x ?Hx; unfold in_PCR in Hx; apply HW; unfold kHighShadowEnd in LOLO; lia])
  end.
  eapply evt_cut; [eapply (pcom_scan_spec t0 A); [reflexivity | reflexivity | exact OK0 | exact BY0' | assumption] |].
  intros ms' (a0' & ->).
  lazymatch goal with H : rw_cells asegs _ (q + -2216) DIR0 |- _ => rename H into DIR1 end.
  call (pcom_tail_spec ds q (A + Z.of_nat (length t0)) ap lo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
    [ exact OKD | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | exact BYT' | lia | lia | exact DIR1 | exact FRh | exact PA' | lia | lia | exact PCX'
    | exact ST | lia | exact LOLO | lia | exact S16 | assumption | ].
  destruct POST as (jd4 & DIR4).
  release_frame FRa PC (q + -2216). release_frame DIR4 PC (q + -2176). release_frame FRb PC (q + -104).
  unfold pcom_saved in FRh. release_frame FRh PC q.
  apply evt_done. unfold pcom_post. rewrite (unsigned_lit q) by lia. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact PC].
Qed.

End WithRIP.
