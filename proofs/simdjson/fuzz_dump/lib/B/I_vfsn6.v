(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import I_pck I_pcrr I_pcbits I_pcseg I_pchead I_pcfmt I_pcd6 I_pcfmt6 I_vprintfw.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import FX_lib F_memset F_memcpy F_fwritex Fe_pop_arg Fe_printf_iface Fe_printf_core Fe_printf_snsink F_sn_write F_towrite Fe_vfprintf.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Fe_pkit F_achk I_memsetw Fe_icalls Fe_vsnprintf.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad PrintfModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.

Definition pfcells6 (m : mem) : Prop := pfcells m /\ ro_cells bsegs m 0x170068 [C8 (Z_to_bv 64 0x15e39c)].

Definition PCOK_el (fmt : list Z) (args : list parg) (slots : list word) (A VA lo : Z) (m : mem) : Prop :=
  (exists f, FMT6 f /\ fmt = f ++ [0]) /\ 0 <= VA /\ VA + 16 < 2^63 /\ pctx m /\ pfcells6 m.

Lemma zb_zb8_nul : forall f, zb (f ++ [0]) = zb8 f ++ [z8].
Proof. intros f. unfold zb, zb8, z8. rewrite map_app. reflexivity. Qed.

Lemma FMT6_cstr : forall m A f, FMT6 f -> bytes_at bsegs m A (zb (f ++ [0])) -> cstr_at m A (zb8 f).
Proof.
  intros m A f FM BY. rewrite zb_zb8_nul in BY. split; [exact BY|].
  apply zb8_nonul. destruct FM as [(c & CC & ->) | ->]; [destruct CC as [-> | [-> | ->]] |]; reflexivity.
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Definition ivfA_post (usp Fp A VA : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR (Z_to_bv 64 0x6e6a4) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 Fp)
                  (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 VA) a3 a4 a5 a6 a7 (Z_to_bv 64 VA) s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x15809c) fc None m' (seg_rom bsegs)
    /\ munch [(usp - 2368, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -48)
    /\ rw_cells bsegs m' (usp + -48) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ivfsn_walkA : forall (usp Fp A VA lo : Z) (f : list Z)
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 2368 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 -> 0 <= Fp < 2^64 ->
  FMT6 f -> cstr_at m A (zb8 f) -> (A + Z.of_nat (length f) + 1 <= lo \/ usp <= A) -> A + 8 <= 2^47 -> chk_ok m A (Z.of_nat (length f) + 1) ->
  0 <= VA -> VA + 16 < 2^63 ->
  pctx m -> pfcells m -> mem_inv bsegs m ->
  evt bsegs (ivfA_post usp Fp A VA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 A) (Z_to_bv 64 VA) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x69f94) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until m. intros ST LO LOLO SPH S16 FP0 FM CSA AB AH CHKA VA0 VAH PCX PFC MI.
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(usp - 2368, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  pose proof (cstr_bound _ _ _ CSA) as (A0 & _).
  destruct PFC as (AI & GCF & CPF & RVP & RVF).
  carve_frame 48%nat ST. rename FR into FRf.
  apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FRf; [| reflexivity]. cbn [mk_CB_cells app] in FRf.
  zhide.
  xsteps_to 0x87788%Z.
  call try_init_spec; [exact AI | rewrite EU48; exact ST | rewrite EU48; lia | lia | assumption |].
  xsteps_to 0x6db6c%Z.
  rename POST into ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CSA1 : cstr_at mm A (zb8 f)) by
      (apply (cstr_agree m mm _ _ CSA); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; rewrite ?length_zb8 in Hx; lia);
    assert (CHKA1 : chk_ok mm A (Z.of_nat (length f) + 1)) by
      (eapply chk_ok_agree; [exact CHKA | lia | destruct FM as [(?c & _ & ->) | ->]; cbn [length]; lia
       | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
    assert (PCX1 : pctx mm) by
      (apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]) end.
  call (pcom6_spec RIP A f VA lo);
    [ reflexivity | reflexivity | exact FM | exact CSA1 | rewrite EU48; lia | exact AH
    | exact ST | rewrite EU48; lia | (unfold kHighShadowEnd; lia) | rewrite EU48; lia
    | rewrite EU48; Z.div_mod_to_equations; lia | lia | lia | exact CHKA1 | exact PCX1 | assumption | ].
  clear CSA1 CHKA1 PCX1. rename POST into ST. rewrite EU48 in ST.
  xsteps_to 0x15809c%Z.
  apply evt_done. unfold ivfA_post. do 13 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FRf.
Qed.
End WithRIP.

Lemma ivfsn_walkB : forall (usp VA lo : Z)
    (ra' ra gp tp t0 t1 t2 s0 s1 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk bsegs m lo (usp + -48) -> lo <= usp + -48 -> usp <= 2^47 ->
  rw_cells bsegs m (usp + -48) [C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom bsegs))
                 /\ stk bsegs m lo usp)
    (MS (mkR ra' (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6e6a4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO UT FRf MI.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  zhide.
  do 6 lstep.
  release_frame FRf ST usp.
  apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.

Section Proof6.
Hypothesis RIP : rip_stmt.

Local Ltac tr_chk C MU := apply (chkr_munch _ _ _ _ _ C MU); intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia.

Theorem ivfsn_proof : ivfsn_stmt PCOK_el.
Proof using RIP.
  unfold ivfsn_stmt. intros until o. cbv zeta.
  intros -> -> -> FH FR CKC DST BY HF P1 VAA AOK MODEL FPF ROOM Hn Hbufp ST LO GLO Q47 Q16 SSP MI FRM HA0 HA QF FVA VAHI QCK CKF CKHI
    DD1 DD2 DD3 GD HSH IC STKC FMTC ROD CHD DSH RODFP IFX PC.
  destruct PC as ((f & FM & EF) & VA0 & VAH & PCX & PFC & RVS).
  set (q := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  unfold IVF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, kHighShadowEnd in *.
  pose proof (rw_cells_bound _ _ _ _ FH) as FB. cbn [cells_size snfile_head gfile_cells csize Nat.add] in FB.
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (FMT6_txt f FM) as (_ & FL).
  assert (LF : zlength fmt = Z.of_nat (length f) + 1) by (rewrite EF; unfold zlength; rewrite length_app; cbn [length]; lia).
  assert (CSA : cstr_at m A (zb8 f)) by (apply (FMT6_cstr m A f FM); rewrite <- EF; exact BY).
  pose proof (chkr_bound m A _ FMTC) as (_ & AHI). unfold kHighMemEnd in AHI.
  assert (CHKA : chk_ok m A (Z.of_nat (length f) + 1)) by (rewrite <- LF; exact (chkr_chk_ok m A _ FMTC)).
  assert (AB : A + Z.of_nat (length f) + 1 <= lo \/ q <= A) by (clear - HA LF QF FVA GLO; unfold zlength in HA, LF; lia).

  eapply evt_cut.
  { rewrite ESP. eapply (ivfsn_walkA RIP q Fp A VA lo f);
      first [exact ST | exact FM | exact CSA | exact AB | exact CHKA | exact PCX | exact PFC | exact MI | lia | (unfold kHighShadowEnd; lia)]. }
  cbv beta. intros ms1 P. unfold ivfA_post in P.
  destruct P as (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU1 & WM1 & MI1 & ST1 & FRf).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).

  assert (AOK1 : args_ok Fp (q + -48 - 352) 80 m1 lo (q + -48) (q + -48 - VF_FRAME) slots args).
  { replace (q + -48 - 352) with (q - 400) by lia. replace (q + -48 - VF_FRAME) with (q - 416) by (unfold VF_FRAME; lia).
    eapply args_ok_vf; [exact AOK | lia | | unfold kHighShadowEnd; lia | unfold SHADOW_HI; lia].
    eapply munch_weaken; [| exact MU1]. unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia. }
  assert (STK1 : forall p n, lo <= p -> p + n <= q + -48 -> chkr m1 p n).
  { intros p n' Hp1 Hp2. apply (chkr_munch _ m m1 p n' (STKC p n' Hp1 ltac:(lia)) MU1).
    intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI in *; lia. }
  assert (IC1 : ictx m1) by (apply (ictx_munch _ m m1 IC MU1 WM1); intros ?x ?Hx; cbn [in_rl ICR outside] in *; lia).
  assert (FMTC1 : chkr m1 A (zlength fmt)) by tr_chk FMTC MU1.
  assert (ROD1 : rod_chk m1).
  { destruct ROD as (R1 & R2 & R3). split; [| split]; [tr_chk R1 MU1 | tr_chk R2 MU1 | tr_chk R3 MU1]. }
  assert (RODFP1 : rod_chk_fp m1).
  { destruct RODFP as (R1 & R2 & R3 & R4 & R5 & R6).
    split; [| split; [| split; [| split; [| split]]]]; [tr_chk R1 MU1 | tr_chk R2 MU1 | tr_chk R3 MU1 | tr_chk R4 MU1 | tr_chk R5 MU1 | tr_chk R6 MU1]. }
  assert (CHD1 : chkr m1 D (zlength o)) by tr_chk CHD MU1.
  destruct SSP as (SSP1 & SSP2). unfold got_ssp, ssp_guard in SSP1, SSP2. unfold va_area in VAA. unfold ifx_real in IFX.
  assert (LZB : length (zb fmt) = length fmt) by (unfold zb; apply length_map).
  pose proof (u64s_length slots) as LU. unfold zlength in *.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => transport_after_call bsegs m mm MU1 WM1 end.
  clear CSA CHKA PCX PFC STKC IC FMTC ROD RODFP CHD AOK.
  eapply evt_cut.
  { eapply (vfprintf_sn_proof RIP) with (Fp := Fp) (CK := CK) (D := D) (n := n) (bufp := bufp) (A := A) (VA := VA) (dn := dn) (junkd := junkd)
      (fmt := fmt) (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
      rewrite ?EU48; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, kHighShadowEnd, zlength, ifx_real.
    all: first [ reflexivity | exact FH | exact FR | exact CKC | exact DST | exact BY | exact HF | exact P1 | exact VAA | exact AOK1
               | exact MODEL | exact FPF | exact ROOM | exact ST1 | split; [exact SSP1 | exact SSP2] | exact MI1 | exact FRM | exact IC1
               | exact STK1 | exact FMTC1 | exact ROD1 | exact RODFP1 | exact CHD1 | exact DSH | exact IFX | lia ]. }
  cbv beta. intros ms2 P. unfold vfprintf_sn_post in P. rewrite ?EU48 in P.
  destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & fjunk & m2 & -> & MU2 & WM2 & MI2 & FRM2
                 & FOK & ST2 & SSP' & DST2 & CK2 & FJ2).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FRf MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FRf2.
  replace (ret_pc (Z_to_bv 64 0x6e6a4)) with (Z_to_bv 64 0x6e6a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

  eapply evt_mono.
  { eapply (ivfsn_walkB q VA lo); [exact ST2 | lia | lia | exact FRf2 | exact MI2]. }
  cbv beta. intros ms3 ((v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & ->) & ST3).
  unfold vfprintf_sn_post. rewrite <- ESP.
  exists v0, v1, v2, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, Ft, fc', fjunk, m2.
  split; [reflexivity|].
  split. { apply (munch_trans _ m m1 m2).
           - eapply munch_weaken; [| exact MU1]. unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia.
           - eapply munch_weaken; [| exact MU2]. unfold sub_fp; intros ?x ?Hx; cbn [outside] in *; lia. }
  split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact FOK|].
  split; [exact ST3|]. split; [exact SSP'|]. split; [exact DST2|]. split; [exact CK2| exact FJ2].
Qed.
End Proof6.
