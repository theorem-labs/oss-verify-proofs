(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_m2s I_consts I_qck D_kit RT_iface F_imemmove I_imvw I_imv Sj_akit Sj_acps Sj_hkit Pj_os_xsputnA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Export FX_lib El_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Local Ltac hideK H := lazymatch type of H with ?T => change (keep T) in H end.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Definition imv_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(Dst, Dst + N); (q - 2224, q)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo q
    /\ rw_cells bsegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at bsegs m' Src src.

Lemma imv_callZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q Dst Src N : Z) (src junk : list byte) (lo : Z),
  bytes_at bsegs m Src src -> length src = Z.to_nat N -> rw_cells bsegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (1 <= N)%Z -> (0 <= Src)%Z -> (Src + N <= 2^47)%Z -> (0 <= Dst)%Z -> (Dst + N <= 2^47)%Z ->
  (0 <= q <= 2^47)%Z -> stk bsegs m lo q -> (lo <= q - 2224)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (Src + N <= lo \/ q <= Src)%Z -> (Dst + N <= lo \/ q <= Dst)%Z ->
  chkr m Src N -> chkr m Dst N -> ictx m -> mem_inv bsegs m ->
  evt bsegs (imv_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7e870) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros BA LEN DC SEP HN HS HS2 HD HD2 Hq ST LO HSH SEPS SEPD CKS CKD IC MI.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EN : Z.of_nat (length src) = N) by lia.
  pose proof (chkr_chk_ok m Src N CKS) as CS. pose proof (chkr_chk_ok m Dst N CKD) as CD. pose proof IC as (ICI & _ & _ & M2S).
  assert (WR : wr_at bsegs m Dst N) by (apply (rw_cells_wr_at bsegs m _ _ _ DC); cbn; lia).
  eapply evt_mono.
  { eapply (imv_spec RIP ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Dst Src src lo);
      rewrite ?Eq, ?EN.
    all: first [reflexivity | exact ST | exact BA | exact WR | exact CS | exact CD | exact M2S | exact ICI | exact MI | unfold kHighShadowEnd in *; lia | lia]. }
  cbv beta. intros ms' PS. unfold imv_post in PS. rewrite !Eq, !EN in PS.
  destruct PS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & ST' & BY).
  unfold imv_postZ. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. split.
  - rewrite <- LEN. apply (rw_cells_CB_intro m' Dst src BY). rewrite EN. exact (wr_at_transport bsegs m m' _ _ WR WM').
  - apply (bytes_at_agree bsegs m m' _ _ BA). apply (agree_of_munch _ m m' _ MU'). intros x Hx. rewrite EN in Hx. cbn [outside]. repeat split; first [exact I | lia].
Qed.

Section Loop.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo OS S N CAP : Z) (bs : list byte) (m0 : word -> option byte).
Hypothesis LO : (lo <= bv_unsigned sp - EL_XSPUTN_DEPTH)%Z.
Hypothesis HSH : (kHighShadowEnd + 8 <= lo)%Z.
Hypothesis SPH : (bv_unsigned sp <= 2^47)%Z.
Hypothesis LOC : os_locA OS.
Hypothesis RO : (OS + 288 <= lo)%Z.
Hypothesis RN : (0 <= N <= CAP)%Z.
Hypothesis RS : (0 <= S)%Z.
Hypothesis RS2 : (S + CAP <= 2^47)%Z.
Hypothesis SEP : ((S + CAP <= lo /\ (S + CAP <= OS \/ OS + 288 <= S)) \/ bv_unsigned sp <= S)%Z.
Hypothesis LBS : length bs = Z.to_nat CAP.

Hypothesis CKS : (0 < N)%Z -> chkr m0 S N.
Hypothesis CKD : chkr m0 (OS + 64) 64.
Hypothesis IC0 : ictx m0.
Hypothesis CC0 : client_consts m0.
Hypothesis DCC0 : el_dccA m0.
Hypothesis SHZ0 : bytes_at bsegs m0 (shad OS) (repeat z8 36).

Notation POST := (os_xsputnX_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS N m0).
Notation W := [(bv_unsigned sp - EL_XSPUTN_DEPTH, bv_unsigned sp); (OS + 40, OS + 128)]%Z.

Local Ltac offW := unfold EL_XSPUTN_DEPTH in *; intros ?x ?Hx; cbn [outside];
  unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; repeat split; first [exact I | lia].

Lemma afacts : forall m, munch W m0 m -> wmono bsegs m0 m ->
  ((0 < N)%Z -> chkr m S N) /\ chkr m (OS + 64) 64 /\ ictx m /\ client_consts m /\ el_dccA m /\ bytes_at bsegs m (shad OS) (repeat z8 36).
Proof using LO HSH LOC RO CKS CKD IC0 CC0 DCC0 SHZ0.
  clear LBS SEP RN RS RS2 SPH. intros m MU WM. pose proof (os_locA_bounds OS LOC) as (B1 & B2 & B3).
  split; [intros HC; apply (chkr_munch _ m0 m _ _ (CKS HC) MU); offW|]. split; [apply (chkr_munch _ m0 m _ _ CKD MU); offW|].
  split; [apply (ictx_munch _ m0 m IC0 MU WM); intros x Hx; cbn [in_rl ICR] in Hx; unfold EL_XSPUTN_DEPTH in *; cbn [outside]; unfold kHighShadowEnd in *; repeat split; first [exact I | lia]|].
  split; [apply (client_consts_munch _ m0 m CC0 MU); offW|]. split; [apply (el_dccA_munch _ m0 m DCC0 MU); offW|].
  apply (shz36_munch _ m0 m OS SHZ0 MU); [lia| lia| offW].
Qed.

Lemma xsputn_exit : forall (pp ep : Z) (pb : word) (dum jf : list byte) (m : word -> option byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 x18 x19 x20 x21 t3 t4 t5 t6 : word),
  PUTINV OS pp ep ->
  munch W m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp + -64) ->
  rw_cells bsegs m (bv_unsigned sp + -64) [CB 8 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m OS [C8 (Z_to_bv 64 0x168808); C8 (Z_to_bv 64 0x6aa1a8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                       C8 pb; C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 ep)] ->
  rw_cells bsegs m (OS + 64) [CB 64 dum] ->
  evt bsegs POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 N) x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x111790) fc None m (seg_rom bsegs)).
Proof using LO HSH SPH LOC RO RN RS RS2 SEP LBS.
  intros until t6. intros PI MU WM MI ST FR SBH DUM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (os_locA_bounds OS LOC) as (B1 & B2 & B3). unfold EL_XSPUTN_DEPTH, kHighShadowEnd in *.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  do 10 lstep.
  release_frame FR ST (bv_unsigned sp).
  glueZ SBH DUM.
  unfold os_xsputnX_post, sb_cellsX, EL_XSPUTN_DEPTH. sys_finish; eassumption.
Qed.

Lemma xsputn_loop : forall (k : nat) (done pp ep : Z) (pb : word) (dum jf : list byte) (m : word -> option byte)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word),
  (N - done <= Z.of_nat k)%Z -> (0 <= done < N)%Z -> PUTINV OS pp ep ->
  munch W m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp + -64) ->
  rw_cells bsegs m (bv_unsigned sp + -64) [CB 8 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m OS [C8 (Z_to_bv 64 0x168808); C8 (Z_to_bv 64 0x6aa1a8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                       C8 pb; C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 ep)] ->
  rw_cells bsegs m (OS + 64) [CB 64 dum] ->
  bytes_at bsegs m S bs ->
  evt bsegs POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 done) (Z_to_bv 64 N) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (S + done)) (Z_to_bv 64 OS) x20 (Z_to_bv 64 (-1)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x111730) fc None m (seg_rom bsegs)).
Proof using RIP LO HSH SPH LOC RO RN RS RS2 SEP LBS CKS CKD IC0 CC0 DCC0 SHZ0.
  induction k as [|k IH]; intros done pp ep pb dum jf m x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6
    HK HD PI MU WM MI ST FR SBH DUM SRC; [lia|].
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (os_locA_bounds OS LOC) as (B1 & B2 & B3). pose proof LOC as (AL16 & _).
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  destruct (afacts m MU WM) as (CKSm & CKDm & ICm & CCm & DCCm & SHZ). pose proof DCCm as (VT & _).
  unfold EL_XSPUTN_DEPTH, kHighShadowEnd in *.
  do 2 lstep.
  lstep.
  destruct (Z_lt_dec pp ep) as [LT|GE].
  2:{
    br_is true ltac:(rewrite bv_ltu_Z, !unsigned_lit by lia; apply negb_true_iff, Z.ltb_ge; lia).
    pose proof (ro_C1_of_bytes m (S + done) _ (F_imemmove.bytes_at_nth m S bs done SRC ltac:(lia))) as CB0.
    assert (EU1 : bv_unsigned (Z_to_bv 64 (S + done)) = (S + done)%Z) by (apply unsigned_lit; lia).
    set (cs := (S + done)%Z) in *.
    set (b := nth (Z.to_nat done) bs (Z_to_bv 8 0)) in *.
    do 5 lstep.

    takeZ SBH 5%nat (OS + 40)%Z SBlo. rename SBH into PUT.
    assert (SHZx : forall m', munch [(bv_unsigned sp + -64 - 16, bv_unsigned sp + -64); (OS + 40, OS + 64)]%Z m m' -> wmono bsegs m m' -> shz m' OS 288).
    { intros m' MU' WM'. change 288%Z with (8 * Z.of_nat 36)%Z. apply (shz_of_zero_run m' OS 36); [Z.div_mod_to_equations; lia| lia|].
      apply (shz36_munch _ m m' OS SHZ MU'); [lia| lia|]. intros x Hx. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in *. repeat split; first [exact I | lia]. }
    eapply evt_cut.
    { eapply (overflow_walk OS (bv_unsigned sp + -64) lo b); [lia| lia| Z.div_mod_to_equations; lia| exact SHZx| exact CCm| exact PUT| exact MI| exact ST| lia| lia| lia| lia]. }
    clear SHZ CB0. post_call bsegs m. rename PC into ST. rename POST into PUT.
    assert (RB : (0 <= bv_unsigned b < 256)%Z) by (pose proof (bv_unsigned_in_range 8 b) as X; unfold bv_modulus in X; cbn in X; lia).
    lstep.
    br_is false ltac:(rewrite bv_eqb_Z, unsigned_lit by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z; apply Z.eqb_neq; lia).
    do 2 lstep.
    lstep.
    subst cs. glueZ SBlo PUT. rename SBlo into SBH.
    destruct (Z_lt_dec (done + 1) N) as [MORE|LAST].
    + br_is true ltac:(rewrite lts_small by lia; apply Z.ltb_lt; lia).
      replace (S + done + 1)%Z with (S + (done + 1))%Z by lia.
      eapply (IH (done + 1)%Z (OS + 64)%Z (OS + 128)%Z); try eassumption; [lia | lia | right; lia].
    + br_is false ltac:(rewrite lts_small by lia; apply Z.ltb_ge; lia).
      lstep.
      replace (done + 1)%Z with N by lia.
      eapply (xsputn_exit (OS + 64)%Z (OS + 128)%Z); try eassumption. right; lia. }

  br_is false ltac:(rewrite bv_ltu_Z, !unsigned_lit by lia; apply negb_false_iff, Z.ltb_lt; lia).
  destruct PI as [[-> ->]|[-> PPR]]; [lia|].
  do 2 lstep.
  lstep.
  assert (CONT : forall (kz : Z) (y11 : word) (mm : word -> option byte), (1 <= kz <= N - done)%Z -> (kz <= OS + 128 - pp)%Z -> mm = m ->
    evt bsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 done) (Z_to_bv 64 N) (Z_to_bv 64 pp) y11 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (S + done)) (Z_to_bv 64 OS) (Z_to_bv 64 kz) (Z_to_bv 64 (-1)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x11174c) fc None mm (seg_rom bsegs))).
  { intros kz y11 mm K1 K2 ->.
    lstep.
    br_is false ltac:(rewrite bv_eqb_Z, unsigned_lit by lia; change (bv_unsigned z64) with 0%Z; apply Z.eqb_neq; lia).
    do 2 lstep.
    lstep.
    destruct (rw_cells_CB_cut3 m (OS + 64) 64 dum (pp - (OS + 64)) kz ltac:(lia) ltac:(lia) ltac:(lia) DUM) as (d1 & d2 & d3 & D1 & D2 & D3).
    replace (OS + 64 + (pp - (OS + 64)))%Z with pp in D2, D3 by lia.
    pose proof (bytes_at_sub m S bs done kz SRC ltac:(lia) ltac:(lia) ltac:(rewrite LBS; lia)) as SUB.
    clear DUM.
    eapply evt_cut.
    { eapply (imv_callZ) with (Dst := pp) (Src := (S + done)%Z) (N := kz) (junk := d2);
        [exact SUB | rewrite firstn_length_le; [reflexivity | rewrite skipn_length, LBS; lia] | exact D2 | lia | lia | lia | lia | lia | lia | lia
        | exact ST | lia | unfold kHighShadowEnd; lia | lia | lia
        | apply (chkr_sub m S N _ _ (CKSm ltac:(lia))); lia | apply (chkr_sub m (OS + 64) 64 _ _ CKDm); lia | exact ICm | assumption]. }
    clear SHZ. post_call bsegs m.
    rename PC into ST. rename PC0 into D2. clear POST.
    do 2 lstep.
    do 4 lstep.
    lstep.
    lazymatch type of D2 with rw_cells _ ?mx _ _ =>
      destruct (rw_cells_CB_join3 mx (OS + 64) _ _ _ 64 _ _ _ pp (pp + kz)%Z D1 D2 D3 ltac:(lia) ltac:(lia) ltac:(lia)) as (dum' & DUM) end.
    clear D1 D2 D3.
    destruct (Z_lt_dec (kz + done) N) as [MORE|LAST].
    + br_is false ltac:(rewrite lts_small by lia; apply negb_false_iff, Z.ltb_lt; lia).
      replace (kz + done)%Z with (done + kz)%Z by lia.
      replace (S + done + kz)%Z with (S + (done + kz))%Z by lia.
      eapply (IH (done + kz)%Z (pp + kz)%Z (OS + 128)%Z); try eassumption; [lia | lia | right; lia].
    + br_is true ltac:(rewrite lts_small by lia; apply negb_true_iff, Z.ltb_ge; lia).
      replace (kz + done)%Z with N by lia.
      eapply (xsputn_exit (pp + kz)%Z (OS + 128)%Z); try eassumption. right; lia. }
  destruct (Z_lt_dec (N - done) (OS + 128 - pp)) as [SM|BG].
  - br_is true ltac:(rewrite lts_small by lia; apply Z.ltb_lt; lia).
    eapply (CONT (N - done)%Z); [lia | lia | reflexivity].
  - br_is false ltac:(rewrite lts_small by lia; apply Z.ltb_ge; lia).
    lstep.
    eapply (CONT (OS + 128 - pp)%Z); [lia | lia | reflexivity].
Qed.

End Loop.

Theorem os_xsputnX_proof : os_xsputnX_stmt.
Proof using RIP.
  unfold os_xsputnX_stmt. intros until bs. intros ST LO HSH SPH SBF PI0 LOC RO SRB LB RN RS RS2 SEP DCC CC SHZ CKS CKD IC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (os_locA_bounds OS LOC) as (B1 & B2 & B3).
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - EL_XSPUTN_DEPTH, bv_unsigned sp); (OS + 40, OS + 128)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (LBS : length bs = Z.to_nat CAP) by lia.
  hideK SHZ.
  unfold sb_cellsX in SBF. pose proof DCC as (VT & _).
  unfold EL_XSPUTN_DEPTH, kHighShadowEnd in *.
  takeZ SBF 8%nat (OS + 64)%Z SBH. rename SBF into DUM.
  carve_frame 64%nat ST.
  do 8 lstep.
  lstep.
  destruct (Z.eq_dec N 0) as [N0|N1].
  - subst N. if_true.
    lstep.
    eapply (xsputn_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS S 0 CAP bs m) with (pp := pp) (ep := ep); try eassumption; unfold EL_XSPUTN_DEPTH, kHighShadowEnd; try lia.
  - br_is false ltac:(rewrite bv_lts_zero_l, unsigned_lit by lia; cbn [negb]; apply negb_false_iff, andb_true_iff; split; apply Z.ltb_lt; lia).
    do 6 lstep.
    replace S with (S + 0)%Z at 2 by lia.
    eapply (xsputn_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS S N CAP bs m) with (k := Z.to_nat N) (done := 0%Z) (pp := pp) (ep := ep);
      try eassumption; unfold EL_XSPUTN_DEPTH, kHighShadowEnd; try lia.
Qed.

End WithRIP.
