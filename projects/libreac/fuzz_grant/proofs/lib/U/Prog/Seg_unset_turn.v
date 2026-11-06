From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Tac Bytes ZBridge Step Arr Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SegSetModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import reac_headamp_tx_effective_c reac_headamp_default_c.
Import ListNotations.
Open Scope Z_scope.

Ltac fix_ret :=
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] => rewrite (ret_pc_even n) by (first [lia | reflexivity]) end.

Lemma land255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof. intros c Hc. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Ltac qprem := first [ reflexivity | word_eq_tac | lia | eassumption | (Z.div_mod_to_equations; lia) ].

Lemma dflt0 : dflt 0 = 0. Proof. reflexivity. Qed.
Lemma dflt1 : dflt 1 = 0. Proof. reflexivity. Qed.
Lemma dflt2 : dflt 2 = 32. Proof. reflexivity. Qed.

Ltac callE EFF HTl HTB HT4 E :=
  eapply evt_cut;
  [ eapply EFF; [reflexivity | reflexivity | reflexivity | lia | lia | right; split; [exact HTl | split; [exact HTB | exact HT4]]]
  | let ms' := fresh "ms" in
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->); fix_ret;
    rewrite ?E, ?dflt0, ?dflt1, ?dflt2 ].

Ltac callD DFL :=
  eapply evt_cut;
  [ eapply DFL; [reflexivity | lia]
  | let ms' := fresh "ms" in
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->); fix_ret;
    rewrite ?dflt0, ?dflt1, ?dflt2 ].

Ltac drive EFF DFL HTl HTB HT4 E :=
  repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 79068) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 79148) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 87448) _ _ _ _) => callE EFF HTl HTB HT4 E
    | |- evt _ _ (MS _ _ (Z_to_bv 64 87432) _ _ _ _) => callD DFL
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => brx
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end).

Ltac fin_q :=
  apply evt_done; do 19 eexists; split; [reflexivity | intros; first [lia | split; word_eq_tac]].

Section Q.
Variable x : slot_ctx.
Hypothesis EFF : reac_headamp_tx_effective_contract.
Hypothesis DFL : reac_headamp_default_contract.

Lemma q_block : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t c q : Z) (T ws : list byte),
  s0 = Z_to_bv 64 t -> s2 = Z_to_bv 64 2 -> s4 = Z_to_bv 64 q -> s5 = Z_to_bv 64 c ->
  s8 = Z_to_bv 64 3 -> s10 = Z_to_bv 64 (SPL x + 360 + 3 * c + q) -> 2 ^ 63 <= bv_unsigned s3 ->
  0 <= c < 48 -> 0 <= q < 3 -> 0 < t -> t mod 4 = 0 ->
  length T = 460%nat -> bytes_at rsegs m t T -> length ws = 144%nat -> bytes_at rsegs m (SPL x + 360) ws ->
  (forall c' q', 0 <= c' < 48 -> 0 <= q' < 3 -> tb ws (3 * c' + q') = tb T (144 + 3 * c' + q')) ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s10' t3' t4' t5' t6',
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4' s5 s6' s7 s8 s9 s10' s11 t3' t4' t5' t6')
               F (Z_to_bv 64 (if q <? 2 then 0x134dc else 0x1352c)) fc None m (seg_rom rsegs) /\
      (q < 2 -> s4' = Z_to_bv 64 (q + 1) /\ s10' = Z_to_bv 64 (SPL x + 360 + 3 * c + (q + 1))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134dc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m t c q T ws -> -> -> -> -> -> Hs3 Hc Hq Ht HT4 HTl HTB Hwl HWB HH.
  pose proof (bytes_at_bound _ _ _ _ HWB) as Hwb. rewrite Hwl in Hwb.
  pose proof (bytes_at_bound _ _ _ _ HTB) as Htb. rewrite HTl in Htb.
  set (b := nth (Z.to_nat (3 * c + q)) ws (Z_to_bv 8 0)).
  assert (HR : ov_read_bytes rsegs m (wa (SPL x + 360 + 3 * c + q)) 1 = Some [b]).
  { replace (SPL x + 360 + 3 * c + q) with (SPL x + 360 + (3 * c + q)) by lia.
    rewrite (bytes_at_read rsegs m _ ws (3 * c + q) 1 HWB) by lia.
    rewrite (firstn1_skipn_nth ws _ (Z_to_bv 8 0)) by lia. reflexivity. }
  pose proof (HH c q Hc Hq) as Hhq. unfold tb in Hhq at 1. fold b in Hhq.
  assert (Eeff : bv_unsigned b = 0 -> eff T t c q = dflt q).
  { intros Hb0. rewrite eff_cell by lia. rewrite <- Hhq, Hb0. reflexivity. }
  assert (q = 0 \/ q = 1 \/ q = 2) as [-> | [-> | ->]] by lia.
  all: zstep; brx; zstep; zstep; if_cases HC1; zify_cond HC1.
  all: first [ specialize (Eeff HC1) | clear Eeff; assert (Eeff : True) by exact I ].
  all: drive EFF DFL HTl HTB HT4 Eeff.
  all: fin_q.
Qed.

End Q.

Theorem seg_unset_turn_holds : reac_headamp_tx_effective_contract -> reac_headamp_default_contract -> seg_unset_turn.
Proof.
  intros EFF DFL. unfold seg_unset_turn. intros x t c ms H.
  apply evt_canon; [eqv_inv_tac|].
  destruct H as (((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & HPL & HST & HMI & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) &
                  Hsp & HSV & HS16 & Hsv12 & HS63) &
                 Hn & Hc & Hs0 & Hs25 & Hs9 & Hs18 & Hs23 & Hs24 & Hs27 & HSL & HCS & (HTb & HT16 & HTl & HT) &
                 (Hwl & Hstl & HWS & HSTA) & HHr & HI1).
  unfold slots in HSL. unfold cslot in HCS.
  pose proof HTb as HTb'. unfold blk in HTb'.
  assert (ESPL : SPL x = x_S x - 608) by reflexivity.
  assert (ELS : LLVM_STACK = 8800) by reflexivity.
  assert (HSlo : 8800 <= x_S x) by (destruct HST as (H0 & _); rewrite ELS in H0; lia).
  rewrite canon_rg by exact Hsvc.
  rewrite Hpc, HF, Hfc, Hrv, Hro, Hs0, Hs25, Hs9, Hs18, Hs23, Hs24, Hs27, Hsp.
  set (m0 := ms_mem ms) in *.
  destruct (CB_bytes _ _ _ _ HT) as (HTB & _ & _).
  destruct (CB_bytes _ _ _ _ HWS) as (HWB & _ & _).
  assert (HHw : forall c' q', 0 <= c' < 48 -> 0 <= q' < 3 ->
            tb (ws_end (x_pl x)) (3 * c' + q') = tb (T_end (x_pl x)) (144 + 3 * c' + q'))
    by (intros c' q' Hc' Hq'; exact (proj1 (HHr c' q' Hc' Hq'))).
  unfold w64, PC_UNSET.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (land255 c) by lia.
  rewrite ?Z.shiftl_mul_pow2 by lia. try (change (2 ^ 1) with 2).
  eapply evt_cut.
  { eapply (q_block x EFF DFL) with (t := t) (c := c) (q := 0) (T := T_end (x_pl x)) (ws := ws_end (x_pl x));
      first [ qprem | (apply lxor_big; Z.div_mod_to_equations; lia) ]. }
  intros ms1 (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & s41 & s61 & s101 &
              t31 & t41 & t51 & t61 & -> & Hq).
  destruct (Hq ltac:(lia)) as [-> ->].
  eapply evt_cut.
  { eapply (q_block x EFF DFL) with (t := t) (c := c) (q := 1) (T := T_end (x_pl x)) (ws := ws_end (x_pl x));
      first [ qprem | (apply lxor_big; Z.div_mod_to_equations; lia) ]. }
  intros ms2 (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & s42 & s62 & s102 &
              t32 & t42 & t52 & t62 & -> & Hq2).
  destruct (Hq2 ltac:(lia)) as [-> ->].
  eapply evt_cut.
  { eapply (q_block x EFF DFL) with (t := t) (c := c) (q := 2) (T := T_end (x_pl x)) (ws := ws_end (x_pl x));
      first [ qprem | (apply lxor_big; Z.div_mod_to_equations; lia) ]. }
  intros ms3 (ra3 & t03 & t13 & t23 & a03 & a13 & a23 & a33 & a43 & a53 & a63 & a73 & s43 & s63 & s103 &
              t33 & t43 & t53 & t63 & -> & _).
  change (if 2 <? 2 then 0x134dc else 0x1352c) with 79148.
  zstep. zstep. zstep.
  if_cases HC; zify_cond HC.
  all: apply evt_done; split; [split; [apply munch_refl | apply wmono_refl]|].
  all: first [ left; split; [lia|]; fin_at | right; split; [lia|]; fin_at ].
Qed.
