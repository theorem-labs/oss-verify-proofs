(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain): the inner walk L02_inner
   from 0x13984 to the join 0x139f0, with the walk from the
   join (L02_back_stmt, Prog/Seg/L02W_inv.v) as a premise.
   - 0x13984 `beqz a0` to the abort: not taken (t <> 0); s7 = t; `beqz s9`: n = length s = 0 skips memcpy, else
     memcpy(t, src, n) (0x1399c, memcpy_c.v);
   - 0x139a0 s9 = t + n, a0 = lb << 56, `sb zero, 0(s9)` (the NUL); `bltz a0` (bit 7 of lb): memset(longl, 'L', 120)
     (0x139e4, memset_c.v), s9 = longl; else `beqz s8` (lb = 0): s9 = 0; else snprintf(sp + 0x40, 40,
     "reac-pw.conf.d/%u-x.conf", lb) (0x139c8, snprintf_m_c.v), s9 = sp + 0x40;
   - at 0x139f0 L02_J with lp = s9 (Prog/Seg/L02W_front_mem.v gives its memory facts).
   Segment lemma of LLVMFuzzerTestOneInput's walk: the front part
   0x13984..0x139f0 of segment L02, plain. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require memcpy_c snprintf_m_c memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import L02M L02D L02W_inv L02W_lab
  L02W_front_mem.
Import ListNotations.
Open Scope Z_scope.

(** ** 0x139ac .. 0x139f0: the label *)
Lemma l02_lab : K_L02 ->
  forall (S c mm t nt src x5 x6 f nf lb : Z) (s : list Z) (rc : rconf) (mc : mconf) (ret : bool)
         (sp gp tp s0 s2 s3 s4 s5 s6 s10 s11 : word) (m0 : word -> option byte)
         (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m1 : word -> option byte),
  L02_J S c mm t nt src x5 x6 f nf lb s rc mc ret sp gp tp s0 s2 s3 s4 s5 s6 s10 s11 m0 ->
  l02_static S c mm t nt src s -> 0 <= lb < 256 -> sp = Z_to_bv 64 (S - 208) ->
  a0 = Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 lb)) 56) ->
  frm0 fc -> l02_mid S c mm t nt s rc mc m0 m1 ->
  evt rsegs (L02_post S c mm t nt src x5 x6 f nf lb s rc mc ret sp gp tp s0 s2 s6 s10 m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 t) (Z_to_bv 64 lb) s9
           s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x139ac) fc None m1 (seg_rom rsegs)).
Proof.
  intros HK S c mm t nt src x5 x6 f nf lb s rc mc ret sp gp tp s0 s2 s3 s4 s5 s6 s10 s11 m0
    ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 F fc m1 K HST Hlb Esp Ea0 FRM MID.
  destruct HK as (_ & HSN & HMS & _).
  destruct (st_S S c mm t nt src s HST) as (_ & HSlo & HShi).
  unfold L02_J in K.
  subst sp a0.
  (* 0x139ac bltz a0 *)
  step.
  rewrite (bltz_lb lb Hlb).
  destruct (Z.leb_spec0 128 lb) as [Hhi|Hlo]; cbv iota.
  - (* bit 7 set: memset(longl, 'L', 120), s9 = longl *)
    do 6 step.
    pose proof MID as (_ & _ & ENV & _ & _ & _ & ((jl & RL) & _)).
    pose proof ENV as (MI & _).
    eapply evt_cut; [eapply HMS with (junk := jl); [exact RL | exact MI] |].
    intros ms' PO. unfold memset_c.memset_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
      MU & WMo & MI2 & RW).
    rewrite ret_pc_even by (first [lia | reflexivity]).
    step.
    destruct (join_hi S c mm t nt src s rc mc m0 m1 m2 lb HST MID ltac:(lia) MU WMo MI2 RW)
      as (J1 & J2 & J3 & J4 & J5 & J6 & J7).
    eapply K; eassumption.
  - (* 0x139b0 beqz s8 *)
    step.
    destruct (Z.eq_dec lb 0) as [E0|E0].
    + (* lb = 0: s9 = 0 *)
      rewrite (weq0_true lb E0). cbv iota.
      step.
      subst lb.
      destruct (join_zero S c mm t nt s rc mc m0 m1 MID) as (J1 & J2 & J3 & J4 & J5 & J6 & J7).
      eapply K; eassumption.
    + (* 0 < lb < 128: snprintf(sp + 0x40, 40, fmt, lb), s9 = sp + 0x40 *)
      rewrite (weq0_false lb) by lia. cbv iota.
      pose proof MID as (_ & _ & ENV & _ & _ & _ & (_ & _ & _ & F28)).
      assert (HR : ov_read_bytes rsegs m1 (wa (S - 208 + 40)) 8 = Some (le8 (Z_to_bv 64 0x1093b))).
      { pose proof (bytes_at_read rsegs m1 (S - 208 + 0x28) (le8 (Z_to_bv 64 0x1093b)) 0 8 F28 ltac:(lia)
          ltac:(rewrite length_le8; lia)) as R.
        assert (E8 : firstn 8 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 0x1093b))) = le8 (Z_to_bv 64 0x1093b))
          by reflexivity.
        rewrite Z.add_0_r, E8 in R.
        exact R. }
      clear F28.
      do 6 step.
      clear HR.
      replace (Z_to_bv 64 (S - 208 + 64)) with (Z_to_bv 64 (S - 144)) by (f_equal; lia).
      pose proof MID as (_ & _ & _ & _ & _ & _ & (_ & _ & (jd & RD) & _)).
      eapply evt_cut; [eapply (snp_ok HSN); [exact HSlo | exact HShi | lia | exact ENV | exact FRM | exact RD] |].
      intros ms' PO. unfold printf_post in PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' &
        m2 & -> & MU & WMo & MI2 & TM2 & FRM2 & _ & ST2 & BD).
      rewrite ret_pc_even by (first [lia | reflexivity]).
      rewrite unsigned_lit in MU, ST2 by lia.
      step.
      destruct (join_mid S c mm t nt src s rc mc m0 m1 m2 lb HST MID ltac:(lia) MU WMo MI2 TM2 ST2 BD)
        as (J1 & J2 & J3 & J4 & J5 & J6 & J7).
      eapply K; eassumption.
Qed.

(** ** 0x139a0 .. 0x139ac: s9 = t + n, a0 = lb << 56, the NUL at t + n *)
Lemma at_139a0 : K_L02 ->
  forall (S c mm t nt src x5 x6 f nf lb n : Z) (s : list Z) (rc : rconf) (mc : mconf) (ret : bool)
         (sp gp tp s0 s2 s3 s4 s5 s6 s10 s11 : word) (m0 : word -> option byte)
         (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte),
  L02_J S c mm t nt src x5 x6 f nf lb s rc mc ret sp gp tp s0 s2 s3 s4 s5 s6 s10 s11 m0 ->
  L02_mem S c mm t nt src s rc mc m0 -> L02_model s lb rc mc -> sp = Z_to_bv 64 (S - 208) ->
  n = Z.of_nat (length s) -> frm0 fc ->
  munch [(t, t + n)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> bytes_at rsegs m t (zb s) ->
  wr_at rsegs m t nt ->
  evt rsegs (L02_post S c mm t nt src x5 x6 f nf lb s rc mc ret sp gp tp s0 s2 s6 s10 m0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 t) (Z_to_bv 64 lb)
           (Z_to_bv 64 n) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x139a0) fc None m (seg_rom rsegs)).
Proof.
  intros HK S c mm t nt src x5 x6 f nf lb n s rc mc ret sp gp tp s0 s2 s3 s4 s5 s6 s10 s11 m0
    ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m K HM HMOD Esp En FRM MU WMo MI BT WR.
  pose proof (l02_static_of S c mm t nt src s rc mc m0 lb HM HMOD) as HST.
  destruct (txt0 S c mm t nt src s rc mc m0 lb n HM HMOD En) as (Ht0 & Htb & Hnt & Hn & _).
  pose proof HMOD as (_ & _ & Hlb & _).
  assert (HS : store_ok rsegs m (wa (t + n)) 1 = true) by (apply (wr_at_store_ok rsegs m t nt n 1 WR); lia).
  destruct (txt_store m0 m t nt n s En Hnt ltac:(lia) ltac:(lia) MU WMo MI BT HS) as (MU1 & WM1 & MI1 & BT1).
  (* add s9, s7, s9; slli a0, s8, 0x38; sb zero, 0(s9) *)
  do 3 step.
  eapply (l02_lab HK); [exact K | exact HST | exact Hlb | exact Esp | reflexivity | exact FRM |].
  exact (l02_mid_of S c mm t nt src s rc mc m0 _ lb HM HMOD MU1 WM1 MI1 BT1).
Qed.

(** ** 0x13984 .. 0x139a0 and the theorem *)
Theorem l02_front : K_L02 -> L02_back_stmt -> L02_inner.
Proof.
  intros HK HB. unfold L02_inner.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    S c mm t nt src x5 x6 f nf lb s rc mc ret Esp Ea0 Es0 Es10 Es2 Es11 Hf Hnf Es4 Es9 Es3 Es5 Es6 Es8 FRM HMOD HM.
  pose proof (l02_static_of S c mm t nt src s rc mc m lb HM HMOD) as HST.
  pose proof (HB S c mm t nt src x5 x6 f nf lb s rc mc ret sp gp tp s0 s2 s3 s4 s5 s6 s10 s11 m HST HMOD
    Esp Es0 Es10 Es2 Es11 Hf Hnf Es4 Es3 Es5 Es6) as K.
  clear HB.
  pose proof HK as (HMC & _).
  subst a0 s9 s8 s3.
  remember (Z.of_nat (length s)) as n eqn:En.
  destruct (txt0 S c mm t nt src s rc mc m lb n HM HMOD En)
    as (Ht0 & Htb & Hnt & Hn & Hsrc & Hsrcb & Ast & MI & BS & (jt & RT) & WR).
  (* 0x13984 beqz a0 (t <> 0); mv s7, a0 *)
  step.
  rewrite (weq0_false t) by lia. cbv iota.
  step.
  (* 0x1398c beqz s9 *)
  step.
  destruct (Z.eq_dec n 0) as [E0|E0].
  - (* n = 0: no copy *)
    rewrite (weq0_true n E0). cbv iota.
    assert (BT : bytes_at rsegs m t (zb s)).
    { destruct s as [|x s']; [apply bytes_at_nil; lia | cbn [length] in En; exfalso; lia]. }
    eapply (at_139a0 HK); [exact K | exact HM | exact HMOD | exact Esp | exact En | exact FRM | apply munch_refl
                          | apply wmono_refl | exact MI | exact BT | exact WR].
  - (* memcpy(t, src, n) *)
    rewrite (weq0_false n) by lia. cbv iota.
    do 4 step.
    eapply evt_cut.
    { eapply (memcpy_ok HMC); [exact En | lia | lia | lia | exact BS | exact RT | lia | exact MI]. }
    intros ms' PO. unfold cpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
      MU & WMo & MI' & BT).
    rewrite ret_pc_even by (first [lia | reflexivity]).
    eapply (at_139a0 HK); [exact K | exact HM | exact HMOD | exact Esp | exact En | exact FRM | exact MU
                          | exact WMo | exact MI' | exact BT | exact (wr_at_transport rsegs m m' t nt WR WMo)].
Qed.
