(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxFrame FxCall FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_app2 B_rt_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_D1_closed.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_shl_limbs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_app2 OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_rt_m2s OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_memiszero OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_D1_closed.B_rpoison OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_shl_limbs.B_asan_memmove2_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_D1_closed.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn M4B_lm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4B_lm.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun KxTac KxRtB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition asan_memmove2_closed : asan_memmove2_stmt := B_D1_closed.B_asan_memmove2_closed.

Lemma stk_of_u8arr' : forall m A bs, u8arr BSEGS m A bs -> stk BSEGS m A (A + Z.of_nat (length bs)).
Proof.
  intros m A bs ((B1 & B2 & B) & (W1 & W2 & W)). split; [lia|]. split; [lia|].
  intros a Ha. split; [replace a with (A + (a - A))%Z by lia; apply W; lia|].
  pose proof (B (Z.to_nat (a - A)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
  replace (A + (a - A))%Z with a in X by lia. destruct (nth_error bs (Z.to_nat (a - A))) as [b|] eqn:Hb.
  - exists b. exact X.
  - apply nth_error_None in Hb. lia.
Qed.
Lemma rdbl_of_rg' : forall E m R A n, rg_ok BSEGS E m R -> rg_kind R <> RO -> bv_unsigned (lden E (rg_base R)) = A -> rsz E R = n ->
  rdbl BSEGS m A n.
Proof.
  intros E m R A n HR Hk Hb Hs. pose proof (rg_flat BSEGS E m R HR) as (F1 & F2). pose proof (u_lden_range E (rg_base R)) as U.
  split; [lia|]. split; [unfold two64 in *; lia|]. intros i Hi.
  pose proof (rd_of_rg BSEGS E m R i HR ltac:(lia) Hk) as X. rewrite Hb in X.
  destruct (mrd BSEGS m (wa (A + i))) as [b|]; [exists b; reflexivity | exfalso; exact (X eq_refl)].
Qed.
Lemma rdbl_app' : forall m a n1 n2, rdbl BSEGS m a n1 -> rdbl BSEGS m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 -> rdbl BSEGS m a (n1 + n2).
Proof.
  intros m a n1 n2 (A1 & A2 & A) (B1 & B2 & B) H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z.ltb_spec0 i n1); [apply A; lia|]. replace (a + i) with (a + n1 + (i - n1)) by ring. apply B; lia.
Qed.
Lemma shz_of_bytes' : forall m a n, bytes_at BSEGS m a (repeat (Z_to_bv 8 0) n) -> shz BSEGS m a (Z.of_nat n).
Proof. intros m a n X. split; [lia|]. rewrite Nat2Z.id. exact X. Qed.
Lemma bytes_at_zeros_sub' : forall m a n k j, bytes_at BSEGS m a (repeat (Z_to_bv 8 0) n) -> (k + j <= n)%nat ->
  bytes_at BSEGS m (a + Z.of_nat k) (repeat (Z_to_bv 8 0) j).
Proof.
  intros m a n k j X H. replace n with (k + (j + (n - k - j)))%nat in X by lia. rewrite !repeat_app in X.
  apply bytes_at_app in X as (_ & X). rewrite repeat_length in X. apply bytes_at_app in X as (X & _). exact X.
Qed.

(* [comment removed for export] *)
Definition RGS0 : list region :=
  [ RG SWB SWS RW TEmpty;
    RG MCD (lconst 496) RW TEmpty;
    RG XA (lconst 496) RW TEmpty;
    RG MCW (lconst 8) FxCore.RT TEmpty;
    track (RG (laddc MCW 8) (lconst 256) RW TEmpty) 4 (List.repeat (BK 0) 63);
    RG (laddc XS (-8)) (lconst 8) FxCore.RT TEmpty; RG XS (lconst 63) FxCore.RT (put_bytes TEmpty 0 (List.repeat (BK 0) 63)); RG (laddc XS 63) (lconst 8) FxCore.RT TEmpty;
    sb_uar_t ] ++ rt_rgs_t ++ relro_rgs.
Lemma RGS0_eq : MMA_RGS false = RGS0. Proof. reflexivity. Qed.
Lemma RGS1_eq : MMA_RGS true = RGS0. Proof. reflexivity. Qed.

Section MCA.
Variable E : valu.
Variable ms : machine_state.
Hypothesis Hd : sden BSEGS E MMA_P0 ms.

Local Abbreviation ra := (bv_unsigned (E 5%positive)).
Local Abbreviation sp := (bv_unsigned (E 4%positive)).
Local Abbreviation fsp := (bv_unsigned (E 10%positive)).
Local Abbreviation ctx := (bv_unsigned (E 15%positive)).
Local Abbreviation thr := (bv_unsigned (E 16%positive)).
Local Abbreviation blk := (bv_unsigned (E 17%positive)).
Local Abbreviation beg := (bv_unsigned (E 18%positive)).
Local Abbreviation tlsb := (bv_unsigned (E 19%positive)).
Local Abbreviation tlse := (bv_unsigned (E 20%positive)).
Local Abbreviation fbv := (bv_unsigned (E 21%positive)).
Local Abbreviation swb := (bv_unsigned (E 23%positive)).
Local Abbreviation sws := (bv_unsigned (E 24%positive)).
Local Abbreviation xq := (bv_unsigned (E 30%positive)).
Local Abbreviation dst := (bv_unsigned (E 33%positive)).
Local Abbreviation mcn := (bv_unsigned (E 34%positive)).
Local Abbreviation mcw := (bv_unsigned (E 35%positive)).

#[using="Type"] Lemma Bnd : forall x : positive, 0 <= bv_unsigned (E x) < two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. pose proof (bv_unsigned_in_range _ (E x)) as X. unfold bv_modulus in X. exact X. Qed.

Ltac open_facts :=
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _); cbn [s_facts MMA_P0] in HF;
  unfold MMA_F, x_facts, rt_facts, two_class, two_class4k, stack_facts in HF; cbn [app] in HF;
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [?F H] end;
  cbn [fact_ok] in *;
  repeat match goal with H : context [lden E ?l] |- _ => progress lnorm_s_in H end;
  rewrite ?u_Z_to_bv in *; unfold vz in *; unfold KHI, KTOP, IMG_END, SH_LO, SHB in *.

#[using="Type"] Lemma rt_app_of_wrapped : forall x n, 6537216 <= x -> x + n <= 2 ^ 47 -> 0 <= n ->
  0 <= (-17594333495296 + (1 * x + 0)) mod two64 <= 2 ^ 64 + 2147446784 - n - 17594333495296 -> rt_app x n /\ app2r x (x + n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x n H1 H2 H3 H4. unfold rt_app, app2r, KHI, KTOP. destruct (Z.le_gt_cases 17594333495296 x) as [Hh|Hl].
  - split; right; lia.
  - assert (Hm : (-17594333495296 + (1 * x + 0)) mod two64 = x - 17594333495296 + two64)
      by (symmetry; apply Z.mod_unique with (q := -1); unfold two64; lia).
    rewrite Hm in H4. unfold two64 in H4. split; left; lia.
Qed.
#[using="Type"] Lemma rt_app_of_wrapped4k : forall x n, 4096 <= x -> x + n <= 2 ^ 47 -> 0 <= n ->
  0 <= (-17594333495296 + (1 * x + 0)) mod two64 <= 2 ^ 64 + 2147446784 - n - 17594333495296 -> rt_app x n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x n H1 H2 H3 H4. unfold rt_app, KHI. destruct (Z.le_gt_cases 17594333495296 x) as [Hh|Hl].
  - right; lia.
  - left. assert (Hm : (-17594333495296 + (1 * x + 0)) mod two64 = x - 17594333495296 + two64)
      by (symmetry; apply Z.mod_unique with (q := -1); unfold two64; lia).
    rewrite Hm in H4. unfold two64 in H4. lia.
Qed.

#[using="ms Hd"] Lemma mca_facts :
  ra mod 2 = 0 /\ 0 <= mcn <= 62 /\ dst mod 8 = 0 /\ 8 * mcw = dst + 17179606944 /\
  4096 * fsp + 5279744 + 32 <= dst <= 4096 * fsp + 5279744 + 2 ^ 20 - 2016 /\
  4096 * fsp + 4231168 <= 8 * xq <= 4096 * fsp + 4231168 + 2 ^ 20 - 632 /\
  512 * fsp + 528896 <= xq <= 512 * fsp + 528896 + 2 ^ 17 - 79 /\
  512 * fsp + 2148110840 <= mcw <= 512 * fsp + 2148110840 + 2 ^ 17 - 256 /\
  mcw + 12 = 2147450880 + dst / 8 /\
  6537216 <= 4096 * fsp <= 2 ^ 47 - 11571200 /\
  (ctx + 160 <= 4096 * fsp \/ 4096 * fsp + 11571200 <= ctx) /\
  (thr + 80 <= 4096 * fsp \/ 4096 * fsp + 11571200 <= thr) /\
  (blk + 32 <= 4096 * fsp \/ 4096 * fsp + 11571200 <= blk) /\
  17594333495296 <= sp - 2224 /\ sp <= 2 ^ 47 /\ sp mod 16 = 0 /\
  2224 <= sp - swb <= 2 ^ 30 /\ 0 <= swb + sws - sp <= 2 ^ 30 /\
  0 <= sp - 2224 - 4096 * fsp - 11571200 <= 2 ^ 47 /\
  app2r (4096 * fsp) (4096 * fsp + 11571200) /\ rt_app ctx 160 /\ rt_app thr 80 /\ rt_app blk 32 /\
  6537216 <= ctx <= 2 ^ 47 - 160 /\ 4096 <= thr <= 2 ^ 47 - 80 /\ 4096 <= blk <= 2 ^ 47 - 32 /\
  1 <= beg <= 2 ^ 64 - 1 /\ 1 <= fbv <= 255.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts.
  pose proof (Bnd 4%positive) as B4. pose proof (Bnd 10%positive) as B10. pose proof (Bnd 15%positive) as B15.
  pose proof (Bnd 16%positive) as B16. pose proof (Bnd 17%positive) as B17. pose proof (Bnd 23%positive) as B23.
  pose proof (Bnd 24%positive) as B24. pose proof (Bnd 30%positive) as B30. pose proof (Bnd 33%positive) as B33.
  pose proof (Bnd 34%positive) as B34. pose proof (Bnd 35%positive) as B35.
  assert (X : 6537216 <= 4096 * fsp <= 2 ^ 47 - 11571200)
    by (clear -F7; change (6537216 / 4096) with 1596 in F7; change ((2 ^ 47 - 11571200) / 4096) with 34359735543 in F7; lia).
  assert (XQ : 512 * fsp + 528896 <= xq <= 512 * fsp + 528896 + 2 ^ 17 - 79)
    by (clear -F6 B30 X; unfold two64 in *; Z.div_mod_to_equations; lia).
  assert (XA : 4096 * fsp + 4231168 <= 8 * xq <= 4096 * fsp + 4231168 + 2 ^ 20 - 632) by (clear -XQ; lia).
  assert (DD : 4096 * fsp + 5279744 + 32 <= dst <= 4096 * fsp + 5279744 + 2 ^ 20 - 2016)
    by (clear -F3 B33 X; unfold two64 in *; Z.div_mod_to_equations; lia).
  assert (MW : 512 * fsp + 2148110840 <= mcw <= 512 * fsp + 2148110840 + 2 ^ 17 - 256)
    by (clear -F4 B35 X; unfold two64 in *; Z.div_mod_to_equations; lia).
  assert (MR : 8 * mcw = dst + 17179606944) by (clear -F2 DD MW X; unfold two64 in *; Z.div_mod_to_equations; lia).
  change (2 ^ 1) with 2 in F. change (2 ^ 3) with 8 in F1. change (2 ^ 4) with 16 in F24.
  assert (MD : mcw + 12 = 2147450880 + dst / 8) by (clear -MR F1; Z.div_mod_to_equations; lia).
  refine (conj F (conj F0 (conj F1 (conj MR (conj DD (conj XA (conj XQ (conj MW (conj MD (conj X (conj _ (conj _ (conj _ (conj _ (conj _ (conj F24 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj F9 (conj F11 (conj F13 (conj F15 F16))))))))))))))))))))))))))).
  - clear -F20 B10 B15 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F21 B10 B16 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F22 B10 B17 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F23 B4. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F23 B4. unfold two64 in *. Z.div_mod_to_equations. lia.
  - destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _). cbn [s_rgs MMA_P0] in HG. rewrite RGS0_eq in HG. unfold RGS0 in HG. cbn [app] in HG.
    apply Forall_cons_iff in HG as [G0 _]. destruct (rg_flat BSEGS E _ _ G0) as (Z1 & Z2). unfold rsz in Z1, Z2. cbn [rg_base rg_size] in Z1, Z2.
    unfold SWB, SWS in Z1, Z2. repeat rewrite lden_lvar in Z1. repeat rewrite lden_lvar in Z2.
    clear -F23 F25 F26 B4 B23 B24 Z1 Z2. unfold two64 in *. Z.div_mod_to_equations. lia.
  - destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & HG & _). cbn [s_rgs MMA_P0] in HG. rewrite RGS0_eq in HG. unfold RGS0 in HG. cbn [app] in HG.
    apply Forall_cons_iff in HG as [G0 _]. destruct (rg_flat BSEGS E _ _ G0) as (Z1 & Z2). unfold rsz in Z1, Z2. cbn [rg_base rg_size] in Z1, Z2.
    unfold SWB, SWS in Z1, Z2. repeat rewrite lden_lvar in Z1. repeat rewrite lden_lvar in Z2.
    clear -F23 F25 F26 B4 B23 B24 Z1 Z2. unfold two64 in *. Z.div_mod_to_equations. lia.
  - clear -F27 B4 B10 X. unfold two64 in *. Z.div_mod_to_equations. lia.
  - apply (proj2 (rt_app_of_wrapped (4096 * fsp) 11571200 ltac:(lia) ltac:(lia) ltac:(lia)
                     ltac:(replace (-17594333495296 + (1 * (4096 * fsp) + 0)) with (-17594333495296 + (4096 * fsp + 0)) by ring; exact F8))).
  - exact (proj1 (rt_app_of_wrapped ctx 160 ltac:(lia) ltac:(lia) ltac:(lia) F10)).
  - exact ((rt_app_of_wrapped4k thr 80 ltac:(lia) ltac:(lia) ltac:(lia) F12)).
  - exact ((rt_app_of_wrapped4k blk 32 ltac:(lia) ltac:(lia) ltac:(lia) F14)).
Qed.

Definition v0 : rt_vals := RTV (4096 * fsp) ctx thr tlsb tlse blk beg.

Ltac rget_norm_in H := repeat match type of H with context [rget ?T ?k] =>
  let v := eval vm_compute in (rget T k) in change (rget T k) with v in H end.

Ltac open_mca :=
  destruct (sden_0 _ _ _ _ Hd) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm);
  cbn [s_pc s_regs s_rgs s_facts s_resv MMA_P0] in Hpc, Hresv, HR, HG, HD, HF; rewrite RGS0_eq in HG, HD;
  pose proof mca_facts as FCT;
  unfold RGS0, rt_rgs_t, relro_rgs in HG; cbn [app] in HG;
  apply Forall_cons_iff in HG as [G0 HG]; apply Forall_cons_iff in HG as [G1 HG]; apply Forall_cons_iff in HG as [G2 HG];
  apply Forall_cons_iff in HG as [G3 HG]; apply Forall_cons_iff in HG as [G4 HG]; apply Forall_cons_iff in HG as [G5 HG];
  apply Forall_cons_iff in HG as [G6 HG]; apply Forall_cons_iff in HG as [G7 HG]; apply Forall_cons_iff in HG as [G8 HG];
  apply Forall_cons_iff in HG as [G9 HG]; apply Forall_cons_iff in HG as [G10 HG]; apply Forall_cons_iff in HG as [G11 HG];
  apply Forall_cons_iff in HG as [G12 HG]; apply Forall_cons_iff in HG as [G13 HG]; apply Forall_cons_iff in HG as [G14 HG];
  apply Forall_cons_iff in HG as [G15 HG]; apply Forall_cons_iff in HG as [G16 HG]; apply Forall_cons_iff in HG as [G17 HG];
  apply Forall_cons_iff in HG as [G18 HG]; apply Forall_cons_iff in HG as [G19 HG]; apply Forall_cons_iff in HG as [G20 HG];
  apply Forall_cons_iff in HG as [G21 HG].

Ltac ubase := lnorm; rewrite u_Z_to_bv; unfold vz; rewrite ?Z.add_0_l, ?Z.add_0_r, ?Z.mul_1_l.

#[using="ms Hd"] Lemma mca_win : 2224 <= sp - swb <= 2 ^ 30 /\ 0 <= swb + sws - sp <= 2 ^ 30.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof mca_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W1 & W2 & _). exact (conj W1 W2).
Qed.

#[using="ms Hd"] Lemma mca_vals : bv_unsigned (lden E XA) = 8 * xq /\ bv_unsigned (lden E (laddc XS (-8))) = 2147450880 + xq - 8 /\
  bv_unsigned (lden E XS) = 2147450880 + xq /\ bv_unsigned (lden E (laddc XS 63)) = 2147450880 + xq + 63 /\
  bv_unsigned (lden E MCD) = dst /\ bv_unsigned (lden E MCW) = mcw /\ bv_unsigned (lden E (laddc MCW 8)) = mcw + 8.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof mca_facts as (_ & _ & _ & _ & _ & _ & Hq & Hw & _ & Hf & _). unfold XA, XS, XQ, SHB, MCD, MCW.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); try (apply lden_lvar); try (rewrite lden_lvar; reflexivity);
    ubase; rewrite Z.mod_small; try ring; clear -Hq Hw Hf; unfold two64 in *; lia.
Qed.

#[using="Hd"] Lemma mca_regs : getr (ms_regs ms) 4 = Z_to_bv 64 6395968 /\ getr (ms_regs ms) 2 = E 4%positive /\ getr (ms_regs ms) 1 = E 5%positive /\
  getr (ms_regs ms) 10 = E 33%positive /\ bv_unsigned (getr (ms_regs ms) 11) = 8 * xq /\ bv_unsigned (getr (ms_regs ms) 12) = 8 * mcn.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_mca. destruct FCT as (_ & Hn & _ & _ & _ & _ & Hq & _ & _ & Hf & _).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - pose proof (HR 4%bv) as X. rget_norm_in X. rewrite X. reflexivity.
  - pose proof (HR 2%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar.
  - pose proof (HR 1%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar.
  - pose proof (HR 10%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar.
  - pose proof (HR 11%bv) as X. rget_norm_in X. rewrite X. exact (proj1 mca_vals).
  - pose proof (HR 12%bv) as X. rget_norm_in X. rewrite X. unfold MCN. ubase. rewrite Z.mod_small; [ring|]. clear -Hn; unfold two64; lia.
Qed.

(* [comment removed for export] *)
Ltac const_cells G o :=
  let X := fresh "X" in
  pose proof (track_bytes_at BSEGS E (ms_mem ms) _ o _ G ltac:(clear; lia) ltac:(cbn; clear; lia)) as X;
  cbn [rg_base RGz track] in X; change (bv_unsigned (lden E (lconst ?z))) with (z mod two64) in X;
  rewrite Z.mod_small in X by (unfold two64; clear; lia);
  apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].

#[using="Hd"] Lemma mca_RT : RT (ms_mem ms) v0.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_mca. unfold RT. cbn [rt_FS rt_ctx rt_thr rt_tlsb rt_tlse rt_blk rt_beg v0].
  destruct FCT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fapp & Capp & Tapp & Bapp & Hc & Ht & Hb & Hg & Hfb).
  unfold KHI, KTOP in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))).
  - unfold sb_uar_t in G8. const_cells G8 0.
  - pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 0 [BK 1] G9 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(vm_compute; reflexivity)) as Y.
    cbn [rg_base] in Y. change (bv_unsigned (lden E (lconst 941792))) with 941792 in Y.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ Y); [vm_compute; reflexivity | cbn; tauto].
  - pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 4 (bkn 4 0) G9 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(vm_compute; reflexivity)) as Y.
    cbn [rg_base] in Y. change (bv_unsigned (lden E (lconst 941792))) with 941792 in Y.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ Y); [vm_compute; reflexivity | cbn; tauto].
  - const_cells G10 0.
  - const_cells G11 0.
  - exists (Z_to_bv 8 fbv). split.
    + pose proof (track_bytes_at BSEGS E (ms_mem ms) _ 0 _ G13 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 1540657))) with 1540657 in X. rewrite Z.add_0_r in X.
      split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. cbn [List.map bden] in X. lnorm_in X. rewrite Z.shiftr_0_r in X. exact X.
    + rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by (clear -Hfb; lia). clear -Hfb; lia.
  - const_cells G12 0.
  - const_cells G14 0.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 0 (bk8 6396000) G15 ltac:(clear; lia) ltac:(cbn; clear; lia)
                    ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X. rewrite Z.add_0_r in X.
      apply (bytes_at_ext BSEGS _ _ _ _ X). apply bytes_eqb_eq. vm_compute. reflexivity.
    + pose proof (cont_le8 BSEGS E (ms_mem ms) _ 8 FS G15 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
      lnorm_in X. rewrite Z.add_0_l, Z.add_0_r in X. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 16 BLK G15 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
    lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - pose proof (cont_bytes_at BSEGS E (ms_mem ms) _ 48 (bk8 6398016) G15 ltac:(clear; lia) ltac:(cbn; clear; lia)
                  ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6395960))) with 6395960 in X.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ X); [vm_compute; reflexivity | cbn; tauto].
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 CTX G16 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. change (bv_unsigned (lden E (lconst 6532072))) with 6532072 in X.
    lnorm_in X. rewrite ?Z.add_0_r in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 THR G17 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. rewrite (u_ctx152 E ltac:(clear -Hc; lia)), Z.add_0_r in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 TLSB G18 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. rewrite (u_thr48 E ltac:(clear -Ht; lia)), Z.add_0_r in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
    + pose proof (cont_le8 BSEGS E (ms_mem ms) _ 8 TLSE G18 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
      cbn [rg_base RGz track] in X. rewrite (u_thr48 E ltac:(clear -Ht; lia)) in X. lnorm_in X. rewrite !Z_to_bv_bv_unsigned, length_le8.
      replace (thr + 48 + Z.of_nat 8) with (thr + 48 + 8) by lia. exact X.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    pose proof (cont_le8 BSEGS E (ms_mem ms) _ 0 BEG G19 ltac:(clear; lia) ltac:(vm_compute; reflexivity)) as X.
    cbn [rg_base RGz track] in X. rewrite (u_blk24 E ltac:(clear -Hb; lia)), Z.add_0_r in X. lnorm_in X. rewrite Z_to_bv_bv_unsigned. exact X.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Fapp (conj _ (conj _ (conj Capp (conj _ (conj Tapp (conj _ (conj Bapp _))))))))))))).
    all: clear -Hf Hc Ht Hb Hg; unfold two64 in *; lia.
Qed.

#[using="Hd"] Lemma mca_stk : stk BSEGS (ms_mem ms) (sp - 2224) sp.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_mca. pose proof mca_win as (W1 & W2).
  assert (S0 : stk BSEGS (ms_mem ms) swb (swb + sws)).
  { apply (stk_of_rg BSEGS E _ _ _ _ G0 ltac:(left; reflexivity)); cbn [rg_base]; [lnorm; reflexivity|].
    unfold rsz. cbn [rg_size]. lnorm. ring. }
  destruct (stk_split BSEGS _ _ (sp - 2224) _ S0 ltac:(clear -W1 W2; lia)) as (_ & S1).
  destruct (stk_split BSEGS _ _ sp _ S1 ltac:(clear -W1 W2; lia)) as (S2 & _). exact S2.
Qed.

#[using="E Hd"] Lemma mca_pr1 : pristine (ms_mem ms) 892928 917504.
Proof. LiaFast.lf_pins (fun (E Hd : LiaFast.U) => LiaFast.u0). open_mca. exact (pristine_of_rg_ro BSEGS E _ _ 892928 24576 G20 eq_refl eq_refl eq_refl). Qed.
#[using="E Hd"] Lemma mca_pr2 : pristine (ms_mem ms) 918096 918488.
Proof. LiaFast.lf_pins (fun (E Hd : LiaFast.U) => LiaFast.u0). open_mca. exact (pristine_of_rg_ro BSEGS E _ _ 918096 392 G21 eq_refl eq_refl eq_refl). Qed.

#[using="ms Hd"] Lemma mca_rtd1 : rt_disj v0 (sp - 2224) sp.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _). cbn [s_facts MMA_P0] in HF.
  assert (HO : Forall (fact_ok E) (rt_out 2224)).
  { rewrite Forall_forall in HF |- *. intros f Hf. apply HF. unfold MMA_F. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hf. }
  destruct (rt_out_ok E 2224 ltac:(lia) HO) as (O1 & O2 & O3).
  unfold rt_disj. cbn [rt_ctx rt_thr rt_blk v0]. clear -O1 O2 O3. repeat split; lia.
Qed.

#[using="ms Hd"] Lemma mca_rtd2 : rt_disj v0 dst (dst + 8 * mcn).
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof mca_facts as (_ & Hn & _ & _ & Hdd & _ & _ & _ & _ & Hf & C1 & C2 & C3 & _).
  unfold rt_disj. cbn [rt_ctx rt_thr rt_blk v0]. clear -C1 C2 C3 Hn Hdd. repeat split; lia.
Qed.

(* [comment removed for export] *)
#[using="Hd"] Lemma mca_src : exists bs : list byte, bytes_at BSEGS (ms_mem ms) (8 * xq) bs /\ Z.of_nat (length bs) = 8 * mcn.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_mca. pose proof mca_vals as (V1 & _). destruct FCT as (_ & Hn & _ & _ & _ & Ha & _ & _ & _ & Hf & _).
  destruct (bytes_exist BSEGS (ms_mem ms) (8 * xq) (Z.to_nat (8 * mcn)) ltac:(clear -Ha Hf; lia) ltac:(clear -Ha Hf Hn; rewrite Z2Nat.id by lia; lia))
    as (bs & J & Lj).
  { intros i Hi. rewrite <- rd1_mrd.
    pose proof (rd_of_rg BSEGS E _ _ (Z.of_nat i) G2
                  ltac:(unfold rsz; cbn [rg_size]; change (bv_unsigned (lden E (lconst 496))) with 496; clear -Hi Hn; lia)
                  ltac:(discriminate)) as X.
    cbn [rg_base] in X. rewrite V1 in X. exact X. }
  exists bs. split; [exact J|]. rewrite Lj, Z2Nat.id by lia. reflexivity.
Qed.

#[using="Hd"] Lemma mca_old : exists old : list byte, u8arr BSEGS (ms_mem ms) dst old /\ Z.of_nat (length old) = 8 * mcn.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_mca. pose proof mca_vals as (_ & _ & _ & _ & V5 & _). destruct FCT as (_ & Hn & _ & _ & Hdd & _ & _ & _ & _ & Hf & _).
  destruct (bytes_exist BSEGS (ms_mem ms) dst (Z.to_nat (8 * mcn)) ltac:(clear -Hdd Hf; lia) ltac:(clear -Hdd Hf Hn; rewrite Z2Nat.id by lia; lia))
    as (old & J & Lj).
  { intros i Hi. rewrite <- rd1_mrd.
    pose proof (rd_of_rg BSEGS E _ _ (Z.of_nat i) G1
                  ltac:(unfold rsz; cbn [rg_size]; change (bv_unsigned (lden E (lconst 496))) with 496; clear -Hi Hn; lia)
                  ltac:(discriminate)) as X.
    cbn [rg_base] in X. rewrite V5 in X. exact X. }
  exists old. split; [|rewrite Lj, Z2Nat.id by lia; reflexivity].
  pose proof (wr_at_of_rg BSEGS E _ _ _ _ G1 ltac:(left; reflexivity) ltac:(cbn [rg_base]; exact V5)
                ltac:(unfold rsz; cbn [rg_size]; reflexivity)) as (W1 & W2 & W).
  change (bv_unsigned (lden E (lconst 496))) with 496 in W2, W.
  split; [exact J|]. split; [lia|]. split; [rewrite Lj, Z2Nat.id by lia; clear -Hdd Hf Hn; unfold two64 in *; lia|].
  intros i Hi. rewrite Lj, Z2Nat.id in Hi by lia. apply W. clear -Hi Hn; lia.
Qed.

(* [comment removed for export] *)
#[using="Hd"] Lemma mca_shz_dst : shz BSEGS (ms_mem ms) (2147450880 + dst / 8) ((dst + 8 * mcn - 1) / 8 - dst / 8 + 1).
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_mca. pose proof mca_vals as (_ & _ & _ & _ & _ & _ & V7). destruct FCT as (_ & Hn & H8 & _ & Hdd & _ & _ & Hw & MD & Hf & _).
  pose proof (track_bytes_at BSEGS E (ms_mem ms) _ 4 _ G4 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X.
  cbn [rg_base track] in X. rewrite V7 in X. cbn [List.map bden] in X.
  assert (Ez : List.map (bden E) (List.repeat (BK 0) 63) = repeat (Z_to_bv 8 0) 63) by reflexivity.
  rewrite Ez in X.
  assert (En : (dst + 8 * mcn - 1) / 8 - dst / 8 + 1 = mcn) by (clear -H8; Z.div_mod_to_equations; lia).
  rewrite En.
  pose proof (bytes_at_zeros_sub' (ms_mem ms) _ 63 0 (Z.to_nat mcn) X ltac:(clear -Hn; lia)) as Y.
  replace (mcw + 8 + 4 + Z.of_nat 0) with (2147450880 + dst / 8) in Y by (clear -MD; lia).
  pose proof (shz_of_bytes' (ms_mem ms) _ _ Y) as Z. rewrite Z2Nat.id in Z by lia. exact Z.
Qed.

(* [comment removed for export] *)
#[using="Hd"] Lemma mca_shz_src : shz BSEGS (ms_mem ms) (2147450880 + 8 * xq / 8) ((8 * xq + 8 * mcn - 1) / 8 - 8 * xq / 8 + 1).
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_mca. pose proof mca_vals as (_ & _ & V3 & _). destruct FCT as (_ & Hn & _ & _ & _ & _ & _ & _ & _ & Hf & _).
  pose proof (zeros_bytes_of_rt BSEGS E _ _ _ 63 G6 ltac:(vm_compute; reflexivity) ltac:(lia) V3) as X.
  assert (E8 : 8 * xq / 8 = xq) by (clear; Z.div_mod_to_equations; lia).
  assert (En : (8 * xq + 8 * mcn - 1) / 8 - 8 * xq / 8 + 1 = mcn) by (clear; Z.div_mod_to_equations; lia).
  rewrite En, E8.
  pose proof (bytes_at_zeros_sub' (ms_mem ms) _ 63 0 (Z.to_nat mcn) X ltac:(clear -Hn; lia)) as Y.
  rewrite Z.add_0_r in Y.
  pose proof (shz_of_bytes' (ms_mem ms) _ _ Y) as Z. rewrite Z2Nat.id in Z by lia. exact Z.
Qed.

#[using="Hd"] Lemma mca_rdbl_dst : rdbl BSEGS (ms_mem ms) mcw 264.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_mca. pose proof mca_vals as (_ & _ & _ & _ & _ & V6 & V7).
  pose proof (rdbl_of_rg' E (ms_mem ms) _ _ 8 G3 ltac:(discriminate) V6 ltac:(reflexivity)) as A1.
  pose proof (rdbl_of_rg' E (ms_mem ms) _ _ 256 G4 ltac:(discriminate) ltac:(cbn [rg_base track]; exact V7) ltac:(reflexivity)) as A2.
  exact (rdbl_app' (ms_mem ms) _ _ _ A1 A2 ltac:(lia) ltac:(lia)).
Qed.

#[using="Hd"] Lemma mca_rdbl_src : rdbl BSEGS (ms_mem ms) (2147450880 + xq - 8) 79.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_mca. pose proof mca_vals as (_ & V2 & V3 & V4 & _).
  pose proof (rdbl_of_rg' E (ms_mem ms) _ _ 8 G5 ltac:(discriminate) V2 ltac:(reflexivity)) as A1.
  pose proof (rdbl_of_rg' E (ms_mem ms) _ _ 63 G6 ltac:(discriminate) V3 ltac:(reflexivity)) as A2.
  pose proof (rdbl_of_rg' E (ms_mem ms) _ _ 8 G7 ltac:(discriminate) V4 ltac:(reflexivity)) as A3.
  pose proof (rdbl_app' (ms_mem ms) _ _ _ A1 ltac:(replace (2147450880 + xq - 8 + 8) with (2147450880 + xq) by ring; exact A2) ltac:(lia) ltac:(lia)) as A12.
  exact (rdbl_app' (ms_mem ms) _ _ _ A12 ltac:(replace (2147450880 + xq - 8 + (8 + 63)) with (2147450880 + xq + 63) by ring; exact A3) ltac:(lia) ltac:(lia)).
Qed.

Ltac rget_norm := repeat match goal with |- context [rget ?T ?k] =>
  let v := eval vm_compute in (rget T k) in change (rget T k) with v end.

Ltac getr_mkR_norm := rewrite getr_mkR;
  match goal with |- context [Z.to_nat (bv_unsigned ?r)] =>
    let v := eval vm_compute in (Z.to_nat (bv_unsigned r)) in change (Z.to_nat (bv_unsigned r)) with v end; cbn beta iota.

Definition Eq (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : valu :=
  upds E [(205%positive, t0); (206%positive, t1); (207%positive, t2); (211%positive, a1); (212%positive, a2); (213%positive, a3);
          (214%positive, a4); (215%positive, a5); (216%positive, a6); (217%positive, a7); (228%positive, t3); (229%positive, t4);
          (230%positive, t5); (231%positive, t6)].

#[using="Type"] Lemma Eq_agree : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6, agree 200 E (Eq t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Proof. LiaFast.lf_pins LiaFast.u0. intros. apply upds_agree. repeat constructor; cbn [fst]; lia. Qed.

#[using="ms Hd"] Lemma mca_HW : forall x,
  (forall j Rj, In j [0%nat; 1%nat] -> nth_error RGS0 j = Some Rj ->
     ~ (bv_unsigned (lden E (rg_base Rj)) <= x < bv_unsigned (lden E (rg_base Rj)) + rsz E Rj)) ->
  Frame.outside [(sp - 2224, sp); (dst, dst + 8 * mcn)] x.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  intros x H. pose proof mca_win as (W1 & W2). pose proof mca_vals as (_ & _ & _ & _ & V5 & _).
  pose proof mca_facts as (_ & Hn & _).
  pose proof (H 0%nat _ ltac:(cbn; tauto) eq_refl) as N0. pose proof (H 1%nat _ ltac:(cbn; tauto) eq_refl) as N1. clear H.
  unfold rsz in N0, N1. cbn [rg_base rg_size track RGz] in N0, N1.
  rewrite V5 in N1. lnorm_in N0. change (bv_unsigned (lden E (lconst 496))) with 496 in N1.
  cbn [Frame.outside]. clear -N0 N1 W1 W2 Hn. repeat split; lia.
Qed.

#[using="Hd"] Lemma mca_run : exists ms' E', isteps BSEGS ms ms' /\
  sden BSEGS E' (with_pc MMA_Q (bv_unsigned (lden E (rget (s_regs MMA_P0) ra_key)))) ms' /\
  agree (s_next MMA_P0) E E' /\ (forall x, fr_pt E (s_rgs MMA_P0) x -> ms_mem ms' x = ms_mem ms x) /\ fpeq ms ms'.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  destruct (sden_0 _ _ _ _ Hd) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm).
  cbn [s_pc s_regs s_rgs s_facts s_resv MMA_P0] in Hpc, Hresv, HR, HG, HD, HF. rewrite RGS0_eq in HG, HD. unfold rsv_ok in Hresv.
  pose proof mca_facts as FCT. pose proof mca_win as (W1 & W2). pose proof (Bnd 4%positive) as Bsp.
  destruct FCT as (Fra & Fn & F8 & MR & Fdd & Fa & Fq & Fw & MD & Ffsp & _ & _ & _ & Fsp & FspK & Fsp16 & _ & _ & C18 & Fapp & _). unfold KHI, KTOP in Ffsp.
  pose proof mca_regs as (Rtp & Rsp & Rra & Ra0 & Ra1 & Ra2).
  pose proof asan_memmove2_closed as SM. unfold asan_memmove2_stmt in SM.
  destruct mca_src as (bs & SRC & Lbs). destruct mca_old as (old & OLD & Lold).
  specialize (SM (getr (ms_regs ms) 1) (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4) (getr (ms_regs ms) 5)
                 (getr (ms_regs ms) 6) (getr (ms_regs ms) 7) (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 10)
                 (getr (ms_regs ms) 11) (getr (ms_regs ms) 12) (getr (ms_regs ms) 13) (getr (ms_regs ms) 14) (getr (ms_regs ms) 15)
                 (getr (ms_regs ms) 16) (getr (ms_regs ms) 17) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19) (getr (ms_regs ms) 20)
                 (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (getr (ms_regs ms) 24) (getr (ms_regs ms) 25)
                 (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (getr (ms_regs ms) 28) (getr (ms_regs ms) 29) (getr (ms_regs ms) 30)
                 (getr (ms_regs ms) 31) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) v0 bs old mcw 264 (2147450880 + xq - 8) 79).
  assert (Husp : bv_unsigned (getr (ms_regs ms) 2) = sp) by (rewrite Rsp; reflexivity).
  assert (Hura : bv_unsigned (getr (ms_regs ms) 1) = ra) by (rewrite Rra; reflexivity).
  assert (Hua0 : bv_unsigned (getr (ms_regs ms) 10) = dst) by (rewrite Ra0; reflexivity).
  rewrite Husp, Hura, Hua0, Ra1, Ra2 in SM.
  assert (HK : evt BSEGS (asan_memmove_post (getr (ms_regs ms) 1) (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4)
                 (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 10) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19)
                 (getr (ms_regs ms) 20) (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (getr (ms_regs ms) 24)
                 (getr (ms_regs ms) 25) (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (ms_fregs ms) (ms_fcsr ms) (8 * mcn) bs
                 (ms_mem ms)) (kms BSEGS ms)).
  { unfold kms. rewrite Hpc, Hresv. apply SM.
    - exact SRC.
    - exact OLD.
    - apply Nat2Z.inj. rewrite Lold, Lbs. reflexivity.
    - exact Lbs.
    - clear -F8. exact F8.
    - clear. Z.div_mod_to_equations. lia.
    - clear. Z.div_mod_to_equations. lia.
    - eapply app2r_sub; [exact Fapp | clear -Fdd; lia | clear -Fdd Fn; lia].
    - clear -Fdd Ffsp Fn. lia.
    - eapply app2r_sub; [exact Fapp | clear -Fa; lia | clear -Fa Fn; lia].
    - clear -Fa Ffsp Fn. lia.
    - clear -Fn. lia.
    - pose proof mca_shz_dst as X. replace ((dst + 8 * mcn - 1) / 8 - dst / 8 + 1) with (8 * mcn / 8) in X
        by (clear -F8 Fn; Z.div_mod_to_equations; lia). exact X.
    - pose proof mca_shz_src as X. replace ((8 * xq + 8 * mcn - 1) / 8 - 8 * xq / 8 + 1) with (8 * mcn / 8) in X
        by (clear -F8 Fn; Z.div_mod_to_equations; lia). exact X.
    - exact mca_rdbl_dst.
    - clear -MD. lia.
    - clear -MD F8 Fn. Z.div_mod_to_equations. lia.
    - exact mca_rdbl_src.
    - clear. Z.div_mod_to_equations. lia.
    - clear -Fn. Z.div_mod_to_equations. lia.
    - exact mca_stk.
    - clear -Fsp. lia.
    - exact Fsp.
    - exact FspK.
    - exact Fsp16.
    - right. clear -C18 Fdd Fn. lia.
    - right. clear -C18 Fa Fn. lia.
    - exact mca_pr1.
    - exact mca_pr2.
    - exact mca_RT.
    - exact mca_rtd1.
    - exact mca_rtd2.
    - exact Fra. }
  clear SM.
  destruct (kit_run BSEGS _ ms Hsvc HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  unfold asan_memmove_post in Hpost.
  destruct Hpost as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms2 & MU & WM & ARR & ST').
  subst ms2. unfold asan_memmove_W in MU. rewrite Husp, Hua0 in MU. rewrite Husp in ST'. rewrite Hua0 in ARR.
  assert (Hmem : ms_mem ms1 = m') by (destruct Heq as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  exists ms1, (Eq t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  split; [exact Hst|]. split; [|split; [|split]].
  - eapply (sden_of_kit BSEGS _ _ ms1); [ | | exact Heq | | exact Hfrm | | | | ].
    + rewrite state_wf_with_pc. exact (proj1 (proj2 MM_wf)).
    + reflexivity.
    + cbn [s_pc with_pc s_regs MMA_P0]. rget_norm. lnorm. rewrite Z_to_bv_bv_unsigned. rewrite Rra. apply ret_pc_even_w.
      exact Fra.
    + (* [comment removed for export] *)
      apply regs_ok_of_cases. intros n Hn. cbn [s_regs with_pc MMA_Q].
      do 32 (destruct n as [|n];
               [ getr_mkR_norm; rget_norm;
                 first [ reflexivity
                       | (rewrite (HR _); rget_norm; lnorm; reflexivity)
                       | (lnorm; reflexivity) ]
               |]).
      lia.
    + (* [comment removed for export] *)
      assert (Hwr : forallb (rwf 200) (s_rgs MMA_Q) = true) by (vm_compute; reflexivity).
      rewrite Forall_forall. intros R HRin. apply (rg_ok_agree BSEGS 200 E _ _ R); [rewrite forallb_forall in Hwr; exact (Hwr R HRin) | apply Eq_agree|].
      revert R HRin. rewrite <- Forall_forall. cbn [s_rgs with_pc MMA_Q]. rewrite RGS1_eq.
      pose proof HG as HG'. unfold RGS0, rt_rgs_t, relro_rgs in HG'. cbn [app] in HG'.
      assert (UW : forall i R, nth_error RGS0 i = Some R -> ~ In i [0%nat; 1%nat] -> rg_ok BSEGS E (ms_mem ms) R -> rg_ok BSEGS E m' R).
      { intros i R Hi Hni HR0. exact (rg_ok_unwritten BSEGS E (ms_mem ms) m' RGS0 _ _ i R HD Hi Hni MU mca_HW HR0). }
      apply Forall_cons_iff in HG' as [G0 HG']. apply Forall_cons_iff in HG' as [G1 HG']. apply Forall_cons_iff in HG' as [G2 HG'].
      apply Forall_cons_iff in HG' as [G3 HG']. apply Forall_cons_iff in HG' as [G4 HG']. apply Forall_cons_iff in HG' as [G5 HG'].
      apply Forall_cons_iff in HG' as [G6 HG']. apply Forall_cons_iff in HG' as [G7 HG']. apply Forall_cons_iff in HG' as [G8 HG'].
      apply Forall_cons_iff in HG' as [G9 HG']. apply Forall_cons_iff in HG' as [G10 HG']. apply Forall_cons_iff in HG' as [G11 HG'].
      apply Forall_cons_iff in HG' as [G12 HG']. apply Forall_cons_iff in HG' as [G13 HG']. apply Forall_cons_iff in HG' as [G14 HG'].
      apply Forall_cons_iff in HG' as [G15 HG']. apply Forall_cons_iff in HG' as [G16 HG']. apply Forall_cons_iff in HG' as [G17 HG'].
      apply Forall_cons_iff in HG' as [G18 HG']. apply Forall_cons_iff in HG' as [G19 HG']. apply Forall_cons_iff in HG' as [G20 HG'].
      apply Forall_cons_iff in HG' as [G21 HG']. clear HG'.
      pose proof mca_vals as (_ & _ & _ & _ & V5 & _).
      unfold rt_rgs_t, relro_rgs. cbn [app].
      pose proof (rgs_disj_nth E _ 0 1 _ _ HD ltac:(discriminate) eq_refl eq_refl) as D1.
      unfold rg_disj, rsz in D1. cbn [rg_base rg_size track RGz] in D1. rewrite V5 in D1. lnorm_in D1.
      change (bv_unsigned (Z_to_bv 64 (496 + 0))) with 496 in D1.
      pose proof (stk_of_u8arr' _ _ _ ARR) as STA. rewrite Lbs in STA.
      constructor.
      { (* [comment removed for export] *)
        apply (rw_mix BSEGS E (ms_mem ms) m' _ _ (sp - 2224) sp G0 eq_refl eq_refl MU ST').
        intros k Hk. unfold rsz in Hk. cbn [rg_base rg_size] in Hk |- *. lnorm_in Hk. lnorm.
        cbn [Frame.outside]. clear -Hk W1 W2 D1 Fn. lia. }
      constructor.
      { (* [comment removed for export] *)
        apply (rw_mix BSEGS E (ms_mem ms) m' _ _ dst (dst + 8 * mcn) G1 eq_refl eq_refl MU STA).
        intros k Hk. unfold rsz in Hk. cbn [rg_base rg_size] in Hk |- *. change (bv_unsigned (lden E (lconst 496))) with 496 in Hk. rewrite V5.
        cbn [Frame.outside]. clear -Hk W1 W2 D1 Fn. lia. }
      constructor; [exact (UW 2%nat _ eq_refl ltac:(cbn; intuition discriminate) G2)|].
      constructor; [exact (UW 3%nat _ eq_refl ltac:(cbn; intuition discriminate) G3)|].
      constructor; [exact (UW 4%nat _ eq_refl ltac:(cbn; intuition discriminate) G4)|].
      constructor; [exact (UW 5%nat _ eq_refl ltac:(cbn; intuition discriminate) G5)|].
      constructor; [exact (UW 6%nat _ eq_refl ltac:(cbn; intuition discriminate) G6)|].
      constructor; [exact (UW 7%nat _ eq_refl ltac:(cbn; intuition discriminate) G7)|].
      constructor; [exact (UW 8%nat _ eq_refl ltac:(cbn; intuition discriminate) G8)|].
      constructor; [exact (UW 9%nat _ eq_refl ltac:(cbn; intuition discriminate) G9)|].
      constructor; [exact (UW 10%nat _ eq_refl ltac:(cbn; intuition discriminate) G10)|].
      constructor; [exact (UW 11%nat _ eq_refl ltac:(cbn; intuition discriminate) G11)|].
      constructor; [exact (UW 12%nat _ eq_refl ltac:(cbn; intuition discriminate) G12)|].
      constructor; [exact (UW 13%nat _ eq_refl ltac:(cbn; intuition discriminate) G13)|].
      constructor; [exact (UW 14%nat _ eq_refl ltac:(cbn; intuition discriminate) G14)|].
      constructor; [exact (UW 15%nat _ eq_refl ltac:(cbn; intuition discriminate) G15)|].
      constructor; [exact (UW 16%nat _ eq_refl ltac:(cbn; intuition discriminate) G16)|].
      constructor; [exact (UW 17%nat _ eq_refl ltac:(cbn; intuition discriminate) G17)|].
      constructor; [exact (UW 18%nat _ eq_refl ltac:(cbn; intuition discriminate) G18)|].
      constructor; [exact (UW 19%nat _ eq_refl ltac:(cbn; intuition discriminate) G19)|].
      constructor; [exact (UW 20%nat _ eq_refl ltac:(cbn; intuition discriminate) G20)|].
      constructor; [exact (UW 21%nat _ eq_refl ltac:(cbn; intuition discriminate) G21)|].
      constructor.
    + (* [comment removed for export] *)
      apply (rgs_disj_agree 200 E); [vm_compute; reflexivity | apply Eq_agree|]. exact HD.
    + (* [comment removed for export] *)
      cbn [s_facts with_pc MMA_Q].
      assert (Hw : forallb (fwf 200) MMA_F = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in Hw. rewrite Forall_forall in HF |- *. intros f Hf.
      exact (fact_ok_agree 200 E _ f (Hw f Hf) (Eq_agree _ _ _ _ _ _ _ _ _ _ _ _ _ _) (HF f Hf)).
  - apply upds_agree. repeat constructor; cbn [fst s_next MMA_P0]; lia.
  - (* [comment removed for export] *)
    intros x Hx. rewrite Hmem. apply MU.
    destruct Hx as [Hout|Hrt].
    + unfold FxStep.outside in Hout. cbn [s_rgs MMA_P0] in Hout. rewrite RGS0_eq in Hout. unfold RGS0, rt_rgs_t, relro_rgs in Hout. cbn [app] in Hout.
      apply Forall_cons_iff in Hout as [O0 Hout]. apply Forall_cons_iff in Hout as [O1 Hout]. clear Hout.
      pose proof mca_vals as (_ & _ & _ & _ & V5 & _).
      unfold rsz in O0, O1. cbn [rg_base rg_size track RGz] in O0, O1. rewrite V5 in O1.
      lnorm_in O0. change (bv_unsigned (lden E (lconst 496))) with 496 in O1.
      pose proof (bv_unsigned_in_range _ x) as Bx. unfold bv_modulus in Bx. change (2 ^ Z.of_N 64) with two64 in Bx.
      cbn [Frame.outside]. clear -O0 O1 W1 W2 Bx Fn. unfold two64 in *. repeat split; lia.
    + apply mca_HW. cbn [s_rgs MMA_P0] in Hrt. rewrite RGS0_eq in Hrt.
      exact (rt_frame E RGS0 [0%nat; 1%nat] x HD ltac:(vm_compute; reflexivity) Hrt).
  - destruct Heq as (_ & HFr & _ & _ & _ & HFc & _). cbn [ms_fregs ms_fcsr with_rom MS] in HFr, HFc. split; [exact HFr | exact HFc].
Qed.

End MCA.

Theorem mca_kfn_fp : kfn_ok_fp BSEGS MMA_P0 MMA_Q.
Proof. intros E ms Hd. exact (mca_run E ms Hd). Qed.
Theorem mca_kfn : kfn_ok BSEGS MMA_P0 MMA_Q.
Proof. exact (kfn_okP_ok BSEGS fpeq _ _ mca_kfn_fp). Qed.
