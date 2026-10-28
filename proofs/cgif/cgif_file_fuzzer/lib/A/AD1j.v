(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i YA0n YA0e YG00 YG01 YG0f YG0v YG0n YG0s YG0d YCe5 YL02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AF0x AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1w AD1x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2p AE3i AE3h AE3m AE23 AE36 AE37 AD1k AD1o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Definition xconst_chk (rs : smem) (a : Z) (n : N) (v : Z) : bool :=
existsb (fun r => match YP09.r_base r with
| None => existsb (fun c => match YP09.c_val c with
| CImg len => (YP09.c_off c <=? a) && (a + Z.of_N n <=? YP09.c_off c + len) && img_cell_chk a (N.to_nat n) v
| CVal w (SLit v') => (YP09.c_off c =? a) && (w =? n)%N && (v' =? v) && (0 <=? v) && (v <? 2 ^ (8 * Z.of_N n)) && (Z.of_N n <=? 8)
| _ => false end) (YP09.r_chunks r)
| Some _ => false end) rs.
Lemma xconst_sound : forall E m rs a n v, mem_ok tfibsegs E m rs -> xconst_chk rs a n v = true -> val_mem tfibsegs m a (N.to_nat n) v.
Proof.
intros E m rs a n v HM Hc. unfold xconst_chk in Hc. apply existsb_exists in Hc as (r & Hr & Hc).
destruct (YP09.r_base r) as [b|] eqn:Hb; [discriminate|]. apply existsb_exists in Hc as (c & Hcin & Hc).
destruct c as [off cv]. cbn [YP09.c_val YP09.c_off] in Hc.
destruct cv as [w s| len | | ]; try discriminate.
- destruct s; try discriminate. apply andb_prop in Hc as [Hc H6]. apply andb_prop in Hc as [Hc H5]. apply andb_prop in Hc as [Hc H4].
apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply Z.eqb_eq in H1. apply N.eqb_eq in H2. apply Z.eqb_eq in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5. apply Z.leb_le in H6. subst off w z.
destruct HM as (_ & Hrs & _). pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. cbn [base_val] in Hck.
rewrite <- (Z.add_0_l a). apply (val_of_chunk_ok tfibsegs E m 0 a n (SLit v) v Hck); [reflexivity | lia | lia].
- apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply (val_mem_img m off (off + len)); [| lia | pose proof (N_nat_Z n); lia | exact H3].
exact (img_rd_of_mem_ok E m rs r off len HM Hr Hb Hcin).
Qed.
Definition xatom_chk (rs : smem) (a : Z) (w : N) (n : nat) : bool :=
existsb (fun r => match YP09.r_base r with
| None => existsb (fun c => match YP09.c_val c with
| CVal w' (SOff n' 0) => (YP09.c_off c =? a) && (w' =? w)%N && (n' =? n)%nat && (Z.of_N w <=? 8)
| _ => false end) (YP09.r_chunks r)
| Some _ => false end) rs.
Lemma xatom_sound : forall E m rs a w n v, mem_ok tfibsegs E m rs -> xatom_chk rs a w n = true ->
bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> val_mem tfibsegs m a (N.to_nat w) v.
Proof.
intros E m rs a w n v HM Hc Hv Hvr. unfold xatom_chk in Hc. apply existsb_exists in Hc as (r & Hr & Hc).
destruct (YP09.r_base r) as [b|] eqn:Hb; [discriminate|]. apply existsb_exists in Hc as (c & Hcin & Hc).
destruct c as [off cv]. cbn [YP09.c_val YP09.c_off] in Hc.
destruct cv as [w' s| len | | ]; try discriminate. destruct s as [ | n' [|p|p] | | | | | | | | | ]; try discriminate.
apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply Z.eqb_eq in H1. apply N.eqb_eq in H2. apply Nat.eqb_eq in H3. apply Z.leb_le in H4. subst off w' n'.
destruct HM as (_ & Hrs & _). pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. cbn [base_val] in Hck.
rewrite <- (Z.add_0_l a). apply (val_of_chunk_ok tfibsegs E m 0 a w (SOff n 0) _ Hck); [| exact Hvr | exact H4].
cbn [sv_denot]. rewrite Z.add_0_r, <- Hv, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Section g.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma cov0 : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md -> aview tfibsegs (w_H W) mem 0x137ea0 = Some 0.
Proof.
intros ly S W mem md HAR.
pose proof (tfib_const_lookup B HB ly S (w_H W) mem 0x137ea0 1 0 (proj1 HAR) ltac:(vm_compute; reflexivity)) as V.
pose proof (V 0%nat ltac:(cbn; lia)) as V0. rewrite Z.add_0_r in V0. unfold aview. rewrite V0. reflexivity.
Qed.
Lemma completed_free : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md -> ~ aowned B ly S 0xa2990.
Proof.
intros ly S W mem md HAR. apply (tfib_low_not_owned B ly S W mem md 0xa2990 HAR); [unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END; lia|].
apply (tfib_not_owned_static B 0xa2990 0xa2991 0xa2990 HB); [vm_compute; reflexivity | lia].
Qed.
Lemma mu0 : forall ly, cell_lookup (Tfib_const ly) (ANum 0xa38b0) = Some (ACell (ANum 0xa38b0) 8 (AV (ANum 0))).
Proof. intros ly. vm_compute. reflexivity. Qed.
Let X1 : xret_realizes tfibsegs B X1_PC XW1 XTRUE := x1_realizes B LAWS cov0.
Let X3 : xret_realizes tfibsegs B X3_PC XW3 X3PRE := x3_realizes B LAWS completed_free.
Let X2 : xret_realizes_noar tfibsegs B X2_PC XW2 XTRUE := x2_realizes B HB mu0.
Definition ex_chk (XI : smem) (cells : list (Z * N * Z)) : bool :=
forallb (fun f => match f with (a, n, v) =>
((F_STDERR <=? a) && (a <? F_STDERR + FILE_SZ)) || xconst_chk XI a n v end)%bool cells.
Lemma ex_consts_chk : ex_chk IMG_XL ex_consts = true /\ ex_chk IMG_X ex_consts1 = true.
Proof. vm_compute. split; reflexivity. Qed.
Definition XC (XI : smem) (cells : list (Z * N * Z)) : Prop := (XI = IMG_X /\ cells = ex_consts1) \/ (XI = IMG_XL /\ cells = ex_consts).
Lemma ex_consts_of_img : forall XI cells E (W : world tfibsegs) mem, XC XI cells -> mem_ok tfibsegs E (mrestrict (w_H W) mem) XI -> est (w_H W) mem ->
cells_are cells (mrestrict (w_H W) mem) /\
exists sew, val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew /\ val_mem tfibsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew /\ 0 <= sew < 2 ^ 64.
Proof.
intros XI cells E W mem HXC HM (sew & Hsew & E8 & E16 & E40 & E56 & E140). split; [| exists sew; exact (conj E40 (conj E56 Hsew))].
assert (CHK : ex_chk XI cells = true) by (destruct HXC as [[-> ->] | [-> ->]]; [exact (proj2 ex_consts_chk) | exact (proj1 ex_consts_chk)]).
unfold cells_are. apply (proj2 (Forall_forall _ _)). intros [[a n] v] Hin.
pose proof (proj1 (forallb_forall _ _) CHK _ Hin) as Hc. cbn beta iota in Hc.
apply orb_prop in Hc as [Hc|Hc]; [| exact (xconst_sound E _ XI a n v HM Hc)].
apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
assert (HFE : F_STDERR = 0xa2578) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity. rewrite HFE in H1, H2. rewrite HFS in H2.
destruct HXC as [[_ ->] | [_ ->]]; [unfold ex_consts1 in Hin | unfold ex_consts in Hin]; cbn [In] in Hin;
(repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; first [exact E8 | exact E16 | exact E140 | exfalso; clear - H1 H2; unfold F_STDIN in *; lia] | ]));
destruct Hin.
Qed.
Lemma ex_ranges_free : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) /\
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a).
Proof.
intros ly S W mem md HAR. rewrite (ts_tp B HB).
assert (HFE : F_STDERR = 0xa2578) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity. assert (HFO : F_STDOUT = 665192) by reflexivity.
assert (HFI : F_STDIN = 665432) by reflexivity. assert (HGC : A_GOT_canary = 650296) by reflexivity. assert (HCA : A_canary = 6262736) by reflexivity.
assert (HBF : STDOUT_BUFA = 6264480) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity. assert (HTP : TFIB_TP = 0x5d8f90) by reflexivity.
assert (G : forall lo hi a, forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r))%bool Tfib_owned_static = true ->
lo <= a < hi -> hi <= 0x5fb000 -> 0x10000 <= lo -> ~ aowned B ly S a).
{ intros lo hi a Hc Ha Hhi Hlo. apply (tfib_low_not_owned B ly S W mem md a HAR); [unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END; lia|]. exact (tfib_not_owned_static B lo hi a HB Hc Ha). }
split.
- intros a Hr. unfold ex_cell_range, vo_file, vf_file in Hr. rewrite HFE, HFS, HFO, HFI, HCA, HTP in Hr.
repeat (destruct Hr as [H|Hr]; [match type of H with ?lo <= a < ?hi => apply (G lo hi a); [vm_compute; reflexivity | exact H | lia | lia] end |]).
match type of Hr with ?lo <= a < ?hi => apply (G lo hi a); [vm_compute; reflexivity | exact Hr | lia | lia] end.
- intros a Ha. rewrite HBF, HBS in Ha. apply (G 6264480 (6264480 + 1024) a); [vm_compute; reflexivity | exact Ha | lia | lia].
Qed.
Theorem tfib_exit_site : exit_site_tfa B est xst.
Proof.
intros XI E W regs mem md ly S usp d fs code k HXI E0 [Ulo Uhi] U16 Htid Ha0 Hcode Hsp Hd Hret R3 R4 HMX Hwin HAI HAR HTOP Hnev HEST HK Hfd1 Hfs.
assert (HXI' : XI = IMG_X \/ XI = IMG_XL) by (destruct HXI as [[HX _] | HX]; [left | right]; exact HX).
assert (HXC : exists cls, XC XI cls /\ ((XI = IMG_X /\ k = 0%nat /\ cls = ex_consts1) \/ (XI = IMG_XL /\ cls = ex_consts))).
{ destruct HXI as [[HX Hk] | HX]; [exists ex_consts1 | exists ex_consts]; (split; [| first [left; repeat split; assumption || reflexivity | right; split; [assumption | reflexivity]]]);
[left | right]; split; [exact HX | reflexivity | exact HX | reflexivity]. }
destruct HXC as (cls & HXC & Hreg).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold sp_window_lo, sp_window_hi in Ulo, Uhi.
destruct HTOP as (Htopw & Hslo & Hshi & _).
assert (HVF : VF_STK = 9104) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HBF : STDOUT_BUFA = 6264480) by reflexivity. assert (HBS : STDOUT_BSZ = 1024) by reflexivity.
pose proof (ex_consts_of_img XI cls E W mem HXC HMX HEST) as (HC & sew & Hew1 & Hew2 & Hsewr).
pose proof (ex_ranges_free ly S W mem md HAR) as [HXown HBown].
assert (Ct : xatom_chk XI (TFIB_TP - 168) 4 8 = true) by (destruct HXI' as [-> | ->]; vm_compute; reflexivity).
pose proof (xatom_sound E _ XI _ _ _ _ HMX Ct eq_refl ltac:(change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia)) as Htidc.
rewrite <- (ts_tp B HB) in Htidc. change (N.to_nat 4) with 4%nat in Htidc. clear Ct.
assert (Cg : xconst_chk XI A_GOT_canary 8 A_canary = true) by (destruct HXI' as [-> | ->]; vm_compute; reflexivity).
assert (Cc : xatom_chk XI A_canary 8 41 = true) by (destruct HXI' as [-> | ->]; vm_compute; reflexivity).
pose proof (xconst_sound E _ XI _ _ _ HMX Cg) as Hgot.
pose proof (xatom_sound E _ XI _ _ _ _ HMX Cc eq_refl ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (u64_range (ew E 41)))) as Hcan.
change (N.to_nat 8) with 8%nat in Hgot, Hcan. clear Cg Cc.
assert (HPRE : ecall_pre tfibsegs B ly S W regs mem md).
{ split; [exact HAR|]. split; [exact Hret|]. split; [rewrite Hsp, <- Zminus_mod_idemp_l, U16; destruct Hd as [-> | ->]; reflexivity|].
split; [pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO; pose proof (lo_top _ LO) as (T1 & _); rewrite Hsp; unfold ly_bot, kStackSpan, ESTACK in *; lia|]. split; [rewrite Hshi, Hsp; unfold kHighMemEnd; lia|].
split; [intros a Ha; apply Hwin; rewrite Hsp in Ha; unfold ESTACK in Ha; lia|].
rewrite (ts_gp B HB), (ts_tp B HB). exact (conj R3 R4). }
assert (Hsp44 : 2 ^ 44 <= spZ regs) by (rewrite Hsp; lia).
assert (Hstk : ly_stk_lo ly + VF_STK <= spZ regs) by (pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO; pose proof (lo_top _ LO) as (T1 & _); rewrite Hsp, HVF; unfold ly_bot, kStackSpan in *; lia).
assert (Hband : forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) by (intros a Ha; unfold vf_band in Ha; rewrite Hsp, HVF in Ha; apply Hwin; lia).
assert (Hcode' : 0 <= code < 256) by lia.
assert (HTPX : as_tp B = TFIB_TPX) by (rewrite (ts_tp B HB); reflexivity).
change (mkCfg (mkst regs (w64 A_exit) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs AE23.A_exit regs mem md).
rewrite <- Hfs.
destruct HK as [[-> HSI] | [Hk1 HX]].
-
apply (srz_conseq tfibsegs _ (t_exit (Z_to_bv 64 code) (m_fs md))).
2:{ unfold wr, ex. cbn [Nat.sub repeat concat map]. apply t_eq_sym. apply t_emit_nil_eq. apply t_emit_has_nil. }
destruct Hreg as [(_ & _ & ->) | [_ ->]].
+ exact (tfib_exit_pristine1 B LAWS HB X1 X2 X3 ly S W regs mem md code _ (bv_unsigned (ew E 41)) sew HPRE Hsp44 Hstk Hband Ha0 Hcode' HTPX HC Htidc ltac:(lia)
Hgot Hcan (u64_range (ew E 41)) Hew1 Hew2 Hsewr (stdout_pristine_img _ _ HSI) HXown HBown HAI).
+ exact (tfib_exit_pristine B LAWS HB X1 X2 X3 ly S W regs mem md code _ (bv_unsigned (ew E 41)) sew HPRE Hsp44 Hstk Hband Ha0 Hcode' HTPX HC Htidc ltac:(lia)
Hgot Hcan (u64_range (ew E 41)) Hew1 Hew2 Hsewr (stdout_pristine_img _ _ HSI) HXown HBown HAI).
-
destruct Hreg as [(_ & Hk0 & _) | [_ ->]]; [exfalso; lia|].
destruct HX as (_ & Hcap & Hmid & HPEND).
destruct (Nat.eq_dec k 1) as [-> | Hk2].
+
apply (srz_conseq tfibsegs _ (t_exit (Z_to_bv 64 code) (m_fs md))).
2:{ unfold wr, ex. cbn [Nat.sub repeat concat map]. apply t_eq_sym. apply t_emit_nil_eq. apply t_emit_has_nil. }
replace (STDOUT_BUFA + 2 * (Z.of_nat 1 - 1)) with STDOUT_BUFA in Hmid by lia.
exact (tfib_exit_empty B LAWS HB X1 X2 X3 ly S W regs mem md code _ (bv_unsigned (ew E 41)) sew HPRE Hsp44 Hstk Hband Ha0 Hcode' HTPX HC Htidc ltac:(lia)
Hgot Hcan (u64_range (ew E 41)) Hew1 Hew2 Hsewr Hmid HXown HBown HAI).
+
unfold wr, ex.
apply (tfib_exit_flush B LAWS HB X1 X2 X3 ly S W regs mem md code _ (bv_unsigned (ew E 41)) sew (STDOUT_BUFA + 2 * (Z.of_nat k - 1)) (concat (repeat line0 (k - 1))) ch_stdout
HPRE Hsp44 Hstk Hband Ha0 Hcode' HTPX HC Htidc ltac:(lia) Hgot Hcan (u64_range (ew E 41)) Hew1 Hew2 Hsewr Hmid).
* rewrite length_pend. rewrite Nat2Z.inj_mul, Nat2Z.inj_sub by lia. cbn [Z.of_nat Pos.of_succ_nat]. lia.
* rewrite length_pend. lia.
* rewrite HBS. lia.
* intros i Hi. rewrite (HPEND i Hi). f_equal. f_equal. apply nth_indep. exact Hi.
* split; [exact (Hfd1 Hk1) | reflexivity].
* exact HXown.
* exact HBown.
* exact HAI.
Qed.
End g.
End e.
