(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_llvmfS1.v at a working branch 79d8c0f1b8f, RE-WALKED on B's
   instructions (B 0x809e0..0x80a50; A 0x8097c..0x809c4). Registers as on A. B differs from A by: four UBSan pointer-overflow
   guards between `add s4, a0, a1` and the first memchr, each branching to 0x80ba0 (L+0x224, `unimp`):
     0x809e8 bltu s4, a0          (uri < data)
     0x809f8 beqz a2              (a2 = (data != 0) ^ (uri == 0), set by 0x809ec snez / 0x809f0 seqz / 0x809f4 xor)
     0x80a00 bltu s2, s4          (text < uri)
     0x80a0c beqz a0              (a0 = (data != 0) ^ (text == 0), set by 0x80a04 seqz / 0x80a08 xor);
   each is proved NOT taken in lf_seg1: the trap arm of the branch split is refuted by B5's class lemma for it
   (lib/B/FMTrapB.v at a working branch c89f3cdf72d; FM-B-TRAPS.md rows 48-51: 0x809e8 and 0x80a00 class K3,
   fmt_add_ltu_not; 0x809f8 and 0x80a0c class K6, fmt_nullpres_not); and by the
   s6 / s1 arithmetic: A keeps s6 = (size != 0) and computes size - s6 in a0; B computes a1 = (size != 0), uri = data + a1,
   s6 := -a1 (0x80a10 neg) and, after the first memchr, s1 := size + s6 (0x80a30), s3 := s1 - k (0x80a34). lf_P1 (the cut
   to the next segment) is A's: s0 = un, s2 = text, s3 = tn, s4 = uri. Only the internal cut lf_M differs from A: s6 holds
   -(size != 0) (w64 (- lx_s6 cx)) instead of (size != 0). Imports: lib.A AXxx -> lib.ReusableB YXxx (a Theorem Labs lane's
   REUSABLEB-LIST); other lib.A -> lib.B; FMupoison stays lib.A. *)
(* LLVMFuzzerTestOneInput 0x8097c (fuzz_manifest.c:296-297), segment 0x809e0 .. 0x80a50: uri := data + (size != 0),
   text := uri + k, un := fuzz_strnlen (uri, k) by memchr (uri, 0, k), tn := fuzz_strnlen (text, size - (size != 0) - k)
   by memchr (text, 0, size - (size != 0) - k). lf_seg1: from 0x809e0 (lf_P0) to 0x80a30 (lf_M: s0 = un); lf_seg1b: from
   0x80a30 to 0x80a50 (lf_P1). No memory is written but memchr's stack window. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YE2k YCfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_llvmf0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_llvmfP FMW_llvmfD.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* between the two memchr calls: s0 = un; next: add s1, s1, s6 *)
Definition LF_M : Z := 0x80a30.

(* x + (-y), the second operand as the run holds it (2^64 - y, or 0) *)
Lemma lf_U_addneg : forall E a b x y, U E a = x -> U E b = (- y) mod 2 ^ 64 -> 0 <= x - y < 2 ^ 64 ->
  U E (SAlu ALU_ADD a b) = x - y.
Proof.
intros E a b x y Ha Hb Hr. rewrite U_SAlu, Ha, Hb. cbn [zalu_raw]. unfold zcanon, M64.
rewrite Z.add_mod_idemp_r by lia. replace (x + - y) with (x - y) by lia. apply Z.mod_small. exact Hr.
Qed.
(* an atom whose register holds any literal *)
Lemma lf_U_atom_mod : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof. intros E n v H. rewrite U_SOff, H, Z.add_0_r, unsigned_lit. unfold zcanon, M64. apply Z.mod_mod. lia. Qed.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis MEMCHR : amemchr_realizes tfibsegs B PC_memchr.

(* 0x80a30: s0 = un, s1 = size, s2 = text, s3 = k, s4 = uri, s6 = -(size != 0) (B: 0x80a10 neg s6, a1); the rest as at
   lf_P0 *)
Definition lf_M (cx : lfx) ly' S' (W' : world tfibsegs) regs' mem' md' : Prop :=
  lf_core B cx ly' S' W' regs' mem' md' 0 /\
  Permutation (ablocks B ly' S') (ablocks B (lx_ly cx) (lx_S cx)) /\
  fm_glob tfibsegs W' mem' (lx_live cx) (lx_peak cx) (lx_cnt cx) SIZE_MAXZ /\
  getr regs' 8 = w64 (lx_un cx) /\ getr regs' 9 = w64 (lx_n cx) /\ getr regs' 18 = w64 (lx_text cx) /\
  getr regs' 19 = w64 (lx_k cx) /\ getr regs' 20 = w64 (lx_uri cx) /\ getr regs' 22 = w64 (- lx_s6 cx).

(* a register the run left as a computed value v, U E v = z *)
Lemma lf_reg_U : forall H E ss ms (r : bv 5) v z,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = v -> U E v = z -> getr (ms_regs ms) r = w64 z.
Proof.
intros H E ss ms r v z HS Hr Hz. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. unfold w64. rewrite <- Hz.
unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* the same, for a value the run leaves as z mod 2^64 *)
Lemma lf_reg_Um : forall H E ss ms (r : bv 5) v z,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = v -> U E v = z mod 2 ^ 64 -> getr (ms_regs ms) r = w64 z.
Proof.
intros H E ss ms r v z HS Hr Hz. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. apply bv_eq. unfold w64.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact Hz.
Qed.

(* the input block lies below alloc_ceiling *)
Lemma lf_pb : forall cx, lf_base B cx -> 0 < lx_n cx -> 4096 <= lx_p cx /\ lx_p cx + lx_n cx + 8 <= alloc_ceiling.
Proof.
intros cx HB Hn. pose proof HB as ((HAR & _) & _ & _ & _ & Hblk & _).
destruct (lf_window B cx (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) 0 (lx_n cx) HB HAR
  (fun i _ => eq_refl) ltac:(intros Hn'; destruct Hblk as [[H0 _] | [_ Hin]]; [lia | exact Hin])
  ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & A1 & A2 & _).
lia.
Qed.

(* the input bytes ride through any step that keeps the memory below alloc_ceiling *)
Lemma lf_inkept_below : forall cx (W : world tfibsegs) m m',
  (0 < lx_n cx -> 0 <= lx_p cx /\ lx_p cx + lx_n cx <= alloc_ceiling) ->
  same_below m m' alloc_ceiling -> lf_inkept cx W m -> lf_inkept cx W m'.
Proof.
intros cx W m m' Hb HS HI i Hi.
rewrite (aview_below (w_H W) m m' alloc_ceiling (lx_p cx + i) HS) by (destruct (Hb ltac:(lia)); lia).
exact (HI i Hi).
Qed.
Lemma lf_inkept_low : forall cx (W : world tfibsegs) m m',
  (0 < lx_n cx -> 0 <= lx_p cx /\ lx_p cx + lx_n cx <= alloc_ceiling) ->
  low_same W W m m' -> lf_inkept cx W m -> lf_inkept cx W m'.
Proof.
intros cx W m m' Hb HL HI i Hi. rewrite (HL (lx_p cx + i)) by (destruct (Hb ltac:(lia)); lia). exact (HI i Hi).
Qed.

(* lf_core through a run that writes no memory and keeps sp, s5 and the callee-saved registers outside lf_X *)
Lemma lf_core_run : forall cx ly S W regs mem md k ss ms md',
  lf_base B cx -> lf_core B cx ly S W regs mem md k ->
  st_ok tfibsegs (Ereg regs []) ss (restrict (w_H W) ms) -> atoms_kept ss lf_X = true ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 21%bv = SOff 21 0 ->
  same_below mem (ms_mem ms) (2 ^ 64) ->
  lf_J B cx ly S W (ms_mem ms) md' k ->
  lf_core B cx ly S W (ms_regs ms) (ms_mem ms) md' k.
Proof.
intros cx ly S W regs mem md k ss ms md' HB (HJ & HFR & Hsp & HK & H21 & HIN & HRO) HS HA E2 E21 SB HJ'.
pose proof HB as (HAP & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & _).
pose proof asan_consts as (C1 & _).
assert (FS : LLVMF_STK = 32768) by reflexivity.
assert (SBc : same_below mem (ms_mem ms) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB); lia).
split; [exact HJ'|].
split; [apply (lf_frame_below cx W mem (ms_mem ms) SB); [unfold lx_sp0, LF_FRAME; lia | unfold lx_sp0; lia | exact HFR]|].
split; [unfold spZ at 1; rewrite (fmw_reg_atom _ regs [] ss ms 2%bv 2%bv 2 HS E2 eq_refl); exact Hsp|].
split; [exact (kept_step (w_H W) (lx_regs cx) regs [] ss ms (ms_regs ms) lf_X HK HS HA (fun r _ => eq_refl))|].
split; [rewrite (fmw_reg_atom _ regs [] ss ms 21%bv 21%bv 21 HS E21 eq_refl); exact H21|].
split; [|exact (arodata_below B W mem (ms_mem ms) SBc HRO)].
apply (lf_inkept_below cx W mem (ms_mem ms)); [|exact SBc|exact HIN].
intros Hn. pose proof (lf_pb cx HB Hn). lia.
Qed.

(* lf_core through a runtime call that writes only its window below sp (FMH_Rt.v rt_post_ro) *)
Lemma lf_core_rt : forall cx ly S W regs mem md k regs2 mem2 md2,
  lf_base B cx -> lf_core B cx ly S W regs mem md k ->
  lf_J B cx ly S W mem2 md2 k -> aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_RT_STR <= a < spZ regs) ->
     aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a) ->
  lf_core B cx ly S W regs2 mem2 md2 k.
Proof.
intros cx ly S W regs mem md k regs2 mem2 md2 HB (HJ & HFR & Hsp & HK & H21 & HIN & HRO) HJ2 HP Hfr.
pose proof HB as (HAP & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & _).
pose proof asan_consts as (C1 & _).
assert (FS : LLVMF_STK = 32768) by reflexivity.
assert (FR : STK_RT_STR = 8192) by reflexivity.
unfold lx_sp0, LF_FRAME in Hsp.
assert (LSm : low_same W W mem mem2) by (apply (low_same_of_win W mem mem2 (spZ regs - STK_RT_STR) (spZ regs) Hfr); lia).
split; [exact HJ2|].
split.
{ apply (lf_frame_kept cx W W mem mem2); [|exact HFR]. intros a Ha. unfold lx_sp0, LF_FRAME in Ha. apply Hfr; lia. }
split; [unfold spZ at 1; rewrite (fmw_pres _ _ 2%bv HP ltac:(fmw_cs_side)); unfold lx_sp0, LF_FRAME; exact Hsp|].
split; [intros r Hc Hn; rewrite (HP r Hc); exact (HK r Hc Hn)|].
split; [rewrite (fmw_pres _ _ 21%bv HP ltac:(fmw_cs_side)); exact H21|].
split; [|exact (arodata_low B W W mem mem2 LSm HRO)].
apply (lf_inkept_low cx W mem mem2); [|exact LSm|exact HIN].
intros Hn. pose proof (lf_pb cx HB Hn). lia.
Qed.

(* x - y as the run writes it: x + y * (2^64 - 1) *)
Lemma lf_U_sub : forall E a b m x y, U E a = x -> U E b = y -> m mod 2 ^ 64 = 2 ^ 64 - 1 -> 0 <= x - y < 2 ^ 64 ->
  U E (SAlu ALU_ADD a (SMd M_MUL b (SLit m))) = x - y.
Proof.
intros E a b m x y Ha Hb Hm Hr. rewrite U_SAlu, U_SMd, U_SLit, Ha, Hb. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
rewrite Hm, Z.add_mod_idemp_r by lia.
replace (x + y * (2 ^ 64 - 1)) with (x - y + y * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. exact Hr.
Qed.

(* ---- 0x80a30 .. 0x80a50: s1 := size + s6 (= size - (size != 0)); s3 := s1 - k; memchr (text, 0, s3); s3 := tn ---- *)
Lemma lf_seg1b : forall cx ly S W regs mem md, lf_base B cx -> lf_M cx ly S W regs mem md ->
  (forall ly' S' W' regs' mem' md' k', lf_P1 B cx ly' S' W' regs' mem' md' k' ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P1 regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs LF_M regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md HB (HC & Hperm & Hgl & H8 & H9 & H18 & H19 & H20 & H22) K1.
pose proof HC as (HJ & _ & Hsp & HK & H21 & HIN & HRO).
pose proof HB as (HAP & _ & _ & _ & Hblk & _).
pose proof HAP as (_ & _ & _ & Hgp & Htp & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & _).
pose proof (lx_ranges B cx HB) as (Rk & Rs6 & Rsk & Rn & Rn0 & Rn1 & Luw & Ltw & Run & Rtn & Lub).
pose proof asan_consts as (C1 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
assert (FS : LLVMF_STK = 32768) by reflexivity.
assert (FR : STK_RT_STR = 8192) by reflexivity.
assert (Hinb : 0 < lx_n cx -> In (lx_p cx, lx_n cx) (ablocks B ly S)).
{ intros Hn. apply (Permutation_in _ (Permutation_sym Hperm)). destruct Hblk as [[H0 _] | [_ Hin]]; [lia | exact Hin]. }
assert (Hn0 : 0 <= lx_n cx) by (unfold lx_n; lia).
assert (G3 : getr regs 3 = w64 (as_gp B)) by (rewrite (kept_get _ _ _ 3%bv HK ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Hgp).
assert (G4 : getr regs 4 = w64 (as_tp B)) by (rewrite (kept_get _ _ _ 4%bv HK ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Htp).
(* s3 := (size - k) + s6 = (size - k) - (size != 0) = len tw, as the run computes it (s6 holds 2^64 - 1 or 0; a2 and s3
   differ in the literal's form) *)
assert (U9 : U (Ereg regs []) (SOff 9 0) = lx_n cx)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl); exact H9 | lia]).
assert (U19 : U (Ereg regs []) (SOff 19 0) = lx_k cx)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl); exact H19 | lia]).
assert (U22 : U (Ereg regs []) (SOff 22 0) = (- lx_s6 cx) mod 2 ^ 64)
  by (apply lf_U_atom_mod; rewrite (ew_Ereg_nat regs [] 22 22%bv eq_refl); exact H22).
assert (UK : U (Ereg regs []) (SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 0) (SMd M_MUL (SOff 19 0) (SLit (-1)))) (SOff 22 0))
             = Z.of_nat (length (lx_tw cx))).
{ rewrite Ltw. replace (lx_n cx - lx_s6 cx - lx_k cx) with (lx_n cx - lx_k cx - lx_s6 cx) by lia.
  apply lf_U_addneg; [apply lf_U_sub; [exact U9 | exact U19 | reflexivity | lia] | exact U22 | lia]. }
assert (UK' : U (Ereg regs []) (SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 0) (SMd M_MUL (SOff 19 0) (SLit 18446744073709551615)))
               (SOff 22 0)) = Z.of_nat (length (lx_tw cx))).
{ rewrite Ltw. replace (lx_n cx - lx_s6 cx - lx_k cx) with (lx_n cx - lx_k cx - lx_s6 cx) by lia.
  apply lf_U_addneg; [apply lf_U_sub; [exact U9 | exact U19 | reflexivity | lia] | exact U22 | lia]. }
(* ---- the stretch up to jal memchr at 0x80a44 ---- *)
pose proof (fmw_resume_nr W regs [] mem LF_M) as HS.
unfold cfg_at. change (w64 LF_M) with (Z_to_bv 64 LF_M).
unfold lf_J in HJ.
aj_run_to fmw_tbl_llvmf_ok HS HJ PC_memchr.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
assert (SB1 : same_below mem (ms_mem ms1) (2 ^ 64)) by exact (frame_nil_same _ mem (ms_mem ms1) HF).
clear HF HFr.
assert (SB1c : same_below mem (ms_mem ms1) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB1); lia).
pose proof (lf_core_run cx ly S W regs mem md 0 _ ms1 _ HB HC HS ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) SB1 HJ) as HC1.
pose proof HC1 as (_ & _ & Hsp1' & _ & _ & HIN1 & HRO1).
assert (Hsp1 : spZ (ms_regs ms1) = lx_sp0 cx + -64) by (rewrite Hsp1'; unfold LF_FRAME; lia).
pose proof (fmw_reg_lit _ (Ereg regs []) _ ms1 1%bv 0x80a48 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fmw_reg_atom _ regs [] _ ms1 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs [] _ ms1 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs [] _ ms1 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fmw_reg_atom _ regs [] _ ms1 10%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_lit _ (Ereg regs []) _ ms1 11%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
pose proof (lf_reg_U _ _ _ ms1 12%bv _ _ HS ltac:(vm_compute; reflexivity) UK') as R12.
pose proof (fmw_reg_atom _ regs [] _ ms1 18%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl) as R18.
pose proof (lf_reg_U _ _ _ ms1 19%bv _ _ HS ltac:(vm_compute; reflexivity) UK) as R19.
pose proof (fmw_reg_atom _ regs [] _ ms1 20%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl) as R20.
pose proof HJ as (HAR1 & _).
destruct (IMG ly S W (ms_mem ms1) _ HAR1 HRO1) as (HROM1 & HROO1 & _).
destruct (lf_memchr_pre B cx ly S W (ms_mem ms1) _ (lx_text cx) (lx_tw cx) HB HAR1 HIN1 Hinb
  (or_intror (conj eq_refl eq_refl))) as (MB & M4 & Mc & Mam & Ml & Mra & Mh).
assert (Hgl1 : fm_glob tfibsegs W (ms_mem ms1) (lx_live cx) (lx_peak cx) (lx_cnt cx) SIZE_MAXZ)
  by exact (fm_glob_below W mem (ms_mem ms1) _ _ _ _ SB1c Hgl).
(* ---- memchr (text, 0, len tw) ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms1 HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 PC_memchr) (ms_mem ms1) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs PC_memchr (ms_regs ms1) (ms_mem ms1) m).
  eapply (fmw_aj_rt_ro B W (ms_regs ms1) (ms_mem ms1) _ PC_memchr _ _ _ _ _ _ _ _ ly S 0 STK_RT_STR _ (-64) HJ Hsp1);
    [lia | lia | lia |].
  apply (MEMCHR ly S W (ms_regs ms1) (ms_mem ms1) _ (lx_text cx) (Z.of_nat (length (lx_tw cx))) (lx_tw cx)).
  - apply (fmw_ecall_pre_k B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-64) HJ Hsp1).
    all: first [ reflexivity | lia | (cbv [STK_RT_STR ESTACK]; lia)
               | (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
               | (rewrite R3; exact G3) | (rewrite R4; exact G4) ].
  - exact HROM1.
  - exact HROO1.
  - rewrite R10. exact H18.
  - exact R11.
  - exact R12.
  - exact Ml.
  - exact MB.
  - reflexivity.
  - exact M4.
  - exact Mc.
  - exact Mam.
  - exact Mra.
  - exact Mh. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & H10v & Hv & Hvl & Hfr2).
rewrite R1.
pose proof (lf_core_rt cx ly S W (ms_regs ms1) (ms_mem ms1) _ 0 regs2 mem2 md2 HB HC1 HJ2 HP2 Hfr2) as HC2.
assert (LS2 : low_same W W (ms_mem ms1) mem2)
  by (apply (low_same_of_win W (ms_mem ms1) mem2 (spZ (ms_regs ms1) - STK_RT_STR) (spZ (ms_regs ms1)) Hfr2);
      unfold lx_sp0 in Hsp1; lia).
assert (Hgl2 : fm_glob tfibsegs W mem2 (lx_live cx) (lx_peak cx) (lx_cnt cx) SIZE_MAXZ)
  by exact (fm_glob_low W W (ms_mem ms1) mem2 _ _ _ _ LS2 Hgl1).
assert (P8 : getr regs2 8 = w64 (lx_un cx)) by (rewrite (fmw_pres _ _ 8%bv HP2 ltac:(fmw_cs_side)), R8; exact H8).
assert (P18 : getr regs2 18 = w64 (lx_text cx)) by (rewrite (fmw_pres _ _ 18%bv HP2 ltac:(fmw_cs_side)), R18; exact H18).
assert (P19 : getr regs2 19 = w64 (Z.of_nat (length (lx_tw cx))))
  by (rewrite (fmw_pres _ _ 19%bv HP2 ltac:(fmw_cs_side)); exact R19).
assert (P20 : getr regs2 20 = w64 (lx_uri cx)) by (rewrite (fmw_pres _ _ 20%bv HP2 ltac:(fmw_cs_side)), R20; exact H20).
assert (V10 : U (Ereg regs2 []) (SOff 10 0) = v)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs2 [] 10 10%bv eq_refl); exact H10v | lia]).
assert (V18 : U (Ereg regs2 []) (SOff 18 0) = lx_text cx)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs2 [] 18 18%bv eq_refl); exact P18 | lia]).
assert (VZ : U (Ereg regs2 []) (SLit 0) = 0) by (apply U_lit; lia).
pose proof (lf_memchr_len (lx_tw cx) (lx_text cx) v M4 Hvl) as Htn.
(* ---- 0x80a48: beqz a0 ---- *)
pose proof (fmw_resume_nr W regs2 [] mem2 0x80a48) as HS2.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS2 | intros Hb HS3 | intros Hb HS3];
  rewrite branch_eq_U, V10, VZ in Hb; clear HS2.
- (* memchr found no NUL: tn = len tw *)
  apply Z.eqb_eq in Hb. subst v.
  assert (Etn : lx_tn cx = Z.of_nat (length (lx_tw cx))).
  { destruct Htn as [[_ Ec] | [Hne _]]; [|lia]. unfold lx_tn, lx_tb. rewrite Ec. reflexivity. }
  aj_run_to fmw_tbl_llvmf_ok HS3 HJ2 LF_P1.
  { apply awr_ok_nil. }
  lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms3 end.
  assert (SB3 : same_below mem2 (ms_mem ms3) (2 ^ 64)) by exact (frame_nil_same _ mem2 (ms_mem ms3) HF).
  pose proof (lf_core_run cx ly S W regs2 mem2 md2 0 _ ms3 _ HB HC2 HS3 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) SB3 HJ2) as HC3.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms3 HS3 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 LF_P1) (ms_mem ms3) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs LF_P1 (ms_regs ms3) (ms_mem ms3) m).
  apply (K1 ly S W (ms_regs ms3) (ms_mem ms3) _ 0).
  split; [exact HC3|]. split; [reflexivity|]. split; [exact Hperm|].
  split; [exact (fm_glob_below W mem2 (ms_mem ms3) _ _ _ _ ltac:(apply (same_below_mono _ _ _ _ SB3); lia) Hgl2)|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 8%bv 8%bv 8 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P8|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 18%bv 18%bv 18 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P18|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 19%bv 19%bv 19 HS3 ltac:(vm_compute; reflexivity) eq_refl), P19, Etn;
          reflexivity|].
  rewrite (fmw_reg_atom _ regs2 [] _ ms3 20%bv 20%bv 20 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P20.
- (* memchr found the NUL at v: tn = v - text *)
  apply Z.eqb_neq in Hb.
  assert (Etn : lx_tn cx = v - lx_text cx).
  { destruct Htn as [[Hv0 _] | [_ Ec]]; [lia|]. unfold lx_tn, lx_tb. exact Ec. }
  assert (VS : U (Ereg regs2 []) (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 18 0) (SLit (-1)))) = lx_tn cx)
    by (rewrite Etn; apply lf_U_sub; [exact V10 | exact V18 | reflexivity | lia]).
  aj_run_to fmw_tbl_llvmf_ok HS3 HJ2 LF_P1.
  { apply awr_ok_nil. }
  lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms3 end.
  assert (SB3 : same_below mem2 (ms_mem ms3) (2 ^ 64)) by exact (frame_nil_same _ mem2 (ms_mem ms3) HF).
  pose proof (lf_core_run cx ly S W regs2 mem2 md2 0 _ ms3 _ HB HC2 HS3 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) SB3 HJ2) as HC3.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms3 HS3 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 LF_P1) (ms_mem ms3) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs LF_P1 (ms_regs ms3) (ms_mem ms3) m).
  apply (K1 ly S W (ms_regs ms3) (ms_mem ms3) _ 0).
  split; [exact HC3|]. split; [reflexivity|]. split; [exact Hperm|].
  split; [exact (fm_glob_below W mem2 (ms_mem ms3) _ _ _ _ ltac:(apply (same_below_mono _ _ _ _ SB3); lia) Hgl2)|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 8%bv 8%bv 8 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P8|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 18%bv 18%bv 18 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P18|].
  split; [exact (lf_reg_U _ _ _ ms3 19%bv _ _ HS3 ltac:(vm_compute; reflexivity) VS)|].
  rewrite (fmw_reg_atom _ regs2 [] _ ms3 20%bv 20%bv 20 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P20.
Qed.

(* ---- 0x809e0 .. 0x80a30: a1 := (size != 0); uri := data + a1; the four UBSan guards; text := uri + k; s6 := -a1;
   memchr (uri, 0, k); s0 := un ---- *)
Lemma lf_seg1 : forall cx ly S W regs mem md k, lf_base B cx -> lf_P0 B cx ly S W regs mem md k ->
  (forall ly' S' W' regs' mem' md' k', lf_P1 B cx ly' S' W' regs' mem' md' k' ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P1 regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs LF_P0 regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k HB HP0 K1.
destruct HP0 as (HC & -> & Hperm & Hgl & H9 & H10 & H19).
pose proof HC as (HJ & _ & Hsp & HK & H21 & HIN & HRO).
pose proof HB as (HAP & _ & _ & _ & Hblk & _).
pose proof HAP as (_ & _ & _ & Hgp & Htp & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & _).
pose proof (lx_ranges B cx HB) as (Rk & Rs6 & Rsk & Rn & Rn0 & Rn1 & Luw & Ltw & Run & Rtn & Lub).
pose proof asan_consts as (C1 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
assert (FS : LLVMF_STK = 32768) by reflexivity.
assert (FR : STK_RT_STR = 8192) by reflexivity.
assert (Hinb : 0 < lx_n cx -> In (lx_p cx, lx_n cx) (ablocks B ly S)).
{ intros Hn. apply (Permutation_in _ (Permutation_sym Hperm)). destruct Hblk as [[H0 _] | [_ Hin]]; [lia | exact Hin]. }
assert (Hn0 : 0 <= lx_n cx) by (unfold lx_n; lia).
assert (Hpr : 4096 <= lx_p cx /\ lx_uri cx = lx_p cx + lx_s6 cx /\ lx_text cx = lx_uri cx + lx_k cx /\
              lx_p cx + lx_n cx + 8 <= alloc_ceiling).
{ unfold lx_text, lx_uri. destruct (Z.eq_dec (lx_n cx) 0) as [E0|E0].
  - pose proof (Rn0 E0) as (A1 & A2 & A3). unfold A_EMPTY in A3. pose proof (proj1 alloc_ceiling_val). lia.
  - destruct (lf_pb cx HB ltac:(lia)). lia. }
destruct Hpr as (Hp4 & Huri & Htxt & Hpc).
assert (Hs6 : lx_s6 cx = if 0 <? lx_n cx then 1 else 0).
{ unfold lx_s6. destruct (Z.eqb_spec (lx_n cx) 0), (Z.ltb_spec 0 (lx_n cx)); lia. }
assert (G3 : getr regs 3 = w64 (as_gp B)) by (rewrite (kept_get _ _ _ 3%bv HK ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Hgp).
assert (G4 : getr regs 4 = w64 (as_tp B)) by (rewrite (kept_get _ _ _ 4%bv HK ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Htp).
(* the values the stretch computes *)
assert (U9 : U (Ereg regs []) (SOff 9 0) = lx_n cx)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl); exact H9 | lia]).
assert (U10 : U (Ereg regs []) (SOff 10 0) = lx_p cx)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10 | lia]).
assert (U19 : U (Ereg regs []) (SOff 19 0) = lx_k cx)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl); exact H19 | lia]).
assert (US6 : U (Ereg regs []) (SAlu ALU_SLTU (SLit 0) (SOff 9 0)) = lx_s6 cx).
{ rewrite U_SAlu, U_lit, U9 by lia. cbn [zalu_raw]. rewrite Hs6. unfold zcanon, M64. destruct (0 <? lx_n cx); reflexivity. }
assert (UU : U (Ereg regs []) (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SLit 0) (SOff 9 0))) = lx_uri cx).
{ rewrite U_SAlu, U10, US6. cbn [zalu_raw]. unfold zcanon, M64. rewrite Huri. apply Z.mod_small. lia. }
assert (UA : U (Ereg regs []) (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SLit 0) (SOff 9 0))) (SLit 0))
             = lx_uri cx).
{ rewrite U_SAlu, UU, U_lit by lia. cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. lia. }
assert (UT : U (Ereg regs []) (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SLit 0) (SOff 9 0))) (SOff 19 0))
             = lx_text cx).
{ rewrite U_SAlu, UU, U19. cbn [zalu_raw]. unfold zcanon, M64. rewrite Htxt. apply Z.mod_small. lia. }
(* s6 := -(size != 0) (0x80a10 neg s6, a1) *)
assert (UN6 : U (Ereg regs []) (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU (SLit 0) (SOff 9 0))) = (- lx_s6 cx) mod 2 ^ 64).
{ rewrite U_SAlu, U_lit, US6 by lia. cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.sub_0_l. reflexivity. }
(* text = uri + k lies below 2^64 *)
assert (Hr64 : lx_text cx < 2 ^ 64).
{ pose proof (U_range (Ereg regs []) (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SLit 0) (SOff 9 0))) (SOff 19 0)))
    as R. rewrite UT in R. unfold M64 in R. exact (proj2 R). }
(* ---- the stretch up to jal memchr at 0x80a20, through the four UBSan guards; each branches to 0x80ba0 (L+0x224,
   `unimp`, the UBSan trap) and each is NOT taken (FMTrapB, FM-B-TRAPS.md rows 48-51) ---- *)
pose proof (fmw_resume_nr W regs [] mem LF_P0) as HS.
unfold cfg_at. change (w64 LF_P0) with (Z_to_bv 64 LF_P0).
unfold lf_J in HJ.
(* 0x809e0 snez a1, s1; add s4, a0, a1; the run stops at the guard 0x809e8 *)
aj_run_to fmw_tbl_llvmf_ok HS HJ PC_memchr.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msa end.
assert (SBa : same_below mem (ms_mem msa) (2 ^ 64)) by exact (frame_nil_same _ mem (ms_mem msa) HF).
clear HF HFr.
(* guard 1: 0x809e8 bltu s4, a0, 0x80ba0 -- NOT taken: data + (size != 0) does not wrap (K3, fmt_add_ltu_not) *)
eapply SRr_sym_branch with (c := BC_LTU) (a := SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SLit 0) (SOff 9 0)))
  (b := SOff 10 0); [exact HS | intros Ht _ | intros _ HS'].
{ exfalso. exact (eq_true_false_abs _ Ht (fmt_add_ltu_not _ _ _
    ltac:(rewrite U10, US6; clear - Hr64 Huri Htxt Rk Rs6; lia))). }
clear HS. rename HS' into HS.
(* 0x809ec snez a0, a0; seqz a2, s4; xor a2, a0, a2; the run stops at the guard 0x809f8 *)
aj_run_to fmw_tbl_llvmf_ok HS HJ PC_memchr.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msb end.
assert (SBb : same_below mem (ms_mem msb) (2 ^ 64))
  by exact (same_below_trans _ _ _ _ SBa (frame_nil_same _ (ms_mem msa) (ms_mem msb) HF)).
clear HF HFr.
(* guard 2: 0x809f8 beqz a2, 0x80ba0 -- NOT taken: a2 = (data != 0) ^ (uri == 0) = 1 ^ 0 (K6, fmt_nullpres_not) *)
eapply SRr_sym_branch with (c := BC_EQ)
  (a := SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 10 0))
          (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SLit 0) (SOff 9 0))) (SLit 1)))
  (b := SLit 0); [exact HS | intros Ht _ | intros _ HS'].
{ exfalso. exact (eq_true_false_abs _ Ht (fmt_nullpres_not _ _ _ _ _ _ ltac:(apply U_lit; lia) ltac:(apply U_lit; lia)
    ltac:(apply U_lit; lia) ltac:(rewrite U10; clear - Hp4; lia) ltac:(rewrite UU; clear - Hp4 Huri Rs6; lia))). }
clear HS. rename HS' into HS.
(* 0x809fc add s2, s4, s3; the run stops at the guard 0x80a00 *)
aj_run_to fmw_tbl_llvmf_ok HS HJ PC_memchr.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msc end.
assert (SBc : same_below mem (ms_mem msc) (2 ^ 64))
  by exact (same_below_trans _ _ _ _ SBb (frame_nil_same _ (ms_mem msb) (ms_mem msc) HF)).
clear HF HFr.
(* guard 3: 0x80a00 bltu s2, s4, 0x80ba0 -- NOT taken: uri + k does not wrap (K3, fmt_add_ltu_not) *)
eapply SRr_sym_branch with (c := BC_LTU)
  (a := SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SLit 0) (SOff 9 0))) (SOff 19 0))
  (b := SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SLit 0) (SOff 9 0))); [exact HS | intros Ht _ | intros _ HS'].
{ exfalso. exact (eq_true_false_abs _ Ht (fmt_add_ltu_not _ _ _ ltac:(rewrite UU, U19; clear - Hr64 Htxt; lia))). }
clear HS. rename HS' into HS.
(* 0x80a04 seqz a2, s2; xor a0, a0, a2; the run stops at the guard 0x80a0c *)
aj_run_to fmw_tbl_llvmf_ok HS HJ PC_memchr.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msd end.
assert (SBd : same_below mem (ms_mem msd) (2 ^ 64))
  by exact (same_below_trans _ _ _ _ SBc (frame_nil_same _ (ms_mem msc) (ms_mem msd) HF)).
clear HF HFr.
(* guard 4: 0x80a0c beqz a0, 0x80ba0 -- NOT taken: a0 = (data != 0) ^ (text == 0) = 1 ^ 0 (K6, fmt_nullpres_not) *)
eapply SRr_sym_branch with (c := BC_EQ)
  (a := SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 10 0))
          (SAlu ALU_SLTU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SAlu ALU_SLTU (SLit 0) (SOff 9 0))) (SOff 19 0))
             (SLit 1)))
  (b := SLit 0); [exact HS | intros Ht _ | intros _ HS'].
{ exfalso. exact (eq_true_false_abs _ Ht (fmt_nullpres_not _ _ _ _ _ _ ltac:(apply U_lit; lia) ltac:(apply U_lit; lia)
    ltac:(apply U_lit; lia) ltac:(rewrite U10; clear - Hp4; lia) ltac:(rewrite UT; clear - Hp4 Htxt Huri Rs6 Rk; lia))). }
clear HS. rename HS' into HS.
(* 0x80a10 neg s6, a1; a0 := uri; a1 := 0; a2 := k; jal memchr *)
aj_run_to fmw_tbl_llvmf_ok HS HJ PC_memchr.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
assert (SB1 : same_below mem (ms_mem ms1) (2 ^ 64))
  by exact (same_below_trans _ _ _ _ SBd (frame_nil_same _ (ms_mem msd) (ms_mem ms1) HF)).
clear HF HFr.
assert (SB1c : same_below mem (ms_mem ms1) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB1); lia).
pose proof (lf_core_run cx ly S W regs mem md 0 _ ms1 _ HB HC HS ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) SB1 HJ) as HC1.
pose proof HC1 as (_ & _ & Hsp1' & _ & _ & HIN1 & HRO1).
assert (Hsp1 : spZ (ms_regs ms1) = lx_sp0 cx + -64) by (rewrite Hsp1'; unfold LF_FRAME; lia).
pose proof (fmw_reg_lit _ (Ereg regs []) _ ms1 1%bv 0x80a24 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fmw_reg_atom _ regs [] _ ms1 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs [] _ ms1 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs [] _ ms1 9%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl) as R9.
pose proof (lf_reg_U _ _ _ ms1 10%bv _ _ HS ltac:(vm_compute; reflexivity) UA) as R10.
pose proof (fmw_reg_lit _ (Ereg regs []) _ ms1 11%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
pose proof (fmw_reg_atom _ regs [] _ ms1 12%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl) as R12.
pose proof (lf_reg_U _ _ _ ms1 18%bv _ _ HS ltac:(vm_compute; reflexivity) UT) as R18.
pose proof (fmw_reg_atom _ regs [] _ ms1 19%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl) as R19.
pose proof (lf_reg_U _ _ _ ms1 20%bv _ _ HS ltac:(vm_compute; reflexivity) UU) as R20.
pose proof (lf_reg_Um _ _ _ ms1 22%bv _ _ HS ltac:(vm_compute; reflexivity) UN6) as R22.
pose proof HJ as (HAR1 & _).
destruct (IMG ly S W (ms_mem ms1) _ HAR1 HRO1) as (HROM1 & HROO1 & _).
destruct (lf_memchr_pre B cx ly S W (ms_mem ms1) _ (lx_uri cx) (lx_uw cx) HB HAR1 HIN1 Hinb
  (or_introl (conj eq_refl eq_refl))) as (MB & M4 & Mc & Mam & Ml & Mra & Mh).
rewrite Luw in Mc, Mam, Mh.
assert (Hgl1 : fm_glob tfibsegs W (ms_mem ms1) (lx_live cx) (lx_peak cx) (lx_cnt cx) SIZE_MAXZ)
  by exact (fm_glob_below W mem (ms_mem ms1) _ _ _ _ SB1c Hgl).
(* ---- memchr (uri, 0, k) ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms1 HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 PC_memchr) (ms_mem ms1) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs PC_memchr (ms_regs ms1) (ms_mem ms1) m).
  eapply (fmw_aj_rt_ro B W (ms_regs ms1) (ms_mem ms1) _ PC_memchr _ _ _ _ _ _ _ _ ly S 0 STK_RT_STR _ (-64) HJ Hsp1);
    [lia | lia | lia |].
  apply (MEMCHR ly S W (ms_regs ms1) (ms_mem ms1) _ (lx_uri cx) (lx_k cx) (lx_uw cx)).
  - apply (fmw_ecall_pre_k B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-64) HJ Hsp1).
    all: first [ reflexivity | lia | (cbv [STK_RT_STR ESTACK]; lia)
               | (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity)
               | (rewrite R3; exact G3) | (rewrite R4; exact G4) ].
  - exact HROM1.
  - exact HROO1.
  - exact R10.
  - exact R11.
  - rewrite R12. exact H19.
  - lia.
  - exact MB.
  - exact Luw.
  - exact M4.
  - exact Mc.
  - exact Mam.
  - exact Mra.
  - exact Mh. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & H10v & Hv & Hvl & Hfr2).
rewrite R1.
pose proof (lf_core_rt cx ly S W (ms_regs ms1) (ms_mem ms1) _ 0 regs2 mem2 md2 HB HC1 HJ2 HP2 Hfr2) as HC2.
assert (LS2 : low_same W W (ms_mem ms1) mem2)
  by (apply (low_same_of_win W (ms_mem ms1) mem2 (spZ (ms_regs ms1) - STK_RT_STR) (spZ (ms_regs ms1)) Hfr2);
      unfold lx_sp0 in Hsp1; lia).
assert (Hgl2 : fm_glob tfibsegs W mem2 (lx_live cx) (lx_peak cx) (lx_cnt cx) SIZE_MAXZ)
  by exact (fm_glob_low W W (ms_mem ms1) mem2 _ _ _ _ LS2 Hgl1).
assert (P9 : getr regs2 9 = w64 (lx_n cx)) by (rewrite (fmw_pres _ _ 9%bv HP2 ltac:(fmw_cs_side)), R9; exact H9).
assert (P18 : getr regs2 18 = w64 (lx_text cx)) by (rewrite (fmw_pres _ _ 18%bv HP2 ltac:(fmw_cs_side)); exact R18).
assert (P19 : getr regs2 19 = w64 (lx_k cx)) by (rewrite (fmw_pres _ _ 19%bv HP2 ltac:(fmw_cs_side)), R19; exact H19).
assert (P20 : getr regs2 20 = w64 (lx_uri cx)) by (rewrite (fmw_pres _ _ 20%bv HP2 ltac:(fmw_cs_side)); exact R20).
assert (P22 : getr regs2 22 = w64 (- lx_s6 cx)) by (rewrite (fmw_pres _ _ 22%bv HP2 ltac:(fmw_cs_side)); exact R22).
assert (V10 : U (Ereg regs2 []) (SOff 10 0) = v)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs2 [] 10 10%bv eq_refl); exact H10v | lia]).
assert (V20 : U (Ereg regs2 []) (SOff 20 0) = lx_uri cx)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs2 [] 20 20%bv eq_refl); exact P20 | lia]).
assert (VZ : U (Ereg regs2 []) (SLit 0) = 0) by (apply U_lit; lia).
pose proof (lf_memchr_len (lx_uw cx) (lx_uri cx) v M4 Hvl) as Hun.
(* ---- 0x80a24: s0 := k; beqz a0 ---- *)
pose proof (fmw_resume_nr W regs2 [] mem2 0x80a24) as HS2.
aj_run fmw_tbl_llvmf_ok HS2 HJ2.
{ apply awr_ok_nil. }
lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
assert (SB2 : same_below mem2 (ms_mem ms2) (2 ^ 64)) by exact (frame_nil_same _ mem2 (ms_mem ms2) HF).
clear HF HFr.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS2 | intros Hb HS3 | intros Hb HS3];
  rewrite branch_eq_U, V10, VZ in Hb; clear HS2.
- (* memchr found no NUL: un = k *)
  apply Z.eqb_eq in Hb. subst v.
  assert (Eun : lx_un cx = lx_k cx).
  { destruct Hun as [[_ Ec] | [Hne _]]; [|lia]. unfold lx_un, lx_ub. rewrite Ec. exact Luw. }
  aj_run_to fmw_tbl_llvmf_ok HS3 HJ2 LF_M.
  { apply awr_ok_nil. }
  lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms3 end.
  assert (SB3 : same_below mem2 (ms_mem ms3) (2 ^ 64))
    by exact (same_below_trans _ _ _ _ SB2 (frame_nil_same _ (ms_mem ms2) (ms_mem ms3) HF)).
  pose proof (lf_core_run cx ly S W regs2 mem2 md2 0 _ ms3 _ HB HC2 HS3 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) SB3 HJ2) as HC3.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms3 HS3 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 LF_M) (ms_mem ms3) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs LF_M (ms_regs ms3) (ms_mem ms3) m).
  apply (lf_seg1b cx ly S W (ms_regs ms3) (ms_mem ms3) _ HB); [|exact K1].
  split; [exact HC3|]. split; [exact Hperm|].
  split; [exact (fm_glob_below W mem2 (ms_mem ms3) _ _ _ _ ltac:(apply (same_below_mono _ _ _ _ SB3); lia) Hgl2)|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 8%bv 19%bv 19 HS3 ltac:(vm_compute; reflexivity) eq_refl), P19, Eun;
          reflexivity|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 9%bv 9%bv 9 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P9|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 18%bv 18%bv 18 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P18|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 19%bv 19%bv 19 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P19|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 20%bv 20%bv 20 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P20|].
  rewrite (fmw_reg_atom _ regs2 [] _ ms3 22%bv 22%bv 22 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P22.
- (* memchr found the NUL at v: un = v - uri *)
  apply Z.eqb_neq in Hb.
  assert (Eun : lx_un cx = v - lx_uri cx).
  { destruct Hun as [[Hv0 _] | [_ Ec]]; [lia|]. unfold lx_un, lx_ub. exact Ec. }
  assert (VS : U (Ereg regs2 []) (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 20 0) (SLit (-1)))) = lx_un cx)
    by (rewrite Eun; apply lf_U_sub; [exact V10 | exact V20 | reflexivity | lia]).
  aj_run_to fmw_tbl_llvmf_ok HS3 HJ2 LF_M.
  { apply awr_ok_nil. }
  lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms3 end.
  assert (SB3 : same_below mem2 (ms_mem ms3) (2 ^ 64))
    by exact (same_below_trans _ _ _ _ SB2 (frame_nil_same _ (ms_mem ms2) (ms_mem ms3) HF)).
  pose proof (lf_core_run cx ly S W regs2 mem2 md2 0 _ ms3 _ HB HC2 HS3 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) SB3 HJ2) as HC3.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms3 HS3 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 LF_M) (ms_mem ms3) (seg_rom tfibsegs)) ?m)
    with (cfg_at tfibsegs LF_M (ms_regs ms3) (ms_mem ms3) m).
  apply (lf_seg1b cx ly S W (ms_regs ms3) (ms_mem ms3) _ HB); [|exact K1].
  split; [exact HC3|]. split; [exact Hperm|].
  split; [exact (fm_glob_below W mem2 (ms_mem ms3) _ _ _ _ ltac:(apply (same_below_mono _ _ _ _ SB3); lia) Hgl2)|].
  split; [exact (lf_reg_U _ _ _ ms3 8%bv _ _ HS3 ltac:(vm_compute; reflexivity) VS)|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 9%bv 9%bv 9 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P9|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 18%bv 18%bv 18 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P18|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 19%bv 19%bv 19 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P19|].
  split; [rewrite (fmw_reg_atom _ regs2 [] _ ms3 20%bv 20%bv 20 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P20|].
  rewrite (fmw_reg_atom _ regs2 [] _ ms3 22%bv 22%bv 22 HS3 ltac:(vm_compute; reflexivity) eq_refl); exact P22.
Qed.
End X.
