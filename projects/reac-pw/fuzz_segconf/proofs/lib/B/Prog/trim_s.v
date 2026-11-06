(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module paths and module names changed; 296 of its 332 lines of code are new or changed and 218 lines of the source are left out. *)
(* trim's image-B walk, the strlen call (0x896c4 .. 0x896f0): tr_after_ok : TR_TRAIL_stmt -> TR_FIN_stmt ->
   TR_AFTER_stmt (lib/B/Prog/trim_k.v). ADAPTED from the image-A G3 walk owner's image-A segment lib/A/Prog/trim_s.v
   (commit 07dedd5b93c6), re-derived on image B's code. From the leading loop's exit
   (s0 = p + lead, s2 = 1 - s0): 0x896c4 `mv a0,s0`, 0x896c8 `jal` the strlen trampoline (the listing's pa_sigma
   SS___interceptor_trampoline_strlen, image B 0x43a98), stepped by lib/B/Prog/PaArt.v aj_art_at with the walk's
   hypothesis ASTRLEN (the image-A wrapper-layer owner's interface row 16, RtString.astrlen_realizes); then
     0x896cc `addi a1,s2,-2`, 0x896d0 `bltu a1,a0`, UBSan trap site 2 of 3 (the pointer s0 + |s1| wraps; to the
       unimp 0x89770): a1 = 2 ^ 64 - 1 - s0, and s0 + |s1| = p + |s| < 2 ^ 47 (trim_pre's sa_addr), so not taken
       (tr_trap_ltu; the unit owner's UBSan walk lib/U/Prog/trim.v:151-152 discharges the same test);
     0x896d4 `add a2,s0,a0`, 0x896d8 `beqz a0`: |s1| = 0 goes to FIN through 0x8973c `mv a1,a2` with a1 = s0, else
       0x896dc `sub a0,a0,s2` (a0 = |s1| - (1 - s0) = e - 1) and the constants a3 = 1, a4 = 0x20, a5 = the mask, the
       trailing loop's head with e = s0 + |s1|.
   The string facts strlen asks (its bytes and NUL, aread_ok, the tail after the NUL, the read-only view) come from
   trim_pre at the entry through tr_mid's kept bytes: the string lies below the stack window (a side-stack frame or a
   heap block) or above the entry sp. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
(* interface row 16's carrier (the image-B wrapper-layer owner, 5b814360ea8f): RtString.astrlen_realizes *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase trim_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob trim_k trim_f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma tr_in_skipn : forall {A} (x : A) k l, In x (skipn k l) -> In x l.
Proof. intros A x k l H. rewrite <- (firstn_skipn k l). apply in_or_app. right. exact H. Qed.
(* the C string's tail from byte k as strlen's contract states a string (a list of bytes and its NUL) *)
Lemma tr_astr_of_zs : forall (rd : reader) p s k, (forall a v, rd a = Some v -> 0 <= v < 256) ->
  sa_zs rd p (s ++ [0]) -> ~ In 0 s -> (k <= length s)%nat ->
  astr_atR rd (p + Z.of_nat k) (seg_spec.zb (skipn k s)).
Proof.
intros rd p s k Hrng HZS NZ Hk.
assert (HV : forall i, (i <= length s)%nat -> rd (p + Z.of_nat i) = Some (nth i s 0)) by (intros i Hi; apply sa_zs_nth; [exact HZS | exact Hi]).
assert (HR : forall i, (i < length s)%nat -> 0 <= nth i s 0 < 256) by (intros i Hi; exact (Hrng _ _ (HV i ltac:(lia)))).
unfold seg_spec.zb. split.
- intros i Hi. rewrite length_app, length_map, length_skipn in Hi. cbn [length] in Hi.
  replace (p + Z.of_nat k + Z.of_nat i) with (p + Z.of_nat (k + i)) by lia.
  rewrite (HV (k + i)%nat) by lia.
  destruct (Nat.lt_ge_cases i (length s - k)) as [Hl | Hg].
  + rewrite app_nth1 by (rewrite length_map, length_skipn; lia).
    rewrite (map_nth (Z_to_bv 8) (skipn k s) 0 i), TrimB.nth_skipn0. rewrite bv8_small by (apply HR; lia). reflexivity.
  + assert (i = length s - k)%nat as -> by lia.
    rewrite app_nth2 by (rewrite length_map, length_skipn; lia).
    rewrite length_map, length_skipn, Nat.sub_diag. cbn [nth]. replace (k + (length s - k))%nat with (length s) by lia.
    rewrite nth_overflow by lia. reflexivity.
- intros Hin. apply in_map_iff in Hin as (x & Hx & Hin).
  pose proof (In_nth _ _ 0 (tr_in_skipn _ _ _ Hin)) as (i & Hi & Hxi).
  apply NZ. rewrite <- Hxi in Hx. pose proof (HR i Hi) as Hr.
  apply (f_equal bv_unsigned) in Hx. rewrite bv8_small in Hx by exact Hr. rewrite bv8_small in Hx by lia.
  rewrite <- Hx. apply nth_In. exact Hi.
Qed.

(* the shadow hull of a sub-range lies in the hull of the range *)
Lemma tr_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 Hn s Hs. apply H.
pose proof (Z.div_le_mono (shadow_addr x) (shadow_addr x') 8 ltac:(lia) (shadow_mono x x' H1)) as D1.
pose proof (Z.div_le_mono (shadow_addr (x' + n' - 1)) (shadow_addr (x + n - 1)) 8 ltac:(lia)
  (shadow_mono (x' + n' - 1) (x + n - 1) ltac:(lia))) as D2.
lia.
Qed.

Lemma tr_br_eq0 : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (v =? 0) = b.
Proof.
intros E n v b H Hv Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc.
Qed.

(* a register's value from the executor's alu terms over atoms of known value *)
Ltac tr_reg N :=
  rewrite N; cbn [sv_denot];
  repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
  rewrite ?w64_off, ?md_mul_lit, ?alu64_add_lit, ?alu64_sub_lit;
  unfold w64; first [reflexivity | f_equal; lia].

(* the trap test `bltu a1,a0` at 0x896d0, a1 = s2 - 2 = 2 ^ 64 - 1 - s0 (s2 = 1 - s0), a0 = |s1|: taken only when
   s0 + |s1| >= 2 ^ 64; the offset d is the executor's word for -2 *)
Lemma tr_trap_ltu : forall E m d n s0 v,
  branch_taken BC_LTU (sv_denot E (SOff m d)) (sv_denot E (SOff n 0)) = true ->
  ew E m = Z_to_bv 64 (1 - s0) -> ew E n = Z_to_bv 64 v ->
  1 <= s0 -> 0 <= v -> s0 + v < 2 ^ 64 -> (d + 2) mod 2 ^ 64 = 0 -> False.
Proof.
intros E m d n s0 v Hc Hm Hn Hs Hv Hsv Hd.
rewrite branch_ltu_U in Hc. unfold U in Hc. cbn [sv_denot] in Hc. rewrite Hm, Hn in Hc.
rewrite !unsigned_lit in Hc. unfold zcanon, M64 in Hc. apply Z.ltb_lt in Hc.
Z.div_mod_to_equations. lia.
Qed.

(* the AFTER seed: every register its own atom, no region *)
Definition ta_ss : sstate := mkSS TR_AFTER sr_atoms [] None (mkFacts [] [] []).
Definition TA_KEPT : list (bv 5) := 2%bv :: 8%bv :: 9%bv :: 18%bv :: TR_KEPT.
Lemma ta_kept_incl : forall r, In r (2%bv :: 9%bv :: TR_KEPT) -> In r TA_KEPT.
Proof.
intros r [<- | [<- | Hr]]; unfold TA_KEPT; [left; reflexivity | right; right; left; reflexivity | right; right; right; right; exact Hr].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* the runtime record facts of the image (the strlen step needs its errno cell, pal_env) *)
Hypothesis TL : PALib B.
(* the image-A wrapper-layer owner's interface row 16, at the listing's strlen trampoline *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Ltac ta_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* after a run that writes nothing: the environment agrees with E0 below k (HAE), the memory is the seed's (KM),
   every byte present at the seed is present (KP) *)
Ltac ta_after E0 HAE KM KP :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    lazymatch type of HAE with env_agree ?k _ _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KPn := fresh "KPn" in
    assert (HAEn : env_agree k E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H _) (ms_mem msn) a = aview SEGS (w_H _) _ a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    assert (KPn : forall a, apresent (w_H _) _ a -> apresent (w_H _) (ms_mem msn) a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (apresent_grows _ _ _ a HG (KP a Ha)));
    clear HFr HG HAE KM KP; rename HAEn into HAE; rename KMn into KM; rename KPn into KP;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
    end
  end.

Lemma tr_after_ok : TR_TRAIL_stmt B -> TR_FIN_stmt B -> TR_AFTER_stmt B.
Proof.
intros HTRAIL HFIN. unfold TR_AFTER_stmt.
intros ly S W regs mem md ch p s regs1 memc mdc HCX HMID HRG H8 H18.
pose proof (tr_cx_facts B LAWS ly S W regs mem md ch p s HCX)
  as (HSTR & HADDR & HZONE & HPR & HSB & Hp4096 & Hp47 & Hn32 & HOUT & Hal16 & Hsp0 & Hsp47).
pose proof HCX as (HPRE & HROD & H10 & Hp64 & _ & HEV).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HMID as (HJ0 & KEEP & KPR & _).
pose proof HRG as (R2 & R9 & RK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_trim = 4128) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HSTR as ((HZS & NZ) & HTAIL).
pose proof (TrimB.lead_le s NZ) as HLL. pose proof (TrimB.s1_len s NZ) as S1L. pose proof (TrimB.rtrim_len s NZ) as RTL.
assert (HE : trim_end_addr p s = p + Z.of_nat (seg_spec.trim_lead s) + Z.of_nat (TrimB.te s (length (TrimB.s1_of s))))
  by (unfold trim_end_addr; rewrite RTL; lia).
set (lead := seg_spec.trim_lead s) in *.
set (len1 := length (TrimB.s1_of s)) in *.
(* the seed *)
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) ta_ss
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + TR_AFTER)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ta_ss. apply pa_entry_st_ok_full;
    [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg regs1 []) (Eimg (Ereg regs1 [])))
  by (split; [intros n Hn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 [])) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
revert HS HEI HA0 EE. generalize (Eimg (Ereg regs1 [])) as E. intros E HS HEI HA0 EE.
assert (E8 : ew E 8 = Z_to_bv 64 (p + Z.of_nat lead)) by (rewrite (EE 8%nat 8%bv eq_refl); exact H8).
assert (E18 : ew E 18 = Z_to_bv 64 (1 - (p + Z.of_nat lead))) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (SHOK : sh_ok SEGS tr_Bx [] E (mrestrict (w_H W) memc)) by constructor.
unfold tr_at.
(* 0x89120 mv a0,s0; 0x89124 jal the strlen trampoline *)
paj_run_tok RUN HS HJ0 SHOK Bspan.
{ ta_awr. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H W) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
assert (KP1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HFr HG.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2'. prreg HS (3%bv : bv 5) R3'. prreg HS (4%bv : bv 5) R4'.
prreg HS (10%bv : bv 5) R10'.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ at 1. rewrite R2', (EE 2%nat 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (R3'' : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite R3', (EE 3%nat 3%bv eq_refl), (RK 3%bv ltac:(cbn; tauto)). exact Hgp. }
assert (R4'' : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite R4', (EE 4%nat 4%bv eq_refl), (RK 4%bv ltac:(cbn; tauto)). exact Htp. }
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the string at strlen's call: the entry's bytes, kept *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_trim <= a < spZ regs) -> rdW W (ms_mem ms) a = rdW W mem a)
  by (intros a Ha Hn; rewrite KM1 by exact Ha; exact (KEEP a Ha Hn)).
assert (HZS1 : sa_zs (rdW W (ms_mem ms)) p (s ++ [0])).
{ intros i Hi. rewrite length_app in Hi; cbn [length] in Hi. rewrite KEEP1 by lia.
  exact (HZS i ltac:(rewrite length_app; cbn [length]; lia)). }
assert (Hrng1 : forall a v, rdW W (ms_mem ms) a = Some v -> 0 <= v < 256)
  by (intros a v Hv; destruct (aview_byte SEGS (w_H W) (ms_mem ms) a v Hv) as (_ & _ & _ & Hr); exact Hr).
pose proof (tr_astr_of_zs _ p s lead Hrng1 HZS1 NZ HLL) as HSTR1.
set (s1b := seg_spec.zb (skipn lead s)) in *.
assert (Hlen1b : astr_len s1b = Z.of_nat (length s) - Z.of_nat lead)
  by (unfold astr_len, s1b, seg_spec.zb; rewrite length_map, length_skipn; lia).
assert (HRD : aread_ok SEGS ESTACK W (ms_regs ms) (ms_mem ms) (p + Z.of_nat lead) (astr_len s1b + 1)).
{ rewrite Hlen1b. destruct HADDR as (Ha0 & Ha63 & Hamr & HRA & HHV).
  split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros a Ha. split.
    - replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia. rewrite (sa_zs_nth _ p s _ HZS1) by lia. discriminate.
    - unfold ascratch_stk. rewrite Hsp1. lia. }
  split; [unfold amem_range in *; lia|]. split.
  - apply (range_addressable_kept_win (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - STK_trim) (spZ regs)); [exact KEEP1 | lia | lia | lia |].
    exact (range_addressable_sub _ _ p (Z.of_nat (length s) + 1) (p + Z.of_nat lead) (Z.of_nat (length s) - Z.of_nat lead + 1)
      HRA ltac:(lia) ltac:(lia)).
  - intros Hn. apply (shadow_hull_vis_kept_win (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - STK_trim) (spZ regs)); [exact KEEP1 | lia | lia | lia | lia |].
    exact (tr_hull_sub _ p (Z.of_nat (length s) + 1) (p + Z.of_nat lead) (Z.of_nat (length s) - Z.of_nat lead + 1)
      (HHV ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (HTV : atail_vis SEGS W (ms_mem ms) (p + Z.of_nat lead + astr_len s1b)).
{ rewrite Hlen1b. intros a Ha.
  replace (p + Z.of_nat lead + (Z.of_nat (length s) - Z.of_nat lead)) with (p + Z.of_nat (length s)) in Ha by lia.
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
  destruct (Z_lt_le_dec a (spZ regs - STK_trim)) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec a (spZ regs)) as [Hhi|Hhi]].
  - rewrite KEEP1 by lia. exact (HTAIL a Ha).
  - apply (aview_some_of_apresent SEGS). pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
    apply Hpres1. lia.
  - rewrite KEEP1 by lia. exact (HTAIL a Ha). }
assert (HROM1 : rt_rom_view SEGS B W (ms_mem ms)).
{ intros a (sg & Hsg & Hw & Hr) Ho He.
  pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hr))) as Hia. unfold kImgEnd in Hia.
  rewrite KEEP1 by lia. exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He). }
(* the call *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low ESTACK (fun _ => False) (SIG SS___interceptor_trampoline_strlen)
    W (ms_regs ms) (ms_mem ms) STK_trim (spZ regs) (tr_FP p s) ly S W mem md [] ly S _ 0 (-32)
    (Z_to_bv 64 (BASE + TR_RET)) _ HJ0 Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite HSTK, Hes; lia) R1
    (fun a (H : False) => False_ind _ H)).
  apply (ASTRLEN fx ly S W (ms_regs ms) (ms_mem ms) _ (p + Z.of_nat lead) s1b).
  - exact (ecall_pre_stk_at SEGS B ESTACK STK_trim (spZ regs) (tr_FP p s) ly S W mem md [] ly S W (ms_mem ms) _ 0
      (ms_regs ms) (-32) HJ0 Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite HSTK, Hes; lia) HraT R3'' R4'').
  - rewrite R10', E8. reflexivity.
  - lia.
  - apply astr_atR_view. exact HSTR1.
  - exact HRD.
  - exact HTV.
  - exact HROM1. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2).
jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ constructor. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 in HS end.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [assumption | cbv; lia]).
assert (E36 : ew E2 36 = Z_to_bv 64 (Z.of_nat (length s) - Z.of_nat lead))
  by (rewrite <- Hlen1b; unfold w64 in Ha02; rewrite <- Ha02, HE2; reflexivity).
assert (HA2 : env_agree 32 (Ereg regs1 []) E2).
{ rewrite HE2. eapply env_agree_trans; [exact HA0|]. apply (env_agree_havoc_ge 32 32); [lia|].
  first [apply env_agree_refl | eapply env_agree_le; [|apply env_agree_extK]; lia]. }
assert (E8' : ew E2 8 = Z_to_bv 64 (p + Z.of_nat lead)) by (rewrite (proj1 HA2 8%nat ltac:(lia)); exact H8).
assert (E18' : ew E2 18 = Z_to_bv 64 (1 - (p + Z.of_nat lead))) by (rewrite (proj1 HA2 18%nat ltac:(lia)); exact H18).
clear HE2.
assert (SHOK2 : sh_ok SEGS tr_Bx [] E2 (mrestrict (w_H W) mem2)) by constructor.
pose proof (env_agree_refl 48 E2) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W mem2 a = rdW W mem2 a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem2 a) by (intros; assumption).
(* the memory and the presence from the cut's to after the call *)
assert (KMc : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_trim <= a < spZ regs - 32) -> rdW W mem2 a = rdW W memc a).
{ intros a Ha Hn. rewrite HK2; [exact (KM1 a Ha) | exact Ha | rewrite HSTK in Hn; rewrite Hes; lia | tauto]. }
assert (KPc : forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) memc a -> ~ in_img SEGS a -> apresent (w_H W) mem2 a).
{ intros a Ha Hp Hi. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  destruct (Z_lt_le_dec a (spZ regs - STK_trim)) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec a (spZ regs - 32)) as [Hhi|Hhi]].
  - apply (apresent_transfer SEGS (w_H W) (w_H W) (ms_mem ms) mem2 a Ha Hi); [|exact (KP1 a Hp)].
    apply HK2; [exact Ha | rewrite HSTK in Hlo; rewrite Hes; lia | tauto].
  - apply Hpres2. lia.
  - apply (apresent_transfer SEGS (w_H W) (w_H W) (ms_mem ms) mem2 a Ha Hi); [|exact (KP1 a Hp)].
    apply HK2; [exact Ha | rewrite Hes; lia | tauto]. }
(* 0x896cc addi a1,s2,-2; 0x896d0 bltu a1,a0: UBSan trap site 2 of 3 (s0 + |s1| wraps), not taken *)
paj_run_tok RUN HS HJ2 SHOK2 Bspan.
{ ta_awr. }
ta_after E2 HAE KM KP.
psrr_branch_tok RUN BR HS SHOK2 Bspan.
{ exfalso. apply (tr_trap_ltu _ 18 _ 36 (p + Z.of_nat lead) (Z.of_nat (length s) - Z.of_nat lead) Hc).
  - exact (tr_ag_ew _ _ _ 18 _ HAE ltac:(lia) E18').
  - exact (tr_ag_ew _ _ _ 36 _ HAE ltac:(lia) E36).
  - lia. - lia. - lia.
  - vm_compute. reflexivity. }
clear Hc.
(* 0x896d4 add a2,s0,a0; 0x896d8 beqz a0 *)
paj_run_tok RUN HS HJ2 SHOK2 Bspan.
{ ta_awr. }
ta_after E2 HAE KM KP.
psrr_branch_tok RUN BR HS SHOK2 Bspan.
- (* |s1| = 0: FIN with a1 = s0 *)
  pose proof (tr_br_eq0 _ 36 _ _ (tr_ag_ew _ _ _ 36 _ HAE ltac:(lia) E36) ltac:(lia) Hc) as L0.
  apply Z.eqb_eq in L0. clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 Bspan TR_FIN. { ta_awr. }
  ta_after E2 HAE KM KP.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TA_KEPT HS (tr_ag32 _ _ _ _ 48 ltac:(lia) HA2 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof (tr_ag_ew _ _ _ 8 _ HAE ltac:(lia) E8') as E8n. pose proof (tr_ag_ew _ _ _ 36 _ HAE ltac:(lia) E36) as E36n.
  prreg HS (11%bv : bv 5) N11.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
  apply (HFIN ly S W regs mem md ch p s rg mm mdn HCX) end.
  + apply (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ2).
    * intros a Ha Hn. rewrite (KM a Ha). exact (KMc a Ha Hn).
    * intros a Ha Hp Hi. exact (KP a (KPc a Ha Hp Hi)).
  + exact (tr_regs_kept regs regs1 _ HRG (fun r Hr => HK r (ta_kept_incl r Hr))).
  + rewrite (HK 8%bv) by (cbn; tauto). exact H8.
  + assert (Hl1 : len1 = 0%nat) by lia. rewrite HE, Hl1, TrimB.te_0. tr_reg N11.
- (* |s1| > 0: TRAIL at j = |s1| *)
  pose proof (tr_br_eq0 _ 36 _ _ (tr_ag_ew _ _ _ 36 _ HAE ltac:(lia) E36) ltac:(lia) Hc) as L0.
  apply Z.eqb_neq in L0. clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 Bspan TR_TRAIL. { ta_awr. }
  ta_after E2 HAE KM KP.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TA_KEPT HS (tr_ag32 _ _ _ _ 48 ltac:(lia) HA2 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof (tr_ag_ew _ _ _ 8 _ HAE ltac:(lia) E8') as E8n. pose proof (tr_ag_ew _ _ _ 18 _ HAE ltac:(lia) E18') as E18n.
  pose proof (tr_ag_ew _ _ _ 36 _ HAE ltac:(lia) E36) as E36n.
  prreg HS (10%bv : bv 5) N10. prreg HS (12%bv : bv 5) N12. prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14.
  prreg HS (15%bv : bv 5) N15.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
  apply (HTRAIL ly S W regs mem md ch p s rg mm mdn len1 HCX) end.
  + apply (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ2).
    * intros a Ha Hn. rewrite (KM a Ha). exact (KMc a Ha Hn).
    * intros a Ha Hp Hi. exact (KP a (KPc a Ha Hp Hi)).
  + exact (tr_regs_kept regs regs1 _ HRG (fun r Hr => HK r (ta_kept_incl r Hr))).
  + lia.
  + reflexivity.
  + rewrite (HK 8%bv) by (cbn; tauto). exact H8.
  + tr_reg N10.
  + tr_reg N12.
  + first [exact N13 | rewrite N13; vm_compute; reflexivity].
  + first [exact N14 | rewrite N14; vm_compute; reflexivity].
  + first [exact N15 | rewrite N15; vm_compute; reflexivity].
Qed.

End e.
End f.
End d.
