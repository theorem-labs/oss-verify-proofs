(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module paths and module names changed; 263 of its 296 lines of code are new or changed and 221 lines of the source are left out. *)
(* trim's image-A walk, the trailing-blank loop (0x89148 .. 0x8918c): tr_trail_ok : TR_FIN_stmt -> TR_TRAIL_stmt
   (lib/A/Prog/trim_k.v), by induction on j, the bytes of s1 = dropwhile blank s still before e, in the form of
   fuzz_command's answer_l.v (a loop with inline checks, re-seeded at each iteration). One iteration at e = p + lead + j:
   check 2 (0x89148-0x89184, load1 at e - 1: the obligation that e - 1 is addressable, from trim_pre's sa_addr), the
   byte c = s[lead + j - 1], `bltu 0x20, c` and bit c of the mask: c not blank goes to FIN with a1 = e (and then
   te s j = j); c blank steps e down and either loops (e - 1 > s0) or goes to FIN with a1 = s0 (j = 1, te s 1 = 0).
   The plain proof of the same loop: the plain-build walk owner's lib/Prog/trim.v LOOP2 at db8c4beebf62. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegGlob SegInstA trim_c trim_k trim_t.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- TRAIL, 0x89148: every register its own atom but a3 = 0x20 and a4 = the mask (pinned); a0 = e - 1 (atom 10,
   the check's address), a2 = e (atom 12; the load reads e - 1 through a1 = a2 - 1), s0 = p + lead (atom 8), s2 = SB
   (atom 18); the extra atom 32 is the byte at e - 1, the one region (read only) ---- *)
Definition tt_regs : list sv := sr_set (sr_set sr_atoms 13%bv (SLit 32)) 14%bv (SLit TR_MASK).
Definition tt_regions : smem :=
[ YP09.mkRegion (Some 12%nat) (-1) 0 (-1) (-1) [YP09.mkChunk (-1) (CVal 1 (SOff 32 0))] ].
Definition tt_facts : facts :=
mkFacts [ (8%nat, mkAF 4096 (2 ^ 47 - 1) 0); (10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (12%nat, mkAF 4097 (2 ^ 47 - 1) 0);
          (18%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition tt_ss : sstate := mkSS TR_TRAIL tt_regs tt_regions None tt_facts.
(* the registers an iteration does not write *)
Definition TT_KEPT : list (bv 5) := 2%bv :: 8%bv :: 18%bv :: TR_KEPT.
Lemma tt_kept_incl : forall r, In r (2%bv :: 18%bv :: TR_KEPT) -> In r TT_KEPT.
Proof.
intros r [<- | [<- | Hr]]; unfold TT_KEPT; [left; reflexivity | right; right; left; reflexivity | right; right; right; exact Hr].
Qed.

(* the branches of an iteration *)
Lemma tr_br_ltu_lit : forall E n v z b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SLit z)) (sv_denot E (SOff n 0)) = b -> (z <? v) = b.
Proof.
intros E n v z b H Hv Hz Hc. rewrite branch_ltu_U, U_lit, (U_atom E n v H Hv) in Hc by exact Hz. exact Hc.
Qed.
Lemma tr_br_ltu_off : forall E n m v w d b, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w ->
0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> 0 <= w + d < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SOff n 0)) (sv_denot E (SOff m d)) = b -> (v <? w + d) = b.
Proof.
intros E n m v w d b Hn Hm Hv Hw Hd Hc. rewrite branch_ltu_U, (U_atom E n v Hn Hv), (U_atom_off E m w d Hm Hw Hd) in Hc.
exact Hc.
Qed.
Lemma tr_br_mask : forall E n c b, ew E n = Z_to_bv 64 c -> 0 <= c <= 32 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SAlu ALU_SRL (SLit TR_MASK) (SOff n 0)) (SLit 1))) (sv_denot E (SLit 0)) = b ->
negb (SegModel.blank c) = b.
Proof.
intros E n c b Hn Hc H. rewrite branch_eq_U, !U_SAlu, !U_lit, (U_atom E n c Hn) in H by (unfold TR_MASK; lia).
cbn [zalu_raw] in H. unfold TR_MASK in H.
assert (Hs : 0 <= Z.shiftr 4294976000 (Z.land c 63) < M64).
{ split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by (apply Z.land_nonneg; lia).
  pose proof (Z.pow_pos_nonneg 2 (Z.land c 63) ltac:(lia) ltac:(apply Z.land_nonneg; lia)).
  pose proof (Z.div_le_upper_bound 4294976000 (2 ^ Z.land c 63) 4294976000 ltac:(lia) ltac:(nia)). unfold M64. lia. }
rewrite (zcanon_id (Z.shiftr _ _)) in H by exact Hs.
assert (Ha : 0 <= Z.land (Z.shiftr 4294976000 (Z.land c 63)) 1 < M64).
{ change (Z.land (Z.shiftr 4294976000 (Z.land c 63)) 1) with (Z.land (Z.shiftr 4294976000 (Z.land c 63)) (Z.ones 1)).
  rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (Z.shiftr 4294976000 (Z.land c 63)) (2 ^ 1) ltac:(lia)). unfold M64. lia. }
rewrite (zcanon_id (Z.land _ _)) in H by exact Ha.
rewrite <- (TrimA.blank_mask_b c Hc). exact H.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition tt_E (regs1 : bvmap 5 word) (C : Z) : env := Eimg (Ereg regs1 [Z_to_bv 64 C]).

Lemma tt_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc S0 e C,
getr regs1 8 = w64 S0 -> getr regs1 10 = w64 (e - 1) -> getr regs1 12 = w64 e ->
getr regs1 13 = w64 32 -> getr regs1 14 = w64 TR_MASK -> getr regs1 18 = w64 SB ->
4096 <= S0 <= 2 ^ 47 - 1 -> 4097 <= e <= 2 ^ 47 - 1 -> 0 <= C <= 255 ->
rdW W memc (e - 1) = Some C ->
st_ok_pi SEGS VAL (tt_E regs1 C) tt_ss (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + TR_TRAIL)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc S0 e C H8 H10 H12 H13 H14 H18 HS0 He HC HrdC.
set (E := tt_E regs1 C).
assert (E8 : ew E 8 = Z_to_bv 64 S0) by (subst E; unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 8 8%bv eq_refl); exact H8).
assert (E10 : ew E 10 = Z_to_bv 64 (e - 1)) by (subst E; unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 10 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 e) by (subst E; unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 12 12%bv eq_refl); exact H12).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (subst E; unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 18 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 C) by (subst E; unfold tt_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
rewrite restrict_mkst_fx. unfold tt_ss. apply pa_entry_st_ok_full.
- unfold tt_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H13] | intros X; discriminate X | cbn [sv_denot]; exact H14].
- vm_compute. reflexivity.
- unfold tt_regions. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E12, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
  destruct (aview_byte SEGS (w_H W) memc (e - 1) C HrdC) as (b & Hb & Hv & _).
  exists b. split.
  + cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
    rewrite !Z.add_0_r, (unsigned_lit_small C), (unsigned_lit_small C) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    subst C. apply Z_to_bv_bv_unsigned.
  + replace (e + -1 + 0) with (e - 1) by lia. exact Hb.
- cbn. tauto.
- split; [|split; exact I].
  cbn [tt_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E8, E10, E12, E18, E32, !unsigned_lit_small by (unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* after a run that writes nothing: the environment agrees with the seed's E0 below 33 (HAE), the memory is memc
   (KM), every byte present in memc is present (KP) *)
Ltac tt_after E0 HAE KM KP :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KPn := fresh "KPn" in
    assert (HAEn : env_agree 33 E0 En) by (env_agree_chain HAE);
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
  end.
Ltac tt_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Lemma tr_trail_ok : TR_FIN_stmt B -> TR_TRAIL_stmt B.
Proof.
intros HFIN. unfold TR_TRAIL_stmt.
intros ly S W regs mem md ch p s regs1 memc mdc j HCX.
pose proof (tr_cx_facts B LAWS ly S W regs mem md ch p s HCX)
  as (HSTR & HADDR & HZONE & HPR & HSB & Hp4096 & Hp47 & Hn32 & HOUT & Hal16 & Hsp0 & Hsp47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_trim = 4128) by reflexivity.
destruct HSTR as ((HZS & NZ) & HTAIL).
pose proof (TrimA.lead_le s NZ) as HLL. pose proof (TrimA.s1_len s NZ) as S1L.
pose proof (TrimA.rtrim_len s NZ) as RTL.
assert (HE : trim_end_addr p s = p + Z.of_nat (seg_spec.trim_lead s) + Z.of_nat (TrimA.te s (length (TrimA.s1_of s))))
  by (unfold trim_end_addr; rewrite RTL; lia).
set (lead := seg_spec.trim_lead s) in *.
set (len1 := length (TrimA.s1_of s)) in *.
revert regs1 memc mdc.
induction j as [|j IH]; intros regs1 memc mdc HMID HRG Hj Hte H8 H10 H12 H13 H14; [lia|].
pose proof HRG as (R2 & R18 & RK).
pose proof HMID as (HJ & KEEP & KPR & _).
(* the byte at e - 1 = p + lead + j *)
pose proof (sa_zs_nth _ p s (lead + j) HZS ltac:(lia)) as V0.
set (C := nth (lead + j) s 0) in *.
assert (VC : rdW W memc (p + Z.of_nat lead + Z.of_nat (Datatypes.S j) - 1) = Some C).
{ replace (p + Z.of_nat lead + Z.of_nat (Datatypes.S j) - 1) with (p + Z.of_nat (lead + j)) by lia.
  rewrite KEEP by lia. exact V0. }
destruct (aview_byte SEGS (w_H W) mem _ _ V0) as (_ & _ & _ & HCr).
assert (TS : TrimA.te s (Datatypes.S j) = if SegModel.blank C then TrimA.te s j else Datatypes.S j)
  by (rewrite TrimA.te_S, (TrimA.s1_nth s j NZ); reflexivity).
(* the seed *)
pose proof (tt_entry W regs1 memc (p + Z.of_nat lead) (p + Z.of_nat lead + Z.of_nat (Datatypes.S j)) C
  H8 H10 H12 H13 H14 R18 ltac:(lia) ltac:(lia) ltac:(lia) VC) as HS.
assert (HEI : img_env VAL A_LIM (tt_E regs1 C)) by (unfold tt_E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg regs1 [Z_to_bv 64 C]) (tt_E regs1 C))
  by (split; [intros n Hn; unfold tt_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E8 : ew (tt_E regs1 C) 8 = Z_to_bv 64 (p + Z.of_nat lead)) by (unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 8 8%bv eq_refl); exact H8).
assert (E10 : ew (tt_E regs1 C) 10 = Z_to_bv 64 (p + Z.of_nat lead + Z.of_nat (Datatypes.S j) - 1))
  by (unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 10 10%bv eq_refl); exact H10).
assert (E12 : ew (tt_E regs1 C) 12 = Z_to_bv 64 (p + Z.of_nat lead + Z.of_nat (Datatypes.S j)))
  by (unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 12 12%bv eq_refl); exact H12).
assert (E18 : ew (tt_E regs1 C) 18 = Z_to_bv 64 SB) by (unfold tt_E; rewrite (ew_Eimg_Ereg_nat regs1 _ 18 18%bv eq_refl); exact R18).
assert (E32 : ew (tt_E regs1 C) 32 = Z_to_bv 64 C) by (unfold tt_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
revert HS HEI HA0 E8 E10 E12 E18 E32. generalize (tt_E regs1 C) as E0. intros E0 HS HEI HA0 E8 E10 E12 E18 E32.
pose proof (env_agree_refl 33 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW W memc a = rdW W memc a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros; assumption).
assert (SHOK : sh_ok SEGS tr_Bx [] E0 (mrestrict (w_H W) memc)) by constructor.
assert (HRA : range_addressable (rdW W memc) SHADOW_OFF p (Z.of_nat (length s) + 1)).
{ apply (range_addressable_kept_win (rdW W mem) (rdW W memc) (spZ regs - STK_trim) (spZ regs)); [exact KEEP | lia | lia | lia |].
  destruct HADDR as (_ & _ & _ & HRA & _). exact HRA. }
(* the exits to FIN: a1 = e' with e' = trim_end_addr p s *)
assert (EXIT : forall regs1' memc' mdc', tr_mid B ly S W regs mem md p s memc' mdc' ->
  (forall r, In r TT_KEPT -> getr regs1' r = getr regs1 r) ->
  getr regs1' 11 = w64 (trim_end_addr p s) ->
  SRr SEGS W (mkCfg (mkst regs1' (Z_to_bv 64 (BASE + TR_FIN)) memc' (seg_rom SEGS)) mdc') (tr_post B regs ly S W mem md p s)).
{ intros regs1' memc' mdc' HM' HK' N11.
  exact (HFIN ly S W regs mem md ch p s regs1' memc' mdc' HCX HM'
    (tr_regs_kept regs regs1 regs1' HRG (fun r Hr => HK' r (tt_kept_incl r Hr)))
    ltac:(rewrite (HK' 8%bv) by (cbn; tauto); exact H8) N11). }
unfold tr_at.
(* 0x89148 .. 0x89160: check 2, the byte, `bltu a3,a5` (c > 32 leaves) *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem]. unfold tr_Bx. rewrite (U_atom _ 18 SB E18), (U_atom _ 10 _ E10) by (unfold SB; lia). rewrite SB_SHADOW_OFF.
  exact (range_addressable_sub _ _ p (Z.of_nat (length s) + 1) (p + Z.of_nat lead + Z.of_nat (Datatypes.S j) - 1) 1 HRA
    ltac:(lia) ltac:(lia)). }
{ tt_awr. }
tt_after E0 HAE KM KP.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* c > 32: not blank, FIN with a1 = a2 = e *)
  pose proof (tr_br_ltu_lit _ 32 _ 32 _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) Hc) as Cgt.
  apply Z.ltb_lt in Cgt. clear Hc.
  assert (BC : SegModel.blank C = false)
    by (destruct (SegModel.blank C) eqn:BC0; [apply TrimA.blank_le32 in BC0; lia | reflexivity]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_FIN. { tt_awr. }
  tt_after E0 HAE KM KP.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TT_KEPT HS (tr_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (11%bv : bv 5) N11. rewrite E12 in N11.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
  apply (EXIT rg mm mdn) end.
  + exact (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ (fun a Ha _ => KM a Ha) (fun a _ Ha _ => KP a Ha)).
  + exact HK.
  + rewrite N11, HE, <- Hte, TS, BC. unfold w64. first [reflexivity | f_equal; lia].
- (* c <= 32: bit c of the mask *)
  pose proof (tr_br_ltu_lit _ 32 _ 32 _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) ltac:(lia) Hc) as Cle.
  apply Z.ltb_ge in Cle. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_TRAIL. { tt_awr. }
  tt_after E0 HAE KM KP.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* the bit is 0: not blank, FIN with a1 = a2 = e *)
    pose proof (tr_br_mask _ 32 C _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as BC.
    apply Bool.negb_true_iff in BC. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_FIN. { tt_awr. }
    tt_after E0 HAE KM KP.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TT_KEPT HS (tr_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (11%bv : bv 5) N11. rewrite E12 in N11.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    apply (EXIT rg mm mdn) end.
    * exact (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ (fun a Ha _ => KM a Ha) (fun a _ Ha _ => KP a Ha)).
    * exact HK.
    * rewrite N11, HE, <- Hte, TS, BC. unfold w64. first [reflexivity | f_equal; lia].
  + (* blank: e steps down; `bltu s0,a1` *)
    pose proof (tr_br_mask _ 32 C _ (tr_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as BC.
    apply Bool.negb_false_iff in BC. clear Hc.
    rewrite TS, BC in Hte.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_TRAIL. { tt_awr. }
    tt_after E0 HAE KM KP.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* s0 < e - 1: the next iteration, at j *)
      pose proof (tr_br_ltu_off _ 8 12 _ _ (-1) _ (tr_ag_ew _ _ _ 8 _ HAE ltac:(lia) E8) (tr_ag_ew _ _ _ 12 _ HAE ltac:(lia) E12)
        ltac:(lia) ltac:(lia) ltac:(lia) Hc) as Hlt.
      apply Z.ltb_lt in Hlt. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_TRAIL. { tt_awr. }
      tt_after E0 HAE KM KP.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TT_KEPT HS (tr_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (10%bv : bv 5) N10. prreg HS (12%bv : bv 5) N12. prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14.
      rewrite E10 in N10. rewrite E12 in N12.
      rewrite unsigned_lit_small in N10 by lia. rewrite unsigned_lit_small in N12 by lia.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      apply (IH rg mm mdn) end.
      -- exact (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ (fun a Ha _ => KM a Ha) (fun a _ Ha _ => KP a Ha)).
      -- exact (tr_regs_kept regs regs1 _ HRG (fun r Hr => HK r (tt_kept_incl r Hr))).
      -- lia.
      -- exact Hte.
      -- rewrite (HK 8%bv) by (cbn; tauto). exact H8.
      -- rewrite N10. unfold w64. first [reflexivity | f_equal; lia].
      -- rewrite N12. unfold w64. first [reflexivity | f_equal; lia].
      -- exact N13.
      -- exact N14.
    * (* e - 1 = s0: j = 0, FIN with a1 = s0 *)
      pose proof (tr_br_ltu_off _ 8 12 _ _ (-1) _ (tr_ag_ew _ _ _ 8 _ HAE ltac:(lia) E8) (tr_ag_ew _ _ _ 12 _ HAE ltac:(lia) E12)
        ltac:(lia) ltac:(lia) ltac:(lia) Hc) as Hge.
      apply Z.ltb_ge in Hge. clear Hc.
      assert (Ej : j = 0%nat) by lia. subst j.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan TR_FIN. { tt_awr. }
      tt_after E0 HAE KM KP.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ TT_KEPT HS (tr_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (11%bv : bv 5) N11. rewrite E12 in N11. rewrite unsigned_lit_small in N11 by lia.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      apply (EXIT rg mm mdn) end.
      -- exact (tr_mid_step B ly S W regs mem md p s memc mdc _ _ HMID ltac:(lia) HJ (fun a Ha _ => KM a Ha) (fun a _ Ha _ => KP a Ha)).
      -- exact HK.
      -- rewrite N11, HE, <- Hte, TrimA.te_0. unfold w64. first [reflexivity | f_equal; lia].
Qed.

End e.
End f.
End d.
