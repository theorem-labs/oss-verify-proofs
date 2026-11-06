(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 211 of its 238 lines of code are new or changed and 1251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeShort.v, with its module paths and module names changed; 530 of its 563 lines of code are new or changed and 205 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC1h YC1i YC88 YI67 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonJs DiscoArm3JsonK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb slot_ser_Pq.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition C3_RET : Z := 0x15b4.
Definition C3_PMAX : Z := 140737479966720.
Definition C3_BX : sv := SOff 19 0.
Definition c3_alias : sv * sv := (SAlu ALU_ADD (SOff 24 0) (SOff 21 0), SOff 33 0).
Definition c3_atomsC : list (nat * afact) :=
  [(19%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (20%nat, mkAF 32 32 0); (21%nat, mkAF 0 969 0);
   (24%nat, mkAF 4096 C3_PMAX 0); (25%nat, mkAF (2 ^ 64 - 1 - C3_PMAX) (2 ^ 64 - 1 - 4096) 0);
   (33%nat, mkAF 4096 C3_PMAX 0); (34%nat, mkAF 33 255 0)].
Definition c3_atomsB : list (nat * afact) :=
  [(19%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (21%nat, mkAF 0 969 0);
   (24%nat, mkAF 4096 C3_PMAX 0); (33%nat, mkAF 4096 C3_PMAX 0)].
Definition c3_lt : acond := mkAC BC_LTU (SOff 21 0) (SOff 26 0).
Definition c3_lt1 : acond := mkAC BC_LTU (SOff 21 1) (SOff 26 0).
Definition c3_nz : acond := mkAC BC_NE (SOff 10 0) (SLit 0).
Definition c3_regC : smem :=
  [YP09.mkRegion (Some 33%nat) 0 2 0 0
     [YP09.mkChunk 0 (CVal 1 (SLit 44)); YP09.mkChunk 1 (CVal 1 (SOff 34 0))]].
Definition c3_regB : smem :=
  [YP09.mkRegion (Some 9%nat) 352 360 0 0 [YP09.mkChunk 352 (CVal 8 (SOff 34 0))];
   YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 125))]].
Definition c3_ssC : sstate := mkSS SLOT_OFF sr_atoms c3_regC None (mkFacts c3_atomsC [c3_lt1; c3_lt] [c3_alias]).
Definition c3_ssB : sstate := mkSS SLOT_OFF sr_atoms c3_regB None (mkFacts c3_atomsB [c3_lt] [c3_alias]).
Definition c3_ssR : sstate := mkSS C3_RET sr_atoms [] None (mkFacts [] [c3_nz] []).
Definition c3_SHC : list shent := [mkSHE 33 0 2].
Definition c3_SHB : list shent := [mkSHE 33 0 1].

Lemma c3_oo : forall (fb a s stk : Z) (nn : nat),
  4096 <= fb -> fb + 4096 <= a - stk -> 0 <= stk -> a + 472 <= s -> s <= 2 ^ 47 -> (nn <= 9)%nat ->
  fb + 240 + 144 * Z.of_nat nn <= 2 ^ 64 /\
  (forall x, fb + 240 <= x < fb + 240 + 144 * Z.of_nat nn ->
     ~ (a - stk <= x < a \/ a + 448 <= x < a + 448 + 20)).
Proof.
  intros fb a s stk nn H1 H2 H3 H4 H5 H6.
  assert (Hn : Z.of_nat nn <= 9) by lia.
  pose proof (Nat2Z.is_nonneg nn) as Hn0.
  split; [lia|]. intros x Hx [Hq|Hq]; lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis JSC : jsc_step_stmt B MT XM_LIB RLO RHI tfib_K.

Lemma c3_shent : forall ly S (W : world SEGS) mem md (E : env) (q : nat) (bp len lo hi : Z),
  AR SEGS B ly S W mem md -> In (bp, len) (ablocks B ly S) ->
  U E C3_BX = SHADOW_OFF -> 0 <= lo <= hi ->
  bp <= U E (SOff q 0) + lo -> U E (SOff q 0) + hi <= bp + req_size len ->
  shent_ok SEGS C3_BX E (rd W mem) (mkSHE q lo hi).
Proof.
  intros ly S W mem md E q bp len lo hi HAR Hin HB Hlh Hlo Hhi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & _).
  eapply (shent_ok_of_range SEGS (w_H W) mem E C3_BX q bp (req_size len) (U E (SOff q 0)) lo hi).
  - exact (range_addressable_of_block SEGS B LAWS ly S W mem md bp len bp (req_size len) HAR Hin
             ltac:(lia) ltac:(lia)).
  - exact HB.
  - reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

Theorem a3j_C3 : jseg_C3 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin ip t c2 count acc vpad W cf HIN.
unfold jslot_in, jcut, d_arm_at_pf, d_at in HIN.
destruct HIN as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc0 & Hcf & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev &
  HMO & Hacc & Hi & Hn & Hnow & HRL & (R26 & R24 & R25 & R21 & R22 & R23) &
  (HSP1 & HTAB & HBUF & HXS) & HSP0 & HBODY).
subst cf.
destruct HXS as (HFIN & Hipt & Hcount & Hlacc & HCONT & Hlc2 & HFAc2 & HMEM & HSL).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs3 & Rs2 & Rs4 & Rs11).
pose proof HFIN as (HJR & Hfinb & HNOWS & HTLEN & HTOKS).
pose proof HBUF as (Hcap & HGARR).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof ASAN_CEIL_range as (Hceil1 & _). unfold ASAN_CEIL in Hceil1.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBODY as (Tb & Gb & Lkb & Hb & HFRM & HSHD & HOBJ & HBLK & _).
pose proof HBLK as (HPerm0 & _ & _ & _).
assert (Hinbuf : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinbuf) as (Hbuf16 & Hbuf4096 & Hbufceil & Hbufapp & _ & _ & _).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia. }
rewrite Hreq in Hbufceil, Hbufapp.
assert (Hrle : a3_r T1 now <= 969) by (unfold a3_r; lia).
assert (Hcnt7 : count <= 7).
{ destruct HCONT as (f0 & i20 & c20 & _ & HA0).
  pose proof (jobjs_after_count (a3_text T1 now) fin i20 count acc c20 HA0). lia. }
assert (Hlobjs : (length (acc ++ [c2]) <= 9)%nat).
{ rewrite length_app, Hlacc. cbn [length]. lia. }
pose proof (jpairs_cont_step (a3_text T1 now) fin t c2 count acc HCONT) as HSTEP.
destruct HSTEP as [(Hc44 & HFROMP) | (Hc44f & Hc125 & HAFTER)].
-
  pose proof (at_byte_true _ _ _ Hc44) as (Hlt44 & Hby44).
  assert (Ht0 : 0 <= t) by lia.
  assert (Hrt : t < a3_r T1 now) by (unfold a3_r, jlen in *; lia).
  rewrite (json_ws_id (a3_text T1 now) (t + 1) HNOWS ltac:(lia)) in HFROMP.
  pose proof (jpairs_from_step (a3_text T1 now) fin (t + 1) c2 count acc HFROMP)
    as (jj & kk & ks & kl & j2 & vk & vs & vl & cnew & HJS & Hkk1 & Hcolon & HJS2 & Hupd & HCONT2).
  assert (Hjgt : t + 1 < jj) by exact (jscalar_lt (a3_text T1 now) (t + 1) jj kk ks kl ltac:(lia) HJS).
  rewrite (json_ws_id (a3_text T1 now) jj HNOWS ltac:(lia)) in Hcolon.
  assert (Hjjr : jj < a3_r T1 now)
    by (pose proof (at_byte_true _ _ _ Hcolon) as (Hq & _); unfold a3_r, jlen in *; lia).
  pose proof (jscalar_in (a3_text T1 now) (t + 1) jj kk ks kl HJS) as Ht1r.
  assert (Ht1r' : t + 1 < a3_r T1 now) by (unfold a3_r, jlen in *; lia).
  assert (Hb1 : 33 <= jbyte (a3_text T1 now) (t + 1) <= 255)
    by (apply jno_ws_byte; [exact HNOWS | unfold jlen, a3_r in *; lia]).
  remember (Eimg (Ereg regs [w64 SHADOW_OFF; w64 (buf + t); w64 (jbyte (a3_text T1 now) (t + 1))])) as E0 eqn:HE0.
  assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
  assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
    by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (ENP : ew E0 33 = w64 (buf + t)).
  { rewrite HE0, Eimg_low by (unfold A_TEXT; lia).
    change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. }
  assert (ENB : ew E0 34 = w64 (jbyte (a3_text T1 now) (t + 1))).
  { rewrite HE0, Eimg_low by (unfold A_TEXT; lia).
    change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. reflexivity. }
  assert (U9 : bv_unsigned (ew E0 9) = d_A cx).
  { rewrite (EE0 9%nat 9%bv eq_refl), Rs1. unfold w64. apply unsigned_lit_small. lia. }
  assert (V19 : bv_unsigned (ew E0 19) = SHADOW_OFF).
  { rewrite (EE0 19%nat 19%bv eq_refl), Rs3. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
  assert (V20 : bv_unsigned (ew E0 20) = 32).
  { rewrite (EE0 20%nat 20%bv eq_refl), Rs4. unfold w64. apply unsigned_lit_small. lia. }
  assert (V21 : bv_unsigned (ew E0 21) = t).
  { rewrite (EE0 21%nat 21%bv eq_refl), R21. unfold w64. apply unsigned_lit_small. lia. }
  assert (V24 : bv_unsigned (ew E0 24) = buf).
  { rewrite (EE0 24%nat 24%bv eq_refl), R24. unfold w64. apply unsigned_lit_small. lia. }
  assert (V25 : bv_unsigned (ew E0 25) = 2 ^ 64 - 1 - buf).
  { rewrite (EE0 25%nat 25%bv eq_refl), R25, jk_lnot by lia. apply unsigned_lit_small. lia. }
  assert (V26 : bv_unsigned (ew E0 26) = a3_r T1 now).
  { rewrite (EE0 26%nat 26%bv eq_refl), R26. unfold w64. apply unsigned_lit_small. lia. }
  assert (V33 : bv_unsigned (ew E0 33) = buf + t) by (rewrite ENP; unfold w64; apply unsigned_lit_small; lia).
  assert (V34 : bv_unsigned (ew E0 34) = jbyte (a3_text T1 now) (t + 1))
    by (rewrite ENB; unfold w64; apply unsigned_lit_small; lia).
  assert (U19 : U E0 C3_BX = SHADOW_OFF).
  { unfold C3_BX. rewrite U_SOff, V19, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia. }
  assert (U21 : U E0 (SOff 21 0) = t) by (rewrite U_SOff, V21, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  assert (U211 : U E0 (SOff 21 1) = t + 1) by (rewrite U_SOff, V21; apply zcanon_id; unfold M64; lia).
  assert (U26 : U E0 (SOff 26 0) = a3_r T1 now) by (rewrite U_SOff, V26, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  assert (UNP : U E0 (SOff 33 0) = buf + t) by (rewrite U_SOff, V33, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  assert (HG : facts_ok E0 (mkFacts c3_atomsC [c3_lt1; c3_lt] [c3_alias])).
  { unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
    - unfold c3_atomsC. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite V19, V20, V21, V24, V25, V33, V34.
      rewrite Z.pow_0_r, !Z.mod_1_r. unfold C3_PMAX, SHADOW_OFF in *.
      repeat split; lia.
    - cbn [conds_ok]. unfold c3_lt1, c3_lt, acond_ok. cbn [ac_c ac_a ac_b].
      rewrite !branch_ltu_U. rewrite U211, U21, U26.
      split; [apply Z.ltb_lt; lia|]. split; [apply Z.ltb_lt; lia | exact I].
    - unfold c3_alias. cbn [alias_ok]. split; [|exact I].
      apply U_inj. rewrite (U_add_off_atom E0 24 0 21 0 ltac:(unfold M64; lia) ltac:(unfold M64; lia)).
      rewrite V24, V21, UNP. lia. }
  assert (HROK : Forall (region_ok SEGS E0 (rd W mem3)) c3_regC).
  { constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite V33.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    destruct (jk_byte W mem3 buf (a3_text T1 now ++ [0]) t HGARR ltac:(rewrite length_app; cbn [length]; unfold a3_r in *; lia))
      as (Hv0 & _).
    destruct (jk_byte W mem3 buf (a3_text T1 now ++ [0]) (t + 1) HGARR
      ltac:(rewrite length_app; cbn [length]; unfold a3_r in *; lia)) as (Hv1 & _).
    rewrite (jk_nth_app (a3_text T1 now) t ltac:(unfold jlen, a3_r in *; lia)) in Hv0.
    rewrite (jk_nth_app (a3_text T1 now) (t + 1) ltac:(unfold jlen, a3_r in *; lia)) in Hv1.
    rewrite Hby44 in Hv0.
    constructor; [|constructor; [|constructor]].
    - apply (chunk_ok_val SEGS E0 _ (buf + t) 0 1 (SLit 44) 44).
      + cbn [sv_denot]. reflexivity.
      + cbn [Z.of_N]. lia.
      + cbn [Z.of_N]. lia.
      + cbn [N.to_nat]. replace (buf + t + 0) with (buf + t) by lia. exact Hv0.
    - apply (chunk_ok_val SEGS E0 _ (buf + t) 1 1 (SOff 34 0) (jbyte (a3_text T1 now) (t + 1))).
      + cbn [sv_denot]. rewrite V34, Z.add_0_r. reflexivity.
      + cbn [Z.of_N]. lia.
      + cbn [Z.of_N]. lia.
      + cbn [N.to_nat]. replace (buf + t + 1) with (buf + (t + 1)) by lia. exact Hv1. }
  assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 c3_ssC
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + SLOT_OFF)) mem3 (YK11.seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE0. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - exact HROK.
    - cbn [pairwise_disjoint all_disjoint c3_regC]. split; exact I.
    - exact HG. }
  assert (SHOK : sh_ok SEGS C3_BX c3_SHC E0 (rd W mem3)).
  { unfold c3_SHC. constructor; [|constructor].
    apply (c3_shent ly3 S3 W mem3 md3 E0 33%nat buf (Z.max (slot_ser_defs.ser_cap op) 1) 0 2 HAR3 Hinbuf);
      [exact U19 | lia | rewrite UNP; lia | rewrite UNP, Hreq; lia]. }
  unfold cfg_at, w64.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?E ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' a1 b1 c1 d1 e1 f1 g1) end.
    intros a Ha. exfalso. revert Ha. apply jk_nowin. vm_compute. reflexivity. }
  assert (Emem : ms_mem ms = mem3).
  { apply functional_extensionality. intros x. apply HF.
    apply jk_nowin. vm_compute. reflexivity. }
  rewrite Emem in HJ.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  rewrite (EE0 2%nat 2%bv eq_refl) in Q2.
  rewrite (EE0 3%nat 3%bv eq_refl) in Q3.
  rewrite (EE0 4%nat 4%bv eq_refl) in Q4.
  rewrite (EE0 8%nat 8%bv eq_refl) in Q8.
  rewrite (EE0 9%nat 9%bv eq_refl) in Q9.
  rewrite (EE0 24%nat 24%bv eq_refl) in Q10.
  rewrite V21 in Q11.
  rewrite (EE0 26%nat 26%bv eq_refl) in Q12.
  rewrite U9 in Q13.
  rewrite (EE0 18%nat 18%bv eq_refl) in Q18.
  rewrite (EE0 19%nat 19%bv eq_refl) in Q19.
  rewrite (EE0 20%nat 20%bv eq_refl) in Q20.
  rewrite (EE0 22%nat 22%bv eq_refl) in Q22.
  rewrite (EE0 23%nat 23%bv eq_refl) in Q23.
  rewrite (EE0 24%nat 24%bv eq_refl) in Q24.
  rewrite (EE0 25%nat 25%bv eq_refl) in Q25.
  rewrite (EE0 26%nat 26%bv eq_refl) in Q26.
  rewrite (EE0 27%nat 27%bv eq_refl) in Q27.
  pmkst HS.
  rewrite Emem, pa_sigma_json_scalar.
  eapply SRr_bind.
  { eapply (JSC cx h i n now op W0 c0 T0 T1 buf dsh_scr C3_RET (t + 1) 448 jj kk ks kl
      (fun rg => getr rg 22 = w64 (jcur cx count mod 8) /\ getr rg 23 = w64 (jcur cx count))
      (fun Wx mx => jmem cx buf count vpad (acc ++ [c2]) Wx mx /\ jslots cx count Wx mx) W _).
    - unfold C3_RET. lia.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - exact HJS.
    - intros rg rg' HP (A22 & A23).
      assert (P22 : getr rg' 22 = getr rg 22) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
      assert (P23 : getr rg' 23 = getr rg 23) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
      rewrite P22, P23. split; [exact A22 | exact A23].
    - intros W1 m1 W2 m2 (HM1 & HS1) (K1 & K2 & K3 & K4 & HK).
      destruct HM1 as (Mpl & Mpad & MOO & MF6).
      destruct HS1 as (S408 & S368 & S360 & S328 & S296 & S352).
      assert (KV : forall off v, 0 <= off -> off + 8 <= 448 ->
        val_mem SEGS (rd W1 m1) (d_A cx + off) 8 v -> val_mem SEGS (rd W2 m2) (d_A cx + off) 8 v).
      { intros off v H1 H2 Hv.
        apply (jk_val_mem_kept _ W1 m1 W2 m2 (d_A cx + off) 8%nat v HK ltac:(lia)
                 ltac:(cbn [Z.of_nat]; lia)); [|exact Hv].
        intros x Hx. cbn [Z.of_nat] in Hx. intros [Hq|Hq]; lia. }
      split.
      + split; [exact Mpl|].
        split; [|split].
        * apply (jk_garr8_kept _ W1 m1 W2 m2 (d_A cx + 444)
                   (map (fun b : byte => bv_unsigned b) vpad) HK ltac:(lia)).
          -- rewrite length_map, Mpl. cbn [Z.of_nat]. lia.
          -- intros x Hx. rewrite length_map, Mpl in Hx. cbn [Z.of_nat] in Hx.
             intros [Hq|Hq]; lia.
          -- exact Mpad.
        * destruct (c3_oo (d_FB cx) (d_A cx) (d_S cx) TJSON_SCALAR_STK (length (acc ++ [c2]))
                      K1 K2 ltac:(unfold TJSON_SCALAR_STK, ESTACK; lia) K3 K4 Hlobjs) as (HOO1 & HOO2).
          apply (jk_garr8_kept _ W1 m1 W2 m2 (d_obj cx OO)
                   (map (fun b : byte => bv_unsigned b)
                      (slot_ser_defs.objs_bytes buf vpad (acc ++ [c2]))) HK
                   ltac:(unfold d_obj; cbn [dobj_off]; lia)).
          -- rewrite length_map. unfold d_obj. cbn [dobj_off].
             rewrite (slot_ser_Pq.objs_len buf vpad (acc ++ [c2]) Mpl MF6), Nat2Z.inj_mul.
             change (Z.of_nat 144) with 144. exact HOO1.
          -- intros x Hx. rewrite length_map in Hx.
             rewrite (slot_ser_Pq.objs_len buf vpad (acc ++ [c2]) Mpl MF6), Nat2Z.inj_mul in Hx.
             change (Z.of_nat 144) with 144 in Hx.
             unfold d_obj in *. cbn [dobj_off] in *. exact (HOO2 x Hx).
          -- exact MOO.
        * exact MF6.
      + split; [exact (KV 408 _ ltac:(lia) ltac:(lia) S408)|].
        split; [exact (KV 368 _ ltac:(lia) ltac:(lia) S368)|].
        split; [exact (KV 360 _ ltac:(lia) ltac:(lia) S360)|].
        split; [exact (KV 328 _ ltac:(lia) ltac:(lia) S328)|].
        split; [exact (KV 296 _ ltac:(lia) ltac:(lia) S296)|].
        exact (KV 352 _ ltac:(lia) ltac:(lia) S352).
    - unfold jsc_in, jcut. split; [exact HFROM|].
      unfold d_arm_at_pf, d_at.
      exists fq, ly3, S3, (ms_regs ms), mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, acc0.
      split; [unfold cfg_at, w64; rewrite <- Emem; reflexivity|].
      split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|].
      split; [exact Hk|]. split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
      split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
      split.
      { split; [unfold spZ; rewrite Q2; exact Rsp|].
        split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
        split; [rewrite Q9; exact Rs1|]. split; [rewrite Q19; exact Rs3|]. split; [rewrite Q18; exact Rs2|].
        split; [rewrite Q20; exact Rs4|].
        rewrite Q27; exact Rs11. }
      split.
      { split; [rewrite Q26; exact R26|]. split; [rewrite Q24; exact R24|]. split; [rewrite Q25; exact R25|].
        split; [unfold w64, C3_RET; exact Q1|].
        split; [rewrite Q10; exact R24|].
        split; [unfold w64; exact Q11|].
        split; [rewrite Q12; exact R26|].
        split; [unfold w64; exact Q13|].
        split; [rewrite Q22; exact R22 | rewrite Q23; exact R23]. }
      split.
      { split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|].
        split; [exact HMEM | exact HSL]. }
      split; [exact HSP0 | exact HBODY]. }
  cbv beta. intros W4 cfg4 HW4 HOUT.
  unfold jsc_out, jcut, d_arm_at_pf, d_at in HOUT.
  destruct HOUT as (HFROM4 & fq4 & ly4 & S4 & regs4 & mem4 & md4 & k4 & acc4 & Hcfg4 & Hfrm04 & HBASE4 & HJ4 & HFR4 &
    Hk4 &
    Hnev4 & HMO4 & Hacc4 & Hi4 & Hn4 & Hnow4 & HRL4 & (R26' & R24' & R25' & R10' & R22' & R23') &
    (HSP1' & HTAB' & HBUF' & (HMEM' & HSL') & V448 & V456 & V464) & HSP0' & HBODY4).
  subst cfg4.
  pose proof HRL4 as (Rsp4 & Rgp4 & Rtp4 & Rs04 & Rs14 & Rs34 & Rs24 & Rs44 & Rs114).
  assert (Hj0 : 0 < jj) by lia.
  assert (Hjj64 : jj < 2 ^ 64) by lia.
  remember (Eimg (Ereg regs4 [])) as E1 eqn:HE1.
  assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply Eimg_env).
  assert (EE1 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E1 nn = getr regs4 r)
    by (intros nn r Hr; rewrite HE1; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (HG1 : facts_ok E1 (mkFacts [] [c3_nz] [])).
  { unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [exact I|]. split; [|exact I].
    cbn [conds_ok]. unfold c3_nz, acond_ok. cbn [ac_c ac_a ac_b]. split; [|exact I].
    rewrite branch_ne_U, U_lit by lia.
    rewrite (U_atom E1 10%nat jj ltac:(rewrite (EE1 10%nat 10%bv eq_refl); exact R10') ltac:(lia)).
    apply negb_true_iff. apply Z.eqb_neq. lia. }
  assert (HS1 : st_ok_pi (fx := fq4) SEGS VAL E1 c3_ssR
    (restrict (w_H W4) (YK11.mkst (fx := fq4) regs4 (Z_to_bv 64 (BASE + C3_RET)) mem4 (YK11.seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE1. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - exact HG1. }
  pose proof (paj_run_to (fx := fq4) (PI := PI) B LAWS) as RUNTO4.
  assert (SHOK1 : sh_ok SEGS C3_BX (@nil shent) E1 (rd W4 mem4)) by constructor.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO4 HS1 HJ4 SHOK1 Bspan PAIR_OFF.
  { lazymatch goal with |- awr_ok ?E ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' a1 b1 c1 d1 e1 f1 g1) end.
    apply awr_ok_nil. }
  assert (Emem4 : ms_mem ms0 = mem4).
  { apply functional_extensionality. intros x. apply HF0.
    apply jk_nowin. vm_compute. reflexivity. }
  rewrite Emem4 in HJ4.
  prreg HS1 (2%bv : bv 5) P2. prreg HS1 (3%bv : bv 5) P3. prreg HS1 (4%bv : bv 5) P4.
  prreg HS1 (8%bv : bv 5) P8. prreg HS1 (9%bv : bv 5) P9. prreg HS1 (10%bv : bv 5) P10.
  prreg HS1 (18%bv : bv 5) P18. prreg HS1 (19%bv : bv 5) P19. prreg HS1 (20%bv : bv 5) P20.
  prreg HS1 (22%bv : bv 5) P22. prreg HS1 (23%bv : bv 5) P23. prreg HS1 (24%bv : bv 5) P24.
  prreg HS1 (25%bv : bv 5) P25. prreg HS1 (26%bv : bv 5) P26. prreg HS1 (27%bv : bv 5) P27.
  rewrite (EE1 2%nat 2%bv eq_refl) in P2. rewrite (EE1 3%nat 3%bv eq_refl) in P3.
  rewrite (EE1 4%nat 4%bv eq_refl) in P4. rewrite (EE1 8%nat 8%bv eq_refl) in P8.
  rewrite (EE1 9%nat 9%bv eq_refl) in P9. rewrite (EE1 10%nat 10%bv eq_refl) in P10.
  rewrite (EE1 18%nat 18%bv eq_refl) in P18. rewrite (EE1 19%nat 19%bv eq_refl) in P19.
  rewrite (EE1 20%nat 20%bv eq_refl) in P20. rewrite (EE1 22%nat 22%bv eq_refl) in P22.
  rewrite (EE1 23%nat 23%bv eq_refl) in P23. rewrite (EE1 24%nat 24%bv eq_refl) in P24.
  rewrite (EE1 25%nat 25%bv eq_refl) in P25. rewrite (EE1 26%nat 26%bv eq_refl) in P26.
  rewrite (EE1 27%nat 27%bv eq_refl) in P27.
  pmkst HS1. rewrite Emem4.
  apply SRr_ret. left.
  exists (t + 1), jj, kk, ks, kl. split; [lia|].
  unfold jpair_in, jcut. split; [exact HFROM4|].
  unfold d_arm_at_pf, d_at.
  exists fq4, ly4, S4, (ms_regs ms0), mem4, (with_vm_backing (m_vm_lazy md4) mat0 md4), k4, acc4.
  split; [unfold cfg_at, w64; rewrite <- Emem4; reflexivity|].
  split; [exact Hfrm04|]. split; [exact HBASE4|]. split; [exact HJ4|]. split; [exact HFR4|].
  split; [exact Hk4|]. split; [exact Hnev4|]. split; [exact HMO4|]. split; [exact Hacc4|].
  split; [exact Hi4|]. split; [exact Hn4|]. split; [exact Hnow4|].
  split.
  { split; [unfold spZ; rewrite P2; exact Rsp4|].
    split; [rewrite P3; exact Rgp4|]. split; [rewrite P4; exact Rtp4|]. split; [rewrite P8; exact Rs04|].
    split; [rewrite P9; exact Rs14|]. split; [rewrite P19; exact Rs34|]. split; [rewrite P18; exact Rs24|].
    split; [rewrite P20; exact Rs44|].
    rewrite P27; exact Rs114. }
  split.
  { split; [rewrite P26; exact R26'|]. split; [rewrite P24; exact R24'|]. split; [rewrite P25; exact R25'|].
    split; [rewrite P10; exact R10'|].
    split; [rewrite P22; exact R22' | rewrite P23; exact R23']. }
  split.
  { split; [exact HSP1'|]. split; [exact HTAB'|]. split; [exact HBUF'|].
    split; [exact HFIN|]. split; [lia|]. split; [exact Hcount|]. split; [exact Hlacc|].
    split; [exact HJS|]. split; [exact HFROMP|]. split; [exact Hlc2|]. split; [exact HFAc2|].
    split; [exact HMEM'|]. split; [exact HSL'|].
    split; [exact V448|].
    split; [replace (d_A cx + 456) with (d_A cx + 448 + 8) by lia; exact V456|].
    replace (d_A cx + 464) with (d_A cx + 448 + 16) by lia; exact V464. }
  split; [exact HSP0' | exact HBODY4].
-
  pose proof (at_byte_true _ _ _ Hc125) as (Hlt125 & Hby125).
  assert (Ht0 : 0 <= t) by lia.
  assert (Hrt : t < a3_r T1 now) by (unfold a3_r, jlen in *; lia).
  remember (Eimg (Ereg regs [w64 SHADOW_OFF; w64 (buf + t); w64 count])) as E0 eqn:HE0.
  assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
  assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
    by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (ENP : ew E0 33 = w64 (buf + t)).
  { rewrite HE0, Eimg_low by (unfold A_TEXT; lia).
    change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. }
  assert (ENC : ew E0 34 = w64 count).
  { rewrite HE0, Eimg_low by (unfold A_TEXT; lia).
    change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. reflexivity. }
  assert (U9 : bv_unsigned (ew E0 9) = d_A cx).
  { rewrite (EE0 9%nat 9%bv eq_refl), Rs1. unfold w64. apply unsigned_lit_small. lia. }
  assert (V19 : bv_unsigned (ew E0 19) = SHADOW_OFF).
  { rewrite (EE0 19%nat 19%bv eq_refl), Rs3. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
  assert (V21 : bv_unsigned (ew E0 21) = t).
  { rewrite (EE0 21%nat 21%bv eq_refl), R21. unfold w64. apply unsigned_lit_small. lia. }
  assert (V24 : bv_unsigned (ew E0 24) = buf).
  { rewrite (EE0 24%nat 24%bv eq_refl), R24. unfold w64. apply unsigned_lit_small. lia. }
  assert (V26 : bv_unsigned (ew E0 26) = a3_r T1 now).
  { rewrite (EE0 26%nat 26%bv eq_refl), R26. unfold w64. apply unsigned_lit_small. lia. }
  assert (V33 : bv_unsigned (ew E0 33) = buf + t) by (rewrite ENP; unfold w64; apply unsigned_lit_small; lia).
  assert (V34 : bv_unsigned (ew E0 34) = count) by (rewrite ENC; unfold w64; apply unsigned_lit_small; lia).
  assert (U19 : U E0 C3_BX = SHADOW_OFF).
  { unfold C3_BX. rewrite U_SOff, V19, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia. }
  assert (U21 : U E0 (SOff 21 0) = t) by (rewrite U_SOff, V21, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  assert (U26 : U E0 (SOff 26 0) = a3_r T1 now) by (rewrite U_SOff, V26, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  assert (UNP : U E0 (SOff 33 0) = buf + t) by (rewrite U_SOff, V33, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  assert (HG : facts_ok E0 (mkFacts c3_atomsB [c3_lt] [c3_alias])).
  { unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
    - unfold c3_atomsB. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite V19, V21, V24, V33.
      rewrite Z.pow_0_r, !Z.mod_1_r. unfold C3_PMAX, SHADOW_OFF in *.
      repeat split; lia.
    - cbn [conds_ok]. unfold c3_lt, acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_ltu_U, U21, U26. split; [apply Z.ltb_lt; lia | exact I].
    - unfold c3_alias. cbn [alias_ok]. split; [|exact I].
      apply U_inj. rewrite (U_add_off_atom E0 24 0 21 0 ltac:(unfold M64; lia) ltac:(unfold M64; lia)).
      rewrite V24, V21, UNP. lia. }
  pose proof HSL as (S408 & S368 & S360 & S328 & S296 & S352).
  assert (HROK : Forall (region_ok SEGS E0 (rd W mem3)) c3_regB).
  { constructor; [|constructor; [|constructor]].
    - unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E0 _ (d_A cx) 352 8 (SOff 34 0) count).
      + cbn [sv_denot]. rewrite V34, Z.add_0_r. reflexivity.
      + cbn [Z.of_N]. lia.
      + cbn [Z.of_N]. lia.
      + cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact S352.
    - unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite V33.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      destruct (jk_byte W mem3 buf (a3_text T1 now ++ [0]) t HGARR
        ltac:(rewrite length_app; cbn [length]; unfold a3_r in *; lia)) as (Hv0 & _).
      rewrite (jk_nth_app (a3_text T1 now) t ltac:(unfold jlen, a3_r in *; lia)) in Hv0. rewrite Hby125 in Hv0.
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E0 _ (buf + t) 0 1 (SLit 125) 125).
      + cbn [sv_denot]. reflexivity.
      + cbn [Z.of_N]. lia.
      + cbn [Z.of_N]. lia.
      + cbn [N.to_nat]. replace (buf + t + 0) with (buf + t) by lia. exact Hv0. }
  assert (HPD : pairwise_disjoint E0 c3_regB).
  { cbn [pairwise_disjoint all_disjoint c3_regB]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, V33.
    split; [split; [right; lia | exact I] | split; [exact I | exact I]]. }
  assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 c3_ssB
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + SLOT_OFF)) mem3 (YK11.seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE0. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - exact HROK.
    - exact HPD.
    - exact HG. }
  assert (SHOK : sh_ok SEGS C3_BX c3_SHB E0 (rd W mem3)).
  { unfold c3_SHB. constructor; [|constructor].
    apply (c3_shent ly3 S3 W mem3 md3 E0 33%nat buf (Z.max (slot_ser_defs.ser_cap op) 1) 0 1 HAR3 Hinbuf);
      [exact U19 | lia | rewrite UNP; lia | rewrite UNP, Hreq; lia]. }
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan OEND_OFF.
  { lazymatch goal with |- awr_ok ?E ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' a1 b1 c1 d1 e1 f1 g1) end.
    intros a Ha. exfalso. revert Ha. apply jk_nowin. vm_compute. reflexivity. }
  assert (Emem : ms_mem ms = mem3).
  { apply functional_extensionality. intros x. apply HF.
    apply jk_nowin. vm_compute. reflexivity. }
  rewrite Emem in HJ.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  rewrite (EE0 2%nat 2%bv eq_refl) in Q2.
  rewrite (EE0 3%nat 3%bv eq_refl) in Q3.
  rewrite (EE0 4%nat 4%bv eq_refl) in Q4.
  rewrite (EE0 8%nat 8%bv eq_refl) in Q8.
  rewrite (EE0 9%nat 9%bv eq_refl) in Q9.
  rewrite (EE0 18%nat 18%bv eq_refl) in Q18.
  rewrite (EE0 19%nat 19%bv eq_refl) in Q19.
  rewrite (EE0 20%nat 20%bv eq_refl) in Q20.
  rewrite (EE0 21%nat 21%bv eq_refl) in Q21.
  rewrite ENC in Q22.
  rewrite (EE0 24%nat 24%bv eq_refl) in Q24.
  rewrite (EE0 25%nat 25%bv eq_refl) in Q25.
  rewrite (EE0 26%nat 26%bv eq_refl) in Q26.
  rewrite (EE0 27%nat 27%bv eq_refl) in Q27.
  pmkst HS. rewrite Emem.
  apply SRr_ret. right.
  exists t. split; [lia|].
  unfold joend_in, jcut. split; [exact HFROM|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms), mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, acc0.
  split; [unfold cfg_at, w64; rewrite <- Emem; reflexivity|].
  split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|].
  split; [exact Hk|]. split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { split; [unfold spZ; rewrite Q2; exact Rsp|].
    split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
    split; [rewrite Q9; exact Rs1|]. split; [rewrite Q19; exact Rs3|]. split; [rewrite Q18; exact Rs2|].
    split; [rewrite Q20; exact Rs4|].
    rewrite Q27; exact Rs11. }
  split.
  { split; [rewrite Q26; exact R26|]. split; [rewrite Q24; exact R24|]. split; [rewrite Q25; exact R25|].
    split; [rewrite Q21; exact R21 | exact Q22]. }
  split.
  { split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|].
    split; [exact HFIN|]. split; [lia|]. split; [exact Hcount|]. split; [exact Hlacc|].
    split; [exact Hc125|]. split; [exact HAFTER|]. split; [exact Hlc2|]. split; [exact HFAc2|]. exact HMEM. }
  split; [exact HSP0 | exact HBODY].
Qed.

End h.
End f.
End d.
