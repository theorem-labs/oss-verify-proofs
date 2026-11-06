(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module names changed; 493 of its 540 lines of code are new or changed and 449 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC81 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonJs JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb slot_ser_Pq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition C3_RET : Z := 0x1420.
Definition C3_NP : nat := 33%nat.
Definition C3_NB : nat := 34%nat.
Definition C3_BX : sv := SOff 18 0.
Definition c3_alias : sv * sv := (SAlu ALU_ADD (SOff 26 0) (SOff 21 0), SOff C3_NP 0).
Definition c3_atoms : list (nat * afact) :=
  [(18%nat, mkAF SB SB 0); (25%nat, mkAF 32 32 0);
   (C3_NP, mkAF 4096 (2 ^ 47 - 16) 0); (C3_NB, mkAF 33 255 0)].
Definition c3_lt : acond := mkAC BC_LTU (SOff 21 0) (SOff 22 0).
Definition c3_lt1 : acond := mkAC BC_LTU (SOff 21 1) (SOff 22 0).
Definition c3_nz : acond := mkAC BC_NE (SOff 10 0) (SLit 0).
Definition c3_regC : smem :=
  [YP09.mkRegion (Some C3_NP) 0 2 0 0
     [YP09.mkChunk 0 (CVal 1 (SLit 44)); YP09.mkChunk 1 (CVal 1 (SOff C3_NB 0))]].
Definition c3_regB : smem :=
  [YP09.mkRegion (Some C3_NP) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 125))]].
Definition c3_ssC : sstate := mkSS SLOT_OFF sr_atoms c3_regC None (mkFacts c3_atoms [c3_lt1; c3_lt] [c3_alias]).
Definition c3_ssB : sstate := mkSS SLOT_OFF sr_atoms c3_regB None (mkFacts c3_atoms [c3_lt] [c3_alias]).
Definition c3_ssR : sstate := mkSS C3_RET sr_atoms [] None (mkFacts [] [c3_nz] []).
Definition c3_SHC : list shent := [mkSHE C3_NP 0 2].
Definition c3_SHB : list shent := [mkSHE C3_NP 0 1].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma c3_nowin : forall (E : env) (rs : smem) (a : Z),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> ~ in_wrange E rs a.
Proof.
  intros E rs a Hf (r & Hin & Hr). rewrite forallb_forall in Hf.
  pose proof (Hf r Hin) as Hq. apply Z.leb_le in Hq. lia.
Qed.

Lemma c3_byte : forall (W : world SEGS) m (a : Z) (l : list Z) (jx : Z),
  garr8 SEGS (rd W m) a l -> 0 <= jx < Z.of_nat (length l) ->
  val_mem SEGS (rd W m) (a + jx) 1 (nth (Z.to_nat jx) l 0) /\ 0 <= nth (Z.to_nat jx) l 0 < 256.
Proof.
  intros W m a l jx Hg Hj.
  assert (Hn : (Z.to_nat jx < length l)%nat) by lia.
  destruct (Hg (Z.to_nat jx) Hn) as [Hv Hr]. rewrite Z2Nat.id in Hv by lia. split; assumption.
Qed.

Lemma c3_nth_app : forall (l : list Z) (x : Z), 0 <= x < jlen l -> nth (Z.to_nat x) (l ++ [0]) 0 = jbyte l x.
Proof.
  intros l x Hx. unfold jbyte, jlen in *. rewrite app_nth1 by lia. reflexivity.
Qed.

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
destruct HIN as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc0 & Hcf & HCSR & HBASE & HJ & HFR & Hk & Hnev &
  HMO & Hacc & Hi & Hn & Hnow & HRL & (R22 & R26 & R21 & R19 & R23 & R24 & R27) &
  (HSP1 & HTAB & HBUF & HXS) & HSP0 & HBODY).
subst cf.
destruct HXS as (HFIN & Hipt & Hcount & Hlacc & HCONT & Hlc2 & HFAc2 & HMEM & V392 & V336 & V280).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HFIN as (HJR & Hfinb & HNOWS & HTLEN & HTOKS).
pose proof HBUF as (Hcap & HGARR).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBODY as (Tb & Gb & Lkb & Hb & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HDCAN & HSTKF & HAWRF).
pose proof HBLK as (HPerm0 & _ & _ & HOFFb).
assert (Hinbuf : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinbuf) as (Hbuf16 & Hbuf4096 & Hbufceil & Hbufapp & _ & _ & _).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = slot_ser_defs.ser_cap op).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia. }
rewrite Hreq in Hbufceil, Hbufapp.
assert (BV19 : bv_unsigned (19%bv : bv 5) = 19) by (vm_compute; reflexivity).
assert (BV23 : bv_unsigned (23%bv : bv 5) = 23) by (vm_compute; reflexivity).
assert (BV24 : bv_unsigned (24%bv : bv 5) = 24) by (vm_compute; reflexivity).
assert (BV27 : bv_unsigned (27%bv : bv 5) = 27) by (vm_compute; reflexivity).
assert (Hrlen : a3_r T1 now = jlen (a3_text T1 now)) by reflexivity.
assert (Hrle : a3_r T1 now <= 969) by (unfold a3_r; lia).
assert (Hglen : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1).
{ rewrite length_app. cbn [length]. unfold a3_r. lia. }
assert (Hcnt7 : count <= 7).
{ destruct HCONT as (f0 & i20 & c20 & _ & HA0).
  pose proof (jobjs_after_count (a3_text T1 now) fin i20 count acc c20 HA0). lia. }
assert (Hlobjs : (length (acc ++ [c2]) <= 9)%nat).
{ rewrite length_app, Hlacc. cbn [length]. lia. }
assert (HL9 : Z.of_nat (length (acc ++ [c2])) <= 9) by lia.
pose proof (jpairs_cont_step (a3_text T1 now) fin t c2 count acc HCONT) as HSTEP.
destruct HSTEP as [(Hc44 & HFROMP) | (Hc44f & Hc125 & HAFTER)].
-
  pose proof (at_byte_true _ _ _ Hc44) as (Hlt44 & Hby44).
  assert (Ht0 : 0 <= t) by lia.
  assert (Hrt : t < a3_r T1 now) by lia.
  rewrite (json_ws_id (a3_text T1 now) (t + 1) HNOWS ltac:(lia)) in HFROMP.
  pose proof (jpairs_from_step (a3_text T1 now) fin (t + 1) c2 count acc HFROMP)
    as (jj & kk & ks & kl & j2 & vk & vs & vl & cnew & HJS & Hkk1 & Hcolon & HJS2 & Hupd & HCONT2).
  assert (Hjgt : t + 1 < jj) by exact (jscalar_lt (a3_text T1 now) (t + 1) jj kk ks kl ltac:(lia) HJS).
  rewrite (json_ws_id (a3_text T1 now) jj HNOWS ltac:(lia)) in Hcolon.
  pose proof (at_byte_true _ _ _ Hcolon) as (Hjlt & _).
  assert (Hb1 : 33 <= jbyte (a3_text T1 now) (t + 1) <= 255)
    by (apply jno_ws_byte; [exact HNOWS | lia]).
  remember (Eimg (Ereg regs [w64 SB; w64 (buf + t); w64 (jbyte (a3_text T1 now) (t + 1))])) as E0 eqn:HE0.
  assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
  assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
    by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (ENP : ew E0 C3_NP = w64 (buf + t)).
  { rewrite HE0, Eimg_low by (unfold C3_NP, A_TEXT; lia).
    change C3_NP with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. }
  assert (ENB : ew E0 C3_NB = w64 (jbyte (a3_text T1 now) (t + 1))).
  { rewrite HE0, Eimg_low by (unfold C3_NB, A_TEXT; lia).
    change C3_NB with (32 + 2)%nat. rewrite ew_Ereg_extra. reflexivity. }
  assert (U18 : U E0 (SOff 18 0) = SHADOW_OFF).
  { apply (U_atom E0 18%nat SHADOW_OFF); [rewrite (EE0 18%nat 18%bv eq_refl); exact Rs2 | unfold SHADOW_OFF; lia]. }
  assert (U21 : U E0 (SOff 21 0) = t).
  { apply (U_atom E0 21%nat t); [rewrite (EE0 21%nat 21%bv eq_refl); exact R21 | lia]. }
  assert (U22 : U E0 (SOff 22 0) = a3_r T1 now).
  { apply (U_atom E0 22%nat (a3_r T1 now)); [rewrite (EE0 22%nat 22%bv eq_refl); exact R22 | lia]. }
  assert (U26 : U E0 (SOff 26 0) = buf).
  { apply (U_atom E0 26%nat buf); [rewrite (EE0 26%nat 26%bv eq_refl); exact R26 | lia]. }
  assert (UNP : U E0 (SOff C3_NP 0) = buf + t) by (apply (U_atom E0 C3_NP (buf + t) ENP); lia).
  assert (HG : facts_ok E0 (mkFacts c3_atoms [c3_lt1; c3_lt] [c3_alias])).
  { unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
    - unfold c3_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite (EE0 18%nat 18%bv eq_refl), (EE0 25%nat 25%bv eq_refl), ENP, ENB, Rs2, Rs9.
      unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF, SB in *; lia).
      rewrite Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
      repeat split; lia.
    - cbn [conds_ok]. unfold c3_lt1, c3_lt, acond_ok. cbn [ac_c ac_a ac_b].
      rewrite !branch_ltu_U.
      assert (U211 : U E0 (SOff 21 1) = t + 1)
        by (apply (U_atom_off E0 21%nat t 1); [rewrite (EE0 21%nat 21%bv eq_refl); exact R21 | lia | lia]).
      rewrite U211, U21, U22. split; [apply Z.ltb_lt; lia|]. split; [apply Z.ltb_lt; lia | exact I].
    - unfold c3_alias. cbn [alias_ok]. split; [|exact I].
      rewrite (denot_lit_U E0 (SAlu ALU_ADD (SOff 26 0) (SOff 21 0))), (denot_lit_U E0 (SOff C3_NP 0)).
      f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U21, U26, UNP. apply zcanon_id. unfold M64. lia. }
  assert (HROK : Forall (region_ok SEGS E0 (rd W mem3)) c3_regC).
  { constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite ENP. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    destruct (c3_byte W mem3 buf (a3_text T1 now ++ [0]) t HGARR ltac:(lia)) as (Hv0 & _).
    destruct (c3_byte W mem3 buf (a3_text T1 now ++ [0]) (t + 1) HGARR ltac:(lia)) as (Hv1 & _).
    rewrite (c3_nth_app (a3_text T1 now) t ltac:(lia)) in Hv0. rewrite (c3_nth_app (a3_text T1 now) (t + 1) ltac:(lia)) in Hv1.
    rewrite Hby44 in Hv0.
    constructor; [|constructor; [|constructor]].
    - apply (chunk_ok_val SEGS E0 _ (buf + t) 0 1 (SLit 44) 44).
      + cbn [sv_denot]. reflexivity.
      + cbn [Z.of_N]. lia.
      + cbn [Z.of_N]. lia.
      + cbn [N.to_nat]. replace (buf + t + 0) with (buf + t) by lia. exact Hv0.
    - apply (chunk_ok_val SEGS E0 _ (buf + t) 1 1 (SOff C3_NB 0) (jbyte (a3_text T1 now) (t + 1))).
      + rewrite (denot_lit_U E0 (SOff C3_NB 0)). f_equal.
        apply (U_atom E0 C3_NB (jbyte (a3_text T1 now) (t + 1)) ENB). lia.
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
    apply (c3_shent ly3 S3 W mem3 md3 E0 C3_NP buf (Z.max (slot_ser_defs.ser_cap op) 1) 0 2 HAR3 Hinbuf);
      [exact U18 | lia | rewrite UNP; lia | rewrite UNP, Hreq; lia]. }
  unfold cfg_at, w64.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?E ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' a1 b1 c1 d1 e1 f1 g1) end.
    intros a Ha. exfalso. revert Ha. apply c3_nowin. vm_compute. reflexivity. }
  assert (Emem : ms_mem ms = mem3).
  { apply functional_extensionality. intros x. apply HF.
    apply c3_nowin. vm_compute. reflexivity. }
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
  rewrite (EE0 26%nat 26%bv eq_refl) in Q10.
  rewrite (EE0 21%nat 21%bv eq_refl) in Q11.
  rewrite (EE0 22%nat 22%bv eq_refl) in Q12.
  rewrite (EE0 9%nat 9%bv eq_refl) in Q13.
  rewrite (EE0 18%nat 18%bv eq_refl) in Q18.
  rewrite (EE0 19%nat 19%bv eq_refl) in Q19.
  rewrite (EE0 20%nat 20%bv eq_refl) in Q20.
  rewrite (EE0 22%nat 22%bv eq_refl) in Q22.
  rewrite (EE0 23%nat 23%bv eq_refl) in Q23.
  rewrite (EE0 24%nat 24%bv eq_refl) in Q24.
  rewrite (EE0 25%nat 25%bv eq_refl) in Q25.
  rewrite (EE0 26%nat 26%bv eq_refl) in Q26.
  rewrite (EE0 27%nat 27%bv eq_refl) in Q27.
  rewrite R21 in Q11. rewrite R22 in Q12. rewrite Rs1 in Q13. rewrite R26 in Q10.
  unfold w64 in Q11, Q13. rewrite !unsigned_lit_small in Q11, Q13 by lia.
  pmkst HS.
  rewrite Emem, pa_sigma_json_scalar.
  eapply SRr_bind.
  { eapply (JSC cx h i n now op W0 c0 T0 T1 buf dsh_scr C3_RET (t + 1) 448 jj kk ks kl
      (fun rg => getr rg 19 = w64 (- a3_r T1 now) /\ getr rg 23 = w64 (jcur cx count) /\
         getr rg 24 = w64 (jcur cx count + 24) /\ getr rg 27 = w64 (jcur cx count + 48))
      (fun Wx mx => jmem cx buf count vpad (acc ++ [c2]) Wx mx /\
         val_mem SEGS (rd Wx mx) (d_A cx + 392) 8 (jcur cx count + 72) /\
         val_mem SEGS (rd Wx mx) (d_A cx + 336) 8 (jcur cx count + 96) /\
         val_mem SEGS (rd Wx mx) (d_A cx + 280) 8 (jcur cx count + 120)) W _).
    - unfold C3_RET. lia.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - exact HJS.
    - intros rg rg' HP (A19 & A23 & A24 & A27).
      split; [rewrite (jsc_getr_kept rg rg' 19 HP ltac:(rewrite BV19; unfold acallee_saved; lia)); exact A19|].
      split; [rewrite (jsc_getr_kept rg rg' 23 HP ltac:(rewrite BV23; unfold acallee_saved; lia)); exact A23|].
      split; [rewrite (jsc_getr_kept rg rg' 24 HP ltac:(rewrite BV24; unfold acallee_saved; lia)); exact A24|].
      rewrite (jsc_getr_kept rg rg' 27 HP ltac:(rewrite BV27; unfold acallee_saved; lia)); exact A27.
    - intros W1 m1 W2 m2 (HM1 & P392 & P336 & P280) (K1 & K2 & K3 & K4 & HK).
      destruct HM1 as (M408 & M368 & Mpl & Mpad & MOO & MF6).
      assert (KV : forall off v, 0 <= off -> off + 8 <= 448 ->
        val_mem SEGS (rd W1 m1) (d_A cx + off) 8 v -> val_mem SEGS (rd W2 m2) (d_A cx + off) 8 v).
      { intros off v H1 H2 Hv.
        apply (jsc_val_mem_kept _ W1 m1 W2 m2 (d_A cx + off) 8%nat v HK ltac:(lia)
                 ltac:(cbn [Z.of_nat]; lia)); [|exact Hv].
        intros x Hx. cbn [Z.of_nat] in Hx. intros [Hq|Hq]; lia. }
      split; [|split; [|split]].
      + split; [exact (KV 408 count ltac:(lia) ltac:(lia) M408)|].
        split; [exact (KV 368 (buf + 1) ltac:(lia) ltac:(lia) M368)|].
        split; [exact Mpl|].
        split; [|split].
        * apply (jsc_garr8_kept _ W1 m1 W2 m2 (d_A cx + 444)
                   (map (fun b : byte => bv_unsigned b) vpad) HK ltac:(lia)).
          -- rewrite length_map, Mpl. cbn [Z.of_nat]. lia.
          -- intros x Hx. rewrite length_map, Mpl in Hx. cbn [Z.of_nat] in Hx.
             intros [Hq|Hq]; lia.
          -- exact Mpad.
        * destruct (c3_oo (d_FB cx) (d_A cx) (d_S cx) TJSON_SCALAR_STK (length (acc ++ [c2]))
                      K1 K2 ltac:(unfold TJSON_SCALAR_STK, ESTACK; lia) K3 K4 Hlobjs) as (HOO1 & HOO2).
          apply (jsc_garr8_kept _ W1 m1 W2 m2 (d_obj cx OO)
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
      + exact (KV 392 (jcur cx count + 72) ltac:(lia) ltac:(lia) P392).
      + exact (KV 336 (jcur cx count + 96) ltac:(lia) ltac:(lia) P336).
      + exact (KV 280 (jcur cx count + 120) ltac:(lia) ltac:(lia) P280).
    - unfold jsc_in, jcut. split; [exact HFROM|].
      unfold d_arm_at_pf, d_at.
      exists fq, ly3, S3, (ms_regs ms), mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, acc0.
      split; [unfold cfg_at, w64; rewrite <- Emem; reflexivity|].
      split; [exact HCSR|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|].
      split; [exact Hk|]. split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
      split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
      split.
      { split; [unfold spZ; rewrite Q2; exact Rsp|].
        split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
        split; [rewrite Q9; exact Rs1|]. split; [rewrite Q18; exact Rs2|]. split; [rewrite Q20; exact Rs4|].
        rewrite Q25; exact Rs9. }
      split.
      { split; [rewrite Q22; exact R22|]. split; [rewrite Q26; exact R26|].
        split; [exact Q1|]. split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|].
        split; [rewrite Q13; unfold w64; reflexivity|].
        split; [rewrite Q19; exact R19|]. split; [rewrite Q23; exact R23|].
        split; [rewrite Q24; exact R24|]. rewrite Q27; exact R27. }
      split.
      { split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|].
        split; [exact HMEM|]. split; [exact V392|]. split; [exact V336|]. exact V280. }
      split; [exact HSP0 | exact HBODY]. }
  cbv beta. intros W4 cfg4 HW4 HOUT.
  unfold jsc_out, jcut, d_arm_at_pf, d_at in HOUT.
  destruct HOUT as (HFROM4 & fq4 & ly4 & S4 & regs4 & mem4 & md4 & k4 & acc4 & Hcfg4 & HCSR4 & HBASE4 & HJ4 & HFR4 & Hk4 &
    Hnev4 & HMO4 & Hacc4 & Hi4 & Hn4 & Hnow4 & HRL4 & (R22' & R26' & R10' & R19' & R23' & R24' & R27') &
    (HSP1' & HTAB' & HBUF' & (HMEM' & P392 & P336 & P280) & V448 & V456 & V464) & HSP0' & HBODY4).
  subst cfg4.
  pose proof HRL4 as (Rsp4 & Rgp4 & Rtp4 & Rs04 & Rs14 & Rs24 & Rs44 & Rs94).
  assert (Hj0 : 0 < jj) by lia.
  remember (Eimg (Ereg regs4 [w64 SB])) as E1 eqn:HE1.
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
    apply c3_nowin. vm_compute. reflexivity. }
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
  split; [exact HCSR4|]. split; [exact HBASE4|]. split; [exact HJ4|]. split; [exact HFR4|].
  split; [exact Hk4|]. split; [exact Hnev4|]. split; [exact HMO4|]. split; [exact Hacc4|].
  split; [exact Hi4|]. split; [exact Hn4|]. split; [exact Hnow4|].
  split.
  { split; [unfold spZ; rewrite P2; exact Rsp4|].
    split; [rewrite P3; exact Rgp4|]. split; [rewrite P4; exact Rtp4|]. split; [rewrite P8; exact Rs04|].
    split; [rewrite P9; exact Rs14|]. split; [rewrite P18; exact Rs24|]. split; [rewrite P20; exact Rs44|].
    rewrite P25; exact Rs94. }
  split.
  { split; [rewrite P22; exact R22'|]. split; [rewrite P26; exact R26'|].
    split; [rewrite P10; exact R10'|]. split; [rewrite P19; exact R19'|].
    split; [rewrite P23; exact R23'|]. split; [rewrite P24; exact R24'|]. rewrite P27; exact R27'. }
  split.
  { split; [exact HSP1'|]. split; [exact HTAB'|]. split; [exact HBUF'|].
    split; [exact HFIN|]. split; [lia|]. split; [exact Hcount|]. split; [exact Hlacc|].
    split; [exact HJS|]. split; [exact HFROMP|]. split; [exact Hlc2|]. split; [exact HFAc2|].
    split; [exact HMEM'|]. split; [exact P392|]. split; [exact P336|]. split; [exact P280|].
    split; [exact V448|].
    split; [replace (d_A cx + 456) with (d_A cx + 448 + 8) by lia; exact V456|].
    replace (d_A cx + 464) with (d_A cx + 448 + 16) by lia; exact V464. }
  split; [exact HSP0' | exact HBODY4].
-
  pose proof (at_byte_true _ _ _ Hc125) as (Hlt125 & Hby125).
  assert (Ht0 : 0 <= t) by lia.
  assert (Hrt : t < a3_r T1 now) by lia.
  remember (Eimg (Ereg regs [w64 SB; w64 (buf + t); w64 33])) as E0 eqn:HE0.
  assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
  assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
    by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (ENP : ew E0 C3_NP = w64 (buf + t)).
  { rewrite HE0, Eimg_low by (unfold C3_NP, A_TEXT; lia).
    change C3_NP with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. }
  assert (ENB : ew E0 C3_NB = w64 33).
  { rewrite HE0, Eimg_low by (unfold C3_NB, A_TEXT; lia).
    change C3_NB with (32 + 2)%nat. rewrite ew_Ereg_extra. reflexivity. }
  assert (U18 : U E0 (SOff 18 0) = SHADOW_OFF).
  { apply (U_atom E0 18%nat SHADOW_OFF); [rewrite (EE0 18%nat 18%bv eq_refl); exact Rs2 | unfold SHADOW_OFF; lia]. }
  assert (U21 : U E0 (SOff 21 0) = t).
  { apply (U_atom E0 21%nat t); [rewrite (EE0 21%nat 21%bv eq_refl); exact R21 | lia]. }
  assert (U22 : U E0 (SOff 22 0) = a3_r T1 now).
  { apply (U_atom E0 22%nat (a3_r T1 now)); [rewrite (EE0 22%nat 22%bv eq_refl); exact R22 | lia]. }
  assert (U26 : U E0 (SOff 26 0) = buf).
  { apply (U_atom E0 26%nat buf); [rewrite (EE0 26%nat 26%bv eq_refl); exact R26 | lia]. }
  assert (UNP : U E0 (SOff C3_NP 0) = buf + t) by (apply (U_atom E0 C3_NP (buf + t) ENP); lia).
  assert (HG : facts_ok E0 (mkFacts c3_atoms [c3_lt] [c3_alias])).
  { unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split].
    - unfold c3_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite (EE0 18%nat 18%bv eq_refl), (EE0 25%nat 25%bv eq_refl), ENP, ENB, Rs2, Rs9.
      unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF, SB in *; lia).
      rewrite Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
      repeat split; lia.
    - cbn [conds_ok]. unfold c3_lt, acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_ltu_U, U21, U22. split; [apply Z.ltb_lt; lia | exact I].
    - unfold c3_alias. cbn [alias_ok]. split; [|exact I].
      rewrite (denot_lit_U E0 (SAlu ALU_ADD (SOff 26 0) (SOff 21 0))), (denot_lit_U E0 (SOff C3_NP 0)).
      f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U21, U26, UNP. apply zcanon_id. unfold M64. lia. }
  assert (HROK : Forall (region_ok SEGS E0 (rd W mem3)) c3_regB).
  { constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite ENP. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    destruct (c3_byte W mem3 buf (a3_text T1 now ++ [0]) t HGARR ltac:(lia)) as (Hv0 & _).
    rewrite (c3_nth_app (a3_text T1 now) t ltac:(lia)) in Hv0. rewrite Hby125 in Hv0.
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E0 _ (buf + t) 0 1 (SLit 125) 125).
    - cbn [sv_denot]. reflexivity.
    - cbn [Z.of_N]. lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. replace (buf + t + 0) with (buf + t) by lia. exact Hv0. }
  assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 c3_ssB
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + SLOT_OFF)) mem3 (YK11.seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE0. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - exact HROK.
    - cbn [pairwise_disjoint all_disjoint c3_regB]. split; exact I.
    - exact HG. }
  assert (SHOK : sh_ok SEGS C3_BX c3_SHB E0 (rd W mem3)).
  { unfold c3_SHB. constructor; [|constructor].
    apply (c3_shent ly3 S3 W mem3 md3 E0 C3_NP buf (Z.max (slot_ser_defs.ser_cap op) 1) 0 1 HAR3 Hinbuf);
      [exact U18 | lia | rewrite UNP; lia | rewrite UNP, Hreq; lia]. }
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan OEND_OFF.
  { lazymatch goal with |- awr_ok ?E ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' a1 b1 c1 d1 e1 f1 g1) end.
    intros a Ha. exfalso. revert Ha. apply c3_nowin. vm_compute. reflexivity. }
  assert (Emem : ms_mem ms = mem3).
  { apply functional_extensionality. intros x. apply HF.
    apply c3_nowin. vm_compute. reflexivity. }
  rewrite Emem in HJ.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  rewrite (EE0 2%nat 2%bv eq_refl) in Q2.
  rewrite (EE0 3%nat 3%bv eq_refl) in Q3.
  rewrite (EE0 4%nat 4%bv eq_refl) in Q4.
  rewrite (EE0 8%nat 8%bv eq_refl) in Q8.
  rewrite (EE0 9%nat 9%bv eq_refl) in Q9.
  rewrite (EE0 18%nat 18%bv eq_refl) in Q18.
  rewrite (EE0 19%nat 19%bv eq_refl) in Q19.
  rewrite (EE0 20%nat 20%bv eq_refl) in Q20.
  rewrite (EE0 21%nat 21%bv eq_refl) in Q21.
  rewrite (EE0 22%nat 22%bv eq_refl) in Q22.
  rewrite (EE0 25%nat 25%bv eq_refl) in Q25.
  rewrite (EE0 26%nat 26%bv eq_refl) in Q26.
  pmkst HS. rewrite Emem.
  apply SRr_ret. right.
  exists t. split; [lia|].
  unfold joend_in, jcut. split; [exact HFROM|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms), mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, acc0.
  split; [unfold cfg_at, w64; rewrite <- Emem; reflexivity|].
  split; [exact HCSR|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|].
  split; [exact Hk|]. split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { split; [unfold spZ; rewrite Q2; exact Rsp|].
    split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
    split; [rewrite Q9; exact Rs1|]. split; [rewrite Q18; exact Rs2|]. split; [rewrite Q20; exact Rs4|].
    rewrite Q25; exact Rs9. }
  split.
  { split; [rewrite Q22; exact R22|]. split; [rewrite Q26; exact R26|].
    split; [rewrite Q21; exact R21|]. rewrite Q19; exact R19. }
  split.
  { split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|].
    split; [exact HFIN|]. split; [lia|]. split; [exact Hcount|]. split; [exact Hlacc|].
    split; [exact Hc125|]. split; [exact HAFTER|]. split; [exact Hlc2|]. split; [exact HFAc2|]. exact HMEM. }
  split; [exact HSP0 | exact HBODY].
Qed.

End h.
End f.
End d.
