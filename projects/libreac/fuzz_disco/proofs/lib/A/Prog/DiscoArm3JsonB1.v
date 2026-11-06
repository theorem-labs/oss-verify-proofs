(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module names changed; 346 of its 391 lines of code are new or changed and 451 lines of the source are left out. *)
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
DiscoArm3JsonJs DiscoArm3JsonBDefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition B1_NP : nat := 33%nat.
Definition B1_NB : nat := 34%nat.
Definition B1_BX : sv := SOff 18 0.
Definition b1_al0 : sv * sv := (SAlu ALU_ADD (SOff 26 0) (SOff 24 0), SOff B1_NP 0).
Definition b1_al1 : sv * sv := (SAlu ALU_SUB (SLit 0) (SAlu ALU_XOR (SOff 24 0) (SLit (-1))), SOff 24 1).
Definition b1_atoms : list (nat * afact) :=
  [(18%nat, mkAF SB SB 0); (25%nat, mkAF 32 32 0);
   (B1_NP, mkAF 4096 (2 ^ 47 - 16) 0); (B1_NB, mkAF 33 255 0)].
Definition b1_lt1 : acond := mkAC BC_LTU (SOff 24 1) (SOff 22 0).
Definition b1_ne : acond := mkAC BC_NE (SOff B1_NB 0) (SLit 125).
Definition b1_rA : YP09.region := YP09.mkRegion (Some 9%nat) 368 376 0 0 [YP09.mkChunk 368 (CVal 8 (SOff 26 1))].
Definition b1_rP : YP09.region :=
  YP09.mkRegion (Some B1_NP) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 123)); YP09.mkChunk 1 (CVal 1 (SOff B1_NB 0))].
Definition b1_rQ : YP09.region :=
  YP09.mkRegion (Some B1_NP) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 123)); YP09.mkChunk 1 (CVal 1 (SLit 125))].
Definition b1_ssP : sstate :=
  mkSS OBJ_OFF sr_atoms [b1_rP; b1_rA] None (mkFacts b1_atoms [b1_lt1; b1_ne] [b1_al0; b1_al1]).
Definition b1_ssQ : sstate :=
  mkSS OBJ_OFF sr_atoms [b1_rQ; b1_rA] None (mkFacts b1_atoms [b1_lt1] [b1_al0; b1_al1]).
Definition b1_SH : list shent := [mkSHE B1_NP 0 2].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma b1_nowin : forall (E : env) (rs : smem) (a : Z),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> ~ in_wrange E rs a.
Proof.
  intros E rs a Hf (r & Hin & Hr). rewrite forallb_forall in Hf.
  pose proof (Hf r Hin) as Hq. apply Z.leb_le in Hq. lia.
Qed.

Lemma b1_byte : forall (W : world SEGS) m (a : Z) (l : list Z) (jx : Z),
  garr8 SEGS (rd W m) a l -> 0 <= jx < Z.of_nat (length l) ->
  val_mem SEGS (rd W m) (a + jx) 1 (nth (Z.to_nat jx) l 0) /\ 0 <= nth (Z.to_nat jx) l 0 < 256.
Proof.
  intros W m a l jx Hg Hj.
  assert (Hn : (Z.to_nat jx < length l)%nat) by lia.
  destruct (Hg (Z.to_nat jx) Hn) as [Hv Hr]. rewrite Z2Nat.id in Hv by lia. split; assumption.
Qed.

Lemma b1_nth_app : forall (l : list Z) (x : Z), 0 <= x < jlen l -> nth (Z.to_nat x) (l ++ [0]) 0 = jbyte l x.
Proof.
  intros l x Hx. unfold jbyte, jlen in *. rewrite app_nth1 by lia. reflexivity.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma b1_shent : forall ly S (W : world SEGS) mem md (E : env) (q : nat) (bp len lo hi : Z),
  AR SEGS B ly S W mem md -> In (bp, len) (ablocks B ly S) ->
  U E B1_BX = SHADOW_OFF -> 0 <= lo <= hi ->
  bp <= U E (SOff q 0) + lo -> U E (SOff q 0) + hi <= bp + req_size len ->
  shent_ok SEGS B1_BX E (rd W mem) (mkSHE q lo hi).
Proof.
  intros ly S W mem md E q bp len lo hi HAR Hin HB Hlh Hlo Hhi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & _).
  eapply (shent_ok_of_range SEGS (w_H W) mem E B1_BX q bp (req_size len) (U E (SOff q 0)) lo hi).
  - exact (range_addressable_of_block SEGS B LAWS ly S W mem md bp len bp (req_size len) HAR Hin
             ltac:(lia) ltac:(lia)).
  - exact HB.
  - reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

Theorem a3j_B1 : jseg_B1 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W cf HIN.
unfold jobj_in, jcut, d_arm_at_pf, d_at in HIN.
destruct HIN as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc0 & Hcf & HCSR & HBASE & HJ & HFR & Hk & Hnev &
  HMO & Hacc & Hi & Hn & Hnow & HRL & (R22 & R26 & R24 & R19 & R27 & R23) &
  (HSP1 & HTAB & HBUF & HXS) & HSP0 & HBODY).
subst cf.
destruct HXS as (HFIN & Hii & Hcount & Hlacc & HOBJS & HMEM).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HFIN as (HJR & Hfinb & HNOWS & HTLEN & HTOKS).
pose proof HBUF as (Hcap & HGARR).
pose proof HMEM as (M408 & M368 & Mpl & Mpad & MOO & MF6).
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
assert (Hrlen : a3_r T1 now = jlen (a3_text T1 now)) by reflexivity.
assert (Hrle : a3_r T1 now <= 969) by (unfold a3_r; lia).
assert (Hglen : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1).
{ rewrite length_app. cbn [length]. unfold a3_r. lia. }
pose proof (jobjs_from_step (a3_text T1 now) fin ii count acc HOBJS) as (H123 & HCASE).
rewrite (json_ws_id (a3_text T1 now) (ii + 1) HNOWS ltac:(lia)) in HCASE.
pose proof (at_byte_true _ _ _ H123) as (Hlt0 & Hby0).
assert (Hlt1 : ii + 1 < jlen (a3_text T1 now)).
{ destruct HCASE as [(H125 & _) | (_ & HPF)].
  - exact (proj1 (at_byte_true _ _ _ H125)).
  - destruct (jpairs_from_step (a3_text T1 now) fin (ii + 1) jobj_empty count acc HPF)
      as (jj & kk & ks & kl & _ & _ & _ & _ & _ & HJS & _).
    exact (jscalar_in (a3_text T1 now) (ii + 1) jj kk ks kl HJS). }
assert (Hb1 : 33 <= jbyte (a3_text T1 now) (ii + 1) <= 255) by (apply jno_ws_byte; [exact HNOWS | lia]).
remember (Eimg (Ereg regs [w64 SB; w64 (buf + ii); w64 (jbyte (a3_text T1 now) (ii + 1))])) as E0 eqn:HE0.
assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (ENP : ew E0 B1_NP = w64 (buf + ii)).
{ rewrite HE0, Eimg_low by (unfold B1_NP, A_TEXT; lia).
  change B1_NP with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (ENB : ew E0 B1_NB = w64 (jbyte (a3_text T1 now) (ii + 1))).
{ rewrite HE0, Eimg_low by (unfold B1_NB, A_TEXT; lia).
  change B1_NB with (32 + 2)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (U18 : U E0 (SOff 18 0) = SHADOW_OFF).
{ apply (U_atom E0 18%nat SHADOW_OFF); [rewrite (EE0 18%nat 18%bv eq_refl); exact Rs2 | unfold SHADOW_OFF; lia]. }
assert (U24 : U E0 (SOff 24 0) = ii).
{ apply (U_atom E0 24%nat ii); [rewrite (EE0 24%nat 24%bv eq_refl); exact R24 | lia]. }
assert (U241 : U E0 (SOff 24 1) = ii + 1).
{ apply (U_atom_off E0 24%nat ii 1); [rewrite (EE0 24%nat 24%bv eq_refl); exact R24 | lia | lia]. }
assert (U22 : U E0 (SOff 22 0) = a3_r T1 now).
{ apply (U_atom E0 22%nat (a3_r T1 now)); [rewrite (EE0 22%nat 22%bv eq_refl); exact R22 | lia]. }
assert (U26 : U E0 (SOff 26 0) = buf).
{ apply (U_atom E0 26%nat buf); [rewrite (EE0 26%nat 26%bv eq_refl); exact R26 | lia]. }
assert (U261 : U E0 (SOff 26 1) = buf + 1).
{ apply (U_atom_off E0 26%nat buf 1); [rewrite (EE0 26%nat 26%bv eq_refl); exact R26 | lia | lia]. }
assert (UNP : U E0 (SOff B1_NP 0) = buf + ii) by (apply (U_atom E0 B1_NP (buf + ii) ENP); lia).
assert (UNB : U E0 (SOff B1_NB 0) = jbyte (a3_text T1 now) (ii + 1))
  by (apply (U_atom E0 B1_NB (jbyte (a3_text T1 now) (ii + 1)) ENB); lia).
assert (HAT : atoms_ok E0 b1_atoms).
{ unfold b1_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (EE0 18%nat 18%bv eq_refl), (EE0 25%nat 25%bv eq_refl), ENP, ENB, Rs2, Rs9.
  unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF, SB in *; lia).
  rewrite Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
  repeat split; lia. }
assert (HAL : alias_ok E0 [b1_al0; b1_al1]).
{ unfold b1_al0, b1_al1. cbn [alias_ok]. split; [|split; [|exact I]].
  - rewrite (denot_lit_U E0 (SAlu ALU_ADD (SOff 26 0) (SOff 24 0))), (denot_lit_U E0 (SOff B1_NP 0)).
    f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U24, U26, UNP. apply zcanon_id. unfold M64. lia.
  - apply U_inj. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, U24, U241.
    replace (zcanon (-1)) with (2 ^ 64 - 1) by reflexivity.
    rewrite lxor_allones by lia.
    unfold zcanon, M64.
    rewrite (Z.mod_small 0) by lia. rewrite (Z.mod_small (2 ^ 64 - 1 - ii)) by lia.
    replace (0 - (2 ^ 64 - 1 - ii)) with ((ii + 1) + (-1) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HLT1 : acond_ok E0 b1_lt1).
{ unfold b1_lt1, acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, U241, U22. apply Z.ltb_lt. lia. }
assert (HRA : region_ok SEGS E0 (rd W mem3) b1_rA).
{ unfold region_ok, b1_rA.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite (EE0 9%nat 9%bv eq_refl), Rs1. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E0 _ (d_A cx) 368 8 (SOff 26 1) (buf + 1)).
  - rewrite (denot_lit_U E0 (SOff 26 1)). f_equal. exact U261.
  - cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. exact M368. }
destruct (b1_byte W mem3 buf (a3_text T1 now ++ [0]) ii HGARR ltac:(lia)) as (Hv0 & _).
destruct (b1_byte W mem3 buf (a3_text T1 now ++ [0]) (ii + 1) HGARR ltac:(lia)) as (Hv1 & _).
rewrite (b1_nth_app (a3_text T1 now) ii ltac:(lia)) in Hv0.
rewrite (b1_nth_app (a3_text T1 now) (ii + 1) ltac:(lia)) in Hv1.
rewrite Hby0 in Hv0.
replace (buf + (ii + 1)) with (buf + ii + 1) in Hv1 by lia.
assert (HC0 : YP09.chunk_ok SEGS E0 (rd W mem3) (buf + ii) (YP09.mkChunk 0 (CVal 1 (SLit 123)))).
{ apply (chunk_ok_val SEGS E0 _ (buf + ii) 0 1 (SLit 123) 123).
  - cbn [sv_denot]. reflexivity.
  - cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. replace (buf + ii + 0) with (buf + ii) by lia. exact Hv0. }
assert (HXD : buf + ii + 2 <= d_A cx + 368) by lia.
assert (SHOK : sh_ok SEGS B1_BX b1_SH E0 (rd W mem3)).
{ unfold b1_SH. constructor; [|constructor].
  apply (b1_shent ly3 S3 W mem3 md3 E0 B1_NP buf (Z.max (slot_ser_defs.ser_cap op) 1) 0 2 HAR3 Hinbuf);
    [exact U18 | lia | rewrite UNP; lia | rewrite UNP, Hreq; lia]. }
unfold cfg_at, w64.
destruct HCASE as [(H125 & HAFT) | (H125f & HPF)].
-
  pose proof (at_byte_true _ _ _ H125) as (_ & Hby1).
  rewrite Hby1 in Hv1.
  assert (HROK : Forall (region_ok SEGS E0 (rd W mem3)) [b1_rQ; b1_rA]).
  { constructor; [|constructor; [exact HRA | constructor]].
    unfold region_ok, b1_rQ.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite ENP. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [exact HC0 | constructor; [|constructor]].
    apply (chunk_ok_val SEGS E0 _ (buf + ii) 1 1 (SLit 125) 125).
    - cbn [sv_denot]. reflexivity.
    - cbn [Z.of_N]. lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. exact Hv1. }
  assert (HDJ : pairwise_disjoint E0 [b1_rQ; b1_rA]).
  { cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, b1_rQ, b1_rA.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite ENP, (EE0 9%nat 9%bv eq_refl), Rs1. unfold w64. rewrite !unsigned_lit_small by lia. left. lia. }
  assert (HG : facts_ok E0 (mkFacts b1_atoms [b1_lt1] [b1_al0; b1_al1])).
  { unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [exact HAT|]. split; [|exact HAL].
    cbn [conds_ok]. split; [exact HLT1 | exact I]. }
  assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 b1_ssQ
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + OBJ_OFF)) mem3 (YK11.seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE0. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - exact HROK.
    - exact HDJ.
    - exact HG. }
  clear HG.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan OEND_OFF.
  { lazymatch goal with |- awr_ok ?E ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' a1 b1 c1 d1 e1 f1 g1) end.
    intros a Ha. exfalso. revert Ha. apply b1_nowin. vm_compute. reflexivity. }
  assert (Emem : ms_mem ms = mem3).
  { apply functional_extensionality. intros x. apply HF.
    apply b1_nowin. vm_compute. reflexivity. }
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
  rewrite (EE0 24%nat 24%bv eq_refl) in Q21.
  rewrite (EE0 22%nat 22%bv eq_refl) in Q22.
  rewrite (EE0 25%nat 25%bv eq_refl) in Q25.
  rewrite (EE0 26%nat 26%bv eq_refl) in Q26.
  rewrite R24 in Q21. unfold w64 in Q21. rewrite unsigned_lit_small in Q21 by lia.
  pmkst HS. rewrite Emem.
  apply SRr_ret. right.
  unfold joend_in, jcut. split; [exact HFROM|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms), mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, acc0.
  split; [unfold cfg_at, w64; reflexivity|].
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
    split; [exact Q21|]. rewrite Q19; exact R19. }
  split.
  { split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|].
    split; [exact HFIN|]. split; [lia|]. split; [exact Hcount|]. split; [exact Hlacc|].
    split; [exact H125|]. split; [exact HAFT|]. split; [reflexivity|].
    split; [exact (jb_empty_in (a3_text T1 now)) | exact HMEM]. }
  split; [exact HSP0 | exact HBODY].
-
  assert (Hne : jbyte (a3_text T1 now) (ii + 1) <> 125).
  { rewrite at_byte_spec in H125f by lia. apply Z.eqb_neq. exact H125f. }
  assert (HROK : Forall (region_ok SEGS E0 (rd W mem3)) [b1_rP; b1_rA]).
  { constructor; [|constructor; [exact HRA | constructor]].
    unfold region_ok, b1_rP.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite ENP. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [exact HC0 | constructor; [|constructor]].
    apply (chunk_ok_val SEGS E0 _ (buf + ii) 1 1 (SOff B1_NB 0) (jbyte (a3_text T1 now) (ii + 1))).
    - rewrite (denot_lit_U E0 (SOff B1_NB 0)). f_equal. exact UNB.
    - cbn [Z.of_N]. lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. exact Hv1. }
  assert (HDJ : pairwise_disjoint E0 [b1_rP; b1_rA]).
  { cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, b1_rP, b1_rA.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite ENP, (EE0 9%nat 9%bv eq_refl), Rs1. unfold w64. rewrite !unsigned_lit_small by lia. left. lia. }
  assert (HG : facts_ok E0 (mkFacts b1_atoms [b1_lt1; b1_ne] [b1_al0; b1_al1])).
  { unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [exact HAT|]. split; [|exact HAL].
    cbn [conds_ok]. split; [exact HLT1|]. split; [|exact I].
    unfold b1_ne, acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, UNB, U_lit by lia.
    apply negb_true_iff. apply Z.eqb_neq. exact Hne. }
  assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 b1_ssP
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + OBJ_OFF)) mem3 (YK11.seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE0. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - exact HROK.
    - exact HDJ.
    - exact HG. }
  clear HG.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?E ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' a1 b1 c1 d1 e1 f1 g1) end.
    intros a Ha. exfalso. revert Ha. apply b1_nowin. vm_compute. reflexivity. }
  assert (Emem : ms_mem ms = mem3).
  { apply functional_extensionality. intros x. apply HF.
    apply b1_nowin. vm_compute. reflexivity. }
  rewrite Emem in HJ.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  rewrite (EE0 2%nat 2%bv eq_refl) in Q2.
  rewrite (EE0 3%nat 3%bv eq_refl) in Q3.
  rewrite (EE0 4%nat 4%bv eq_refl) in Q4.
  rewrite (EE0 8%nat 8%bv eq_refl) in Q8.
  rewrite (EE0 9%nat 9%bv eq_refl) in Q9.
  rewrite (EE0 26%nat 26%bv eq_refl) in Q10.
  rewrite (EE0 24%nat 24%bv eq_refl) in Q11.
  rewrite (EE0 22%nat 22%bv eq_refl) in Q12.
  rewrite (EE0 9%nat 9%bv eq_refl) in Q13.
  rewrite (EE0 18%nat 18%bv eq_refl) in Q18.
  rewrite (EE0 19%nat 19%bv eq_refl) in Q19.
  rewrite (EE0 20%nat 20%bv eq_refl) in Q20.
  rewrite (EE0 22%nat 22%bv eq_refl) in Q22.
  rewrite (EE0 23%nat 23%bv eq_refl) in Q23.
  rewrite (EE0 25%nat 25%bv eq_refl) in Q25.
  rewrite (EE0 26%nat 26%bv eq_refl) in Q26.
  rewrite (EE0 27%nat 27%bv eq_refl) in Q27.
  rewrite R24 in Q11. rewrite R22 in Q12. rewrite Rs1 in Q13. rewrite R26 in Q10.
  unfold w64 in Q11, Q13. rewrite !unsigned_lit_small in Q11, Q13 by lia.
  pmkst HS.
  rewrite Emem, pa_sigma_json_scalar.
  apply SRr_ret. left.
  unfold jb_call, jsc_in, jcut. split; [exact HFROM|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms), mem3, (with_vm_backing (m_vm_lazy md3) mat md3), k, acc0.
  split; [unfold cfg_at, w64; reflexivity|].
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
    split; [rewrite Q13; unfold w64, JSC_KEY_OFF; reflexivity|].
    unfold jb_R. split; [rewrite Q19; exact R19|]. split; [rewrite Q27; exact R27|]. rewrite Q23; exact R23. }
  split.
  { split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|].
    unfold jb_X. split; [exact HFIN|]. split; [exact Hii|]. split; [exact Hcount|]. split; [exact Hlacc|].
    split; [exact HPF | exact HMEM]. }
  split; [exact HSP0 | exact HBODY].
Qed.

End h.
End f.
End d.
