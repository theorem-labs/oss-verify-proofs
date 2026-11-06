(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 1243 of its 1273 lines of code are new or changed and 39 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntCls.v, with its module paths, module names, addresses and numbers changed; 433 of its 668 lines of code are new or changed and 1038 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC81 YC1g YC1h YC4b YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require GateModel CtrlParsed slot_classify.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt ClassifyCore ReacDiscoClassify ReacDiscoClassifyOnSegment
DiscoYEntClsCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition s1_acs : list YP09.chunk := [YP09.mkChunk 368 (CVal 8 (SOff 563 0))].
Definition s1_rs (acs : list YP09.chunk) : smem :=
  [YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ acs)].

Lemma s1_sub : forall shf acs, submem (s1_rs acs) (d_kregions shf acs [] ++ []).
Proof.
intros shf acs. unfold s1_rs, d_kregions. cbn [app].
apply submem_drop. apply submem_keep; [|apply submem_nil].
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. intros c Hc. exact Hc.
Qed.

Lemma s1_len_our : forall pl, length (our_of pl) = 6%nat.
Proof. intros pl. unfold our_of. rewrite length_map, length_seq. reflexivity. Qed.

Lemma s1_w64_add : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma s1_lock_ok : forall F len U Lb Lb', length F = 50%nat -> lock_ok Lb ->
  cm_lock F len U (Some Lb) = Some Lb' -> lock_ok Lb'.
Proof.
intros F len U Lb Lb' LF HL E. unfold cm_lock, classify_model in E. cbv zeta in E.
repeat (match type of E with context [if ?c then _ else _] => destruct c end); cbn [snd fst] in E;
  injection E as <-; try exact HL.
pose proof HL as (HL12 & _).
assert (Ls : length (src F) = 6%nat) by (unfold src, CtrlParsed.fld; rewrite length_firstn, length_skipn, LF; reflexivity).
assert (Lf : length (firstn 2 (skipn 6 Lb)) = 2%nat) by (rewrite length_firstn, length_skipn, HL12; reflexivity).
unfold lock_ok, latch. split.
- unfold CtrlParsed.fld. rewrite !length_app, Ls, Lf, slot_classify.sc_le4_len. reflexivity.
- right. unfold CtrlParsed.fu, CtrlParsed.fld. rewrite app_assoc, skipn_app, length_app, Ls, Lf.
  rewrite skipn_all2 by (rewrite length_app, Ls, Lf; lia). replace (8 - (6 + 2))%nat with 0%nat by reflexivity.
  rewrite skipn_O.
  vm_compute. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma s1_env_xs : forall cx E regs v, ew (d_env cx E (cl_vals regs [v])) 563 = v.
Proof.
intros cx E regs v. unfold d_env. change 563%nat with (AT_FL + 33)%nat.
rewrite (ew_havoc_new _ AT_FL _ 33 (Z_to_bv 64 0))
  by (cbn [length]; unfold cl_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia).
reflexivity.
Qed.

Lemma s1_aview_ext : forall (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros W m m' HM a. apply aview_eq_of. unfold mrestrict. rewrite HM. reflexivity.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = FF_canary.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BKEEP : d_body_keep_stmt B.
Hypothesis BTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis TCLS : ReacDiscoClassify.treac_disco_classify_spec B.
Hypothesis TCLSS : ReacDiscoClassifyOnSegment.treac_disco_classify_on_segment_spec B.
#[local] Notation DCTX := (d_ctx B MT XM_LIB RLO RHI tfib_K).

Lemma s1_seat : forall (fq : YK11.FPState) cx h i n now op nb fr len regs ly3 S3 (W : world SEGS) mem3 md3 k pc xs acs,
  DCTX cx ly3 S3 W mem3 md3 k -> cl_base B cx h i n now op nb fr len regs ly3 S3 W mem3 ->
  (forall E, d_E cx E -> Forall (YP09.chunk_ok SEGS (d_env cx E (cl_vals regs xs)) (rd W mem3) (d_A cx)) acs) ->
  regions_wf (d_kregions dsh_rec acs [] ++ []) = true -> regions_wf (s1_rs acs) = true ->
  exists E, d_E cx E /\
    st_ok_pi (fx := fq) SEGS VAL (d_env cx E (cl_vals regs xs)) (mkSS pc cl_sr (s1_rs acs) None (d_facts [] []))
      (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx h i n now op nb fr len regs ly3 S3 W mem3 md3 k pc xs acs HC HB3 HACS Hwf Hwf2.
pose proof HB3 as (_ & _ & _ & _ & _ & HrL & _ & _ & _ & _ & _ & _ & _ & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HE & HRG & HFL & _).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC) as (Hal16 & Hlo & Hhi & _).
pose proof asan_consts as (C1 & _).
pose proof (cl_A_range cx ltac:(clear - Hlo C1; unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (clear - Hlo Hhi HA1 C1; unfold MFRAME, LLVMF_STK in *; lia).
exists E. split; [exact HE|].
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E pc cl_sr (cl_vals regs xs) acs [] [] (d_facts [] [])
  HC HE HRG HFL (cl_regs_ok B cx E regs xs HE HrL HAr2)
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs xs) [] [] HC HE I I)
  (HACS E HE) (Forall_nil _) (Forall_nil _) I (Forall_nil _) Hwf) as HS0.
exact (st_ok_pi_submem _ _ _ (s1_rs acs) HS0 (s1_sub dsh_rec acs) Hwf2).
Qed.

Lemma s1_acs_ok : forall cx E regs fr (W : world SEGS) m,
  0 <= fr < 2 ^ 64 -> val_mem SEGS (rd W m) (d_A cx + 368) 8 fr ->
  Forall (YP09.chunk_ok SEGS (d_env cx E (cl_vals regs [w64 fr])) (rd W m) (d_A cx)) s1_acs.
Proof.
intros cx E regs fr W m Hfr Hv. unfold s1_acs. apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS (d_env cx E (cl_vals regs [w64 fr])) (rd W m) (d_A cx) 368 8 (SOff 563 0) fr).
- rewrite sv_denot_SOff0. exact (s1_env_xs cx E regs (w64 fr)).
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hfr.
- cbn. lia.
- exact Hv.
Qed.

Lemma s1_frbnd : forall cx h n fr len shf ly3 S3 (W : world SEGS) m md k,
  DCTX cx ly3 S3 W m md k -> d_body B cx h n (dxb fr len) shf ly3 S3 W m -> 0 <= fr < 2 ^ 64.
Proof.
intros cx h n fr len shf ly3 S3 W m md k HC HB.
destruct (Z.eq_dec fr 0) as [-> | Hne]; [lia|].
pose proof HB as (T0 & G0 & Lk0 & H0 & _ & _ & _ & Hbl & _).
assert (Hin : In (fr, len) (ablocks B ly3 S3)).
{ pose proof Hbl as (Hp & _). eapply Permutation_in; [apply Permutation_sym; exact Hp|].
  unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k HC)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR & _).
destruct (al_blocks SEGS B LAWS ly3 S3 W m md fr len HAR Hin) as (_ & Hfr0 & Hfrc & _ & _ & _ & Hn0).
pose proof (req_size_pos len (proj1 Hn0)) as Hrq.
pose proof asan_consts as (C1 & _). lia.
Qed.

Lemma s1_top : forall cx ly3 S3 (W : world SEGS) m md k, DCTX cx ly3 S3 W m md k ->
  d_S cx <= ly_top ly3 /\ alloc_ceiling <= ly_stk_lo ly3.
Proof.
intros cx ly3 S3 W m md k (Hbase & HJ & _).
destruct Hbase as ((HPRE & _) & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & _ & _ & _ & _ & Htop1 & _).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & _).
change (spZ (c_regs cx)) with (d_S cx) in *. rewrite Etop, Eslo. lia.
Qed.

Lemma s1_base_ext : forall cx h i n now op nb fr len regs regs' ly3 S3 (W : world SEGS) m m' md' k,
  cl_base B cx h i n now op nb fr len regs ly3 S3 W m ->
  DCTX cx ly3 S3 W m' md' k ->
  (forall x, m' x = m x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr regs' r = getr regs r) ->
  cl_base B cx h i n now op nb fr len regs' ly3 S3 W m'.
Proof.
intros cx h i n now op nb fr len regs regs' ly3 S3 W m m' md' k HB HC HM RG.
pose proof HB as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HsREC & HsOP & Hlen & Hnb & Hnbn & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _).
pose proof (s1_aview_ext W m m' HM) as Hav.
assert (VM : forall a q v, val_mem SEGS (rd W m) a q v -> val_mem SEGS (rd W m') a q v)
  by (intros a q v Hv; eapply YC88.val_mem_aview_kept_x; [intros x _; exact (Hav x) | exact Hv]).
assert (GA : forall p L, garr8 SEGS (rd W m) p L -> garr8 SEGS (rd W m') p L)
  by (intros p L HL; eapply YC88.garr8_aview_kept; [intros x _; exact (Hav x) | exact HL]).
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact Hop|]. split; [exact Hop2|].
split.
{ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27). unfold d_rL, spZ in *.
  rewrite !RG by (cbv; tauto). repeat split; assumption. }
split; [destruct Hsp0 as (P1 & P2); split; apply VM; assumption|].
split.
{ destruct Hfrm as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
  apply GA; exact F4. }
split; [destruct HsREC as (P1 & P2 & P3 & P4); split; [apply VM; exact P1|]; split; [apply VM; exact P2|];
  split; apply VM; assumption|].
split; [destruct HsOP as (P1 & P2); split; apply VM; assumption|].
split; [exact Hlen|]. split; [exact Hnb|]. split; [exact Hnbn|].
apply (BTOBS LAWS cx h n (dxb fr len) dsh_rec dsh_rec ly3 S3 W m ly3 S3 W m' md' k
  (d_S cx - LLVMF_STK) (d_S cx) [] (fun _ => False) Hbody).
- exact (conj (proj1 HC) (proj1 (proj2 HC))).
- lia.
- lia.
- intros a [].
- intros a _ _. exact (Hav a).
- apply Forall_nil.
- apply Permutation_refl.
- exact (cl_frame_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h dsh_rec W m ly3 S3 W m' md' k HC Hframe
    (fun a _ => Hav a)).
- exact (cl_shadow_keep cx dsh_rec W W m m' Hshadow (fun a _ => Hav a)).
Qed.

Lemma s1_sg_ext : forall cx nb len Sg (W : world SEGS) m m',
  (forall x, m' x = m x) -> cl_sg cx nb len Sg W m -> cl_sg cx nb len Sg W m'.
Proof.
intros cx nb len Sg W m m' HM (L1 & L2 & L3).
pose proof (s1_aview_ext W m m' HM) as Hav.
split; [exact L1|]. split; [|exact L3].
eapply YC88.garr8_aview_kept; [intros x _; exact (Hav x) | exact L2].
Qed.

Lemma s1_fblk : forall cx h n shf nb fr len ly3 S3 (W : world SEGS) m md k,
  DCTX cx ly3 S3 W m md k -> d_body B cx h n (dxb fr len) shf ly3 S3 W m -> d_frm cx nb fr len W m ->
  nb <= c_n cx -> len <= nb -> 50 <= len ->
  0 < fr /\ cls_read W m (d_A cx) fr 50 /\ cls_sep B ly3 S3 fr 50 /\
  garr8 SEGS (rd W m) fr (cls_bytes (slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)))) /\
  (fr + req_size len <= d_FB cx \/ d_FB cx + 4096 <= fr) /\ In (fr, len) (ablocks B ly3 S3).
Proof.
intros cx h n shf nb fr len ly3 S3 W m md k HC HB (F1 & F2 & F3 & F4) Hnbn Hlen H50.
pose proof HB as (T0 & G0 & Lk0 & H0 & _ & _ & _ & Hbl & _ & _ & _ & Hgeo & _).
pose proof Hgeo as (_ & _ & _ & _ & _ & G6 & _).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(clear - Hlo C1; unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (Hne : fr <> 0) by (intros E0; specialize (F2 E0); lia).
assert (Hin : In (fr, len) (ablocks B ly3 S3)).
{ pose proof Hbl as (Hp & _). eapply Permutation_in; [apply Permutation_sym; exact Hp|].
  unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
destruct (al_blocks SEGS B LAWS ly3 S3 W m md fr len HAR Hin) as (Hfr16 & Hfr0 & Hfrc & Hfra & Hfrp & _).
pose proof (req_size_pos len ltac:(lia)) as Hrq.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W m md fr len DFRAME_CLASS (c_fpos cx) HAR Hin Hfin) as Hd.
rewrite Efa, cl_fs6 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
split; [lia|]. split; [|split; [|split; [|split; [lia | exact Hin]]]].
- unfold cls_read. split; [lia|]. split; [pose proof alloc_ceiling_lt; lia|].
  split; [exact (amem_range_of_block SEGS B LAWS ly3 S3 W m md fr len fr 50 HAR Hin ltac:(lia) ltac:(lia))|].
  split; [right; unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia|].
  split; [intros a Ha; apply (Hfrp a); lia|].
  split; [exact (range_addressable_of_block SEGS B LAWS ly3 S3 W m md fr len fr 50 HAR Hin ltac:(lia) ltac:(lia))|].
  exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W m md fr len fr 50 HAR Hin ltac:(lia) ltac:(lia) ltac:(lia)).
- right. left. exists fr, len. split; [exact Hin|]. lia.
- unfold cls_bytes. rewrite cl_fb50 by (rewrite cl_rest_len; lia). apply cl_garr8_firstn. exact F4.
Qed.

Lemma s1_ret : forall cx h i n now op nb fr len (fq : YK11.FPState) ly3 S3 (W : world SEGS)
  (regs4 : bvmap 5 word) m4 md4 k acc pc lk (L : option (list byte)) (OB : list byte) (W2 : world SEGS) c2,
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W m4 md4 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= cl_kmax i -> acc <= cl_amax MT i ->
  cl_base B cx h i n now op nb fr len regs4 ly3 S3 W m4 ->
  getr regs4 1 = w64 (BASE + pc) -> spZ regs4 = d_A cx ->
  ((L = None /\ lk = 0) \/ (exists Lb, L = Some Lb /\ lk = d_obj cx OLOCK /\ lock_ok Lb)) ->
  tcls_post B fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W m4 k regs4 lk (d_obj cx OS) len
    (slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) (our_of (c_pl cx)) OB L W2 c2 ->
  cl_R B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len pc W2 c2.
Proof.
intros cx h i n now op nb fr len fq ly3 S3 W regs4 m4 md4 k acc pc lk L OB W2 c2
  Hb HFRM0 HJ3 Hfrs Hk Hacc HB3 R1 Hsp4 HL Hpost.
set (FB := slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) in *.
destruct Hpost as (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hc & _ & Hcsr2 & HJ2 & HPR & Hfr2 & Hperm2 & Hret & Hout & Hlock & HK).
change (k + EV_CLS) with (k + 0) in HJ2. rewrite Z.add_0_r in HJ2.
assert (HC3 : DCTX cx ly3 S3 W m4 md4 k) by (split; [exact Hb | split; [exact HJ3 | exact Hfrs]]).
assert (HC2 : DCTX cx ly2 S2 W2 mem2 md2 k) by (split; [exact Hb | split; [exact HJ2 | rewrite Hfr2; exact Hfrs]]).
pose proof HB3 as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HsREC & HsOP & Hlen & Hnb & Hnbn & Hbody).
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m4 md4 k HC3)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(clear - Hlo C1; unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
set (wr := cls_wr lk (d_obj cx OS) L).
assert (HK' : cl_kept B ly3 S3 W m4 W2 mem2 (d_A cx - CLS_STK) (d_A cx) wr)
  by (unfold tcls_kept in HK; rewrite Hsp4 in HK; exact HK).
assert (Hwr : forall a, wr a -> d_FB cx + 24 <= a < d_FB cx + DFRAME_SIZE).
{ intros a Ha. unfold wr, cls_wr in Ha. unfold DFRAME_SIZE.
  destruct HL as [(-> & ->) | (Lb & -> & -> & _)]; unfold d_obj in Ha; cbn [dobj_off] in Ha; destruct Ha as [Ha | Ha];
    [lia | destruct Ha | lia | cbn [dobj_off] in Ha; lia]. }
assert (Hwrc : forall a, wr a -> a < alloc_ceiling)
  by (intros a Ha; pose proof (Hwr a Ha); rewrite cl_fs6 in G2; unfold DFRAME_SIZE in *; lia).
assert (VA : forall o v, 0 <= o -> o + 8 <= 472 -> val_mem SEGS (rd W m4) (d_A cx + o) 8 v ->
  val_mem SEGS (rd W2 mem2) (d_A cx + o) 8 v).
{ intros o v Ho1 Ho2 Hv.
  exact (cl_slot_keep B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m4 md4 k W2 mem2 _ _ wr o v HC3 HK'
    ltac:(lia) Hwrc Ho1 Ho2 Hv). }
set (os := match L with None => [] | Some _ => [OLOCK] end).
assert (Hos : forall a, wr a -> d_rdset B cx h a -> Exists (fun o => d_objr cx o a) os).
{ intros a Ha Hrd. unfold wr, cls_wr in Ha. destruct (cl_objr_dec cx OLOCK a) as [Hlk | Hnlk].
  - destruct HL as [(EL & Elk) | (Lb & EL & Elk & _)].
    + exfalso. subst L lk. destruct Ha as [Ha | Ha]; [|destruct Ha].
      unfold d_obj in Ha. cbn [dobj_off] in Ha. unfold d_objr, d_obj in Hlk. cbn [dobj_off dobj_size] in Hlk. lia.
    + unfold os. rewrite EL. apply Exists_cons_hd. exact Hlk.
  - exfalso. apply (cl_s_not_rdset B tfib_K AIL KCAN cx h a Hgeo Hoff); [|exact Hnlk|exact Hrd].
    destruct HL as [(-> & ->) | (Lb & -> & -> & _)]; unfold d_obj in Ha; cbn [dobj_off] in Ha; destruct Ha as [Ha | Ha];
      [lia | destruct Ha | lia | cbn [dobj_off] in Ha; lia]. }
assert (Hnew : Forall (fun o => d_obj_new cx o W2 mem2) os).
{ unfold os. destruct HL as [(-> & ->) | (Lb & -> & -> & HLok)]; [apply Forall_nil|].
  apply Forall_cons; [|apply Forall_nil].
  destruct (slot_classify.sc_cm_lock FB len (our_of (c_pl cx)) Lb (slot_classify.fb50_len _) (proj1 HLok))
    as (Lb' & ELb & LLb).
  exists Lb'. split; [exact LLb|]. split; [exact (Hlock Lb' ELb)|].
  exact (s1_lock_ok FB len (our_of (c_pl cx)) Lb Lb' (slot_classify.fb50_len _) HLok ELb). }
unfold cl_R, d_at. exists fx', ly2, S2, regs2, mem2, md2, k, acc.
split; [rewrite Hc, R1; reflexivity|].
split; [destruct Hcsr2 as [E | E]; [rewrite E; exact HFRM0 | exact E]|].
split; [exact Hb|]. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|]. split; [exact Hk|].
split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); unfold cl_kmax in *; lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
exists (cm_ret FB len (our_of (c_pl cx)) L).
split; [|split].
- split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact Hop|]. split; [exact Hop2|].
  split.
  { unfold d_rL. unfold spZ in Hsp |- *.
    assert (E2 : getr regs2 2 = getr regs4 2) by exact (cl_cs regs4 regs2 2 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
    rewrite E2. split; [exact Hsp|].
    split; [exact (cl_cs regs4 regs2 3 _ HPR ltac:(unfold acallee_saved; lia) Hgp)|].
    split; [exact (cl_cs regs4 regs2 4 _ HPR ltac:(unfold acallee_saved; lia) Htp)|].
    split; [exact (cl_cs regs4 regs2 8 _ HPR ltac:(unfold acallee_saved; lia) H8)|].
    split; [exact (cl_cs regs4 regs2 9 _ HPR ltac:(unfold acallee_saved; lia) H9)|].
    split; [exact (cl_cs regs4 regs2 19 _ HPR ltac:(unfold acallee_saved; lia) H19)|].
    split; [exact (cl_cs regs4 regs2 18 _ HPR ltac:(unfold acallee_saved; lia) H18)|].
    split; [exact (cl_cs regs4 regs2 20 _ HPR ltac:(unfold acallee_saved; lia) H20)|].
    exact (cl_cs regs4 regs2 27 _ HPR ltac:(unfold acallee_saved; lia) H27). }
  split; [destruct Hsp0 as (P1 & P2); split; apply VA; first [lia | assumption]|].
  split; [exact (cl_frm_keep B MT XM_LIB RLO RHI tfib_K LAWS cx nb fr len ly3 S3 W m4 md4 k W2 mem2 _ _ wr h n dsh_rec
    HC3 Hbody HK' ltac:(intros a Ha; pose proof (Hwr a Ha); unfold DFRAME_SIZE in *; lia) Hfrm)|].
  split; [destruct HsREC as (P1 & P2 & P3 & P4); split; [apply VA; [lia | lia | exact P1]|];
    split; [apply VA; [lia | lia | exact P2]|]; split; apply VA; first [lia | assumption]|].
  split; [destruct HsOP as (P1 & P2); split; apply VA; first [lia | assumption]|].
  split; [exact Hlen|]. split; [exact Hnb|]. split; [exact Hnbn|].
  exact (cl_body_call B MT XM_LIB RLO RHI tfib_K LAWS AIL KCAN cx h n (dxb fr len) dsh_rec ly3 S3 W m4 md4 k
    ly2 S2 W2 mem2 md2 k _ _ wr os Hbody HC3 HC2 HK'
    ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia)
    ltac:(lia) Hwr Hos Hnew Hperm2 BTOBS).
- exact Hret.
- destruct (slot_classify.sc_cm_ret_cases FB len (our_of (c_pl cx)) L) as [EE | EE]; [left; exact EE|].
  right. split; [exact EE|]. exists (cm_out FB len (our_of (c_pl cx)) L OB).
  destruct (slot_classify.sc_sight FB len (our_of (c_pl cx)) L (slot_classify.fb50_len _) EE) as (Hsf & Hl24 & _ & _).
  destruct (slot_classify.sc_cm_ret0 FB len (our_of (c_pl cx)) L OB EE) as (_ & _ & _ & Eout).
  unfold cl_sg. rewrite Eout in Hout |- *.
  split; [exact Hl24|]. split; [exact Hout|].
  assert (H50 : 50 <= len) by exact (proj1 Hsf).
  assert (EF : FB = cl_F (c_pl cx) nb len).
  { unfold FB, cl_F. apply cl_fb50. rewrite cl_rest_len; [lia | pose proof Hfrm as (FF1 & _); lia | lia]. }
  rewrite <- EF. exact Hsf.
Qed.

Theorem pb_cl_L1 : cl_L1_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len W c Hin Hop0 Hnbn.
unfold cls_in, d_arm_at_pf in Hin. rewrite Hop0 in Hin. cbn [Z.eqb] in Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (Hi & Hn & Hnow & HrL & HR & HX & Hsp0 & Hbody).
destruct HX as (_ & Hop2 & Hfrm & HsREC & HsOP & Hlen & Hnb).
assert (HB3 : cl_base B cx h i n now op nb fr len regs ly3 S3 W mem3).
{ split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [left; exact Hop0|].
  split; [exact Hop2|]. split; [exact HrL|]. split; [exact Hsp0|]. split; [exact Hfrm|].
  split; [exact HsREC|]. split; [exact HsOP|]. split; [exact Hlen|]. split; [exact Hnb|].
  split; [exact Hnbn|]. exact Hbody. }
assert (HC : DCTX cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(clear - Hlo C1; unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (clear - Hlo Hhi HA1 C1; unfold MFRAME, LLVMF_STK in *; lia).
assert (Hfrb : 0 <= fr < 2 ^ 64) by exact (s1_frbnd cx h n fr len dsh_rec ly3 S3 W mem3 md3 k HC Hbody).
destruct (s1_seat fq cx h i n now op nb fr len regs ly3 S3 W mem3 md3 k CLS_OFF [w64 fr] s1_acs HC HB3
  (fun E _ => s1_acs_ok cx E regs fr W mem3 Hfrb (proj1 (proj2 (proj2 HsREC))))
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (E & HE & HS).
pose proof HE as (EE & E32 & HEimg & E60 & EFB & ESH).
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs [w64 fr])))
  by (unfold d_env; apply img_env_havoc_hi; [exact HEimg | unfold A_LIM, AT_FL; lia]).
assert (EF : ew (d_env cx E (cl_vals regs [w64 fr])) 516 = w64 (d_FB cx))
  by (unfold d_env; rewrite ew_havoc_old by (unfold AT_FL; lia); exact EFB).
pose proof (cl_regs_ok B cx E regs [w64 fr] HE HrL HAr2) as HROK.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNC.
unfold cfg_at. change (w64 (BASE + CLS_OFF)) with (Z_to_bv 64 (BASE + CLS_OFF)).
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hpt.
clear HF HFr HG.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS), (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (R1 : getr (ms_regs ms) 1 = w64 (BASE + 0xec0)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  unfold w64. exact (codeptr_val _ 3776 HEI). }
assert (A10 : getr (ms_regs ms) 10 = w64 fr).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  rewrite sv_denot_SOff0. exact (s1_env_xs cx E regs (w64 fr)). }
assert (A11 : getr (ms_regs ms) 11 = w64 len).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS), <- (proj2 HR), (HROK 12%bv).
  f_equal; vm_compute; reflexivity. }
assert (A12 : getr (ms_regs ms) 12 = w64 (d_obj cx OOUR)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 12%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite EF. unfold w64, d_obj. cbn [dobj_off]. rewrite s1_w64_add. reflexivity. }
assert (A13 : getr (ms_regs ms) 13 = w64 (d_obj cx OS)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 13%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite EF. unfold w64, d_obj. cbn [dobj_off]. rewrite s1_w64_add. reflexivity. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (s1_base_ext cx h i n now op nb fr len regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) md4 k HB3 HC4 Hpt RG)
  as HB4.
pose proof HB4 as (_ & _ & _ & _ & _ & HrL4 & _ & Hfrm4 & _ & _ & _ & _ & _ & Hbody4).
pose proof HrL4 as (Hsp4 & Hgp4 & Htp4 & H84 & _).
pose proof Hbody4 as (T4 & G4 & Lk4 & H4 & Hframe4 & Hshadow4 & Hobjs4 & Hblocks4 & Hinput4 & Himg4 & Hoff4 & Hgeo4
  & Hcan4 & Hstk4 & Hawr4).
pose proof Hframe4 as (E4 & HdE4 & Hregs4 & _).
pose proof Hobjs4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HGour & _).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k HC4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres4 & _ & _ & HAR4 & _ & _ & _).
destruct (cl_achain B MT XM_LIB XN_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k E4 (d_A cx) HC4 HdE4
  (Forall_inv Hregs4) ltac:(unfold MFRAME in HA1; lia)) as (ch & Hch).
destruct (cl_garr8_ex (w_H W) (ms_mem ms) (d_obj cx OS) 24
  ltac:(intros a Ha; apply HFpres4; unfold d_obj in Ha; cbn [dobj_off] in Ha; lia)) as (OB & LOB & HOB).
destruct (s1_top cx ly3 S3 W (ms_mem ms) md4 k HC4) as (Htop & Hslo).
assert (Es0 : s0Z (ms_regs ms) = d_S cx)
  by (unfold s0Z; rewrite H84; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (HFB8 : d_FB cx mod 4 = 0) by (rewrite <- (Z.mod_mod (d_FB cx) 32) in HFal by lia; lia).
pose proof Hgeo4 as (_ & GG2 & _). rewrite cl_fs6 in GG2.
rewrite (pa_sigma_reac_disco_classify (PI := PI)) in HS.
pmkst HS.
eapply SRr_bind.
{ apply (TCLS fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md4 k (ms_regs ms) ch fr len (d_obj cx OOUR) (d_obj cx OS)
    (slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) (our_of (c_pl cx)) OB HJ Himg4).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
    rewrite unsigned_lit_small by lia. pose proof (@pa_base_lo _ _ PL_both3_0 PI).
    unfold YImgTop.IMG_LO in *. lia.
  - exact Hgp4.
  - exact Htp4.
  - exact A10.
  - exact A11.
  - exact A12.
  - exact A13.
  - rewrite Hsp4, Es0. exact Hch.
  - rewrite Hsp4. lia.
  - rewrite Hsp4. unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *. lia.
  - rewrite Hsp4. unfold MFRAME in HA1. lia.
  - rewrite Hsp4. unfold MFRAME in HA1. lia.
  - rewrite Hfrs. cbn [length Z.of_nat]. unfold CLS_DEPTH. lia.
  - pose proof Hfrm4 as (F1 & _). unfold REC_MAX in F1. lia.
  - apply slot_classify.fb50_len.
  - apply s1_len_our.
  - exact LOB.
  - intros H50. destruct (s1_fblk cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k HC4 Hbody4 Hfrm4 Hnbn Hlen H50)
      as (Hf0 & Hfr & Hfs & Hfg & _). rewrite Hsp4. exact (conj Hf0 (conj Hfr (conj Hfs Hfg))).
  - rewrite Hsp4. exact (cl_cread_obj B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k OOUR (d_A cx)
      HC4 Hshadow4 ltac:(vm_compute; reflexivity)
      ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia)).
  - left. exists DFRAME_CLASS, (c_fpos cx). split; [exact Hfin|]. rewrite Efa, cl_fs6. unfold d_obj. cbn [dobj_off]. lia.
  - exact HGour.
  - unfold d_obj. cbn [dobj_off]. lia.
  - unfold d_obj. cbn [dobj_off]. rewrite Z.add_mod by lia. rewrite HFB8. reflexivity.
  - rewrite Hsp4. exact (cl_cread_obj B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k OS (d_A cx)
      HC4 Hshadow4 ltac:(vm_compute; reflexivity)
      ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia)).
  - exact HOB.
  - intros a Ha. apply (proj1 (Hawr4 a ltac:(unfold d_obj in Ha; cbn [dobj_off] in Ha; unfold DFRAME_SIZE; lia))).
  - left. unfold d_obj. cbn [dobj_off]. lia.
  - unfold d_obj. cbn [dobj_off]. lia.
  - intros H50. destruct (s1_fblk cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k HC4 Hbody4 Hfrm4 Hnbn Hlen H50)
      as (_ & _ & _ & _ & Hsep & _). pose proof (req_size_pos len ltac:(lia)). unfold d_obj. cbn [dobj_off]. lia. }
intros W2 c2 _ Hpost. apply SRr_ret.
exact (s1_ret cx h i n now op nb fr len fq ly3 S3 W (ms_regs ms) (ms_mem ms) md4 k acc 0xec0 0 None OB W2 c2
  Hbase HFRM0 HJ Hfrs Hk Hacc HB4 R1 Hsp4 (or_introl (conj eq_refl eq_refl)) Hpost).
Qed.

Theorem pb_cl_L2 : cl_L2_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len W c Hin Hop0 Hnbn.
unfold cls_in, d_arm_at_pf in Hin. rewrite Hop0 in Hin. cbn [Z.eqb] in Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (Hi & Hn & Hnow & HrL & HR & HX & Hsp0 & Hbody).
destruct HX as (_ & Hop2 & Hfrm & HsREC & HsOP & Hlen & Hnb).
assert (HB3 : cl_base B cx h i n now op nb fr len regs ly3 S3 W mem3).
{ split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [right; exact Hop0|].
  split; [exact Hop2|]. split; [exact HrL|]. split; [exact Hsp0|]. split; [exact Hfrm|].
  split; [exact HsREC|]. split; [exact HsOP|]. split; [exact Hlen|]. split; [exact Hnb|].
  split; [exact Hnbn|]. exact Hbody. }
assert (HC : DCTX cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(clear - Hlo C1; unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (clear - Hlo Hhi HA1 C1; unfold MFRAME, LLVMF_STK in *; lia).
assert (Hfrb : 0 <= fr < 2 ^ 64) by exact (s1_frbnd cx h n fr len dsh_rec ly3 S3 W mem3 md3 k HC Hbody).
destruct (s1_seat fq cx h i n now op nb fr len regs ly3 S3 W mem3 md3 k CLSS_OFF [w64 fr] s1_acs HC HB3
  (fun E _ => s1_acs_ok cx E regs fr W mem3 Hfrb (proj1 (proj2 (proj2 HsREC))))
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (E & HE & HS).
pose proof HE as (EE & E32 & HEimg & E60 & EFB & ESH).
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs [w64 fr])))
  by (unfold d_env; apply img_env_havoc_hi; [exact HEimg | unfold A_LIM, AT_FL; lia]).
assert (EF : ew (d_env cx E (cl_vals regs [w64 fr])) 516 = w64 (d_FB cx))
  by (unfold d_env; rewrite ew_havoc_old by (unfold AT_FL; lia); exact EFB).
pose proof (cl_regs_ok B cx E regs [w64 fr] HE HrL HAr2) as HROK.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNC.
unfold cfg_at. change (w64 (BASE + CLSS_OFF)) with (Z_to_bv 64 (BASE + CLSS_OFF)).
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hpt.
clear HF HFr HG.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS), (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (R1 : getr (ms_regs ms) 1 = w64 (BASE + 0xed8)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  unfold w64. exact (codeptr_val _ 3800 HEI). }
assert (A10 : getr (ms_regs ms) 10 = w64 (d_obj cx OLOCK)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite EF. unfold w64, d_obj. cbn [dobj_off]. rewrite s1_w64_add. reflexivity. }
assert (A11 : getr (ms_regs ms) 11 = w64 fr).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  rewrite sv_denot_SOff0. exact (s1_env_xs cx E regs (w64 fr)). }
assert (A12 : getr (ms_regs ms) 12 = w64 len).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 12%bv HS), <- (proj2 HR), (HROK 12%bv).
  f_equal; vm_compute; reflexivity. }
assert (A13 : getr (ms_regs ms) 13 = w64 (d_obj cx OOUR)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 13%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite EF. unfold w64, d_obj. cbn [dobj_off]. rewrite s1_w64_add. reflexivity. }
assert (A14 : getr (ms_regs ms) 14 = w64 (d_obj cx OS)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 14%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite EF. unfold w64, d_obj. cbn [dobj_off]. rewrite s1_w64_add. reflexivity. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (s1_base_ext cx h i n now op nb fr len regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) md4 k HB3 HC4 Hpt RG)
  as HB4.
pose proof HB4 as (_ & _ & _ & _ & _ & HrL4 & _ & Hfrm4 & _ & _ & _ & _ & _ & Hbody4).
pose proof HrL4 as (Hsp4 & Hgp4 & Htp4 & H84 & _).
pose proof Hbody4 as (T4 & G4 & Lk4 & H4 & Hframe4 & Hshadow4 & Hobjs4 & Hblocks4 & Hinput4 & Himg4 & Hoff4 & Hgeo4
  & Hcan4 & Hstk4 & Hawr4).
pose proof Hframe4 as (E4 & HdE4 & Hregs4 & _).
pose proof Hobjs4 as (_ & _ & _ & _ & _ & _ & LLk & GLk & QLk & HGour & _).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k HC4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres4 & _ & _ & HAR4 & _ & _ & _).
destruct (cl_achain B MT XM_LIB XN_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k E4 (d_A cx) HC4 HdE4
  (Forall_inv Hregs4) ltac:(unfold MFRAME in HA1; lia)) as (ch & Hch).
destruct (cl_garr8_ex (w_H W) (ms_mem ms) (d_obj cx OS) 24
  ltac:(intros a Ha; apply HFpres4; unfold d_obj in Ha; cbn [dobj_off] in Ha; lia)) as (OB & LOB & HOB).
destruct (s1_top cx ly3 S3 W (ms_mem ms) md4 k HC4) as (Htop & Hslo).
assert (Es0 : s0Z (ms_regs ms) = d_S cx)
  by (unfold s0Z; rewrite H84; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (HFB8 : d_FB cx mod 4 = 0) by (rewrite <- (Z.mod_mod (d_FB cx) 32) in HFal by lia; lia).
pose proof Hgeo4 as (_ & GG2 & _). rewrite cl_fs6 in GG2.
rewrite (pa_sigma_reac_disco_classify_on_segment (PI := PI)) in HS.
pmkst HS.
eapply SRr_bind.
{ apply (TCLSS fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md4 k (ms_regs ms) ch (d_obj cx OLOCK) fr len
    (d_obj cx OOUR) (d_obj cx OS)
    (slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) (our_of (c_pl cx)) OB (Some Lk4) HJ Himg4).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
    rewrite unsigned_lit_small by lia. pose proof (@pa_base_lo _ _ PL_both3_0 PI).
    unfold YImgTop.IMG_LO in *. lia.
  - exact Hgp4.
  - exact Htp4.
  - exact A10.
  - exact A11.
  - exact A12.
  - exact A13.
  - exact A14.
  - rewrite Hsp4, Es0. exact Hch.
  - rewrite Hsp4. lia.
  - rewrite Hsp4. unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *. lia.
  - rewrite Hsp4. unfold MFRAME in HA1. lia.
  - rewrite Hsp4. unfold MFRAME in HA1. lia.
  - rewrite Hfrs. cbn [length Z.of_nat]. unfold CLS_DEPTH. lia.
  - pose proof Hfrm4 as (F1 & _). unfold REC_MAX in F1. lia.
  - apply slot_classify.fb50_len.
  - apply s1_len_our.
  - exact LOB.
  - intros H50. destruct (s1_fblk cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k HC4 Hbody4 Hfrm4 Hnbn Hlen H50)
      as (Hf0 & Hfr & Hfs & Hfg & _). rewrite Hsp4. exact (conj Hf0 (conj Hfr (conj Hfs Hfg))).
  - rewrite Hsp4. exact (cl_cread_obj B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k OOUR (d_A cx)
      HC4 Hshadow4 ltac:(vm_compute; reflexivity)
      ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia)).
  - left. exists DFRAME_CLASS, (c_fpos cx). split; [exact Hfin|]. rewrite Efa, cl_fs6. unfold d_obj. cbn [dobj_off]. lia.
  - exact HGour.
  - unfold d_obj. cbn [dobj_off]. lia.
  - unfold d_obj. cbn [dobj_off]. rewrite Z.add_mod by lia. rewrite HFB8. reflexivity.
  - rewrite Hsp4. exact (cl_cread_obj B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k OS (d_A cx)
      HC4 Hshadow4 ltac:(vm_compute; reflexivity)
      ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia)).
  - exact HOB.
  - intros a Ha. apply (proj1 (Hawr4 a ltac:(unfold d_obj in Ha; cbn [dobj_off] in Ha; unfold DFRAME_SIZE; lia))).
  - left. unfold d_obj. cbn [dobj_off]. lia.
  - split; [unfold d_obj; cbn [dobj_off]; lia|].
    split; [unfold d_obj; cbn [dobj_off]; rewrite Z.add_mod by lia; rewrite HFB8; reflexivity|].
    split; [exact LLk|].
    split; [rewrite Hsp4; exact (cl_cread_obj B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k OLOCK (d_A cx)
      HC4 Hshadow4 ltac:(vm_compute; reflexivity)
      ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia))|].
    split; [exact GLk|].
    split; [intros a Ha; apply (proj1 (Hawr4 a ltac:(unfold d_obj in Ha; cbn [dobj_off] in Ha; unfold DFRAME_SIZE; lia)))|].
    left. unfold d_obj. cbn [dobj_off]. lia.
  - unfold d_obj. cbn [dobj_off]. lia.
  - intros H50. destruct (s1_fblk cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k HC4 Hbody4 Hfrm4 Hnbn Hlen H50)
      as (_ & _ & _ & _ & Hsep & _). pose proof (req_size_pos len ltac:(lia)). unfold d_obj. cbn [dobj_off]. lia.
  - split; [unfold d_obj; cbn [dobj_off]; lia|].
    split; [unfold d_obj; cbn [dobj_off]; lia|].
    intros H50. destruct (s1_fblk cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k HC4 Hbody4 Hfrm4 Hnbn Hlen H50)
      as (_ & _ & _ & _ & Hsep & _). pose proof (req_size_pos len ltac:(lia)). unfold d_obj. cbn [dobj_off]. lia. }
intros W2 c2 _ Hpost. apply SRr_ret.
exact (s1_ret cx h i n now op nb fr len fq ly3 S3 W (ms_regs ms) (ms_mem ms) md4 k acc 0xed8 (d_obj cx OLOCK)
  (Some Lk4) OB W2 c2 Hbase HFRM0 HJ Hfrs Hk Hacc HB4 R1 Hsp4
  (or_intror (ex_intro _ Lk4 (conj eq_refl (conj eq_refl QLk)))) Hpost).
Qed.

Theorem pb_cl_L3 : cl_L3_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  r & HB3 & Hr10 & Hrr).
pose proof HB3 as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HsREC & HsOP & Hlen & Hnb & Hnbn & Hbody).
assert (HC : DCTX cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(clear - Hlo C1; unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (clear - Hlo Hhi HA1 C1; unfold MFRAME, LLVMF_STK in *; lia).
destruct (s1_seat fq cx h i n now op nb fr len regs ly3 S3 W mem3 md3 k 0xec0 ([] : list word) ([] : list YP09.chunk)
  HC HB3 (fun E _ => Forall_nil _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (E & HE & HS).
pose proof HE as (EE & E32 & HEimg & E60 & EFB & ESH).
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs [])))
  by (unfold d_env; apply img_env_havoc_hi; [exact HEimg | unfold A_LIM, AT_FL; lia]).
pose proof (cl_regs_ok B cx E regs [] HE HrL HAr2) as HROK.
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
unfold cfg_at. change (w64 (BASE + 0xec0)) with (Z_to_bv 64 (BASE + 0xec0)).
paj_run_to_sh RUNTO HS HJ 0xed8.
{ awr_ok_tac. }
pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hpt.
clear HF HFr HG.
assert (RG : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 10; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r0 = getr regs r0).
{ intros r0 Hr0. rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r0 HS), (HROK r0).
  cbv [In] in Hr0. repeat (destruct Hr0 as [<-|Hr0]; [f_equal; vm_compute; reflexivity|]). destruct Hr0. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (s1_base_ext cx h i n now op nb fr len regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) md4 k HB3 HC4 Hpt
  ltac:(intros r0 Hr0; apply RG; cbv [In] in Hr0 |- *; tauto)) as HB4.
pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc] in Hms.
apply SRr_ret. rewrite Hms. unfold cl_R, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc.
split; [reflexivity|]. split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
exists r. split; [exact HB4|].
split; [rewrite RG by (cbv; tauto); exact Hr10|].
destruct Hrr as [E1 | (E0 & Sg & HSg)]; [left; exact E1|].
right. split; [exact E0|]. exists Sg. exact (s1_sg_ext cx nb len Sg W mem3 (ms_mem ms) Hpt HSg).
Qed.

End h.
End f.
End d.
