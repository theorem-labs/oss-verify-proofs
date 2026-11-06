(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 390 of its 421 lines of code are new or changed and 38 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody
ClassifyCore ReacDiscoClassify ReacDiscoClassifyOnSegment CheckSighting ReacDiscoGateShouldPush DiscoEntClsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition cl10_acs : list YP09.chunk :=
  [YP09.mkChunk 408 (CVal 8 (SOff 563 0)); YP09.mkChunk 392 (CVal 8 (SOff 564 0));
   YP09.mkChunk 224 (CVal 8 (SOff 565 0)); YP09.mkChunk 248 (CVal 8 (SOff 566 0));
   YP09.mkChunk 368 (CVal 8 (SOff 567 0)); YP09.mkChunk 336 (CVal 8 (SOff 568 0));
   YP09.mkChunk 280 (CVal 8 (SOff 569 0))].
Definition cl10_rs : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ cl10_acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 3007 3008 (dfhdr_chunks ++ []);
   fshadow_region AT_SH DFRAME_CLASS 0 0 (dsh_chunks dsh_rec);
   got_regionP; bcell_regionP 32].
Definition cl10_wchk (rs : smem) : bool :=
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    (obase_eqb (YP09.r_base r) (Some AT_F) && (YP09.r_wlo r =? 3007) && (YP09.r_whi r =? 3008))) rs.
Definition cl10_xs (op sop push cur nb len fr : Z) : list word :=
  [w64 op; w64 sop; w64 push; w64 cur; w64 nb; w64 len; w64 fr].
Definition cl10_keep (F : Z) (m0 m : word -> option byte) : Prop :=
  (forall x : word, bv_unsigned x <> F -> m x = m0 x) /\ mem_grows m0 m.

Lemma cl10_sub : submem cl10_rs (d_kregions dsh_rec cl10_acs [] ++ []).
Proof.
unfold cl10_rs, d_kregions, fshadow_region. cbn [app]. unfold DFRAME_SIZE.
repeat (apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
  split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|]).
apply submem_nil.
Qed.

Lemma cl10_wr : forall E rs a, cl10_wchk rs = true -> in_wrange E rs a -> a = base_val E (Some AT_F) + 3007.
Proof.
intros E rs a Hc (r & Hin & Ha). unfold cl10_wchk in Hc. rewrite forallb_forall in Hc. specialize (Hc r Hin).
apply orb_true_iff in Hc as [Hc | Hc]; [apply Z.leb_le in Hc; lia|].
apply andb_true_iff in Hc as [Hc Hhi]. apply andb_true_iff in Hc as [Hb Hlo].
apply Z.eqb_eq in Hlo, Hhi.
destruct (YP09.r_base r) as [nb|] eqn:Eb; [|discriminate Hb]. simpl in Hb. apply Nat.eqb_eq in Hb. subst nb.
lia.
Qed.

Lemma cl10_kstep : forall E rs F (m0 m1 m2 : word -> option byte),
  frame_of E rs m1 m2 -> mem_grows m1 m2 -> cl10_keep F m0 m1 ->
  base_val E (Some AT_F) + 3007 = F -> cl10_wchk rs = true -> cl10_keep F m0 m2.
Proof.
intros E rs F m0 m1 m2 Hfr Hg (K & G) HF Hc. split.
- intros x Hx. rewrite <- (K x Hx). apply Hfr. intros Hw. apply Hx. rewrite <- HF. exact (cl10_wr E rs _ Hc Hw).
- exact (mem_grows_trans _ _ _ G Hg).
Qed.

Ltac cl10_eqs HE :=
  let rec go j :=
    lazymatch j with
    | 24%nat => idtac
    | 15%nat => go 16%nat
    | _ => let E := fresh "E" in pose proof (HE j ltac:(lia) ltac:(lia)) as E; cbn [nth] in E; subst; go (Datatypes.S j)
    end in go 0%nat.

Lemma cl10_sf : forall (X Y F U : list byte) len st, length X = 24%nat -> length Y = 24%nat ->
  (forall j, (j < 24)%nat -> j <> 15%nat -> nth j Y (CtrlParsed.zb 0) = nth j X (CtrlParsed.zb 0)) ->
  sighting_facts X F U len st -> sighting_facts Y F U len st.
Proof.
intros X Y F U len st HX HY HE HF.
do 24 (destruct X as [|? X]; [discriminate HX|]). destruct X; [|discriminate HX].
do 24 (destruct Y as [|? Y]; [discriminate HY|]). destruct Y; [|discriminate HY].
cl10_eqs HE.
unfold sighting_facts, disco_classify_c.sighting_ok, CtrlParsed.fld, CtrlParsed.fu, CtrlParsed.fb in *.
cbn [firstn skipn nth length] in *. exact HF.
Qed.

Lemma cl10_w64_mod : forall v, Z_to_bv 64 (v mod 2 ^ 64) = Z_to_bv 64 v.
Proof.
intros v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

Lemma cl10_atom : forall {rc : YM05.RunCeil} {PI : PAImg disco_listing} cx E regs xs j, (j < length xs)%nat ->
  ew (d_env cx E (cl_vals regs xs)) (563 + j) = nth j xs (Z_to_bv 64 0).
Proof.
intros rc PI cx E regs xs j Hj. replace (563 + j)%nat with (AT_X + (32 + j))%nat by (unfold AT_X; lia).
rewrite d_env_x by (unfold cl_vals; rewrite length_app, length_map, length_seq; lia).
unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. f_equal. lia.
Qed.

Ltac cl10_awr EFB HAW :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat);
      [reflexivity | exact EFB | cbn [YP09.r_wlo YP09.r_whi]; exact HAW |] ].

Ltac cl10_step Kold Knew EB :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  lazymatch goal with HG : mem_grows _ _ |- _ =>
  pose proof (cl10_kstep _ _ _ _ _ _ HFr HG Kold EB ltac:(vm_compute; reflexivity)) as Knew;
  clear HFr HG Kold end end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end.

Ltac cl10_reg HS r :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?H ?msx) =>
  rewrite (st_ok_pi_restrict_reg H Ex ssx msx r HS);
  let v := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with v end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma cl10_vm_mod : forall m a v, val_mem SEGS m a 8 v -> val_mem SEGS m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H j Hj. rewrite (H j Hj). unfold YO0f.le_byte.
replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma cl10_byte_eq : forall m a (b1 b2 : byte), val_mem SEGS m a 1 (bv_unsigned b1) -> val_mem SEGS m a 1 (bv_unsigned b2) -> b1 = b2.
Proof.
intros m a b1 b2 H1 H2. pose proof (H1 0%nat ltac:(lia)) as E1. pose proof (H2 0%nat ltac:(lia)) as E2.
rewrite E1 in E2.
assert (E : Z_to_bv 8 (YO0f.le_byte (bv_unsigned b1) 1 0) = Z_to_bv 8 (YO0f.le_byte (bv_unsigned b2) 1 0))
  by congruence.
pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2.
change (bv_modulus 8) with 256 in R1, R2.
rewrite !le_byte_1 in E by lia. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DCAN : asink_img_laws SEGS B tfib_K /\ ak_canary tfib_K = AE2k.FF_canary.

Definition cl10_mem (cx : dcx) (h i n now nb fr len : Z) (ly3 : alayout) (S3 : astate) (W : world SEGS)
  (m : word -> option byte) : Prop :=
  d_sp0 cx i now W m /\ d_frm cx nb fr len W m /\
  val_mem SEGS (rd W m) (d_A cx + 248) 8 (d_cur cx nb) /\ val_mem SEGS (rd W m) (d_A cx + 336) 8 len /\
  val_mem SEGS (rd W m) (d_A cx + 368) 8 nb /\ val_mem SEGS (rd W m) (d_A cx + 280) 8 fr /\
  (exists Sg, cl_sg cx nb len Sg W m) /\ d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W m.

Lemma cl10_rL : forall (fq : YK11.FPState) cx E ss ms (H : word -> bool) regs,
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict H ms) -> regs_ok E cl_sr regs -> d_rL B cx regs ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> sr_get (ss_regs ss) r = sr_get cl_sr r) ->
  d_rL B cx (ms_regs ms).
Proof.
intros fq cx E ss ms H regs HS HR HL Hs.
assert (K : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), (Hs r Hr). symmetry. exact (HR r). }
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25). unfold d_rL, spZ in *.
rewrite (K 2%bv), (K 3%bv), (K 4%bv), (K 8%bv), (K 9%bv), (K 18%bv), (K 20%bv), (K 25%bv)
  by (cbv [In]; repeat (first [left; reflexivity | right])).
repeat split; assumption.
Qed.

Lemma cl10_leaf : forall (fq : YK11.FPState) (cx : dcx) h i n now op nb fr len push Sg ly3 S3 (W : world SEGS)
  regs0 mem3 md3 k E vals ss ms md',
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] -> d_E cx E ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss (restrict (w_H W) ms) ->
  d_land_chk dsh_rec (ss_mem ss) = true ->
  cl_base B cx h i n now op nb fr len regs0 ly3 S3 W mem3 -> cl_sg cx nb len Sg W mem3 ->
  cl_spl cx nb fr len push W mem3 ->
  cl10_keep (d_FB cx + 3007) (rd W mem3) (rd W (ms_mem ms)) ->
  cl10_mem cx h i n now nb fr len ly3 S3 W (ms_mem ms).
Proof.
intros fq cx h i n now op nb fr len push Sg ly3 S3 W regs0 mem3 md3 k E vals ss ms md'
  HB HJ0 HJ1 HFR HE HS Hchk Hcb Hsg Hspl (KP & KG).
assert (HC0 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HB | split; [exact HJ0 | exact HFR]]).
assert (HC1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md' k)
  by (split; [exact HB | split; [exact HJ1 | exact HFR]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC0)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
unfold MFRAME in HA1. unfold LLVMF_STK in Hlo.
pose proof Hcb as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbc & Hbody).
pose proof Hspl as (H224 & Hpush & H280 & H336 & H368).
pose proof Hsg as (HSgl & HSg & HSf).
pose proof Hbody as (T & G & Lk & Hh & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & _ & Hstk & Hawr).
pose proof Hframe as (E0 & HdE0 & Hregs0 & Hflag0 & H216 & H152).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> a <> d_FB cx + 3007 ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hne. apply aview_eq_of. apply KP. rewrite unsigned_lit_small by lia. exact Hne. }
assert (KV : forall a nn v, 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
  (d_FB cx + 3007 < a \/ a + Z.of_nat nn <= d_FB cx + 3007) ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W (ms_mem ms)) a nn v).
{ intros a nn v Ha0 Ha1 Ha2 Hv j Hj.
  rewrite (mbyte_of_aview SEGS _ _ _ _ _ (KA (a + Z.of_nat j) ltac:(lia) ltac:(lia))). exact (Hv j Hj). }
assert (KA8 : forall off v, 0 <= off -> off + 8 <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) 8 v).
{ intros off v Ho1 Ho2 Hv. apply KV; [lia | change (Z.of_nat 8) with 8; lia | left; lia | exact Hv]. }
assert (H216' : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 216) 8 h) by (apply KA8; [lia | lia | exact H216]).
assert (H152' : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 152) 8 (h + 440)) by (apply KA8; [lia | lia | exact H152]).
destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_rec ly3 S3 W md' k (d_env cx E vals) ss ms HC1
  (d_E_env cx E vals HE) (d_env_fl cx E vals) HS Hchk H216' H152') as [Hframe1 Hshadow1].
assert (Hbody1 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms)).
{ apply (d_body_rt B cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx)
    (fun a => a = d_FB cx + 3007) Hbody).
  - unfold LLVMF_STK. lia.
  - lia.
  - cbv beta. intros a ->. right. apply (cl_s_not_rdset B tfib_K DCAN cx h _ Hgeo Hoff); [lia|].
    unfold d_objr, d_obj. cbn [dobj_off dobj_size]. lia.
  - intros a Ha Hne. exact (KA a Ha Hne).
  - intros a _ Hp. exact (apresent_grows _ _ _ a KG Hp).
  - exact Hframe1.
  - exact Hshadow1.
  - lia. }
assert (Hfrm1 : d_frm cx nb fr len W (ms_mem ms)).
{ destruct Hfrm as (F1 & F2 & Fnb & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fnb|].
  destruct (Z.eq_dec fr 0) as [Efr | Hne].
  - subst fr. rewrite (F2 eq_refl). intros j Hj. rewrite length_map, length_firstn in Hj. lia.
  - assert (Hin : In (fr, len) (ablocks B ly3 S3)).
    { pose proof Hblocks as (Hp & _). eapply Permutation_in; [apply Permutation_sym; exact Hp|].
      unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
    destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 fr len HAR Hin) as (_ & Hb1 & Hb2 & _).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 fr len DFRAME_CLASS (c_fpos cx) HAR Hin Hfin) as Hd.
    rewrite Efa, fs6 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof (req_size_pos len ltac:(lia)) as Hrq.
    eapply YC88.garr8_aview_kept; [|exact F3]. intros a Ha.
    rewrite length_map, length_firstn in Ha.
    apply KA; lia. }
assert (HpS : forall a, d_obj cx OS <= a < d_obj cx OS + Z.of_nat 24 -> apresent (w_H W) (ms_mem ms) a).
{ intros a Ha. apply (apresent_grows _ _ _ a KG). apply HFpres. unfold d_obj in Ha. cbn [dobj_off] in Ha. lia. }
destruct (cl_garr8_ex (w_H W) (ms_mem ms) (d_obj cx OS) 24 HpS) as (L & HLl & HLg).
assert (Enth : forall (X : list byte) j, (j < length X)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) X) 0 = bv_unsigned (nth j X (CtrlParsed.zb 0))).
{ intros X j Hj. rewrite (nth_indep _ 0 (bv_unsigned (CtrlParsed.zb 0))) by (rewrite length_map; exact Hj).
  apply (map_nth (fun b : byte => bv_unsigned b)). }
assert (HLS : forall j, (j < 24)%nat -> j <> 15%nat -> nth j L (CtrlParsed.zb 0) = nth j Sg (CtrlParsed.zb 0)).
{ intros j Hj Hne.
  destruct (HLg j ltac:(rewrite length_map; lia)) as (V1 & _).
  destruct (HSg j ltac:(rewrite length_map; lia)) as (V2 & _).
  rewrite Enth in V1 by lia. rewrite Enth in V2 by lia.
  apply (cl10_byte_eq (rd W (ms_mem ms)) (d_obj cx OS + Z.of_nat j)); [exact V1|].
  apply KV; [unfold d_obj; cbn [dobj_off]; lia | unfold d_obj; cbn [dobj_off]; change (Z.of_nat 1) with 1; lia | | exact V2].
  unfold d_obj. cbn [dobj_off]. change (Z.of_nat 1) with 1. lia. }
assert (HsgL : cl_sg cx nb len L W (ms_mem ms))
  by (split; [exact HLl | split; [exact HLg | exact (cl10_sf Sg L _ _ _ _ HSgl HLl HLS HSf)]]).
unfold cl10_mem. split; [|split; [exact Hfrm1|]].
- destruct Hsp0 as (S1 & S2). split; apply KA8; try lia; assumption.
- split; [apply KA8; [lia | lia | exact H248]|]. split; [apply KA8; [lia | lia | exact H336]|].
  split; [apply KA8; [lia | lia | exact H368]|]. split; [apply KA8; [lia | lia | exact H280]|].
  split; [exists L; exact HsgL | exact Hbody1].
Qed.

Lemma cl10_fin_obs : forall (fq : YK11.FPState) (cx : dcx) h i n now op nb fr len push Sg ly3 S3 (W : world SEGS)
  regs0 mem3 md3 k acc E vals ss ms md',
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= cl_kmax i -> st_nev S3 <= st_nev (c_S cx) + cl_kmax i ->
  mo_le MT (c_S cx) S3 acc -> acc <= cl_amax MT i -> d_E cx E ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> ss_pc ss = OBS_OFF -> d_land_chk dsh_rec (ss_mem ss) = true ->
  cl_base B cx h i n now op nb fr len regs0 ly3 S3 W mem3 -> cl_sg cx nb len Sg W mem3 ->
  cl_spl cx nb fr len push W mem3 ->
  cl10_keep (d_FB cx + 3007) (rd W mem3) (rd W (ms_mem ms)) ->
  d_rL B cx (ms_regs ms) -> dR_obs cx (ms_regs ms) ->
  cl_post B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W (mkCfg ms md').
Proof.
intros fq cx h i n now op nb fr len push Sg ly3 S3 W regs0 mem3 md3 k acc E vals ss ms md'
  Hf0 HB HJ0 HJ1 HFR Hk Hnev Hmo Hacc HE HS Hrv Hpc Hchk Hcb Hsg Hspl HK HrL HrO.
destruct (cl10_leaf fq cx h i n now op nb fr len push Sg ly3 S3 W regs0 mem3 md3 k E vals ss ms md'
  HB HJ0 HJ1 HFR HE HS Hchk Hcb Hsg Hspl HK)
  as (Hsp0 & Hfrm & H248 & H336 & H368 & H280 & (L & HLl & HLg & HLf) & Hbody).
pose proof Hcb as (Hi & Hn & Hnow & Hop & Hop2 & _ & _ & _ & _ & _ & _ & Hlen & Hnb & _).
unfold cl_post. left. exists L. unfold obs_in, d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite (st_ok_pi_restrict_mkst (w_H W) _ _ ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
split; [exact Hf0|]. split; [exact HB|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact HrL|]. split; [exact HrO|].
split; [|split; [exact Hsp0 | exact Hbody]].
exact (conj Hop (conj Hop2 (conj Hfrm (conj HLl (conj HLg (conj HLf (conj H248 (conj H336 (conj H368
  (conj H280 (conj Hlen Hnb))))))))))).
Qed.

Lemma cl10_fin_r27 : forall (fq : YK11.FPState) (cx : dcx) h i n now op nb fr len push Sg ly3 S3 (W : world SEGS)
  regs0 mem3 md3 k acc E vals ss ms md',
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= cl_kmax i -> st_nev S3 <= st_nev (c_S cx) + cl_kmax i ->
  mo_le MT (c_S cx) S3 acc -> acc <= cl_amax MT i -> d_E cx E ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> ss_pc ss = R27_OFF -> d_land_chk dsh_rec (ss_mem ss) = true ->
  cl_base B cx h i n now op nb fr len regs0 ly3 S3 W mem3 -> cl_sg cx nb len Sg W mem3 ->
  cl_spl cx nb fr len push W mem3 ->
  cl10_keep (d_FB cx + 3007) (rd W mem3) (rd W (ms_mem ms)) ->
  d_rL B cx (ms_regs ms) ->
  getr (ms_regs ms) 14 = w64 (d_cur cx nb) -> getr (ms_regs ms) 24 = w64 len -> getr (ms_regs ms) 23 = w64 nb ->
  getr (ms_regs ms) 27 = w64 fr -> getr (ms_regs ms) 22 = w64 (d_obj cx OS) ->
  getr (ms_regs ms) 26 = w64 (d_obj cx OOUR) ->
  cl_post B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W (mkCfg ms md').
Proof.
intros fq cx h i n now op nb fr len push Sg ly3 S3 W regs0 mem3 md3 k acc E vals ss ms md'
  Hf0 HB HJ0 HJ1 HFR Hk Hnev Hmo Hacc HE HS Hrv Hpc Hchk Hcb Hsg Hspl HK HrL R14 R24 R23 R27 R22 R26.
destruct (cl10_leaf fq cx h i n now op nb fr len push Sg ly3 S3 W regs0 mem3 md3 k E vals ss ms md'
  HB HJ0 HJ1 HFR HE HS Hchk Hcb Hsg Hspl HK)
  as (Hsp0 & Hfrm & _ & _ & _ & _ & _ & Hbody).
pose proof Hcb as (Hi & Hn & Hnow & Hop & Hop2 & _ & _ & _ & _ & _ & _ & Hlen & Hnb & _).
unfold cl_post. right. unfold r27_in, d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite (st_ok_pi_restrict_mkst (w_H W) _ _ ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
split; [exact Hf0|]. split; [exact HB|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hi|]. split; [lia|]. split; [exact Hnow|]. split; [exact HrL|].
split; [exact (conj R14 (conj R24 (conj R23 (conj R27 (conj R22 R26)))))|].
split; [exact (conj Hfrm (conj Hlen eq_refl))|]. split; [exact Hsp0|].
exact (cl_body_n B cx h n (nb - len) (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) Hbody ltac:(lia)).
Qed.

Theorem cl_L10 : cl_L10_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold cl_L10_stmt. intros cx h i n now op nb fr len W c Hx.
unfold cl_X, d_at in Hx.
destruct Hx as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & HB & HJ & HFR & Hk & Hnev & Hmo & Hacc &
  Sg & push & Hcb & Hsg & Hspl).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
pose proof HJ as HJ0.
pose proof Hcb as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbc & Hbody).
pose proof Hspl as (H224 & Hpush & H280 & H336 & H368).
pose proof Hbody as (T & G & Lk & Hh & Hframe & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hawr).
pose proof Hframe as (E & HE & HRG & HFL & _ & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC) as (Hal16 & Hlo & Hhi & HF0 & HFc & _).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (RA : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose (xs := cl10_xs op (if op <? 128 then op else op - 256) push (d_cur cx nb) nb len fr).
pose (vals := cl_vals regs xs).
pose proof (cl_regs_ok B cx E regs xs HE HrL RA) as HROK.
assert (AX : forall j, (j < 7)%nat -> ew (d_env cx E vals) (563 + j) = nth j xs (Z_to_bv 64 0))
  by (intros j Hj; exact (cl10_atom cx E regs xs j Hj)).
pose proof (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HC HE I I) as HFACTS.
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) cl10_acs).
{ unfold cl10_acs. repeat apply Forall_cons; try apply Forall_nil.
  all: let ck j v Hv := apply (chunk_ok_val SEGS _ _ _ _ 8 _ (v mod 2 ^ 64));
    [ rewrite sv_denot_SOff0, cl10_w64_mod; exact (AX j ltac:(lia))
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia
    | cbn; lia
    | apply cl10_vm_mod; exact Hv ] in
    first [ ck 0%nat op H408 | ck 1%nat (if op <? 128 then op else op - 256) H392 | ck 2%nat push H224
          | ck 3%nat (d_cur cx nb) H248 | ck 4%nat nb H368 | ck 5%nat len H336 | ck 6%nat fr H280 ]. }
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0xdd0 cl_sr vals
  cl10_acs [] [] (d_facts [] []) HC HE HRG HFL HROK HFACTS HACS (Forall_nil _) (Forall_nil _) I (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ cl10_rs HS0 cl10_sub ltac:(vm_compute; reflexivity)) as HS. clear HS0.
pose proof (d_E_env cx E vals HE) as HEd. pose proof HEd as (_ & _ & HEI & _).
assert (EFB : bv_unsigned (ew (d_env cx E vals) 516) = d_FB cx).
{ rewrite d_env_old by (unfold AT_FL; lia). pose proof HE as (_ & _ & _ & _ & HF & _). unfold AT_F in HF.
  rewrite HF. try unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in Hlo. lia. }
assert (EB : base_val (d_env cx E vals) (Some AT_F) + 3007 = d_FB cx + 3007)
  by (change AT_F with 516%nat; cbn [base_val]; rewrite EFB; reflexivity).
assert (HAW : forall a, d_FB cx + 3007 <= a < d_FB cx + 3008 ->
  awr_byte LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3
    [(DFRAME_CLASS, c_fpos cx)] a)
  by (intros a Ha; exact (proj1 (Hawr a ltac:(unfold DFRAME_SIZE; lia)))).
assert (K0 : cl10_keep (d_FB cx + 3007) (rd W mem3) (rd W mem3))
  by (split; [intros x _; reflexivity | apply mem_grows_refl]).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_disco) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + 0xdd0)) with (Z_to_bv 64 (BASE + 0xdd0)).
let rLt HSx := (apply (cl10_rL fq cx _ _ _ _ regs HSx HROK HrL); intros r Hr; cbv [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]); destruct Hr) in
let fobs HSx K := (
  apply SRr_ret;
  apply (cl10_fin_obs fq cx h i n now op nb fr len push Sg ly3 S3 W regs mem3 md3 k acc E vals _ _ _
    Hf0 HB HJ0 HJ HFR Hk Hnev Hmo Hacc HE HSx eq_refl eq_refl ltac:(vm_compute; reflexivity) Hcb Hsg Hspl K);
  [ rLt HSx
  | split; [ cl10_reg HSx (22%bv : bv 5); cbn [sv_denot]; rewrite EFB; reflexivity
           | cl10_reg HSx (26%bv : bv 5); cbn [sv_denot]; rewrite EFB; reflexivity ] ]) in
let fr27 HSx K := (
  apply SRr_ret;
  apply (cl10_fin_r27 fq cx h i n now op nb fr len push Sg ly3 S3 W regs mem3 md3 k acc E vals _ _ _
    Hf0 HB HJ0 HJ HFR Hk Hnev Hmo Hacc HE HSx eq_refl eq_refl ltac:(vm_compute; reflexivity) Hcb Hsg Hspl K);
  [ rLt HSx
  | cl10_reg HSx (14%bv : bv 5); rewrite sv_denot_SOff0; exact (AX 3%nat ltac:(lia))
  | cl10_reg HSx (24%bv : bv 5); rewrite sv_denot_SOff0; exact (AX 5%nat ltac:(lia))
  | cl10_reg HSx (23%bv : bv 5); rewrite sv_denot_SOff0; exact (AX 4%nat ltac:(lia))
  | cl10_reg HSx (27%bv : bv 5); rewrite sv_denot_SOff0; exact (AX 6%nat ltac:(lia))
  | cl10_reg HSx (22%bv : bv 5); cbn [sv_denot]; rewrite EFB; reflexivity
  | cl10_reg HSx (26%bv : bv 5); cbn [sv_denot]; rewrite EFB; reflexivity ]) in
paj_run_to_sh RUNTO HS HJ OBS_OFF; [cl10_awr EFB HAW | cl10_step K0 K1 EB;
  apply (BR W _ _ _ _ _ BC_EQ (SAlu ALU_AND (SOff 563 0) (SLit 16)) (SLit 0) HS); intros Hc1 HS1;
  (paj_run_to_sh RUNTO HS1 HJ OBS_OFF; [cl10_awr EFB HAW | cl10_step K1 K2 EB;
    apply (BR W _ _ _ _ _ BC_EQ (SAlu ALU_OR (SOff 565 0) (SAlu ALU_AND (SOff 563 0) (SLit 4))) (SLit 0) HS1);
    intros Hc2 HS2;
    [ paj_run_to_sh RUNTO HS2 HJ R27_OFF; [cl10_awr EFB HAW | cl10_step K2 K3 EB; fr27 HS2 K3]
    | paj_run_to_sh RUNTO HS2 HJ OBS_OFF; [cl10_awr EFB HAW | cl10_step K2 K3 EB; fobs HS2 K3] ] ]) ].
Qed.

End h.
End f.
End d.
