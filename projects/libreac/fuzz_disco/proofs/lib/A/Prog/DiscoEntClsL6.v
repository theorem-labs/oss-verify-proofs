(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 413 of its 443 lines of code are new or changed and 39 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require GateModel CtrlParsed slot_classify.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition cl6_sr : list sv := sr_set cl_sr 19%bv (SOff AT_F 2624).
Definition cl6_acs : list YP09.chunk :=
  [YP09.mkChunk 232 (CVal 8 (SOff 564 0)); YP09.mkChunk 248 (CVal 8 (SOff 566 0)); YP09.mkChunk 344 (CVal 8 (SOff 565 0))].
Definition cl6_fcs : list YP09.chunk := [YP09.mkChunk 2880 (CVal 4 (SOff 563 0))].
Definition cl6_wchk (rs : smem) : bool :=
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    (YP09.obase_eqb (YP09.r_base r) (Some 60%nat) && (224 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 376))) rs.

Ltac cl6_in := cbv [In]; repeat (first [left; reflexivity | right]).

Ltac cl6_win HS n lo hi :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HR := fresh "HR" in
pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HR;
let HW := fresh "HW" in let HW2 := fresh "HW2" in
pose proof (region_ok_rewindow _ Ex _ r lo hi HR) as HW;
lazymatch type of HW with ?P -> _ =>
  assert (HW2 : P) by (intros o Ho; destruct HR as (_ & _ & HW0 & _); apply HW0; cbn [YP09.r_wlo YP09.r_whi]; lia) end;
specialize (HW HW2);
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r lo hi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) HW) as HS3;
clear HS HR HW HW2; rename HS3 into HS; norm_ss HS end.

Ltac cl6_r60 HS HR :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 60%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HR end.

Ltac cl6_awr cx U60 HAS :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
  [ reflexivity | rewrite U60; lia | cbn [YP09.r_wlo YP09.r_whi]; unfold LLVMF_STK; lia
  | cbn [YP09.r_wlo YP09.r_whi]; lia | ] ].

Ltac cl6_br BR W HS c ra rb :=
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
    let a := eval vm_compute in (sr_get (ss_regs s) ra) in
    let b := eval vm_compute in (sr_get (ss_regs s) rb) in
    apply (BR W _ _ _ _ _ c a b HS)
  end.

Ltac cl6_reg HS r :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?s (restrict ?H ?m) =>
    rewrite (st_ok_pi_restrict_reg H E s m r HS);
    let e := eval vm_compute in (sr_get (ss_regs s) r) in change (sr_get (ss_regs s) r) with e
  end.

Ltac cl6_keep HS HROK :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS), (HROK r);
  cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr.

Lemma cl6_atom : forall E sr regs (r : bv 5) n v, regs_ok E sr regs -> sr_get sr r = SOff n 0 ->
  getr regs r = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E sr regs r n v HR Hs Hg. rewrite <- sv_denot_SOff0, <- Hs, <- (HR r). exact Hg. Qed.

Lemma cl6_soff0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. rewrite denot_lit_U, (U_atom E n v H Hv). reflexivity. Qed.

Lemma cl6_lit_mod : forall v, Z_to_bv 64 (v mod 2 ^ 64) = Z_to_bv 64 v.
Proof.
intros v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

Lemma cl6_soffm : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 (v mod 2 ^ 64).
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply cl6_lit_mod. Qed.

Lemma cl6_frame : forall E rs (m m' : word -> option byte) A, frame_of E rs m m' -> cl6_wchk rs = true ->
  bv_unsigned (ew E 60) = A -> forall x : word, ~ (A + 224 <= bv_unsigned x < A + 376) -> m' x = m x.
Proof.
intros E rs m m' A HF Hc HA x Hx. apply HF. intros (r & Hin & Ha).
unfold cl6_wchk in Hc. rewrite forallb_forall in Hc. specialize (Hc r Hin).
apply orb_true_iff in Hc as [Hc | Hc]; [apply Z.leb_le in Hc; lia|].
apply andb_true_iff in Hc as [Hc H2]. apply andb_true_iff in Hc as [H0 H1].
apply YP09.obase_eqb_eq in H0. rewrite H0 in Ha. cbn [base_val] in Ha. rewrite HA in Ha.
apply Z.leb_le in H1, H2. lia.
Qed.

Lemma cl6_usx : forall E q v, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff q 0)) = v.
Proof.
intros E q v H Hv. rewrite U_SExt, (U_atom E q v H) by lia. cbv beta iota.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small v (2 ^ 32)) by lia. rewrite (Z.mod_small (v + 2 ^ 32 / 2) (2 ^ 32)) by lia.
replace (v + 2 ^ 32 / 2 - 2 ^ 32 / 2) with v by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma cl6_dec : forall E q v, ew E q = Z_to_bv 64 v -> 1 <= v < 2 ^ 31 ->
  sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff q 0)) (SLit (-1))) = Z_to_bv 64 (v - 1).
Proof.
intros E q v H Hv. rewrite denot_lit_U. f_equal. rewrite U_SAlu, (cl6_usx E q v H), U_SLit by lia. cbn [zalu_raw].
unfold zcanon, M64. rewrite Z.add_mod_idemp_r by lia. rewrite Z.mod_small by lia. lia.
Qed.

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

Definition cl6_xs (cx : dcx) (g i now nb : Z) : list word := [w64 g; w64 i; w64 now; w64 (d_cur cx nb)].

Lemma cl6_ex : forall cx E regs xs j, (j < length xs)%nat ->
  ew (d_env cx E (cl_vals regs xs)) (563 + j) = nth j xs (Z_to_bv 64 0).
Proof.
intros cx E regs xs j Hj. replace (563 + j)%nat with (AT_X + (32 + j))%nat by (unfold AT_X; lia).
rewrite d_env_x by (unfold cl_vals; rewrite length_app, length_map, length_seq; lia).
unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. replace (32 + j - 32)%nat with j by lia. reflexivity.
Qed.

Lemma cl6_vm_mod : forall (m : word -> option byte) a v, val_mem SEGS m a 8 (v mod 2 ^ 64) <-> val_mem SEGS m a 8 v.
Proof.
intros m a v. unfold val_mem, YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma cl6_fld : forall E m lo hi wlo whi cs A od q v,
  region_ok SEGS E m (YP09.mkRegion (Some 60%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 60) = A ->
  In (YP09.mkChunk od (CVal 8 (SOff q 0))) cs -> ew E q = Z_to_bv 64 v -> val_mem SEGS m (A + od) 8 v.
Proof.
intros E m lo hi wlo whi cs A od q v HR HA Hin Hq. apply (proj1 (cl6_vm_mod m (A + od) v)).
change 8%nat with (N.to_nat 8).
apply (field_of_region E m 60%nat A cs lo hi wlo whi od 8%N (SOff q 0) (v mod 2 ^ 64) HR HA Hin).
- apply cl6_soffm. exact Hq.
- change (8 * Z.of_N 8) with 64. apply Z.mod_pos_bound. lia.
- change (Z.of_N 8) with 8. lia.
Qed.

Lemma cl6_av : forall (W : world SEGS) (m mf : word -> option byte) lo hi,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mf x = m x) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) mf a = aview SEGS (w_H W) m a.
Proof.
intros W m mf lo hi MF a Ha Hn. apply aview_eq_of. unfold mrestrict.
rewrite MF; [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma cl6_kvm : forall (W : world SEGS) (m mf : word -> option byte) A a v,
  (forall x : word, ~ (A + 224 <= bv_unsigned x < A + 376) -> mf x = m x) ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= A + 224 \/ A + 376 <= a) ->
  val_mem SEGS (rd W m) a 8 v -> val_mem SEGS (rd W mf) a 8 v.
Proof.
intros W m mf A a v MF H0 H1 H2 HV. eapply YC88.val_mem_aview_kept_x; [|exact HV].
intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply (cl6_av W m mf (A + 224) (A + 376) MF); lia.
Qed.

Section h.
Variable B : asyms.

Lemma cl6_rL : forall cx regs regs', d_rL B cx regs ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr regs' r = getr regs r) -> d_rL B cx regs'.
Proof.
intros cx regs regs' (L2 & L3 & L4 & L8 & L9 & L18 & L20 & L25) K. unfold d_rL, spZ in *.
rewrite (K 2%bv), (K 3%bv), (K 4%bv), (K 8%bv), (K 9%bv), (K 18%bv), (K 20%bv), (K 25%bv) by cl6_in.
repeat split; assumption.
Qed.

Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).

Lemma cl6_land : forall (fq : YK11.FPState) (cx : dcx) (pc kmax accmax : Z)
  (P : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop)
  (W : world SEGS) ly3 S3 md' k acc E ss ms,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax -> mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  (forall md, P (ms_regs ms) ly3 S3 W (ms_mem ms) md) ->
  DAT cx pc kmax accmax P W (mkCfg ms md').
Proof.
intros fq cx pc kmax accmax P W ly3 S3 md' k acc E ss ms Hf0 HB HJ HFR Hk Hev Hmo Hacc HS Hrv Hpc HP.
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact Hf0|].
split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|]. exact (HP md').
Qed.

Lemma cl6_post : forall cx h i n now op nb fr len regs ly3 S3 (W : world SEGS) mem3 md3 k0 Sg G push regsf mf,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k0 ->
  cl_base B cx h i n now op nb fr len regs ly3 S3 W mem3 -> cl_sg cx nb len Sg W mem3 -> cl_gate cx G W mem3 ->
  0 <= push <= 1 ->
  (forall x : word, ~ (d_A cx + 224 <= bv_unsigned x < d_A cx + 376) -> mf x = mem3 x) ->
  (forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mf a) ->
  d_frame cx h dsh_rec W mf -> d_shadow cx dsh_rec W mf ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr regsf r = getr regs r) ->
  val_mem SEGS (rd W mf) (d_A cx + 232) 8 i -> val_mem SEGS (rd W mf) (d_A cx + 344) 8 now ->
  val_mem SEGS (rd W mf) (d_A cx + 248) 8 (d_cur cx nb) ->
  val_mem SEGS (rd W mf) (d_A cx + 224) 8 push -> val_mem SEGS (rd W mf) (d_A cx + 280) 8 fr ->
  val_mem SEGS (rd W mf) (d_A cx + 336) 8 len -> val_mem SEGS (rd W mf) (d_A cx + 368) 8 nb ->
  cl_base B cx h i n now op nb fr len regsf ly3 S3 W mf /\ cl_sg cx nb len Sg W mf /\ cl_gate cx G W mf /\
  cl_spl cx nb fr len push W mf.
Proof.
intros cx h i n now op nb fr len regs ly3 S3 W mem3 md3 k0 Sg G push regsf mf HC
  (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbc & Hbody)
  (HSl & HSga & HSf) (HGl & HGa & HGok) Hpush MF MG Hfr' Hsh' K V232 V344 V248 V224 V280 V336 V368.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k0 HC)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & _).
unfold MFRAME, LLVMF_STK in HAr, HSlo.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 224 <= a < d_A cx + 376) ->
  aview SEGS (w_H W) mf a = aview SEGS (w_H W) mem3 a) by exact (cl6_av W mem3 mf _ _ MF).
assert (AVlo : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) mf a = aview SEGS (w_H W) mem3 a)
  by (intros a Ha; apply AV; lia).
refine (conj _ (conj _ (conj _ _))).
- unfold cl_base.
  refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj (cl6_rL cx regs regsf HrL K) (conj (conj V232 V344)
    (conj _ (conj V248 (conj _ (conj _ (conj Hlen (conj Hnb (conj Hnbc _)))))))))))))).
  + destruct Hfrm as (F1 & F2 & Fnb & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fnb|].
    destruct (Z.eq_dec fr 0) as [E0 | Hne].
    * subst fr. rewrite (F2 eq_refl). intros j Hj. rewrite length_map, length_firstn in Hj. lia.
    * pose proof Hbody as (_ & _ & _ & _ & _ & _ & _ & Hbl & _).
      assert (Hin : In (fr, len) (ablocks B ly3 S3)).
      { pose proof Hbl as (Hp & _). eapply Permutation_in; [apply Permutation_sym; exact Hp|].
        unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
      destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 fr len HAR Hin) as (_ & H4096 & Hceil & _).
      pose proof (req_size_pos len ltac:(lia)) as Hrq.
      eapply YC88.garr8_aview_kept; [|exact F3]. intros a Ha.
      rewrite length_map in Ha.
      assert (Hl : Z.of_nat (length (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) <= len)
        by (rewrite length_firstn; lia).
      apply AVlo. lia.
  + eapply YC88.val_mem_aview_kept_x; [|exact H408]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply AV; lia.
  + eapply YC88.val_mem_aview_kept_x; [|exact H392]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply AV; lia.
  + apply (d_body_rt B cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 mf (d_A cx) (d_A cx + 472)
      (fun a => d_A cx + 224 <= a < d_A cx + 376) Hbody).
    * unfold LLVMF_STK. lia.
    * lia.
    * intros a Ha. left. lia.
    * intros a Ha HR. exact (AV a Ha HR).
    * intros a _ Hp. exact (MG a Hp).
    * exact Hfr'.
    * exact Hsh'.
    * lia.
- refine (conj HSl (conj _ HSf)). eapply YC88.garr8_aview_kept; [|exact HSga]. intros a Ha.
  rewrite length_map, HSl in Ha. change (Z.of_nat 24) with 24 in Ha. unfold d_obj in Ha. cbn [dobj_off] in Ha. apply AVlo. lia.
- refine (conj HGl (conj _ HGok)). eapply YC88.garr8_aview_kept; [|exact HGa]. intros a Ha.
  rewrite length_map, HGl in Ha. change (Z.of_nat 264) with 264 in Ha. unfold d_obj in Ha. cbn [dobj_off] in Ha. apply AVlo. lia.
- exact (conj V224 (conj Hpush (conj V280 (conj V336 V368)))).
Qed.

Ltac cl6_after cx U60 M G :=
  lazymatch goal with HF : frame_of _ _ (ms_mem _) (ms_mem _) |- _ =>
    let M0 := fresh "M0" in pose proof (cl6_frame _ _ _ _ (d_A cx) HF) as M0;
    lazymatch type of M0 with cl6_wchk ?rs = true -> _ =>
      let Hw := fresh "Hw" in assert (Hw : cl6_wchk rs = true) by (vm_compute; reflexivity);
      pose proof (M0 Hw U60) as M; clear M0 Hw HF end end;
  lazymatch goal with HG : mem_grows _ _ |- _ => rename HG into G end;
  lazymatch goal with HFr : frame_of _ _ _ _ |- _ => clear HFr end.

Theorem cl_L6 : cl_L6_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold cl_L6_stmt. intros cx h i n now op nb fr len W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k0 & acc & -> & Hf0 & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
  Sg & G & push & HBS & HRC & H19 & HSG & HGT & H10 & Hpush).
pose proof HBS as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbc & Hbody).
pose proof HRC as (H27 & H24 & H23 & H26 & H22).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & _ & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
pose proof HGT as (HGL & HGa & HGok).
pose proof HGok as (_ & HGn & _).
pose proof HdE as (_ & _ & _ & E60 & E516 & _).
unfold AT_A, AT_F in E60, E516.
pose proof Hsp0 as (V232 & V344).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k0) by (split; [exact HB | split; [exact HJ | exact HFR]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k0 HC)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HAS : d_S cx - 640 <= d_A cx <= d_S cx - 576) by (unfold MFRAME in HAr; lia).
assert (Hfu : CtrlParsed.fu G 256 4 = gn G).
{ pose proof (GateModel.fu_rng4 G 256 ltac:(rewrite HGL; lia)) as R. revert HGn.
  unfold gn, CtrlParsed.s32. destruct (Z.ltb_spec (CtrlParsed.fu G 256 4) (2 ^ 31)); lia. }
assert (VG : val_mem SEGS (rd W mem3) (d_FB cx + 2880) 4 (gn G)).
{ rewrite <- Hfu. replace (d_FB cx + 2880) with (d_obj cx OG + Z.of_nat 256)
    by (change (Z.of_nat 256) with 256; unfold d_obj; cbn [dobj_off]; lia).
  apply gsp_val_mem; [exact HGa | rewrite HGL; lia]. }
set (V := cl_vals regs (cl6_xs cx (gn G) i now nb)).
assert (X0 : ew (d_env cx E V) 563 = Z_to_bv 64 (gn G))
  by exact (cl6_ex cx E regs (cl6_xs cx (gn G) i now nb) 0 ltac:(cbn; lia)).
assert (X1 : ew (d_env cx E V) 564 = Z_to_bv 64 i)
  by exact (cl6_ex cx E regs (cl6_xs cx (gn G) i now nb) 1 ltac:(cbn; lia)).
assert (X2 : ew (d_env cx E V) 565 = Z_to_bv 64 now)
  by exact (cl6_ex cx E regs (cl6_xs cx (gn G) i now nb) 2 ltac:(cbn; lia)).
assert (X3 : ew (d_env cx E V) 566 = Z_to_bv 64 (d_cur cx nb))
  by exact (cl6_ex cx E regs (cl6_xs cx (gn G) i now nb) 3 ltac:(cbn; lia)).
assert (U60 : bv_unsigned (ew (d_env cx E V) 60) = d_A cx).
{ rewrite d_env_old by (unfold AT_FL; lia). rewrite E60. unfold w64. apply unsigned_lit_small. exact HAr2. }
assert (A516 : ew (d_env cx E V) 516 = Z_to_bv 64 (d_FB cx)) by (rewrite d_env_old by (unfold AT_FL; lia); exact E516).
assert (HROK : regs_ok (d_env cx E V) cl6_sr regs).
{ unfold cl6_sr. apply (regs_ok_rereg _ cl_sr regs 19%bv (SOff AT_F 2624));
    [exact (cl_regs_ok B cx E regs (cl6_xs cx (gn G) i now nb) HdE HrL HAr2) | reflexivity |].
  rewrite H19. cbn [sv_denot]. unfold AT_F. rewrite A516, unsigned_lit_small by lia. reflexivity. }
assert (HFCS : Forall (YP09.chunk_ok SEGS (d_env cx E V) (rd W mem3) (d_FB cx)) cl6_fcs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ _ 4 _ (gn G)); [apply cl6_soff0; [exact X0 | lia] | cbn; lia | cbn; lia | exact VG]. }
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E V) (rd W mem3) (d_A cx)) cl6_acs).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ i);
      [apply cl6_soff0; [exact X1 | unfold MAX_OPS in Hi; lia] | cbn; unfold MAX_OPS in Hi; lia | cbn; lia | exact V232].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ (d_cur cx nb mod 2 ^ 64));
      [apply cl6_soffm; exact X3 | change (8 * Z.of_N 8) with 64; apply Z.mod_pos_bound; lia | cbn; lia |
       exact (proj2 (cl6_vm_mod _ _ _) H248)].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ now); [apply cl6_soff0; [exact X2 | lia] | cbn; lia | cbn; lia | exact V344]. }
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k0 E 0xd40 cl6_sr
  V cl6_acs cl6_fcs [] (d_facts [] []) HC HdE Hregs Hflag HROK
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k0 E V [] [] HC HdE I I)
  HACS HFCS (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
cl_ro_base HS 516%nat. cl_ro_base HS 529%nat. cl6_win HS 60%nat 224 376.
pose proof (d_E_env cx E V HdE) as HEd. pose proof HEd as (_ & _ & HEI & _).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_disco) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (A541 : ew (d_env cx E V) 541 = Z_to_bv 64 push)
  by exact (cl6_atom _ _ _ 10%bv 541%nat push HROK ltac:(vm_compute; reflexivity) H10).
assert (A558 : ew (d_env cx E V) 558 = Z_to_bv 64 fr)
  by exact (cl6_atom _ _ _ 27%bv 558%nat fr HROK ltac:(vm_compute; reflexivity) H27).
assert (A555 : ew (d_env cx E V) 555 = Z_to_bv 64 len)
  by exact (cl6_atom _ _ _ 24%bv 555%nat len HROK ltac:(vm_compute; reflexivity) H24).
assert (A554 : ew (d_env cx E V) 554 = Z_to_bv 64 nb)
  by exact (cl6_atom _ _ _ 23%bv 554%nat nb HROK ltac:(vm_compute; reflexivity) H23).
unfold cfg_at. change (w64 (BASE + 0xd40)) with (Z_to_bv 64 (BASE + 0xd40)).
paj_run_to_sh RUNTO HS HJ 0xdd0; [cl6_awr cx U60 HAS|].
cl6_after cx U60 M1 G1.
cl6_br BR W HS BC_LTU (11%bv : bv 5) (10%bv : bv 5); intros Hc1 HS1; clear HS;
  rewrite branch_ltu_U, (U_atom _ 541%nat push A541), U_lit in Hc1 by lia.
2: { apply Z.ltb_ge in Hc1. lia. }
apply Z.ltb_lt in Hc1.
paj_run_to_sh RUNTO HS1 HJ 0xdd0; [cl6_awr cx U60 HAS|].
cl6_after cx U60 M2 G2.
cl6_br BR W HS1 BC_GEU (10%bv : bv 5) (24%bv : bv 5); intros Hc2 HS2; clear HS1;
  rewrite branch_geu_U, U_lit, (cl6_usx _ 563%nat (gn G) X0) in Hc2 by lia.
2: { apply negb_false_iff, Z.ltb_lt in Hc2. lia. }
apply negb_true_iff, Z.ltb_ge in Hc2.
paj_run_to_sh RUNTO HS2 HJ 0xdd0; [cl6_awr cx U60 HAS|].
cl6_after cx U60 M3 G3.
cl6_br BR W HS2 BC_EQ (24%bv : bv 5) (0%bv : bv 5); intros Hc3 HS3; clear HS2;
  rewrite branch_eq_U, U_lit, (cl6_usx _ 563%nat (gn G) X0) in Hc3 by lia.
- apply Z.eqb_eq in Hc3.
  paj_run_to_sh RUNTO HS3 HJ 0xdd0; [cl6_awr cx U60 HAS|].
  cl6_after cx U60 M4 G4.
  cl6_r60 HS3 HR60.
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 224 541%nat push HR60 U60) as W224. specialize (W224 ltac:(cl6_in) A541).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 280 558%nat fr HR60 U60) as W280. specialize (W280 ltac:(cl6_in) A558).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 336 555%nat len HR60 U60) as W336. specialize (W336 ltac:(cl6_in) A555).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 368 554%nat nb HR60 U60) as W368. specialize (W368 ltac:(cl6_in) A554).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 232 564%nat i HR60 U60) as W232. specialize (W232 ltac:(cl6_in) X1).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 344 565%nat now HR60 U60) as W344. specialize (W344 ltac:(cl6_in) X2).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 248 566%nat (d_cur cx nb) HR60 U60) as W248. specialize (W248 ltac:(cl6_in) X3).
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msf; cfg_model := _ |} _ =>
    assert (MF : forall x : word, ~ (d_A cx + 224 <= bv_unsigned x < d_A cx + 376) -> ms_mem msf x = mem3 x)
      by (intros x Hx; rewrite (M4 x Hx), (M3 x Hx), (M2 x Hx), (M1 x Hx); reflexivity);
    assert (MG : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem msf) a)
      by (intros a Hp; exact (apresent_grows _ _ _ a G4 (apresent_grows _ _ _ a G3
            (apresent_grows _ _ _ a G2 (apresent_grows _ _ _ a G1 Hp)))));
    assert (K : forall r, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs msf) r = getr regs r)
      by cl6_keep HS3 HROK;
    assert (V216f : val_mem SEGS (rd W (ms_mem msf)) (d_A cx + 216) 8 h)
      by (apply (cl6_kvm W mem3 (ms_mem msf) (d_A cx)); [exact MF | lia | lia | lia | exact Hh216]);
    assert (V152f : val_mem SEGS (rd W (ms_mem msf)) (d_A cx + 152) 8 (h + 440))
      by (apply (cl6_kvm W mem3 (ms_mem msf) (d_A cx)); [exact MF | lia | lia | lia | exact Hh152]);
    lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdf _ =>
      assert (HCf : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msf) mdf k0)
        by (split; [exact HB | split; [exact HJ | exact HFR]]) end;
    destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_rec ly3 S3 W _ k0 (d_env cx E V) _ msf
      HCf (d_E_env cx E V HdE) (d_env_fl cx E V) HS3 ltac:(vm_compute; reflexivity) V216f V152f)
      as [Hfrf Hshf];
    destruct (cl6_post cx h i n now op nb fr len regs ly3 S3 W mem3 md3 k0 Sg G push (ms_regs msf) (ms_mem msf)
      HC HBS HSG HGT Hpush MF MG Hfrf Hshf K W232 W344 W248 W224 W280 W336 W368) as (Pb & Psg & Pgt & Pspl)
  end.
  apply SRr_ret. left. unfold cl_X.
  eapply (cl6_land fq cx 0xdd0 _ _ _ W ly3 S3 _ k0 acc _ _ _ Hf0 HB HJ HFR Hk Hev Hmo Hacc HS3 eq_refl eq_refl).
  intros md. exists Sg, push. exact (conj Pb (conj Psg Pspl)).
- apply Z.eqb_neq in Hc3.
  paj_run_to_sh RUNTO HS3 HJ 0xd80; [cl6_awr cx U60 HAS|].
  cl6_after cx U60 M4 G4.
  cl6_r60 HS3 HR60.
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 224 541%nat push HR60 U60) as W224. specialize (W224 ltac:(cl6_in) A541).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 280 558%nat fr HR60 U60) as W280. specialize (W280 ltac:(cl6_in) A558).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 336 555%nat len HR60 U60) as W336. specialize (W336 ltac:(cl6_in) A555).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 368 554%nat nb HR60 U60) as W368. specialize (W368 ltac:(cl6_in) A554).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 232 564%nat i HR60 U60) as W232. specialize (W232 ltac:(cl6_in) X1).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 344 565%nat now HR60 U60) as W344. specialize (W344 ltac:(cl6_in) X2).
  pose proof (cl6_fld _ _ _ _ _ _ _ (d_A cx) 248 566%nat (d_cur cx nb) HR60 U60) as W248. specialize (W248 ltac:(cl6_in) X3).
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msf; cfg_model := _ |} _ =>
    assert (MF : forall x : word, ~ (d_A cx + 224 <= bv_unsigned x < d_A cx + 376) -> ms_mem msf x = mem3 x)
      by (intros x Hx; rewrite (M4 x Hx), (M3 x Hx), (M2 x Hx), (M1 x Hx); reflexivity);
    assert (MG : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem msf) a)
      by (intros a Hp; exact (apresent_grows _ _ _ a G4 (apresent_grows _ _ _ a G3
            (apresent_grows _ _ _ a G2 (apresent_grows _ _ _ a G1 Hp)))));
    assert (K : forall r, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs msf) r = getr regs r)
      by cl6_keep HS3 HROK;
    assert (V216f : val_mem SEGS (rd W (ms_mem msf)) (d_A cx + 216) 8 h)
      by (apply (cl6_kvm W mem3 (ms_mem msf) (d_A cx)); [exact MF | lia | lia | lia | exact Hh216]);
    assert (V152f : val_mem SEGS (rd W (ms_mem msf)) (d_A cx + 152) 8 (h + 440))
      by (apply (cl6_kvm W mem3 (ms_mem msf) (d_A cx)); [exact MF | lia | lia | lia | exact Hh152]);
    lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdf _ =>
      assert (HCf : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msf) mdf k0)
        by (split; [exact HB | split; [exact HJ | exact HFR]]) end;
    destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_rec ly3 S3 W _ k0 (d_env cx E V) _ msf
      HCf (d_E_env cx E V HdE) (d_env_fl cx E V) HS3 ltac:(vm_compute; reflexivity) V216f V152f)
      as [Hfrf Hshf];
    destruct (cl6_post cx h i n now op nb fr len regs ly3 S3 W mem3 md3 k0 Sg G push (ms_regs msf) (ms_mem msf)
      HC HBS HSG HGT Hpush MF MG Hfrf Hshf K W232 W344 W248 W224 W280 W336 W368) as (Pb & Psg & Pgt & Pspl)
  end.
  apply SRr_ret. right. exists (gn G). unfold cl_LI.
  eapply (cl6_land fq cx 0xd80 _ _ _ W ly3 S3 _ k0 acc _ _ _ Hf0 HB HJ HFR Hk Hev Hmo Hacc HS3 eq_refl eq_refl).
  intros md. split; [exists Sg, G, push; exact (conj Pb (conj Psg (conj Pgt (conj eq_refl Pspl))))|].
  split; [lia|].
  split; [cl6_reg HS3 (23%bv : bv 5); reflexivity|].
  split; [cl6_reg HS3 (24%bv : bv 5); rewrite denot_lit_U, (cl6_usx _ 563%nat (gn G) X0) by lia; reflexivity|].
  split; [cl6_reg HS3 (21%bv : bv 5); rewrite denot_lit_U, (U_atom_off _ 516%nat (d_FB cx) 2656 A516) by lia;
    unfold w64, d_obj; cbn [dobj_off]; f_equal; lia|].
  cl6_reg HS3 (26%bv : bv 5). rewrite (cl6_dec _ 563%nat (gn G) X0) by lia. unfold w64. f_equal. lia.
Qed.
End h.
End f.
End d.
