(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 1243 of its 1273 lines of code are new or changed and 39 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntCls.v, with its module paths, module names and addresses changed; 582 of its 685 lines of code are new or changed and 1170 lines of the source are left out. *)
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
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt ClassifyCore CheckSighting ReacDiscoGateShouldPush DiscoYEntClsCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition s2_rs (acs : list YP09.chunk) : smem := [YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ acs)].
Definition s2_acs : list YP09.chunk :=
  [YP09.mkChunk 320 (CVal 8 (SOff 563 0)); YP09.mkChunk 368 (CVal 8 (SOff 564 0));
   YP09.mkChunk 408 (CVal 8 (SOff 565 0))].

Ltac s2_bvneq := let X := fresh "X" in intros X; apply (f_equal bv_unsigned) in X; cbv in X; discriminate X.

Lemma s2_sub : forall shf acs, submem (s2_rs acs) (d_kregions shf acs [] ++ []).
Proof.
intros shf acs. unfold s2_rs, d_kregions. cbn [app].
apply submem_drop. apply submem_keep; [|apply submem_nil].
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. intros c Hc. exact Hc.
Qed.

Lemma s2_our_len : forall pl, length (our_of pl) = 6%nat.
Proof. intros pl. unfold our_of. rewrite length_map, length_seq. reflexivity. Qed.

Lemma s2_w64_add : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (unfold bv_modulus; cbn; lia). reflexivity.
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

Lemma s2_env_xs : forall cx E regs xs j, (j < length xs)%nat ->
  ew (d_env cx E (cl_vals regs xs)) (563 + j) = nth j xs (Z_to_bv 64 0).
Proof.
intros cx E regs xs j Hj. unfold d_env.
replace (563 + j)%nat with (AT_FL + S (32 + j))%nat by (unfold AT_FL; lia).
rewrite (ew_havoc_new _ AT_FL _ (S (32 + j)) (Z_to_bv 64 0))
  by (cbn [length]; unfold cl_vals; rewrite length_app, length_map, length_seq; lia).
cbn [nth]. unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. replace (32 + j - 32)%nat with j by lia. reflexivity.
Qed.

Lemma s2_av : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' HM a. apply aview_eq_of. unfold mrestrict. rewrite HM. reflexivity. Qed.

Lemma s2_apresent : forall H (m : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hn Hv. unfold aview, mbyte, mrestrict in Hv. rewrite (seg_rom_none SEGS a Ha Hn) in Hv.
unfold apresent. destruct (H (Z_to_bv 64 a)); [exfalso; apply Hv; reflexivity|].
destruct (m (Z_to_bv 64 a)) as [b|]; [split; [reflexivity | exists b; reflexivity] | exfalso; apply Hv; reflexivity].
Qed.

Lemma s2_sg_eq : forall cx nb len Sg (W : world SEGS) m m', (forall x, m' x = m x) ->
  cl_sg cx nb len Sg W m -> cl_sg cx nb len Sg W m'.
Proof.
intros cx nb len Sg W m m' HM (L & G & F). split; [exact L|]. split; [|exact F].
eapply YC88.garr8_aview_kept; [|exact G]. intros a _. exact (s2_av (w_H W) m m' HM a).
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = FF_canary.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis TCHKS : CheckSighting.tcheck_sighting_spec B.
Hypothesis TGPUSH : ReacDiscoGateShouldPush.treac_disco_gate_should_push_spec B.
#[local] Notation DCTX := (d_ctx B MT XM_LIB RLO RHI tfib_K).

Lemma s2_kept_eq : forall ly3 S3 (W : world SEGS) m m' lo,
  (forall x, m' x = m x) -> cl_kept B ly3 S3 W m W m' lo lo (fun _ => False).
Proof.
intros ly3 S3 W m m' lo HM.
pose proof (s2_av (w_H W) m m' HM) as AV.
split; [intros a _ _ _; exact (AV a)|].
split; [intros b mm j _ _ _; exact (AV (b + j))|].
split; [intros a _ _ _; exact (AV a)|].
split; [intros cid pos a _ _ _; exact (AV a)|].
split; [intros a _ _ (Hh & b & Hb); split; [exact Hh | exists b; rewrite HM; exact Hb]|].
intros a Ha. lia.
Qed.

Lemma s2_kept_aj : forall STK1 sp ly3 S3 (W : world SEGS) m md ly2 S2 (W2 : world SEGS) m2 md2 k1,
  ajournal SEGS B STK1 sp [] ly3 S3 W m md [] ly2 S2 W2 m2 md2 k1 ->
  Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  cl_kept B ly3 S3 W m W2 m2 (sp - STK1) sp (fun _ => False).
Proof.
intros STK1 sp ly3 S3 W m md ly2 S2 W2 m2 md2 k1 HJ Hperm.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & J3 & J4 & _ & J6 & _).
pose proof asan_consts as (C1 & _).
split; [intros a Ha Hn _; exact (J1 a Ha Hn)|].
split; [intros b mm j Hin Hj _;
  exact (J2 b mm j Hin (Permutation_in _ (Permutation_sym Hperm) Hin) Hj (inFP_nil (b + j)))|].
split; [intros a Hi Ho He; apply (J3 a Hi Ho He); intros Hop; exfalso; destruct Hop as (r & Hr & _); destruct Hr|].
split; [intros cid pos a Hin Hr _; exact (J4 cid pos a Hin Hr (inFP_nil a))|].
split; [|intros a Ha; exact (J6 a Ha)].
intros a Ha Hn Hp. apply s2_apresent; [lia | |].
- intros Hi. pose proof (pa_img_range a Hi) as Hr. unfold IMG_LO, IMG_TOP in Hr. lia.
- rewrite (J1 a Ha Hn). exact (aview_some_of_apresent SEGS _ _ a Hp).
Qed.

Lemma s2_body_eq : forall cx h n xb ly3 S3 (W : world SEGS) m m' md k md' k',
  d_body B cx h n xb dsh_rec ly3 S3 W m -> DCTX cx ly3 S3 W m md k -> DCTX cx ly3 S3 W m' md' k' ->
  (forall x, m' x = m x) -> d_body B cx h n xb dsh_rec ly3 S3 W m'.
Proof.
intros cx h n xb ly3 S3 W m m' md k md' k' HB HC HC' HM.
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k HC) as (Hal16 & Hlo & _).
pose proof asan_consts as (C1 & _).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
apply (cl_body_call B MT XM_LIB RLO RHI tfib_K LAWS AIL KCAN cx h n xb dsh_rec ly3 S3 W m md k ly3 S3 W m' md' k'
  (d_A cx) (d_A cx) (fun _ => False) [] HB HC HC' (s2_kept_eq ly3 S3 W m m' (d_A cx) HM)).
- unfold MFRAME, LLVMF_STK in *. lia.
- lia.
- intros a [].
- intros a [].
- apply Forall_nil.
- apply Permutation_refl.
- exact BTOBS.
Qed.

Lemma s2_base_eq : forall cx h i n now op nb fr len regs regs' ly3 S3 (W : world SEGS) m m' md k md' k',
  cl_base B cx h i n now op nb fr len regs ly3 S3 W m -> DCTX cx ly3 S3 W m md k -> DCTX cx ly3 S3 W m' md' k' ->
  (forall x, m' x = m x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr regs' r = getr regs r) ->
  cl_base B cx h i n now op nb fr len regs' ly3 S3 W m'.
Proof.
intros cx h i n now op nb fr len regs regs' ly3 S3 W m m' md k md' k' HB HC HC' HM RG.
pose proof HB as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HREC & HOP & Hlen & Hnb & Hnbn & Hbody).
pose proof (s2_kept_eq ly3 S3 W m m' (d_A cx) HM) as HK.
assert (VM : forall off v, 0 <= off -> off + 8 <= 472 -> val_mem SEGS (rd W m) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W m') (d_A cx + off) 8 v)
  by (intros off v H0 H8 Hv; exact (cl_slot_keep B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k W m'
    (d_A cx) (d_A cx) (fun _ => False) off v HC HK (Z.le_refl _) (fun a Ha => False_ind _ Ha) H0 H8 Hv)).
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact Hop|]. split; [exact Hop2|].
split.
{ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27). unfold d_rL, spZ in *.
  rewrite !RG by (clear; cbv; tauto). repeat split; assumption. }
split; [destruct Hsp0 as (S1 & S2); split; apply VM; first [lia | assumption]|].
split; [exact (cl_frm_keep B MT XM_LIB RLO RHI tfib_K LAWS cx nb fr len ly3 S3 W m md k W m' (d_A cx) (d_A cx)
  (fun _ => False) h n dsh_rec HC Hbody HK (fun a Ha => False_ind _ Ha) Hfrm)|].
split; [destruct HREC as (R1 & R2 & R3 & R4); split; [|split; [|split]]; apply VM; first [lia | assumption]|].
split; [destruct HOP as (O1 & O2); split; apply VM; first [lia | assumption]|].
split; [exact Hlen|]. split; [exact Hnb|]. split; [exact Hnbn|].
exact (s2_body_eq cx h n (dxb fr len) ly3 S3 W m m' md k md' k' Hbody HC HC' HM).
Qed.

Lemma s2_base_call : forall cx h i n now op nb fr len regs regs2 ly3 S3 (W : world SEGS) m md k
  ly2 S2 (W2 : world SEGS) m2 md2 k2 lo hi (wr : Z -> Prop) (os : list dobj),
  cl_base B cx h i n now op nb fr len regs ly3 S3 W m -> DCTX cx ly3 S3 W m md k -> DCTX cx ly2 S2 W2 m2 md2 k2 ->
  cl_kept B ly3 S3 W m W2 m2 lo hi wr -> d_S cx - LLVMF_STK <= lo -> hi <= d_A cx ->
  (forall a, wr a -> d_FB cx + 24 <= a < d_FB cx + DFRAME_SIZE) ->
  (forall a, wr a -> d_rdset B cx h a -> Exists (fun o => d_objr cx o a) os) ->
  Forall (fun o => d_obj_new cx o W2 m2) os ->
  Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  aregs_preserved regs regs2 ->
  cl_base B cx h i n now op nb fr len regs2 ly2 S2 W2 m2.
Proof.
intros cx h i n now op nb fr len regs regs2 ly3 S3 W m md k ly2 S2 W2 m2 md2 k2 lo hi wr os
  HB HC3 HC2 HK Hlo Hhi Hwr Hos Hnew Hperm HPR.
pose proof HB as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HREC & HOP & Hlen & Hnb & Hnbn & Hbody).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k HC3) as (_ & _ & _ & _ & HFc & _).
assert (Hwrc : forall a, wr a -> a < alloc_ceiling) by (intros a Ha; pose proof (Hwr a Ha); unfold DFRAME_SIZE in *; lia).
assert (VM : forall off v, 0 <= off -> off + 8 <= 472 -> val_mem SEGS (rd W m) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W2 m2) (d_A cx + off) 8 v)
  by (intros off v H0 H8 Hv; exact (cl_slot_keep B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k W2 m2
    lo hi wr off v HC3 HK Hhi Hwrc H0 H8 Hv)).
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact Hop|]. split; [exact Hop2|].
split.
{ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27). unfold d_rL.
  assert (E2 : getr regs2 2 = getr regs 2) by exact (cl_cs regs regs2 2 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
  unfold spZ in Hsp |- *. rewrite E2. split; [exact Hsp|].
  split; [exact (cl_cs regs regs2 3 _ HPR ltac:(unfold acallee_saved; lia) Hgp)|].
  split; [exact (cl_cs regs regs2 4 _ HPR ltac:(unfold acallee_saved; lia) Htp)|].
  split; [exact (cl_cs regs regs2 8 _ HPR ltac:(unfold acallee_saved; lia) H8)|].
  split; [exact (cl_cs regs regs2 9 _ HPR ltac:(unfold acallee_saved; lia) H9)|].
  split; [exact (cl_cs regs regs2 19 _ HPR ltac:(unfold acallee_saved; lia) H19)|].
  split; [exact (cl_cs regs regs2 18 _ HPR ltac:(unfold acallee_saved; lia) H18)|].
  split; [exact (cl_cs regs regs2 20 _ HPR ltac:(unfold acallee_saved; lia) H20)|].
  exact (cl_cs regs regs2 27 _ HPR ltac:(unfold acallee_saved; lia) H27). }
split; [destruct Hsp0 as (S1 & S1'); split; apply VM; first [lia | assumption]|].
split; [exact (cl_frm_keep B MT XM_LIB RLO RHI tfib_K LAWS cx nb fr len ly3 S3 W m md k W2 m2 lo hi wr h n dsh_rec
  HC3 Hbody HK ltac:(intros a Ha; pose proof (Hwr a Ha); lia) Hfrm)|].
split; [destruct HREC as (R1 & R2 & R3 & R4); split; [|split; [|split]]; apply VM; first [lia | assumption]|].
split; [destruct HOP as (O1 & O2); split; apply VM; first [lia | assumption]|].
split; [exact Hlen|]. split; [exact Hnb|]. split; [exact Hnbn|].
exact (cl_body_call B MT XM_LIB RLO RHI tfib_K LAWS AIL KCAN cx h n (dxb fr len) dsh_rec ly3 S3 W m md k ly2 S2 W2 m2
  md2 k2 lo hi wr os Hbody HC3 HC2 HK Hlo Hhi Hwr Hos Hnew Hperm BTOBS).
Qed.

Lemma s2_afn_s0 : forall STK ly S (W : world SEGS) regs m md ch, afn_pre SEGS B STK ly S W regs m md ch ->
  afn_pre SEGS B STK ly S W (regupd regs 8 (Z_to_bv 64 0)) m md [].
Proof.
intros STK ly S W regs m md ch (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & _ & Hq).
pose proof asan_consts as (C1 & _).
assert (Hsp : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite getr_other by s2_bvneq; reflexivity).
assert (Hs0 : s0Z (regupd regs 8 (Z_to_bv 64 0)) = 0) by (unfold s0Z; rewrite getr_same by s2_bvneq; reflexivity).
split; [exact HAR|].
split; [rewrite getr_other by s2_bvneq; exact Hra|].
split; [unfold raZ in *; rewrite getr_other by s2_bvneq; exact Hra4|].
split; [rewrite getr_other by s2_bvneq; exact Hgp|].
split; [rewrite getr_other by s2_bvneq; exact Htp|].
split; [rewrite Hsp; exact Hstk|].
split; [rewrite Hsp; exact Hpres|].
split; [rewrite Hs0; apply achain_low; lia | exact Hq].
Qed.

Section fx.
Context {fx : YK11.FPState}.
Lemma s2_aj_callF : forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) spw raw ch1
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  YP0l.st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre SEGS B STK1 lyc Sc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr SEGS W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom SEGS)) mdc)
     (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
        c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
        (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fx) k) /\
        (@YK11.fp_csr fx' = @YK11.fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
        ajournal SEGS B STK1 (spZ (ms_regs ms)) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
        aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr SEGS W (mkCfg ms mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
       (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fx) k) /\
       (@YK11.fp_csr fx' = @YK11.fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
       ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o spw raw ch1 K
  HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite YP0m.denot_SOff, HE2, Hspw. apply YP0m.zcanon_small. lia. }
rewrite (st_ok_restrict_mkst SEGS (w_H W) E ss ms HS Hrv).
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k (ms_regs ms) STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfr & Hcs & HJ1 & HP & HK).
exists fx', ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hfr|]. split; [exact Hcs|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
End fx.

Lemma s2_frm0 : forall (fa fb : YK11.FPState), lib.Lib.FP.frm0 (@YK11.fp_csr fa) ->
  (@YK11.fp_csr fb = @YK11.fp_csr fa \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fb)) 5) 7 = 0) ->
  lib.Lib.FP.frm0 (@YK11.fp_csr fb).
Proof. intros fa fb H [E | E]; [rewrite E; exact H | exact E]. Qed.

Theorem pb_cl_L4 : cl_L4_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold cl_L4_stmt. intros cx h i n now op nb fr len W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  r & HB3 & Hr10 & Hrr).
pose proof HB3 as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HREC & HOP & Hlen & Hnb & Hnbn & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan &
  Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & _).
pose proof Hfrm as (F1 & F2 & F3 & F4).
pose proof HREC as (R200 & R328 & R368 & R408).
assert (HC : DCTX cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hac.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (Hfr64 : 0 <= fr < 2 ^ 64).
{ destruct (Z.eq_dec fr 0) as [-> | Hne]; [lia|].
  pose proof Hblocks as (Hp & _).
  assert (Hin : In (fr, len) (ablocks B ly3 S3)).
  { eapply Permutation_in; [apply Permutation_sym; exact Hp|].
    unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
  destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 fr len HAR Hin) as (_ & Hf1 & Hf2 & _).
  pose proof (req_size_pos len ltac:(unfold REC_MAX in F1; lia)). lia. }
set (xs := [w64 now; w64 fr; w64 len]).
pose proof (cl_regs_ok B cx E regs xs HdE HrL HAr2) as HROK.
assert (X0 : ew (d_env cx E (cl_vals regs xs)) 563 = w64 now) by exact (s2_env_xs cx E regs xs 0 ltac:(cbn; lia)).
assert (X1 : ew (d_env cx E (cl_vals regs xs)) 564 = w64 fr) by exact (s2_env_xs cx E regs xs 1 ltac:(cbn; lia)).
assert (X2 : ew (d_env cx E (cl_vals regs xs)) 565 = w64 len) by exact (s2_env_xs cx E regs xs 2 ltac:(cbn; lia)).
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (cl_vals regs xs)) (rd W mem3) (d_A cx)) s2_acs).
{ unfold s2_acs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ now); [rewrite sv_denot_SOff0, X0; reflexivity | cbn; lia | lia | exact (proj2 Hsp0)].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ fr); [rewrite sv_denot_SOff0, X1; reflexivity | cbn; lia | lia | exact R368].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ len);
      [rewrite sv_denot_SOff0, X2; reflexivity | cbn; unfold REC_MAX in F1; lia | lia | exact R408]. }
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0xed8 cl_sr (cl_vals regs xs) s2_acs [] []
  (d_facts [] []) HC HdE Hregs Hflag HROK (FACTS LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs xs) [] [] HC HdE I I)
  HACS (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ (s2_rs s2_acs) HS0 (s2_sub dsh_rec s2_acs) ltac:(vm_compute; reflexivity)) as HS.
clear HS0.
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs xs))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia).
  exact (HI a Ha). }
assert (EF : ew (d_env cx E (cl_vals regs xs)) 516 = Z_to_bv 64 (d_FB cx)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & HFx & _). exact HFx. }
assert (Usp : bv_unsigned (ew (d_env cx E (cl_vals regs xs)) 2) = d_S cx).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (EE & _). rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
assert (D10 : sv_denot (d_env cx E (cl_vals regs xs)) (SOff 541 0) = w64 r).
{ rewrite <- Hr10, (HROK 10%bv). f_equal; vm_compute; reflexivity. }
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNC.
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + 0xed8)) with (Z_to_bv 64 (BASE + 0xed8)).
paj_run_to_sh RUNTO HS HJ R27_OFF; [awr_ok_tac|].
pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hpt1. cbn [ms_mem mkst] in Hpt1.
clear HF HFr HG. rename ms into ms1. rename mat into mat1.
psrr_branch_pi RUNP BR HS.
- paj_run_to_sh RUNTO HS HJ R27_OFF; [awr_ok_tac|].
  pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hpt2.
  clear HF HFr HG. rename ms into ms2. rename mat into mat2.
  assert (Hpt : forall x, ms_mem ms2 x = mem3 x) by (intros x; rewrite Hpt2, Hpt1; reflexivity).
  assert (RG : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms2) r0 = getr regs r0).
  { intros r0 Hr0. rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms2 r0 HS), (HROK r0).
    cbv [In] in Hr0. repeat (destruct Hr0 as [<-|Hr0]; [f_equal; vm_compute; reflexivity|]). destruct Hr0. }
  pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ ms2 HS eq_refl) as Hms. cbn [ss_pc] in Hms.
  eassert (HC2 : DCTX cx ly3 S3 W (ms_mem ms2) _ k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  pose proof (s2_base_eq cx h i n now op nb fr len regs (ms_regs ms2) ly3 S3 W mem3 (ms_mem ms2) md3 k _ k
    HB3 HC HC2 Hpt RG) as HBf.
  pose proof HBf as (_ & _ & _ & _ & _ & HrLf & Hsp0f & Hfrmf & HRECf & _ & _ & _ & _ & Hbodyf).
  apply SRr_ret. left. unfold r27_in, d_arm_at_pf, d_at.
  eexists fq, ly3, S3, (ms_regs ms2), (ms_mem ms2), _, k, acc.
  split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|].
  split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hnev|].
  split; [exact Hmo|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [lia|]. split; [exact Hnow|]. split; [exact HrLf|]. split; [exact I|].
  split; [split; [exact Hfrmf|]; split; [exact HRECf|]; split; [exact Hlen | reflexivity]|].
  split; [exact Hsp0f|].
  exact (cl_body_n B cx h n (nb - len) (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms2) Hbodyf ltac:(lia)).
- assert (Er : r = 0 /\ exists Sg, cl_sg cx nb len Sg W mem3).
  { destruct Hrr as [-> | (E0 & HSg)]; [|exact (conj E0 HSg)].
    exfalso. rewrite D10 in Hc. cbn [sv_denot] in Hc. vm_compute in Hc. discriminate Hc. }
  destruct Er as (-> & Sg & HSg). clear Hc.
  paj_run_to_sh RUNTO HS HJ R27_OFF; [awr_ok_tac|].
  pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hpt2.
  clear HF HFr HG. rename ms into ms2. rename mat into mat2.
  psrr_branch_pi RUNP BR HS.
  2: { exfalso. rewrite D10 in Hc. cbn [sv_denot] in Hc. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ; [awr_ok_tac|].
  pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hpt3.
  clear HF HFr HG. rename ms into ms3. rename mat into mat3.
  assert (Hpt : forall x, ms_mem ms3 x = mem3 x) by (intros x; rewrite Hpt3, Hpt2, Hpt1; reflexivity).
  assert (RG : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26; 27]%bv ->
    getr (ms_regs ms3) r0 = getr regs r0).
  { intros r0 Hr0. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms3 r0 HS), (HROK r0).
    cbv [In] in Hr0. repeat (destruct Hr0 as [<-|Hr0]; [f_equal; vm_compute; reflexivity|]). destruct Hr0. }
  assert (R1 : getr (ms_regs ms3) 1 = w64 (BASE + 0xf0c)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms3 1%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    unfold w64. exact (codeptr_val _ 0xf0c HEI). }
  assert (A10 : getr (ms_regs ms3) 10 = w64 (d_obj cx OS)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms3 10%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    cbn [sv_denot]. rewrite EF, s2_w64_add. reflexivity. }
  assert (A11 : getr (ms_regs ms3) 11 = w64 fr).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms3 11%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    rewrite sv_denot_SOff0. exact X1. }
  assert (A12 : getr (ms_regs ms3) 12 = w64 len).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms3 12%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    rewrite sv_denot_SOff0. exact X2. }
  assert (A13 : getr (ms_regs ms3) 13 = w64 (d_obj cx OOUR)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms3 13%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    cbn [sv_denot]. rewrite EF, s2_w64_add. reflexivity. }
  assert (A14 : getr (ms_regs ms3) 14 = w64 0).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms3 14%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    reflexivity. }
  assert (A21 : getr (ms_regs ms3) 21 = w64 (d_obj cx OS)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms3 21%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    cbn [sv_denot]. rewrite EF, s2_w64_add. reflexivity. }
  assert (A22 : getr (ms_regs ms3) 22 = w64 1).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms3 22%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    reflexivity. }
  assert (A23 : getr (ms_regs ms3) 23 = w64 now).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms3 23%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    rewrite sv_denot_SOff0. exact X0. }
  eassert (HC4 : DCTX cx ly3 S3 W (ms_mem ms3) _ k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  pose proof (s2_base_eq cx h i n now op nb fr len regs (ms_regs ms3) ly3 S3 W mem3 (ms_mem ms3) md3 k _ k HB3 HC HC4 Hpt
    ltac:(intros r0 Hr0; apply RG; clear - Hr0; cbv [In] in Hr0 |- *; tauto)) as HB4.
  pose proof HB4 as (_ & _ & _ & _ & _ & _ & _ & Hfrm4 & _ & _ & _ & _ & _ & Hbody4).
  pose proof Hbody4 as (T4 & G4 & Lk4 & H4 & Hframe4 & Hshadow4 & Hobjs4 & Hblocks4 & Hinput4 & Himg4 & Hoff4 & Hgeo4 &
    _ & _ & Hawr4).
  pose proof Hframe4 as (E4 & HdE4 & Hregs4 & _).
  pose proof Hobjs4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HGour & _).
  pose proof (s2_sg_eq cx nb len Sg W mem3 (ms_mem ms3) Hpt HSg) as HSg4.
  pose proof HSg4 as (LSg & GSg & FSg).
  assert (H50 : 50 <= len) by exact (proj1 FSg).
  assert (Hfr0 : fr <> 0) by (intros E0; pose proof (F2 E0); lia).
  pose proof Hblocks4 as (Hp4 & _).
  assert (Hin4 : In (fr, len) (ablocks B ly3 S3)).
  { eapply Permutation_in; [apply Permutation_sym; exact Hp4|].
    unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hfr0). left; reflexivity. }
  destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms3) _ k HC4)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR4 & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W (ms_mem ms3) _ fr len HAR4 Hin4) as (_ & Hf1 & Hf2 & _).
  pose proof (req_size_pos len ltac:(lia)) as (Hrq1 & Hrq2).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W (ms_mem ms3) _ fr len DFRAME_CLASS (c_fpos cx) HAR4 Hin4 Hfin) as Hsep.
  rewrite Efa, cl_fs6 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
  pose proof (blk_off_imgP B ly3 S3 W (ms_mem ms3) _ fr len HAR4 Hin4) as Hfoi.
  destruct (cl_achain B MT XM_LIB XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms3) _ k E4 (d_A cx) HC4 HdE4
    (Forall_inv Hregs4) ltac:(unfold MFRAME in HA1; lia)) as (ch & Hch).
  assert (Es0 : s0Z (ms_regs ms3) = d_S cx).
  { unfold s0Z. rewrite (RG 8%bv ltac:(clear; cbv; tauto)). destruct HrL as (_ & _ & _ & H8 & _). rewrite H8.
    unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  assert (Hsp4 : spZ (ms_regs ms3) = d_A cx) by (unfold spZ; rewrite (RG 2%bv ltac:(clear; cbv; tauto)); exact (proj1 HrL)).
  pose proof (cl_cread_obj B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms3) _ k OS (d_A cx) HC4 Hshadow4
    ltac:(vm_compute; reflexivity)
    ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia))
    as (_ & _ & SAm & _ & _ & SRa & SSh).
  pose proof (cl_cread_obj B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms3) _ k OOUR (d_A cx) HC4 Hshadow4
    ltac:(vm_compute; reflexivity)
    ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia))
    as (_ & _ & UAm & _ & _ & URa & USh).
  eapply SRr_bind.
  { eapply (s2_aj_callF (fx := fq) W _ _ ms3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
      (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ k TCHECK_SIGHTING_STK [] 0 (d_A cx - d_S cx)
      (ew (d_env cx E (cl_vals regs xs)) 2) (getr (ms_regs ms3) 1) ch
      (fun ly' S' W' (_ : bvmap 5 word) mem' (_ : Model) => Permutation (ablocks B ly' S') (ablocks B ly3 S3) /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs ms3) - TCHECK_SIGHTING_STK <= a < spZ (ms_regs ms3)) ->
           aview SEGS (w_H W') mem' a = aview SEGS (w_H W) (ms_mem ms3) a))
      HS eq_refl HJ).
    - rewrite (RG 2%bv ltac:(clear; cbv; tauto)). cbn [sv_denot]. rewrite Usp.
      replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) by lia.
      destruct HrL as (Hsp & _). unfold spZ in Hsp. rewrite <- Hsp. symmetry. apply Z_to_bv_bv_unsigned.
    - reflexivity.
    - exact Usp.
    - clear - Hal16 HA2. lia.
    - unfold MFRAME in HA1. lia.
    - unfold TCHECK_SIGHTING_STK, ESTACK. lia.
    - unfold TCHECK_SIGHTING_STK, ESTACK, MFRAME, LLVMF_STK in *. lia.
    - rewrite (RG 3%bv ltac:(clear; cbv; tauto)). exact (proj1 (proj2 HrL)).
    - rewrite (RG 4%bv ltac:(clear; cbv; tauto)). exact (proj1 (proj2 (proj2 HrL))).
    - reflexivity.
    - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite R1. unfold w64. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
      rewrite unsigned_lit_small by lia. pose proof (pa_base_lo (PI := PI)). unfold IMG_LO in *. lia.
    - replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) by lia. rewrite Es0. exact Hch.
    - intros HPRE1. cbn [ss_pc setpc]. rewrite pa_sigma_check_sighting.
      apply (TCHKS fq ly3 S3 W (ms_regs ms3) (ms_mem ms3) _ [] (d_obj cx OS) fr len (d_obj cx OOUR) 0 Sg
        (cl_F (c_pl cx) nb len) (our_of (c_pl cx)) (s2_afn_s0 _ _ _ _ _ _ _ _ HPRE1) Himg4 A10 A11 A12 A13 A14).
      + unfold d_obj. cbn [dobj_off]. lia.
      + unfold d_obj. cbn [dobj_off]. clear - HFal. lia.
      + unfold d_obj. cbn [dobj_off]. lia.
      + lia.
      + lia.
      + unfold d_obj. cbn [dobj_off]. lia.
      + unfold d_obj. cbn [dobj_off]. lia.
      + unfold REC_MAX in F1. lia.
      + lia.
      + unfold REC_MAX in F1. lia.
      + exact LSg.
      + exact GSg.
      + unfold cl_F. rewrite length_firstn.
        rewrite (cl_rest_len (c_pl cx) nb len ltac:(lia)
          ltac:(pose proof Hgeo4 as (_ & _ & _ & _ & _ & G6 & _); lia)). lia.
      + exact (cl_garr8_firstn SEGS _ fr _ 50 (proj2 (proj2 (proj2 Hfrm4)))).
      + exact (s2_our_len (c_pl cx)).
      + exact HGour.
      + exact SAm.
      + exact (amem_range_of_block SEGS B LAWS ly3 S3 W (ms_mem ms3) _ fr len fr 50 HAR4 Hin4 ltac:(lia) ltac:(lia)).
      + exact UAm.
      + exact SRa.
      + exact SSh.
      + exact (range_addressable_of_block SEGS B LAWS ly3 S3 W (ms_mem ms3) _ fr len fr 50 HAR4 Hin4
          ltac:(lia) ltac:(lia)).
      + exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W (ms_mem ms3) _ fr len fr 50 HAR4 Hin4
          ltac:(lia) ltac:(lia) ltac:(lia)).
      + exact URa.
      + exact USh.
      + left. rewrite Hsp4. unfold d_obj, TCHECK_SIGHTING_STK, ESTACK, MFRAME, LLVMF_STK in *. cbn [dobj_off]. lia.
      + left. rewrite Hsp4. unfold TCHECK_SIGHTING_STK, ESTACK, MFRAME, LLVMF_STK in *. lia.
      + pose proof Hoff4 as Ho. unfold off_img in Ho |- *. rewrite cl_fs6 in Ho. unfold d_obj. cbn [dobj_off]. lia.
      + unfold off_img in Hfoi |- *. lia.
      + unfold d_obj. cbn [dobj_off]. lia.
      + left. rewrite Hsp4. unfold d_obj, TCHECK_SIGHTING_STK, ESTACK, MFRAME, LLVMF_STK in *. cbn [dobj_off]. lia.
      + exact FSg.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hc2 & Hfrk2 & Hcsr2 & HJ2 & HJc & HPR & Hperm2 & HKa).
  rewrite Z.add_0_r in HJ2.
  pose proof HJc as (_ & _ & _ & _ & _ & Hfr2 & _). cbn [app] in Hfr2.
  assert (HC2 : DCTX cx ly2 S2 W2 mem2 md2 k) by (split; [exact Hbase | split; [exact HJ2 | rewrite Hfr2; exact Hfrs]]).
  pose proof (s2_kept_aj TCHECK_SIGHTING_STK (d_S cx + (d_A cx - d_S cx)) ly3 S3 W (ms_mem ms3) _ ly2 S2 W2 mem2 md2 0
    HJc Hperm2) as HK.
  pose proof (s2_base_call cx h i n now op nb fr len (ms_regs ms3) regs2 ly3 S3 W (ms_mem ms3) _ k ly2 S2 W2 mem2 md2 k
    (d_S cx + (d_A cx - d_S cx) - TCHECK_SIGHTING_STK) (d_S cx + (d_A cx - d_S cx)) (fun _ => False) [] HB4 HC4 HC2 HK
    ltac:(unfold TCHECK_SIGHTING_STK, ESTACK, MFRAME, LLVMF_STK in *; lia) ltac:(lia)
    ltac:(intros a []) ltac:(intros a []) (Forall_nil _) Hperm2 HPR) as HB2.
  assert (HSg2 : cl_sg cx nb len Sg W2 mem2).
  { split; [exact LSg|]. split; [|exact FSg].
    eapply YC88.garr8_aview_kept; [|exact GSg]. intros a Ha. rewrite length_map, LSg in Ha.
    change (Z.of_nat 24) with 24 in Ha. apply HKa; [unfold d_obj in Ha; cbn [dobj_off] in Ha; lia|].
    rewrite Hsp4. unfold d_obj in Ha. cbn [dobj_off] in Ha. unfold TCHECK_SIGHTING_STK, ESTACK, MFRAME, LLVMF_STK in *. lia. }
  apply SRr_ret. right. unfold cl_CSR, d_at. exists fx', ly2, S2, regs2, mem2, md2, k, acc.
  split; [rewrite Hc2, R1; reflexivity|].
  split; [exact (s2_frm0 fq fx' HFRM0 Hcsr2)|]. split; [exact Hbase|]. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|]. split; [exact Hk|].
  split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); unfold cl_kmax in *; lia|].
  split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
  exists Sg. split; [exact HB2|].
  split; [exact (cl_cs (ms_regs ms3) regs2 21 _ HPR ltac:(unfold acallee_saved; lia) A21)|].
  split; [exact (cl_cs (ms_regs ms3) regs2 23 _ HPR ltac:(unfold acallee_saved; lia) A23)|].
  split; [exact (cl_cs (ms_regs ms3) regs2 22 _ HPR ltac:(unfold acallee_saved; lia) A22)|].
  exact HSg2.
Qed.

Theorem pb_cl_L5 : cl_L5_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold cl_L5_stmt. intros cx h i n now op nb fr len W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Sg & HB3 & R21 & R23 & R22 & HSg).
pose proof HB3 as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HREC & HOP & Hlen & Hnb & Hnbn & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan &
  Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & _).
assert (HC : DCTX cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hac.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof (cl_regs_ok B cx E regs [] HdE HrL HAr2) as HROK.
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0xf0c cl_sr (cl_vals regs []) [] [] []
  (d_facts [] []) HC HdE Hregs Hflag HROK (FACTS LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs []) [] [] HC HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ (s2_rs []) HS0 (s2_sub dsh_rec []) ltac:(vm_compute; reflexivity)) as HS.
clear HS0.
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs []))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia).
  exact (HI a Ha). }
assert (EF : ew (d_env cx E (cl_vals regs [])) 516 = Z_to_bv 64 (d_FB cx)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & HFx & _). exact HFx. }
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNC.
unfold cfg_at. change (w64 (BASE + 0xf0c)) with (Z_to_bv 64 (BASE + 0xf0c)).
paj_run_shc RUNP RUNC HS HJ; [awr_ok_tac|].
pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hpt.
clear HF HFr HG.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS), (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (R1 : getr (ms_regs ms) 1 = w64 (BASE + 0xf1c)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  unfold w64. exact (codeptr_val _ 0xf1c HEI). }
assert (A10 : getr (ms_regs ms) 10 = w64 (d_obj cx OG)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite EF, s2_w64_add. reflexivity. }
assert (A11 : getr (ms_regs ms) 11 = w64 (d_obj cx OS)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS). rewrite <- R21, (HROK 21%bv). f_equal; vm_compute; reflexivity. }
assert (A12 : getr (ms_regs ms) 12 = w64 now).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 12%bv HS). rewrite <- R23, (HROK 23%bv). f_equal; vm_compute; reflexivity. }
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
rewrite pa_sigma_reac_disco_gate_should_push in Hms.
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (s2_base_eq cx h i n now op nb fr len regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) md3 k md4 k HB3 HC HC4 Hpt
  ltac:(intros r Hr; apply RG; clear - Hr; cbv [In] in Hr |- *; tauto)) as HB4.
pose proof HB4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbody4).
pose proof Hbody4 as (T4 & G4 & Lk4 & H4 & Hframe4 & Hshadow4 & Hobjs4 & _ & _ & Himg4 & Hoff4 & Hgeo4 & _ & _ & Hawr4).
pose proof Hobjs4 as (_ & _ & _ & LG4 & GG4 & OKG4 & _).
pose proof (s2_sg_eq cx nb len Sg W mem3 (ms_mem ms) Hpt HSg) as HSg4.
pose proof HSg4 as (LSg & GSg & FSg).
assert (Hsp4 : spZ (ms_regs ms) = d_A cx) by (unfold spZ; rewrite (RG 2%bv ltac:(clear; cbv; tauto)); exact (proj1 HrL)).
pose proof (cl_cread_obj B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k OG (d_A cx) HC4 Hshadow4
  ltac:(vm_compute; reflexivity)
  ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia))
  as (_ & _ & GAm & _ & _ & GRa & GSh).
pose proof (cl_cread_obj B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k OS (d_A cx) HC4 Hshadow4
  ltac:(vm_compute; reflexivity)
  ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia))
  as (_ & _ & SAm & _ & _ & SRa & SSh).
rewrite Hms.
eapply SRr_bind.
{ apply (TGPUSH fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
    ly3 S3 W (ms_mem ms) md4 k (ms_regs ms) (d_obj cx OG) (d_obj cx OS) now G4 Sg HJ).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
    rewrite unsigned_lit_small by lia. pose proof (pa_base_lo (PI := PI)). unfold IMG_LO in *. lia.
  - rewrite (RG 3%bv ltac:(clear; cbv; tauto)). exact (proj1 (proj2 HrL)).
  - rewrite (RG 4%bv ltac:(clear; cbv; tauto)). exact (proj1 (proj2 (proj2 HrL))).
  - exact A10.
  - exact A11.
  - exact A12.
  - exact Hnow.
  - rewrite Hsp4. clear - HA2. lia.
  - rewrite Hsp4. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK, MFRAME, LLVMF_STK in *. lia.
  - rewrite Hsp4. unfold MFRAME in HA1. lia.
  - unfold d_obj. cbn [dobj_off]. lia.
  - unfold d_obj. cbn [dobj_off]. clear - HFal. lia.
  - unfold d_obj. cbn [dobj_off]. lia.
  - right. rewrite Hsp4. unfold d_obj, REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK, MFRAME, LLVMF_STK in *.
    cbn [dobj_off]. lia.
  - intros a Ha. apply (Hawr4 a). unfold d_obj in Ha. cbn [dobj_off] in Ha. unfold DFRAME_SIZE. lia.
  - exact GAm.
  - exact GRa.
  - exact GSh.
  - exact LG4.
  - exact GG4.
  - exact OKG4.
  - unfold d_obj. cbn [dobj_off]. lia.
  - unfold d_obj. cbn [dobj_off]. clear - HFal. lia.
  - unfold d_obj. cbn [dobj_off]. lia.
  - right. rewrite Hsp4. unfold d_obj, REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK, MFRAME, LLVMF_STK in *.
    cbn [dobj_off]. lia.
  - exact SAm.
  - exact SRa.
  - exact SSh.
  - exact LSg.
  - exact GSg.
  - left. unfold d_obj. cbn [dobj_off]. lia. }
intros W2 c2 _ Hpost. apply SRr_ret.
destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HPR & Hra2 & H10 & Hfr2 & Hperm2 & HK & HGg & HGok & HGs).
assert (HC2 : DCTX cx ly2 S2 W2 mem2 md2 k) by (split; [exact Hbase | split; [exact HJ2 | rewrite Hfr2; exact Hfrs]]).
assert (HK' : cl_kept B ly3 S3 W (ms_mem ms) W2 mem2 (d_A cx - REAC_DISCO_GATE_SHOULD_PUSH_STK) (d_A cx)
  (fun a => d_obj cx OG <= a < d_obj cx OG + 264))
  by (unfold treac_disco_gate_should_push_kept in HK; rewrite Hsp4 in HK; exact HK).
pose proof (s2_base_call cx h i n now op nb fr len (ms_regs ms) regs2 ly3 S3 W (ms_mem ms) md4 k ly2 S2 W2 mem2 md2 k
  (d_A cx - REAC_DISCO_GATE_SHOULD_PUSH_STK) (d_A cx) (fun a => d_obj cx OG <= a < d_obj cx OG + 264) [OG]
  HB4 HC4 HC2 HK'
  ltac:(unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK, MFRAME, LLVMF_STK in *; lia) (Z.le_refl _)
  ltac:(intros a Ha; unfold d_obj in Ha; cbn [dobj_off] in Ha; unfold DFRAME_SIZE; lia)
  ltac:(intros a Ha _; apply Exists_cons_hd; exact Ha)
  ltac:(apply Forall_cons; [|apply Forall_nil];
        exists (fst (GateModel.gate_model G4 Sg now)); split; [exact (proj1 HGok)|]; split; [exact HGg | exact HGok])
  Hperm2 HPR) as HB2.
unfold cl_GR, d_at. exists fq, ly2, S2, regs2, mem2, md2, k, acc.
split; [rewrite Hc2, R1; reflexivity|].
split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|]. split; [exact Hk|].
split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); unfold cl_kmax in *; lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
exists Sg, (fst (GateModel.gate_model G4 Sg now)), (snd (GateModel.gate_model G4 Sg now)).
split; [exact HB2|].
split; [exact (cl_cs (ms_regs ms) regs2 22 _ HPR ltac:(unfold acallee_saved; lia)
  (eq_trans (RG 22%bv ltac:(clear; cbv; tauto)) R22))|].
split; [split; [exact LSg|]; split; [exact HGs | exact FSg]|].
split; [split; [exact (proj1 HGok)|]; split; [exact HGg | exact HGok]|].
split; [exact H10|].
pose proof (slot_classify.gm_push G4 Sg now) as Hpu. lia.
Qed.

End h.
End f.
End d.
