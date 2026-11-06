(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its addresses changed; 1441 of its 1611 lines of code are new or changed and 973 lines of the source are left out. *)
(* Piece C of segment J of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan 0x81a30 .. 0x81ab4):
   j_C_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_Jcut.v, from Pj1 (BASE + 0x1324) to Pj2 (BASE + 0x13a8).

   The code (BASE + 0x1324 .. BASE + 0x13a8), with said = &id.model_name (a4), fam = s9:
     0x1324 beqz s7          s7 = has_model_name: 0 takes the family path
     0x1328 lbu a0,0(a4)     the first byte of id.model_name
     0x132c bnez a0          not 0: the stem is id.model_name (a4 already holds it)
     0x1330 addiw s9,s9,-1   the family path: fam - 1
     0x1338 bltu a0,s9       2 <u fam - 1 (fam = 0 or fam >= 4): the stem is "REAC" (0x1364)
     0x133c .. 0x1358        a0 = switch.table + 8 * (fam - 1), its shadow byte tested (0 by the table's
                             own shadow: the table is a registered global)
     0x135c ld a4,0(a0)      the stem is the table's entry
     0x136c mv s7,a4         the stem is kept in s7
     0x1370 addi s2,a2,688   s2 = w4 (SF + V_w4)
     0x1374 sb zero,86(s3)   w4's shadow granule is made usable
     0x1378 sd zero,208(s1)  n4 := 0 (mf + M_n1)
     0x137c sd zero,200(s1)  ld := 0 (mf + M_n2)
     0x1390 jal put_dec      put_dec(w4, &n4, in, 2)
     0x13a4 jal put_dec      put_dec(w4, &n4, out, 2)
   The abort at 0x82514 (the table's shadow byte non-zero) is refuted by the table's shadow; the two calls are
   the contract's put_dec (HPD, tput_dec_spec) in the caller-journal form. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require put_dec reac_box_name.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require
SlotModel RcIdentModel IdentSpec put_dec_c disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_Jcut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the address arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model of the stem ----------------------------------------------------------------------- *)
Module JCModel.
Import RcIdentModel SlotModel.
Lemma fam_cmp_range : forall hw, 0 <= fam_cmp hw <= 3.
Proof.
intros hw. unfold fam_cmp. cbv zeta.
destruct (list_eq_dec Z.eq_dec _ _); [lia|].
destruct (list_eq_dec Z.eq_dec _ _); [lia|].
destruct (list_eq_dec Z.eq_dec _ _); lia.
Qed.
Lemma FAM_range : forall inp i, 0 <= FAM (rec_id inp i) <= 3.
Proof.
intros inp i. rewrite (rec_P7 inp i). unfold fam_hw.
destruct (rec_have inp i =? 0); [lia | apply fam_cmp_range].
Qed.
Lemma fam_range : forall inp, 0 <= n_fam inp <= 127.
Proof.
intros inp. unfold n_fam. destruct (128 <=? t_fam_raw inp).
- pose proof (Z.land_ones (t_fam_raw inp) 7 ltac:(lia)) as Hl.
  change (Z.ones 7) with 127 in Hl. change (2 ^ 7) with 128 in Hl. rewrite Hl.
  pose proof (Z.mod_pos_bound (t_fam_raw inp) 128 ltac:(lia)). lia.
- unfold idT. pose proof (FAM_range inp (nrecn inp)). lia.
Qed.
Lemma stem_said : forall inp, n_use_said inp = true -> n_stem inp = name_str (idT inp).
Proof. intros inp H. unfold n_stem. rewrite H. reflexivity. Qed.
Lemma stem_img_of : forall inp, n_use_said inp = false -> n_stem inp = stem_img (n_fam inp).
Proof. intros inp H. unfold n_stem. rewrite H. reflexivity. Qed.
Lemma use_said_false_nm : forall inp, has_model_name (idT inp) = 0 -> n_use_said inp = false.
Proof.
intros inp H. unfold n_use_said, n_said. rewrite H. reflexivity.
Qed.
Lemma use_said_false_b0 : forall inp, bz (nthb (model_name (idT inp)) 0) = 0 -> n_use_said inp = false.
Proof.
intros inp H. unfold n_use_said. rewrite H. cbn [Z.eqb negb]. apply andb_false_r.
Qed.
Lemma use_said_true : forall inp, has_model_name (idT inp) <> 0 ->
  bz (nthb (model_name (idT inp)) 0) <> 0 -> n_use_said inp = true.
Proof.
intros inp H1 H2. unfold n_use_said, n_said.
rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.
(* The model's stem is the bytes reac_box_name's model gives the three table entries. *)
Lemma stem_img_REAC : forall f, f <> 1 -> f <> 2 -> f <> 3 ->
  map bz (stem_img f) = disco_box_name_model.bn_STEM 0.
Proof.
intros f H1 H2 H3. unfold stem_img, disco_box_name_model.bn_STEM.
rewrite (proj2 (Z.eqb_neq f 1) H1), (proj2 (Z.eqb_neq f 2) H2), (proj2 (Z.eqb_neq f 3) H3).
vm_compute. reflexivity.
Qed.
Lemma stem_img_STEM : forall f, map bz (stem_img f) = disco_box_name_model.bn_STEM f.
Proof.
intros f. unfold stem_img, disco_box_name_model.bn_STEM.
destruct (f =? 1); [vm_compute; reflexivity|]. destruct (f =? 2); [vm_compute; reflexivity|].
destruct (f =? 3); vm_compute; reflexivity.
Qed.
Lemma stem_nz : forall inp j, (j < length (n_stem inp))%nat -> bz (nthb (n_stem inp) j) <> 0.
Proof.
intros inp j Hj. unfold n_stem in *. destruct (n_use_said inp).
- unfold name_str in *. unfold nthb. rewrite length_firstn in Hj.
  rewrite SlotModel.nth_first by lia.
  revert Hj. generalize (model_name (idT inp)) as l. clear.
  intros l. generalize j. clear j. induction l as [|x l IH]; intros [|j] Hj; cbn [first_zero length] in *.
  + lia.
  + lia.
  + revert Hj. destruct (Z.eqb_spec (bz x) 0) as [E|E]; intros Hj; [lia | exact E].
  + revert Hj. destruct (Z.eqb_spec (bz x) 0) as [E|E]; intros Hj; [lia|]. cbn [nth]. apply IH. lia.
- revert Hj. unfold stem_img, str_bytes, nthb.
  destruct (n_fam inp =? 1); [|destruct (n_fam inp =? 2); [|destruct (n_fam inp =? 3)]];
  cbn [list_ascii_of_string map length];
  (do 8 (destruct j as [|j]; [cbn; try lia; vm_compute; discriminate|]); cbn; lia).
Qed.
End JCModel.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation HBLOCKS := (hblocks B).

(* ---- what this piece takes, each as the contract's Section states it ------------------------------------ *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis G_SW : In (VAL (A_OBJ 7), 24) G.
Hypothesis G_REAC : In (VAL (A_OBJ 8), 5) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.

(* ---- the shared layer of segment J, at this Section's variables ----------------------------------------- *)
#[local] Notation jcut := (LLVMFuzzerTestOneInput_Jcut.jcut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation jc := (LLVMFuzzerTestOneInput_Jcut.jc B).

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- small memory facts ---------------------------------------------------------------------------------- *)
Lemma jc_bz : forall b : byte, 0 <= bz b < 256.
Proof.
intros b. unfold RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 b) as Hb.
change (bv_modulus 8) with 256 in Hb. exact Hb.
Qed.
Lemma jc_zext8 : forall b : byte, zext 64 (bv_extract 0 8 (w64 (bz b))) = w64 (bz b).
Proof.
intros b. unfold RcIdentModel.bz, w64. rewrite b_extract8_id. apply bv_eq.
unfold zext. rewrite bv_zero_extend_unsigned by lia. rewrite Z_to_bv_unsigned.
symmetry. apply bv_wrap_small. pose proof (bv_unsigned_in_range 8 b) as Hr.
change (bv_modulus 8) with 256 in Hr. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma jc_byte_of_bz : forall b : byte, Z_to_bv 8 (bz b) = b.
Proof. intros b. unfold RcIdentModel.bz. apply Z_to_bv_bv_unsigned. Qed.
Lemma jc_nth_map : forall (l : list byte) j, nth j (map (fun b : byte => bv_unsigned b) l) 0 = bz (nthb l j).
Proof.
unfold RcIdentModel.nthb, RcIdentModel.bz.
intros l; induction l as [|x l IH]; intros [|j]; cbn [map nth]; first [ apply IH | reflexivity ].
Qed.
Lemma jc_vm1 : forall (W : world SEGS) mem a v, aview SEGS (w_H W) mem a = Some v ->
  val_mem SEGS (rd W mem) a 1 v.
Proof.
intros W mem a v Hv k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (rd W mem) a) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_wrap.
change (bv_modulus 8) with 256 in *. change (2 ^ 8) with 256.
repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
Lemma jc_aview_garr8 : forall (W : world SEGS) mem a l i,
  garr8 SEGS (rd W mem) a l -> 0 <= i < Z.of_nat (length l) ->
  aview SEGS (w_H W) mem (a + i) = Some (nth (Z.to_nat i) l 0).
Proof.
intros W mem a l i Hg Hi.
assert (Hj : (Z.to_nat i < length l)%nat) by lia.
pose proof (garr8_mbyte SEGS (rd W mem) a l (Z.to_nat i) Hg Hj) as Hm.
rewrite Z2Nat.id in Hm by lia.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. exact (proj2 (Hg (Z.to_nat i) Hj)).
Qed.
Lemma jc_garr8_app : forall m a (l1 l2 : list Z),
  garr8 SEGS m a l1 -> garr8 SEGS m (a + Z.of_nat (length l1)) l2 -> garr8 SEGS m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. exact (H1 j Hlt).
- rewrite app_nth2 by exact Hge.
  destruct (H2 (j - length l1)%nat ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
  replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. exact Hv.
Qed.
Lemma jc_rom_vis : forall (H : word -> bool) (m : word -> option byte) x,
  seg_rom SEGS (Z_to_bv 64 x) <> None -> aview SEGS H m x <> None.
Proof.
intros H m x Hr E. apply Hr. unfold aview, mbyte, mrestrict in E.
destruct (seg_rom SEGS (Z_to_bv 64 x)) as [b|]; [|reflexivity]. exfalso.
destruct (H (Z_to_bv 64 x)); [cbn in E; discriminate E|].
destruct (m (Z_to_bv 64 x)); cbn in E; discriminate E.
Qed.
(* A shadow cell a run wrote 0 to (J.v's jsh0). *)
Lemma jc_sh0 : forall E (m : word -> option byte) H n b cs lo hi wlo whi od,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 (SLit 0))) cs -> aview SEGS H m (b + od) = Some 0.
Proof.
intros E m H n b cs lo hi wlo whi od HR Hb Hin. apply aview_of_val_mem1; [|lia].
exact (field_of_region E (mrestrict H m) n b cs lo hi wlo whi od 1%N (SLit 0) 0 HR Hb Hin eq_refl
  ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* ---- the keep across a call, as Jcut states it ------------------------------------------------------------ *)
#[local] Notation jcls := (LLVMFuzzerTestOneInput_Jcut.jcls B).
#[local] Notation jkeep4 := (LLVMFuzzerTestOneInput_Jcut.jkeep4 B).
#[local] Notation jvm4 := (LLVMFuzzerTestOneInput_Jcut.jvm4 B).
#[local] Notation jga4 := (LLVMFuzzerTestOneInput_Jcut.jga4 B).
#[local] Notation jcut_mk4 := (LLVMFuzzerTestOneInput_Jcut.jcut_mk4 B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS MTL HMT0).
(* The bytes of the image a call keeps (tcj_kept's third clause), which jkeep4 does not speak of: the stem of
   the family table and "REAC" live there. *)
Definition jcimg (W2 : world SEGS) (mem2 : word -> option byte) (W3 : world SEGS)
  (mem3 : word -> option byte) : Prop :=
  forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a.
Lemma jcimg_refl : forall W m, jcimg W m W m.
Proof. intros W m a _ _ _. reflexivity. Qed.
Lemma jcimg_trans : forall W1 m1 W2 m2 W3 m3, jcimg W1 m1 W2 m2 -> jcimg W2 m2 W3 m3 -> jcimg W1 m1 W3 m3.
Proof. intros W1 m1 W2 m2 W3 m3 H1 H2 a Ha Ho He. rewrite (H2 a Ha Ho He). exact (H1 a Ha Ho He). Qed.

(* ---- the stem, in the two places it can live --------------------------------------------------------------- *)
Lemma jc_nth_skipn : forall (l : list byte) m j d, nth j (skipn m l) d = nth (m + j) l d.
Proof.
induction l as [|x l IH]; intros [|m] j d; cbn; try reflexivity.
- destruct j; reflexivity.
- destruct m; [reflexivity | apply IH].
Qed.
Lemma jc_fz_le : forall l, (RcIdentModel.first_zero l <= length l)%nat.
Proof.
induction l as [|x l IH]; cbn [RcIdentModel.first_zero length]; [lia|].
destruct (bz x =? 0); lia.
Qed.
Lemma jc_fz_nth : forall l, (RcIdentModel.first_zero l < length l)%nat ->
  bz (nthb l (RcIdentModel.first_zero l)) = 0.
Proof.
induction l as [|x l IH]; cbn [RcIdentModel.first_zero length]; intros H; [lia|].
unfold RcIdentModel.nthb. destruct (Z.eqb_spec (bz x) 0) as [E|E]; [exact E|].
cbn [nth]. apply IH. lia.
Qed.
(* the stem of a state whose id has a model name: id.model_name, inside the side frame *)
Lemma jc_stem_said : forall g pos mf nm tk dp ly2 S2 (W : world SEGS) mem md k,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W mem md k ->
  frames S2 = [(4, pos)] -> jlay g pos mf nm tk dp -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  id_at g pos (m_nrec g) W mem -> SlotModel.n_use_said (e_pl g) = true ->
  jstem_at g pos mf W mem (SFa g pos + V_id + 3).
Proof.
intros g pos mf nm tk dp ly2 S2 W mem md k HJ Hfrs Hlay Hmfb Hid Hsaid.
pose proof Hlay as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp).
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & Hly2 & _). pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS ly2 S2 W mem md 4 pos HAR Hin4) as (_ & _ & HFpres & _).
change (fs_frame_bytes 4) with 1024 in HFpres. rewrite EFa in HFpres.
destruct Hid as (Hidb & Hidz & Hidk).
assert (Lid : length (m_id g (m_nrec g)) = 38%nat)
  by (unfold m_id; rewrite SlotModel.rec_id_length; reflexivity).
assert (Hst : SlotModel.n_stem (e_pl g) = SlotModel.name_str (m_id g (m_nrec g)))
  by (exact (JCModel.stem_said (e_pl g) Hsaid)).
assert (HL : (length (SlotModel.n_stem (e_pl g)) <= 16)%nat)
  by (rewrite Hst; unfold m_id; apply SlotModel.name_str_len).
assert (Lmn : length (RcIdentModel.model_name (m_id g (m_nrec g))) = 17%nat)
  by (unfold RcIdentModel.model_name, RcIdentModel.get, RcIdentModel.OFF_NAME, RcIdentModel.NAME_CAP;
      rewrite length_firstn, length_skipn, Lid; reflexivity).
assert (HLfz : length (SlotModel.n_stem (e_pl g))
                 = RcIdentModel.first_zero (RcIdentModel.model_name (m_id g (m_nrec g)))).
{ rewrite Hst. unfold SlotModel.name_str. rewrite length_firstn.
  pose proof (jc_fz_le (RcIdentModel.model_name (m_id g (m_nrec g)))). lia. }
(* a byte of model_name is a byte of id, three on *)
assert (Hmn : forall j, (j < 17)%nat ->
  nthb (RcIdentModel.model_name (m_id g (m_nrec g))) j = nthb (m_id g (m_nrec g)) (3 + j)).
{ intros j Hj. unfold RcIdentModel.model_name, RcIdentModel.get, RcIdentModel.OFF_NAME,
    RcIdentModel.NAME_CAP, RcIdentModel.nthb.
  rewrite (SlotModel.nth_first (skipn 3 (m_id g (m_nrec g))) 17 j (zb 0) Hj). apply jc_nth_skipn. }
assert (Hbyte : forall j, (j <= length (SlotModel.n_stem (e_pl g)))%nat ->
  bz (nthb (SlotModel.n_stem (e_pl g) ++ [zb 0]) j) = bz (nthb (m_id g (m_nrec g)) (3 + j))).
{ intros j Hj. rewrite <- (Hmn j ltac:(lia)).
  destruct (Nat.eq_dec j (length (SlotModel.n_stem (e_pl g)))) as [He | Hne].
  - rewrite He.
    replace (bz (nthb (SlotModel.n_stem (e_pl g) ++ [zb 0]) (length (SlotModel.n_stem (e_pl g))))) with 0
      by (unfold RcIdentModel.nthb; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity).
    rewrite HLfz. symmetry.
    exact (jc_fz_nth (RcIdentModel.model_name (m_id g (m_nrec g))) ltac:(lia)).
  - replace (nthb (SlotModel.n_stem (e_pl g) ++ [zb 0]) j) with (nthb (SlotModel.n_stem (e_pl g)) j)
      by (unfold RcIdentModel.nthb; symmetry; apply app_nth1; lia).
    f_equal. rewrite Hst. unfold SlotModel.name_str, RcIdentModel.nthb.
    apply SlotModel.nth_first. rewrite <- HLfz. lia. }
unfold jstem_at.
split; [exact HL|].
split; [intros j Hj; exact (JCModel.stem_nz (e_pl g) j Hj)|].
split.
{ unfold bytes_at8. intros j Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
  destruct (Hidb (3 + j)%nat ltac:(rewrite length_map, Lid; lia)) as [Hv Hr].
  rewrite jc_nth_map in Hv, Hr. rewrite jc_nth_map.
  rewrite (Hbyte j ltac:(lia)). split; [|apply jc_bz].
  replace (SFa g pos + V_id + 3 + Z.of_nat j) with (SFa g pos + V_id + Z.of_nat (3 + j)) by lia.
  exact Hv. }
split.
{ apply (range_addressable_sub _ _ (SFa g pos + V_id) 32).
  - apply zero_shadow_range; [unfold V_id; clear - HSF64; lia | reflexivity|].
    unfold sh_zero, zero_shadow in *. intros i Hi. apply Hidz. unfold N_id in *. cbn in Hi |- *. lia.
  - unfold V_id. lia.
  - unfold V_id. lia. }
split.
{ intros x Hx. apply (aview_some_of_apresent SEGS). apply HFpres.
  pose proof (Z.mod_pos_bound (SFa g pos + V_id + 3 + Z.of_nat (length (SlotModel.n_stem (e_pl g)))) 8
    ltac:(lia)) as Hm8.
  unfold V_id in *. clear - Hx Hm8 HL HSF0. lia. }
split.
{ apply (in_app_sub (SFa g pos) 1024); [exact HSFapp | unfold V_id; lia | lia | unfold V_id; lia]. }
split; [unfold V_id; lia|].
split; [unfold V_id; clear - HSF1 HL C1; lia|].
intros a Ha. apply (jnwj g pos mf nm tk dp a Hlay Hmfb).
right; right; left. unfold V_id in *. clear - Ha HL. lia.
Qed.
(* the stem of a state with no model name: a string of the image (the family table, or "REAC") *)
Lemma jc_stem_imgstr : forall g pos mf nm tk dp ly2 S2 (W : world SEGS) mem md k a (s : list byte),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W mem md k ->
  frames S2 = [(4, pos)] -> jlay g pos mf nm tk dp -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  SlotModel.n_stem (e_pl g) = s -> (length s <= 16)%nat ->
  reac_box_name.rbn_imgstr B G W mem a (map bz s) ->
  jstem_at g pos mf W mem a.
Proof.
intros g pos mf nm tk dp ly2 S2 W mem md k a s HJ Hfrs Hlay Hmfb Hst HL Himg.
pose proof Hlay as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp).
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & Hly2 & _). pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof (frm_off_imgP B ly2 S2 W mem md 4 pos HAR Hin4) as Hfimg.
change (fs_frame_bytes 4) with 1024 in Hfimg. rewrite EFa in Hfimg.
destruct Himg as (Hlo & Hhi & Hnz & Hga & Hglob & Hfix & Htail).
rewrite length_map in Hhi, Hglob, Hfix, Htail.
assert (HBS : map (fun b : byte => bv_unsigned b) (s ++ [zb 0]) = map bz s ++ [0])
  by (rewrite map_app; reflexivity).
unfold jstem_at. rewrite Hst.
split; [exact HL|].
split.
{ intros j Hj. rewrite Forall_forall in Hnz.
  pose proof (Hnz (bz (nthb s j)) ltac:(apply in_map; unfold RcIdentModel.nthb; apply nth_In; lia)). lia. }
split; [unfold bytes_at8; rewrite HBS; exact Hga|].
split.
{ destruct Hglob as (q & z & Hin & H1 & H2).
  exact (ro_usable_glob SEGS B G ly2 S2 W mem md q z a (Z.of_nat (length s) + 1) GM Hin HAR H1 H2). }
split.
{ intros x Hx. apply jc_rom_vis. apply Htail. exact Hx. }
split.
{ unfold in_app, kLowShadowBeg. clear - Hlo Hhi. split; [lia | left; lia]. }
split; [clear - Hlo; lia|].
split; [clear - Hhi C1; lia|].
intros x Hx HW. unfold WJ, shadow_addr, SHADOW_OFF in HW. unfold ASTACK in Hmf0.
assert (HSF8 : SFa g pos / 8 <= SFa g pos) by (apply Z.div_le_upper_bound; lia).
assert (HSF8' : 0 <= SFa g pos / 8) by (apply Z.div_pos; lia).
clear - HW Hx Hlo Hhi C1 Hfimg HSF0 HSF1 HSF8 HSF8' Hmf0. lia.
Qed.

(* ---- what a caller-journal call asks of its buffers, and what it keeps ------------------------------------ *)
Lemma jc_mod4096_mod8 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof.
intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|].
destruct H as [q ->]. exists (512 * q). lia.
Qed.
(* bytes of the machine stack above sp, inside the caller's window *)
Lemma jc_tsrc_stack : forall STK sp0 FP ly S W0 mem md own lyc Sc (W : world SEGS) memc mdc k sp q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  sp0 - STK <= q -> q + n + 64 <= sp0 -> 0 < n -> sp <= q ->
  tsrc_ok W memc sp q n.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k sp q n HJ Hlo Hhi Hn Hsp.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS lyc Sc W memc mdc (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
  HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
rewrite Elo, Ehi in Hz. rewrite Elo in Hpal. rewrite Ehi in Hpah.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (lo := ly_stk_lo ly) in *. set (hi := ly_stk_hi ly) in *.
assert (Dlo : lo = 4096 * (lo / 4096)) by (clear - Hpal; lia).
assert (Dhi : hi = 4096 * (hi / 4096)) by (clear - Hpah; lia).
split.
{ intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply Hpres; lia | lia]. }
split.
{ eapply range_addressable_sub; [apply zero_shadow_range; [exact (jc_mod4096_mod8 _ Hpal) | | exact Hz] | lia | lia].
  clear - Dlo Dhi. lia. }
split.
{ intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
  assert (Hi : 0 <= s - shadow_of_addr SHADOW_OFF lo < (hi - lo) / 8).
  { unfold shadow_of_addr, SHADOW_OFF. clear - Hs Dlo Dhi Hlo Hhi Hslo Hshi Hn. lia. }
  specialize (Hz _ Hi). replace (shadow_of_addr SHADOW_OFF lo + (s - shadow_of_addr SHADOW_OFF lo)) with s in Hz by lia.
  rewrite Hz. discriminate. }
split; [unfold amem_range; right; rewrite C3, C4; lia|].
lia.
Qed.
(* bytes of a side-stack frame inside an 8-aligned range whose shadow is zero *)
Lemma jc_tsrc_frame : forall STK sp0 FP ly S W0 mem md own lyc Sc (W : world SEGS) memc mdc k sp cid pos a0 N q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= a0 -> a0 + N <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  a0 mod 8 = 0 -> N mod 8 = 0 -> zero_shadow (aview SEGS (w_H W) memc) SHADOW_OFF a0 N ->
  a0 <= q -> q + n <= a0 + N -> 0 < n -> alloc_ceiling <= sp - ESTACK ->
  tsrc_ok W memc sp q n.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k sp cid pos a0 N q n HJ Hin H1 H2 Ha0 HN Hz Hq1 Hq2 Hn Hsp.
pose proof HJ as (HAR & _).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (_ & Happ & Hpres & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F0 & F1 & _).
pose proof asan_consts as (C1 & _).
split.
{ intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply Hpres; lia | lia]. }
split; [eapply range_addressable_sub; [apply zero_shadow_range; [exact Ha0 | exact HN | exact Hz] | lia | lia]|].
split; [apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memc mdc cid pos); [exact HAR | exact Hin | lia | lia | lia]|].
split; [apply (amem_range_sub_app (frame_addr lyc cid pos) (fs_frame_bytes cid)); [exact Happ | lia | lia | lia | lia]|].
lia.
Qed.
(* the caller lets a callee write bytes of its own frame, or of its stack window above sp *)
Lemma jc_twr_frame : forall STK sp0 FP ly S W0 mem md lyc Sc (W : world SEGS) memc mdc k sp pos q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem md [(4, pos)] lyc Sc W memc mdc k ->
  frame_addr lyc 4 pos <= q -> q + n <= frame_addr lyc 4 pos + 1024 -> alloc_ceiling <= sp - ESTACK ->
  twr_ok B STK sp0 FP ly S lyc Sc [(4, pos)] W memc sp q n.
Proof.
intros STK sp0 FP ly S W0 mem md lyc Sc W memc mdc k sp pos q n HJ H1 H2 Hsp a Ha.
assert (Hw : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc [(4, pos)] a).
{ right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  change (fs_frame_bytes 4) with 1024. lia. }
destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
pose proof HJ as (HAR & _). pose proof (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR) as Fb.
split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|].
pose proof asan_consts as (C1 & _).
assert (Hin : In (4, pos) (frames Sc)) by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
destruct (Fb Hin) as (_ & F1 & _). change (fs_frame_bytes 4) with 1024 in F1. lia.
Qed.
Lemma jc_twr_stack : forall STK sp0 FP ly S W0 mem md own lyc Sc (W : world SEGS) memc mdc k sp q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  sp0 - STK <= q -> q + n <= sp0 -> sp <= q ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc sp q n.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k sp q n HJ H1 H2 H3 a Ha.
assert (Hw : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) by (left; lia).
destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho | lia].
Qed.
(* what a call kept, at the bytes the cuts and the stem read *)
Lemma jc_keep_call : forall g pos mf ly2 S2 lyc Sc (W : world SEGS) memc (W3 : world SEGS) mem3 sp STK'
  (E Zs : Z -> Prop),
  tcj_kept B STK' lyc Sc W memc W3 mem3 sp E ->
  frames Sc = [(4, pos)] -> frame_addr lyc 4 pos = SFa g pos ->
  ablocks B lyc Sc = ablocks B ly2 S2 -> alloc_ceiling <= mf ->
  (forall a, sp - STK' <= a < sp -> Zs a) -> (forall a, E a -> Zs a) ->
  (forall a, 0 <= a < 2 ^ 64 -> jcls g pos mf ly2 S2 a -> ~ Zs a ->
     aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W) memc a) /\ jcimg W memc W3 mem3.
Proof.
intros g pos mf ly2 S2 lyc Sc W memc W3 mem3 sp STK' E Zs HK Hfrs EFa Hbl Hmfc Hwin HE.
destruct HK as (K1 & K2 & K3 & K4 & _ & _).
split; [|intros a Ha Ho He; exact (K3 a Ha Ho He)].
intros a Ha Hcls HZ.
destruct Hcls as [H1 | [(p & n & Hin & Hr) | [H3 | H4]]].
- apply K1; [lia | intros Hw; exact (HZ (Hwin a Hw)) | intros Hx; exact (HZ (HE a Hx))].
- pose proof (K2 p n (a - p) ltac:(rewrite Hbl; exact Hin) ltac:(lia)
    ltac:(intros Hx; apply HZ; apply HE; replace a with (p + (a - p)) by lia; exact Hx)) as HH.
  replace (p + (a - p)) with a in HH by lia. exact HH.
- apply (K4 4 pos a); [rewrite Hfrs; left; reflexivity | | intros Hx; exact (HZ (HE a Hx))].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4) with 1024. lia.
- apply (K4 4 pos a); [rewrite Hfrs; left; reflexivity | | intros Hx; exact (HZ (HE a Hx))].
  right. unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 4 / 8) with 128. lia.
Qed.
(* id and an image string, moved to a state that kept their bytes *)
Lemma jc_id_keep : forall g pos mf nm tk dp ly2 S2 (W : world SEGS) m (W3 : world SEGS) m' i,
  jkeep4 g pos mf ly2 S2 W m W3 m' -> jlay g pos mf nm tk dp -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  id_at g pos i W m -> id_at g pos i W3 m'.
Proof.
intros g pos mf nm tk dp ly2 S2 W m W3 m' i HK0 Hlay Hmfb (Hb & Hz & Hk).
pose proof Hlay as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp).
pose proof asan_consts as (C1 & _).
assert (HK : forall a, 0 <= a < 2 ^ 64 ->
  ((SFa g pos <= a < SFa g pos + 528) \/ (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 66)) ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W) m a).
{ intros a Ha Hr. apply HK0; [exact Ha | apply (jnwj g pos mf nm tk dp a Hlay Hmfb) |].
  - destruct Hr as [Hr | Hr]; [right; right; left; exact Hr | right; right; right; right; left; exact Hr].
  - destruct Hr as [Hr | Hr]; [right; right; left; clear - Hr HSF0 HSF1 C1; lia
    | right; right; right; clear - Hr; lia]. }
assert (SH : forall j, 0 <= j < 66 ->
  aview SEGS (w_H W3) m' (shadow_addr (SFa g pos) + j) = aview SEGS (w_H W) m (shadow_addr (SFa g pos) + j)).
{ intros j Hj. apply HK; [unfold shadow_addr, SHADOW_OFF; clear - Hj HSF0 HSF1 C1;
    assert (0 <= SFa g pos / 8) by (apply Z.div_pos; lia);
    assert (8 * (SFa g pos / 8) <= SFa g pos) by (apply Z.mul_div_le; lia); lia|].
  right. lia. }
split; [|split].
- unfold bytes_at8 in *. apply (j_garr8_moved SEGS (w_H W) (w_H W3) m m'); [|exact Hb].
  intros j Hj. rewrite length_map in Hj. unfold m_id in Hj. rewrite SlotModel.rec_id_length in Hj.
  apply HK; [unfold V_id, RcIdentModel.ID_SIZE in *; clear - Hj HSF0 HSF1 C1; lia|].
  left. unfold V_id, RcIdentModel.ID_SIZE in *. clear - Hj. lia.
- unfold sh_zero in *. apply (j_zero_shadow_moved (aview SEGS (w_H W) m)); [|exact Hz].
  intros j Hj. unfold shadow_of_addr. unfold V_id, N_id in *.
  replace (SHADOW_OFF + (SFa g pos + 352) / 8 + j) with (shadow_addr (SFa g pos) + (44 + j))
    by (unfold shadow_addr; clear - HSF64 Hj; lia).
  apply SH. clear - Hj. cbn in Hj. lia.
- unfold sh_blk in *. apply (j_block_shadow_moved (aview SEGS (w_H W) m)); [|exact Hk].
  intros j Hj. unfold shadow_of_addr. unfold V_id, N_id in *.
  replace (SHADOW_OFF + (SFa g pos + 352) / 8 + j) with (shadow_addr (SFa g pos) + (44 + j))
    by (unfold shadow_addr; clear - HSF64 Hj; lia).
  apply SH. clear - Hj. cbn in Hj. lia.
Qed.
Lemma jc_imgstr_keep : forall (W : world SEGS) m (W3 : world SEGS) m' a l,
  jcimg W m W3 m' -> reac_box_name.rbn_imgstr B G W m a l -> reac_box_name.rbn_imgstr B G W3 m' a l.
Proof.
intros W m W3 m' a l HK (Hlo & Hhi & Hnz & Hga & Hglob & Hfix & Htail).
split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hnz|].
split.
- apply (j_garr8_moved SEGS (w_H W) (w_H W3) m m'); [|exact Hga].
  intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  destruct (Hfix (a + j) ltac:(lia)) as (I1 & I2 & I3). exact (HK (a + j) I1 I2 I3).
- split; [exact Hglob|]. split; [exact Hfix | exact Htail].
Qed.

(* ---- 0x81a78 .. 0x81ab4: w4, and the two calls of put_dec ------------------------------------------------- *)
(* the machine frame's counter slots and the shadow cell of w4, as the two runs write them *)
Definition jcA_mf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 160 216 200 216 [YP09.mkChunk 160 (CVal 8 (SOff 32 0))].
Definition jcA_sh : YP09.region := YP09.mkRegion (Some 19%nat) 86 87 86 87 [].
Definition ss_jcA : sstate := mkSS 0x136c sr_atoms [jcA_mf; jcA_sh] None (mkFacts [] [] []).
Definition jcB_mf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition ss_jcB : sstate := mkSS 0x1394 sr_atoms [jcB_mf] None (mkFacts [] [] []).
Ltac jget_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss ?ms =>
      let r := eval vm_compute in (nth_error (ss_mem ss) i) in
      lazymatch r with Some ?rg =>
        pose proof (st_ok_region_nth E (abs_ss val ss) ms i rg HS ltac:(vm_compute; reflexivity)) as HR end
  | st_ok ?segs ?E ?ss ?ms =>
      let r := eval vm_compute in (nth_error (ss_mem ss) i) in
      lazymatch r with Some ?rg =>
        pose proof (st_ok_region_nth E ss ms i rg HS ltac:(vm_compute; reflexivity)) as HR end
  end.
Ltac jc_breg HS r Hname :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?Ev ?ssx (restrict ?H ?msx) =>
      pose proof (st_ok_pi_restrict_reg H Ev ssx msx r HS) as Hname;
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      change (sr_get (ss_regs ssx) r) with e in Hname
  end.
Ltac jc_pres0 HP :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
  intros r Hr; pose proof (HP (bv_unsigned r)) as Hq; rewrite Z_to_bv_bv_unsigned in Hq; apply Hq;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- acallee_saved (bv_unsigned ?x) => let v := eval vm_compute in (bv_unsigned x) in
       change (bv_unsigned x) with v end; unfold acallee_saved; lia |]);
  destruct Hr.

Lemma jc_tail : forall g pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regsT memT mdT stemA,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 memT mdT (4 * Z.of_nat (m_nrec g) + 7) ->
  jkeep4 g pos mf ly2 S2 W2 mem2 W2 memT ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 26; 27]%bv -> getr regsT r = getr regs2 r) ->
  (forall fd, fd_lookup (m_fds mdT) fd = fd_lookup (m_fds md2) fd) -> m_fs mdT = m_fs md2 ->
  SlotModel.n_wok (e_pl g) = true ->
  getr regsT 27 = w64 (SlotModel.n_r (e_pl g)) ->
  getr regsT 26 = w64 (SFa g pos + V_nm) -> getr regsT 24 = w64 (SFa g pos + V_dp) ->
  getr regsT 12 = w64 (SFa g pos) -> getr regsT 14 = w64 stemA ->
  sh_zero W2 memT (SFa g pos + V_nm) N_nm -> sh_zero W2 memT (SFa g pos + V_dp) N_dp ->
  (forall (W3 : world SEGS) mem3 ly3 S3 md3 k3,
     ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
       ly3 S3 W3 mem3 md3 k3 -> frames S3 = [(4, pos)] ->
     jkeep4 g pos mf ly2 S2 W2 memT W3 mem3 -> jcimg W2 memT W3 mem3 ->
     jstem_at g pos mf W3 mem3 stemA) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x136c) regsT memT mdT)
    (jcut g pos mf nm tk dp (BASE + 0x13a8) (Pj2 g pos mf)).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regsT memT mdT stemA
  HJ2 Hfrs HKev MLE MOK HC HJC HJT KEEPT RKT HfdT HfsT Hwok R27 R26 R24 R12 R14 Hzn Hzd HST.
pose proof HC as HC0.
destruct HC0 as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfss & Hinb).
pose proof HJC as HJC0.
destruct HJC0 as (Hlay & Hid & Hid3 & Hhb & R20 & R21 & R22 & V184 & V152 & V144 & V160 & V168 & V136 & Hjb).
pose proof Hlay as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
unfold ASTACK in Hmf0.
pose proof HJT as (HART & HlyT & _ & _ & _ & _ & HnevT & _ & _ & _ & _ & _ & _ & HpresT & _).
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & Hnev2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS ly2 S2 W2 memT mdT 4 pos HART Hin4) as (_ & _ & HFpres & HFSpres).
change (fs_frame_bytes 4) with 1024 in HFpres, HFSpres. rewrite EFa in HFpres, HFSpres.
pose proof HPRE as (HFN & Hraz & _ & _ & _ & _ & _ & _ & Hnev0 & _).
(* the model *)
destruct (SlotModel.wok_chans (e_pl g) Hwok) as [Hin40 Hout40].
assert (Hlin : length (IdentSpec.DEC (SlotModel.t_in (e_pl g)) 2) = 2%nat)
  by (apply SlotModel.DEC2_len; lia).
assert (Hlout : length (IdentSpec.DEC (SlotModel.t_out (e_pl g)) 2) = 2%nat)
  by (apply SlotModel.DEC2_len; lia).
assert (Hdlin : put_dec_c.dec_len (SlotModel.t_in (e_pl g)) 2 = 2)
  by (unfold put_dec_c.dec_len; rewrite Hlin; reflexivity).
assert (Hdlout : put_dec_c.dec_len (SlotModel.t_out (e_pl g)) 2 = 2)
  by (unfold put_dec_c.dec_len; rewrite Hlout; reflexivity).
(* the two machine-frame words the runs read, at memT *)
assert (NWmf : forall a, mf <= a < mf + 200 -> ~ WJ g pos mf a)
  by (intros a Ha; apply (jnwj g pos mf nm tk dp a Hlay Hmfb); left; exact Ha).
assert (V160T : val_mem SEGS (rd W2 memT) (mf + 160) 8 (SlotModel.t_in (e_pl g))).
{ apply (jvm4 g pos mf ly2 S2 W2 mem2 W2 memT _ 8 _ KEEPT); [|exact V160].
  intros k Hk. cbn in Hk. split; [clear - Hk Hmf0 Hmfb Hsp47 C1; lia|].
  split; [apply NWmf; lia | left; lia]. }
assert (V168T : val_mem SEGS (rd W2 memT) (mf + 168) 8 (SlotModel.t_out (e_pl g))).
{ apply (jvm4 g pos mf ly2 S2 W2 mem2 W2 memT _ 8 _ KEEPT); [|exact V168].
  intros k Hk. cbn in Hk. split; [clear - Hk Hmf0 Hmfb Hsp47 C1; lia|].
  split; [apply NWmf; lia | left; lia]. }
(* ---- run 1: 0x136c .. the call at 0x1390 ---- *)
remember (Eimg (Ereg regsT [w64 (SlotModel.t_in (e_pl g))])) as EA eqn:HEA.
assert (HEIA : img_env VAL A_LIM EA) by (rewrite HEA; apply Eimg_env).
assert (EEA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EA n = getr regsT r)
  by (intros n r Hn; rewrite HEA; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ERA : regs_ok EA sr_atoms regsT) by (rewrite HEA; apply regs_ok_Eimg_Ereg).
assert (AGEA : env_agree 32 (Ereg regsT [w64 (SlotModel.t_in (e_pl g))]) EA)
  by (rewrite HEA; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EA32 : ew EA 32 = w64 (SlotModel.t_in (e_pl g)))
  by (rewrite HEA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsT _ 0)).
clear HEA.
assert (U9 : bv_unsigned (ew EA 9) = mf).
{ rewrite (EEA 9%nat 9%bv eq_refl), (RKT 9%bv ltac:(cbn; tauto)), Rs1. apply unsigned_lit_small.
  clear - Hmf0 Hmfb Hsp47 C1. lia. }
assert (HSH1 : 0 <= SFa g pos / 8 /\ 8 * (SFa g pos / 8) <= SFa g pos).
{ split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]. }
assert (U19 : bv_unsigned (ew EA 19) = shadow_addr (SFa g pos)).
{ rewrite (EEA 19%nat 19%bv eq_refl), (RKT 19%bv ltac:(cbn; tauto)), Rs3. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. clear - HSF0 HSF1 C1 HSH1. lia. }
assert (U12 : bv_unsigned (ew EA 12) = SFa g pos)
  by (rewrite (EEA 12%nat 12%bv eq_refl), R12; apply unsigned_lit_small; clear - HSF0 HSF1 C1; lia).
assert (HS : st_ok_pi SEGS VAL EA ss_jcA
  (restrict (w_H W2) (mkst regsT (Z_to_bv 64 (BASE + 0x136c)) memT (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_jcA. apply pa_entry_st_ok_full.
  - exact ERA.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold jcA_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [clear - Hmf0 C1; lia|]. split; [clear - Hmfb Hsp47; lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HpresT; clear - Ho Hmfb HSTK'; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS EA _ mf 160 8 (SOff 32 0) (SlotModel.t_in (e_pl g)));
        [cbn [sv_denot]; rewrite EA32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | clear - Hin40; cbn; lia | cbn; lia | exact V160T].
    + unfold jcA_sh, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
      split; [unfold shadow_addr, SHADOW_OFF; clear - HSF0 HSH1; lia|].
      split; [unfold shadow_addr, SHADOW_OFF; clear - HSF0 HSF1 C1 HSH1; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (shadow_addr (SFa g pos) + o) with (shadow_addr (SFa g pos) + 86) by lia.
      exact (proj1 (HFSpres 86 ltac:(cbn; lia))).
  - apply pairwise_disjoint_of_extents. unfold jcA_mf, jcA_sh, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold shadow_addr, SHADOW_OFF.
    clear - Hmf0 HSF0 HSF1 C1 HSH1. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x136c)) with (Z_to_bv 64 (BASE + 0x136c)).
paj_run_shc RUNP RUNC HS HJT.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U9 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. clear - Ha Hmfb HSTK'. lia.
  - eapply awr_ok_cons_gen; [reflexivity | exact U19 | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 4, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite EFa.
    change (fs_frame_bytes 4 / 8) with 128. clear - Ha. lia. }
(* what run 1 wrote: the two counter slots and w4's shadow cell *)
assert (KEEPA : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mf + 200 <= a < mf + 216 \/ a = shadow_addr (SFa g pos) + 86) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) memT a).
{ lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply (kept_of_frame (segs := SEGS) _ _ _ _ _
      (fun a => mf + 200 <= a < mf + 216 \/ a = shadow_addr (SFa g pos) + 86) HFr) end.
  intros bb wl wh aa Hin Hr.
  lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end.
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val] in Hr; rewrite ?U9, ?U19 in Hr;
      first [left; clear - Hr; lia | right; clear - Hr; lia] | ]).
  destruct Hin. }
clear HF HFr HG.
(* the two counter slots and the shadow cell, as run 1 left them *)
jget_region HS 0%nat RMF. jget_region HS 1%nat RSH.
cbn [ms_mem restrict] in RMF, RSH.
assert (V208 : val_mem SEGS (rd W2 (ms_mem ms)) (mf + 208) 8 0).
{ lazymatch type of RMF with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wl ?wh ?cs) =>
    exact (field_of_region EA (rd W2 (ms_mem ms)) 9%nat mf cs lo hi wl wh 208 8%N (SLit 0) 0 RMF U9
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) end. }
assert (V200 : val_mem SEGS (rd W2 (ms_mem ms)) (mf + 200) 8 0).
{ lazymatch type of RMF with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wl ?wh ?cs) =>
    exact (field_of_region EA (rd W2 (ms_mem ms)) 9%nat mf cs lo hi wl wh 200 8%N (SLit 0) 0 RMF U9
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) end. }
assert (SH86 : aview SEGS (w_H W2) (ms_mem ms) (shadow_addr (SFa g pos) + 86) = Some 0).
{ lazymatch type of RSH with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wl ?wh ?cs) =>
    exact (jc_sh0 EA (ms_mem ms) (w_H W2) 19%nat (shadow_addr (SFa g pos)) cs lo hi wl wh 86 RSH U19
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) end. }
assert (Esh688 : shadow_of_addr SHADOW_OFF (SFa g pos + V_w4) = shadow_addr (SFa g pos) + 86).
{ unfold shadow_of_addr, shadow_addr, V_w4. replace (SFa g pos + 688) with (SFa g pos + 86 * 8) by lia.
  rewrite Z.div_add by lia. lia. }
assert (Zw4 : sh_zero W2 (ms_mem ms) (SFa g pos + V_w4) N_w4).
{ unfold sh_zero, zero_shadow, N_w4. intros i Hi. cbn in Hi.
  replace i with 0 by lia. rewrite Z.add_0_r, Esh688. exact SH86. }
(* ---- 0x1390: put_dec(w4, &n4, in, 2) ---- *)
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (18%bv : bv 5) Q18.
prreg HS (23%bv : bv 5) Q23.
pose proof (regs_kept_of_st_ok SEGS EA _ (restrict (w_H W2) ms) regsT [w64 (SlotModel.t_in (e_pl g))]
  [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 26; 27]%bv HS AGEA ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite (HKR 2%bv ltac:(cbn; tauto)), (RKT 2%bv ltac:(cbn; tauto)), Rsp.
  unfold w64. apply unsigned_lit_small. clear - Hmf0 Hmfb Hsp47 C1. lia. }
pmkst HS. rewrite (PSIG IS_put_dec AF_put_dec eq_refl).
eapply SRr_bind.
{ apply (HPD LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2
    (ms_mem ms) _ (4 * Z.of_nat (m_nrec g) + 7) (ms_regs ms) (SFa g pos + V_w4) (mf + M_n1) 0
    (SlotModel.t_in (e_pl g)) 2 HJT).
  - rewrite Q1. apply ret_ok_codeptr_v; [clear - HBLO; lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by (clear - HBLO HBASE; lia). clear - HBLO. lia.
  - rewrite (HKR 3%bv ltac:(cbn; tauto)), (RKT 3%bv ltac:(cbn; tauto)). exact Rgp.
  - rewrite (HKR 4%bv ltac:(cbn; tauto)), (RKT 4%bv ltac:(cbn; tauto)). exact Rtp.
  - rewrite Q10, U12. unfold w64, V_w4. f_equal; lia.
  - rewrite Q11, U9. unfold w64, M_n1. f_equal; lia.
  - rewrite Q12, EA32. unfold w64. rewrite unsigned_lit_small by (clear - Hin40; lia).
    apply Z.mod_small. clear - Hin40. lia.
  - left. rewrite Q12, EA32. unfold w64. rewrite unsigned_lit_small by (clear - Hin40; lia).
    clear - Hin40. lia.
  - rewrite Q13. reflexivity.
  - lia.
  - rewrite Usp. exact Hmf32.
  - rewrite Usp. unfold put_dec.PUT_DEC_STK, ESTACK. clear - Hmfb HSTK'. lia.
  - rewrite Usp. clear - Hmfb. lia.
  - rewrite Hfrs. cbn [length]. lia.
  - unfold M_n1. clear - Hmf32. lia.
  - unfold V_w4. clear - HSF0. lia.
  - lia.
  - unfold M_n1. exact V208.
  - rewrite Usp. apply (jc_twr_stack LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] ly2 S2 W2 (ms_mem ms) _ (4 * Z.of_nat (m_nrec g) + 7) mf (mf + M_n1) 8 HJT);
      unfold M_n1; clear - Hmfb HSTK'; lia.
  - rewrite Usp, Z.add_0_r, Hdlin.
    apply (jc_twr_frame LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) ly2 S2 W2
      (ms_mem ms) _ (4 * Z.of_nat (m_nrec g) + 7) mf pos (SFa g pos + V_w4) 2 HJT);
      [rewrite EFa; unfold V_w4; lia | rewrite EFa; unfold V_w4; lia
      | unfold ESTACK; clear - Hmf0 HSF0 HSF1 C1; lia].
  - rewrite Usp. apply (jc_tsrc_stack LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] ly2 S2 W2 (ms_mem ms) _ (4 * Z.of_nat (m_nrec g) + 7) mf (mf + M_n1) 8 HJT);
      unfold M_n1; clear - Hmfb HSTK'; lia.
  - rewrite Usp, Z.add_0_r, Hdlin.
    apply (jc_tsrc_frame LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
      ly2 S2 W2 (ms_mem ms) _ (4 * Z.of_nat (m_nrec g) + 7) mf 4 pos (SFa g pos + V_w4) 8
      (SFa g pos + V_w4) 2 HJT ltac:(rewrite Hfrs; left; reflexivity));
      [rewrite EFa; unfold V_w4; lia | rewrite EFa; change (fs_frame_bytes 4) with 1024; unfold V_w4; lia
      | unfold V_w4; clear - HSF64; lia | reflexivity | exact Zw4 | lia | lia | lia
      | unfold ESTACK; clear - Hmf0 HSF0 HSF1 C1; lia].
  - right. rewrite Z.add_0_r, Hdlin. unfold V_w4, M_n1. clear - Hmf0 HSF0 HSF1 C1. lia.
  - rewrite Usp. left. unfold M_n1. lia.
  - rewrite Usp. right. rewrite Z.add_0_r, Hdlin.
    unfold put_dec.PUT_DEC_STK, ESTACK, V_w4. clear - Hmf0 HSF0 HSF1 C1. lia.
  - unfold put_dec.EV_PUT_DEC. clear - Hnev2 Hnev0 HKev HEV. lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & Hbl3 & HK3 & HD3 & HN3).
rewrite Q1. unfold put_dec.EV_PUT_DEC in HJ3. rewrite Z.add_0_r in HJ3.
(* ---- back at 0x1394: what the call kept ---- *)
assert (P3 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv ->
  getr regs3 r = getr (ms_regs ms) r) by (jc_pres0 HP3).
destruct (jc_keep_call g pos mf ly2 S2 ly2 S2 W2 (ms_mem ms) W3 mem3 (spZ (ms_regs ms))
  put_dec.PUT_DEC_STK _
  (fun a => (mf - put_dec.PUT_DEC_STK <= a < mf) \/ (mf + 208 <= a < mf + 216) \/
            (SFa g pos + V_w4 <= a < SFa g pos + V_w4 + 2))
  HK3 Hfrs EFa eq_refl ltac:(clear - Hmf0 C1; lia)
  ltac:(rewrite Usp; intros a Ha; left; exact Ha)
  ltac:(intros a Ha; cbn beta in Ha; destruct Ha as [Ha | Ha];
        [right; left; unfold M_n1 in Ha; clear - Ha; lia
        | rewrite Z.add_0_r, Hdlin in Ha; right; right; clear - Ha; lia]))
  as [KEEP1 IMG1].
(* the facts the second call needs, at the state after the first *)
assert (V200b : val_mem SEGS (rd W3 mem3) (mf + 200) 8 0).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W3) (ms_mem ms) mem3 (mf + 200) (mf + 200) 8 0); [|exact V200].
  intros kk Hkk. cbn in Hkk. apply KEEP1; [clear - Hkk Hmf0 Hmfb Hsp47 C1; lia | left; lia|].
  unfold put_dec.PUT_DEC_STK, ESTACK, V_w4. clear - Hkk Hmf0 HSF0 HSF1 C1. lia. }
assert (V168b : val_mem SEGS (rd W3 mem3) (mf + 168) 8 (SlotModel.t_out (e_pl g))).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W3) (ms_mem ms) mem3 (mf + 168) (mf + 168) 8 _);
    [|apply (val_mem_moved SEGS (w_H W2) (w_H W2) memT (ms_mem ms) (mf + 168) (mf + 168) 8 _); [|exact V168T]].
  - intros kk Hkk. cbn in Hkk. apply KEEP1; [clear - Hkk Hmf0 Hmfb Hsp47 C1; lia | left; lia|].
    unfold put_dec.PUT_DEC_STK, ESTACK, V_w4. clear - Hkk Hmf0 HSF0 HSF1 C1. lia.
  - intros kk Hkk. cbn in Hkk. apply KEEPA; [clear - Hkk Hmf0 Hmfb Hsp47 C1; lia|].
    clear - Hkk Hmf0 HSF0 HSF1 C1. unfold shadow_addr, SHADOW_OFF.
    assert (SFa g pos / 8 <= SFa g pos) by (apply Z.div_le_upper_bound; lia). lia. }
assert (SH86b : aview SEGS (w_H W3) mem3 (shadow_addr (SFa g pos) + 86) = Some 0).
{ rewrite <- SH86. apply KEEP1.
  - unfold shadow_addr, SHADOW_OFF. clear - HSF0 HSF1 C1 HSH1. lia.
  - right; right; right. clear - HSH1. lia.
  - unfold put_dec.PUT_DEC_STK, ESTACK, shadow_addr, SHADOW_OFF, V_w4.
    pose proof HSFapp as Hap. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap.
    clear - Hmf0 HSF0 HSF1 C1 HSH1 Hap. lia. }
assert (Zw4b : sh_zero W3 mem3 (SFa g pos + V_w4) N_w4).
{ unfold sh_zero, zero_shadow, N_w4. intros i Hi. cbn in Hi.
  replace i with 0 by lia. rewrite Z.add_0_r, Esh688. exact SH86b. }
clear HS HJT.
pose proof HSFapp as HapU. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HapU.
assert (R3K : forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 26; 27]%bv ->
  getr regs3 r = getr regsT r).
{ intros r Hr. rewrite (P3 r ltac:(cbn [In] in Hr |- *; tauto)). exact (HKR r Hr). }
(* ---- run 2: 0x1394 .. the call at 0x13a4 ---- *)
remember (Eimg (Ereg regs3 [w64 (SlotModel.t_out (e_pl g))])) as EB eqn:HEB.
assert (HEIB : img_env VAL A_LIM EB) by (rewrite HEB; apply Eimg_env).
assert (EEB : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EB n = getr regs3 r)
  by (intros n r Hn; rewrite HEB; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ERB : regs_ok EB sr_atoms regs3) by (rewrite HEB; apply regs_ok_Eimg_Ereg).
assert (AGEB : env_agree 32 (Ereg regs3 [w64 (SlotModel.t_out (e_pl g))]) EB)
  by (rewrite HEB; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EB32 : ew EB 32 = w64 (SlotModel.t_out (e_pl g)))
  by (rewrite HEB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
clear HEB.
assert (UB9 : bv_unsigned (ew EB 9) = mf).
{ rewrite (EEB 9%nat 9%bv eq_refl), (R3K 9%bv ltac:(cbn; tauto)), (RKT 9%bv ltac:(cbn; tauto)), Rs1.
  apply unsigned_lit_small. clear - Hmf0 Hmfb Hsp47 C1. lia. }
assert (HS : st_ok_pi SEGS VAL EB ss_jcB
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 0x1394)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_jcB. apply pa_entry_st_ok_full.
  - exact ERB.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold jcB_mf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UB9.
    split; [clear - Hmf0 C1; lia|]. split; [clear - Hmfb Hsp47; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS EB _ mf 168 8 (SOff 32 0) (SlotModel.t_out (e_pl g)));
      [cbn [sv_denot]; rewrite EB32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | clear - Hout40; cbn; lia | cbn; lia | exact V168b].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
paj_run_shc RUNP RUNC HS HJ3.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []] end.
  intros bb wl wh aa Hin Hr. lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; lia | ]).
  destruct Hin. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1b. prreg HS (10%bv : bv 5) Q10b. prreg HS (11%bv : bv 5) Q11b.
prreg HS (12%bv : bv 5) Q12b. prreg HS (13%bv : bv 5) Q13b.
pose proof (regs_kept_of_st_ok SEGS EB _ (restrict (w_H W3) ms0) regs3 [w64 (SlotModel.t_out (e_pl g))]
  [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv HS AGEB ltac:(vm_compute; reflexivity)) as HKR2.
cbn [ms_regs restrict] in HKR2.
assert (Usp2 : spZ (ms_regs ms0) = mf).
{ unfold spZ. rewrite (HKR2 2%bv ltac:(cbn; tauto)), (R3K 2%bv ltac:(cbn; tauto)), (RKT 2%bv ltac:(cbn; tauto)), Rsp.
  unfold w64. apply unsigned_lit_small. clear - Hmf0 Hmfb Hsp47 C1. lia. }
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & Hnev3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF3; reflexivity).
assert (Hfrs3' : frames S3 = [(4, pos)]) by (rewrite Hfrs3; exact Hfrs).
rewrite Hdlin, Z.add_0_l in HN3.
assert (VN2 : val_mem SEGS (rd W3 (ms_mem ms0)) (mf + M_n1) 8 2).
{ apply (val_mem_moved SEGS (w_H W3) (w_H W3) mem3 (ms_mem ms0) (mf + M_n1) (mf + M_n1) 8 2); [|exact HN3].
  intros kk Hkk. apply KEEPB. unfold M_n1. cbn in Hkk. clear - Hkk Hmf0 Hmfb Hsp47 C1. lia. }
assert (Zw4c : zero_shadow (aview SEGS (w_H W3) (ms_mem ms0)) SHADOW_OFF (SFa g pos + V_w4) 8).
{ unfold zero_shadow. intros i Hi. cbn in Hi. replace i with 0 by lia. rewrite Z.add_0_r, Esh688.
  rewrite KEEPB; [exact SH86b|]. unfold shadow_addr, SHADOW_OFF. clear - HSF0 HSF1 C1 HSH1. lia. }
(* ---- 0x13a4: put_dec(w4, &n4, out, 2) ---- *)
pmkst HS. rewrite (PSIG IS_put_dec AF_put_dec eq_refl).
eapply SRr_bind.
{ apply (HPD LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 W3
    (ms_mem ms0) _ (4 * Z.of_nat (m_nrec g) + 7) (ms_regs ms0) (SFa g pos + V_w4) (mf + M_n1) 2
    (SlotModel.t_out (e_pl g)) 2 HJ3).
  - rewrite Q1b. apply ret_ok_codeptr_v; [clear - HBLO; lia | reflexivity].
  - unfold raZ. rewrite Q1b, unsigned_lit_small by (clear - HBLO HBASE; lia). clear - HBLO. lia.
  - rewrite (HKR2 3%bv ltac:(cbn; tauto)), (R3K 3%bv ltac:(cbn; tauto)), (RKT 3%bv ltac:(cbn; tauto)).
    exact Rgp.
  - rewrite (HKR2 4%bv ltac:(cbn; tauto)), (R3K 4%bv ltac:(cbn; tauto)), (RKT 4%bv ltac:(cbn; tauto)).
    exact Rtp.
  - rewrite Q10b, (EEB 18%nat 18%bv eq_refl), (P3 18%bv ltac:(cbn; tauto)), Q18, U12.
    unfold w64, V_w4. f_equal; lia.
  - rewrite Q11b, UB9. unfold w64, M_n1. f_equal; lia.
  - rewrite Q12b, EB32. unfold w64. rewrite unsigned_lit_small by (clear - Hout40; lia).
    apply Z.mod_small. clear - Hout40. lia.
  - left. rewrite Q12b, EB32. unfold w64. rewrite unsigned_lit_small by (clear - Hout40; lia).
    clear - Hout40. lia.
  - rewrite Q13b. reflexivity.
  - lia.
  - rewrite Usp2. exact Hmf32.
  - rewrite Usp2. unfold put_dec.PUT_DEC_STK, ESTACK. clear - Hmfb HSTK'. lia.
  - rewrite Usp2. clear - Hmfb. lia.
  - rewrite Hfrs3'. cbn [length]. lia.
  - unfold M_n1. clear - Hmf32. lia.
  - unfold V_w4. clear - HSF0. lia.
  - lia.
  - exact VN2.
  - rewrite Usp2. apply (jc_twr_stack LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] ly3 S3 W3 (ms_mem ms0) _ (4 * Z.of_nat (m_nrec g) + 7) mf (mf + M_n1) 8 HJ3);
      unfold M_n1; clear - Hmfb HSTK'; lia.
  - rewrite Usp2, Hdlout.
    apply (jc_twr_frame LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) ly3 S3 W3
      (ms_mem ms0) _ (4 * Z.of_nat (m_nrec g) + 7) mf pos (SFa g pos + V_w4 + 2) 2 HJ3);
      [rewrite EFa3; unfold V_w4; lia | rewrite EFa3; unfold V_w4; lia
      | unfold ESTACK; clear - Hmf0 HSF0 HSF1 C1; lia].
  - rewrite Usp2. apply (jc_tsrc_stack LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] ly3 S3 W3 (ms_mem ms0) _ (4 * Z.of_nat (m_nrec g) + 7) mf (mf + M_n1) 8 HJ3);
      unfold M_n1; clear - Hmfb HSTK'; lia.
  - rewrite Usp2, Hdlout.
    apply (jc_tsrc_frame LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
      ly3 S3 W3 (ms_mem ms0) _ (4 * Z.of_nat (m_nrec g) + 7) mf 4 pos (SFa g pos + V_w4) 8
      (SFa g pos + V_w4 + 2) 2 HJ3 ltac:(rewrite Hfrs3'; left; reflexivity));
      [rewrite EFa3; unfold V_w4; lia | rewrite EFa3; change (fs_frame_bytes 4) with 1024; unfold V_w4; lia
      | unfold V_w4; clear - HSF64; lia | reflexivity | exact Zw4c | lia | lia | lia
      | unfold ESTACK; clear - Hmf0 HSF0 HSF1 C1; lia].
  - right. rewrite Hdlout. unfold V_w4, M_n1. clear - Hmf0 HSF0 HSF1 C1. lia.
  - rewrite Usp2. left. unfold M_n1. lia.
  - rewrite Usp2. right. rewrite Hdlout.
    unfold put_dec.PUT_DEC_STK, ESTACK, V_w4. clear - Hmf0 HSF0 HSF1 C1. lia.
  - unfold put_dec.EV_PUT_DEC. clear - Hnev3 Hnev2 Hnev0 HKev HEV. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & Hbl4 & HK4 & HD4 & HN4).
rewrite Q1b. unfold put_dec.EV_PUT_DEC in HJ4. rewrite Z.add_0_r in HJ4.
(* ---- the cut at 0x13a8 ---- *)
assert (P4 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv ->
  getr regs4 r = getr (ms_regs ms0) r) by (jc_pres0 HP4).
destruct (jc_keep_call g pos mf ly2 S2 ly3 S3 W3 (ms_mem ms0) W4 mem4 (spZ (ms_regs ms0))
  put_dec.PUT_DEC_STK _
  (fun a => (mf - put_dec.PUT_DEC_STK <= a < mf) \/ (mf + 208 <= a < mf + 216) \/
            (SFa g pos + V_w4 + 2 <= a < SFa g pos + V_w4 + 4))
  HK4 Hfrs3' EFa3 Hbl3 ltac:(clear - Hmf0 C1; lia)
  ltac:(rewrite Usp2; intros a Ha; left; exact Ha)
  ltac:(intros a Ha; cbn beta in Ha; destruct Ha as [Ha | Ha];
        [right; left; unfold M_n1 in Ha; clear - Ha; lia
        | rewrite Hdlout in Ha; right; right; clear - Ha; lia]))
  as [KEEP2 IMG2].
(* what the whole piece kept, from 0x81a78 on *)
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> jcls g pos mf ly2 S2 a ->
  ~ ((mf - put_dec.PUT_DEC_STK <= a < mf) \/ (mf + 200 <= a < mf + 216) \/
     (SFa g pos + V_w4 <= a < SFa g pos + V_w4 + 4) \/ a = shadow_addr (SFa g pos) + 86) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W2) memT a).
{ intros a Ha Hc Hn.
  rewrite KEEP2 by (first [exact Ha | exact Hc | clear - Hn; lia]).
  rewrite KEEPB by exact Ha.
  rewrite KEEP1 by (first [exact Ha | exact Hc | clear - Hn; lia]).
  apply KEEPA; [exact Ha | clear - Hn; lia]. }
assert (ZWJ : forall a, ((mf - put_dec.PUT_DEC_STK <= a < mf) \/ (mf + 200 <= a < mf + 216) \/
     (SFa g pos + V_w4 <= a < SFa g pos + V_w4 + 4) \/ a = shadow_addr (SFa g pos) + 86) -> WJ g pos mf a).
{ intros a Hz. unfold WJ, put_dec.PUT_DEC_STK, ESTACK, V_w4 in *. clear - Hz Hmf0. lia. }
assert (KTM : jkeep4 g pos mf ly2 S2 W2 memT W4 mem4).
{ intros a Ha HW Hc. apply KALL; [exact Ha | exact Hc | intros Hz; exact (HW (ZWJ a Hz))]. }
assert (KIMG : jcimg W2 memT W4 mem4).
{ apply (jcimg_trans W2 memT W2 (ms_mem ms) W4 mem4).
  - intros a Himg Ho He. pose proof (pa_img_range a Himg) as Hr. apply KEEPA.
    + clear - Hr. lia.
    + unfold shadow_addr, SHADOW_OFF. clear - Hr Hmf0 C1 HSH1. lia.
  - apply (jcimg_trans W2 (ms_mem ms) W3 mem3 W4 mem4 IMG1).
    apply (jcimg_trans W3 mem3 W3 (ms_mem ms0) W4 mem4); [|exact IMG2].
    intros a Himg _ _. pose proof (pa_img_range a Himg) as Hr. apply KEEPB. clear - Hr. lia. }
assert (K34 : forall a, 0 <= a < 2 ^ 64 -> jcls g pos mf ly2 S2 a ->
  ~ ((mf - put_dec.PUT_DEC_STK <= a < mf) \/ (mf + 208 <= a < mf + 216) \/
     (SFa g pos + V_w4 + 2 <= a < SFa g pos + V_w4 + 4)) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hc Hn. rewrite (KEEP2 a Ha Hc Hn). exact (KEEPB a Ha). }
apply SRr_ret.
apply (jcut_mk4 g pos mf nm tk dp (BASE + 0x13a8) (Pj2 g pos mf) ly2 S2 W2 regs2 mem2 md2
  ly4 S4 W4 regs4 mem4 md4 HJ2 Hfrs HKev MLE MOK HC HJC HJ4).
- rewrite Hfrs4. exact Hfrs3'.
- rewrite Hbl4, Hbl3. apply Permutation_refl.
- intros a Ha HW Hc. rewrite (KTM a Ha HW Hc). exact (KEEPT a Ha HW Hc).
- intros r Hr. rewrite (P4 r ltac:(cbn [In] in Hr |- *; tauto)), (HKR2 r ltac:(cbn [In] in Hr |- *; tauto)).
  rewrite (R3K r ltac:(cbn [In] in Hr |- *; tauto)). apply RKT. cbn [In] in Hr |- *; tauto.
- destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as [D3 _].
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as [D1 _].
  intros fd. rewrite D3, D1. reflexivity.
- destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as [_ D4].
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as [_ D2].
  rewrite D4, D2. reflexivity.
- unfold Pj2.
  assert (R4 : forall r : bv 5, In r [18; 23; 24; 26; 27]%bv -> getr regs4 r = getr (ms_regs ms) r).
  { intros r Hr. rewrite (P4 r ltac:(cbn [In] in Hr |- *; tauto)), (HKR2 r ltac:(cbn [In] in Hr |- *; tauto)).
    apply P3. cbn [In] in Hr |- *; tauto. }
  refine (conj Hwok _).
  split; [rewrite (R4 27%bv ltac:(cbn; tauto)), (HKR 27%bv ltac:(cbn; tauto)); exact R27|].
  split; [rewrite (R4 26%bv ltac:(cbn; tauto)), (HKR 26%bv ltac:(cbn; tauto)); exact R26|].
  split; [rewrite (R4 24%bv ltac:(cbn; tauto)), (HKR 24%bv ltac:(cbn; tauto)); exact R24|].
  split; [rewrite (R4 18%bv ltac:(cbn; tauto)), Q18, U12; unfold w64, V_w4; f_equal; lia|].
  split.
  { exists stemA. split.
    - rewrite (R4 23%bv ltac:(cbn; tauto)), Q23, (EEA 14%nat 14%bv eq_refl). exact R14.
    - exact (HST W4 mem4 ly4 S4 md4 _ HJ4 ltac:(rewrite Hfrs4; exact Hfrs3') KTM KIMG). }
  split.
  { unfold bytes_at8, SlotModel.n_W4. rewrite map_app. apply jc_garr8_app.
    - rewrite Z.add_0_r in HD3.
      apply (j_garr8_moved SEGS (w_H W3) (w_H W4) mem3 mem4); [|exact HD3].
      intros j Hj. rewrite length_map, Hlin in Hj. cbn in Hj.
      apply K34; [unfold V_w4; clear - Hj HSF0 HSF1 C1; lia | right; right; left; unfold V_w4; lia |].
      unfold put_dec.PUT_DEC_STK, ESTACK, V_w4. clear - Hj Hmf0 HSF0 HSF1 C1. lia.
    - rewrite length_map, Hlin. exact HD4. }
  split; [rewrite Hdlout in HN4; exact HN4|].
  split.
  { apply (val_mem_moved SEGS (w_H W3) (w_H W4) mem3 mem4 (mf + M_n2) (mf + M_n2) 8 0); [|unfold M_n2; exact V200b].
    intros kk Hkk. cbn in Hkk. unfold M_n2. apply K34; [clear - Hkk Hmf0 Hmfb Hsp47 C1; lia | left; lia |].
    unfold put_dec.PUT_DEC_STK, ESTACK, V_w4. clear - Hkk Hmf0 HSF0 HSF1 C1. lia. }
  split.
  { unfold sh_zero in *. apply (j_zero_shadow_moved (aview SEGS (w_H W2) memT)); [|exact Hzn].
    intros i Hi. unfold N_nm in Hi. cbn in Hi.
    replace (shadow_of_addr SHADOW_OFF (SFa g pos + V_nm) + i) with (shadow_addr (SFa g pos) + (66 + i))
      by (unfold shadow_of_addr, shadow_addr, V_nm; clear - HSF64 Hi; lia).
    apply KALL; [unfold shadow_addr, SHADOW_OFF; clear - Hi HSF0 HSF1 C1 HSH1; lia | right; right; right; lia |].
    unfold put_dec.PUT_DEC_STK, ESTACK, shadow_addr, SHADOW_OFF, V_w4.
    clear - Hi Hmf0 HSF0 HSF1 C1 HSH1 HapU. lia. }
  split.
  { unfold sh_zero in *. apply (j_zero_shadow_moved (aview SEGS (w_H W2) memT)); [|exact Hzd].
    intros i Hi. unfold N_dp in Hi. cbn in Hi.
    replace (shadow_of_addr SHADOW_OFF (SFa g pos + V_dp) + i) with (shadow_addr (SFa g pos) + (74 + i))
      by (unfold shadow_of_addr, shadow_addr, V_dp; clear - HSF64 Hi; lia).
    apply KALL; [unfold shadow_addr, SHADOW_OFF; clear - Hi HSF0 HSF1 C1 HSH1; lia | right; right; right; lia |].
    unfold put_dec.PUT_DEC_STK, ESTACK, shadow_addr, SHADOW_OFF, V_w4.
    clear - Hi Hmf0 HSF0 HSF1 C1 HSH1 HapU. lia. }
  { unfold sh_zero, zero_shadow, N_w4. intros i Hi. cbn in Hi.
    replace i with 0 by lia. rewrite Z.add_0_r, Esh688.
    rewrite K34; [exact SH86b | unfold shadow_addr, SHADOW_OFF; clear - HSF0 HSF1 C1 HSH1; lia
    | right; right; right; lia |].
    unfold put_dec.PUT_DEC_STK, ESTACK, shadow_addr, SHADOW_OFF, V_w4.
    clear - Hmf0 HSF0 HSF1 C1 HSH1 HapU. lia. }
Qed.

(* ---- 0x81a3c .. 0x81a78: the family path ------------------------------------------------------------------ *)
(* the switch table of the entry (object 7), and the shadow byte of the entry it reads *)
Definition jcT_tbl : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 7)) 0 24 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
     YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
Definition jcT_atoms : list (nat * afact) :=
  [(13%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (A_OBJ 7, mkAF IMG_LO IMG_TOP 0)].
Definition ss_jcT : sstate := mkSS 0x1330 sr_atoms [jcT_tbl] None (mkFacts jcT_atoms [] []).
Definition jcR_atoms : list (nat * afact) :=
  [(13%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (A_OBJ 7, mkAF IMG_LO IMG_TOP 0); (25%nat, mkAF 4 127 0)].
Definition ss_jcR : sstate := mkSS 0x1330 sr_atoms [jcT_tbl] None (mkFacts jcR_atoms [] []).
Definition jcT_SH : list shent := [mkSHE (A_OBJ 7) 0 24].
Definition jcT_Bx : sv := SOff 13 0.
Definition jcT_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* A leaf of the family path: the state at 0x136c, whose stem is a string of the image. *)
Lemma jc_fam_leaf : forall g pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regsT memT
    (regsF : bvmap 5 word) memF mdF stemA,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
  jkeep4 g pos mf ly2 S2 W2 mem2 W2 memT ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 26; 27]%bv -> getr regsT r = getr regs2 r) ->
  SlotModel.n_wok (e_pl g) = true ->
  getr regsT 27 = w64 (SlotModel.n_r (e_pl g)) ->
  getr regsT 26 = w64 (SFa g pos + V_nm) -> getr regsT 24 = w64 (SFa g pos + V_dp) ->
  getr regsT 12 = w64 (SFa g pos) ->
  sh_zero W2 memT (SFa g pos + V_nm) N_nm -> sh_zero W2 memT (SFa g pos + V_dp) N_dp ->
  (length (SlotModel.n_stem (e_pl g)) <= 16)%nat ->
  reac_box_name.rbn_imgstr B G W2 memT stemA (map bz (SlotModel.n_stem (e_pl g))) ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 memF mdF (4 * Z.of_nat (m_nrec g) + 7) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) memF a = aview SEGS (w_H W2) memT a) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 12; 19; 20; 21; 22; 24; 26; 27]%bv -> getr regsF r = getr regsT r) ->
  getr regsF 14 = w64 stemA ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x136c) regsF memF mdF)
    (jcut g pos mf nm tk dp (BASE + 0x13a8) (Pj2 g pos mf)).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regsT memT regsF memF mdF stemA
  HJ2 Hfrs HKev MLE MOK HC HJC KEEPT RKT Hwok R27 R26 R24 R12 Hzn Hzd HLs HIMGS HJF KEEPF RKF R14.
pose proof HJC as HJC0.
destruct HJC0 as (Hlay & Hid & Hid3 & Hhb & R20 & R21 & R22 & V184 & V152 & V144 & V160 & V168 & V136 & Hjb).
pose proof HC as HC0.
destruct HC0 as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & _).
assert (IMGF : jcimg W2 memT W2 memF).
{ intros a Himg _ _. pose proof (pa_img_range a Himg) as Hr. apply KEEPF. clear - Hr. lia. }
apply (jc_tail g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regsF memF mdF stemA
  HJ2 Hfrs HKev MLE MOK HC HJC HJF).
- intros a Ha HW Hc. rewrite (KEEPF a Ha). exact (KEEPT a Ha HW Hc).
- intros r Hr. rewrite (RKF r ltac:(cbn [In] in Hr |- *; tauto)). apply RKT. exact Hr.
- destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF) as [D3 _].
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as [D1 _].
  intros fd. rewrite D3, D1. reflexivity.
- destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF) as [_ D4].
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as [_ D2].
  rewrite D4, D2. reflexivity.
- exact Hwok.
- rewrite (RKF 27%bv ltac:(cbn; tauto)). exact R27.
- rewrite (RKF 26%bv ltac:(cbn; tauto)). exact R26.
- rewrite (RKF 24%bv ltac:(cbn; tauto)). exact R24.
- rewrite (RKF 12%bv ltac:(cbn; tauto)). exact R12.
- exact R14.
- unfold sh_zero in *. apply (j_zero_shadow_moved (aview SEGS (w_H W2) memT)); [|exact Hzn].
  intros i Hi. apply KEEPF. unfold shadow_of_addr, SHADOW_OFF, V_nm, N_nm in *.
  pose proof Hlay as (Hmf0' & _ & _ & HSF0 & HSF1 & _). pose proof asan_consts as (C1 & _).
  assert (0 <= (SFa g pos + 528) / 8) by (apply Z.div_pos; lia).
  assert ((SFa g pos + 528) / 8 <= SFa g pos + 528) by (apply Z.div_le_upper_bound; lia).
  clear - Hi HSF0 HSF1 C1 H H0. cbn in Hi. lia.
- unfold sh_zero in *. apply (j_zero_shadow_moved (aview SEGS (w_H W2) memT)); [|exact Hzd].
  intros i Hi. apply KEEPF. unfold shadow_of_addr, SHADOW_OFF, V_dp, N_dp in *.
  pose proof Hlay as (Hmf0' & _ & _ & HSF0 & HSF1 & _). pose proof asan_consts as (C1 & _).
  assert (0 <= (SFa g pos + 592) / 8) by (apply Z.div_pos; lia).
  assert ((SFa g pos + 592) / 8 <= SFa g pos + 592) by (apply Z.div_le_upper_bound; lia).
  clear - Hi HSF0 HSF1 C1 H H0. cbn in Hi. lia.
- intros W3 mem3 ly3 S3 md3 k3 HJ3 Hfr3 KK IMGK.
  apply (jc_stem_imgstr g pos mf nm tk dp ly3 S3 W3 mem3 md3 k3 stemA (SlotModel.n_stem (e_pl g))
    HJ3 Hfr3 Hlay Hmfb eq_refl HLs).
  apply (jc_imgstr_keep W2 memF W3 mem3); [exact IMGK|].
  apply (jc_imgstr_keep W2 memT W2 memF); [exact IMGF | exact HIMGS].
Qed.

Lemma jc_fam : forall g pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regsT memT mdT,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 memT mdT (4 * Z.of_nat (m_nrec g) + 7) ->
  jkeep4 g pos mf ly2 S2 W2 mem2 W2 memT ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 26; 27]%bv -> getr regsT r = getr regs2 r) ->
  (forall fd, fd_lookup (m_fds mdT) fd = fd_lookup (m_fds md2) fd) -> m_fs mdT = m_fs md2 ->
  SlotModel.n_wok (e_pl g) = true -> SlotModel.n_use_said (e_pl g) = false ->
  getr regsT 27 = w64 (SlotModel.n_r (e_pl g)) ->
  getr regsT 26 = w64 (SFa g pos + V_nm) -> getr regsT 24 = w64 (SFa g pos + V_dp) ->
  getr regsT 12 = w64 (SFa g pos) -> getr regsT 13 = w64 SHADOW_OFF ->
  getr regsT 25 = w64 (SlotModel.n_fam (e_pl g)) ->
  sh_zero W2 memT (SFa g pos + V_nm) N_nm -> sh_zero W2 memT (SFa g pos + V_dp) N_dp ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1330) regsT memT mdT)
    (jcut g pos mf nm tk dp (BASE + 0x13a8) (Pj2 g pos mf)).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regsT memT mdT
  HJ2 Hfrs HKev MLE MOK HC HJC HJT KEEPT RKT HfdT HfsT Hwok Hsaid R27 R26 R24 R12 R13 R25 Hzn Hzd.
pose proof HC as HC0.
destruct HC0 as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfss & Hinb).
pose proof HJC as HJC0.
destruct HJC0 as (Hlay & Hid & Hid3 & Hhb & R20 & R21 & R22 & V184 & V152 & V144 & V160 & V168 & V136 & Hjb).
pose proof Hlay as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE. pose proof pa_wx as Hwx.
pose proof pa_segs_low as Hsegs.
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'. unfold ASTACK in Hmf0.
pose proof HJT as (HART & HlyT & _).
pose proof (pa_obj_img 7 ltac:(lia)) as HO7. pose proof (pa_val_range (A_OBJ 7)) as HR7.
pose proof (pa_obj_img 8 ltac:(lia)) as HO8. pose proof (pa_val_range (A_OBJ 8)) as HR8.
(* the image of this state, and its family table *)
assert (HROD : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) memT)).
{ pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _).
  eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJT | apply HRO; exact HROS]. }
destruct (HIMG W2 memT HROD)
  as (_ & _ & _ & _ & _ & Htb8 & (s1 & s2 & s3 & Vs1 & Vs2 & Vs3 & I1 & I2 & I3) & IREAC & _).
(* the model's stem on this path *)
assert (Hst : SlotModel.n_stem (e_pl g) = SlotModel.stem_img (SlotModel.n_fam (e_pl g)))
  by exact (JCModel.stem_img_of (e_pl g) Hsaid).
assert (HLs : (length (SlotModel.n_stem (e_pl g)) <= 16)%nat)
  by (pose proof (SlotModel.n_stem_len (e_pl g)); lia).
pose proof (JCModel.fam_range (e_pl g)) as Hfam.
(* what each leaf must still give jc_tail *)
assert (HRK : forall (regsF : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 12; 19; 20; 21; 22; 24; 26; 27]%bv -> getr regsF r = getr regsT r) ->
  forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 26; 27]%bv -> getr regsF r = getr regs2 r).
{ intros regsF HK r Hr. rewrite (HK r ltac:(cbn [In] in Hr |- *; tauto)). apply RKT. exact Hr. }
(* ---- the symbolic state at 0x1330, and the table's shadow entry ---- *)
remember (Eimg (Ereg regsT [w64 s1; w64 s2; w64 s3])) as ET eqn:HET.
assert (HEIT : img_env VAL A_LIM ET) by (rewrite HET; apply Eimg_env).
assert (ERT : regs_ok ET sr_atoms regsT) by (rewrite HET; apply regs_ok_Eimg_Ereg).
assert (AGET : env_agree 32 (Ereg regsT [w64 s1; w64 s2; w64 s3]) ET)
  by (rewrite HET; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EET : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew ET n = getr regsT r)
  by (intros n r Hn; rewrite HET; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ET32 : ew ET 32 = w64 s1)
  by (rewrite HET; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsT _ 0)).
assert (ET33 : ew ET 33 = w64 s2)
  by (rewrite HET; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsT _ 1)).
assert (ET34 : ew ET 34 = w64 s3)
  by (rewrite HET; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsT _ 2)).
clear HET.
assert (ET13 : ew ET 13 = w64 SHADOW_OFF) by (rewrite (EET 13%nat 13%bv eq_refl); exact R13).
assert (ET25 : ew ET 25 = w64 (SlotModel.n_fam (e_pl g))) by (rewrite (EET 25%nat 25%bv eq_refl); exact R25).
assert (ET7 : ew ET (A_OBJ 7) = Z_to_bv 64 (VAL (A_OBJ 7)))
  by (apply (img_env_atomP ET (A_OBJ 7) HEIT); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (ET8 : ew ET (A_OBJ 8) = Z_to_bv 64 (VAL (A_OBJ 8)))
  by (apply (img_env_atomP ET (A_OBJ 8) HEIT); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U7 : bv_unsigned (ew ET (A_OBJ 7)) = VAL (A_OBJ 7))
  by (rewrite ET7; apply unsigned_lit_small; lia).
(* the three table words are image strings, so each is a small address *)
assert (RT1 : IMG_LO + 64 <= s1 /\ s1 + 64 <= IMG_TOP) by (destruct I1 as (A1 & A2 & _); cbn [length] in A2; lia).
assert (RT2 : IMG_LO + 64 <= s2 /\ s2 + 64 <= IMG_TOP) by (destruct I2 as (A1 & A2 & _); cbn [length] in A2; lia).
assert (RT3 : IMG_LO + 64 <= s3 /\ s3 + 64 <= IMG_TOP) by (destruct I3 as (A1 & A2 & _); cbn [length] in A2; lia).
assert (HROt : Forall (region_ok SEGS ET (mrestrict (w_H W2) memT)) [jcT_tbl]).
{ constructor; [|constructor]. unfold jcT_tbl, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U7.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (chunk_ok_val SEGS ET _ (VAL (A_OBJ 7)) 0 8 (SOff 32 0) s1);
      [cbn [sv_denot]; rewrite ET32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | cbn; clear - RT1; lia | cbn; lia | rewrite Z.add_0_r; exact Vs1].
  - apply (chunk_ok_val SEGS ET _ (VAL (A_OBJ 7)) 8 8 (SOff 33 0) s2);
      [cbn [sv_denot]; rewrite ET33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | cbn; clear - RT2; lia | cbn; lia | exact Vs2].
  - apply (chunk_ok_val SEGS ET _ (VAL (A_OBJ 7)) 16 8 (SOff 34 0) s3);
      [cbn [sv_denot]; rewrite ET34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | cbn; clear - RT3; lia | cbn; lia | exact Vs3]. }
assert (HPDt : pairwise_disjoint ET [jcT_tbl]) by (cbn [pairwise_disjoint all_disjoint]; split; exact I).
assert (SHOK : sh_ok SEGS jcT_Bx jcT_SH ET (mrestrict (w_H W2) memT)).
{ unfold sh_ok, jcT_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W2) memT ET jcT_Bx (A_OBJ 7) (VAL (A_OBJ 7)) 24 (VAL (A_OBJ 7)) 0 24
    (ro_usable_glob SEGS B G ly2 S2 W2 memT mdT (VAL (A_OBJ 7)) 24 (VAL (A_OBJ 7)) 24 GM G_SW
       (proj1 HJT) ltac:(lia) ltac:(lia)));
  [ unfold U, jcT_Bx; cbn [sv_denot]; rewrite ET13, Z.add_0_r;
    unfold w64; rewrite Z_to_bv_bv_unsigned; rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity
  | exact (U_img_atom ET HEIT (A_OBJ 7) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
  | lia | lia
  | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF; clear - Hx HO7; lia ]. }
assert (HS0 : st_ok_pi SEGS VAL ET ss_jcT
  (restrict (w_H W2) (mkst regsT (Z_to_bv 64 (BASE + 0x1330)) memT (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_jcT. apply pa_entry_st_ok_full;
  [exact ERT | vm_compute; reflexivity | exact HROt | exact HPDt |].
  unfold facts_ok, jcT_atoms. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite ET13, ET7. unfold w64.
  rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite (unsigned_lit_small (VAL (A_OBJ 7))) by (clear - HR7; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. clear - HO7. repeat split; lia. }
unfold cfg_at. change (w64 (BASE + 0x1330)) with (Z_to_bv 64 (BASE + 0x1330)).
(* ---- the leaves ---- *)
assert (Hcases : SlotModel.n_fam (e_pl g) = 0 \/ SlotModel.n_fam (e_pl g) = 1 \/
  SlotModel.n_fam (e_pl g) = 2 \/ SlotModel.n_fam (e_pl g) = 3 \/ 4 <= SlotModel.n_fam (e_pl g) <= 127)
  by (clear - Hfam; lia).
destruct Hcases as [Hf | [Hf | [Hf | [Hf | Hf]]]].
- (* fam = 0: fam - 1 wraps, so the stem is "REAC" (0x81a70) *)
  pose proof (st_ok_pi_pin_reg' ET _ _ 25%bv 0 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite R25, Hf; reflexivity) eq_refl) as HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_jcT] in HS. clear HS0.
  paj_run_to_tok RUNTO HS HJT SHOK jcT_Bspan 0x136c;
    [ apply awr_ok_cons_ro; [unfold jcT_tbl; cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil] | ].
  assert (KEEPR : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) memT a).
  { intros a Ha. lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []] end.
    intros bb wl wh aa Hin Hr. lazymatch type of Hin with In _ (windows ?rs) =>
      let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; lia | ]).
    destruct Hin. }
  clear HF HFr HG.
  prreg HS (14%bv : bv 5) Q14.
  pose proof (regs_kept_of_st_ok_pi ET _ _ regsT [w64 s1; w64 s2; w64 s3]
    [2; 3; 4; 8; 9; 12; 19; 20; 21; 22; 24; 26; 27]%bv HS AGET ltac:(vm_compute; reflexivity)) as RKF.
  cbn [ms_regs restrict] in RKF.
  pmkst HS.
  apply (jc_fam_leaf g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regsT memT (ms_regs ms) (ms_mem ms) _
    (VAL (A_OBJ 8)) HJ2 Hfrs HKev MLE MOK HC HJC KEEPT RKT Hwok R27 R26 R24 R12 Hzn Hzd HLs
    ltac:(rewrite Hst, Hf, (JCModel.stem_img_REAC 0 ltac:(lia) ltac:(lia) ltac:(lia)); exact IREAC)
    HJT KEEPR RKF ltac:(rewrite Q14; change 249%nat with (A_OBJ 8); rewrite ET8; reflexivity)).
- (* fam = 1: the stem is the table's first entry *)
  pose proof (st_ok_pi_pin_reg' ET _ _ 25%bv 1 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite R25, Hf; reflexivity) eq_refl) as HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_jcT] in HS. clear HS0.
  paj_run_to_tok RUNTO HS HJT SHOK jcT_Bspan 0x136c;
    [ apply awr_ok_cons_ro; [unfold jcT_tbl; cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil] | ].
  assert (KEEPR : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) memT a).
  { intros a Ha. lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []] end.
    intros bb wl wh aa Hin Hr. lazymatch type of Hin with In _ (windows ?rs) =>
      let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; lia | ]).
    destruct Hin. }
  clear HF HFr HG.
  prreg HS (14%bv : bv 5) Q14.
  pose proof (regs_kept_of_st_ok_pi ET _ _ regsT [w64 s1; w64 s2; w64 s3]
    [2; 3; 4; 8; 9; 12; 19; 20; 21; 22; 24; 26; 27]%bv HS AGET ltac:(vm_compute; reflexivity)) as RKF.
  cbn [ms_regs restrict] in RKF.
  pmkst HS.
  apply (jc_fam_leaf g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regsT memT (ms_regs ms) (ms_mem ms) _
    s1 HJ2 Hfrs HKev MLE MOK HC HJC KEEPT RKT Hwok R27 R26 R24 R12 Hzn Hzd HLs
    ltac:(rewrite Hst, Hf, JCModel.stem_img_STEM; exact I1)
    HJT KEEPR RKF ltac:(rewrite Q14, ET32; reflexivity)).
- (* fam = 2: the table's second entry *)
  pose proof (st_ok_pi_pin_reg' ET _ _ 25%bv 2 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite R25, Hf; reflexivity) eq_refl) as HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_jcT] in HS. clear HS0.
  paj_run_to_tok RUNTO HS HJT SHOK jcT_Bspan 0x136c;
    [ apply awr_ok_cons_ro; [unfold jcT_tbl; cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil] | ].
  assert (KEEPR : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) memT a).
  { intros a Ha. lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []] end.
    intros bb wl wh aa Hin Hr. lazymatch type of Hin with In _ (windows ?rs) =>
      let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; lia | ]).
    destruct Hin. }
  clear HF HFr HG.
  prreg HS (14%bv : bv 5) Q14.
  pose proof (regs_kept_of_st_ok_pi ET _ _ regsT [w64 s1; w64 s2; w64 s3]
    [2; 3; 4; 8; 9; 12; 19; 20; 21; 22; 24; 26; 27]%bv HS AGET ltac:(vm_compute; reflexivity)) as RKF.
  cbn [ms_regs restrict] in RKF.
  pmkst HS.
  apply (jc_fam_leaf g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regsT memT (ms_regs ms) (ms_mem ms) _
    s2 HJ2 Hfrs HKev MLE MOK HC HJC KEEPT RKT Hwok R27 R26 R24 R12 Hzn Hzd HLs
    ltac:(rewrite Hst, Hf, JCModel.stem_img_STEM; exact I2)
    HJT KEEPR RKF ltac:(rewrite Q14, ET33; reflexivity)).
- (* fam = 3: the table's third entry *)
  pose proof (st_ok_pi_pin_reg' ET _ _ 25%bv 3 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite R25, Hf; reflexivity) eq_refl) as HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_jcT] in HS. clear HS0.
  paj_run_to_tok RUNTO HS HJT SHOK jcT_Bspan 0x136c;
    [ apply awr_ok_cons_ro; [unfold jcT_tbl; cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil] | ].
  assert (KEEPR : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) memT a).
  { intros a Ha. lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []] end.
    intros bb wl wh aa Hin Hr. lazymatch type of Hin with In _ (windows ?rs) =>
      let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; lia | ]).
    destruct Hin. }
  clear HF HFr HG.
  prreg HS (14%bv : bv 5) Q14.
  pose proof (regs_kept_of_st_ok_pi ET _ _ regsT [w64 s1; w64 s2; w64 s3]
    [2; 3; 4; 8; 9; 12; 19; 20; 21; 22; 24; 26; 27]%bv HS AGET ltac:(vm_compute; reflexivity)) as RKF.
  cbn [ms_regs restrict] in RKF.
  pmkst HS.
  apply (jc_fam_leaf g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regsT memT (ms_regs ms) (ms_mem ms) _
    s3 HJ2 Hfrs HKev MLE MOK HC HJC KEEPT RKT Hwok R27 R26 R24 R12 Hzn Hzd HLs
    ltac:(rewrite Hst, Hf, JCModel.stem_img_STEM; exact I3)
    HJT KEEPR RKF ltac:(rewrite Q14, ET34; reflexivity)).
- (* 4 <= fam: 2 <u fam - 1, so the stem is "REAC" again *)
  assert (HS : st_ok_pi SEGS VAL ET ss_jcR
    (restrict (w_H W2) (mkst regsT (Z_to_bv 64 (BASE + 0x1330)) memT (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_jcR. apply pa_entry_st_ok_full;
    [exact ERT | vm_compute; reflexivity | exact HROt | exact HPDt |].
    unfold facts_ok, jcR_atoms. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite ET13, ET7, ET25. unfold w64.
    rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (unsigned_lit_small (VAL (A_OBJ 7))) by (clear - HR7; lia).
    rewrite (unsigned_lit_small (SlotModel.n_fam (e_pl g))) by (clear - Hfam; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. clear - HO7 Hf. repeat split; lia. }
  clear HS0.
  paj_run_to_tok RUNTO HS HJT SHOK jcT_Bspan 0x136c;
    [ apply awr_ok_cons_ro; [unfold jcT_tbl; cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil] | ].
  assert (KEEPR : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) memT a).
  { intros a Ha. lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []] end.
    intros bb wl wh aa Hin Hr. lazymatch type of Hin with In _ (windows ?rs) =>
      let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; lia | ]).
    destruct Hin. }
  clear HF HFr HG.
  prreg HS (14%bv : bv 5) Q14.
  pose proof (regs_kept_of_st_ok_pi ET _ _ regsT [w64 s1; w64 s2; w64 s3]
    [2; 3; 4; 8; 9; 12; 19; 20; 21; 22; 24; 26; 27]%bv HS AGET ltac:(vm_compute; reflexivity)) as RKF.
  cbn [ms_regs restrict] in RKF.
  pmkst HS.
  apply (jc_fam_leaf g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regsT memT (ms_regs ms) (ms_mem ms) _
    (VAL (A_OBJ 8)) HJ2 Hfrs HKev MLE MOK HC HJC KEEPT RKT Hwok R27 R26 R24 R12 Hzn Hzd HLs
    ltac:(rewrite Hst, (JCModel.stem_img_REAC (SlotModel.n_fam (e_pl g)) ltac:(clear - Hf; lia)
      ltac:(clear - Hf; lia) ltac:(clear - Hf; lia)); exact IREAC)
    HJT KEEPR RKF ltac:(rewrite Q14; change 249%nat with (A_OBJ 8); rewrite ET8; reflexivity)).
Qed.
(* ---- 0x81a30 .. 0x81a3c: the model name, and the piece ---------------------------------------------------- *)
(* the first byte of id.model_name, which the run reads at 0x81a34 (a4 = &id.model_name) *)
Definition jcS_said : YP09.region :=
  YP09.mkRegion (Some 14%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition ss_jcS : sstate := mkSS 0x1324 sr_atoms [jcS_said] None (mkFacts [] [] []).
Lemma jc_br_val : forall E n z c, ew E n = w64 z -> 0 <= z < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = (z =? c) /\
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = negb (z =? c).
Proof.
intros E n z c Hn Hz Hc. rewrite branch_eq_U, branch_ne_U, (U_atom E n z Hn Hz), U_SLit, zcanon_id
  by (unfold M64; lia). split; reflexivity.
Qed.
Lemma jc_mn0 : forall idb, length idb = 38%nat -> nthb (RcIdentModel.model_name idb) 0 = nthb idb 3.
Proof.
intros idb Hl. unfold RcIdentModel.model_name, RcIdentModel.get, RcIdentModel.OFF_NAME,
  RcIdentModel.NAME_CAP, RcIdentModel.nthb.
rewrite (SlotModel.nth_first (skipn 3 idb) 17 0 (zb 0) ltac:(lia)). apply (jc_nth_skipn idb 3 0).
Qed.

Theorem j_C : j_C_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf nm tk dp W2 c2 Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & HKev & MLE & MOK & HC & HJC & HP).
destruct HP as (Hwok & R27 & R26 & R24 & R12 & R13 & R14 & R23 & R25 & Hzn & Hzd).
pose proof HC as HC0.
destruct HC0 as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & _).
pose proof HJ as HJ0.
pose proof HJC as HJC0.
destruct HJC0 as (Hlay & Hid & Hid3 & Hhb & R20 & R21 & R22 & _).
pose proof Hlay as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
unfold ASTACK in Hmf0.
set (idb := m_id g (m_nrec g)) in *.
assert (Lid : length idb = 38%nat) by (unfold idb, m_id; rewrite SlotModel.rec_id_length; reflexivity).
assert (Hidt : SlotModel.idT (e_pl g) = idb) by reflexivity.
destruct Hid as (Hidb & Hidz & Hidk).
(* the byte at a4 *)
assert (Hb0r : 0 <= bz (nthb idb 3) < 256) by apply jc_bz.
assert (Vb0 : val_mem SEGS (rd W2 mem2) (SFa g pos + V_id + 3) 1 (bz (nthb idb 3))).
{ assert (H3 : (3 < length (map (fun b : byte => bv_unsigned b) idb))%nat)
    by (rewrite length_map, Lid; lia).
  destruct (Hidb 3%nat H3) as [Hv _].
  rewrite jc_nth_map in Hv. replace (SFa g pos + V_id + 3) with (SFa g pos + V_id + Z.of_nat 3) by lia.
  exact Hv. }
(* the environment and the state at 0x1324 *)
remember (Eimg (Ereg regs2 [w64 (bz (nthb idb 3))])) as ES eqn:HES.
assert (HEIS : img_env VAL A_LIM ES) by (rewrite HES; apply Eimg_env).
assert (ERS : regs_ok ES sr_atoms regs2) by (rewrite HES; apply regs_ok_Eimg_Ereg).
assert (AGES : env_agree 32 (Ereg regs2 [w64 (bz (nthb idb 3))]) ES)
  by (rewrite HES; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EES : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew ES n = getr regs2 r)
  by (intros n r Hn; rewrite HES; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES32 : ew ES 32 = w64 (bz (nthb idb 3)))
  by (rewrite HES; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
clear HES.
assert (ES23 : ew ES 23 = w64 (RcIdentModel.has_model_name idb)) by (rewrite (EES 23%nat 23%bv eq_refl); exact R23).
assert (U14 : bv_unsigned (ew ES 14) = SFa g pos + V_id + 3).
{ rewrite (EES 14%nat 14%bv eq_refl), R14. apply unsigned_lit_small. unfold V_id. clear - HSF0 HSF1 C1. lia. }
assert (Hhmn : 0 <= RcIdentModel.has_model_name idb < 256)
  by (unfold RcIdentModel.has_model_name; apply jc_bz).
assert (HS : st_ok_pi SEGS VAL ES ss_jcS
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1324)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_jcS. apply pa_entry_st_ok_full.
  - exact ERS.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold jcS_said, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U14.
    split; [unfold V_id; clear - HSF0; lia|]. split; [unfold V_id; clear - HSF1 C1; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS ES _ (SFa g pos + V_id + 3) 0 1 (SOff 32 0) (bz (nthb idb 3)));
      [cbn [sv_denot]; rewrite ES32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | cbn; clear - Hb0r; lia | cbn; lia | rewrite Z.add_0_r; exact Vb0].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x1324)) with (Z_to_bv 64 (BASE + 0x1324)).
(* what the state after a run of this piece's head gives jc_fam / jc_tail *)
assert (HKEEP0 : forall (m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) mem2 a) ->
  jkeep4 g pos mf ly2 S2 W2 mem2 W2 m')
  by (intros m' HK a Ha _ _; exact (HK a Ha)).
(* 0x1324 beqz s7 *)
psrr_branch_pi RUNP BR HS.
- (* no model name: the family path *)
  assert (Hsaid : SlotModel.n_use_said (e_pl g) = false).
  { apply JCModel.use_said_false_nm. rewrite Hidt.
    destruct (jc_br_val ES 23%nat (RcIdentModel.has_model_name idb) 0 ES23 ltac:(lia) ltac:(lia)) as [Hb _].
    rewrite Hb in Hc. apply Z.eqb_eq in Hc. exact Hc. }
  clear Hc.
  paj_run_to_sh RUNTOP HS HJ 0x1330.
  { apply awr_ok_cons_ro; [unfold jcS_said; cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
  assert (KEEPR : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []] end.
    intros bb wl wh aa Hin Hr. lazymatch type of Hin with In _ (windows ?rs) =>
      let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; lia | ]).
    destruct Hin. }
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi ES _ _ regs2 [w64 (bz (nthb idb 3))]
    [2; 3; 4; 8; 9; 12; 13; 19; 20; 21; 22; 24; 25; 26; 27]%bv HS AGES ltac:(vm_compute; reflexivity)) as RKF.
  cbn [ms_regs restrict] in RKF.
  pmkst HS.
  apply (jc_fam g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _
    HJ0 Hfrs HKev MLE MOK HC HJC HJ ltac:(apply HKEEP0; exact KEEPR)
    ltac:(intros r Hr; apply RKF; cbn [In] in Hr |- *; tauto)
    ltac:(destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [D3 _];
          destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [D1 _];
          intros fd; rewrite D3, D1; reflexivity)
    ltac:(destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [_ D4];
          destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [_ D2];
          rewrite D4, D2; reflexivity)
    Hwok Hsaid
    ltac:(rewrite RKF by (cbn; tauto); exact R27) ltac:(rewrite RKF by (cbn; tauto); exact R26)
    ltac:(rewrite RKF by (cbn; tauto); exact R24) ltac:(rewrite RKF by (cbn; tauto); exact R12)
    ltac:(rewrite RKF by (cbn; tauto); exact R13) ltac:(rewrite RKF by (cbn; tauto); exact R25)
    ltac:(unfold sh_zero in *; apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2));
          [intros i Hi; apply KEEPR; unfold shadow_of_addr, SHADOW_OFF, V_nm, N_nm in *;
           assert (0 <= (SFa g pos + 528) / 8) by (apply Z.div_pos; lia);
           assert ((SFa g pos + 528) / 8 <= SFa g pos + 528) by (apply Z.div_le_upper_bound; lia);
           cbn in Hi; clear - Hi HSF0 HSF1 C1 H H0; lia | exact Hzn])
    ltac:(unfold sh_zero in *; apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2));
          [intros i Hi; apply KEEPR; unfold shadow_of_addr, SHADOW_OFF, V_dp, N_dp in *;
           assert (0 <= (SFa g pos + 592) / 8) by (apply Z.div_pos; lia);
           assert ((SFa g pos + 592) / 8 <= SFa g pos + 592) by (apply Z.div_le_upper_bound; lia);
           cbn in Hi; clear - Hi HSF0 HSF1 C1 H H0; lia | exact Hzd])).
- (* a model name: its first byte decides *)
  assert (Hnm : RcIdentModel.has_model_name idb <> 0).
  { destruct (jc_br_val ES 23%nat (RcIdentModel.has_model_name idb) 0 ES23 ltac:(lia) ltac:(lia)) as [Hb _].
    rewrite Hb in Hc. apply Z.eqb_neq in Hc. exact Hc. }
  clear Hc.
  paj_run_to_sh RUNTOP HS HJ 0x132c.
  { apply awr_ok_cons_ro; [unfold jcS_said; cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []] end.
    intros bb wl wh aa Hin Hr. lazymatch type of Hin with In _ (windows ?rs) =>
      let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; lia | ]).
    destruct Hin. }
  clear HF HFr HG.
  prreg HS (10%bv : bv 5) Q10.
  pose proof (regs_kept_of_st_ok_pi ES _ _ regs2 [w64 (bz (nthb idb 3))]
    [2; 3; 4; 8; 9; 12; 13; 14; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS AGES
    ltac:(vm_compute; reflexivity)) as RK1.
  cbn [ms_regs restrict] in RK1.
  assert (EQ10 : getr (ms_regs ms) 10 = w64 (bz (nthb idb 3)))
    by (rewrite Q10, ES32; apply jc_zext8).
  (* 0x132c bnez a0 *)
  psrr_branch_pi RUNP BR HS.
  + (* the model name is the stem *)
    assert (Hsaid : SlotModel.n_use_said (e_pl g) = true).
    { apply JCModel.use_said_true; rewrite Hidt.
      - exact Hnm.
      - rewrite (jc_mn0 idb Lid).
        jc_breg HS (10%bv : bv 5) Hd10. rewrite EQ10 in Hd10.
        lazymatch type of Hc with branch_taken BC_NE (sv_denot ?Ev ?A) _ = _ =>
          assert (HUA : U Ev A = bz (nthb idb 3))
            by (unfold U; rewrite <- Hd10; unfold w64; apply unsigned_lit_small; clear - Hb0r; lia) end.
        rewrite branch_ne_U, jU_lit, HUA in Hc. change (0 mod M64) with 0 in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
    clear Hc.
    paj_run_to_sh RUNTOP HS HJ 0x136c.
    { apply awr_ok_cons_ro; [unfold jcS_said; cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
      aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
    { intros a Ha. rewrite <- (KEEP1 a Ha).
      lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
        apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []] end.
      intros bb wl wh aa Hin Hr. lazymatch type of Hin with In _ (windows ?rs) =>
        let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; lia | ]).
      destruct Hin. }
    clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi ES _ _ regs2 [w64 (bz (nthb idb 3))]
      [2; 3; 4; 8; 9; 12; 13; 14; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS AGES
      ltac:(vm_compute; reflexivity)) as RK2.
    cbn [ms_regs restrict] in RK2.
    pmkst HS.
    apply (jc_tail g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs ms0) (ms_mem ms0) _
      (SFa g pos + V_id + 3) HJ0 Hfrs HKev MLE MOK HC HJC HJ ltac:(apply HKEEP0; exact KEEP2)
      ltac:(intros r Hr; apply RK2; cbn [In] in Hr |- *; tauto)
      ltac:(destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [D3 _];
            destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [D1 _];
            intros fd; rewrite D3, D1; reflexivity)
      ltac:(destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [_ D4];
            destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [_ D2];
            rewrite D4, D2; reflexivity)
      Hwok
      ltac:(rewrite RK2 by (cbn; tauto); exact R27) ltac:(rewrite RK2 by (cbn; tauto); exact R26)
      ltac:(rewrite RK2 by (cbn; tauto); exact R24) ltac:(rewrite RK2 by (cbn; tauto); exact R12)
      ltac:(rewrite RK2 by (cbn; tauto); exact R14)
      ltac:(unfold sh_zero in *; apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2));
            [intros i Hi; apply KEEP2; unfold shadow_of_addr, SHADOW_OFF, V_nm, N_nm in *;
             assert (0 <= (SFa g pos + 528) / 8) by (apply Z.div_pos; lia);
             assert ((SFa g pos + 528) / 8 <= SFa g pos + 528) by (apply Z.div_le_upper_bound; lia);
             cbn in Hi; clear - Hi HSF0 HSF1 C1 H H0; lia | exact Hzn])
      ltac:(unfold sh_zero in *; apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2));
            [intros i Hi; apply KEEP2; unfold shadow_of_addr, SHADOW_OFF, V_dp, N_dp in *;
             assert (0 <= (SFa g pos + 592) / 8) by (apply Z.div_pos; lia);
             assert ((SFa g pos + 592) / 8 <= SFa g pos + 592) by (apply Z.div_le_upper_bound; lia);
             cbn in Hi; clear - Hi HSF0 HSF1 C1 H H0; lia | exact Hzd])).
    intros W3 mem3 ly3 S3 md3 k3 HJ3 Hfr3 KK IMGK.
    apply (jc_stem_said g pos mf nm tk dp ly3 S3 W3 mem3 md3 k3 HJ3 Hfr3 Hlay Hmfb); [|exact Hsaid].
    apply (jc_id_keep g pos mf nm tk dp ly2 S2 W2 mem2 W3 mem3 (m_nrec g));
      [ intros a Ha HW Hcl; rewrite (KK a Ha HW Hcl); exact (KEEP2 a Ha)
      | exact Hlay | exact Hmfb
      | exact (conj Hidb (conj Hidz Hidk)) ].
  + (* the model name starts with a NUL: the family path *)
    assert (Hsaid : SlotModel.n_use_said (e_pl g) = false).
    { apply JCModel.use_said_false_b0. rewrite Hidt, (jc_mn0 idb Lid).
      jc_breg HS (10%bv : bv 5) Hd10. rewrite EQ10 in Hd10.
      lazymatch type of Hc with branch_taken BC_NE (sv_denot ?Ev ?A) _ = _ =>
        assert (HUA : U Ev A = bz (nthb idb 3))
          by (unfold U; rewrite <- Hd10; unfold w64; apply unsigned_lit_small; clear - Hb0r; lia) end.
      rewrite branch_ne_U, jU_lit, HUA in Hc. change (0 mod M64) with 0 in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
    clear Hc.
    paj_run_to_sh RUNTOP HS HJ 0x1330.
    { apply awr_ok_cons_ro; [unfold jcS_said; cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
      aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
    { intros a Ha. rewrite <- (KEEP1 a Ha).
      lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
        apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr); [|exact Ha | intros []] end.
      intros bb wl wh aa Hin Hr. lazymatch type of Hin with In _ (windows ?rs) =>
        let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hr; lia | ]).
      destruct Hin. }
    clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi ES _ _ regs2 [w64 (bz (nthb idb 3))]
      [2; 3; 4; 8; 9; 12; 13; 19; 20; 21; 22; 24; 25; 26; 27]%bv HS AGES
      ltac:(vm_compute; reflexivity)) as RK2.
    cbn [ms_regs restrict] in RK2.
    pmkst HS.
    apply (jc_fam g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs ms0) (ms_mem ms0) _
      HJ0 Hfrs HKev MLE MOK HC HJC HJ ltac:(apply HKEEP0; exact KEEP2)
      ltac:(intros r Hr; apply RK2; cbn [In] in Hr |- *; tauto)
      ltac:(destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [D3 _];
            destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [D1 _];
            intros fd; rewrite D3, D1; reflexivity)
      ltac:(destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [_ D4];
            destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as [_ D2];
            rewrite D4, D2; reflexivity)
      Hwok Hsaid
      ltac:(rewrite RK2 by (cbn; tauto); exact R27) ltac:(rewrite RK2 by (cbn; tauto); exact R26)
      ltac:(rewrite RK2 by (cbn; tauto); exact R24) ltac:(rewrite RK2 by (cbn; tauto); exact R12)
      ltac:(rewrite RK2 by (cbn; tauto); exact R13) ltac:(rewrite RK2 by (cbn; tauto); exact R25)
      ltac:(unfold sh_zero in *; apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2));
            [intros i Hi; apply KEEP2; unfold shadow_of_addr, SHADOW_OFF, V_nm, N_nm in *;
             assert (0 <= (SFa g pos + 528) / 8) by (apply Z.div_pos; lia);
             assert ((SFa g pos + 528) / 8 <= SFa g pos + 528) by (apply Z.div_le_upper_bound; lia);
             cbn in Hi; clear - Hi HSF0 HSF1 C1 H H0; lia | exact Hzn])
      ltac:(unfold sh_zero in *; apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2));
            [intros i Hi; apply KEEP2; unfold shadow_of_addr, SHADOW_OFF, V_dp, N_dp in *;
             assert (0 <= (SFa g pos + 592) / 8) by (apply Z.div_pos; lia);
             assert ((SFa g pos + 592) / 8 <= SFa g pos + 592) by (apply Z.div_le_upper_bound; lia);
             cbn in Hi; clear - Hi HSF0 HSF1 C1 H H0; lia | exact Hzd])).
Qed.

Check j_C : j_C_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS.

End c.
End b.
End a.
