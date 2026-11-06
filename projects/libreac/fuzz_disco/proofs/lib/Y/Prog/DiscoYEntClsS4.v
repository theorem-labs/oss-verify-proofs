(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 419 of its 458 lines of code are new or changed and 1239 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntProC.v, with its module paths and module names changed; 636 of its 687 lines of code are new or changed and 407 lines of the source are left out. *)
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
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC81 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt ClassifyCore DiscoYEntClsCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition s4_acs : list YP09.chunk := [YP09.mkChunk 376 (CVal 8 (SOff 563 0))].
Definition s4_cs : list YP09.chunk := [YP09.mkChunk 384 (CVal 8 (SOff AT_F 2624)); YP09.mkChunk 376 (CVal 8 (SOff 563 0))].
Definition s4_rs : smem := [YP09.mkRegion (Some AT_A) 0 472 0 0 s4_cs].
Definition s4_ss (pc : Z) : sstate := mkSS pc cl_sr s4_rs None (d_facts [] []).
Definition s4_kl : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition s4_rl : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv.

Lemma s4_sub : submem s4_rs (d_kregions dsh_rec s4_acs [] ++ []).
Proof.
unfold s4_rs, d_kregions. cbn [app].
apply submem_drop. apply submem_keep; [|apply submem_nil].
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
intros c Hc. unfold s4_cs in Hc. apply in_or_app.
destruct Hc as [<- | [<- | []]]; [left | right; left; reflexivity].
clear. cbv [dslot_chunks map fst snd In]. tauto.
Qed.

Lemma s4_vals_lo : forall (regs : bvmap 5 word) xs (j : nat), (j < 32)%nat ->
  nth j (cl_vals regs xs) (Z_to_bv 64 0) = getr regs (Z_to_bv 5 (Z.of_nat j)).
Proof.
intros regs xs j Hj. unfold cl_vals. rewrite app_nth1 by (rewrite length_map, length_seq; exact Hj).
set (f := fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))).
transitivity (nth j (map f (seq 0 32)) (f 0%nat)); [apply nth_indep; rewrite length_map, length_seq; exact Hj|].
rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma s4_vals_hi : forall (regs : bvmap 5 word) xs (j : nat),
  nth (32 + j) (cl_vals regs xs) (Z_to_bv 64 0) = nth j xs (Z_to_bv 64 0).
Proof.
intros regs xs j. unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. f_equal. lia.
Qed.

Lemma s4_nth_skipn : forall {A : Type} (l : list A) m n d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
intros A l. induction l as [|x l IH]; intros m n d; destruct m; cbn; try reflexivity; try (destruct n; reflexivity).
apply IH.
Qed.

Lemma s4_nth_fld : forall (G : list byte) a q, (q < 6)%nat -> (a + 6 <= length G)%nat ->
  nth q (map bv_unsigned (firstn 6 (skipn a G))) 0 = bv_unsigned (nth (a + q) G (Z_to_bv 8 0)).
Proof.
intros G a q Hq Ha.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, length_firstn, length_skipn; lia).
rewrite map_nth. f_equal. rewrite nth_firstn.
replace (q <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hq).
apply s4_nth_skipn.
Qed.

Lemma s4_add_den : forall E n m a b c, ew E n = Z_to_bv 64 a -> ew E m = Z_to_bv 64 b ->
  0 <= a -> 0 <= b -> 0 <= c -> a + c + b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n c) (SOff m 0)) = Z_to_bv 64 (a + c + b).
Proof.
intros E n m a b c Ha Hb Ra Rb Rc Rs. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, (U_atom_off E n a c Ha), (U_atom E m b Hb) by lia.
cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.

Lemma s4_sll_den : forall E n m a b, ew E n = Z_to_bv 64 a -> ew E m = Z_to_bv 64 b ->
  0 <= a -> 0 <= b < 2 ^ 58 -> a + 2624 + 32 * b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 2624) (SAlu ALU_SLL (SOff m 0) (SLit 5))) = Z_to_bv 64 (a + 2624 + 32 * b).
Proof.
intros E n m a b Ha Hb Ra Rb Rs. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, (U_atom_off E n a 2624 Ha), U_SAlu, (U_atom E m b Hb), U_lit by lia.
cbn [zalu_raw]. change (Z.land 5 63) with 5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
rewrite (zcanon_id (b * 32)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma s4_off_den : forall E n a c, ew E n = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (a + c).
Proof. intros E n a c Ha Ra. cbn [sv_denot]. rewrite Ha, unsigned_lit_small by lia. reflexivity. Qed.

Ltac s4_srk :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; clear - Hr; cbv [In s4_rl s4_kl] in Hr;
  repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]); destruct Hr.

Ltac s4_rgk HS :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) => rewrite (st_ok_pi_restrict_reg H E ss ms r HS)
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) => rewrite (st_ok_restrict_reg segs H E ss ms r HS)
  end;
  f_equal; clear - Hr; cbv [In s4_rl s4_kl] in Hr;
  repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]); destruct Hr.

Ltac s4_rg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma s4_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
intros cx E vals j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.

Lemma s4_ewr : forall cx E (regs : bvmap 5 word) xs q (n : nat) (r : bv 5), q = (AT_X + n)%nat ->
  Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew (d_env cx E (cl_vals regs xs)) q = getr regs r.
Proof.
intros cx E regs xs q n r -> Hr Hn. rewrite s4_env_x by (unfold cl_vals; rewrite length_app, length_map, length_seq; lia).
rewrite s4_vals_lo by exact Hn. rewrite Hr, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma s4_ewx : forall cx E (regs : bvmap 5 word) xs q (j : nat), q = (AT_X + 32 + j)%nat -> (j < length xs)%nat ->
  ew (d_env cx E (cl_vals regs xs)) q = nth j xs (Z_to_bv 64 0).
Proof.
intros cx E regs xs q j -> Hj. replace (AT_X + 32 + j)%nat with (AT_X + (32 + j))%nat by lia.
rewrite s4_env_x by (unfold cl_vals; rewrite length_app, length_map, length_seq; lia).
apply s4_vals_hi.
Qed.

Lemma s4_ewo : forall cx E vals n, (n < AT_FL)%nat -> ew (d_env cx E vals) n = ew E n.
Proof. intros cx E vals n Hn. unfold d_env. apply ew_havoc_old. exact Hn. Qed.

Lemma s4_img : forall cx E vals, d_E cx E -> img_env VAL A_LIM (d_env cx E vals).
Proof.
intros cx E vals (_ & _ & HEI & _). unfold d_env. apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL; lia].
Qed.

Lemma s4_aview_ext : forall (H : word -> bool) (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' HM a. apply aview_eq_of. unfold mrestrict. rewrite HM. reflexivity. Qed.

Lemma s4_pres_ext : forall (H : word -> bool) (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, apresent H m a -> apresent H m' a.
Proof. intros H m m' HM a (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite HM. exact Hb. Qed.

Lemma s4_aview_G : forall (H : word -> bool) m p (G : list byte) q,
  garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) G) -> 0 <= q < Z.of_nat (length G) ->
  aview SEGS H m (p + q) = Some (bv_unsigned (nth (Z.to_nat q) G (Z_to_bv 8 0))).
Proof.
intros H m p G q HG Hq. unfold aview.
replace (p + q) with (p + Z.of_nat (Z.to_nat q)) by lia.
rewrite (garr8_mbyte SEGS _ p _ (Z.to_nat q) HG) by (rewrite length_map; lia).
set (f := fun b : byte => bv_unsigned b).
rewrite (nth_indep (map f G) 0 (f (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. unfold f. cbn [option_map]. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma s4_gate_ne : forall (H : word -> bool) m p (G : list byte) k j,
  garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) G) -> gate_ok G ->
  0 <= k -> k < j -> j < gn G ->
  (forall q, 0 <= q < 6 -> aview SEGS H m (p + 32 * k + q) = aview SEGS H m (p + 32 * j + q)) -> False.
Proof.
intros H m p G k j HG (LG & Hgn & Hne) Hk Hkj Hj HE.
specialize (Hne (Z.to_nat k) (Z.to_nat j) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; exact Hj)).
unfold CtrlParsed.bytes_eqb in Hne.
destruct (list_eq_dec Z.eq_dec _ _) as [_ | Hn]; [discriminate | apply Hn].
unfold gmac, CtrlParsed.fld.
apply (nth_ext _ _ 0 0); [rewrite !length_map, !length_firstn, !length_skipn; lia|].
intros q Hq. rewrite length_map, length_firstn, length_skipn in Hq.
rewrite !s4_nth_fld by lia.
pose proof (HE (Z.of_nat q) ltac:(lia)) as Q.
rewrite <- !Z.add_assoc in Q.
rewrite !(s4_aview_G H m p G) in Q by (first [exact HG | lia]).
injection Q as Q.
replace (32 * Z.to_nat k + q)%nat with (Z.to_nat (32 * k + Z.of_nat q)) by lia.
replace (32 * Z.to_nat j + q)%nat with (Z.to_nat (32 * j + Z.of_nat q)) by lia.
exact Q.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = FF_canary.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
#[local] Notation DCTX := (d_ctx B MT XM_LIB RLO RHI tfib_K).

Lemma s4_rL_eq : forall cx (regs rg : bvmap 5 word), d_rL B cx regs ->
  (forall r : bv 5, In r s4_rl -> getr rg r = getr regs r) -> d_rL B cx rg.
Proof.
intros cx regs rg HL K.
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
unfold d_rL, spZ in *. rewrite !K by (clear; cbv; tauto). repeat split; assumption.
Qed.

Lemma s4_rL_pres : forall cx (r3 r2 : bvmap 5 word), aregs_preserved r3 r2 -> d_rL B cx r3 -> d_rL B cx r2.
Proof.
intros cx r3 r2 HP (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
assert (E2 : getr r2 2 = getr r3 2) by exact (cl_cs r3 r2 2 _ HP ltac:(unfold acallee_saved; lia) eq_refl).
unfold d_rL, spZ in *. rewrite E2.
split; [exact Hsp|].
split; [exact (cl_cs r3 r2 3 _ HP ltac:(unfold acallee_saved; lia) Hgp)|].
split; [exact (cl_cs r3 r2 4 _ HP ltac:(unfold acallee_saved; lia) Htp)|].
split; [exact (cl_cs r3 r2 8 _ HP ltac:(unfold acallee_saved; lia) H8)|].
split; [exact (cl_cs r3 r2 9 _ HP ltac:(unfold acallee_saved; lia) H9)|].
split; [exact (cl_cs r3 r2 19 _ HP ltac:(unfold acallee_saved; lia) H19)|].
split; [exact (cl_cs r3 r2 18 _ HP ltac:(unfold acallee_saved; lia) H18)|].
split; [exact (cl_cs r3 r2 20 _ HP ltac:(unfold acallee_saved; lia) H20)|].
exact (cl_cs r3 r2 27 _ HP ltac:(unfold acallee_saved; lia) H27).
Qed.

Lemma s4_jregs_eq : forall cx nn k j (regs rg : bvmap 5 word), cl_jregs cx nn k j regs ->
  (forall r : bv 5, In r s4_kl -> getr rg r = getr regs r) -> cl_jregs cx nn k j rg.
Proof.
intros cx nn k j regs rg (Hk & Hj & R21 & R24 & R22 & R26 & R25 & R23) K.
unfold cl_jregs. rewrite !K by (clear; cbv; tauto).
exact (conj Hk (conj Hj (conj R21 (conj R24 (conj R22 (conj R26 (conj R25 R23))))))).
Qed.

Lemma s4_jregs_pres : forall cx nn k j (r3 r2 : bvmap 5 word), aregs_preserved r3 r2 ->
  cl_jregs cx nn k j r3 -> cl_jregs cx nn k j r2.
Proof.
intros cx nn k j r3 r2 HP (Hk & Hj & R21 & R24 & R22 & R26 & R25 & R23).
split; [exact Hk|]. split; [exact Hj|].
split; [exact (cl_cs r3 r2 21 _ HP ltac:(unfold acallee_saved; lia) R21)|].
split; [exact (cl_cs r3 r2 24 _ HP ltac:(unfold acallee_saved; lia) R24)|].
split; [exact (cl_cs r3 r2 22 _ HP ltac:(unfold acallee_saved; lia) R22)|].
split; [exact (cl_cs r3 r2 26 _ HP ltac:(unfold acallee_saved; lia) R26)|].
split; [exact (cl_cs r3 r2 25 _ HP ltac:(unfold acallee_saved; lia) R25)|].
exact (cl_cs r3 r2 23 _ HP ltac:(unfold acallee_saved; lia) R23).
Qed.

Lemma s4_keep_regs : forall cx E xs (regs rg : bvmap 5 word) (l : list (bv 5)), d_E cx E -> d_rL B cx regs ->
  0 <= d_A cx < 2 ^ 64 ->
  (forall r : bv 5, In r l -> getr rg r = sv_denot (d_env cx E (cl_vals regs xs)) (sr_get cl_sr r)) ->
  forall r : bv 5, In r l -> getr rg r = getr regs r.
Proof.
intros cx E xs regs rg l HE HL HA RG r Hr. rewrite (RG r Hr), (cl_regs_ok B cx E regs xs HE HL HA r). reflexivity.
Qed.

Lemma s4_seat : forall (fq : YK11.FPState) cx h ly3 S3 (W : world SEGS) (regs : bvmap 5 word) mem3 md3 kk pc,
  DCTX cx ly3 S3 W mem3 md3 kk -> d_frame cx h dsh_rec W mem3 -> d_rL B cx regs ->
  exists E, d_E cx E /\
    st_ok_pi (fx := fq) SEGS VAL (d_env cx E (cl_vals regs [w64 (dnot (d_obj cx OG))])) (s4_ss pc)
      (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx h ly3 S3 W regs mem3 md3 kk pc HC (E & HE & HRG & HFL & V184 & V120 & V136 & V376 & V280 & V232 & V264) HrL.
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 kk HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
set (vals := cl_vals regs [w64 (dnot (d_obj cx OG))]).
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) s4_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS (d_env cx E vals) (rd W mem3) (d_A cx) 376 8 (SOff 563 0) (dnot (d_obj cx OG))).
  - rewrite sv_denot_SOff0. unfold vals. rewrite (s4_ewx cx E regs [w64 (dnot (d_obj cx OG))] 563 0 eq_refl ltac:(cbn; lia)). reflexivity.
  - unfold dnot, d_obj. cbn [dobj_off]. change (8 * Z.of_N 8) with 64. lia.
  - lia.
  - exact V376. }
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 kk E pc cl_sr vals s4_acs [] [] (d_facts [] [])
  HC HE HRG HFL (cl_regs_ok B cx E regs _ HE HrL HAr2) (FACTS LAWS cx ly3 S3 W mem3 md3 kk E vals [] [] HC HE I I)
  HACS (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
exists E. split; [exact HE|].
exact (st_ok_pi_submem _ _ _ s4_rs HS0 s4_sub ltac:(vm_compute; reflexivity)).
Qed.

Lemma s4_kept : forall cx ly3 S3 (W : world SEGS) m3 md3 k3 m4 lo hi,
  DCTX cx ly3 S3 W m3 md3 k3 -> d_S cx - LLVMF_STK <= lo -> hi <= d_S cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m4 a = aview SEGS (w_H W) m3 a) ->
  (forall a, apresent (w_H W) m3 a -> apresent (w_H W) m4 a) ->
  cl_kept B ly3 S3 W m3 W m4 lo hi (fun _ => False).
Proof.
intros cx ly3 S3 W m3 md3 k3 m4 lo hi HC Hlo Hhi KV KP.
pose proof HC as (_ & _ & Hfrs).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m3 md3 k3 HC)
  as (Hal16 & Hslo & Hshi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold cl_kept. split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hn _. apply KV; [lia | exact Hn].
- intros b m i Hin Hi _. destruct (al_blocks SEGS B LAWS ly3 S3 W m3 md3 b m HAR Hin) as (_ & Hb0 & Hbc & _).
  apply KV; unfold LLVMF_STK in *; lia.
- intros a Ha _ _. pose proof (pa_segs_low a Ha) as Hl. apply KV; unfold LLVMF_STK in *; lia.
- intros cid pos a Hin Ha _. rewrite Hfrs in Hin. destruct Hin as [Hq | []]. injection Hq as <- <-.
  unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. rewrite Efa, cl_fs6 in Ha.
  unfold shadow_addr, SHADOW_OFF in Ha. change (4096 / 8) with 512 in Ha.
  apply KV; unfold LLVMF_STK in *; lia.
- intros a _ _ Hp. exact (KP a Hp).
- intros a Ha. apply KP. apply HWpres. lia.
Qed.

Lemma s4_lmem_keep : forall cx h i n now op nb fr len nn (regs rg : bvmap 5 word) ly3 S3 (W : world SEGS) m3 md3 k3
  m4 md4 k4 lo hi,
  cl_lmem B cx h i n now op nb fr len nn regs ly3 S3 W m3 ->
  DCTX cx ly3 S3 W m3 md3 k3 -> DCTX cx ly3 S3 W m4 md4 k4 ->
  d_S cx - LLVMF_STK <= lo -> hi <= d_A cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m4 a = aview SEGS (w_H W) m3 a) ->
  (forall a, apresent (w_H W) m3 a -> apresent (w_H W) m4 a) ->
  d_rL B cx rg ->
  cl_lmem B cx h i n now op nb fr len nn rg ly3 S3 W m4.
Proof.
intros cx h i n now op nb fr len nn regs rg ly3 S3 W m3 md3 k3 m4 md4 k4 lo hi HL HC3 HC4 Hlo Hhi KV KP HrL.
destruct HL as (Sg & G & push & HB & HSg & HG & HnnG & Hspl).
pose proof HB as (Hi & Hn & Hnow & Hop & Hop2 & _ & Hsp0 & Hfrm & HREC & HOP & Hlen & Hnb & Hnbn & Hbody).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m3 md3 k3 HC3) as (Hal16 & Hslo & Hshi & HF0 & HFc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HK : cl_kept B ly3 S3 W m3 W m4 lo hi (fun _ => False))
  by exact (s4_kept cx ly3 S3 W m3 md3 k3 m4 lo hi HC3 Hlo ltac:(unfold MFRAME in HA1; lia) KV KP).
assert (VA : forall o v, 0 <= o -> o + 8 <= 472 -> val_mem SEGS (rd W m3) (d_A cx + o) 8 v ->
  val_mem SEGS (rd W m4) (d_A cx + o) 8 v)
  by (intros o v Ho1 Ho2 Hv; exact (cl_slot_keep B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m3 md3 k3 W m4 lo hi
    (fun _ => False) o v HC3 HK Hhi (fun a Hf => False_ind _ Hf) Ho1 Ho2 Hv)).
assert (VF : forall p L, d_FB cx <= p -> p + Z.of_nat (length L) <= d_FB cx + 4096 ->
  garr8 SEGS (rd W m3) p L -> garr8 SEGS (rd W m4) p L).
{ intros p L H1 H2 Hg. eapply YC88.garr8_aview_kept; [|exact Hg]. intros a Ha. apply KV; unfold LLVMF_STK in *; lia. }
exists Sg, G, push. split; [|split; [|split; [|split]]].
- unfold cl_base.
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact Hop|]. split; [exact Hop2|].
  split; [exact HrL|].
  split; [destruct Hsp0 as (S1 & S2); split; apply VA; first [lia | assumption]|].
  split; [exact (cl_frm_keep B MT XM_LIB RLO RHI tfib_K LAWS cx nb fr len ly3 S3 W m3 md3 k3 W m4 lo hi
    (fun _ => False) h n dsh_rec HC3 Hbody HK (fun a Hf => False_ind _ Hf) Hfrm)|].
  split; [destruct HREC as (R1 & R2 & R3 & R4); split; [|split; [|split]]; apply VA; first [lia | assumption]|].
  split; [destruct HOP as (O1 & O2); split; apply VA; first [lia | assumption]|].
  split; [exact Hlen|]. split; [exact Hnb|]. split; [exact Hnbn|].
  exact (cl_body_call B MT XM_LIB RLO RHI tfib_K LAWS AIL KCAN cx h n (dxb fr len) dsh_rec ly3 S3 W m3 md3 k3
    ly3 S3 W m4 md4 k4 lo hi (fun _ => False) [] Hbody HC3 HC4 HK Hlo Hhi (fun a Hf => False_ind _ Hf)
    (fun a Hf _ => False_ind _ Hf) (Forall_nil _) (Permutation_refl _) BTOBS).
- destruct HSg as (LSg & GSg & HSf). split; [exact LSg|]. split; [|exact HSf].
  apply VF; [unfold d_obj; cbn [dobj_off]; lia | rewrite length_map, LSg; unfold d_obj; cbn [dobj_off]; lia | exact GSg].
- destruct HG as (LG & GG & HGok). split; [exact LG|]. split; [|exact HGok].
  apply VF; [unfold d_obj; cbn [dobj_off]; lia | rewrite length_map, LG; unfold d_obj; cbn [dobj_off]; lia | exact GG].
- exact HnnG.
- destruct Hspl as (V296 & Hp). split; [apply VA; [lia | lia | exact V296] | exact Hp].
Qed.

Lemma s4_x_of : forall cx h i n now op nb fr len nn (regs : bvmap 5 word) ly3 S3 (W : world SEGS) m,
  cl_lmem B cx h i n now op nb fr len nn regs ly3 S3 W m ->
  exists Sg push, cl_base B cx h i n now op nb fr len regs ly3 S3 W m /\ cl_sg cx nb len Sg W m /\ cl_spl cx push W m.
Proof.
intros cx h i n now op nb fr len nn regs ly3 S3 W m (Sg & G & push & HB & HSg & _ & _ & Hspl).
exists Sg, push. exact (conj HB (conj HSg Hspl)).
Qed.

Lemma s4_land : forall (fq : YK11.FPState) cx h i n now op nb fr len nn (regs : bvmap 5 word) ly3 S3 (W : world SEGS)
  mem3 md3 kk E xs (ss : sstate) (ms : machine_state) md',
  cl_lmem B cx h i n now op nb fr len nn regs ly3 S3 W mem3 ->
  DCTX cx ly3 S3 W mem3 md3 kk -> d_E cx E ->
  DCTX cx ly3 S3 W (ms_mem ms) md' kk ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (cl_vals regs xs)) ss (restrict (w_H W) ms) ->
  (forall x, ms_mem ms x = mem3 x) ->
  (forall r : bv 5, In r s4_rl -> sr_get (ss_regs ss) r = sr_get cl_sr r) ->
  cl_lmem B cx h i n now op nb fr len nn (ms_regs ms) ly3 S3 W (ms_mem ms).
Proof.
intros fq cx h i n now op nb fr len nn regs ly3 S3 W mem3 md3 kk E xs ss ms md' HL HC HE HC4 HS MEQ SR.
pose proof HL as (Sg & G & push & HB & _). pose proof HB as (_ & _ & _ & _ & _ & HrL & _).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 kk HC) as (Hal16 & Hslo & Hshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (KL : forall r : bv 5, In r s4_rl -> getr (ms_regs ms) r = getr regs r).
{ apply (s4_keep_regs cx E xs regs (ms_regs ms) s4_rl HE HrL HAr2). intros r Hr.
  rewrite (st_ok_pi_restrict_reg (w_H W) _ ss ms r HS), (SR r Hr). reflexivity. }
apply (s4_lmem_keep cx h i n now op nb fr len nn regs (ms_regs ms) ly3 S3 W mem3 md3 kk (ms_mem ms) md' kk
  (d_A cx) (d_A cx) HL HC HC4).
- unfold MFRAME, LLVMF_STK in *. lia.
- lia.
- intros a _ _. apply s4_aview_ext. exact MEQ.
- intros a Hp. exact (s4_pres_ext (w_H W) mem3 (ms_mem ms) MEQ a Hp).
- exact (s4_rL_eq cx regs (ms_regs ms) HrL KL).
Qed.

Ltac s4_cfg := lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
  let ms4 := fresh "ms4" in let md4 := fresh "md4" in set (ms4 := msx) in *; set (md4 := mdx) in * end.

Ltac s4_mem M Mp :=
  lazymatch goal with HF : frame_of _ _ _ (ms_mem _) |- _ =>
    pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as M; cbn [ms_mem mkst] in M end;
  clear_frames;
  lazymatch type of M with forall x, ms_mem ?b x = ?a x =>
    lazymatch type of Mp with forall y, ?a y = ?c y =>
      let Mn := fresh "Mn" in assert (Mn : forall x, ms_mem b x = c x) by (intros x; rewrite M; apply Mp);
      clear M Mp; rename Mn into Mp end end.

Lemma s4_l7 : cl_L7_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len nn k W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & kk & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HL &
  Hkn & R21 & R24 & R22 & R26).
pose proof HL as (Sg & G & push & HB3 & HSg & HG & HnnG & Hspl).
pose proof HG as (_ & _ & HGok). pose proof HGok as (_ & Hgn & _).
pose proof HB3 as (_ & _ & _ & _ & _ & HrL & _ & _ & _ & _ & _ & _ & _ & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
assert (HC : DCTX cx ly3 S3 W mem3 md3 kk) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 kk HC) as (Hal16 & Hslo & Hshi & HF0 & HFc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (s4_seat fq cx h ly3 S3 W regs mem3 md3 kk 0xf4c HC Hframe HrL) as (E & HE & HS).
set (xs := [w64 (dnot (d_obj cx OG))]) in HS.
pose proof (s4_img cx E (cl_vals regs xs) HE) as HEI.
pose proof HE as (_ & _ & _ & _ & E516 & _).
assert (D552 : ew (d_env cx E (cl_vals regs xs)) 552 = Z_to_bv 64 k)
  by exact (eq_trans (s4_ewr cx E regs xs 552 21 21%bv eq_refl eq_refl ltac:(lia)) R21).
assert (D555 : ew (d_env cx E (cl_vals regs xs)) 555 = Z_to_bv 64 nn)
  by exact (eq_trans (s4_ewr cx E regs xs 555 24 24%bv eq_refl eq_refl ltac:(lia)) R24).
assert (D553 : ew (d_env cx E (cl_vals regs xs)) 553 = Z_to_bv 64 (32 * (k + 1)))
  by exact (eq_trans (s4_ewr cx E regs xs 553 22 22%bv eq_refl eq_refl ltac:(lia)) R22).
assert (D557 : ew (d_env cx E (cl_vals regs xs)) 557 = Z_to_bv 64 (32 * nn))
  by exact (eq_trans (s4_ewr cx E regs xs 557 26 26%bv eq_refl eq_refl ltac:(lia)) R26).
assert (D516 : ew (d_env cx E (cl_vals regs xs)) 516 = Z_to_bv 64 (d_FB cx))
  by (rewrite s4_ewo by (unfold AT_FL; lia); exact E516).
assert (M0 : forall x, mem3 x = mem3 x) by reflexivity.
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + 0xf4c)) with (Z_to_bv 64 (BASE + 0xf4c)).
unfold s4_ss in HS.
paj_run_to_sh RUNTO HS HJ 0xf68; [unfold s4_rs; cbn [ss_mem]; awr_ok_tac|].
s4_mem M1 M0.
psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U, (U_atom_off _ 552 k 1 D552), (U_atom _ 555 nn D555) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hge.
  paj_run_to_sh RUNTO HS HJ 0xfac; [awr_ok_tac|].
  s4_mem M2 M0.
  psrr_branch_pi RUNP BR HS.
  + exfalso. rewrite branch_ne_U, (U_atom_off _ 552 k 1 D552), (U_atom _ 555 nn D555) in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc. lia.
  + clear Hc. paj_run_to_sh RUNTO HS HJ 0xfac; [awr_ok_tac|].
    s4_mem M3 M0.
    s4_cfg.
    assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms4) md4 kk) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
    pose proof (s4_land fq cx h i n now op nb fr len nn regs ly3 S3 W mem3 md3 kk E xs _ ms4 md4 HL HC HE HC4 HS M0)
      as HLM.
    specialize (HLM ltac:(s4_srk)).
    pmkst HS. apply SRr_ret. left.
    unfold cl_X, d_at. exists fq, ly3, S3, (ms_regs ms4), (ms_mem ms4), md4, kk, acc.
    split; [reflexivity|]. split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
    split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
    exact (s4_x_of cx h i n now op nb fr len nn (ms_regs ms4) ly3 S3 W (ms_mem ms4) HLM).
- rewrite branch_geu_U, (U_atom_off _ 552 k 1 D552), (U_atom _ 555 nn D555) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hlt.
  paj_run_to_sh RUNTO HS HJ 0xf68; [awr_ok_tac|].
  s4_mem M2 M0.
  s4_cfg.
  assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms4) md4 kk) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  pose proof (s4_land fq cx h i n now op nb fr len nn regs ly3 S3 W mem3 md3 kk E xs _ ms4 md4 HL HC HE HC4 HS M0)
    as HLM.
  specialize (HLM ltac:(s4_srk)).
  s4_rg HS (21%bv : bv 5) X21. s4_rg HS (22%bv : bv 5) X22. s4_rg HS (23%bv : bv 5) X23.
  s4_rg HS (24%bv : bv 5) X24. s4_rg HS (25%bv : bv 5) X25. s4_rg HS (26%bv : bv 5) X26.
  pmkst HS. apply SRr_ret. right.
  unfold cl_LJ, d_at. exists fq, ly3, S3, (ms_regs ms4), (ms_mem ms4), md4, kk, acc.
  split; [reflexivity|]. split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
  split; [exact HLM|].
  unfold cl_jregs. split; [lia|]. split; [exact Hlt|].
  split; [rewrite X21; exact (s4_off_den _ 552 k 1 D552 ltac:(lia))|].
  split; [rewrite X24, sv_denot_SOff0; exact D555|].
  split; [rewrite X22, sv_denot_SOff0; exact D553|].
  split; [rewrite X26, sv_denot_SOff0; exact D557|].
  split; [rewrite X25, (s4_sll_den _ 516 552 (d_FB cx) k D516 D552) by lia; reflexivity|].
  rewrite X23, sv_denot_SOff0. exact D553.
Qed.

Theorem pb_cl_L7 : cl_L7_stmt B MT XM_LIB RLO RHI tfib_K.
Proof. exact s4_l7. Qed.

Lemma s4_l8 : cl_L8_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len nn k j W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & kk & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HL & HJR).
pose proof HL as (Sg & G & push & HB3 & HSg & HG & HnnG & Hspl).
pose proof HJR as (Hkj & Hjn & R21 & R24 & R22 & R26 & R25 & R23).
pose proof HG as (LG & GG & HGok). pose proof HGok as (_ & Hgn & _).
pose proof HB3 as (_ & _ & _ & _ & _ & HrL & _ & _ & _ & _ & _ & _ & _ & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _).
assert (HC : DCTX cx ly3 S3 W mem3 md3 kk) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 kk HC)
  as (Hal16 & Hslo & Hshi & HF0 & HFc & HFia & _ & HFal & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (EOG : d_obj cx OG = d_FB cx + 2624) by reflexivity.
destruct (s4_seat fq cx h ly3 S3 W regs mem3 md3 kk 0xf68 HC Hframe HrL) as (E & HE & HS).
set (xs := [w64 (dnot (d_obj cx OG))]) in HS.
pose proof (s4_img cx E (cl_vals regs xs) HE) as HEI.
pose proof HE as (_ & _ & _ & E60 & E516 & _).
assert (D554 : ew (d_env cx E (cl_vals regs xs)) 554 = Z_to_bv 64 (32 * j))
  by exact (eq_trans (s4_ewr cx E regs xs 554 23 23%bv eq_refl eq_refl ltac:(lia)) R23).
assert (D563 : ew (d_env cx E (cl_vals regs xs)) 563 = Z_to_bv 64 (dnot (d_obj cx OG)))
  by exact (s4_ewx cx E regs xs 563 0 eq_refl ltac:(unfold xs; cbn; lia)).
assert (D516 : ew (d_env cx E (cl_vals regs xs)) 516 = Z_to_bv 64 (d_FB cx))
  by (rewrite s4_ewo by (unfold AT_FL; lia); exact E516).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNC.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + 0xf68)) with (Z_to_bv 64 (BASE + 0xf68)).
unfold s4_ss in HS.
paj_run_to_sh RUNTO HS HJ 0xf94; [unfold s4_rs; cbn [ss_mem]; awr_ok_tac|].
pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as M1. cbn [ms_mem mkst] in M1. clear HF HFr HG.
psrr_branch_pi RUNP BR HS; cycle 1.
{ exfalso. rewrite branch_ne_U, (U_atom _ 554 (32 * j) D554) in Hc by lia. rewrite U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc. clear - Hc Hkj Hjn HnnG Hgn. lia. }
clear Hc.
paj_run_to_sh RUNTO HS HJ 0xf94; [awr_ok_tac|].
pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as M2. clear HF HFr HG.
psrr_branch_pi RUNP BR HS; cycle 1.
{ exfalso. rewrite branch_geu_U, (U_atom _ 563 (dnot (d_obj cx OG)) D563), (U_atom _ 554 (32 * j) D554) in Hc
    by (unfold dnot; try rewrite EOG; lia).
  apply negb_false_iff, Z.ltb_lt in Hc. unfold dnot in Hc. rewrite EOG in Hc. clear - Hc HFc C1 Hkj Hjn HnnG Hgn. lia. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ; [awr_ok_tac|].
pose proof (cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)) as M3. clear HF HFr HG.
lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ => set (ms3 := msx) in *; set (md3' := mdx) in * end.
assert (MT3 : forall x, ms_mem ms3 x = mem3 x).
{ intros x. rewrite M3. lazymatch type of M2 with forall y, ms_mem ?a y = _ => idtac end. rewrite M2. exact (M1 x). }
assert (KG : forall r : bv 5, In r s4_kl -> getr (ms_regs ms3) r = getr regs r)
  by exact (s4_keep_regs cx E xs regs (ms_regs ms3) s4_kl HE HrL HAr2 ltac:(s4_rgk HS)).
assert (KL : forall r : bv 5, In r s4_rl -> getr (ms_regs ms3) r = getr regs r)
  by exact (s4_keep_regs cx E xs regs (ms_regs ms3) s4_rl HE HrL HAr2 ltac:(s4_rgk HS)).
pose proof (s4_rL_eq cx regs (ms_regs ms3) HrL KL) as HrLT.
pose proof HrLT as (HspT & HgpT & HtpT & _).
s4_rg HS (10%bv : bv 5) Ra0. s4_rg HS (11%bv : bv 5) Ra1. s4_rg HS (12%bv : bv 5) Ra2. s4_rg HS (1%bv : bv 5) Rra.
assert (HC3 : DCTX cx ly3 S3 W (ms_mem ms3) md3' kk) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms3) md3' kk HC3)
  as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres3 & _ & _ & HAR3 & Hfin & Efa & _).
assert (Hsh3 : d_shadow cx dsh_rec W (ms_mem ms3))
  by (intros q Hq; rewrite (s4_aview_ext (w_H W) mem3 (ms_mem ms3) MT3); exact (Hshadow q Hq)).
assert (HF8 : d_FB cx mod 8 = 0) by (clear - HFal; lia).
pose proof (cl_obj_ra cx W (ms_mem ms3) OG Hsh3 HF8 ltac:(lia) ltac:(vm_compute; reflexivity)) as HRA.
change (dobj_size OG) with 264 in HRA.
assert (GG3 : garr8 SEGS (rd W (ms_mem ms3)) (d_obj cx OG) (map (fun b : byte => bv_unsigned b) G)).
{ eapply YC88.garr8_aview_kept; [|exact GG]. intros a _. apply s4_aview_ext. exact MT3. }
pmkst HS.
assert (HES : ESTACK = 4096) by reflexivity.
eapply SRr_bind.
{ apply (aj_bcmp_at SEGS B LAWS pa_segs_low _ (ABCMP fq) W (ms_regs ms3) (ms_mem ms3) LLVMF_STK (d_S cx) []
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3' kk
    (d_obj cx OG + 32 * k) (d_obj cx OG + 32 * j) 6 (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 0xf94)) HJ).
  - rewrite Ra0, sv_denot_SOff0, (s4_ewr cx E regs xs 556 25 25%bv eq_refl eq_refl ltac:(lia)). exact R25.
  - rewrite Ra1, (s4_add_den _ 516 554 (d_FB cx) (32 * j) 2624 D516 D554) by lia.
    reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - rewrite EOG. lia.
  - rewrite EOG. clear - HFc C1 Hkj Hjn HnnG Hgn. pose proof alloc_ceiling_lt. lia.
  - rewrite EOG. lia.
  - rewrite EOG. clear - HFc C1 Hkj Hjn HnnG Hgn. pose proof alloc_ceiling_lt. lia.
  - rewrite HspT. lia.
  - clear - HA2 Hal16. lia.
  - unfold MFRAME in HA1. lia.
  - rewrite HES. unfold MFRAME, LLVMF_STK in *. lia.
  - exact HgpT.
  - exact HtpT.
  - rewrite Rra. exact (codeptr_val _ 3988 HEI).
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [apply aview_some_of_apresent; apply HFpres3; rewrite EOG in Ha; lia|].
    rewrite HspT, HES. rewrite EOG in Ha. unfold LLVMF_STK, MFRAME in *. lia.
  - intros a Ha. split; [apply aview_some_of_apresent; apply HFpres3; rewrite EOG in Ha; lia|].
    rewrite HspT, HES. rewrite EOG in Ha. unfold LLVMF_STK, MFRAME in *. lia.
  - intros a Ha. rewrite HES. rewrite EOG in Ha. unfold LLVMF_STK, MFRAME in *. lia.
  - intros a Ha. rewrite HES. rewrite EOG in Ha. unfold LLVMF_STK, MFRAME in *. lia.
  - apply (amem_range_sub_app (d_FB cx) 4096); [exact HFia | lia | rewrite EOG; lia | rewrite EOG; lia | lia].
  - apply (amem_range_sub_app (d_FB cx) 4096); [exact HFia | lia | rewrite EOG; lia | rewrite EOG; lia | lia].
  - apply (range_addressable_sub _ _ (d_obj cx OG) 264); [exact HRA | lia | lia].
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W (ms_mem ms3) md3' DFRAME_CLASS (c_fpos cx));
      [exact HAR3 | exact Hfin | rewrite Efa, EOG; lia | rewrite Efa, cl_fs6, EOG; lia | lia].
  - apply (range_addressable_sub _ _ (d_obj cx OG) 264); [exact HRA | lia | lia].
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W (ms_mem ms3) md3' DFRAME_CLASS (c_fpos cx));
      [exact HAR3 | exact Hfin | rewrite Efa, EOG; lia | rewrite Efa, cl_fs6, EOG; lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
apply SRr_ret.
assert (HC2 : DCTX cx ly3 S3 W mem2 md2 kk) by (split; [exact Hbase | split; [exact HJ2 | exact Hfrs]]).
unfold cl_BR, d_at. exists fq, ly3, S3, regs2, mem2, md2, kk, acc.
split; [reflexivity|]. split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ2|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
split; [|split].
- apply (s4_lmem_keep cx h i n now op nb fr len nn regs regs2 ly3 S3 W mem3 md3 kk mem2 md2 kk
    (d_A cx - 2 * ESTACK) (d_A cx) HL HC HC2).
  + rewrite HES. unfold MFRAME, LLVMF_STK in *. lia.
  + lia.
  + intros a Ha Hn. rewrite (Hfr a Ha) by (replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) by lia; exact Hn).
    apply s4_aview_ext. exact MT3.
  + intros a Hp. apply Hpr2. apply (s4_pres_ext (w_H W) mem3 (ms_mem ms3) MT3). exact Hp.
  + exact (s4_rL_pres cx (ms_regs ms3) regs2 HP2 HrLT).
- exact (s4_jregs_pres cx nn k j (ms_regs ms3) regs2 HP2 (s4_jregs_eq cx nn k j regs (ms_regs ms3) HJR KG)).
- intros Hz0. rewrite Hv in Hz0. pose proof (proj1 Hcmp Hz0) as Hq.
  apply (s4_gate_ne (w_H W) (ms_mem ms3) (d_obj cx OG) G k j GG3 HGok); [lia | lia | rewrite HnnG; exact Hjn | exact Hq].
Qed.

Theorem pb_cl_L8 : cl_L8_stmt B MT XM_LIB RLO RHI tfib_K.
Proof. exact s4_l8. Qed.

Lemma s4_l9 : cl_L9_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len nn k j W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & kk & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HL &
  HJR & H10).
pose proof HJR as (Hkj & Hjn & R21 & R24 & R22 & R26 & R25 & R23).
pose proof HL as (Sg & G & push & HB3 & HSg & HG & HnnG & Hspl).
pose proof HG as (_ & _ & HGok). pose proof HGok as (_ & Hgn & _).
pose proof HB3 as (_ & _ & _ & _ & _ & HrL & _ & _ & _ & _ & _ & _ & _ & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
assert (HC : DCTX cx ly3 S3 W mem3 md3 kk) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (s4_seat fq cx h ly3 S3 W regs mem3 md3 kk 0xf94 HC Hframe HrL) as (E & HE & HS).
set (xs := [w64 (dnot (d_obj cx OG))]) in HS.
pose proof (s4_img cx E (cl_vals regs xs) HE) as HEI.
assert (D541 : ew (d_env cx E (cl_vals regs xs)) 541 = getr regs 10)
  by exact (s4_ewr cx E regs xs 541 10 10%bv eq_refl eq_refl ltac:(lia)).
assert (D552 : ew (d_env cx E (cl_vals regs xs)) 552 = Z_to_bv 64 (k + 1))
  by exact (eq_trans (s4_ewr cx E regs xs 552 21 21%bv eq_refl eq_refl ltac:(lia)) R21).
assert (D555 : ew (d_env cx E (cl_vals regs xs)) 555 = Z_to_bv 64 nn)
  by exact (eq_trans (s4_ewr cx E regs xs 555 24 24%bv eq_refl eq_refl ltac:(lia)) R24).
assert (D553 : ew (d_env cx E (cl_vals regs xs)) 553 = Z_to_bv 64 (32 * (k + 1)))
  by exact (eq_trans (s4_ewr cx E regs xs 553 22 22%bv eq_refl eq_refl ltac:(lia)) R22).
assert (D557 : ew (d_env cx E (cl_vals regs xs)) 557 = Z_to_bv 64 (32 * nn))
  by exact (eq_trans (s4_ewr cx E regs xs 557 26 26%bv eq_refl eq_refl ltac:(lia)) R26).
assert (D556 : ew (d_env cx E (cl_vals regs xs)) 556 = Z_to_bv 64 (d_obj cx OG + 32 * k))
  by exact (eq_trans (s4_ewr cx E regs xs 556 25 25%bv eq_refl eq_refl ltac:(lia)) R25).
assert (D554 : ew (d_env cx E (cl_vals regs xs)) 554 = Z_to_bv 64 (32 * j))
  by exact (eq_trans (s4_ewr cx E regs xs 554 23 23%bv eq_refl eq_refl ltac:(lia)) R23).
assert (M0 : forall x, mem3 x = mem3 x) by reflexivity.
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + 0xf94)) with (Z_to_bv 64 (BASE + 0xf94)).
unfold s4_ss in HS.
psrr_branch_pi RUNP BR HS; cycle 1.
{ exfalso. rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc. apply U_inj in Hc.
  rewrite sv_denot_SOff0, D541 in Hc. apply H10. exact Hc. }
clear Hc.
paj_run_to_sh RUNTO HS HJ 0xf68; [unfold s4_rs; cbn [ss_mem]; awr_ok_tac|].
s4_mem M1 M0.
psrr_branch_pi RUNP BR HS.
- rewrite branch_ne_U, (U_atom _ 557 (32 * nn) D557), (U_atom_off _ 554 (32 * j) 32 D554) in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hne.
  paj_run_to_sh RUNTO HS HJ 0xf68; [awr_ok_tac|].
  s4_mem M2 M0.
  s4_cfg.
  assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms4) md4 kk) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  pose proof (s4_land fq cx h i n now op nb fr len nn regs ly3 S3 W mem3 md3 kk E xs _ ms4 md4 HL HC HE HC4 HS M0)
    as HLM.
  specialize (HLM ltac:(s4_srk)).
  s4_rg HS (21%bv : bv 5) X21. s4_rg HS (22%bv : bv 5) X22. s4_rg HS (23%bv : bv 5) X23.
  s4_rg HS (24%bv : bv 5) X24. s4_rg HS (25%bv : bv 5) X25. s4_rg HS (26%bv : bv 5) X26.
  pmkst HS. apply SRr_ret. left.
  unfold cl_LJ, d_at. exists fq, ly3, S3, (ms_regs ms4), (ms_mem ms4), md4, kk, acc.
  split; [reflexivity|]. split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
  split; [exact HLM|].
  unfold cl_jregs. split; [lia|]. split; [lia|].
  split; [rewrite X21, sv_denot_SOff0; exact D552|].
  split; [rewrite X24, sv_denot_SOff0; exact D555|].
  split; [rewrite X22, sv_denot_SOff0; exact D553|].
  split; [rewrite X26, sv_denot_SOff0; exact D557|].
  split; [rewrite X25, sv_denot_SOff0; exact D556|].
  rewrite X23, (s4_off_den _ 554 (32 * j) 32 D554) by lia. unfold w64. f_equal. lia.
- rewrite branch_ne_U, (U_atom _ 557 (32 * nn) D557), (U_atom_off _ 554 (32 * j) 32 D554) in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Heq.
  paj_run_to_sh RUNTO HS HJ 0xfac; [awr_ok_tac|].
  s4_mem M2 M0.
  psrr_branch_pi RUNP BR HS; cycle 1.
  { exfalso. rewrite branch_ne_U, (U_atom _ 552 (k + 1) D552), (U_atom _ 555 nn D555) in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  clear Hc.
  paj_run_to_sh RUNTO HS HJ 0xf4c; [awr_ok_tac|].
  s4_mem M3 M0.
  s4_cfg.
  assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms4) md4 kk) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  pose proof (s4_land fq cx h i n now op nb fr len nn regs ly3 S3 W mem3 md3 kk E xs _ ms4 md4 HL HC HE HC4 HS M0)
    as HLM.
  specialize (HLM ltac:(s4_srk)).
  s4_rg HS (21%bv : bv 5) X21. s4_rg HS (22%bv : bv 5) X22. s4_rg HS (24%bv : bv 5) X24. s4_rg HS (26%bv : bv 5) X26.
  pmkst HS. apply SRr_ret. right. left.
  unfold cl_LI, d_at. exists fq, ly3, S3, (ms_regs ms4), (ms_mem ms4), md4, kk, acc.
  split; [reflexivity|]. split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
  split; [exact HLM|]. split; [lia|].
  split; [rewrite X21, sv_denot_SOff0; exact D552|].
  split; [rewrite X24, sv_denot_SOff0; exact D555|].
  split; [rewrite X22, (s4_off_den _ 553 (32 * (k + 1)) 32 D553) by lia; unfold w64; f_equal; lia|].
  rewrite X26, sv_denot_SOff0. exact D557.
Qed.

Theorem pb_cl_L9 : cl_L9_stmt B MT XM_LIB RLO RHI tfib_K.
Proof. exact s4_l9. Qed.

End h.
End f.
End d.
