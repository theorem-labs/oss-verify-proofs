(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of rec_shape_of (plugin-hostd/fuzz_command, 0x891ec, 69 instructions),
   in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the entry state with the GOT word and the shadow cell)
   and A/ACh5.v (the composition of the segments into the contract): the prologue up to the loop head (0x891ec ..
   0x89254), then the loop of lib/A/Prog/rec_shape_of_s.v for the 28 rows, from the image's read-only table g_shapes
   and the literals it points to (lib/A/Prog/CmdRo.v). The per-binary facts are the lemmas of CmdRecFacts' groups in
   lib/A/Prog/CmdRecBase.v, CmdRecRo.v and CmdRecImg.v, under the walk hypotheses
   (with cgif's names). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_shape_of.v, with its module paths and module names changed; 3488 of its 3546 lines of code are new or changed and 260 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK06.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YI0m YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8i YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YN3v YI04 YI08 YA0o YCbm YA0q YC81 YC88 YC4b YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
reac_disco_table_observe_c disco_table_c disco_table reac_disco_table_observe.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition rs_hold (A : Prop) : Prop := A.
Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.
#[local] Ltac Lia.lia ::=
  first [ LiaTwx2.zify_prune; LiaTwx2.zify_noeuclid; xlia zchecker
        | LiaTwx2.zify_prune; LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]. #[local] Ltac rlia := first [ LiaTwx2.zify_prune; LiaTwx2.zify_noeuclid; xlia zchecker | LiaTwx2.zify_noeuclid; xlia zchecker | lia ]. #[local] Ltac kprune := first [ lazymatch goal with Hr : 0 <= _ < 8 |- _ => first [ lazymatch goal with |- context [length ?Y] => lazymatch goal with Hl : length Y = _ |- _ => clear - Hr Hl end end | clear - Hr ] end | idtac ].
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Definition REAC_DISCO_TABLE_OBSERVE_STK : Z := 112 + 2 * ESTACK.
Definition treac_disco_table_observe_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp t : Z) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_TABLE_OBSERVE_STK <= a < sp) -> ~ (t <= a < t + 400) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (t <= b + i < t + 400) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ (t <= a < t + 400) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - REAC_DISCO_TABLE_OBSERVE_STK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, sp - REAC_DISCO_TABLE_OBSERVE_STK <= a < sp -> apresent (w_H W2) mem2 a).
Definition treac_disco_table_observe_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z))
  (ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (t s ow now : Z) (T G : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (T' : list byte) (ret : Z),
    c2 = mkCfg (YK11.mkst (fx := fq) regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ YK11.getr regs2 10 = w64 ret /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    treac_disco_table_observe_kept lyc Sc W memc W2 mem2 (spZ regs) t /\
    garr8 SEGS (mrestrict (w_H W2) mem2) t (map (fun b : byte => bv_unsigned b) T') /\ length T' = 400%nat /\
    garr8 SEGS (mrestrict (w_H W2) mem2) s (map (fun b : byte => bv_unsigned b) G) /\
    reac_disco_table_observe_c.observe_model T G ow now T' ret /\
    disco_table_c.tbl_T1 T' /\ disco_table_c.tbl_T2 T' /\ disco_table_c.tbl_T3 T' /\
    (disco_table_c.tbl_T4 T -> disco_table_c.tbl_T4 T').
Definition treac_disco_table_observe_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (t s ow now : Z) (T G : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
  YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  YK11.getr regs 10 = w64 t -> YK11.getr regs 11 = w64 s -> YK11.getr regs 12 = w64 ow -> YK11.getr regs 13 = w64 now ->
  -2 ^ 31 <= ow < 2 ^ 31 -> 0 <= now < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_DISCO_TABLE_OBSERVE_STK -> spZ regs <= sp0 ->
  0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 -> amem_range t 400 ->
  (spZ regs <= t \/ t + 400 <= spZ regs - REAC_DISCO_TABLE_OBSERVE_STK) ->
  (forall a, t <= a < t + 400 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) t 400 ->
  garr8 SEGS (mrestrict (w_H W) memc) t (map (fun b : byte => bv_unsigned b) T) -> length T = 400%nat ->
  0 < s -> s + 24 <= 2 ^ 63 -> amem_range s 24 ->
  s mod 8 = 0 -> (forall a, s <= a < s + 24 -> apresent (w_H W) memc a) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 24 ->
  (spZ regs <= s \/ s + 24 <= spZ regs - REAC_DISCO_TABLE_OBSERVE_STK) ->
  shadow_hull_vis (aview SEGS (w_H W) memc) s 24 ->
  garr8 SEGS (mrestrict (w_H W) memc) s (map (fun b : byte => bv_unsigned b) G) -> length G = 24%nat ->
  ((exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= s /\ s + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
   (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= s /\ s + 24 <= b + req_size m)) ->
  s + 24 <= t \/ t + 400 <= s ->
  disco_table_c.tbl_T1 T -> disco_table_c.tbl_T2 T -> disco_table_c.tbl_T3 T ->
  disco_table_c.sighting_S1 G -> disco_table_c.sighting_S2 G ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_disco_table_observe) regs memc mdc)
    (treac_disco_table_observe_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs t s ow now T G).
Lemma le_bytes_nth : forall n z kk, (kk < n)%nat ->
  nth_error (Z_to_le_bytes n z) kk = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat kk))).
Proof.
induction n as [|n IH]; intros z kk Hk; [lia|].
destruct kk as [|kk]; cbn [Z_to_le_bytes nth_error].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma z8_mod : forall x, Z_to_bv 8 (x mod 256) = Z_to_bv 8 x.
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_mod. lia.
Qed.
Lemma garr8_byte : forall (m : word -> option byte) p (X : list byte) j b,
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) X) -> nth_error X j = Some b ->
  mbyte SEGS m (p + Z.of_nat j) = Some b.
Proof.
intros m p X j b HG Hj.
assert (Hl : (j < length (map (fun b : byte => bv_unsigned b) X))%nat)
  by (rewrite length_map; apply nth_error_Some; rewrite Hj; discriminate).
destruct (HG j Hl) as [Hm Hr].
assert (Hn : nth j (map (fun b : byte => bv_unsigned b) X) 0 = bv_unsigned b).
{ apply nth_error_nth. rewrite nth_error_map, Hj. reflexivity. }
rewrite Hn in Hm, Hr. specialize (Hm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hm. rewrite Z.add_0_r in Hm.
rewrite Hm, le_byte_1_0 by exact Hr. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma garr8_u_at : forall (m : word -> option byte) p (X : list byte) o (w : nat),
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) X) -> 0 <= o -> o + Z.of_nat w <= Z.of_nat (length X) ->
  val_mem SEGS m (p + o) w (disco_table_c.u_at X o w).
Proof.
intros m p X o w HG Ho Hw kk Hk.
set (v := disco_table_c.u_at X o w).
assert (Hle : Z_to_le_bytes w v = disco_table_c.sub X o w) by (apply reac_disco_table_observe.le_sub; lia).
assert (Hv : 0 <= v < 2 ^ (8 * Z.of_nat w)).
{ unfold v, disco_table_c.u_at. pose proof (disco_table.ble_range (disco_table_c.sub X o w)) as R.
  rewrite (disco_table.length_sub X o w) in R by lia. exact R. }
pose proof (le_bytes_nth w v kk Hk) as Hn. rewrite Hle in Hn.
rewrite reac_disco_table_observe.nth_sub in Hn by lia.
pose proof (garr8_byte m p X _ _ HG Hn) as Hb.
replace (p + o + Z.of_nat kk) with (p + Z.of_nat (Z.to_nat o + kk)) by lia. rewrite Hb.
f_equal. cbv delta [YG0f.le_byte YO0f.le_byte] beta. rewrite (Z.mod_small v) by lia. rewrite z8_mod. reflexivity.
Qed.
Definition ckv (o : Z) (w : N) (a : nat) : YP09.chunk := YP09.mkChunk o (CVal w (SOff a 0)).
Definition sav_chunks : list YP09.chunk :=
  [ckv 8 8 45; ckv 16 8 44; ckv 24 8 43; ckv 32 8 42; ckv 40 8 41; ckv 48 8 40; ckv 56 8 39;
   ckv 64 8 38; ckv 72 8 37; ckv 80 8 36; ckv 88 8 35; ckv 96 8 34; ckv 104 8 33].
Definition rK_stk : YP09.region := YP09.mkRegion (Some 2%nat) 0 112 0 0 (ckv 0 8 32 :: sav_chunks).
Definition rK_head : YP09.region := YP09.mkRegion (Some 8%nat) 384 396 384 396 [ckv 384 4 46; ckv 388 4 47; ckv 392 4 48].
Definition rK_ent : YP09.region := YP09.mkRegion (Some 19%nat) 0 48 8 48
  [ckv 8 4 49; ckv 12 1 50; ckv 13 1 51; ckv 14 1 52; ckv 15 1 53; ckv 16 1 54; ckv 20 4 55; ckv 24 4 56;
   ckv 17 3 64; ckv 28 4 65; ckv 32 8 66; ckv 40 8 67].
Definition rK_sig : YP09.region := YP09.mkRegion (Some 18%nat) 0 24 0 0
  [ckv 8 4 57; ckv 12 1 58; ckv 13 1 59; ckv 14 1 60; ckv 15 1 61; ckv 16 1 62; ckv 20 4 63].
Definition rg_K : smem := [rK_stk; rK_head; rK_ent; rK_sig].
Definition AF32 : afact := mkAF 0 (2 ^ 32 - 1) 0.
Definition AF8 : afact := mkAF 0 255 0.
Definition fa_K : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 8 (2 ^ 47 - 401) 3); (18%nat, mkAF 8 (2 ^ 47 - 25) 3);
    (19%nat, mkAF 8 (2 ^ 47 - 49) 3); (22%nat, mkAF SB SB 0);
    (46%nat, AF32); (47%nat, AF32); (48%nat, AF32);
    (49%nat, AF32); (50%nat, AF8); (51%nat, AF8); (52%nat, AF8); (53%nat, AF8); (54%nat, AF8);
    (55%nat, AF32); (56%nat, AF32);
    (57%nat, AF32); (58%nat, AF8); (59%nat, AF8); (60%nat, AF8); (61%nat, AF8); (62%nat, AF8); (63%nat, AF32) ] [] [].
Definition ss_K (pc : Z) : sstate := mkSS pc sr_atoms rg_K None fa_K.
Definition BxK : sv := SOff 22 0.
Definition SH_K : list shent := [mkSHE 8 0 400; mkSHE 19 0 48; mkSHE 18 0 24].
Definition rg_K6 : smem := [rK_stk; rK_head; rK_ent].
Definition fa_K6 : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 8 (2 ^ 47 - 401) 3);
    (19%nat, mkAF 8 (2 ^ 47 - 49) 3); (22%nat, mkAF SB SB 0); (14%nat, mkAF 0 1 0);
    (46%nat, AF32); (47%nat, AF32); (48%nat, AF32);
    (49%nat, AF32); (50%nat, AF8); (51%nat, AF8); (52%nat, AF8); (53%nat, AF8); (54%nat, AF8);
    (55%nat, AF32); (56%nat, AF32) ] [] [].
Definition ss_K6 (pc : Z) : sstate := mkSS pc sr_atoms rg_K6 None fa_K6.
Definition SH_K6 : list shent := [mkSHE 8 0 400; mkSHE 19 0 48].
Lemma mod64_32 : forall x, (x mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
intros x. rewrite (Z.mod_eq x (2 ^ 64)) by lia.
replace (x - 2 ^ 64 * (x / 2 ^ 64)) with (x + (- (2 ^ 32 * (x / 2 ^ 64))) * 2 ^ 32) by lia. apply Z.mod_add. lia.
Qed.
Lemma br_flag : forall E' (f : bool), ew E' 14 = Z_to_bv 64 (Z.b2z f) ->
  branch_taken BC_EQ (sv_denot E' (SOff 14 0)) (sv_denot E' (SLit 0)) = negb f.
Proof.
intros E' f H. rewrite branch_eq_U. unfold U. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
destruct f; cbn [Z.b2z negb]; rewrite !unsigned_lit_small by lia; reflexivity.
Qed.
Lemma br_s32z : forall E' n u, ew E' n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  branch_taken BC_EQ (sv_denot E' (SExt true 32 (SOff n 0))) (sv_denot E' (SLit 0)) = (u =? 0).
Proof.
intros E' n u H Hu. rewrite branch_eq_U, U_SExt, U_SOff, U_SLit, H, Z.add_0_r, unsigned_lit_small by lia.
change (Z.of_N 32) with 32. unfold zcanon, M64. rewrite (Z.mod_small u (2 ^ 64)) by lia.
rewrite (Z.mod_small u (2 ^ 32)) by lia. change (0 mod 2 ^ 64) with 0.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.eqb_spec u 0) as [->|Hn]; [reflexivity|]. apply Z.eqb_neq. intros Hm.
destruct (Z.ltb_spec u (2 ^ 31)).
- rewrite (Z.mod_small (u + 2 ^ 31)) in Hm by lia. rewrite Z.mod_small in Hm by lia. lia.
- rewrite <- (Z.mod_add (u + 2 ^ 31) (-1) (2 ^ 32)) in Hm by lia.
  rewrite (Z.mod_small (u + 2 ^ 31 + -1 * 2 ^ 32)) in Hm by lia.
  rewrite <- (Z.mod_add (u + 2 ^ 31 + -1 * 2 ^ 32 - 2 ^ 31) 1 (2 ^ 64)) in Hm by lia.
  rewrite Z.mod_small in Hm by lia. lia.
Qed.
Lemma br_ow : forall E' (ow : Z), -2 ^ 31 <= ow < 2 ^ 31 -> ew E' 5 = Z_to_bv 64 ow ->
  branch_taken BC_EQ (sv_denot E' (SOff 5 0)) (sv_denot E' (SLit 0)) = (ow =? 0).
Proof.
intros E' ow Hr H. rewrite branch_eq_U. unfold U. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (unsigned_lit_small 0) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.eqb_spec ow 0) as [->|Hn]; [reflexivity|]. apply Z.eqb_neq. intros Hm.
destruct (Z.leb_spec 0 ow).
- rewrite Z.mod_small in Hm by lia. lia.
- rewrite <- (Z.mod_add ow 1 (2 ^ 64)) in Hm by lia. rewrite Z.mod_small in Hm by lia. lia.
Qed.
Lemma seq_val : forall E' n u, ew E' n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  bv_unsigned (sv_denot E' (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1))) mod 2 ^ (8 * 4) = (u + 1) mod 2 ^ 32.
Proof.
intros E' n u H Hu.
change (bv_unsigned (sv_denot E' (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1))))
  with (U E' (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1))).
rewrite U_SAlu, U_SExt, U_SOff, U_SLit, H, Z.add_0_r, unsigned_lit_small by lia.
change (8 * 4) with 32. change (Z.of_N 32) with 32. cbn [zalu_raw]. unfold zcanon, M64.
rewrite mod64_32, Zplus_mod, mod64_32, (mod64_32 1).
rewrite (Z.mod_small u (2 ^ 64)) by lia.
change (2 ^ 32) with (bv_modulus 32). rewrite reac_disco_table_observe.swrap_mod, Zmod_mod.
rewrite <- Zplus_mod. reflexivity.
Qed.
Definition sx32 (u : Z) : Z := if u <? 2 ^ 31 then u else u + (2 ^ 64 - 2 ^ 32).
Lemma U_sx : forall E' n u, ew E' n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> U E' (SExt true 32 (SOff n 0)) = sx32 u.
Proof.
intros E' n u H Hu. rewrite U_SExt, (U_atom E' n u H) by lia. change (Z.of_N 32) with 32.
rewrite (Z.mod_small u (2 ^ 32)) by lia. unfold zcanon, M64, sx32, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec u (2 ^ 31)).
- rewrite (Z.mod_small (u + 2 ^ 31)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite <- (Z.mod_add (u + 2 ^ 31) (-1) (2 ^ 32)) by lia. rewrite (Z.mod_small (u + 2 ^ 31 + -1 * 2 ^ 32)) by lia.
  rewrite <- (Z.mod_add (u + 2 ^ 31 + -1 * 2 ^ 32 - 2 ^ 31) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma U_lit : forall E' z, 0 <= z < 2 ^ 64 -> U E' (SLit z) = z.
Proof. intros E' z Hz. rewrite U_SLit. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
Lemma sx_eqb : forall u v, 0 <= u < 2 ^ 32 -> 0 <= v < 2 ^ 32 -> (sx32 u =? sx32 v) = (u =? v).
Proof.
intros u v Hu Hv. unfold sx32. destruct (Z.ltb_spec u (2 ^ 31)), (Z.ltb_spec v (2 ^ 31));
destruct (Z.eqb_spec u v); first [reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
Qed.
Lemma sx_eqk : forall u z, 0 <= u < 2 ^ 32 -> 0 <= z < 2 ^ 31 -> (sx32 u =? z) = (u =? z).
Proof.
intros u z Hu Hz. unfold sx32. destruct (Z.ltb_spec u (2 ^ 31));
destruct (Z.eqb_spec u z); first [reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
Qed.
Lemma sx_ltb : forall u v, 0 <= u < 2 ^ 32 -> 0 <= v < 2 ^ 32 -> (sx32 u <? sx32 v) = (u <? v).
Proof.
intros u v Hu Hv. unfold sx32. destruct (Z.ltb_spec u (2 ^ 31)), (Z.ltb_spec v (2 ^ 31));
destruct (Z.ltb_spec u v); first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.
Lemma swrap32_val : forall u, 0 <= u < 2 ^ 32 -> bv_swrap 32 u = if u <? 2 ^ 31 then u else u - 2 ^ 32.
Proof.
intros u Hu. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec u (2 ^ 31)).
- rewrite Z.mod_small by lia. lia.
- rewrite <- (Z.mod_add (u + 2 ^ 31) (-1) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma s32_eqb : forall u v, 0 <= u < 2 ^ 32 -> 0 <= v < 2 ^ 32 -> (bv_swrap 32 u =? bv_swrap 32 v) = (u =? v).
Proof.
intros u v Hu Hv. rewrite (swrap32_val u Hu), (swrap32_val v Hv).
destruct (Z.ltb_spec u (2 ^ 31)), (Z.ltb_spec v (2 ^ 31));
destruct (Z.eqb_spec u v); first [reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
Qed.
Lemma s32_eqk : forall u z, 0 <= u < 2 ^ 32 -> 0 <= z < 2 ^ 31 -> (bv_swrap 32 u =? z) = (u =? z).
Proof.
intros u z Hu Hz. rewrite (swrap32_val u Hu). destruct (Z.ltb_spec u (2 ^ 31));
destruct (Z.eqb_spec u z); first [reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
Qed.
Lemma if_same_l : forall (A : Type) (c : bool) (x : A), (if c then x else x) = x.
Proof. intros A [|] x; reflexivity. Qed.
Lemma sub_if_d : forall (c : bool) X Y j n, disco_table_c.sub (if c then X else Y) j n =
  if c then disco_table_c.sub X j n else disco_table_c.sub Y j n.
Proof. intros [|] X Y j n; reflexivity. Qed.
Lemma len_if_d : forall (c : bool) (X Y : list byte), length (if c then X else Y) = if c then length X else length Y.
Proof. intros [|] X Y; reflexivity. Qed.
Lemma sx_val : forall E' n u, ew E' n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  bv_unsigned (sv_denot E' (SExt true 32 (SOff n 0))) mod 2 ^ (8 * 4) = u.
Proof.
intros E' n u H Hu. change (bv_unsigned (sv_denot E' (SExt true 32 (SOff n 0)))) with (U E' (SExt true 32 (SOff n 0))).
rewrite (U_sx E' n u H Hu). change (8 * 4) with 32. unfold sx32. destruct (Z.ltb_spec u (2 ^ 31)).
- apply Z.mod_small. lia.
- replace (u + (2 ^ 64 - 2 ^ 32)) with (u + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma br_ge0 : forall E' n u, ew E' n = Z_to_bv 64 u -> 0 <= u < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E' (SLit 0)) (sv_denot E' (SOff n 0)) = (u <=? 0).
Proof.
intros E' n u H Hu. cbn [branch_taken sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. unfold bv_lts, bv_signed.
rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0) by lia. rewrite (Z.mod_small u) by lia. rewrite !Z.mod_small by lia.
repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end;
destruct (Z.leb_spec u 0); first [reflexivity | lia].
Qed.
Lemma bv_eq_U : forall E' e z, 0 <= z < 2 ^ 64 -> U E' e = z -> sv_denot E' e = Z_to_bv 64 z.
Proof. intros E' e z Hz H. apply bv_eq. rewrite unsigned_lit_small by exact Hz. exact H. Qed.
Lemma n48 : forall E' u, ew E' 33 = Z_to_bv 64 u -> 1 <= u <= 8 ->
  sv_denot E' (SAlu ALU_SUB
    (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) (SLit 6))
    (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) (SLit 4))) =
  Z_to_bv 64 (48 * u).
Proof.
intros E' u H Hu. cbn [sv_denot]. rewrite H.
assert (Hc : u = 1 \/ u = 2 \/ u = 3 \/ u = 4 \/ u = 5 \/ u = 6 \/ u = 7 \/ u = 8) by lia.
repeat (destruct Hc as [-> | Hc]; [apply bv_eq; vm_compute; reflexivity |]). subst u. apply bv_eq; vm_compute; reflexivity.
Qed.
Section w.
Context {fx : YK11.FPState}.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (t s ow now : Z) (T G : list byte).
Hypothesis HJc : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : getr regs 3 = w64 (as_gp B).
Hypothesis Htp : getr regs 4 = w64 (as_tp B).
Hypothesis H10 : getr regs 10 = w64 t.
Hypothesis H11 : getr regs 11 = w64 s.
Hypothesis H12 : getr regs 12 = w64 ow.
Hypothesis H13 : getr regs 13 = w64 now.
Hypothesis Row : -2 ^ 31 <= ow < 2 ^ 31.
Hypothesis Rnow : 0 <= now < 2 ^ 64.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hwin : sp0 - STK <= spZ regs - REAC_DISCO_TABLE_OBSERVE_STK.
Hypothesis Hspl : spZ regs <= sp0.
Hypothesis Ht0 : 0 < t.
Hypothesis Ht8 : t mod 8 = 0.
Hypothesis Ht63 : t + 400 <= 2 ^ 63.
Hypothesis Htam : amem_range t 400.
Hypothesis Htside : spZ regs <= t \/ t + 400 <= spZ regs - REAC_DISCO_TABLE_OBSERVE_STK.
Hypothesis Htw : forall a, t <= a < t + 400 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a.
Hypothesis Htra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400.
Hypothesis Htsh : shadow_hull_vis (aview SEGS (w_H W) memc) t 400.
Hypothesis HTg : garr8 SEGS (mrestrict (w_H W) memc) t (map (fun b : byte => bv_unsigned b) T).
Hypothesis HTl : length T = 400%nat.
Hypothesis Hs0 : 0 < s.
Hypothesis Hs63 : s + 24 <= 2 ^ 63.
Hypothesis Hsam : amem_range s 24.
Hypothesis Hs8 : s mod 8 = 0.
Hypothesis Hspres : forall a, s <= a < s + 24 -> apresent (w_H W) memc a.
Hypothesis Hsra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 24.
Hypothesis Hsside : spZ regs <= s \/ s + 24 <= spZ regs - REAC_DISCO_TABLE_OBSERVE_STK.
Hypothesis Hssh : shadow_hull_vis (aview SEGS (w_H W) memc) s 24.
Hypothesis HGg : garr8 SEGS (mrestrict (w_H W) memc) s (map (fun b : byte => bv_unsigned b) G).
Hypothesis HGl : length G = 24%nat.
Hypothesis Hslive : (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= s /\
  s + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
  (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= s /\ s + 24 <= b + req_size m).
Hypothesis Hdts : s + 24 <= t \/ t + 400 <= s.
Hypothesis HT1 : disco_table_c.tbl_T1 T.
Hypothesis HT2 : disco_table_c.tbl_T2 T.
Hypothesis HT3 : disco_table_c.tbl_T3 T.
Hypothesis HS1 : disco_table_c.sighting_S1 G.
Hypothesis HS2 : disco_table_c.sighting_S2 G.
Definition tQ : world SEGS -> config -> Prop :=
  treac_disco_table_observe_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs t s ow now T G.
Definition tJ (m : word -> option byte) (md : Model) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k.
Definition tKP (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_DISCO_TABLE_OBSERVE_STK <= a < spZ regs) -> ~ (t <= a < t + 400) ->
  aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a.
Definition tPR (m : word -> option byte) : Prop := forall a, apresent (w_H W) memc a -> apresent (w_H W) m a.
Definition tTB (m : word -> option byte) (X : list byte) : Prop :=
  garr8 SEGS (mrestrict (w_H W) m) t (map (fun b : byte => bv_unsigned b) X) /\ length X = 400%nat.
Lemma stk_lo : alloc_ceiling <= spZ regs - REAC_DISCO_TABLE_OBSERVE_STK /\ spZ regs <= 2 ^ 47.
Proof.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
destruct Hst as (_ & _ & H3 & H4 & H5 & H6 & _). unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *. lia.
Qed.
Lemma tbl_off_img : forall a, t <= a < t + 400 -> ~ in_img SEGS a.
Proof.
intros a Ha Himg. destruct (Htw a Ha) as [Hw _].
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
pose proof (pa_img_range a Himg) as Hr. pose proof (pa_segs_low a Himg) as Hl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hst as (_ & _ & H3 & H4 & _).
destruct Hw as [Hst | [[_ (b & n & Hb & Hbr)] | [(b & n & Hb & _ & Hbr) | (cid & pos & Hin & Hz)]]].
- lia.
- pose proof (blk_off_imgP B lyc Sc W memc mdc b n HARc Hb) as Ho. unfold off_img in Ho. lia.
- pose proof (blk_off_imgP B lyc Sc W memc mdc b n HARc Hb) as Ho. unfold off_img in Ho. lia.
- assert (Hf : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HARc Hf) as Ho.
  pose proof (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hf) as (Hf1 & Hf2 & _).
  unfold off_img in Ho. unfold in_zr in Hz. cbn [fst snd] in Hz.
  destruct Hz as [Hz | Hz]; [lia|]. unfold shadow_addr, SHADOW_OFF in Hz. unfold YImgTop.IMG_TOP in Hr. lia.
Qed.
Lemma fin_post : forall regs2 m md X ret,
  tJ m md -> tKP m -> tPR m -> tTB m X ->
  aregs_preserved regs regs2 -> getr regs2 10 = w64 ret ->
  reac_disco_table_observe_c.observe_model T G ow now X ret ->
  tQ W (mkCfg (mkst regs2 (getr regs 1) m (seg_rom SEGS)) md).
Proof.
intros regs2 m md X ret HJ HK HP [HX HXl] HPR Hret HM.
pose proof (proj1 HJc) as HARc. pose proof stk_lo as [Hlo Hhi].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (reac_disco_table_observe.observe_model_tbl T G ow now X ret HTl HGl HT1 HT2 HT3 HS1 HS2 HM) as (U1 & U2 & U3 & U4).
exists lyc, Sc, regs2, m, md, X, ret.
split; [reflexivity|]. split; [exact HJ|]. split; [exact HPR|]. split; [exact Hret|].
split; [reflexivity|]. split; [apply Permutation_refl|].
split.
{ unfold treac_disco_table_observe_kept. split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn Ht. apply HK; [lia | exact Hn | exact Ht].
  - intros b n i Hb Hi Ht. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HARc Hb) as (_ & H4096 & Hce & _).
    apply HK; [lia | lia | exact Ht].
  - intros a Hi _ _. pose proof (pa_segs_low a Hi) as Hl.
    apply HK; [lia | lia | intros Ht; exact (tbl_off_img a Ht Hi)].
  - intros cid pos a Hf Ha Ht.
    pose proof (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hf) as (Hf1 & Hf2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfb.
    assert (Ha2 : 0 <= a < alloc_ceiling).
    { unfold frame_rng, in_zr in Ha. cbn [fst snd] in Ha. destruct Ha as [Ha | Ha]; [lia|].
      unfold shadow_addr, SHADOW_OFF in Ha.
      pose proof (Z.mul_div_le (frame_addr lyc cid pos) 8 ltac:(lia)).
      pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)).
      assert (0 <= frame_addr lyc cid pos / 8) by (apply Z.div_pos; lia).
      assert (0 <= fs_frame_bytes cid / 8) by (apply Z.div_pos; lia).
      lia. }
    apply HK; [lia | lia | exact Ht].
  - intros a Ha Hn Hp. exact (HP a Hp).
  - intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
    apply Hpres. lia. }
split; [exact HX|]. split; [exact HXl|].
split.
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W) memc m s); [|exact HGg].
  intros a Ha. rewrite length_map, HGl in Ha. apply HK; [lia | lia | lia]. }
split; [exact HM|]. tauto.
Qed.
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Definition SAVSL : list (Z * bv 5) :=
  [(104, 1%bv); (96, 8%bv); (88, 9%bv); (80, 18%bv); (72, 19%bv); (64, 20%bv); (56, 21%bv); (48, 22%bv);
   (40, 23%bv); (32, 24%bv); (24, 25%bv); (16, 26%bv); (8, 27%bv)].
Definition tSV (m : word -> option byte) : Prop :=
  forall o q, In (o, q) SAVSL -> val_mem SEGS (mrestrict (w_H W) m) (spZ regs - 112 + o) 8 (bv_unsigned (getr regs q)).
Definition tOW (m : word -> option byte) : Prop :=
  val_mem SEGS (mrestrict (w_H W) m) (spZ regs - 112 + 0) 8 (bv_unsigned (Z_to_bv 64 ow)).
Definition xK (X : list byte) (r : Z) : list word :=
  Z_to_bv 64 ow :: getr regs 1 :: getr regs 8 :: getr regs 9 :: getr regs 18 :: getr regs 19 :: getr regs 20 ::
  getr regs 21 :: getr regs 22 :: getr regs 23 :: getr regs 24 :: getr regs 25 :: getr regs 26 :: getr regs 27 ::
  map (Z_to_bv 64)
    [disco_table_c.u_at X 384 4; disco_table_c.u_at X 388 4; disco_table_c.u_at X 392 4;
     disco_table_c.u_at X (48 * r + 8) 4; disco_table_c.u_at X (48 * r + 12) 1; disco_table_c.u_at X (48 * r + 13) 1;
     disco_table_c.u_at X (48 * r + 14) 1; disco_table_c.u_at X (48 * r + 15) 1; disco_table_c.u_at X (48 * r + 16) 1;
     disco_table_c.u_at X (48 * r + 20) 4; disco_table_c.u_at X (48 * r + 24) 4;
     disco_table_c.u_at G 8 4; disco_table_c.u_at G 12 1; disco_table_c.u_at G 13 1; disco_table_c.u_at G 14 1;
     disco_table_c.u_at G 15 1; disco_table_c.u_at G 16 1; disco_table_c.u_at G 20 4;
     disco_table_c.u_at X (48 * r + 17) 3; disco_table_c.u_at X (48 * r + 28) 4; disco_table_c.u_at X (48 * r + 32) 8;
     disco_table_c.u_at X (48 * r + 40) 8].
Definition EK (regs' : bvmap 5 word) (X : list byte) (r : Z) : env := Eimg (Ereg regs' (xK X r)).
Lemma kp_ra : forall m a n, tKP m -> 0 <= a -> amem_range a n -> 0 <= n ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF a n -> range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n.
Proof.
intros m a n HK Ha Ham Hn H. apply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact H].
rs_hide_all. apply rs_hide in Rnow.
intros x Hx. pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Htam as Ht. unfold shadow_of_addr.
pose proof (Z.mul_div_le x 8 ltac:(lia)). pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_succ_div_gt x 8 ltac:(lia)).
apply HK; unfold amem_range, SHADOW_OFF, REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; rlia.
Qed.
Lemma kp_shv : forall m a n, tKP m -> 0 <= a -> amem_range a n -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) memc) a n -> shadow_hull_vis (aview SEGS (w_H W) m) a n.
Proof.
intros m a n HK Ha Ham Hn H x Hx. pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rs_hide_all. apply rs_hide in Rnow.
pose proof Htam as Ht. unfold shadow_addr, SHADOW_OFF in Hx.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le (a + n - 1) 8 ltac:(lia)).
pose proof (Z.mul_succ_div_gt a 8 ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + a / 8) 8 ltac:(lia)). pose proof (Z.mul_succ_div_gt (2147450880 + a / 8) 8 ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z.mul_div_le (a + n - 1) 8 ltac:(lia)). pose proof (Z.div_le_mono a (a + n - 1) 8 ltac:(lia) ltac:(lia)).
rewrite HK; [apply H; unfold shadow_addr, SHADOW_OFF; exact Hx | | |];
unfold amem_range, REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; rlia.
Qed.
Lemma kp_garr8_G : forall m, tKP m -> garr8 SEGS (mrestrict (w_H W) m) s (map (fun b : byte => bv_unsigned b) G).
Proof.
intros m HK. pose proof stk_lo as [Hlo Hhi].
apply (garr8_aview_kept SEGS (w_H W) (w_H W) memc m s); [|exact HGg]. intros a Ha. rewrite length_map, HGl in Ha.
apply HK; unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; lia.
Qed.
Lemma kst_ok : forall pc regs' m X r,
  tKP m -> tPR m -> tTB m X -> tSV m -> tOW m -> 0 <= r < 8 ->
  spZ regs' = spZ regs - 112 -> getr regs' 8 = w64 t -> getr regs' 18 = w64 s ->
  getr regs' 19 = w64 (t + 48 * r) -> getr regs' 22 = w64 SB ->
  st_ok_pi SEGS VAL (EK regs' X r) (ss_K pc) (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
  sh_ok SEGS BxK SH_K (EK regs' X r) (mrestrict (w_H W) m).
Proof.
intros pc regs' m X r HK HP [HX HXl] HSV HOW Hr Hsp R8 R18 R19 R22.
rs_hide_all. apply rs_hide in Rnow.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Htam as Hamt. pose proof Hsam as Hams. pose proof Htside as Hts. pose proof Hsside as Hss.
unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hlo, Hts, Hss.
pose proof (kp_garr8_G m HK) as HGm.
assert (E2 : ew (EK regs' X r) 2 = getr regs' 2)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ 2 2%bv eq_refl)).
assert (E8 : ew (EK regs' X r) 8 = Z_to_bv 64 t)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew (EK regs' X r) 18 = Z_to_bv 64 s)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew (EK regs' X r) 19 = Z_to_bv 64 (t + 48 * r))
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl); exact R19).
assert (E22 : ew (EK regs' X r) 22 = Z_to_bv 64 SB)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl); exact R22).
assert (VB : forall n v, ew (EK regs' X r) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val (EK regs' X r) (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (B2 : base_val (EK regs' X r) (Some 2%nat) = spZ regs - 112) by (cbn [base_val]; rewrite E2; exact Hsp).
assert (Rt : 0 <= t < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Rs : 0 <= s < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Re : 0 <= t + 48 * r < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Hwr : forall a, t <= a < t + 400 -> writable_at SEGS (mrestrict (w_H W) m) a).
{ intros a Ha. apply (apresent_writable SEGS). apply HP. exact (proj2 (Htw a Ha)). }
assert (UA : forall o w, 0 <= o -> o + Z.of_nat w <= 400 ->
  val_mem SEGS (mrestrict (w_H W) m) (t + o) w (disco_table_c.u_at X o w)).
{ intros o w Ho Hw. apply garr8_u_at; [exact HX | exact Ho | rewrite HXl; exact Hw]. }
assert (UG : forall o w, 0 <= o -> o + Z.of_nat w <= 24 ->
  val_mem SEGS (mrestrict (w_H W) m) (s + o) w (disco_table_c.u_at G o w)).
{ intros o w Ho Hw. apply garr8_u_at; [exact HGm | exact Ho | rewrite HGl; exact Hw]. }
assert (UR : forall bs o w, 0 <= disco_table_c.u_at bs o w < 2 ^ (8 * Z.of_N (N.of_nat w))).
{ intros bs o w. rewrite nat_N_Z. apply reac_disco_table_observe.u_at_range. }
rewrite restrict_mkst_fx.
split.
- unfold ss_K. apply pa_entry_st_ok_full.
  + unfold EK. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rg_K, rK_stk, rK_head, rK_ent, rK_sig, sav_chunks, ckv.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite B2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with
           | |- chunk_ok _ _ _ _ (YP09.mkChunk 0 _) =>
             apply (chunk_ok_val SEGS _ _ _ 0 8 _ (bv_unsigned (Z_to_bv 64 ow)));
             [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
               rewrite Z.add_0_r; reflexivity
             | pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 ow)) as Hb; unfold bv_modulus in Hb; zside
             | zside | exact HOW ]
           | |- chunk_ok _ _ _ _ (YP09.mkChunk ?o _) =>
             let q := lazymatch o with 104 => constr:(1%bv : bv 5) | 96 => constr:(8%bv : bv 5) | 88 => constr:(9%bv : bv 5)
               | 80 => constr:(18%bv : bv 5) | 72 => constr:(19%bv : bv 5) | 64 => constr:(20%bv : bv 5)
               | 56 => constr:(21%bv : bv 5) | 48 => constr:(22%bv : bv 5) | 40 => constr:(23%bv : bv 5)
               | 32 => constr:(24%bv : bv 5) | 24 => constr:(25%bv : bv 5) | 16 => constr:(26%bv : bv 5)
               | 8 => constr:(27%bv : bv 5) end in
             apply (chunk_ok_val SEGS _ _ _ o 8 _ (bv_unsigned (getr regs q)));
             [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
               rewrite Z.add_0_r; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs q)) as Hb; unfold bv_modulus in Hb; zside
             | zside | apply HSV; cbv [SAVSL In]; clear - Row; tauto ]
           end.
    * rewrite (VB 8%nat t E8 Rt). split; [lia|]. split; [lia|].
      split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?w _)) =>
        apply (chunk_ok_val SEGS _ _ _ o w _ (disco_table_c.u_at X o (N.to_nat w)));
        [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (UR X o (N.to_nat w)) as Hb; rewrite N2Nat.id in Hb; exact Hb
        | zside | apply UA; zside ] end.
    * rewrite (VB 19%nat (t + 48 * r) E19 Re). split; [lia|]. split; [lia|].
      split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?w _)) =>
        apply (chunk_ok_val SEGS _ _ _ o w _ (disco_table_c.u_at X (48 * r + o) (N.to_nat w)));
        [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (UR X (48 * r + o) (N.to_nat w)) as Hb; rewrite N2Nat.id in Hb; exact Hb
        | zside | replace (t + 48 * r + o) with (t + (48 * r + o)) by lia; apply UA; zside ] end.
    * rewrite (VB 18%nat s E18 Rs). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?w _)) =>
        apply (chunk_ok_val SEGS _ _ _ o w _ (disco_table_c.u_at G o (N.to_nat w)));
        [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (UR G o (N.to_nat w)) as Hb; rewrite N2Nat.id in Hb; exact Hb
        | zside | apply UG; zside ] end.
  + apply pairwise_disjoint_of_extents. unfold rg_K, rK_stk, rK_head, rK_ent, rK_sig, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2, (VB 8%nat t E8 Rt), (VB 19%nat (t + 48 * r) E19 Re),
      (VB 18%nat s E18 Rs).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold rs_hold in Hts, Hss, Hdts. unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *. repeat split; rlia.
  + split; [|split; [exact I | exact I]].
    unfold fa_K, AF32, AF8. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E18, E19, E22. change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
    rewrite !unsigned_lit_small by (unfold SB; lia).
    unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map].
    rewrite !unsigned_lit_small by (first [apply UR | pose proof (UR X 384 4) as U0; cbn in U0; lia
      | lazymatch goal with |- 0 <= disco_table_c.u_at ?bs ?o ?w < _ => pose proof (UR bs o w) as U0; cbn in U0; lia end]).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    pose proof (bv_unsigned_in_range 64 (getr regs' 14)) as H14.
    assert (Hm1 : (spZ regs - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
    assert (Hm2 : (t + 48 * r) mod 8 = 0) by (rewrite Zplus_mod, Ht8, Zmult_mod; reflexivity).
    assert (Ht8' : 8 <= t) by (pose proof (Z.div_mod t 8 ltac:(lia)) as Hd; rewrite Ht8 in Hd; lia).
    assert (Hs8' : 8 <= s) by (pose proof (Z.div_mod s 8 ltac:(lia)) as Hd; rewrite Hs8 in Hd; lia).
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamt, Hams.
    unfold rs_hold in Ht8, Hs8.
    repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- context [disco_table_c.u_at ?bs ?o ?w] => pose proof (UR bs o w) as U0; cbn in U0; rlia end
          | lazymatch goal with |- context [SB] => unfold SB; rlia end | rlia ].
- unfold sh_ok, SH_K. repeat apply Forall_cons; try apply Forall_nil; unfold shent_ok, app_apart, BxK;
  cbn [she_m she_lo she_hi].
  all: rewrite (U_atom _ 22 SB E22) by (unfold SB; lia).
  + rewrite (U_atom _ 8 t E8) by lia. split.
    * replace (t + 0) with t by lia. replace (400 - 0) with 400 by lia.
      exact (kp_ra m t 400 HK ltac:(lia) Htam ltac:(lia) Htra).
    * intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
  + rewrite (U_atom _ 19 (t + 48 * r) E19) by lia. split.
    * replace (t + 48 * r + 0) with (t + 48 * r) by lia. replace (48 - 0) with 48 by lia.
      apply (range_addressable_sub _ _ t 400); [exact (kp_ra m t 400 HK ltac:(lia) Htam ltac:(lia) Htra) | lia | lia].
    * intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
  + rewrite (U_atom _ 18 s E18) by lia. split.
    * replace (s + 0) with s by lia. replace (24 - 0) with 24 by lia.
      exact (kp_ra m s 24 HK ltac:(lia) Hsam ltac:(lia) Hsra).
    * intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
Qed.
Lemma kst6_ok : forall pc regs' m X r,
  tKP m -> tPR m -> tTB m X -> tSV m -> tOW m -> 0 <= r < 8 ->
  spZ regs' = spZ regs - 112 -> getr regs' 8 = w64 t ->
  getr regs' 19 = w64 (t + 48 * r) -> getr regs' 22 = w64 SB -> bv_unsigned (getr regs' 14) <= 1 ->
  st_ok_pi SEGS VAL (EK regs' X r) (ss_K6 pc) (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
  sh_ok SEGS BxK SH_K6 (EK regs' X r) (mrestrict (w_H W) m).
Proof.
intros pc regs' m X r HK HP [HX HXl] HSV HOW Hr Hsp R8 R19 R22 R14.
rs_hide_all. apply rs_hide in Rnow.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Htam as Hamt. pose proof Hsam as Hams. pose proof Htside as Hts. pose proof Hsside as Hss.
unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hlo, Hts, Hss.
assert (E2 : ew (EK regs' X r) 2 = getr regs' 2)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ 2 2%bv eq_refl)).
assert (E8 : ew (EK regs' X r) 8 = Z_to_bv 64 t)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl); exact R8).
assert (E14 : ew (EK regs' X r) 14 = getr regs' 14)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ 14 14%bv eq_refl)).
assert (E19 : ew (EK regs' X r) 19 = Z_to_bv 64 (t + 48 * r))
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl); exact R19).
assert (E22 : ew (EK regs' X r) 22 = Z_to_bv 64 SB)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl); exact R22).
assert (VB : forall n v, ew (EK regs' X r) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val (EK regs' X r) (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (B2 : base_val (EK regs' X r) (Some 2%nat) = spZ regs - 112) by (cbn [base_val]; rewrite E2; exact Hsp).
assert (Rt : 0 <= t < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Re : 0 <= t + 48 * r < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Hwr : forall a, t <= a < t + 400 -> writable_at SEGS (mrestrict (w_H W) m) a).
{ intros a Ha. apply (apresent_writable SEGS). apply HP. exact (proj2 (Htw a Ha)). }
assert (UA : forall o w, 0 <= o -> o + Z.of_nat w <= 400 ->
  val_mem SEGS (mrestrict (w_H W) m) (t + o) w (disco_table_c.u_at X o w)).
{ intros o w Ho Hw. apply garr8_u_at; [exact HX | exact Ho | rewrite HXl; exact Hw]. }
assert (UR : forall bs o w, 0 <= disco_table_c.u_at bs o w < 2 ^ (8 * Z.of_N (N.of_nat w))).
{ intros bs o w. rewrite nat_N_Z. apply reac_disco_table_observe.u_at_range. }
rewrite restrict_mkst_fx.
split.
- unfold ss_K6. apply pa_entry_st_ok_full.
  + unfold EK. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rg_K6, rK_stk, rK_head, rK_ent, sav_chunks, ckv.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite B2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with
           | |- chunk_ok _ _ _ _ (YP09.mkChunk 0 _) =>
             apply (chunk_ok_val SEGS _ _ _ 0 8 _ (bv_unsigned (Z_to_bv 64 ow)));
             [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
               rewrite Z.add_0_r; reflexivity
             | pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 ow)) as Hb; unfold bv_modulus in Hb; zside
             | zside | exact HOW ]
           | |- chunk_ok _ _ _ _ (YP09.mkChunk ?o _) =>
             let q := lazymatch o with 104 => constr:(1%bv : bv 5) | 96 => constr:(8%bv : bv 5) | 88 => constr:(9%bv : bv 5)
               | 80 => constr:(18%bv : bv 5) | 72 => constr:(19%bv : bv 5) | 64 => constr:(20%bv : bv 5)
               | 56 => constr:(21%bv : bv 5) | 48 => constr:(22%bv : bv 5) | 40 => constr:(23%bv : bv 5)
               | 32 => constr:(24%bv : bv 5) | 24 => constr:(25%bv : bv 5) | 16 => constr:(26%bv : bv 5)
               | 8 => constr:(27%bv : bv 5) end in
             apply (chunk_ok_val SEGS _ _ _ o 8 _ (bv_unsigned (getr regs q)));
             [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
               rewrite Z.add_0_r; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs q)) as Hb; unfold bv_modulus in Hb; zside
             | zside | apply HSV; cbv [SAVSL In]; clear - Row; tauto ]
           end.
    * rewrite (VB 8%nat t E8 Rt). split; [lia|]. split; [lia|].
      split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?w _)) =>
        apply (chunk_ok_val SEGS _ _ _ o w _ (disco_table_c.u_at X o (N.to_nat w)));
        [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (UR X o (N.to_nat w)) as Hb; rewrite N2Nat.id in Hb; exact Hb
        | zside | apply UA; zside ] end.
    * rewrite (VB 19%nat (t + 48 * r) E19 Re). split; [lia|]. split; [lia|].
      split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?w _)) =>
        apply (chunk_ok_val SEGS _ _ _ o w _ (disco_table_c.u_at X (48 * r + o) (N.to_nat w)));
        [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (UR X (48 * r + o) (N.to_nat w)) as Hb; rewrite N2Nat.id in Hb; exact Hb
        | zside | replace (t + 48 * r + o) with (t + (48 * r + o)) by lia; apply UA; zside ] end.
  + apply pairwise_disjoint_of_extents. unfold rg_K6, rK_stk, rK_head, rK_ent, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2, (VB 8%nat t E8 Rt), (VB 19%nat (t + 48 * r) E19 Re).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold rs_hold in Hts. unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *. repeat split; rlia.
  + split; [|split; [exact I | exact I]].
    unfold fa_K6, AF32, AF8. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E14, E19, E22. change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
    rewrite !unsigned_lit_small by (unfold SB; lia).
    unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map].
    rewrite !unsigned_lit_small by (first [apply UR | pose proof (UR X 384 4) as U0; cbn in U0; lia
      | lazymatch goal with |- 0 <= disco_table_c.u_at ?bs ?o ?w < _ => pose proof (UR bs o w) as U0; cbn in U0; lia end]).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    pose proof (bv_unsigned_in_range 64 (getr regs' 14)) as H14.
    assert (Hm1 : (spZ regs - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
    assert (Hm2 : (t + 48 * r) mod 8 = 0) by (rewrite Zplus_mod, Ht8, Zmult_mod; reflexivity).
    assert (Ht8' : 8 <= t) by (pose proof (Z.div_mod t 8 ltac:(lia)) as Hd; rewrite Ht8 in Hd; lia).
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamt, Hams.
    repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- context [disco_table_c.u_at ?bs ?o ?w] => pose proof (UR bs o w) as U0; cbn in U0; rlia end
          | lazymatch goal with |- context [SB] => unfold SB; rlia end | rlia ].
- unfold sh_ok, SH_K6. repeat apply Forall_cons; try apply Forall_nil; unfold shent_ok, app_apart, BxK;
  cbn [she_m she_lo she_hi].
  all: rewrite (U_atom _ 22 SB E22) by (unfold SB; lia).
  + rewrite (U_atom _ 8 t E8) by lia. split.
    * replace (t + 0) with t by lia. replace (400 - 0) with 400 by lia.
      exact (kp_ra m t 400 HK ltac:(lia) Htam ltac:(lia) Htra).
    * intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
  + rewrite (U_atom _ 19 (t + 48 * r) E19) by lia. split.
    * replace (t + 48 * r + 0) with (t + 48 * r) by lia. replace (48 - 0) with 48 by lia.
      apply (range_addressable_sub _ _ t 400); [exact (kp_ra m t 400 HK ltac:(lia) Htam ltac:(lia) Htra) | lia | lia].
    * intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
Qed.
Definition tbn (M : word -> option byte) (X : list byte) : Prop :=
  length X = 400%nat /\ forall j b, nth_error X j = Some b -> mbyte SEGS M (t + Z.of_nat j) = Some b.
Lemma tTB_tbn : forall m X, tTB m X -> tbn (mrestrict (w_H W) m) X.
Proof. intros m X [HG HL]. split; [exact HL|]. intros j b Hj. exact (garr8_byte _ _ _ _ _ HG Hj). Qed.
Lemma tbn_tTB : forall m X, tbn (mrestrict (w_H W) m) X -> tTB m X.
Proof.
intros m X [HL HN]. split; [|exact HL]. intros j Hj. rewrite length_map in Hj.
destruct (nth_error X j) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
assert (Hn : nth j (map (fun b : byte => bv_unsigned b) X) 0 = bv_unsigned b)
  by (apply nth_error_nth; rewrite nth_error_map, Hb; reflexivity).
rewrite Hn. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. change (2 ^ Z.of_N 8) with 256 in Hr.
split; [|lia]. intros kk Hk. destruct kk as [|kk]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, (HN j b Hb).
rewrite le_byte_1_0 by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition wapply (X : list byte) (ws : list (Z * nat * Z)) : list byte :=
  fold_left (fun acc (x : Z * nat * Z) => let '(o, w, v) := x in disco_table_c.upd acc o (Z_to_le_bytes w v)) ws X.
Definition wcov (ws : list (Z * nat * Z)) (j : Z) : Prop :=
  Exists (fun x : Z * nat * Z => let '(o, w, _) := x in o <= j < o + Z.of_nat w) ws.
Definition wvals (M : word -> option byte) (ws : list (Z * nat * Z)) : Prop :=
  Forall (fun x : Z * nat * Z => let '(o, w, v) := x in 0 <= o /\ o + Z.of_nat w <= 400 /\ val_mem SEGS M (t + o) w v) ws.
Fixpoint wdisj (ws : list (Z * nat * Z)) : Prop :=
  match ws with
  | [] => True
  | (o, w, _) :: r => (forall j, o <= j < o + Z.of_nat w -> ~ wcov r j) /\ wdisj r
  end.
Lemma upd_nth : forall (X bs : list byte) o j, 0 <= o -> o + Z.of_nat (length bs) <= Z.of_nat (length X) ->
  (j < length X)%nat ->
  nth_error (disco_table_c.upd X o bs) j =
  if (o <=? Z.of_nat j) && (Z.of_nat j <? o + Z.of_nat (length bs)) then nth_error bs (j - Z.to_nat o) else nth_error X j.
Proof.
intros X bs o j Ho Hl Hj. unfold disco_table_c.upd.
rewrite OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.upd_bytes_nth by lia.
destruct (Nat.leb_spec (Z.to_nat o) j); destruct (Nat.ltb_spec j (Z.to_nat o + length bs));
destruct (Z.leb_spec o (Z.of_nat j)); destruct (Z.ltb_spec (Z.of_nat j) (o + Z.of_nat (length bs))); cbn [andb];
first [reflexivity | lia].
Qed.
Lemma tbn_ws : forall ws M M' X, tbn M X -> wvals M' ws -> wdisj ws ->
  (forall j, 0 <= j < 400 -> ~ wcov ws j -> mbyte SEGS M' (t + j) = mbyte SEGS M (t + j)) ->
  tbn M' (wapply X ws).
Proof.
induction ws as [|[[o w] v] ws IH]; intros M M' X [HL HN] HV HD HF.
- change (wapply X []) with X. split; [exact HL|]. intros j b Hj.
  assert (Hjl : (j < 400)%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hj; discriminate).
  rewrite (HF (Z.of_nat j)) by (try lia; intros Hc; inversion Hc). exact (HN j b Hj).
- unfold wvals in HV. inversion HV as [|x r Hx HV' Heq]; subst. destruct Hx as [Ho [Hw Hvm]]. destruct HD as [HD1 HD2].
  cbn [wapply fold_left]. fold (wapply (disco_table_c.upd X o (Z_to_le_bytes w v)) ws).
  set (M1 := fun x : word => if (t + o <=? bv_unsigned x) && (bv_unsigned x <? t + o + Z.of_nat w) then M' x else M x).
  assert (HM1 : forall j, 0 <= j < 400 -> mbyte SEGS M1 (t + j) =
    if (o <=? j) && (j <? o + Z.of_nat w) then mbyte SEGS M' (t + j) else mbyte SEGS M (t + j)).
  { intros j Hj. unfold mbyte, M1. rewrite unsigned_lit_small by lia.
    destruct (Z.leb_spec (t + o) (t + j)); destruct (Z.ltb_spec (t + j) (t + o + Z.of_nat w));
    destruct (Z.leb_spec o j); destruct (Z.ltb_spec j (o + Z.of_nat w)); cbn [andb]; first [reflexivity | lia]. }
  apply (IH M1 M'); [| exact HV' | exact HD2 |].
  + pose proof (length_Z_to_le_bytes w v) as Hlw.
    split.
    * rewrite reac_disco_table_observe.upd_len by lia. exact HL.
    * intros j b Hj.
      assert (Hjl : (j < 400)%nat).
      { rewrite <- HL. rewrite <- (reac_disco_table_observe.upd_len X o (Z_to_le_bytes w v)) by lia.
        apply nth_error_Some. rewrite Hj. discriminate. }
      rewrite upd_nth in Hj by lia. rewrite (HM1 (Z.of_nat j)) by lia. rewrite Hlw in Hj.
      destruct ((o <=? Z.of_nat j) && (Z.of_nat j <? o + Z.of_nat w)) eqn:Hc.
      -- apply andb_true_iff in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2.
         rewrite <- (OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.Z_to_le_bytes_mod w v (8 * Z.of_nat w)) in Hj by lia.
         rewrite le_bytes_nth in Hj by lia. injection Hj as <-.
         pose proof (Hvm (j - Z.to_nat o)%nat ltac:(lia)) as Hb.
         replace (t + o + Z.of_nat (j - Z.to_nat o)) with (t + Z.of_nat j) in Hb by lia. rewrite Hb.
         f_equal. cbv delta [YG0f.le_byte YO0f.le_byte] beta. rewrite z8_mod; repeat f_equal; lia.
      -- exact (HN j b Hj).
  + intros j Hj Hnc. rewrite HM1 by exact Hj.
    destruct ((o <=? j) && (j <? o + Z.of_nat w)) eqn:Hc; [reflexivity|].
    apply HF; [exact Hj|]. intros Hcov. unfold wcov in Hcov. inversion Hcov as [x r Hx Heq | x r Hx Heq]; subst.
    * cbn beta iota in Hx. apply andb_false_iff in Hc as [Hc | Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc]; lia.
    * exact (Hnc Hx).
Qed.
Lemma tbn_cover : forall ws M M' X X', tbn M X -> length X' = 400%nat -> wvals M' ws ->
  (forall j, 0 <= j < 400 -> ~ wcov ws j ->
     mbyte SEGS M' (t + j) = mbyte SEGS M (t + j) /\ nth_error X' (Z.to_nat j) = nth_error X (Z.to_nat j)) ->
  Forall (fun x : Z * nat * Z => let '(o, w, v) := x in disco_table_c.sub X' o w = Z_to_le_bytes w v) ws ->
  tbn M' X'.
Proof.
intros ws M M' X X' [HL HN] HL' HV HF HE. split; [exact HL'|]. intros j b Hj.
assert (Hjl : (j < 400)%nat) by (rewrite <- HL'; apply nth_error_Some; rewrite Hj; discriminate).
destruct (Exists_dec (fun x : Z * nat * Z => let '(o, w, _) := x in o <= Z.of_nat j < o + Z.of_nat w) ws) as [Hc | Hc].
- intros [[o w] v]. destruct (Z_le_dec o (Z.of_nat j)); destruct (Z_lt_dec (Z.of_nat j) (o + Z.of_nat w));
  [left; lia | right; lia | right; lia | right; lia].
- apply Exists_exists in Hc as ([[o w] v] & Hin & Hov).
  unfold wvals in HV. rewrite Forall_forall in HV, HE.
  destruct (HV _ Hin) as (Ho & Hw & Hvm). pose proof (HE _ Hin) as Hs. cbv beta iota in Hs.
  assert (Hn : nth_error (disco_table_c.sub X' o w) (j - Z.to_nat o) = nth_error X' j).
  { rewrite reac_disco_table_observe.nth_sub by lia. f_equal. lia. }
  rewrite Hs, Hj in Hn.
  rewrite <- (OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.Z_to_le_bytes_mod w v (8 * Z.of_nat w)) in Hn by lia.
  rewrite le_bytes_nth in Hn by lia. injection Hn as <-.
  pose proof (Hvm (j - Z.to_nat o)%nat ltac:(lia)) as Hb.
  replace (t + o + Z.of_nat (j - Z.to_nat o)) with (t + Z.of_nat j) in Hb by lia. rewrite Hb.
  f_equal. cbv delta [YG0f.le_byte YO0f.le_byte] beta. rewrite z8_mod; repeat f_equal; lia.
- destruct (HF (Z.of_nat j) ltac:(lia) Hc) as [Hm Hx]. rewrite Hm. rewrite Nat2Z.id in Hx. rewrite Hx in Hj.
  exact (HN j b Hj).
Qed.
Lemma awr_tbl : forall E rs r, 0 <= r < 8 -> bv_unsigned (ew E 8) = t -> bv_unsigned (ew E 19) = t + 48 * r ->
  Forall (fun x : YP09.region => YP09.r_whi x <= YP09.r_wlo x \/
     (YP09.r_base x = Some 8%nat /\ 0 <= YP09.r_wlo x /\ YP09.r_whi x <= 400) \/
     (YP09.r_base x = Some 19%nat /\ 0 <= YP09.r_wlo x /\ YP09.r_whi x <= 48)) rs ->
  awr_ok E rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
intros E rs r Hr H8 H19 HF. induction HF as [|x rs Hx HF IH]; [apply awr_ok_nil|].
destruct Hx as [Hro | [(Hb & H1 & H2) | (Hb & H1 & H2)]].
- apply awr_ok_cons_ro; [exact Hro | exact IH].
- eapply awr_ok_cons_gen; [exact Hb | exact H8 | | exact IH]. intros a Ha. apply (Htw a). lia.
- eapply awr_ok_cons_gen; [exact Hb | exact H19 | | exact IH]. intros a Ha. apply (Htw a). lia.
Qed.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Definition WK (r : Z) (a : Z) : Prop := t + 384 <= a < t + 396 \/ t + 48 * r + 8 <= a < t + 48 * r + 48.
Lemma run_mem : forall E rs r m0 m1 m2,
  0 <= r < 8 ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> WK r a) ->
  tKP m1 -> tPR m1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ WK r a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a) ->
  tKP m2 /\ tPR m2 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ WK r a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m0 a).
Proof.
intros E rs r m0 m1 m2 Hr HF HG Hwn HK HP HO.
pose proof (kept_of_frame (segs := SEGS) E rs (w_H W) m1 m2 (WK r) HF Hwn) as HKF.
split; [|split].
- intros a Ha Hs Ht. rewrite (HKF a Ha) by (unfold WK; lia). apply HK; assumption.
- intros a Hp. eapply apresent_grows; [exact HG | apply HP; exact Hp].
- intros a Ha Hw. rewrite (HKF a Ha Hw). apply HO; assumption.
Qed.
Definition cws (E : env) (bo : Z) (cs : list YP09.chunk) : list (Z * nat * Z) :=
  flat_map (fun c : YP09.chunk => match YP09.c_val c with
    | CVal w e => [(bo + YP09.c_off c, N.to_nat w, bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w))]
    | _ => [] end) cs.
Definition cws_ok (bo : Z) (cs : list YP09.chunk) : Prop :=
  Forall (fun c : YP09.chunk => match YP09.c_val c with
    | CVal w _ => Z.of_N w <= 8 /\ 0 <= bo + YP09.c_off c /\ bo + YP09.c_off c + Z.of_N w <= 400
    | _ => True end) cs.
Lemma wvals_region : forall E M n lo hi wlo whi cs bo,
  region_ok SEGS E M (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = t + bo -> cws_ok bo cs ->
  wvals M (cws E bo cs).
Proof.
intros E M n lo hi wlo whi cs bo HR Hb Hok. unfold wvals, cws. apply Forall_forall. intros [[o w] v] Hin.
apply in_flat_map in Hin as (c & Hc & Hx). unfold cws_ok in Hok. rewrite Forall_forall in Hok.
pose proof (Hok c Hc) as Hcw.
destruct c as [co cv]. cbn [YP09.c_val YP09.c_off] in Hx, Hcw. destruct cv as [w' e | | |]; try (destruct Hx; fail).
destruct Hx as [Hx | []]. injection Hx as <- <- <-. destruct Hcw as (Hw8 & H0 & H1).
split; [lia|]. split; [rewrite N_nat_Z; lia|].
pose proof (field_of_region_any (segs := SEGS) E M n (t + bo) cs lo hi wlo whi co w' e HR Hb Hc Hw8) as Hv.
replace (t + bo + co) with (t + (bo + co)) in Hv by lia. exact Hv.
Qed.
Definition covb (cs : list YP09.chunk) (z : Z) : bool :=
  existsb (fun c : YP09.chunk => match YP09.c_val c with
    | CVal w _ => (YP09.c_off c <=? z) && (z <? YP09.c_off c + Z.of_N w) | _ => false end) cs.
Lemma wcov_covb : forall E bo cs z, covb cs z = true -> wcov (cws E bo cs) (bo + z).
Proof.
intros E bo cs z H. unfold covb in H. apply existsb_exists in H as (c & Hc & Hk).
unfold wcov, cws. apply Exists_exists. destruct c as [co cv]. cbn [YP09.c_val YP09.c_off] in Hk.
destruct cv as [w e | | |]; try discriminate.
exists (bo + co, N.to_nat w, bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)). split.
- apply in_flat_map. exists {| YP09.c_off := co; YP09.c_val := CVal w e |}. split; [exact Hc | left; reflexivity].
- apply andb_true_iff in Hk as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. cbv beta iota. rewrite N_nat_Z. lia.
Qed.
Definition covall (cs : list YP09.chunk) (lo hi : Z) : bool :=
  forallb (covb cs) (map (fun i => lo + Z.of_nat i) (List.seq 0 (Z.to_nat (hi - lo)))).
Lemma covall_ok : forall cs lo hi z, covall cs lo hi = true -> lo <= z < hi -> covb cs z = true.
Proof.
intros cs lo hi z H Hk. unfold covall in H. rewrite forallb_forall in H. apply H. apply in_map_iff.
exists (Z.to_nat (z - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma kleaf_tbn : forall E M M' X X' r csH csE,
  0 <= r < 8 -> tbn M X -> length X' = 400%nat ->
  region_ok SEGS E M' (YP09.mkRegion (Some 8%nat) 384 396 384 396 csH) -> bv_unsigned (ew E 8) = t ->
  region_ok SEGS E M' (YP09.mkRegion (Some 19%nat) 0 48 8 48 csE) -> bv_unsigned (ew E 19) = t + 48 * r ->
  cws_ok 0 csH -> cws_ok (48 * r) csE -> covall csH 384 396 = true -> covall csE 8 48 = true ->
  (forall j, 0 <= j < 400 -> ~ WK r (t + j) ->
     mbyte SEGS M' (t + j) = mbyte SEGS M (t + j) /\ nth_error X' (Z.to_nat j) = nth_error X (Z.to_nat j)) ->
  Forall (fun x : Z * nat * Z => let '(o, w, v) := x in disco_table_c.sub X' o w = Z_to_le_bytes w v)
    (cws E 0 csH ++ cws E (48 * r) csE) ->
  tbn M' X'.
Proof.
intros E M M' X X' r csH csE Hr HX HL RH UH RE UE OH OE CH CE HO HE.
apply (tbn_cover (cws E 0 csH ++ cws E (48 * r) csE) M M' X X'); try assumption.
- unfold wvals. apply Forall_app. split.
  + apply (wvals_region E M' 8 384 396 384 396 csH 0 RH); [rewrite Z.add_0_r; exact UH | exact OH].
  + exact (wvals_region E M' 19 0 48 8 48 csE (48 * r) RE UE OE).
- intros j Hj Hnc. apply HO; [exact Hj|]. intros Hw. apply Hnc. unfold wcov. apply Exists_app.
  unfold WK in Hw. destruct Hw as [Hw | Hw].
  + left. replace j with (0 + j) by lia. apply wcov_covb. apply (covall_ok csH 384 396); [exact CH | lia].
  + right. replace j with (48 * r + (j - 48 * r)) by lia. apply wcov_covb. apply (covall_ok csE 8 48); [exact CE | lia].
Qed.
Lemma apres_of : forall regs2,
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 -> getr regs2 18 = getr regs 18 ->
  getr regs2 19 = getr regs 19 -> getr regs2 20 = getr regs 20 -> getr regs2 21 = getr regs 21 ->
  getr regs2 22 = getr regs 22 -> getr regs2 23 = getr regs 23 -> getr regs2 24 = getr regs 24 ->
  getr regs2 25 = getr regs 25 -> getr regs2 26 = getr regs 26 -> getr regs2 27 = getr regs 27 ->
  aregs_preserved regs regs2.
Proof.
intros regs2 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 q Hq. unfold acallee_saved in Hq.
destruct Hq as [-> | [-> | [-> | [-> | [-> | Hq]]]]]; [exact H2 | exact H3 | exact H4 | exact H8 | exact H9 |].
assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
destruct Hq' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; assumption.
Qed.
Lemma sv_keep : forall m m', (forall a, spZ regs - 112 <= a < spZ regs -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  tSV m -> tOW m -> tSV m' /\ tOW m'.
Proof.
intros m m' He HS HO. split.
- intros o q Hin. pose proof (HS o q Hin) as Hv. apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) m m'); [|exact Hv].
  intros x Hx. apply He. cbv [SAVSL In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]). destruct Hin.
- apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) m m'); [|exact HO]. intros x Hx. apply He. lia.
Qed.
Lemma nth_upd_out : forall (X bs : list byte) o j, 0 <= o -> o + Z.of_nat (length bs) <= Z.of_nat (length X) ->
  (j < length X)%nat -> ~ (o <= Z.of_nat j < o + Z.of_nat (length bs)) ->
  nth_error (disco_table_c.upd X o bs) j = nth_error X j.
Proof.
intros X bs o j Ho Hl Hj Hn. rewrite upd_nth by assumption.
destruct ((o <=? Z.of_nat j) && (Z.of_nat j <? o + Z.of_nat (length bs)))%bool eqn:Hc; [|reflexivity].
apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma k6_mod : forall r f, 0 <= r < disco_table_c.n_of T -> disco_table_c.find_res T (disco_table_c.s_mac G) r ->
  f = (reac_disco_table_observe.cR T G r || reac_disco_table_observe.cD T G r || reac_disco_table_observe.cS T G r ||
      reac_disco_table_observe.cF T G r || reac_disco_table_observe.cC T G r)%bool ->
  forall X2 ret, (X2, ret) = (if (f || reac_disco_table_observe.cO T ow r)%bool
     then (disco_table_c.upd (reac_disco_table_observe.kG T G ow now r) 392
             (Z_to_le_bytes 4 (disco_table_c.seq_of T + 1)), 1)
     else (reac_disco_table_observe.kG T G ow now r, 0)) ->
  reac_disco_table_observe_c.observe_model T G ow now X2 ret.
Proof.
intros r f Hr FI Hf X2 ret HX. exists r. split; [exact FI|]. left. split; [lia|].
rewrite reac_disco_table_observe.known_eq. rewrite <- Hf. exact HX.
Qed.
Ltac ekq0 HE n H :=
  lazymatch type of HE with ?E = EK ?a ?b ?c =>
    let v := eval cbv [EK Eimg Ereg xK ew A_TEXT A_LIM Nat.leb Nat.ltb andb Nat.sub nth map] in (ew (EK a b c) n) in
    assert (H : ew E n = v) by (rewrite HE; reflexivity) end.
Tactic Notation "ekq" constr(HE) constr(n) ident(H) := ekq0 HE n H.
Tactic Notation "ekall" constr(HE) :=
  ekq HE 33%nat EQ33; ekq HE 34%nat EQ34; ekq HE 35%nat EQ35; ekq HE 36%nat EQ36; ekq HE 37%nat EQ37;
  ekq HE 38%nat EQ38; ekq HE 39%nat EQ39; ekq HE 40%nat EQ40; ekq HE 41%nat EQ41; ekq HE 42%nat EQ42;
  ekq HE 43%nat EQ43; ekq HE 44%nat EQ44; ekq HE 45%nat EQ45; ekq HE 46%nat EQ46; ekq HE 47%nat EQ47;
  ekq HE 48%nat EQ48; ekq HE 49%nat EQ49; ekq HE 50%nat EQ50; ekq HE 51%nat EQ51; ekq HE 52%nat EQ52;
  ekq HE 53%nat EQ53; ekq HE 54%nat EQ54; ekq HE 55%nat EQ55; ekq HE 56%nat EQ56; ekq HE 57%nat EQ57;
  ekq HE 58%nat EQ58; ekq HE 59%nat EQ59; ekq HE 60%nat EQ60; ekq HE 61%nat EQ61; ekq HE 62%nat EQ62;
  ekq HE 63%nat EQ63; ekq HE 64%nat EQ64; ekq HE 65%nat EQ65; ekq HE 66%nat EQ66; ekq HE 67%nat EQ67.
Ltac ekr := repeat match goal with H : ew ?E ?n = _ |- context [ew ?E ?n] => rewrite H end.
Ltac ekr_in Hc := repeat match goal with H : ew ?E ?n = _ |- _ =>
  lazymatch type of Hc with context [ew E n] => rewrite H in Hc end end.
Ltac awrK U8 U19 Hr8 :=
  apply (awr_tbl _ _ _ Hr8); [cbn [ew ewset extK Nat.eqb]; exact U8 | cbn [ew ewset extK Nat.eqb]; exact U19 |];
  lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_whi YP09.r_wlo YP09.r_base];
  first [left; apply Z.leb_le; reflexivity | right; left; split; [reflexivity | split; apply Z.leb_le; reflexivity] | right; right; split; [reflexivity | split; apply Z.leb_le; reflexivity] | left; lia | right; left; split; [reflexivity | lia] | right; right; split; [reflexivity | lia]].
Ltac kwin U8 U19 := intros b_ wlo_ whi_ a_ Hin_ Hr_; vm_compute in Hin_;
  repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val ew ewset extK Nat.eqb] in Hr_;
    rewrite ?U8, ?U19 in Hr_; unfold WK; first [clear - Hr_; lia | lia] |]); destruct Hin_.
Lemma rs_upd_len : forall X k v, 0 <= k /\ k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  length (disco_table_c.upd X k v) = length X.
Proof. intros X k0 v [H1 H2]. exact (reac_disco_table_observe.upd_len X k0 v H1 H2). Qed.
Lemma rs_len_if : forall (c : bool) X k v, 0 <= k /\ k + Z.of_nat (length v) <= Z.of_nat (length X) ->
  length (if c then disco_table_c.upd X k v else X) = length X.
Proof. intros c X k0 v [H1 H2]. exact (reac_disco_table_observe.len_if c X k0 v H1 H2). Qed.
Lemma rs_length_sub : forall bs k n, 0 <= k /\ k + Z.of_nat n <= Z.of_nat (length bs) ->
  length (disco_table_c.sub bs k n) = n.
Proof. intros bs k0 n [H1 H2]. exact (disco_table.length_sub bs k0 n H1 H2). Qed.
Lemma rs_sub_upd_other : forall X k v j n,
  0 <= k /\ 0 <= j /\ k + Z.of_nat (length v) <= Z.of_nat (length X) /\ j + Z.of_nat n <= Z.of_nat (length X) /\
  (j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j) ->
  disco_table_c.sub (disco_table_c.upd X k v) j n = disco_table_c.sub X j n.
Proof. intros X k0 v j n (H1 & H2 & H3 & H4 & H5). exact (reac_disco_table_observe.sub_upd_other X k0 v j n H1 H2 H3 H4 H5). Qed.
Lemma rs_sub_if_other : forall (c : bool) X k v j n,
  0 <= k /\ 0 <= j /\ k + Z.of_nat (length v) <= Z.of_nat (length X) /\ j + Z.of_nat n <= Z.of_nat (length X) /\
  (j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j) ->
  disco_table_c.sub (if c then disco_table_c.upd X k v else X) j n = disco_table_c.sub X j n.
Proof. intros c X k0 v j n (H1 & H2 & H3 & H4 & H5). exact (reac_disco_table_observe.sub_if_other c X k0 v j n H1 H2 H3 H4 H5). Qed.
Ltac mvl := repeat first [ progress cbn [length]
  | match goal with
    | H : length (disco_table_c.upd ?A ?B ?C) = _ |- context [length (disco_table_c.upd ?A ?B ?C)] => rewrite H
    | H : length (if ?A then ?B else ?C) = _ |- context [length (if ?A then ?B else ?C)] => rewrite H end
  | lazymatch goal with |- context [length (Z_to_le_bytes _ _)] => rewrite OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.length_Z_to_le_bytes end
  | lazymatch goal with |- context [length (disco_table_c.sub _ _ _)] => rewrite rs_length_sub by (first [kprune; lia | lia]) end
  | lazymatch goal with |- context [length (disco_table_c.upd _ _ _)] => rewrite rs_upd_len by (mvl; first [kprune; lia | lia]) end | lazymatch goal with |- context [length (if _ then _ else _)] => rewrite rs_len_if by (mvl; first [kprune; lia | lia]) end
  | lazymatch goal with |- context [length (if _ then _ else _)] => rewrite len_if_d end | lazymatch goal with |- context [if _ then _ else _] => rewrite if_same_l end ].
Ltac rs_lens L :=
  lazymatch goal with
  | _ : length L = _ |- _ => idtac
  | _ =>
    lazymatch L with
    | disco_table_c.upd ?Y _ _ => rs_lens Y
    | (if _ then ?Y1 else ?Y2) => rs_lens Y1; rs_lens Y2
    | _ => idtac
    end;
    lazymatch L with
    | disco_table_c.upd _ _ _ => let H := fresh "HLn" in try assert (H : length L = 400%nat) by (mvl; first [kprune; lia | lia])
    | (if _ then _ else _) => let H := fresh "HLn" in try assert (H : length L = 400%nat) by (mvl; first [kprune; lia | lia])
    | _ => idtac
    end
  end.
Ltac rs_lens_goal := try lazymatch goal with |- context [disco_table_c.sub ?L _ _] => rs_lens L end.
Ltac msub := repeat first [ lazymatch goal with |- context [disco_table_c.sub (disco_table_c.upd _ _ _) _ _] => rewrite rs_sub_upd_other by (mvl; kprune; LiaTwx2.zify_prune; LiaTwx2.zify_noeuclid; xlia zchecker) end
  | lazymatch goal with |- context [disco_table_c.sub (if _ then _ else _) _ _] => rewrite rs_sub_if_other by (mvl; kprune; LiaTwx2.zify_prune; LiaTwx2.zify_noeuclid; xlia zchecker) end ].
Ltac nnorm := repeat match goal with
  | |- context [N.to_nat ?n] => let v := eval vm_compute in (N.to_nat n) in change (N.to_nat n) with v
  | |- context [Z.of_N ?n] => let v := eval vm_compute in (Z.of_N n) in change (Z.of_N n) with v end.
Ltac katom := cbn [sv_denot ew ewset extK Nat.eqb]; ekr; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
  lazymatch goal with |- context [bv_unsigned (Z_to_bv 64 (disco_table_c.u_at ?bs ?o ?w))] =>
    pose proof (reac_disco_table_observe.u_at_range bs o w) as Ur; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ur;
    rewrite (unsigned_lit_small (disco_table_c.u_at bs o w)) by (clear - Ur; lia); rewrite (Z.mod_small (disco_table_c.u_at bs o w)) by (clear - Ur; lia);
    rewrite reac_disco_table_observe.le_sub by (mvl; first [kprune; lia | lia]) end;
  msub; reflexivity.
Ltac kchunks := rs_lens_goal; cbn [cws flat_map YP09.c_val YP09.c_off app]; nnorm;
  repeat apply Forall_cons; try apply Forall_nil; cbv beta iota; rewrite ?Z.add_0_l; try katom.
Ltac kfin X X' r ret HOf HKf HPf HXn HXl Hr8 U8 U19 U2 E3 E4 :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let Ra0 := fresh "Ra0" in let Rra := fresh "Rra" in let Q2 := fresh "Q2" in let Q3 := fresh "Q3" in
  let Q4 := fresh "Q4" in let Q8 := fresh "Q8" in let Q9 := fresh "Q9" in let Q18 := fresh "Q18" in
  let Q19 := fresh "Q19" in let Q20 := fresh "Q20" in let Q21 := fresh "Q21" in let Q22 := fresh "Q22" in
  let Q23 := fresh "Q23" in let Q24 := fresh "Q24" in let Q25 := fresh "Q25" in let Q26 := fresh "Q26" in
  let Q27 := fresh "Q27" in let RH := fresh "RH" in let RE := fresh "RE" in let mat' := fresh "mat" in
  prreg HS (10%bv : bv 5) Ra0; prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Q2;
  prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9;
  prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21;
  prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23; prreg HS (24%bv : bv 5) Q24; prreg HS (25%bv : bv 5) Q25;
  prreg HS (26%bv : bv 5) Q26; prreg HS (27%bv : bv 5) Q27;
  let rH := eval vm_compute in (nth 1 (ss_mem ss) (stack_region 0)) in
  let rE := eval vm_compute in (nth 2 (ss_mem ss) (stack_region 0)) in
  pose proof (st_ok_pi_region_nth Ex ss (restrict (w_H W) msx) 1 rH HS ltac:(vm_compute; reflexivity)) as RH;
  pose proof (st_ok_pi_region_nth Ex ss (restrict (w_H W) msx) 2 rE HS ltac:(vm_compute; reflexivity)) as RE;
  cbn [ms_mem restrict] in RH, RE;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros mat';
  rewrite Rra; ekr; rewrite (Hra : v_jalr (getr regs 1) 0 = getr regs 1);
  apply (fin_post (ms_regs msx) (ms_mem msx) _ X' ret);
  [ apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
  | exact HKf | exact HPf
  | apply tbn_tTB; rs_lens X'; eapply (kleaf_tbn Ex _ _ X X' r _ _ Hr8 HXn);
    [ mvl; first [exact HXl | rewrite HXl; reflexivity | lia]
    | exact RH | cbn [ew ewset extK Nat.eqb]; exact U8 | exact RE | cbn [ew ewset extK Nat.eqb]; exact U19
    | unfold cws_ok; repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.c_val YP09.c_off Z.of_N]; first [clear - Hr8; lia | lia]
    | unfold cws_ok; repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.c_val YP09.c_off Z.of_N]; first [clear - Hr8; lia | lia]
    | vm_compute; reflexivity | vm_compute; reflexivity | | ]
  | apply apres_of;
    [ rewrite Q2, U2; replace (spZ regs - 112 + 112) with (spZ regs) by lia; apply Z_to_bv_bv_unsigned
    | rewrite Q3; exact E3 | rewrite Q4; exact E4
    | rewrite Q8; ekr; reflexivity | rewrite Q9; ekr; reflexivity | rewrite Q18; ekr; reflexivity
    | rewrite Q19; ekr; reflexivity | rewrite Q20; ekr; reflexivity | rewrite Q21; ekr; reflexivity
    | rewrite Q22; ekr; reflexivity | rewrite Q23; ekr; reflexivity | rewrite Q24; ekr; reflexivity
    | rewrite Q25; ekr; reflexivity | rewrite Q26; ekr; reflexivity | rewrite Q27; ekr; reflexivity ]
  | rewrite Ra0; reflexivity
  | ] end.
Lemma k6 : forall regs' m md r f X,
  0 <= r < disco_table_c.n_of T -> disco_table_c.find_res T (disco_table_c.s_mac G) r ->
  f = (reac_disco_table_observe.cR T G r || reac_disco_table_observe.cD T G r || reac_disco_table_observe.cS T G r ||
      reac_disco_table_observe.cF T G r || reac_disco_table_observe.cC T G r)%bool ->
  reac_disco_table_observe.kF T G now r = X ->
  disco_table_c.u_at X 392 4 = disco_table_c.seq_of T ->
  disco_table_c.u_at X (48 * r + 24) 4 = disco_table_c.u_at T (48 * r + 24) 4 ->
  tJ m md -> tKP m -> tPR m -> tTB m X -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 19 = w64 (t + 48 * r) ->
  getr regs' 22 = w64 SB -> getr regs' 5 = Z_to_bv 64 ow -> getr regs' 14 = Z_to_bv 64 (Z.b2z f) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x54f0)) m (seg_rom SEGS)) md) tQ.
Proof.
intros regs' m md r f X Hr FI Hf HXd Xseq Xown HJ HK HP HX HSV HOW Hsp R3 R4 R8 R19 R22 R5 R14.
rs_hide_all. apply rs_hide in Rnow.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (Hr8 : 0 <= r < 8) by (unfold disco_table_c.tbl_T1 in HT1; lia).
assert (R14' : bv_unsigned (getr regs' 14) <= 1)
  by (rewrite R14; destruct f; cbn [Z.b2z]; rewrite unsigned_lit_small by lia; lia).
destruct (kst6_ok 0x54f0 regs' m X r HK HP HX HSV HOW Hr8 Hsp R8 R19 R22 R14') as [HS SHOK].
pose proof (tTB_tbn m X HX) as HXn.
assert (HO : forall a, 0 <= a < 2 ^ 64 -> ~ WK r a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m a) by reflexivity.
assert (HXl : length X = 400%nat) by exact (proj2 HX).
remember (EK regs' X r) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Rt : 0 <= t < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia).
assert (U8 : bv_unsigned (ew E 8) = t)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl), R8;
      apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = t + 48 * r)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), R19;
      apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 112)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Hsp).
assert (E3 : ew E 3 = getr regs 3)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs 4)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 4 4%bv eq_refl); exact R4).
assert (E5 : ew E 5 = Z_to_bv 64 ow)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 5 5%bv eq_refl); exact R5).
assert (E14 : ew E 14 = Z_to_bv 64 (Z.b2z f))
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 14 14%bv eq_refl); exact R14).
ekall HE.
paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
destruct (run_mem _ _ r m m _ Hr8 HFr HG ltac:(kwin U8 U19) HK HP HO) as (HK1 & HP1 & HO1). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite (br_ow _ ow Row ltac:(cbn [ew ewset extK Nat.eqb]; exact E5)) in Hc. apply Z.eqb_eq in Hc. rename Hc into Hw0.
  paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite (br_flag _ f ltac:(cbn [ew ewset extK Nat.eqb]; exact E14)) in Hc. apply negb_true_iff in Hc.
    paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    kfin X X r 0 HO3 HK3 HP3 HXn HXl Hr8 U8 U19 U2 E3 E4.
    * intros j Hj Hw. split; [apply (mbyte_of_aview SEGS); apply HO3; [lia | exact Hw] | reflexivity].
    * kchunks.
    * apply (k6_mod r f Hr FI Hf X 0). rewrite Hc.
      unfold reac_disco_table_observe.kG. rewrite HXd. unfold reac_disco_table_observe.cO. rewrite Hw0. reflexivity.
  + rewrite (br_flag _ f ltac:(cbn [ew ewset extK Nat.eqb]; exact E14)) in Hc. apply negb_false_iff in Hc.
    paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    kfin X (disco_table_c.upd X 392 (Z_to_le_bytes 4 (disco_table_c.seq_of T + 1))) r 1 HO3 HK3 HP3 HXn HXl Hr8 U8 U19 U2 E3 E4.
    * intros j Hj Hw. split; [apply (mbyte_of_aview SEGS); apply HO3; [lia | exact Hw] |].
      rewrite nth_upd_out; [reflexivity | lia | mvl; lia | rewrite HXl; lia | mvl; unfold WK in Hw; first [clear - Hw Hj; LiaTwx2.zify_noeuclid; xlia zchecker | rlia]].
    * kchunks.
      rewrite (seq_val _ 48 (disco_table_c.u_at X 392 4)) by (first [cbn [ew ewset extK Nat.eqb]; exact EQ48 | apply reac_disco_table_observe.u32_range]).
      rewrite Xseq. rewrite (OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.Z_to_le_bytes_mod 4 _ 32) by lia.
      apply reac_disco_table_observe.mf_sub_upd_at; mvl; lia.
    * apply (k6_mod r f Hr FI Hf _ 1). rewrite Hc.
      unfold reac_disco_table_observe.kG. rewrite HXd. unfold reac_disco_table_observe.cO. rewrite Hw0. reflexivity.
- rewrite (br_ow _ ow Row ltac:(cbn [ew ewset extK Nat.eqb]; exact E5)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hw0.
  paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  assert (Ru : 0 <= disco_table_c.u_at X (48 * r + 24) 4 < 2 ^ 32) by apply reac_disco_table_observe.u32_range.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite (br_s32z _ 56 _ ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ56) Ru) in Hc. apply Z.eqb_eq in Hc. rename Hc into Ho0.
    paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    kfin X (disco_table_c.upd (disco_table_c.upd X (48 * r + 24) (Z_to_le_bytes 4 1)) 392
           (Z_to_le_bytes 4 (disco_table_c.seq_of T + 1))) r 1 HO3 HK3 HP3 HXn HXl Hr8 U8 U19 U2 E3 E4.
    * intros j Hj Hw. split; [apply (mbyte_of_aview SEGS); apply HO3; [lia | exact Hw] |].
      rewrite nth_upd_out; [| lia | mvl; lia | mvl; rewrite ?HXl; lia | mvl; unfold WK in Hw; first [clear - Hw Hj; LiaTwx2.zify_noeuclid; xlia zchecker | rlia]].
      rewrite nth_upd_out; [reflexivity | lia | mvl; lia | rewrite HXl; lia | mvl; unfold WK in Hw; first [clear - Hw Hj; LiaTwx2.zify_noeuclid; xlia zchecker | rlia]].
    * kchunks.
      -- rewrite (seq_val _ 48 (disco_table_c.u_at X 392 4)) by (first [cbn [ew ewset extK Nat.eqb]; exact EQ48 | apply reac_disco_table_observe.u32_range]).
         rewrite Xseq. rewrite (OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.Z_to_le_bytes_mod 4 _ 32) by lia.
         apply reac_disco_table_observe.mf_sub_upd_at; mvl; lia.
      -- cbn [sv_denot]. rewrite unsigned_lit_small by lia. change (8 * 4) with 32. rewrite Z.mod_small by lia.
         msub. apply reac_disco_table_observe.mf_sub_upd_at; mvl; lia.
    * apply (k6_mod r f Hr FI Hf _ 1).
      assert (HcO : reac_disco_table_observe.cO T ow r = true).
      { unfold reac_disco_table_observe.cO, disco_table_c.owned_of, disco_table_c.s32_at. rewrite <- Xown, Ho0.
        apply andb_true_iff. split; [apply negb_true_iff, Z.eqb_neq; exact Hw0 | reflexivity]. }
      rewrite HcO, orb_true_r. unfold reac_disco_table_observe.kG. rewrite HcO, HXd. reflexivity.
  + rewrite (br_s32z _ 56 _ ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ56) Ru) in Hc. apply Z.eqb_neq in Hc. rename Hc into Ho0.
    assert (HcO : reac_disco_table_observe.cO T ow r = false).
    { unfold reac_disco_table_observe.cO, disco_table_c.owned_of, disco_table_c.s32_at. rewrite <- Xown.
      apply andb_false_iff. right. apply Z.eqb_neq. unfold bv_swrap, bv_wrap.
      change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
      destruct (Z.ltb_spec (disco_table_c.u_at X (48 * r + 24) 4) (2 ^ 31)).
      - rewrite Z.mod_small by rlia. rlia.
      - rewrite <- (Z.mod_add _ (-1) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia. }
    paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * rewrite (br_flag _ f ltac:(cbn [ew ewset extK Nat.eqb]; exact E14)) in Hc. apply negb_true_iff in Hc.
      paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
      destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK3 HP3 HO3) as (HK4 & HP4 & HO4). clear HF HFr HG.
      kfin X X r 0 HO4 HK4 HP4 HXn HXl Hr8 U8 U19 U2 E3 E4.
      -- intros j Hj Hw. split; [apply (mbyte_of_aview SEGS); apply HO4; [lia | exact Hw] | reflexivity].
      -- kchunks.
      -- apply (k6_mod r f Hr FI Hf X 0). rewrite Hc, HcO. cbn [orb].
         unfold reac_disco_table_observe.kG. rewrite HcO, HXd. reflexivity.
    * rewrite (br_flag _ f ltac:(cbn [ew ewset extK Nat.eqb]; exact E14)) in Hc. apply negb_false_iff in Hc.
      paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
      destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK3 HP3 HO3) as (HK4 & HP4 & HO4). clear HF HFr HG.
      kfin X (disco_table_c.upd X 392 (Z_to_le_bytes 4 (disco_table_c.seq_of T + 1))) r 1 HO4 HK4 HP4 HXn HXl Hr8 U8 U19 U2 E3 E4.
      -- intros j Hj Hw. split; [apply (mbyte_of_aview SEGS); apply HO4; [lia | exact Hw] |].
         rewrite nth_upd_out; [reflexivity | lia | mvl; lia | rewrite HXl; lia | mvl; unfold WK in Hw; first [clear - Hw Hj; LiaTwx2.zify_noeuclid; xlia zchecker | rlia]].
      -- kchunks.
         rewrite (seq_val _ 48 (disco_table_c.u_at X 392 4)) by (first [cbn [ew ewset extK Nat.eqb]; exact EQ48 | apply reac_disco_table_observe.u32_range]).
         rewrite Xseq. rewrite (OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.Z_to_le_bytes_mod 4 _ 32) by lia.
         apply reac_disco_table_observe.mf_sub_upd_at; mvl; lia.
      -- apply (k6_mod r f Hr FI Hf _ 1). rewrite Hc. cbn [orb].
         unfold reac_disco_table_observe.kG. rewrite HcO, HXd. reflexivity.
Qed.
Let RUNTO := paj_run_to B LAWS.
Ltac urng := lazymatch goal with |- 0 <= disco_table_c.u_at ?bs ?o ?w < _ =>
  let Ur := fresh "Ur" in pose proof (reac_disco_table_observe.u_at_range bs o w) as Ur; cbn in Ur; lia end.
Ltac bz Hc :=
  rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in Hc;
  repeat match type of Hc with
  | context [U ?Ex (SExt true 32 (SOff ?n 0))] =>
      lazymatch goal with Heq : ew _ n = Z_to_bv 64 ?u |- _ =>
        rewrite (U_sx Ex n u ltac:(cbn [ew ewset extK Nat.eqb]; exact Heq) ltac:(apply reac_disco_table_observe.u32_range)) in Hc end
  | context [U ?Ex (SOff ?n 0)] =>
      lazymatch goal with Heq : ew _ n = Z_to_bv 64 ?u |- _ =>
        rewrite (U_atom Ex n u ltac:(cbn [ew ewset extK Nat.eqb]; exact Heq) ltac:(urng)) in Hc end
  | context [U ?Ex (SLit ?z)] => rewrite (U_lit Ex z ltac:(lia)) in Hc
  end;
  rewrite ?sx_eqb, ?sx_ltb in Hc by (apply reac_disco_table_observe.u32_range);
  rewrite ?sx_eqk in Hc by (first [apply reac_disco_table_observe.u32_range | lia]);
  rewrite ?negb_true_iff, ?negb_false_iff in Hc;
  first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc].
Ltac mflag := unfold reac_disco_table_observe.cR, reac_disco_table_observe.cD, reac_disco_table_observe.cS,
  reac_disco_table_observe.cF, reac_disco_table_observe.cC, disco_table_c.role_of_e, disco_table_c.s_role,
  disco_table_c.s32_at, disco_table_c.hd_of, disco_table_c.din_of, disco_table_c.dout_of,
  reac_disco_table_observe_c.slots_of, reac_disco_table_observe_c.fam_of, reac_disco_table_observe_c.ch_of,
  disco_table_c.s_hd, disco_table_c.s_din, disco_table_c.s_dout, disco_table_c.s_slots, disco_table_c.s_fam,
  disco_table_c.s_ch;
  rewrite ?s32_eqb by (apply reac_disco_table_observe.u32_range);
  rewrite ?s32_eqk by (first [apply reac_disco_table_observe.u32_range | lia]);
  repeat match goal with
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end;
  cbn [negb andb orb]; first [reflexivity | exfalso; rlia].
Ltac xfld HXd := rewrite <- HXd; unfold disco_table_c.seq_of, disco_table_c.u_at; f_equal;
  unfold reac_disco_table_observe.kF, reac_disco_table_observe.kE, reac_disco_table_observe.kD,
    reac_disco_table_observe.kC, reac_disco_table_observe.kB, reac_disco_table_observe.kA;
  rs_lens_goal; repeat first [ lazymatch goal with |- context [disco_table_c.sub (disco_table_c.upd _ _ _) _ _] => rewrite rs_sub_upd_other by (mvl; first [kprune; lia | lia]) end
    | lazymatch goal with |- context [disco_table_c.sub (if _ then _ else _) _ _] => rewrite rs_sub_if_other by (mvl; first [kprune; lia | lia]) end | rewrite if_same_l | rewrite sub_if_d ];
  reflexivity.
Ltac kch := first
  [ lazymatch goal with |- context [bv_unsigned (sv_denot ?Ex (SExt true 32 (SOff ?n 0))) mod _] =>
      lazymatch goal with Heq : ew _ n = Z_to_bv 64 ?u |- _ =>
        rewrite (sx_val Ex n u ltac:(cbn [ew ewset extK Nat.eqb]; exact Heq) ltac:(apply reac_disco_table_observe.u32_range)) end end;
    rewrite reac_disco_table_observe.le_sub by (mvl; first [kprune; lia | lia])
  | cbn [sv_denot ew ewset extK Nat.eqb]; ekr; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    lazymatch goal with |- context [bv_unsigned (Z_to_bv 64 (disco_table_c.u_at ?bs ?o ?w))] =>
      let Ur := fresh "Ur" in
      pose proof (reac_disco_table_observe.u_at_range bs o w) as Ur; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ur;
      rewrite (unsigned_lit_small (disco_table_c.u_at bs o w)) by (clear - Ur; lia); rewrite (Z.mod_small (disco_table_c.u_at bs o w)) by (clear - Ur; lia);
      rewrite reac_disco_table_observe.le_sub by (mvl; first [kprune; lia | lia]) end
  | cbn [sv_denot]; lazymatch goal with |- context [bv_unsigned (Z_to_bv 64 ?z) mod _] =>
      rewrite (unsigned_lit_small z) by lia; rewrite (Z.mod_small z) by (split; [lia | exact eq_refl]); cbn [Z_to_le_bytes] end
  | cbn [sv_denot ew ewset extK Nat.eqb]; ekr; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    rewrite (unsigned_lit_small now) by (unfold rs_hold in Rnow; lia);
    rewrite (Z.mod_small now) by (split; [unfold rs_hold in Rnow; lia | exact (proj2 Rnow)]) ];
  msub; first [reflexivity | apply reac_disco_table_observe.mf_sub_upd_at; mvl; first [kprune; lia | lia]].
Ltac kchs := cbn [cws flat_map YP09.c_val YP09.c_off app]; nnorm;
  repeat apply Forall_cons; try apply Forall_nil; cbv beta iota; rewrite ?Z.add_0_l; try kch.
Ltac nout HXl Hw := repeat (rewrite nth_upd_out;
  [| lia | mvl; first [lia | rewrite HXl; lia] | mvl; first [rewrite HXl; lia | lia] | mvl; unfold WK in Hw; first [lazymatch goal with Hj : 0 <= _ < 400 |- _ => clear - Hw Hj; LiaTwx2.zify_noeuclid; xlia zchecker end | rlia]]);
  reflexivity.
Ltac kgoal HSTK HOf HKf HPf HSV HOW U2 :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- ?g =>
    lazymatch g with
    | 0 <= _ < _ => assumption
    | disco_table_c.find_res _ _ _ => assumption
    | tJ _ _ => exact HJ
    | tKP _ => exact HKf
    | tPR _ => exact HPf
    | tSV _ => exact (proj1 (sv_keep _ _ (fun a Ha => HOf a (proj1 (HSTK a Ha)) (proj2 (HSTK a Ha))) HSV HOW))
    | tOW _ => exact (proj2 (sv_keep _ _ (fun a Ha => HOf a (proj1 (HSTK a Ha)) (proj2 (HSTK a Ha))) HSV HOW))
    | spZ _ = _ =>
      let Q := fresh "Q" in prreg HS (2%bv : bv 5) Q;
      change (spZ (ms_regs msx)) with (bv_unsigned (getr (ms_regs msx) 2)); rewrite Q; exact U2
    | getr _ ?q = _ =>
      let Q := fresh "Q" in prreg HS q Q; rewrite Q; first [assumption | reflexivity | ekr; reflexivity]
    end
  end.
Ltac ktb X X' r HOf HXn HXl Hr8 U8 U19 :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) |- tTB _ _ =>
  let RH := fresh "RH" in let RE := fresh "RE" in
  let rH := eval vm_compute in (nth 1 (ss_mem ss) (stack_region 0)) in
  let rE := eval vm_compute in (nth 2 (ss_mem ss) (stack_region 0)) in
  pose proof (st_ok_pi_region_nth Ex ss (restrict (w_H W) msx) 1 rH HS ltac:(vm_compute; reflexivity)) as RH;
  pose proof (st_ok_pi_region_nth Ex ss (restrict (w_H W) msx) 2 rE HS ltac:(vm_compute; reflexivity)) as RE;
  cbn [ms_mem restrict] in RH, RE;
  apply tbn_tTB; rs_lens X'; eapply (kleaf_tbn Ex _ _ X X' r _ _ Hr8 HXn);
  [ mvl; first [exact HXl | rewrite HXl; reflexivity | lia]
  | exact RH | cbn [ew ewset extK Nat.eqb]; exact U8 | exact RE | cbn [ew ewset extK Nat.eqb]; exact U19
  | unfold cws_ok; repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.c_val YP09.c_off Z.of_N]; first [clear - Hr8; lia | lia]
  | unfold cws_ok; repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.c_val YP09.c_off Z.of_N]; first [clear - Hr8; lia | lia]
  | vm_compute; reflexivity | vm_compute; reflexivity
  | let j := fresh "j" in let Hj := fresh "Hj" in let Hw := fresh "Hw" in
    intros j Hj Hw; split; [apply (mbyte_of_aview SEGS); apply HOf; [lia | exact Hw] | nout HXl Hw]
  | kchs ] end.
Ltac knx NEXT X X' r f' HSTK HOf HKf HPf HXn HXl HSV HOW Hr8 U8 U19 U2 :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) |- _ =>
  pmkst HS;
  apply (NEXT (ms_regs msx) (ms_mem msx) _ r f' X'); try kgoal HSTK HOf HKf HPf HSV HOW U2;
  try ktb X X' r HOf HXn HXl Hr8 U8 U19 end.
Lemma stk_nwk : forall r a, 0 <= r < 8 -> spZ regs - 112 <= a < spZ regs -> 0 <= a < 2 ^ 64 /\ ~ WK r a.
Proof.
intros r a Hr Ha. pose proof stk_lo as [Hlo_ Hhi_]. pose proof Htside as Hts_. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hlo_, Hts_. split; [lia | unfold WK; lia].
Qed.
Lemma k5 : forall regs' m md r f X,
  0 <= r < disco_table_c.n_of T -> disco_table_c.find_res T (disco_table_c.s_mac G) r ->
  f = (reac_disco_table_observe.cR T G r || reac_disco_table_observe.cD T G r || reac_disco_table_observe.cS T G r ||
      reac_disco_table_observe.cF T G r)%bool ->
  reac_disco_table_observe.kE T G now r = X ->
  tJ m md -> tKP m -> tPR m -> tTB m X -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 18 = w64 s -> getr regs' 19 = w64 (t + 48 * r) ->
  getr regs' 22 = w64 SB -> getr regs' 5 = Z_to_bv 64 ow -> getr regs' 14 = Z_to_bv 64 (Z.b2z f) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x54ac)) m (seg_rom SEGS)) md) tQ.
Proof.
intros regs' m md r f X Hr FI Hf HXd HJ HK HP HX HSV HOW Hsp R3 R4 R8 R18 R19 R22 R5 R14.
rs_hide_all. apply rs_hide in Rnow.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (Hr8 : 0 <= r < 8) by (unfold disco_table_c.tbl_T1 in HT1; lia).
destruct (kst_ok 0x54ac regs' m X r HK HP HX HSV HOW Hr8 Hsp R8 R18 R19 R22) as [HS SHOK].
pose proof (tTB_tbn m X HX) as HXn.
assert (HO : forall a, 0 <= a < 2 ^ 64 -> ~ WK r a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m a) by reflexivity.
assert (HXl : length X = 400%nat) by exact (proj2 HX).
pose proof (fun a => stk_nwk r a Hr8) as HSTK.
assert (Xseq : disco_table_c.u_at X 392 4 = disco_table_c.seq_of T) by xfld HXd.
assert (Xown : disco_table_c.u_at X (48 * r + 24) 4 = disco_table_c.u_at T (48 * r + 24) 4) by xfld HXd.
assert (Xch : disco_table_c.u_at X (48 * r + 20) 4 = disco_table_c.u_at T (48 * r + 20) 4) by xfld HXd.
remember (EK regs' X r) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Rt : 0 <= t < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia).
assert (U8 : bv_unsigned (ew E 8) = t)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl), R8;
      apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = t + 48 * r)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), R19;
      apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 112)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Hsp).
assert (E3 : ew E 3 = getr regs 3)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs 4)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 4 4%bv eq_refl); exact R4).
assert (E5 : ew E 5 = Z_to_bv 64 ow)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 5 5%bv eq_refl); exact R5).
assert (E8 : ew E 8 = Z_to_bv 64 t)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl); exact R8).
assert (E14 : ew E 14 = Z_to_bv 64 (Z.b2z f))
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 14 14%bv eq_refl); exact R14).
assert (E19 : ew E 19 = Z_to_bv 64 (t + 48 * r))
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = Z_to_bv 64 SB)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl); exact R22).
ekall HE.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x54f0; [awrK U8 U19 Hr8|].
destruct (run_mem _ _ r m m _ Hr8 HFr HG ltac:(kwin U8 U19) HK HP HO) as (HK1 & HP1 & HO1). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- bz Hc. rewrite Xch in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x54f0; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  knx k6 X X r f HSTK HO2 HK2 HP2 HXn HXl HSV HOW Hr8 U8 U19 U2.
  + rewrite Hf. assert (Hcc : reac_disco_table_observe.cC T G r = false) by (first [clear - Hc; mflag | mflag]). rewrite Hcc, orb_false_r. reflexivity.
  + unfold reac_disco_table_observe.kF. rewrite HXd. assert (Hcc : reac_disco_table_observe.cC T G r = false) by (first [clear - Hc; mflag | mflag]).
    rewrite Hcc. reflexivity.
  + exact Xseq.
  + exact Xown.
- bz Hc. rewrite Xch in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x54f0; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  knx k6 X (disco_table_c.upd X (48 * r + 20) (disco_table_c.sub G 20 4)) r true HSTK HO2 HK2 HP2 HXn HXl HSV HOW Hr8 U8 U19 U2.
  + assert (Hcc : reac_disco_table_observe.cC T G r = true) by (first [clear - Hc; mflag | mflag]). rewrite Hcc, orb_true_r. reflexivity.
  + unfold reac_disco_table_observe.kF. rewrite HXd. assert (Hcc : reac_disco_table_observe.cC T G r = true) by (first [clear - Hc; mflag | mflag]).
    rewrite Hcc. reflexivity.
  + unfold disco_table_c.u_at. msub. exact Xseq.
  + unfold disco_table_c.u_at. msub. exact Xown.
Qed.
Ltac kenv regs' r HE R3 R4 R5 R8 R14 R18 R19 R22 Hsp :=
  let E := lazymatch type of HE with ?E = _ => E end in
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env);
  assert (U8 : bv_unsigned (ew E 8) = t)
    by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl), R8;
        apply unsigned_lit_small; unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia);
  assert (U19 : bv_unsigned (ew E 19) = t + 48 * r)
    by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), R19;
        apply unsigned_lit_small; unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia);
  assert (U2 : bv_unsigned (ew E 2) = spZ regs - 112)
    by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Hsp);
  assert (E3 : ew E 3 = getr regs 3)
    by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 3 3%bv eq_refl); exact R3);
  assert (E4 : ew E 4 = getr regs 4)
    by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 4 4%bv eq_refl); exact R4);
  assert (E5 : ew E 5 = Z_to_bv 64 ow)
    by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 5 5%bv eq_refl); exact R5);
  assert (E8 : ew E 8 = Z_to_bv 64 t)
    by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl); exact R8);
  assert (E14 : ew E 14 = getr regs' 14)
    by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ 14 14%bv eq_refl));
  rewrite R14 in E14;
  assert (E18 : ew E 18 = Z_to_bv 64 s)
    by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 18 18%bv eq_refl); exact R18);
  assert (E19 : ew E 19 = Z_to_bv 64 (t + 48 * r))
    by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl); exact R19);
  assert (E22 : ew E 22 = Z_to_bv 64 SB)
    by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl); exact R22);
  ekall HE.
Ltac kstart :=
  pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs.
Lemma k4 : forall regs' m md r f X,
  0 <= r < disco_table_c.n_of T -> disco_table_c.find_res T (disco_table_c.s_mac G) r ->
  f = (reac_disco_table_observe.cR T G r || reac_disco_table_observe.cD T G r || reac_disco_table_observe.cS T G r)%bool ->
  reac_disco_table_observe.kD T G now r = X ->
  tJ m md -> tKP m -> tPR m -> tTB m X -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 18 = w64 s -> getr regs' 19 = w64 (t + 48 * r) ->
  getr regs' 22 = w64 SB -> getr regs' 5 = Z_to_bv 64 ow -> getr regs' 14 = Z_to_bv 64 (Z.b2z f) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x5464)) m (seg_rom SEGS)) md) tQ.
Proof.
intros regs' m md r f X Hr FI Hf HXd HJ HK HP HX HSV HOW Hsp R3 R4 R8 R18 R19 R22 R5 R14.
rs_hide_all. apply rs_hide in Rnow.
kstart.
assert (Hr8 : 0 <= r < 8) by (unfold disco_table_c.tbl_T1 in HT1; lia).
destruct (kst_ok 0x5464 regs' m X r HK HP HX HSV HOW Hr8 Hsp R8 R18 R19 R22) as [HS SHOK].
pose proof (tTB_tbn m X HX) as HXn.
assert (HO : forall a, 0 <= a < 2 ^ 64 -> ~ WK r a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m a) by reflexivity.
assert (HXl : length X = 400%nat) by exact (proj2 HX).
pose proof (fun a => stk_nwk r a Hr8) as HSTK.
assert (XF : disco_table_c.u_at X (48 * r + 15) 1 = disco_table_c.u_at T (48 * r + 15) 1) by xfld HXd.
remember (EK regs' X r) as E eqn:HE.
kenv regs' r HE R3 R4 R5 R8 R14 R18 R19 R22 Hsp.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x54ac; [awrK U8 U19 Hr8|].
destruct (run_mem _ _ r m m _ Hr8 HFr HG ltac:(kwin U8 U19) HK HP HO) as (HK1 & HP1 & HO1). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- bz Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x54ac; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  assert (Hcc : reac_disco_table_observe.cF T G r = false) by (first [clear - Hc; mflag | mflag]).
  knx k5 X X r f HSTK HO2 HK2 HP2 HXn HXl HSV HOW Hr8 U8 U19 U2.
  + rewrite Hf, Hcc, orb_false_r. reflexivity.
  + unfold reac_disco_table_observe.kE. rewrite HXd, Hcc. reflexivity.
- bz Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x54ac; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + bz Hc0. rewrite XF in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x54ac; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    assert (Hcc : reac_disco_table_observe.cF T G r = false) by (first [clear - Hc Hc0; mflag | mflag]).
    knx k5 X X r f HSTK HO3 HK3 HP3 HXn HXl HSV HOW Hr8 U8 U19 U2.
    * rewrite Hf, Hcc, orb_false_r. reflexivity.
    * unfold reac_disco_table_observe.kE. rewrite HXd, Hcc. reflexivity.
  + bz Hc0. rewrite XF in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x54ac; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    assert (Hcc : reac_disco_table_observe.cF T G r = true) by (first [clear - Hc Hc0; mflag | mflag]).
    knx k5 X (disco_table_c.upd X (48 * r + 15) (disco_table_c.sub G 15 1)) r true HSTK HO3 HK3 HP3 HXn HXl HSV HOW Hr8 U8 U19 U2.
    * rewrite Hcc, orb_true_r. reflexivity.
    * unfold reac_disco_table_observe.kE. rewrite HXd, Hcc. reflexivity.
Qed.
Lemma k3 : forall regs' m md r f X,
  0 <= r < disco_table_c.n_of T -> disco_table_c.find_res T (disco_table_c.s_mac G) r ->
  f = (reac_disco_table_observe.cR T G r || reac_disco_table_observe.cD T G r)%bool ->
  reac_disco_table_observe.kC T G now r = X ->
  tJ m md -> tKP m -> tPR m -> tTB m X -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 18 = w64 s -> getr regs' 19 = w64 (t + 48 * r) ->
  getr regs' 22 = w64 SB -> getr regs' 5 = Z_to_bv 64 ow -> getr regs' 14 = Z_to_bv 64 (Z.b2z f) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x541c)) m (seg_rom SEGS)) md) tQ.
Proof.
intros regs' m md r f X Hr FI Hf HXd HJ HK HP HX HSV HOW Hsp R3 R4 R8 R18 R19 R22 R5 R14.
rs_hide_all. apply rs_hide in Rnow.
kstart.
assert (Hr8 : 0 <= r < 8) by (unfold disco_table_c.tbl_T1 in HT1; lia).
destruct (kst_ok 0x541c regs' m X r HK HP HX HSV HOW Hr8 Hsp R8 R18 R19 R22) as [HS SHOK].
pose proof (tTB_tbn m X HX) as HXn.
assert (HO : forall a, 0 <= a < 2 ^ 64 -> ~ WK r a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m a) by reflexivity.
assert (HXl : length X = 400%nat) by exact (proj2 HX).
pose proof (fun a => stk_nwk r a Hr8) as HSTK.
assert (XF : disco_table_c.u_at X (48 * r + 16) 1 = disco_table_c.u_at T (48 * r + 16) 1) by xfld HXd.
remember (EK regs' X r) as E eqn:HE.
kenv regs' r HE R3 R4 R5 R8 R14 R18 R19 R22 Hsp.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5464; [awrK U8 U19 Hr8|].
destruct (run_mem _ _ r m m _ Hr8 HFr HG ltac:(kwin U8 U19) HK HP HO) as (HK1 & HP1 & HO1). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- bz Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5464; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  assert (Hcc : reac_disco_table_observe.cS T G r = false) by (first [clear - Hc; mflag | mflag]).
  knx k4 X X r f HSTK HO2 HK2 HP2 HXn HXl HSV HOW Hr8 U8 U19 U2.
  + rewrite Hf, Hcc, orb_false_r. reflexivity.
  + unfold reac_disco_table_observe.kD. rewrite HXd, Hcc. reflexivity.
- bz Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5464; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + bz Hc0. rewrite XF in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5464; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    assert (Hcc : reac_disco_table_observe.cS T G r = false) by (first [clear - Hc Hc0; mflag | mflag]).
    knx k4 X X r f HSTK HO3 HK3 HP3 HXn HXl HSV HOW Hr8 U8 U19 U2.
    * rewrite Hf, Hcc, orb_false_r. reflexivity.
    * unfold reac_disco_table_observe.kD. rewrite HXd, Hcc. reflexivity.
  + bz Hc0. rewrite XF in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5464; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    assert (Hcc : reac_disco_table_observe.cS T G r = true) by (first [clear - Hc Hc0; mflag | mflag]).
    knx k4 X (disco_table_c.upd X (48 * r + 16) (disco_table_c.sub G 16 1)) r true HSTK HO3 HK3 HP3 HXn HXl HSV HOW Hr8 U8 U19 U2.
    * rewrite Hcc, orb_true_r. reflexivity.
    * unfold reac_disco_table_observe.kD. rewrite HXd, Hcc. reflexivity.
Qed.
Lemma k2 : forall regs' m md r f X,
  0 <= r < disco_table_c.n_of T -> disco_table_c.find_res T (disco_table_c.s_mac G) r ->
  f = reac_disco_table_observe.cR T G r ->
  reac_disco_table_observe.kB T G now r = X ->
  tJ m md -> tKP m -> tPR m -> tTB m X -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 18 = w64 s -> getr regs' 19 = w64 (t + 48 * r) ->
  getr regs' 22 = w64 SB -> getr regs' 5 = Z_to_bv 64 ow -> getr regs' 14 = Z_to_bv 64 (Z.b2z f) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x5310)) m (seg_rom SEGS)) md) tQ.
Proof.
intros regs' m md r f X Hr FI Hf HXd HJ HK HP HX HSV HOW Hsp R3 R4 R8 R18 R19 R22 R5 R14.
rs_hide_all. apply rs_hide in Rnow.
kstart.
assert (Hr8 : 0 <= r < 8) by (unfold disco_table_c.tbl_T1 in HT1; lia).
destruct (kst_ok 0x5310 regs' m X r HK HP HX HSV HOW Hr8 Hsp R8 R18 R19 R22) as [HS SHOK].
pose proof (tTB_tbn m X HX) as HXn.
assert (HO : forall a, 0 <= a < 2 ^ 64 -> ~ WK r a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m a) by reflexivity.
assert (HXl : length X = 400%nat) by exact (proj2 HX).
pose proof (fun a => stk_nwk r a Hr8) as HSTK.
assert (XF12 : disco_table_c.u_at X (48 * r + 12) 1 = disco_table_c.u_at T (48 * r + 12) 1) by xfld HXd.
assert (XF13 : disco_table_c.u_at X (48 * r + 13) 1 = disco_table_c.u_at T (48 * r + 13) 1) by xfld HXd.
assert (XF14 : disco_table_c.u_at X (48 * r + 14) 1 = disco_table_c.u_at T (48 * r + 14) 1) by xfld HXd.
remember (EK regs' X r) as E eqn:HE.
kenv regs' r HE R3 R4 R5 R8 R14 R18 R19 R22 Hsp.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x541c; [awrK U8 U19 Hr8|].
destruct (run_mem _ _ r m m _ Hr8 HFr HG ltac:(kwin U8 U19) HK HP HO) as (HK1 & HP1 & HO1). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- bz Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x541c; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  assert (Hcc : reac_disco_table_observe.cD T G r = false) by (first [clear - Hc; mflag | mflag]).
  knx k3 X X r f HSTK HO2 HK2 HP2 HXn HXl HSV HOW Hr8 U8 U19 U2.
  + rewrite Hf, Hcc, orb_false_r. reflexivity.
  + unfold reac_disco_table_observe.kC. rewrite HXd, Hcc. reflexivity.
- bz Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x541c; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + bz Hc0. rewrite XF12 in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x541c; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    assert (Hcc : reac_disco_table_observe.cD T G r = true) by (first [clear - Hc Hc0; mflag | mflag]).
    knx k3 X (disco_table_c.upd (disco_table_c.upd (disco_table_c.upd X (48 * r + 12) [Z_to_bv 8 1]) (48 * r + 13) (disco_table_c.sub G 13 1)) (48 * r + 14) (disco_table_c.sub G 14 1)) r true HSTK HO3 HK3 HP3 HXn HXl HSV HOW Hr8 U8 U19 U2.
    * rewrite Hcc, orb_true_r. reflexivity.
    * unfold reac_disco_table_observe.kC. rewrite HXd, Hcc. reflexivity.
  + bz Hc0. rewrite XF12 in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x541c; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * bz Hc1. rewrite XF13 in Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x541c; [awrK U8 U19 Hr8|].
      destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK3 HP3 HO3) as (HK4 & HP4 & HO4). clear HF HFr HG.
      assert (Hcc : reac_disco_table_observe.cD T G r = true) by (first [clear - Hc Hc0 Hc1; mflag | mflag]).
      knx k3 X (disco_table_c.upd (disco_table_c.upd (disco_table_c.upd X (48 * r + 12) [Z_to_bv 8 1]) (48 * r + 13) (disco_table_c.sub G 13 1)) (48 * r + 14) (disco_table_c.sub G 14 1)) r true HSTK HO4 HK4 HP4 HXn HXl HSV HOW Hr8 U8 U19 U2.
      -- rewrite Hcc, orb_true_r. reflexivity.
      -- unfold reac_disco_table_observe.kC. rewrite HXd, Hcc. reflexivity.
    * bz Hc1. rewrite XF13 in Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x541c; [awrK U8 U19 Hr8|].
      destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK3 HP3 HO3) as (HK4 & HP4 & HO4). clear HF HFr HG.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- bz Hc2. rewrite XF14 in Hc2.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x541c; [awrK U8 U19 Hr8|].
         destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK4 HP4 HO4) as (HK5 & HP5 & HO5). clear HF HFr HG.
         assert (Hcc : reac_disco_table_observe.cD T G r = false) by (first [clear - Hc Hc0 Hc1 Hc2; mflag | mflag]).
         knx k3 X X r f HSTK HO5 HK5 HP5 HXn HXl HSV HOW Hr8 U8 U19 U2.
         ++ rewrite Hf, Hcc, orb_false_r. reflexivity.
         ++ unfold reac_disco_table_observe.kC. rewrite HXd, Hcc. reflexivity.
      -- bz Hc2. rewrite XF14 in Hc2.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x541c; [awrK U8 U19 Hr8|].
         destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK4 HP4 HO4) as (HK5 & HP5 & HO5). clear HF HFr HG.
         assert (Hcc : reac_disco_table_observe.cD T G r = true) by (first [clear - Hc Hc0 Hc1 Hc2; mflag | mflag]).
         knx k3 X (disco_table_c.upd (disco_table_c.upd (disco_table_c.upd X (48 * r + 12) [Z_to_bv 8 1]) (48 * r + 13) (disco_table_c.sub G 13 1)) (48 * r + 14) (disco_table_c.sub G 14 1)) r true HSTK HO5 HK5 HP5 HXn HXl HSV HOW Hr8 U8 U19 U2.
         ++ rewrite Hcc, orb_true_r. reflexivity.
         ++ unfold reac_disco_table_observe.kC. rewrite HXd, Hcc. reflexivity.
Qed.
Lemma k1 : forall r regs' m md,
  0 <= r < disco_table_c.n_of T -> disco_table_c.find_res T (disco_table_c.s_mac G) r ->
  tJ m md -> tKP m -> tPR m -> tTB m T -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 18 = w64 s -> getr regs' 19 = w64 (t + 48 * r) -> getr regs' 20 = w64 now ->
  getr regs' 22 = w64 SB ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x52a8)) m (seg_rom SEGS)) md) tQ.
Proof.
intros r regs' m md Hr FI HJ HK HP HX HSV HOW Hsp R3 R4 R8 R18 R19 R20 R22.
rs_hide_all. apply rs_hide in Rnow.
kstart.
assert (Hr8 : 0 <= r < 8) by (unfold disco_table_c.tbl_T1 in HT1; lia).
destruct (kst_ok 0x52a8 regs' m T r HK HP HX HSV HOW Hr8 Hsp R8 R18 R19 R22) as [HS SHOK].
pose proof (tTB_tbn m T HX) as HXn.
assert (HO : forall a, 0 <= a < 2 ^ 64 -> ~ WK r a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m a) by reflexivity.
assert (HXl : length T = 400%nat) by exact HTl.
pose proof (fun a => stk_nwk r a Hr8) as HSTK.
remember (EK regs' T r) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (U8 : bv_unsigned (ew E 8) = t)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl), R8;
      apply unsigned_lit_small; unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia).
assert (U19 : bv_unsigned (ew E 19) = t + 48 * r)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), R19;
      apply unsigned_lit_small; unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 112)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Hsp).
assert (E3 : ew E 3 = getr regs 3)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs 4)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 4 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 t)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 s)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (t + 48 * r))
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 now)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 20 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 SB)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl); exact R22).
ekq HE 32%nat EQ32.
ekall HE.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5310; [awrK U8 U19 Hr8|].
destruct (run_mem _ _ r m m _ Hr8 HFr HG ltac:(kwin U8 U19) HK HP HO) as (HK1 & HP1 & HO1). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- bz Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5310; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  assert (Hcc : reac_disco_table_observe.cR T G r = false) by (first [clear - Hc; mflag | mflag]).
  knx k2 T (disco_table_c.upd T (48 * r + 40) (Z_to_le_bytes 8 now)) r false HSTK HO2 HK2 HP2 HXn HXl HSV HOW Hr8 U8 U19 U2.
  + rewrite Hcc. reflexivity.
  + unfold reac_disco_table_observe.kB, reac_disco_table_observe.kA. rewrite Hcc. reflexivity.
- bz Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5310; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + bz Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5310; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    assert (Hcc : reac_disco_table_observe.cR T G r = false) by (first [clear - Hc Hc0; mflag | mflag]).
    knx k2 T (disco_table_c.upd T (48 * r + 40) (Z_to_le_bytes 8 now)) r false HSTK HO3 HK3 HP3 HXn HXl HSV HOW Hr8 U8 U19 U2.
    * rewrite Hcc. reflexivity.
    * unfold reac_disco_table_observe.kB, reac_disco_table_observe.kA. rewrite Hcc. reflexivity.
  + bz Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5310; [awrK U8 U19 Hr8|].
    destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK2 HP2 HO2) as (HK3 & HP3 & HO3). clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * bz Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5310; [awrK U8 U19 Hr8|].
      destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK3 HP3 HO3) as (HK4 & HP4 & HO4). clear HF HFr HG.
      assert (Hcc : reac_disco_table_observe.cR T G r = true) by (first [clear - Hc Hc0 Hc1; mflag | mflag]).
      knx k2 T (disco_table_c.upd (disco_table_c.upd T (48 * r + 40) (Z_to_le_bytes 8 now)) (48 * r + 8) (disco_table_c.sub G 8 4))
        r true HSTK HO4 HK4 HP4 HXn HXl HSV HOW Hr8 U8 U19 U2.
      -- rewrite Hcc. reflexivity.
      -- unfold reac_disco_table_observe.kB, reac_disco_table_observe.kA. rewrite Hcc. reflexivity.
    * bz Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5310; [awrK U8 U19 Hr8|].
      destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK3 HP3 HO3) as (HK4 & HP4 & HO4). clear HF HFr HG.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- bz Hc2.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5310; [awrK U8 U19 Hr8|].
         destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK4 HP4 HO4) as (HK5 & HP5 & HO5). clear HF HFr HG.
         assert (Hcc : reac_disco_table_observe.cR T G r = true) by (first [clear - Hc Hc0 Hc1 Hc2; mflag | mflag]).
         knx k2 T (disco_table_c.upd (disco_table_c.upd T (48 * r + 40) (Z_to_le_bytes 8 now)) (48 * r + 8) (disco_table_c.sub G 8 4))
           r true HSTK HO5 HK5 HP5 HXn HXl HSV HOW Hr8 U8 U19 U2.
         ++ rewrite Hcc. reflexivity.
         ++ unfold reac_disco_table_observe.kB, reac_disco_table_observe.kA. rewrite Hcc. reflexivity.
      -- bz Hc2.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5310; [awrK U8 U19 Hr8|].
         destruct (run_mem _ _ r m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK4 HP4 HO4) as (HK5 & HP5 & HO5). clear HF HFr HG.
         assert (Hcc : reac_disco_table_observe.cR T G r = false) by (first [clear - Hc Hc0 Hc1 Hc2; mflag | mflag]).
         knx k2 T (disco_table_c.upd T (48 * r + 40) (Z_to_le_bytes 8 now)) r false HSTK HO5 HK5 HP5 HXn HXl HSV HOW Hr8 U8 U19 U2.
         ++ rewrite Hcc. reflexivity.
         ++ unfold reac_disco_table_observe.kB, reac_disco_table_observe.kA. rewrite Hcc. reflexivity.
Qed.
Definition k1_stmt : Prop := forall r regs' m md,
  0 <= r < disco_table_c.n_of T -> disco_table_c.find_res T (disco_table_c.s_mac G) r ->
  tJ m md -> tKP m -> tPR m -> tTB m T -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 18 = w64 s -> getr regs' 19 = w64 (t + 48 * r) -> getr regs' 20 = w64 now ->
  getr regs' 22 = w64 SB ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x52a8)) m (seg_rom SEGS)) md) tQ.
Definition append_stmt : Prop := forall regs' m md,
  disco_table_c.find_res T (disco_table_c.s_mac G) (-1) -> 0 <= disco_table_c.n_of T < 8 ->
  tJ m md -> tKP m -> tPR m -> tTB m T -> tSV m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 9 = w64 ow -> getr regs' 18 = w64 s -> getr regs' 20 = w64 now ->
  getr regs' 21 = w64 (t + 384) -> getr regs' 22 = w64 SB -> getr regs' 23 = w64 (2 ^ 64 - 1 - t) ->
  getr regs' 24 = w64 (disco_table_c.n_of T) -> getr regs' 25 = w64 ((t + 384) / 8 + SB) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x50bc)) m (seg_rom SEGS)) md) tQ.
Definition ap_stk : YP09.region := YP09.mkRegion (Some 2%nat) 0 112 0 0 sav_chunks.
Definition ap_rg : smem := [ap_stk; rK_head; rK_ent; rK_sig].
Definition ap_fa : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 8 (2 ^ 47 - 401) 3); (18%nat, mkAF 8 (2 ^ 47 - 25) 3);
    (19%nat, mkAF 8 (2 ^ 47 - 49) 3); (22%nat, mkAF SB SB 0);
    (46%nat, AF32); (47%nat, AF32); (48%nat, AF32);
    (49%nat, AF32); (50%nat, AF8); (51%nat, AF8); (52%nat, AF8); (53%nat, AF8); (54%nat, AF8);
    (55%nat, AF32); (56%nat, AF32);
    (57%nat, AF32); (58%nat, AF8); (59%nat, AF8); (60%nat, AF8); (61%nat, AF8); (62%nat, AF8); (63%nat, AF32) ] [] [].
Definition ap_ss (pc : Z) : sstate := mkSS pc sr_atoms ap_rg None ap_fa.
Definition ap_sr0 : list sv := sr_set (sr_set sr_atoms 21%bv (SOff 8 384))
  25%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 384) (SLit 3)) (SOff 22 0)).
Definition ap_fa0 : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 8 (2 ^ 47 - 401) 3); (22%nat, mkAF SB SB 0);
    (23%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 9) 0); (24%nat, mkAF 0 7 0); (46%nat, AF32) ] [] [].
Definition ap_hd0 : YP09.region := YP09.mkRegion (Some 8%nat) 384 388 384 388 [ckv 384 4 46].
Definition ap_ss0 : sstate := mkSS 0x50bc ap_sr0 [ap_hd0] None ap_fa0.
Definition ap_SH0 : list shent := [mkSHE 8 0 400].
Lemma ap_st0 : forall regs' m,
  tKP m -> tPR m -> tTB m T -> 0 <= disco_table_c.n_of T < 8 ->
  spZ regs' = spZ regs - 112 -> getr regs' 8 = w64 t -> getr regs' 21 = w64 (t + 384) -> getr regs' 22 = w64 SB ->
  getr regs' 23 = w64 (2 ^ 64 - 1 - t) -> getr regs' 24 = w64 (disco_table_c.n_of T) ->
  getr regs' 25 = w64 ((t + 384) / 8 + SB) ->
  st_ok_pi SEGS VAL (EK regs' T (disco_table_c.n_of T)) ap_ss0
    (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + 0x50bc)) m (seg_rom SEGS))) /\
  sh_ok SEGS BxK ap_SH0 (EK regs' T (disco_table_c.n_of T)) (mrestrict (w_H W) m).
Proof.
intros regs' m HK HP [HX HXl] Hn Hsp R8 R21 R22 R23 R24 R25.
rs_hide_all. apply rs_hide in Rnow.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Htam as Hamt. pose proof Htside as Hts.
unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hlo, Hts.
assert (E2 : ew (EK regs' T (disco_table_c.n_of T)) 2 = getr regs' 2)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ 2 2%bv eq_refl)).
assert (E8 : ew (EK regs' T (disco_table_c.n_of T)) 8 = Z_to_bv 64 t)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl); exact R8).
assert (E22 : ew (EK regs' T (disco_table_c.n_of T)) 22 = Z_to_bv 64 SB)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl); exact R22).
assert (E23 : ew (EK regs' T (disco_table_c.n_of T)) 23 = Z_to_bv 64 (2 ^ 64 - 1 - t))
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 23 23%bv eq_refl); exact R23).
assert (E24 : ew (EK regs' T (disco_table_c.n_of T)) 24 = Z_to_bv 64 (disco_table_c.n_of T))
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 24 24%bv eq_refl); exact R24).
assert (VB : forall n v, ew (EK regs' T (disco_table_c.n_of T)) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  base_val (EK regs' T (disco_table_c.n_of T)) (Some n) = v).
{ intros n v Hn' Hv. cbn [base_val]. rewrite Hn'. apply unsigned_lit_small. exact Hv. }
assert (Rt : 0 <= t < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Hwr : forall a, t <= a < t + 400 -> writable_at SEGS (mrestrict (w_H W) m) a).
{ intros a Ha. apply (apresent_writable SEGS). apply HP. exact (proj2 (Htw a Ha)). }
assert (UA : forall o w, 0 <= o -> o + Z.of_nat w <= 400 ->
  val_mem SEGS (mrestrict (w_H W) m) (t + o) w (disco_table_c.u_at T o w)).
{ intros o w Ho Hw. apply garr8_u_at; [exact HX | exact Ho | rewrite HXl; exact Hw]. }
assert (UR : forall bs o w, 0 <= disco_table_c.u_at bs o w < 2 ^ (8 * Z.of_N (N.of_nat w))).
{ intros bs o w. rewrite nat_N_Z. apply reac_disco_table_observe.u_at_range. }
assert (Ht8' : 8 <= t) by (pose proof (Z.div_mod t 8 ltac:(lia)) as Hd; rewrite Ht8 in Hd; lia).
rewrite restrict_mkst_fx.
split.
- unfold ap_ss0. apply pa_entry_st_ok_full.
  + unfold ap_sr0. apply YI04.regs_ok_pin; [apply YI04.regs_ok_pin | |].
    * unfold EK. apply regs_ok_Eimg_Ereg.
    * intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc.
    * cbn [sv_denot]. rewrite E8, unsigned_lit_small by lia. exact R21.
    * intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc.
    * rewrite denot_lit_U, R25. unfold w64. f_equal.
      rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom_off _ 8 t 384 E8) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
      rewrite (U_atom _ 22 SB E22) by (unfold SB; lia). rewrite U_SLit.
      change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      assert (0 <= (t + 384) / 8 <= t + 384) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      rewrite (zcanon_id ((t + 384) / 8)) by (unfold M64, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
      symmetry. apply zcanon_id. unfold M64, SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  + vm_compute. reflexivity.
  + unfold ap_hd0, ckv. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 8%nat t E8 Rt). split; [lia|]. split; [lia|].
    split; [intros o Ho; apply Hwr; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?w _)) =>
      apply (chunk_ok_val SEGS _ _ _ o w _ (disco_table_c.u_at T o (N.to_nat w)));
      [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (UR T o (N.to_nat w)) as Hb; rewrite N2Nat.id in Hb; exact Hb
      | zside | apply UA; zside ] end.
  + apply pairwise_disjoint_of_extents. unfold ap_hd0, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 8%nat t E8 Rt).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    unfold ap_fa0, AF32. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E22, E23, E24. change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
    rewrite !unsigned_lit_small by (unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
    unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map].
    rewrite !unsigned_lit_small by (first [apply UR | pose proof (UR T 384 4) as U0; cbn in U0; lia
      | lazymatch goal with |- 0 <= disco_table_c.u_at ?bs ?o ?w < _ => pose proof (UR bs o w) as U0; cbn in U0; lia end]).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm1 : (spZ regs - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamt.
    unfold rs_hold in Ht8.
    repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- context [disco_table_c.u_at ?bs ?o ?w] => pose proof (UR bs o w) as U0; cbn in U0; rlia end
          | lazymatch goal with |- context [SB] => unfold SB; rlia end | rlia ].
- unfold sh_ok, ap_SH0. repeat apply Forall_cons; try apply Forall_nil; unfold shent_ok, app_apart, BxK;
  cbn [she_m she_lo she_hi].
  rewrite (U_atom _ 22 SB E22) by (unfold SB; lia).
  rewrite (U_atom _ 8 t E8) by lia. split.
  + replace (t + 0) with t by lia. replace (400 - 0) with 400 by lia.
    exact (kp_ra m t 400 HK ltac:(lia) Htam ltac:(lia) Htra).
  + intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
Qed.
Lemma ap_kst : forall pc regs' m X r,
  tKP m -> tPR m -> tTB m X -> tSV m -> 0 <= r < 8 ->
  spZ regs' = spZ regs - 112 -> getr regs' 8 = w64 t -> getr regs' 18 = w64 s ->
  getr regs' 19 = w64 (t + 48 * r) -> getr regs' 22 = w64 SB ->
  st_ok_pi SEGS VAL (EK regs' X r) (ap_ss pc) (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
  sh_ok SEGS BxK SH_K (EK regs' X r) (mrestrict (w_H W) m).
Proof.
intros pc regs' m X r HK HP [HX HXl] HSV Hr Hsp R8 R18 R19 R22.
rs_hide_all. apply rs_hide in Rnow.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Htam as Hamt. pose proof Hsam as Hams. pose proof Htside as Hts. pose proof Hsside as Hss.
unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hlo, Hts, Hss.
pose proof (kp_garr8_G m HK) as HGm.
assert (E2 : ew (EK regs' X r) 2 = getr regs' 2)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ 2 2%bv eq_refl)).
assert (E8 : ew (EK regs' X r) 8 = Z_to_bv 64 t)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew (EK regs' X r) 18 = Z_to_bv 64 s)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew (EK regs' X r) 19 = Z_to_bv 64 (t + 48 * r))
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl); exact R19).
assert (E22 : ew (EK regs' X r) 22 = Z_to_bv 64 SB)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl); exact R22).
assert (VB : forall n v, ew (EK regs' X r) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val (EK regs' X r) (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (B2 : base_val (EK regs' X r) (Some 2%nat) = spZ regs - 112) by (cbn [base_val]; rewrite E2; exact Hsp).
assert (Rt : 0 <= t < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Rs : 0 <= s < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Re : 0 <= t + 48 * r < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Hwr : forall a, t <= a < t + 400 -> writable_at SEGS (mrestrict (w_H W) m) a).
{ intros a Ha. apply (apresent_writable SEGS). apply HP. exact (proj2 (Htw a Ha)). }
assert (UA : forall o w, 0 <= o -> o + Z.of_nat w <= 400 ->
  val_mem SEGS (mrestrict (w_H W) m) (t + o) w (disco_table_c.u_at X o w)).
{ intros o w Ho Hw. apply garr8_u_at; [exact HX | exact Ho | rewrite HXl; exact Hw]. }
assert (UG : forall o w, 0 <= o -> o + Z.of_nat w <= 24 ->
  val_mem SEGS (mrestrict (w_H W) m) (s + o) w (disco_table_c.u_at G o w)).
{ intros o w Ho Hw. apply garr8_u_at; [exact HGm | exact Ho | rewrite HGl; exact Hw]. }
assert (UR : forall bs o w, 0 <= disco_table_c.u_at bs o w < 2 ^ (8 * Z.of_N (N.of_nat w))).
{ intros bs o w. rewrite nat_N_Z. apply reac_disco_table_observe.u_at_range. }
rewrite restrict_mkst_fx.
split.
- unfold ap_ss. apply pa_entry_st_ok_full.
  + unfold EK. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ap_rg, ap_stk, rK_head, rK_ent, rK_sig, sav_chunks, ckv.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite B2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with
           | |- chunk_ok _ _ _ _ (YP09.mkChunk ?o _) =>
             let q := lazymatch o with 104 => constr:(1%bv : bv 5) | 96 => constr:(8%bv : bv 5) | 88 => constr:(9%bv : bv 5)
               | 80 => constr:(18%bv : bv 5) | 72 => constr:(19%bv : bv 5) | 64 => constr:(20%bv : bv 5)
               | 56 => constr:(21%bv : bv 5) | 48 => constr:(22%bv : bv 5) | 40 => constr:(23%bv : bv 5)
               | 32 => constr:(24%bv : bv 5) | 24 => constr:(25%bv : bv 5) | 16 => constr:(26%bv : bv 5)
               | 8 => constr:(27%bv : bv 5) end in
             apply (chunk_ok_val SEGS _ _ _ o 8 _ (bv_unsigned (getr regs q)));
             [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
               rewrite Z.add_0_r; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs q)) as Hb; unfold bv_modulus in Hb; zside
             | zside | apply HSV; cbv [SAVSL In]; clear - Row; tauto ]
           end.
    * rewrite (VB 8%nat t E8 Rt). split; [lia|]. split; [lia|].
      split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?w _)) =>
        apply (chunk_ok_val SEGS _ _ _ o w _ (disco_table_c.u_at X o (N.to_nat w)));
        [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (UR X o (N.to_nat w)) as Hb; rewrite N2Nat.id in Hb; exact Hb
        | zside | apply UA; zside ] end.
    * rewrite (VB 19%nat (t + 48 * r) E19 Re). split; [lia|]. split; [lia|].
      split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?w _)) =>
        apply (chunk_ok_val SEGS _ _ _ o w _ (disco_table_c.u_at X (48 * r + o) (N.to_nat w)));
        [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (UR X (48 * r + o) (N.to_nat w)) as Hb; rewrite N2Nat.id in Hb; exact Hb
        | zside | replace (t + 48 * r + o) with (t + (48 * r + o)) by lia; apply UA; zside ] end.
    * rewrite (VB 18%nat s E18 Rs). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?w _)) =>
        apply (chunk_ok_val SEGS _ _ _ o w _ (disco_table_c.u_at G o (N.to_nat w)));
        [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (UR G o (N.to_nat w)) as Hb; rewrite N2Nat.id in Hb; exact Hb
        | zside | apply UG; zside ] end.
  + apply pairwise_disjoint_of_extents. unfold ap_rg, ap_stk, rK_head, rK_ent, rK_sig, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2, (VB 8%nat t E8 Rt), (VB 19%nat (t + 48 * r) E19 Re),
      (VB 18%nat s E18 Rs).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold rs_hold in Hts, Hss, Hdts. unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *. repeat split; rlia.
  + split; [|split; [exact I | exact I]].
    unfold ap_fa, AF32, AF8. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E18, E19, E22. change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
    rewrite !unsigned_lit_small by (unfold SB; lia).
    unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map].
    rewrite !unsigned_lit_small by (first [apply UR | pose proof (UR X 384 4) as U0; cbn in U0; lia
      | lazymatch goal with |- 0 <= disco_table_c.u_at ?bs ?o ?w < _ => pose proof (UR bs o w) as U0; cbn in U0; lia end]).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm1 : (spZ regs - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
    assert (Hm2 : (t + 48 * r) mod 8 = 0) by (rewrite Zplus_mod, Ht8, Zmult_mod; reflexivity).
    assert (Ht8' : 8 <= t) by (pose proof (Z.div_mod t 8 ltac:(lia)) as Hd; rewrite Ht8 in Hd; lia).
    assert (Hs8' : 8 <= s) by (pose proof (Z.div_mod s 8 ltac:(lia)) as Hd; rewrite Hs8 in Hd; lia).
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamt, Hams.
    unfold rs_hold in Ht8, Hs8.
    repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- context [disco_table_c.u_at ?bs ?o ?w] => pose proof (UR bs o w) as U0; cbn in U0; rlia end
          | lazymatch goal with |- context [SB] => unfold SB; rlia end | rlia ].
- unfold sh_ok, SH_K. repeat apply Forall_cons; try apply Forall_nil; unfold shent_ok, app_apart, BxK;
  cbn [she_m she_lo she_hi].
  all: rewrite (U_atom _ 22 SB E22) by (unfold SB; lia).
  + rewrite (U_atom _ 8 t E8) by lia. split.
    * replace (t + 0) with t by lia. replace (400 - 0) with 400 by lia.
      exact (kp_ra m t 400 HK ltac:(lia) Htam ltac:(lia) Htra).
    * intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
  + rewrite (U_atom _ 19 (t + 48 * r) E19) by lia. split.
    * replace (t + 48 * r + 0) with (t + 48 * r) by lia. replace (48 - 0) with 48 by lia.
      apply (range_addressable_sub _ _ t 400); [exact (kp_ra m t 400 HK ltac:(lia) Htam ltac:(lia) Htra) | lia | lia].
    * intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
  + rewrite (U_atom _ 18 s E18) by lia. split.
    * replace (s + 0) with s by lia. replace (24 - 0) with 24 by lia.
      exact (kp_ra m s 24 HK ltac:(lia) Hsam ltac:(lia) Hsra).
    * intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
Qed.
#[local] Notation ap_XA := (disco_table_c.upd T 384 (Z_to_le_bytes 4 (disco_table_c.n_of T + 1))).
#[local] Notation ap_X1 := (disco_table_c.upd ap_XA (48 * disco_table_c.n_of T) (Z_to_le_bytes 48 0)).
#[local] Notation ap_X2 := (disco_table_c.upd ap_X1 (48 * disco_table_c.n_of T) (disco_table_c.sub G 0 6)).
#[local] Notation ap_XF := (disco_table_c.upd (disco_table_c.upd ap_XA (48 * disco_table_c.n_of T)
  (reac_disco_table_observe_c.new_entry G ow now)) 392 (Z_to_le_bytes 4 (disco_table_c.seq_of T + 1))).
Lemma ap_upd_in : forall (X bs : list byte) o j, 0 <= o -> o + Z.of_nat (length bs) <= Z.of_nat (length X) ->
  (j < length X)%nat -> o <= Z.of_nat j < o + Z.of_nat (length bs) ->
  nth_error (disco_table_c.upd X o bs) j = nth_error bs (j - Z.to_nat o).
Proof.
intros X bs o j Ho Hl Hj Hin. rewrite upd_nth by assumption.
destruct ((o <=? Z.of_nat j) && (Z.of_nat j <? o + Z.of_nat (length bs)))%bool eqn:Hc; [reflexivity|].
apply andb_false_iff in Hc as [H1 | H1]; [apply Z.leb_gt in H1 | apply Z.ltb_ge in H1]; lia.
Qed.
Lemma ap_ne_nth : forall (G' : list byte) ow' now' q, length G' = 24%nat -> (q < 8)%nat ->
  nth_error (reac_disco_table_observe_c.new_entry G' ow' now') q =
  if (q <? 6)%nat then nth_error (disco_table_c.sub G' 0 6) q else nth_error (Z_to_le_bytes 48 0) q.
Proof.
intros G' ow' now' q LG Hk.
do 24 (destruct G' as [|? G']; [cbn in LG; lia|]). destruct G'; [|cbn in LG; lia].
do 8 (destruct q as [|q]; [reflexivity|]). lia.
Qed.
Lemma ap_ne_sub : forall (G' : list byte) ow' now', length G' = 24%nat ->
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 8 4 = disco_table_c.sub G' 8 4 /\
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 12 1 = disco_table_c.sub G' 12 1 /\
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 13 1 = disco_table_c.sub G' 13 1 /\
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 14 1 = disco_table_c.sub G' 14 1 /\
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 15 1 = disco_table_c.sub G' 15 1 /\
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 16 1 = disco_table_c.sub G' 16 1 /\
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 20 4 = disco_table_c.sub G' 20 4 /\
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 17 3 = Z_to_le_bytes 3 0 /\
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 28 4 = Z_to_le_bytes 4 0 /\
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 24 4 = Z_to_le_bytes 4 (if ow' =? 0 then 0 else 1) /\
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 32 8 = Z_to_le_bytes 8 now' /\
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G' ow' now') 40 8 = Z_to_le_bytes 8 now'.
Proof.
intros G' ow' now' LG.
do 24 (destruct G' as [|? G']; [cbn in LG; lia|]). destruct G'; [|cbn in LG; lia].
repeat split; reflexivity.
Qed.
Lemma ap_sext : forall E' n u, ew E' n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  bv_unsigned (sv_denot E' (SExt true 32 (SOff n 0))) mod 2 ^ (8 * 4) = u.
Proof.
intros E' n u H Hu.
change (bv_unsigned (sv_denot E' (SExt true 32 (SOff n 0)))) with (U E' (SExt true 32 (SOff n 0))).
rewrite U_SExt, U_SOff, H, Z.add_0_r, unsigned_lit_small by lia.
change (8 * 4) with 32. change (Z.of_N 32) with 32. cbv iota. unfold zcanon, M64.
rewrite (Z.mod_small u (2 ^ 64)) by lia. rewrite mod64_32, (Z.mod_small u (2 ^ 32)) by lia.
change (2 ^ 32) with (bv_modulus 32). rewrite reac_disco_table_observe.swrap_mod.
apply Z.mod_small. change (bv_modulus 32) with (2 ^ 32). lia.
Qed.
Lemma ap_sltu : forall E', ew E' 9 = Z_to_bv 64 ow ->
  bv_unsigned (sv_denot E' (SAlu ALU_SLTU (SLit 0) (SOff 9 0))) mod 2 ^ (8 * 4) = if ow =? 0 then 0 else 1.
Proof.
intros E' H.
change (bv_unsigned (sv_denot E' (SAlu ALU_SLTU (SLit 0) (SOff 9 0)))) with (U E' (SAlu ALU_SLTU (SLit 0) (SOff 9 0))).
rewrite U_SAlu, U_SLit, U_SOff, H, Z.add_0_r. cbn [zalu_raw].
rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. change (0 mod 2 ^ 64) with 0.
destruct (Z.eqb_spec ow 0) as [->|Hn]; [reflexivity|].
assert (Hp : 0 < ow mod 2 ^ 64).
{ destruct (Z.leb_spec 0 ow).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add ow 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
destruct (Z.ltb_spec 0 (ow mod 2 ^ 64)); [reflexivity | lia].
Qed.
Lemma ap_now : forall E', ew E' 20 = Z_to_bv 64 now -> bv_unsigned (sv_denot E' (SOff 20 0)) mod 2 ^ (8 * 8) = now.
Proof.
intros E' H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia.
apply Z.mod_small. lia.
Qed.
Lemma ap_inc : forall E', ew E' 24 = Z_to_bv 64 (disco_table_c.n_of T) -> 0 <= disco_table_c.n_of T < 8 ->
  bv_unsigned (sv_denot E' (SOff 24 1)) mod 2 ^ (8 * Z.of_N 4) = disco_table_c.n_of T + 1.
Proof.
intros E' H Hn. cbn [sv_denot]. rewrite H, (unsigned_lit_small (disco_table_c.n_of T)) by lia.
rewrite unsigned_lit_small by lia.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). apply Z.mod_small. lia.
Qed.
Lemma ap_dv : forall E', ew E' 8 = Z_to_bv 64 t -> ew E' 24 = Z_to_bv 64 (disco_table_c.n_of T) ->
  0 <= disco_table_c.n_of T < 8 ->
  sv_denot E' (SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 24 0) (SLit 48))) = Z_to_bv 64 (t + 48 * disco_table_c.n_of T).
Proof.
intros E' H8 H24 Hn. pose proof Htam as Ha. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ha.
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom _ 8 t H8) by lia. rewrite (U_atom _ 24 _ H24) by lia. rewrite U_lit by lia.
rewrite (zcanon_id (disco_table_c.n_of T * 48)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma ap_sv : forall m m', (forall a, spZ regs - 112 <= a < spZ regs -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  tSV m -> tSV m'.
Proof.
intros m m' He HS o q Hin. pose proof (HS o q Hin) as Hv. apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) m m'); [|exact Hv].
intros x Hx. apply He. cbv [SAVSL In] in Hin.
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]). destruct Hin.
Qed.
Lemma ap_shv_sub : forall rd x n x' n', shadow_hull_vis rd x n -> 0 <= x -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H0 H1 H2 H3 z Hz. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1).
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
lia.
Qed.
Lemma ap_src : forall m a, tKP m -> s <= a < s + 24 -> aview SEGS (w_H W) m a <> None.
Proof.
intros m a HK Ha. pose proof (kp_garr8_G m HK) as HG'.
destruct (HG' (Z.to_nat (a - s)) ltac:(rewrite length_map, HGl; lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). replace (s + Z.of_nat (Z.to_nat (a - s)) + Z.of_nat 0) with a in Hv by lia.
unfold aview. rewrite Hv. cbn [option_map]. discriminate.
Qed.
Lemma ap_zero_vm : forall (M : word -> option byte) d (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> mbyte SEGS M (d + i) = Some (Z_to_bv 8 0)) -> val_mem SEGS M d n 0.
Proof.
intros M d n H kk Hk. rewrite (H (Z.of_nat kk)) by lia. f_equal. f_equal.
cbv delta [YG0f.le_byte YO0f.le_byte] beta. rewrite Zmod_0_l, Z.shiftr_0_l, Zmod_0_l. reflexivity.
Qed.
Lemma ap_mb_of_av : forall (m : word -> option byte) a z, aview SEGS (w_H W) m a = Some z ->
  mbyte SEGS (mrestrict (w_H W) m) a = Some (Z_to_bv 8 z).
Proof.
intros m a z H. unfold aview in H. destruct (mbyte SEGS (mrestrict (w_H W) m) a) as [b|]; cbn in H; [|discriminate].
injection H as <-. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Ltac ap_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac ap_rgn HS i rg R :=
  first [ pose proof (st_ok_pi_region_nth _ _ _ i rg HS ltac:(vm_compute; reflexivity)) as R
        | pose proof (st_ok_region_nth (segs := SEGS) _ _ _ i rg HS ltac:(vm_compute; reflexivity)) as R ];
  cbn [ms_mem restrict mkst] in R.
Lemma ap_nth : forall j, 0 <= disco_table_c.n_of T < 8 -> 0 <= j < 400 -> ~ WK (disco_table_c.n_of T) (t + j) ->
  nth_error ap_XF (Z.to_nat j) = nth_error ap_X2 (Z.to_nat j).
Proof.
intros j Hn Hj Hw. unfold WK in Hw.
rs_hide_all. apply rs_hide in Rnow.
pose proof (proj1 (reac_disco_table_observe.mf_ne G ow now HGl)) as LN.
assert (Hjl : (Z.to_nat j < 400)%nat) by lia.
destruct (Z_lt_le_dec j (48 * disco_table_c.n_of T + 48)) as [Hlt | Hge];
  [destruct (Z_lt_le_dec j (48 * disco_table_c.n_of T)) as [Hlo | Hge2] |].
- rewrite !nth_upd_out by (mvl; rewrite ?LN; mvl; lia). reflexivity.
- assert (Hj8 : j < 48 * disco_table_c.n_of T + 8) by rlia.
  rewrite (nth_upd_out _ _ 392) by (mvl; rewrite ?LN; mvl; lia).
  rewrite ap_upd_in by (mvl; rewrite ?LN; mvl; lia).
  rewrite (ap_ne_nth G ow now _ HGl) by lia.
  destruct (Z_lt_le_dec j (48 * disco_table_c.n_of T + 6)).
  + replace (Z.to_nat j - Z.to_nat (48 * disco_table_c.n_of T) <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite ap_upd_in by (mvl; lia). reflexivity.
  + replace (Z.to_nat j - Z.to_nat (48 * disco_table_c.n_of T) <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    rewrite nth_upd_out by (mvl; lia). rewrite ap_upd_in by (mvl; lia). reflexivity.
- rewrite !nth_upd_out by (mvl; rewrite ?LN; mvl; rlia). reflexivity.
Qed.
Lemma ap_atom1 : forall Ex a bs k' (w : nat) z, (w <= 8)%nat -> ew Ex a = Z_to_bv 64 (disco_table_c.u_at bs k' w) ->
  z = 2 ^ (8 * Z.of_nat w) -> bv_unsigned (sv_denot Ex (SOff a 0)) mod z = disco_table_c.u_at bs k' w.
Proof.
intros Ex a bs k' w z Hw H Hz. subst z. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
pose proof (reac_disco_table_observe.u_at_range bs k' w) as Ur.
assert (Hp : 2 ^ (8 * Z.of_nat w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
Qed.
Lemma ap_mb2 : forall (m m' : word -> option byte) a b, aview SEGS (w_H W) m' a = aview SEGS (w_H W) m b ->
  mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) b.
Proof.
intros m m' a b H. unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W) m') a) as [x|], (mbyte SEGS (mrestrict (w_H W) m) b) as [y|]; cbn in H;
  try discriminate; [|reflexivity].
injection H as H. f_equal. apply bv_eq. exact H.
Qed.
Lemma ap_lx : forall o (w : nat), 0 <= o -> o + Z.of_nat w <= 48 -> 0 <= disco_table_c.n_of T < 8 ->
  disco_table_c.sub ap_XF (48 * disco_table_c.n_of T + o) w =
  disco_table_c.sub (reac_disco_table_observe_c.new_entry G ow now) o w.
Proof.
intros o w Ho Hw Hn. pose proof (proj1 (reac_disco_table_observe.mf_ne G ow now HGl)) as LN.
rewrite reac_disco_table_observe.sub_upd_other by (mvl; lia).
rewrite reac_disco_table_observe.sub_upd_in by (mvl; lia). f_equal. lia.
Qed.
Lemma ap_lx384 : 0 <= disco_table_c.n_of T < 8 -> disco_table_c.sub ap_XF 384 4 = Z_to_le_bytes 4 (disco_table_c.n_of T + 1).
Proof.
intros Hn. pose proof (proj1 (reac_disco_table_observe.mf_ne G ow now HGl)) as LN.
rewrite reac_disco_table_observe.sub_upd_other by (mvl; lia).
rewrite reac_disco_table_observe.sub_upd_other by (mvl; lia).
apply reac_disco_table_observe.mf_sub_upd_at; mvl; lia.
Qed.
Lemma ap_lx392 : 0 <= disco_table_c.n_of T < 8 -> disco_table_c.sub ap_XF 392 4 = Z_to_le_bytes 4 (disco_table_c.seq_of T + 1).
Proof.
intros Hn. pose proof (proj1 (reac_disco_table_observe.mf_ne G ow now HGl)) as LN.
apply reac_disco_table_observe.mf_sub_upd_at; mvl; lia.
Qed.
Lemma ap_x2o : forall k' (w : nat), 0 <= k' -> k' + Z.of_nat w <= 400 ->
  (k' + Z.of_nat w <= 48 * disco_table_c.n_of T \/ 48 * disco_table_c.n_of T + 48 <= k') -> 0 <= disco_table_c.n_of T < 8 ->
  disco_table_c.sub ap_X2 k' w = disco_table_c.sub ap_XA k' w.
Proof.
intros k' w H0 H1 H2 Hn.
rewrite reac_disco_table_observe.sub_upd_other by (mvl; lia).
rewrite reac_disco_table_observe.sub_upd_other by (mvl; lia). reflexivity.
Qed.
Lemma ap_x2slot : forall o (w : nat), 6 <= o -> o + Z.of_nat w <= 48 -> 0 <= disco_table_c.n_of T < 8 ->
  disco_table_c.sub ap_X2 (48 * disco_table_c.n_of T + o) w = disco_table_c.sub (Z_to_le_bytes 48 0) o w.
Proof.
intros o w Ho Hw Hn.
rewrite reac_disco_table_observe.sub_upd_other by (mvl; lia).
rewrite reac_disco_table_observe.sub_upd_in by (mvl; lia). f_equal. lia.
Qed.
Lemma ap_seq : 0 <= disco_table_c.n_of T < 8 -> disco_table_c.u_at ap_X2 392 4 = disco_table_c.seq_of T.
Proof.
intros Hn. unfold disco_table_c.seq_of, disco_table_c.u_at. rewrite ap_x2o by lia.
rewrite reac_disco_table_observe.sub_upd_other by (mvl; lia). reflexivity.
Qed.
Lemma ap_c : forall regs3 m md,
  disco_table_c.find_res T (disco_table_c.s_mac G) (-1) -> 0 <= disco_table_c.n_of T < 8 ->
  tJ m md -> tKP m -> tPR m -> tTB m ap_X2 -> tSV m ->
  spZ regs3 = spZ regs - 112 -> getr regs3 3 = getr regs 3 -> getr regs3 4 = getr regs 4 ->
  getr regs3 8 = w64 t -> getr regs3 9 = w64 ow -> getr regs3 18 = w64 s ->
  getr regs3 19 = w64 (t + 48 * disco_table_c.n_of T) -> getr regs3 20 = w64 now -> getr regs3 22 = w64 SB ->
  SRr SEGS W (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 0x5108)) m (seg_rom SEGS)) md) tQ.
Proof.
intros regs3 m md FI Hn HJ HK HP HX HSV Hsp R3 R4 R8 R9 R18 R19 R20 R22.
rs_hide_all. apply rs_hide in Rnow.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct (ap_kst 0x5108 regs3 m _ (disco_table_c.n_of T) HK HP HX HSV Hn Hsp R8 R18 R19 R22) as [HS SHOK].
pose proof (tTB_tbn m _ HX) as HXn.
assert (HO : forall a, 0 <= a < 2 ^ 64 -> ~ WK (disco_table_c.n_of T) a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m a)
  by reflexivity.
pose proof (proj2 HX) as HXl.
remember (EK regs3 ap_X2 (disco_table_c.n_of T)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Rt : 0 <= t < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia).
assert (U8 : bv_unsigned (ew E 8) = t)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl), R8;
      apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = t + 48 * disco_table_c.n_of T)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 19 19%bv eq_refl), R19;
      apply unsigned_lit_small; unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 112)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact Hsp).
assert (E3 : ew E 3 = getr regs 3)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs 4)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 4 4%bv eq_refl); exact R4).
assert (E9 : ew E 9 = Z_to_bv 64 ow)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); exact R9).
assert (E20 : ew E 20 = Z_to_bv 64 now)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 20 20%bv eq_refl); exact R20).
ekall HE.
paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hn|].
destruct (run_mem _ _ (disco_table_c.n_of T) m m _ Hn HFr HG ltac:(kwin U8 U19) HK HP HO) as (HK1 & HP1 & HO1).
clear HF HFr HG.
pose proof (proj1 (reac_disco_table_observe.mf_ne G ow now HGl)) as LN.
destruct (ap_ne_sub G ow now HGl) as (NE8 & NE12 & NE13 & NE14 & NE15 & NE16 & NE20 & NE17 & NE28 & NE24 & NE32 & NE40).
kfin constr:(ap_X2) constr:(ap_XF) (disco_table_c.n_of T) 1 HO1 HK1 HP1 HXn HXl Hn U8 U19 U2 E3 E4.
- intros j Hj Hw. split; [apply (mbyte_of_aview SEGS); apply HO1; [lia | exact Hw] | exact (ap_nth j Hn Hj Hw)].
- kchunks.
  + rewrite (ap_lx392 Hn).
    lazymatch goal with |- context [sv_denot ?Ex _] =>
      rewrite (seq_val Ex 48 (disco_table_c.u_at ap_X2 392 4))
        by (first [cbn [ew ewset extK Nat.eqb]; exact EQ48 | apply reac_disco_table_observe.u32_range]) end.
    rewrite (ap_seq Hn). rewrite (OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.Z_to_le_bytes_mod 4 _ 32) by lia.
    reflexivity.
  + rewrite (ap_lx384 Hn).
    lazymatch goal with |- context [sv_denot ?Ex _] =>
      rewrite (ap_atom1 Ex 46 _ 384 4 (2 ^ (8 * 4)) ltac:(lia) ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ46) eq_refl) end.
    rewrite reac_disco_table_observe.le_sub by (mvl; lia). rewrite ap_x2o by lia.
    symmetry. apply reac_disco_table_observe.mf_sub_upd_at; mvl; lia.
  + rewrite (ap_lx 40 8) by lia. rewrite NE40. f_equal.
    lazymatch goal with |- context [sv_denot ?Ex _] => symmetry; apply (ap_now Ex); cbn [ew ewset extK Nat.eqb]; exact E20 end.
  + rewrite (ap_lx 32 8) by lia. rewrite NE32. f_equal.
    lazymatch goal with |- context [sv_denot ?Ex _] => symmetry; apply (ap_now Ex); cbn [ew ewset extK Nat.eqb]; exact E20 end.
  + rewrite (ap_lx 24 4) by lia. rewrite NE24. f_equal.
    lazymatch goal with |- context [sv_denot ?Ex _] => symmetry; apply (ap_sltu Ex); cbn [ew ewset extK Nat.eqb]; exact E9 end.
  + rewrite (ap_lx 20 4) by lia. rewrite NE20.
    lazymatch goal with |- context [sv_denot ?Ex _] =>
      rewrite (ap_sext Ex 63 (disco_table_c.u_at G 20 4))
        by (first [cbn [ew ewset extK Nat.eqb]; exact EQ63 | apply reac_disco_table_observe.u32_range]) end.
    symmetry. apply reac_disco_table_observe.le_sub; lia.
  + rewrite (ap_lx 16 1) by lia. rewrite NE16.
    lazymatch goal with |- context [sv_denot ?Ex _] =>
      rewrite (ap_atom1 Ex 62 _ 16 1 (2 ^ (8 * 1)) ltac:(lia) ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ62) eq_refl) end.
    symmetry. apply reac_disco_table_observe.le_sub; lia.
  + rewrite (ap_lx 15 1) by lia. rewrite NE15.
    lazymatch goal with |- context [sv_denot ?Ex _] =>
      rewrite (ap_atom1 Ex 61 _ 15 1 (2 ^ (8 * 1)) ltac:(lia) ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ61) eq_refl) end.
    symmetry. apply reac_disco_table_observe.le_sub; lia.
  + rewrite (ap_lx 14 1) by lia. rewrite NE14.
    lazymatch goal with |- context [sv_denot ?Ex _] =>
      rewrite (ap_atom1 Ex 60 _ 14 1 (2 ^ (8 * 1)) ltac:(lia) ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ60) eq_refl) end.
    symmetry. apply reac_disco_table_observe.le_sub; lia.
  + rewrite (ap_lx 13 1) by lia. rewrite NE13.
    lazymatch goal with |- context [sv_denot ?Ex _] =>
      rewrite (ap_atom1 Ex 59 _ 13 1 (2 ^ (8 * 1)) ltac:(lia) ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ59) eq_refl) end.
    symmetry. apply reac_disco_table_observe.le_sub; lia.
  + rewrite (ap_lx 12 1) by lia. rewrite NE12.
    lazymatch goal with |- context [sv_denot ?Ex _] =>
      rewrite (ap_atom1 Ex 58 _ 12 1 (2 ^ (8 * 1)) ltac:(lia) ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ58) eq_refl) end.
    symmetry. apply reac_disco_table_observe.le_sub; lia.
  + rewrite (ap_lx 8 4) by lia. rewrite NE8.
    lazymatch goal with |- context [sv_denot ?Ex _] =>
      rewrite (ap_sext Ex 57 (disco_table_c.u_at G 8 4))
        by (first [cbn [ew ewset extK Nat.eqb]; exact EQ57 | apply reac_disco_table_observe.u32_range]) end.
    symmetry. apply reac_disco_table_observe.le_sub; lia.
  + rewrite (ap_lx 17 3) by lia. rewrite NE17.
    lazymatch goal with |- context [sv_denot ?Ex _] =>
      rewrite (ap_atom1 Ex 64 _ _ 3 (2 ^ (8 * 3)) ltac:(lia) ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ64) eq_refl) end.
    rewrite reac_disco_table_observe.le_sub by (mvl; lia). rewrite (ap_x2slot 17 3) by lia. reflexivity.
  + rewrite (ap_lx 28 4) by lia. rewrite NE28.
    lazymatch goal with |- context [sv_denot ?Ex _] =>
      rewrite (ap_atom1 Ex 65 _ _ 4 (2 ^ (8 * 4)) ltac:(lia) ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ65) eq_refl) end.
    rewrite reac_disco_table_observe.le_sub by (mvl; lia). rewrite (ap_x2slot 28 4) by lia. reflexivity.
- exists (-1). split; [exact FI|]. right; right. split; [reflexivity|]. split; [lia|]. reflexivity.
Qed.
Lemma ap_b : forall regs2 m md,
  disco_table_c.find_res T (disco_table_c.s_mac G) (-1) -> 0 <= disco_table_c.n_of T < 8 ->
  tJ m md -> tKP m -> tPR m -> tTB m ap_X1 -> tSV m ->
  spZ regs2 = spZ regs - 112 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = w64 t -> getr regs2 9 = w64 ow -> getr regs2 18 = w64 s ->
  getr regs2 19 = w64 (t + 48 * disco_table_c.n_of T) -> getr regs2 20 = w64 now -> getr regs2 22 = w64 SB ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x50f8)) m (seg_rom SEGS)) md) tQ.
Proof.
intros regs2 m md FI Hn HJ HK HP HX HSV Hsp R3 R4 R8 R9 R18 R19 R20 R22.
rs_hide_all. apply rs_hide in Rnow. unfold rs_hold in Htside.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
destruct Hst as (Hs16 & _).
pose proof Htam as Hamt. pose proof Hsam as Hams.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamt, Hams.
destruct (ap_kst 0x50f8 regs2 m _ (disco_table_c.n_of T) HK HP HX HSV Hn Hsp R8 R18 R19 R22) as [HS SHOK].
pose proof (tTB_tbn m _ HX) as HXn.
assert (HO : forall a, 0 <= a < 2 ^ 64 -> ~ WK (disco_table_c.n_of T) a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m a)
  by reflexivity.
pose proof (proj2 HX) as HXl.
remember (EK regs2 ap_X1 (disco_table_c.n_of T)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Rt : 0 <= t < 2 ^ 64) by lia.
assert (U8 : bv_unsigned (ew E 8) = t)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), R8;
      apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = t + 48 * disco_table_c.n_of T)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl), R19;
      apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 112)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact Hsp).
assert (E3 : ew E 3 = getr regs 3)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs 4)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 4 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 t)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 ow)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 s)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (t + 48 * disco_table_c.n_of T))
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 now)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 SB)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl); exact R22).
ekall HE.
paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hn|].
destruct (run_mem _ _ (disco_table_c.n_of T) m m _ Hn HFr HG ltac:(kwin U8 U19) HK HP HO) as (HK1 & HP1 & HO1).
clear HF HFr HG.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (18%bv : bv 5) Rs2. prreg HS (19%bv : bv 5) Rs3.
prreg HS (20%bv : bv 5) Rs4. prreg HS (22%bv : bv 5) Rs6.
ap_rgn HS 1%nat rK_head RH. ap_rgn HS 2%nat rK_ent RE. unfold rK_head, rK_ent, ckv in RH, RE.
assert (HXn1 : tbn (mrestrict (w_H W) (ms_mem ms)) ap_X1).
{ eapply (kleaf_tbn E _ _ _ _ (disco_table_c.n_of T) _ _ Hn HXn);
  [ exact HXl | exact RH | exact U8 | exact RE | exact U19
  | unfold cws_ok; repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.c_val YP09.c_off Z.of_N]; lia
  | unfold cws_ok; repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.c_val YP09.c_off Z.of_N]; lia
  | vm_compute; reflexivity | vm_compute; reflexivity
  | intros j Hj Hw; split; [apply (mbyte_of_aview SEGS); apply HO1; [lia | exact Hw] | reflexivity]
  | kchunks ]. }
assert (Qsp : spZ (ms_regs ms) = spZ regs - 112) by (unfold spZ at 1; rewrite Rsp; exact U2).
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fx) W (ms_regs ms) (ms_mem ms)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (t + 48 * disco_table_c.n_of T) s 6 (spZ regs - 112 - sp0) _ HJ);
  [ rewrite Ra0, E19; reflexivity
  | rewrite Ra1, E18; reflexivity
  | rewrite Ra2; reflexivity
  | rlia | rlia | rlia
  | rewrite Qsp; rlia
  | unfold rs_hold in Hal; rlia | rlia
  | unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; rlia
  | rewrite Rgp, E3; exact Hgp
  | rewrite Rtp, E4; exact Htp
  | exact Rra
  | apply ret_ok_codeptr_v; [rlia | reflexivity]
  | intros a Ha; split; [exact (proj1 (Htw a ltac:(rlia))) | unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; rlia]
  | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; rlia
  | apply (range_addressable_sub _ _ t 400); [exact (kp_ra (ms_mem ms) t 400 HK1 ltac:(rlia) Htam ltac:(rlia) Htra) | rlia | rlia]
  | intros _; apply (kp_shv (ms_mem ms) (t + 48 * disco_table_c.n_of T) 6 HK1);
    [ rlia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; rlia | rlia
    | apply (ap_shv_sub _ t 400); [exact Htsh | rlia | rlia | rlia | rlia] ]
  | split; [rlia|]; split; [rlia|]; split;
    [ intros a Ha; split;
      [ exact (ap_src (ms_mem ms) a HK1 ltac:(rlia)) | rewrite Qsp; unfold rs_hold in Hsside; unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; rlia ] |];
    split; [unfold rs_hold in Hdts; rlia|]; split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; rlia|]; split;
    [ apply (range_addressable_sub _ _ s 24); [exact (kp_ra (ms_mem ms) s 24 HK1 ltac:(rlia) Hsam ltac:(rlia) Hsra) | rlia | rlia]
    | intros _; apply (kp_shv (ms_mem ms) s 6 HK1);
      [ rlia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; rlia | rlia
      | apply (ap_shv_sub _ s 24); [exact Hssh | rlia | rlia | rlia | rlia] ] ] ]
| ].
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HPR3 & Ha03 & Heff & Hfr & Hpres3).
cbv beta iota in Heff.
assert (HK3 : tKP mem3).
{ intros a Ha Hs Ht. rewrite Hfr by (unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; rlia). apply HK1; assumption. }
assert (HP3 : tPR mem3) by (intros a Hp; apply Hpres3; apply HP1; exact Hp).
assert (HSV3 : tSV mem3).
{ apply (ap_sv m mem3); [|exact HSV]. intros a Ha.
  rewrite Hfr by (unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; lia).
  apply HO1; [unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; lia|]. unfold WK.
  unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; lia. }
assert (HX3 : tTB mem3 ap_X2).
{ apply tbn_tTB.
  pose proof (garr8_u_at _ s G 0 6 (kp_garr8_G (ms_mem ms) HK1) ltac:(lia) ltac:(rewrite HGl; lia)) as Hv.
  pose proof (tbn_ws [(48 * disco_table_c.n_of T, 6%nat, disco_table_c.u_at G 0 6)] _ (mrestrict (w_H W) mem3) _ HXn1) as HT.
  cbn [wapply fold_left] in HT. rewrite (reac_disco_table_observe.le_sub G 0 6) in HT by lia. apply HT.
  - unfold wvals. apply Forall_cons; [|apply Forall_nil]. split; [lia|]. split; [cbn [Z.of_nat Pos.of_succ_nat]; lia|].
    intros kk Hk. rewrite <- (Hv kk Hk). apply ap_mb2.
    replace (s + 0 + Z.of_nat kk) with (s + Z.of_nat kk) by lia. exact (Heff (Z.of_nat kk) ltac:(lia)).
  - cbn [wdisj]. split; [intros j _ Hc; inversion Hc | exact I].
  - intros j Hj Hnc. apply (mbyte_of_aview SEGS).
    rewrite Hfr; [reflexivity | lia | | unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; lia].
    intros Hd. apply Hnc. apply Exists_cons_hd. cbv beta iota. change (Z.of_nat 6) with 6. lia. }
assert (P2 : getr regs3 2 = getr (ms_regs ms) 2) by exact (HPR3 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs3 3 = getr (ms_regs ms) 3) by exact (HPR3 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs3 4 = getr (ms_regs ms) 4) by exact (HPR3 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs3 8 = getr (ms_regs ms) 8) by exact (HPR3 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs3 9 = getr (ms_regs ms) 9) by exact (HPR3 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs3 18 = getr (ms_regs ms) 18) by exact (HPR3 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs3 19 = getr (ms_regs ms) 19) by exact (HPR3 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs3 20 = getr (ms_regs ms) 20) by exact (HPR3 20 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs3 22 = getr (ms_regs ms) 22) by exact (HPR3 22 ltac:(unfold acallee_saved; lia)).
apply (ap_c regs3 mem3 md3 FI Hn HJ3 HK3 HP3 HX3 HSV3).
- change (spZ regs3) with (bv_unsigned (getr regs3 2)). rewrite P2. exact Qsp.
- rewrite P3, Rgp. exact E3.
- rewrite P4, Rtp. exact E4.
- rewrite P8, Rs0, E8. reflexivity.
- rewrite P9, Rs1, E9. reflexivity.
- rewrite P18, Rs2, E18. reflexivity.
- rewrite P19, Rs3, E19. reflexivity.
- rewrite P20, Rs4, E20. reflexivity.
- rewrite P22, Rs6, E22. reflexivity.
Qed.
Theorem ap_append : append_stmt.
Proof.
intros regs' m md FI Hn HJ HK HP HX HSV Hsp R3 R4 R8 R9 R18 R20 R21 R22 R23 R24 R25.
rs_hide_all. apply rs_hide in Rnow. unfold rs_hold in Htside.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
destruct Hst as (Hs16 & _).
pose proof Htam as Hamt. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamt.
destruct (ap_st0 regs' m HK HP HX Hn Hsp R8 R21 R22 R23 R24 R25) as [HS SHOK].
pose proof (tTB_tbn m T HX) as HXn.
remember (EK regs' T (disco_table_c.n_of T)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Rt : 0 <= t < 2 ^ 64) by lia.
assert (U8 : bv_unsigned (ew E 8) = t)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl), R8;
      apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 112)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Hsp).
assert (E3 : ew E 3 = getr regs 3)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs 4)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 4 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 t)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 ow)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 s)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 18 18%bv eq_refl); exact R18).
assert (E20 : ew E 20 = Z_to_bv 64 now)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 20 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 SB)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl); exact R22).
assert (E24 : ew E 24 = Z_to_bv 64 (disco_table_c.n_of T))
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 24 24%bv eq_refl); exact R24).
paj_run_tok RUN HS HJ SHOK Bspan;
[ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  eapply awr_ok_cons_gen; [reflexivity | exact U8 | | apply awr_ok_nil];
  cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (Htw a); lia
| ].
pmkst HS.
prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (18%bv : bv 5) Rs2.
prreg HS (20%bv : bv 5) Rs4. prreg HS (22%bv : bv 5) Rs6.
ap_reg HS (10%bv : bv 5) Ra0. ap_reg HS (19%bv : bv 5) Rs3.
ap_rgn HS 0%nat (YP09.mkRegion (Some 8%nat) 384 388 384 388 [YP09.mkChunk 384 (CVal 4 (SOff 24 1))]) RH.
lazymatch type of RH with region_ok _ ?Ex _ _ =>
  assert (X8 : ew Ex 8 = Z_to_bv 64 t) by (cbn [ew ewset extK Nat.eqb]; exact E8);
  assert (X24 : ew Ex 24 = Z_to_bv 64 (disco_table_c.n_of T)) by (cbn [ew ewset extK Nat.eqb]; exact E24);
  assert (XU8 : bv_unsigned (ew Ex 8) = t) by (cbn [ew ewset extK Nat.eqb]; exact U8)
end.
assert (HOA : forall a, 0 <= a < 2 ^ 64 -> ~ (t + 384 <= a < t + 388) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) m a).
{ apply (kept_of_frame (segs := SEGS) _ _ (w_H W) m (ms_mem ms) (fun a => t + 384 <= a < t + 388) HFr).
  intros b_ wlo_ whi_ a_ Hin_ Hr_. vm_compute in Hin_. destruct Hin_ as [Hq_ | []]. injection Hq_ as <- <- <-.
  cbn [base_val ew ewset extK Nat.eqb] in Hr_. rewrite U8 in Hr_. lia. }
assert (HKA : tKP (ms_mem ms)) by (intros a Ha Hs Ht; rewrite HOA by rlia; apply HK; assumption).
assert (HPA : tPR (ms_mem ms)) by (intros a Hp; eapply apresent_grows; [exact HG | apply HP; exact Hp]).
assert (HSVA : tSV (ms_mem ms)).
{ apply (ap_sv m (ms_mem ms)); [|exact HSV]. intros a Ha.
  apply HOA; unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; lia. }
assert (HXA : tbn (mrestrict (w_H W) (ms_mem ms)) ap_XA).
{ pose proof (field_of_region_any (segs := SEGS) _ _ 8 t _ 384 388 384 388 384 4 (SOff 24 1) RH XU8
    ltac:(left; reflexivity) ltac:(cbn; lia)) as Hv.
  rewrite (ap_inc _ X24 Hn) in Hv. change (N.to_nat 4) with 4%nat in Hv.
  pose proof (tbn_ws [(384, 4%nat, disco_table_c.n_of T + 1)] _ (mrestrict (w_H W) (ms_mem ms)) _ HXn) as HT.
  cbn [wapply fold_left] in HT. apply HT.
  - unfold wvals. apply Forall_cons; [|apply Forall_nil]. split; [lia|]. split; [cbn [Z.of_nat Pos.of_succ_nat]; lia|].
    exact Hv.
  - cbn [wdisj]. split; [intros j _ Hc; inversion Hc | exact I].
  - intros j Hj Hnc. apply (mbyte_of_aview SEGS). apply HOA; [lia|].
    intros Hw. apply Hnc. apply Exists_cons_hd. cbv beta iota. change (Z.of_nat 4) with 4. lia. }
assert (Qsp : spZ (ms_regs ms) = spZ regs - 112) by (unfold spZ at 1; rewrite Rsp; exact U2).
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA AS___asan_memset) (AMEMSET fx) W (ms_regs ms) (ms_mem ms)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (t + 48 * disco_table_c.n_of T) 0 48 (spZ regs - 112 - sp0) _ HJ);
  [ rewrite Ra0; exact (ap_dv _ X8 X24 Hn)
  | rewrite Ra1; reflexivity
  | rewrite Ra2; reflexivity
  | rlia | rlia | rlia
  | rewrite Qsp; rlia
  | unfold rs_hold in Hal; rlia | rlia
  | unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; rlia
  | rewrite Rgp, E3; exact Hgp
  | rewrite Rtp, E4; exact Htp
  | exact Rra
  | apply ret_ok_codeptr_v; [rlia | reflexivity]
  | intros a Ha; split; [exact (proj1 (Htw a ltac:(rlia))) | unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; rlia]
  | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; rlia
  | apply (range_addressable_sub _ _ t 400); [exact (kp_ra (ms_mem ms) t 400 HKA ltac:(rlia) Htam ltac:(rlia) Htra) | rlia | rlia]
  | intros _; apply (kp_shv (ms_mem ms) (t + 48 * disco_table_c.n_of T) 48 HKA);
    [ rlia | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; rlia | rlia
    | apply (ap_shv_sub _ t 400); [exact Htsh | rlia | rlia | rlia | rlia] ]
  | exact I ]
| ].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR2 & Ha02 & Heff & Hfr & Hpres2).
cbv beta iota in Heff.
assert (HK2 : tKP mem2).
{ intros a Ha Hs Ht. rewrite Hfr by (unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; rlia). apply HKA; assumption. }
assert (HP2 : tPR mem2) by (intros a Hp; apply Hpres2; apply HPA; exact Hp).
assert (HSV2 : tSV mem2).
{ apply (ap_sv (ms_mem ms) mem2); [|exact HSVA]. intros a Ha.
  apply Hfr; unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; lia. }
assert (HX2 : tTB mem2 ap_X1).
{ apply tbn_tTB.
  pose proof (tbn_ws [(48 * disco_table_c.n_of T, 48%nat, 0)] _ (mrestrict (w_H W) mem2) _ HXA) as HT.
  cbn [wapply fold_left] in HT. apply HT.
  - unfold wvals. apply Forall_cons; [|apply Forall_nil]. split; [lia|]. split; [cbn [Z.of_nat Pos.of_succ_nat]; lia|].
    apply ap_zero_vm. intros i Hi. apply ap_mb_of_av. rewrite (Heff i) by lia. reflexivity.
  - cbn [wdisj]. split; [intros j _ Hc; inversion Hc | exact I].
  - intros j Hj Hnc. apply (mbyte_of_aview SEGS).
    rewrite Hfr; [reflexivity | lia | | unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *; lia].
    intros Hd. apply Hnc. apply Exists_cons_hd. cbv beta iota. change (Z.of_nat 48) with 48. lia. }
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HPR2 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (HPR2 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (HPR2 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (HPR2 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (HPR2 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr (ms_regs ms) 18) by exact (HPR2 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (HPR2 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (HPR2 20 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (HPR2 22 ltac:(unfold acallee_saved; lia)).
apply (ap_b regs2 mem2 md2 FI Hn HJ2 HK2 HP2 HX2 HSV2).
- change (spZ regs2) with (bv_unsigned (getr regs2 2)). rewrite P2. exact Qsp.
- rewrite P3, Rgp. exact E3.
- rewrite P4, Rtp. exact E4.
- rewrite P8, Rs0, E8. reflexivity.
- rewrite P9, Rs1, E9. reflexivity.
- rewrite P18, Rs2, E18. reflexivity.
- rewrite P19, Rs3. exact (ap_dv _ X8 X24 Hn).
- rewrite P20, Rs4, E20. reflexivity.
- rewrite P22, Rs6, E22. reflexivity.
Qed.
Definition loop_stmt : Prop := forall i regs' m md,
  0 <= i < disco_table_c.n_of T ->
  (forall j, 0 <= j < i -> disco_table_c.mac_of T j <> disco_table_c.s_mac G) ->
  tJ m md -> tKP m -> tPR m -> tTB m T -> tSV m -> tOW m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 9 = w64 384 -> getr regs' 18 = w64 s -> getr regs' 20 = w64 now ->
  getr regs' 21 = w64 (t + 384) -> getr regs' 22 = w64 SB -> getr regs' 23 = w64 (2 ^ 64 - 1 - t) ->
  getr regs' 24 = w64 (disco_table_c.n_of T) -> getr regs' 25 = w64 ((t + 384) / 8 + SB) ->
  getr regs' 26 = w64 (48 * i) -> getr regs' 27 = w64 (48 * disco_table_c.n_of T) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x5054)) m (seg_rom SEGS)) md) tQ.
Definition lp_fa : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Definition lp_ss (pc : Z) : sstate := mkSS pc sr_atoms [rK_stk] None lp_fa.
Definition lp_M (m : word -> option byte) : Prop := tKP m /\ tPR m /\ tTB m T /\ tSV m /\ tOW m.
Lemma lp_M_keep : forall m m',
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_DISCO_TABLE_OBSERVE_STK <= a < spZ regs - 112) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) -> lp_M m -> lp_M m'.
Proof.
intros m m' He Hp (HK & HP & [HX HL] & HSV & HOW).
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Htside as Hts. pose proof Ht0 as Ht0'. pose proof Ht63 as Ht63'.
assert (HR : 112 <= REAC_DISCO_TABLE_OBSERVE_STK) by (unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK; lia).
split; [|split; [|split]].
- intros a Ha Hs Ht. rewrite (He a Ha ltac:(lia)). apply HK; assumption.
- intros a Ha. apply Hp, HP, Ha.
- split; [|exact HL]. apply (garr8_aview_kept SEGS (w_H W) (w_H W) m m' t); [|exact HX].
  intros a Ha. rewrite length_map, HL in Ha. apply (He a ltac:(lia) ltac:(lia)).
- apply (sv_keep m m'); [|exact HSV | exact HOW]. intros a Ha. apply (He a ltac:(lia) ltac:(lia)).
Qed.
Lemma lp_ro : forall E rs m1 m2,
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> False) ->
  lp_M m1 -> lp_M m2.
Proof.
intros E rs m1 m2 HF HG Hw HM. apply (lp_M_keep m1 m2); [| intros a Ha; exact (apresent_grows _ _ _ _ HG Ha) | exact HM].
intros a Ha _. apply (kept_of_frame (segs := SEGS) E rs (w_H W) m1 m2 (fun _ => False) HF); [exact Hw | exact Ha | tauto].
Qed.
Lemma lp_st : forall pc regs' m, lp_M m -> spZ regs' = spZ regs - 112 ->
  st_ok_pi SEGS VAL (EK regs' T 0) (lp_ss pc) (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
  sh_ok SEGS BxK [] (EK regs' T 0) (mrestrict (w_H W) m).
Proof.
intros pc regs' m (HK & HP & HX & HSV & HOW) Hsp.
rs_hide_all. apply rs_hide in Rnow.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hlo.
assert (E2 : ew (EK regs' T 0) 2 = getr regs' 2)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ 2 2%bv eq_refl)).
assert (B2 : base_val (EK regs' T 0) (Some 2%nat) = spZ regs - 112) by (cbn [base_val]; rewrite E2; exact Hsp).
rewrite restrict_mkst_fx.
split; [|constructor].
unfold lp_ss. apply pa_entry_st_ok_full.
- unfold EK. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rK_stk, sav_chunks, ckv.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite B2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  all: lazymatch goal with
       | |- chunk_ok _ _ _ _ (YP09.mkChunk 0 _) =>
         apply (chunk_ok_val SEGS _ _ _ 0 8 _ (bv_unsigned (Z_to_bv 64 ow)));
         [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
           rewrite Z.add_0_r; reflexivity
         | pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 ow)) as Hb; unfold bv_modulus in Hb; zside
         | zside | exact HOW ]
       | |- chunk_ok _ _ _ _ (YP09.mkChunk ?o _) =>
         let q := lazymatch o with 104 => constr:(1%bv : bv 5) | 96 => constr:(8%bv : bv 5) | 88 => constr:(9%bv : bv 5)
           | 80 => constr:(18%bv : bv 5) | 72 => constr:(19%bv : bv 5) | 64 => constr:(20%bv : bv 5)
           | 56 => constr:(21%bv : bv 5) | 48 => constr:(22%bv : bv 5) | 40 => constr:(23%bv : bv 5)
           | 32 => constr:(24%bv : bv 5) | 24 => constr:(25%bv : bv 5) | 16 => constr:(26%bv : bv 5)
           | 8 => constr:(27%bv : bv 5) end in
         apply (chunk_ok_val SEGS _ _ _ o 8 _ (bv_unsigned (getr regs q)));
         [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
           rewrite Z.add_0_r; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs q)) as Hb; unfold bv_modulus in Hb; zside
         | zside | apply HSV; cbv [SAVSL In]; clear - Row; tauto ]
       end.
- apply pairwise_disjoint_of_extents. unfold rK_stk, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  unfold lp_fa. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
  change (2 ^ 4) with 16.
  assert (Hm1 : (spZ regs - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
Lemma lp_av_nth : forall m (L : list byte) p j b,
  garr8 SEGS (mrestrict (w_H W) m) p (map (fun b : byte => bv_unsigned b) L) -> nth_error L j = Some b ->
  aview SEGS (w_H W) m (p + Z.of_nat j) = Some (bv_unsigned b).
Proof. intros m L p j b HG Hb. unfold aview. rewrite (garr8_byte _ _ _ _ _ HG Hb). reflexivity. Qed.
Lemma lp_mac : forall m i, 0 <= i < 8 -> lp_M m ->
  ((forall j, 0 <= j < 6 -> aview SEGS (w_H W) m (t + 48 * i + j) = aview SEGS (w_H W) m (s + j)) <->
   disco_table_c.mac_of T i = disco_table_c.s_mac G).
Proof.
intros m i Hi (HK & HP & [HX HL] & _ & _). pose proof (kp_garr8_G m HK) as HGg2.
assert (NT : forall j, (j < 6)%nat -> nth_error (disco_table_c.mac_of T i) j = nth_error T (Z.to_nat (48 * i) + j))
  by (intros j Hj; unfold disco_table_c.mac_of; apply reac_disco_table_observe.nth_sub; [lia | exact Hj]).
assert (NG : forall j, (j < 6)%nat -> nth_error (disco_table_c.s_mac G) j = nth_error G j).
{ intros j Hj. unfold disco_table_c.s_mac. rewrite reac_disco_table_observe.nth_sub by (lia || exact Hj).
  cbn [Z.to_nat Nat.add]. reflexivity. }
assert (LM : length (disco_table_c.mac_of T i) = 6%nat)
  by (unfold disco_table_c.mac_of; apply disco_table.length_sub; [lia | rewrite HL; lia]).
assert (LS : length (disco_table_c.s_mac G) = 6%nat)
  by (unfold disco_table_c.s_mac; apply disco_table.length_sub; [lia | rewrite HGl; lia]).
assert (VT : forall j b, nth_error T (Z.to_nat (48 * i) + j) = Some b ->
  aview SEGS (w_H W) m (t + 48 * i + Z.of_nat j) = Some (bv_unsigned b)).
{ intros j b Hb. replace (t + 48 * i + Z.of_nat j) with (t + Z.of_nat (Z.to_nat (48 * i) + j)) by lia.
  exact (lp_av_nth m T t _ b HX Hb). }
assert (VG : forall j b, nth_error G j = Some b -> aview SEGS (w_H W) m (s + Z.of_nat j) = Some (bv_unsigned b))
  by (intros j b Hb; exact (lp_av_nth m G s j b HGg2 Hb)).
split.
- intros HE. apply nth_error_ext. intros j. destruct (Nat.lt_ge_cases j 6) as [Hj|Hj].
  + rewrite (NT j Hj), (NG j Hj).
    destruct (nth_error T (Z.to_nat (48 * i) + j)) as [b1|] eqn:E1; [|apply nth_error_None in E1; rewrite HL in E1; lia].
    destruct (nth_error G j) as [b2|] eqn:E2; [|apply nth_error_None in E2; rewrite HGl in E2; lia].
    pose proof (HE (Z.of_nat j) ltac:(lia)) as Hq. rewrite (VT j b1 E1), (VG j b2 E2) in Hq.
    injection Hq as Hq. f_equal. apply bv_eq. exact Hq.
  + rewrite (proj2 (nth_error_None (disco_table_c.mac_of T i) j) ltac:(lia)),
      (proj2 (nth_error_None (disco_table_c.s_mac G) j) ltac:(lia)). reflexivity.
- intros HE j Hj. pose proof (NT (Z.to_nat j) ltac:(lia)) as Hn. rewrite HE, (NG (Z.to_nat j) ltac:(lia)) in Hn.
  destruct (nth_error G (Z.to_nat j)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; rewrite HGl in Eb; lia].
  replace j with (Z.of_nat (Z.to_nat j)) by lia. rewrite (VG _ b Eb). exact (VT _ b (eq_sym Hn)).
Qed.
Lemma lp_av_some : forall m (L : list byte) p a,
  garr8 SEGS (mrestrict (w_H W) m) p (map (fun b : byte => bv_unsigned b) L) ->
  p <= a < p + Z.of_nat (length L) -> aview SEGS (w_H W) m a <> None.
Proof.
intros m L p a HG Ha.
destruct (nth_error L (Z.to_nat (a - p))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia. rewrite (lp_av_nth m L p _ b HG Hb). discriminate.
Qed.
Lemma lp_amem_sub : forall p n p' n', amem_range p n -> p <= p' -> p' + n' <= p + n -> 0 <= n' -> amem_range p' n'.
Proof. intros p n p' n' H H1 H2 H3. unfold amem_range in H |- *. clear - H H1 H2 H3. lia. Qed.
Lemma lp_hull_sub : forall rd a n a' n', shadow_hull_vis rd a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> 0 < n' ->
  shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' HV Ha H1 H2 Hn x Hx. apply HV.
assert (M1 : shadow_addr a / 8 <= shadow_addr a' / 8).
{ apply Z.div_le_mono; [clear; lia|]. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; [clear; lia | exact H1]. }
assert (M2 : shadow_addr (a' + n' - 1) / 8 <= shadow_addr (a + n - 1) / 8).
{ apply Z.div_le_mono; [clear; lia|]. unfold shadow_addr. apply Z.add_le_mono_l.
  apply Z.div_le_mono; [clear; lia | clear - H2; lia]. }
revert Hx M1 M2.
generalize (shadow_addr a / 8) (shadow_addr a' / 8) (shadow_addr (a' + n' - 1) / 8) (shadow_addr (a + n - 1) / 8).
intros z1 z2 z3 z4 Hx M1 M2. clear - Hx M1 M2. lia.
Qed.
Lemma lp_prs : forall r1 r2 : bvmap 5 word, aregs_preserved r1 r2 ->
  getr r2 2 = getr r1 2 /\ getr r2 3 = getr r1 3 /\ getr r2 4 = getr r1 4 /\ getr r2 8 = getr r1 8 /\
  getr r2 9 = getr r1 9 /\ getr r2 18 = getr r1 18 /\ getr r2 19 = getr r1 19 /\ getr r2 20 = getr r1 20 /\
  getr r2 21 = getr r1 21 /\ getr r2 22 = getr r1 22 /\ getr r2 23 = getr r1 23 /\ getr r2 24 = getr r1 24 /\
  getr r2 25 = getr r1 25 /\ getr r2 26 = getr r1 26 /\ getr r2 27 = getr r1 27.
Proof.
intros r1 r2 H.
split; [exact (H 2 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 3 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 4 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 8 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 9 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 18 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 19 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 20 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 21 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 22 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 23 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 24 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 25 ltac:(unfold acallee_saved; lia))|].
split; [exact (H 26 ltac:(unfold acallee_saved; lia)) | exact (H 27 ltac:(unfold acallee_saved; lia))].
Qed.
Definition lp_cont (i : Z) : Prop := forall regs2 m2 md2 (v : word),
  tJ m2 md2 -> lp_M m2 ->
  getr regs2 10 = v -> (v = w64 0 <-> disco_table_c.mac_of T i = disco_table_c.s_mac G) ->
  spZ regs2 = spZ regs - 112 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = w64 t -> getr regs2 9 = w64 384 -> getr regs2 18 = w64 s -> getr regs2 19 = w64 (t + 48 * i) ->
  getr regs2 20 = w64 now -> getr regs2 21 = w64 (t + 384) -> getr regs2 22 = w64 SB ->
  getr regs2 23 = w64 (2 ^ 64 - 1 - t) -> getr regs2 24 = w64 (disco_table_c.n_of T) ->
  getr regs2 25 = w64 ((t + 384) / 8 + SB) -> getr regs2 26 = w64 (48 * i) ->
  getr regs2 27 = w64 (48 * disco_table_c.n_of T) ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x5070)) m2 (seg_rom SEGS)) md2) tQ.
Ltac lp_awr := lazymatch goal with |- awr_ok ?E ?rs ?a ?b ?c ?d ?e ?f ?g =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' a b c d e f g) end;
  repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia |]].
Ltac lp_win := let b_ := fresh in let wlo_ := fresh in let whi_ := fresh in let a_ := fresh in
  let Hin_ := fresh in let Hr_ := fresh in
  intros b_ wlo_ whi_ a_ Hin_ Hr_; vm_compute in Hin_;
  repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val] in Hr_; first [clear - Hr_; lia | lia] |]); destruct Hin_.
Tactic Notation "lp_ea" constr(HE) constr(n) constr(q) ident(H) :=
  lazymatch type of HE with ?E = EK ?a ?b ?c =>
    assert (H : ew E n = getr a q)
      by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat a _ n q eq_refl)) end.
Lemma lp_pre : forall i regs' m md, 0 <= i < disco_table_c.n_of T ->
  tJ m md -> lp_M m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 9 = w64 384 -> getr regs' 18 = w64 s -> getr regs' 20 = w64 now ->
  getr regs' 21 = w64 (t + 384) -> getr regs' 22 = w64 SB -> getr regs' 23 = w64 (2 ^ 64 - 1 - t) ->
  getr regs' 24 = w64 (disco_table_c.n_of T) -> getr regs' 25 = w64 ((t + 384) / 8 + SB) ->
  getr regs' 26 = w64 (48 * i) -> getr regs' 27 = w64 (48 * disco_table_c.n_of T) ->
  lp_cont i ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x5054)) m (seg_rom SEGS)) md) tQ.
Proof.
intros i regs' m md Hi HJ HM Hsp R3 R4 R8 R9 R18 R20 R21 R22 R23 R24 R25 R26 R27 HC.
rs_hide_all. apply rs_hide in Rnow.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Htside as Hts. pose proof Hsside as Hss. pose proof Htam as Hamt. pose proof Hsam as Hams.
unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hlo, Hts, Hss.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamt, Hams.
assert (Hn8 : disco_table_c.n_of T <= 8) by (unfold disco_table_c.tbl_T1 in HT1; lia).
destruct (lp_st 0x5054 regs' m HM Hsp) as [HS SHOK].
remember (EK regs' T 0) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
lp_ea HE 2%nat (2%bv : bv 5) E2. lp_ea HE 3%nat (3%bv : bv 5) E3. lp_ea HE 4%nat (4%bv : bv 5) E4.
lp_ea HE 8%nat (8%bv : bv 5) E8. lp_ea HE 9%nat (9%bv : bv 5) E9. lp_ea HE 18%nat (18%bv : bv 5) E18.
lp_ea HE 20%nat (20%bv : bv 5) E20. lp_ea HE 21%nat (21%bv : bv 5) E21. lp_ea HE 22%nat (22%bv : bv 5) E22.
lp_ea HE 23%nat (23%bv : bv 5) E23. lp_ea HE 24%nat (24%bv : bv 5) E24. lp_ea HE 25%nat (25%bv : bv 5) E25.
lp_ea HE 26%nat (26%bv : bv 5) E26. lp_ea HE 27%nat (27%bv : bv 5) E27.
assert (U8 : U E (SOff 8 0) = t) by (apply U_atom; [rewrite E8, R8; reflexivity | lia]).
assert (U9 : U E (SOff 9 0) = 384) by (apply U_atom; [rewrite E9, R9; reflexivity | lia]).
assert (U26 : U E (SOff 26 0) = 48 * i) by (apply U_atom; [rewrite E26, R26; reflexivity | lia]).
assert (U23 : U E (SOff 23 0) = 2 ^ 64 - 1 - t) by (apply U_atom; [rewrite E23, R23; reflexivity | lia]).
paj_run_tok RUN HS HJ SHOK Bspan; [lp_awr|].
pose proof (lp_ro _ _ _ _ HFr HG ltac:(lp_win) HM) as HM1. clear HM HF HFr HG. rename HM1 into HM.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite branch_eq_U, U26, U9 in Hc. apply Z.eqb_eq in Hc. lia.
- clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [lp_awr|].
  pose proof (lp_ro _ _ _ _ HFr HG ltac:(lp_win) HM) as HM1. clear HM HF HFr HG. rename HM1 into HM.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite branch_ltu_U, U23, U26 in Hc. apply Z.ltb_lt in Hc. lia.
  + clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan; [lp_awr|].
    pose proof (lp_ro _ _ _ _ HFr HG ltac:(lp_win) HM) as HM1. clear HM HF HFr HG. rename HM1 into HM.
    repeat rewrite wvb_collapse in HJ.
    prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
    prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
    prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
    prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    assert (Rsum : forall rr : bv 5, getr (ms_regs ms1) rr = alu64 ALU_ADD (ew E 8) (ew E 26) ->
      getr (ms_regs ms1) rr = w64 (t + 48 * i)).
    { intros rr Hrr. rewrite Hrr, E8, E26, R8, R26.
      change (w64 t) with (Z_to_bv 64 t). change (w64 (48 * i)) with (Z_to_bv 64 (48 * i)).
      change (w64 (t + 48 * i)) with (Z_to_bv 64 (t + 48 * i)).
      rewrite zalu64_sound. f_equal. unfold zalu64, zcanon, M64. cbn [zalu_raw].
      rewrite (Z.mod_small t) by lia. rewrite (Z.mod_small (48 * i)) by lia. apply Z.mod_small. lia. }
    apply Rsum in Ra0. apply Rsum in Q19. clear Rsum.
    rewrite E18, R18 in Ra1. rewrite E2 in Q2. rewrite E3, R3 in Q3. rewrite E4, R4 in Q4.
    rewrite E8, R8 in Q8. rewrite E9, R9 in Q9. rewrite E18, R18 in Q18. rewrite E20, R20 in Q20.
    rewrite E21, R21 in Q21. rewrite E22, R22 in Q22. rewrite E23, R23 in Q23. rewrite E24, R24 in Q24.
    rewrite E25, R25 in Q25. rewrite E26, R26 in Q26. rewrite E27, R27 in Q27.
    assert (Hsp1 : spZ (ms_regs ms1) = spZ regs - 112) by (unfold spZ; rewrite Q2; exact Hsp).
    pose proof HM as (HK & HP & [HX HL] & HSV & HOW).
    pose proof (kp_garr8_G (ms_mem ms1) HK) as HGm.
    pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
    destruct Hst as (Hsp16 & _).
    assert (Ho16 : (spZ regs - 112 - sp0) mod 16 = 0).
    { pose proof (proj1 (Z.mod_divide _ 16 ltac:(lia)) Hal) as [a1 Ha1].
      pose proof (proj1 (Z.mod_divide _ 16 ltac:(lia)) Hsp16) as [b1 Hb1].
      apply Z.mod_divide; [lia|]. exists (a1 - 7 - b1). lia. }
    assert (Rti : 0 <= t + 48 * i /\ t + 48 * i + 6 <= 2 ^ 63) by lia.
    pmkst HS.
    eapply SRr_bind;
    [ eapply (aj_bcmp_at (fx := fx) SEGS B LAWS Hsegs (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fx) W
        (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
        (t + 48 * i) s 6 (spZ regs - 112 - sp0) (Z_to_bv 64 (BASE + 0x5070)) HJ)
    | ].
    { exact Ra0. }
    { exact Ra1. }
    { exact Ra2. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { rewrite Hsp1. lia. }
    { exact Ho16. }
    { lia. }
    { unfold REAC_DISCO_TABLE_OBSERVE_STK in Hwin. lia. }
    { rewrite Q3. exact Hgp. }
    { rewrite Q4. exact Htp. }
    { exact Rra. }
    { apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { intros a Ha. split.
      - apply (lp_av_some (ms_mem ms1) T t a HX). rewrite HL. cbn [Z.of_nat]. lia.
      - rewrite Hsp1. unfold rs_hold in Hts. unfold ESTACK. rlia. }
    { intros a Ha. split.
      - apply (lp_av_some (ms_mem ms1) G s a HGm). rewrite HGl. cbn [Z.of_nat]. lia.
      - rewrite Hsp1. unfold rs_hold in Hss. unfold ESTACK. rlia. }
    { intros a Ha. unfold rs_hold in Hts. unfold ESTACK. rlia. }
    { intros a Ha. unfold rs_hold in Hss. unfold ESTACK. rlia. }
    { apply (lp_amem_sub t 400); [exact Htam | lia | lia | lia]. }
    { apply (lp_amem_sub s 24); [exact Hsam | lia | lia | lia]. }
    { apply (kp_ra (ms_mem ms1) (t + 48 * i) 6 HK ltac:(lia)
        ltac:(apply (lp_amem_sub t 400); [exact Htam | lia | lia | lia]) ltac:(lia)).
      apply (range_addressable_sub _ _ t 400); [exact Htra | lia | lia]. }
    { intros _. apply (kp_shv (ms_mem ms1) (t + 48 * i) 6 HK ltac:(lia)
        ltac:(apply (lp_amem_sub t 400); [exact Htam | lia | lia | lia]) ltac:(lia)).
      apply (lp_hull_sub _ t 400); [exact Htsh | lia | lia | lia | lia]. }
    { apply (kp_ra (ms_mem ms1) s 6 HK ltac:(lia)
        ltac:(apply (lp_amem_sub s 24); [exact Hsam | lia | lia | lia]) ltac:(lia)).
      apply (range_addressable_sub _ _ s 24); [exact Hsra | lia | lia]. }
    { intros _. apply (kp_shv (ms_mem ms1) s 6 HK ltac:(lia)
        ltac:(apply (lp_amem_sub s 24); [exact Hsam | lia | lia | lia]) ltac:(lia)).
      apply (lp_hull_sub _ s 24); [exact Hssh | lia | lia | lia | lia]. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
    destruct (lp_prs _ _ HP2) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    apply (HC regs2 mem2 md2 v).
    * exact HJ2.
    * apply (lp_M_keep (ms_mem ms1) mem2); [| exact Hpres2 | exact HM].
      intros a Ha Hn. apply Hfr2; [exact Ha|]. unfold REAC_DISCO_TABLE_OBSERVE_STK in Hn. rlia.
    * exact Hv.
    * split; intros HH.
      ** apply (proj1 (lp_mac (ms_mem ms1) i ltac:(lia) HM)). apply (proj1 Hcmp). exact HH.
      ** apply (proj2 Hcmp). apply (proj2 (lp_mac (ms_mem ms1) i ltac:(lia) HM)). exact HH.
    * unfold spZ. rewrite P2. exact Hsp1.
    * rewrite P3. exact Q3.
    * rewrite P4. exact Q4.
    * rewrite P8. exact Q8.
    * rewrite P9. exact Q9.
    * rewrite P18. exact Q18.
    * rewrite P19. exact Q19.
    * rewrite P20. exact Q20.
    * rewrite P21. exact Q21.
    * rewrite P22. exact Q22.
    * rewrite P23. exact Q23.
    * rewrite P24. exact Q24.
    * rewrite P25. exact Q25.
    * rewrite P26. exact Q26.
    * rewrite P27. exact Q27.
Qed.
Lemma lp_beq : forall E' n (v : word), ew E' n = v ->
  (branch_taken BC_EQ (sv_denot E' (SOff n 0)) (sv_denot E' (SLit 0)) = true <-> v = w64 0).
Proof.
intros E' n v H. rewrite branch_eq_U, U_SOff, U_lit by lia. rewrite H, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 v) as Hv. change (bv_modulus 64) with (2 ^ 64) in Hv.
rewrite zcanon_id by (unfold M64; lia). rewrite Z.eqb_eq.
change (w64 0) with (Z_to_bv 64 0). rewrite bv_eq, (unsigned_lit_small 0) by lia. reflexivity.
Qed.
Lemma lp_blt : forall E' n c u, ew E' n = Z_to_bv 64 u -> 0 <= u < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E' (SOff n 0)) (sv_denot E' (SLit c)) = (u <? c).
Proof.
intros E' n c u H Hu Hc. cbn [branch_taken]. unfold bv_lts.
change (bv_signed (sv_denot E' (SOff n 0))) with (Sg E' (SOff n 0)).
change (bv_signed (sv_denot E' (SLit c))) with (Sg E' (SLit c)).
rewrite S_SOff, S_SLit, H, Z.add_0_r, unsigned_lit_small by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (u + 2 ^ 63)) by lia. rewrite (Z.mod_small (c + 2 ^ 63)) by lia.
replace (u + 2 ^ 63 - 2 ^ 63) with u by lia. replace (c + 2 ^ 63 - 2 ^ 63) with c by lia. reflexivity.
Qed.
Lemma lp_full_mod : forall X2 ret,
  (forall j, 0 <= j < disco_table_c.n_of T -> disco_table_c.mac_of T j <> disco_table_c.s_mac G) ->
  8 <= disco_table_c.n_of T -> (X2, ret) = reac_disco_table_observe_c.observe_full T ->
  reac_disco_table_observe_c.observe_model T G ow now X2 ret.
Proof.
intros X2 ret NF Hn HX. exists (-1). split; [left; split; [reflexivity | exact NF]|].
right; left. split; [reflexivity|]. split; [exact Hn | exact HX].
Qed.
Lemma lp_sw0 : forall u, 0 <= u < 2 ^ 32 -> (bv_swrap 32 u =? 0) = (u =? 0).
Proof.
intros u Hu. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.eqb_spec u 0) as [->|Hn]; [reflexivity|]. apply Z.eqb_neq.
destruct (Z.ltb_spec u (2 ^ 31)).
- rewrite Z.mod_small by lia. lia.
- rewrite <- (Z.mod_add _ (-1) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Definition lp_at (i : Z) : Prop := forall regs' m md,
  0 <= i < disco_table_c.n_of T ->
  (forall j, 0 <= j < i -> disco_table_c.mac_of T j <> disco_table_c.s_mac G) ->
  tJ m md -> lp_M m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 9 = w64 384 -> getr regs' 18 = w64 s -> getr regs' 20 = w64 now ->
  getr regs' 21 = w64 (t + 384) -> getr regs' 22 = w64 SB -> getr regs' 23 = w64 (2 ^ 64 - 1 - t) ->
  getr regs' 24 = w64 (disco_table_c.n_of T) -> getr regs' 25 = w64 ((t + 384) / 8 + SB) ->
  getr regs' 26 = w64 (48 * i) -> getr regs' 27 = w64 (48 * disco_table_c.n_of T) ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x5054)) m (seg_rom SEGS)) md) tQ.
Definition lp_fa6 : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 8 (2 ^ 47 - 401) 3);
    (19%nat, mkAF 8 (2 ^ 47 - 49) 3); (22%nat, mkAF SB SB 0);
    (46%nat, AF32); (47%nat, AF32); (48%nat, AF32);
    (49%nat, AF32); (50%nat, AF8); (51%nat, AF8); (52%nat, AF8); (53%nat, AF8); (54%nat, AF8);
    (55%nat, AF32); (56%nat, AF32) ] [] [].
Definition lp_ss6 (pc : Z) : sstate := mkSS pc sr_atoms rg_K6 None lp_fa6.
Lemma lp_st6 : forall pc regs' m X r,
  tKP m -> tPR m -> tTB m X -> tSV m -> tOW m -> 0 <= r < 8 ->
  spZ regs' = spZ regs - 112 -> getr regs' 8 = w64 t ->
  getr regs' 19 = w64 (t + 48 * r) -> getr regs' 22 = w64 SB ->
  st_ok_pi SEGS VAL (EK regs' X r) (lp_ss6 pc) (restrict (w_H W) (mkst regs' (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))) /\
  sh_ok SEGS BxK SH_K6 (EK regs' X r) (mrestrict (w_H W) m).
Proof.
intros pc regs' m X r HK HP [HX HXl] HSV HOW Hr Hsp R8 R19 R22.
rs_hide_all. apply rs_hide in Rnow.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Htam as Hamt. pose proof Hsam as Hams. pose proof Htside as Hts. pose proof Hsside as Hss.
unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hlo, Hts, Hss.
assert (E2 : ew (EK regs' X r) 2 = getr regs' 2)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs' _ 2 2%bv eq_refl)).
assert (E8 : ew (EK regs' X r) 8 = Z_to_bv 64 t)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl); exact R8).
assert (E19 : ew (EK regs' X r) 19 = Z_to_bv 64 (t + 48 * r))
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl); exact R19).
assert (E22 : ew (EK regs' X r) 22 = Z_to_bv 64 SB)
  by (unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl); exact R22).
assert (VB : forall n v, ew (EK regs' X r) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val (EK regs' X r) (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (B2 : base_val (EK regs' X r) (Some 2%nat) = spZ regs - 112) by (cbn [base_val]; rewrite E2; exact Hsp).
assert (Rt : 0 <= t < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Re : 0 <= t + 48 * r < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Hwr : forall a, t <= a < t + 400 -> writable_at SEGS (mrestrict (w_H W) m) a).
{ intros a Ha. apply (apresent_writable SEGS). apply HP. exact (proj2 (Htw a Ha)). }
assert (UA : forall o w, 0 <= o -> o + Z.of_nat w <= 400 ->
  val_mem SEGS (mrestrict (w_H W) m) (t + o) w (disco_table_c.u_at X o w)).
{ intros o w Ho Hw. apply garr8_u_at; [exact HX | exact Ho | rewrite HXl; exact Hw]. }
assert (UR : forall bs o w, 0 <= disco_table_c.u_at bs o w < 2 ^ (8 * Z.of_N (N.of_nat w))).
{ intros bs o w. rewrite nat_N_Z. apply reac_disco_table_observe.u_at_range. }
rewrite restrict_mkst_fx.
split.
- unfold lp_ss6. apply pa_entry_st_ok_full.
  + unfold EK. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rg_K6, rK_stk, rK_head, rK_ent, sav_chunks, ckv.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite B2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with
           | |- chunk_ok _ _ _ _ (YP09.mkChunk 0 _) =>
             apply (chunk_ok_val SEGS _ _ _ 0 8 _ (bv_unsigned (Z_to_bv 64 ow)));
             [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
               rewrite Z.add_0_r; reflexivity
             | pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 ow)) as Hb; unfold bv_modulus in Hb; zside
             | zside | exact HOW ]
           | |- chunk_ok _ _ _ _ (YP09.mkChunk ?o _) =>
             let q := lazymatch o with 104 => constr:(1%bv : bv 5) | 96 => constr:(8%bv : bv 5) | 88 => constr:(9%bv : bv 5)
               | 80 => constr:(18%bv : bv 5) | 72 => constr:(19%bv : bv 5) | 64 => constr:(20%bv : bv 5)
               | 56 => constr:(21%bv : bv 5) | 48 => constr:(22%bv : bv 5) | 40 => constr:(23%bv : bv 5)
               | 32 => constr:(24%bv : bv 5) | 24 => constr:(25%bv : bv 5) | 16 => constr:(26%bv : bv 5)
               | 8 => constr:(27%bv : bv 5) end in
             apply (chunk_ok_val SEGS _ _ _ o 8 _ (bv_unsigned (getr regs q)));
             [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
               rewrite Z.add_0_r; reflexivity
             | pose proof (bv_unsigned_in_range 64 (getr regs q)) as Hb; unfold bv_modulus in Hb; zside
             | zside | apply HSV; cbv [SAVSL In]; clear - Row; tauto ]
           end.
    * rewrite (VB 8%nat t E8 Rt). split; [lia|]. split; [lia|].
      split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?w _)) =>
        apply (chunk_ok_val SEGS _ _ _ o w _ (disco_table_c.u_at X o (N.to_nat w)));
        [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (UR X o (N.to_nat w)) as Hb; rewrite N2Nat.id in Hb; exact Hb
        | zside | apply UA; zside ] end.
    * rewrite (VB 19%nat (t + 48 * r) E19 Re). split; [lia|]. split; [lia|].
      split; [intros o Ho; apply Hwr; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?w _)) =>
        apply (chunk_ok_val SEGS _ _ _ o w _ (disco_table_c.u_at X (48 * r + o) (N.to_nat w)));
        [ cbn [sv_denot]; unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map];
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (UR X (48 * r + o) (N.to_nat w)) as Hb; rewrite N2Nat.id in Hb; exact Hb
        | zside | replace (t + 48 * r + o) with (t + (48 * r + o)) by lia; apply UA; zside ] end.
  + apply pairwise_disjoint_of_extents. unfold rg_K6, rK_stk, rK_head, rK_ent, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2, (VB 8%nat t E8 Rt), (VB 19%nat (t + 48 * r) E19 Re).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold rs_hold in Hts. unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in *. repeat split; rlia.
  + split; [|split; [exact I | exact I]].
    unfold lp_fa6, AF32, AF8. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E19, E22. change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp.
    rewrite !unsigned_lit_small by (unfold SB; lia).
    unfold EK, Eimg, Ereg, xK, A_TEXT, A_LIM; cbn [ew Nat.leb Nat.ltb andb Nat.sub nth map].
    rewrite !unsigned_lit_small by (first [apply UR | pose proof (UR X 384 4) as U0; cbn in U0; lia
      | lazymatch goal with |- 0 <= disco_table_c.u_at ?bs ?o ?w < _ => pose proof (UR bs o w) as U0; cbn in U0; lia end]).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm1 : (spZ regs - 112) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
    assert (Hm2 : (t + 48 * r) mod 8 = 0) by (rewrite Zplus_mod, Ht8, Zmult_mod; reflexivity).
    assert (Ht8' : 8 <= t) by (pose proof (Z.div_mod t 8 ltac:(lia)) as Hd; rewrite Ht8 in Hd; lia).
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamt, Hams.
    repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- context [disco_table_c.u_at ?bs ?o ?w] => pose proof (UR bs o w) as U0; cbn in U0; rlia end
          | lazymatch goal with |- context [SB] => unfold SB; rlia end | rlia ].
- unfold sh_ok, SH_K6. repeat apply Forall_cons; try apply Forall_nil; unfold shent_ok, app_apart, BxK;
  cbn [she_m she_lo she_hi].
  all: rewrite (U_atom _ 22 SB E22) by (unfold SB; lia).
  + rewrite (U_atom _ 8 t E8) by lia. split.
    * replace (t + 0) with t by lia. replace (400 - 0) with 400 by lia.
      exact (kp_ra m t 400 HK ltac:(lia) Htam ltac:(lia) Htra).
    * intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
  + rewrite (U_atom _ 19 (t + 48 * r) E19) by lia. split.
    * replace (t + 48 * r + 0) with (t + 48 * r) by lia. replace (48 - 0) with 48 by lia.
      apply (range_addressable_sub _ _ t 400); [exact (kp_ra m t 400 HK ltac:(lia) Htam ltac:(lia) Htra) | lia | lia].
    * intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
Qed.
Lemma lp_full : forall regs' m md,
  disco_table_c.n_of T = 8 ->
  (forall j, 0 <= j < disco_table_c.n_of T -> disco_table_c.mac_of T j <> disco_table_c.s_mac G) ->
  tJ m md -> lp_M m ->
  spZ regs' = spZ regs - 112 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = w64 t -> getr regs' 19 = w64 (t + 48 * 7) -> getr regs' 22 = w64 SB ->
  SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x5088)) m (seg_rom SEGS)) md) tQ.
Proof.
intros regs' m md Hn NF HJ (HK & HP & HX & HSV & HOW) Hsp R3 R4 R8 R19 R22.
rs_hide_all. apply rs_hide in Rnow.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (Hr8 : 0 <= 7 < 8) by lia.
destruct (lp_st6 0x5088 regs' m T 7 HK HP HX HSV HOW Hr8 Hsp R8 R19 R22) as [HS SHOK].
pose proof (tTB_tbn m T HX) as HXn.
assert (HO : forall a, 0 <= a < 2 ^ 64 -> ~ WK 7 a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m a) by reflexivity.
assert (HXl : length T = 400%nat) by exact HTl.
remember (EK regs' T 7) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Rt : 0 <= t < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia).
assert (U8 : bv_unsigned (ew E 8) = t)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl), R8;
      apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = t + 48 * 7)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl), R19;
      apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 112)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Hsp).
assert (E3 : ew E 3 = getr regs 3)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 3 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = getr regs 4)
  by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs' _ 4 4%bv eq_refl); exact R4).
ekall HE.
paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
destruct (run_mem _ _ 7 m m _ Hr8 HFr HG ltac:(kwin U8 U19) HK HP HO) as (HK1 & HP1 & HO1). clear HF HFr HG.
assert (Ru : 0 <= disco_table_c.u_at T 388 4 < 2 ^ 32) by apply reac_disco_table_observe.u32_range.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite branch_ne_U, <- branch_eq_U, (br_s32z _ 47 _ ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ47) Ru) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hov.
  paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ 7 m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  kfin T T 7 0 HO2 HK2 HP2 HXn HXl Hr8 U8 U19 U2 E3 E4.
  + intros j Hj Hw. split; [apply (mbyte_of_aview SEGS); apply HO2; [lia | exact Hw] | reflexivity].
  + kchunks.
  + apply lp_full_mod; [exact NF | lia |].
    unfold reac_disco_table_observe_c.observe_full, disco_table_c.ov_of, disco_table_c.s32_at.
    rewrite (lp_sw0 _ Ru). replace (disco_table_c.u_at T 388 4 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hov).
    reflexivity.
- rewrite branch_ne_U, <- branch_eq_U, (br_s32z _ 47 _ ltac:(cbn [ew ewset extK Nat.eqb]; exact EQ47) Ru) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hov.
  paj_run_tok RUN HS HJ SHOK Bspan; [awrK U8 U19 Hr8|].
  destruct (run_mem _ _ 7 m _ _ Hr8 HFr HG ltac:(kwin U8 U19) HK1 HP1 HO1) as (HK2 & HP2 & HO2). clear HF HFr HG.
  kfin T (disco_table_c.upd (disco_table_c.upd T 388 (Z_to_le_bytes 4 1)) 392
         (Z_to_le_bytes 4 (disco_table_c.seq_of T + 1))) 7 0 HO2 HK2 HP2 HXn HXl Hr8 U8 U19 U2 E3 E4.
  + intros j Hj Hw. split; [apply (mbyte_of_aview SEGS); apply HO2; [lia | exact Hw] |].
    rewrite nth_upd_out; [| lia | mvl; lia | mvl; rewrite ?HXl; lia | mvl; unfold WK in Hw; first [clear - Hw Hj; LiaTwx2.zify_noeuclid; xlia zchecker | rlia]].
    rewrite nth_upd_out; [reflexivity | lia | mvl; lia | rewrite HXl; lia | mvl; unfold WK in Hw; first [clear - Hw Hj; LiaTwx2.zify_noeuclid; xlia zchecker | rlia]].
  + kchunks.
    all: first
      [ rewrite (seq_val _ 48 (disco_table_c.u_at T 392 4))
          by (first [cbn [ew ewset extK Nat.eqb]; exact EQ48 | apply reac_disco_table_observe.u32_range]);
        rewrite (OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.Z_to_le_bytes_mod 4 _ 32) by lia;
        apply reac_disco_table_observe.mf_sub_upd_at; mvl; lia
      | cbn [sv_denot]; rewrite unsigned_lit_small by lia; change (8 * 4) with 32; rewrite Z.mod_small by lia;
        msub; apply reac_disco_table_observe.mf_sub_upd_at; mvl; lia ].
  + apply lp_full_mod; [exact NF | lia |].
    unfold reac_disco_table_observe_c.observe_full, disco_table_c.ov_of, disco_table_c.s32_at.
    rewrite (lp_sw0 _ Ru), Hov. reflexivity.
Qed.
Ltac lp_after := match goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _, HM : lp_M _ |- _ =>
  let HM1 := fresh "HM" in pose proof (lp_ro _ _ _ _ HFr HG ltac:(lp_win) HM) as HM1; clear HM HFr HG;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end end;
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => repeat rewrite wvb_collapse in HJ end.
Lemma lp_post : k1_stmt -> append_stmt -> forall i regs2 m2 md2 (v : word),
  0 <= i < disco_table_c.n_of T ->
  (forall j, 0 <= j < i -> disco_table_c.mac_of T j <> disco_table_c.s_mac G) ->
  (i + 1 < disco_table_c.n_of T -> lp_at (i + 1)) ->
  tJ m2 md2 -> lp_M m2 ->
  getr regs2 10 = v -> (v = w64 0 <-> disco_table_c.mac_of T i = disco_table_c.s_mac G) ->
  spZ regs2 = spZ regs - 112 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = w64 t -> getr regs2 9 = w64 384 -> getr regs2 18 = w64 s -> getr regs2 19 = w64 (t + 48 * i) ->
  getr regs2 20 = w64 now -> getr regs2 21 = w64 (t + 384) -> getr regs2 22 = w64 SB ->
  getr regs2 23 = w64 (2 ^ 64 - 1 - t) -> getr regs2 24 = w64 (disco_table_c.n_of T) ->
  getr regs2 25 = w64 ((t + 384) / 8 + SB) -> getr regs2 26 = w64 (48 * i) ->
  getr regs2 27 = w64 (48 * disco_table_c.n_of T) ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x5070)) m2 (seg_rom SEGS)) md2) tQ.
Proof.
intros K1 AP i regs2 m2 md2 v Hi NP IH HJ HM Hv Hiff Hsp R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
rs_hide_all. apply rs_hide in Rnow.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (Hn8 : disco_table_c.n_of T <= 8) by (unfold disco_table_c.tbl_T1 in HT1; lia).
pose proof Htam as Hamt. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamt.
destruct (lp_st 0x5070 regs2 m2 HM Hsp) as [HS SHOK].
remember (EK regs2 T 0) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
lp_ea HE 2%nat (2%bv : bv 5) E2. lp_ea HE 3%nat (3%bv : bv 5) E3. lp_ea HE 4%nat (4%bv : bv 5) E4.
lp_ea HE 8%nat (8%bv : bv 5) E8. lp_ea HE 9%nat (9%bv : bv 5) E9. lp_ea HE 10%nat (10%bv : bv 5) E10.
lp_ea HE 18%nat (18%bv : bv 5) E18. lp_ea HE 19%nat (19%bv : bv 5) E19.
lp_ea HE 20%nat (20%bv : bv 5) E20. lp_ea HE 21%nat (21%bv : bv 5) E21. lp_ea HE 22%nat (22%bv : bv 5) E22.
lp_ea HE 23%nat (23%bv : bv 5) E23. lp_ea HE 24%nat (24%bv : bv 5) E24. lp_ea HE 25%nat (25%bv : bv 5) E25.
lp_ea HE 26%nat (26%bv : bv 5) E26. lp_ea HE 27%nat (27%bv : bv 5) E27.
ekq HE 32%nat EQ32.
assert (Ev : ew E 10 = v) by (rewrite E10; exact Hv).
psrr_branch_tok RUN BR HS SHOK Bspan.
- assert (Hm : disco_table_c.mac_of T i = disco_table_c.s_mac G)
    by (apply Hiff; apply (proj1 (lp_beq E 10 v Ev)); exact Hc).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x52a8; [lp_awr|]. lp_after.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  lazymatch goal with HM : lp_M _ |- _ => destruct HM as (HK & HP & HX & HSV & HOW) end.
  eapply (K1 i); [exact Hi | right; split; [exact Hi | split; [exact Hm | exact NP]] | exact HJ | exact HK | exact HP
    | exact HX | exact HSV | exact HOW | | | | | | | | ].
  + unfold spZ. rewrite Q2, E2. exact Hsp.
  + rewrite Q3, E3. exact R3.
  + rewrite Q4, E4. exact R4.
  + rewrite Q8, E8. exact R8.
  + rewrite Q18, E18. exact R18.
  + rewrite Q19, E19. exact R19.
  + rewrite Q20, E20. exact R20.
  + rewrite Q22, E22. exact R22.
- assert (NE : disco_table_c.mac_of T i <> disco_table_c.s_mac G).
  { intros Hm. apply (proj2 Hiff) in Hm. apply (proj2 (lp_beq E 10 v Ev)) in Hm. rewrite Hm in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [lp_awr|]. lp_after.
  assert (U27 : U E (SOff 27 0) = 48 * disco_table_c.n_of T) by (apply U_atom; [rewrite E27, R27; reflexivity | lia]).
  assert (U26 : U E (SOff 26 48) = 48 * i + 48) by (apply U_atom_off; [rewrite E26, R26; reflexivity | lia | lia]).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite branch_ne_U, U27, U26 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    assert (Hlt : i + 1 < disco_table_c.n_of T) by rlia.
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5054; [lp_awr|]. lp_after.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
    prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
    prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    assert (NP1 : forall j, 0 <= j < i + 1 -> disco_table_c.mac_of T j <> disco_table_c.s_mac G)
      by (intros j Hj; destruct (Z.eq_dec j i) as [->|Hji]; [exact NE | apply NP; rlia]).
    lazymatch goal with HM : lp_M _ |- _ => eapply (IH Hlt _ _ _ ltac:(lia) NP1 HJ HM) end.
    * unfold spZ. rewrite Q2, E2. exact Hsp.
    * rewrite Q3, E3. exact R3.
    * rewrite Q4, E4. exact R4.
    * rewrite Q8, E8. exact R8.
    * rewrite Q9, E9. exact R9.
    * rewrite Q18, E18. exact R18.
    * rewrite Q20, E20. exact R20.
    * rewrite Q21, E21. exact R21.
    * rewrite Q22, E22. exact R22.
    * rewrite Q23, E23. exact R23.
    * rewrite Q24, E24. exact R24.
    * rewrite Q25, E25. exact R25.
    * rewrite Q26, E26, R26. change (w64 (48 * i)) with (Z_to_bv 64 (48 * i)).
      rewrite unsigned_lit_small by lia. change (w64 (48 * (i + 1))) with (Z_to_bv 64 (48 * (i + 1))). f_equal. lia.
    * rewrite Q27, E27. exact R27.
  + rewrite branch_ne_U, U27, U26 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    assert (Hni : disco_table_c.n_of T = i + 1) by lia.
    clear Hc.
    assert (NF : forall j, 0 <= j < disco_table_c.n_of T -> disco_table_c.mac_of T j <> disco_table_c.s_mac G)
      by (intros j Hj; destruct (Z.eq_dec j i) as [->|Hji]; [exact NE | apply NP; rlia]).
    paj_run_tok RUN HS HJ SHOK Bspan; [lp_awr|]. lp_after.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * rewrite (lp_blt E 24 8 (disco_table_c.n_of T) ltac:(rewrite E24, R24; reflexivity) ltac:(lia) ltac:(lia)) in Hc.
      apply Z.ltb_lt in Hc. rename Hc into Hn8'.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x50bc; [lp_awr|]. lp_after.
      pmkst HS.
      prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
      prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
      prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
      lazymatch goal with HM : lp_M _ |- _ => destruct HM as (HK & HP & HX & HSV & HOW) end.
      eapply AP; [left; split; [reflexivity | exact NF] | lia | exact HJ | exact HK | exact HP | exact HX | exact HSV
        | | | | | | | | | | | | ].
      -- unfold spZ. rewrite Q2, E2. exact Hsp.
      -- rewrite Q3, E3. exact R3.
      -- rewrite Q4, E4. exact R4.
      -- rewrite Q8, E8. exact R8.
      -- rewrite Q9, EQ32. reflexivity.
      -- rewrite Q18, E18. exact R18.
      -- rewrite Q20, E20. exact R20.
      -- rewrite Q21, E21. exact R21.
      -- rewrite Q22, E22. exact R22.
      -- rewrite Q23, E23. exact R23.
      -- rewrite Q24, E24. exact R24.
      -- rewrite Q25, E25. exact R25.
    * rewrite (lp_blt E 24 8 (disco_table_c.n_of T) ltac:(rewrite E24, R24; reflexivity) ltac:(lia) ltac:(lia)) in Hc.
      apply Z.ltb_ge in Hc.
      assert (Hn : disco_table_c.n_of T = 8) by lia. assert (Hi7 : i = 7) by lia. subst i.
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5088; [lp_awr|]. lp_after.
      pmkst HS.
      prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
      prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
      lazymatch goal with HM : lp_M _ |- _ => eapply (lp_full _ _ _ Hn NF HJ HM) end.
      -- unfold spZ. rewrite Q2, E2. exact Hsp.
      -- rewrite Q3, E3. exact R3.
      -- rewrite Q4, E4. exact R4.
      -- rewrite Q8, E8. exact R8.
      -- rewrite Q19, E19. exact R19.
      -- rewrite Q22, E22. exact R22.
Qed.
Theorem lp_loop : k1_stmt -> append_stmt -> loop_stmt.
Proof.
intros K1 AP.
assert (IND : forall kk i, Z.of_nat kk = disco_table_c.n_of T - i -> lp_at i).
{ induction kk as [|kk IHk]; intros i Hk; unfold lp_at;
    intros regs' m md Hi NP HJ HM Hsp R3 R4 R8 R9 R18 R20 R21 R22 R23 R24 R25 R26 R27; [lia|].
  apply (lp_pre i regs' m md Hi HJ HM Hsp R3 R4 R8 R9 R18 R20 R21 R22 R23 R24 R25 R26 R27).
  intros regs2 m2 md2 v HJ2 HM2 Hv Hiff Hsp2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
  exact (lp_post K1 AP i regs2 m2 md2 v Hi NP (fun _ => IHk (i + 1) ltac:(lia)) HJ2 HM2 Hv Hiff Hsp2
    Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27). }
unfold loop_stmt.
intros i regs' m md Hi NP HJ HK HP HX HSV HOW Hsp R3 R4 R8 R9 R18 R20 R21 R22 R23 R24 R25 R26 R27.
exact (IND (Z.to_nat (disco_table_c.n_of T - i)) i ltac:(lia) regs' m md Hi NP HJ
  (conj HK (conj HP (conj HX (conj HSV HOW)))) Hsp R3 R4 R8 R9 R18 R20 R21 R22 R23 R24 R25 R26 R27).
Qed.
Definition main_stmt : Prop :=
  SRr SEGS W (cfg_at SEGS (BASE + AF_both3_reac_disco_table_observe) regs memc mdc) tQ.
Definition rM_head : YP09.region := YP09.mkRegion (Some 10%nat) 384 388 384 384 [ckv 384 4 33].
Definition rg_M : smem := [stack_region 112; got_regionP; bcell_regionP 32; rM_head].
Definition fa_M : facts := mkFacts
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 8 (2 ^ 47 - 401) 3); (11%nat, mkAF 8 (2 ^ 47 - 25) 3);
    (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 8 0) ] [] [].
Definition ss_M : sstate := mkSS AF_both3_reac_disco_table_observe sr_atoms rg_M None fa_M.
Definition BxM : sv := SOff 32 0.
Definition SH_M : list shent := [mkSHE 10 0 400].
Definition EM : env := Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (disco_table_c.u_at T 384 4)]).
Lemma HnU : disco_table_c.n_of T = disco_table_c.u_at T 384 4 /\ 0 <= disco_table_c.u_at T 384 4 <= 8.
Proof.
pose proof HT1 as H1. pose proof (reac_disco_table_observe.u32_range T 384) as R.
unfold disco_table_c.tbl_T1, disco_table_c.n_of, disco_table_c.s32_at in H1 |- *. rewrite (swrap32_val _ R) in *.
destruct (Z.ltb_spec (disco_table_c.u_at T 384 4) (2 ^ 31)); lia.
Qed.
Lemma tbl_off_rng : forall a, t <= a < t + 400 -> ~ (YImgTop.IMG_LO <= a < YImgTop.IMG_TOP).
Proof.
intros a Ha Hr. destruct (Htw a Ha) as [Hw _].
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hst as (_ & _ & H3 & H4 & _).
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hr.
destruct Hw as [Hst | [[_ (b & n & Hb & Hbr)] | [(b & n & Hb & _ & Hbr) | (cid & pos & Hin & Hz)]]].
- lia.
- pose proof (blk_off_imgP B lyc Sc W memc mdc b n HARc Hb) as Ho. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Ho. lia.
- pose proof (blk_off_imgP B lyc Sc W memc mdc b n HARc Hb) as Ho. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Ho. lia.
- assert (Hf : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HARc Hf) as Ho.
  pose proof (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hf) as (Hf1 & Hf2 & _).
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Ho. unfold in_zr in Hz. cbn [fst snd] in Hz.
  destruct Hz as [Hz | Hz]; [lia|]. unfold shadow_addr, SHADOW_OFF in Hz. lia.
Qed.
Lemma mst_ok :
  st_ok_pi SEGS VAL EM ss_M (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_disco_table_observe)) memc (seg_rom SEGS))) /\
  sh_ok SEGS BxM SH_M EM (mrestrict (w_H W) memc).
Proof.
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rs_hide_all. apply rs_hide in Rnow.
pose proof Htam as Hamt. pose proof Hsam as Hams. pose proof Htside as Hts. pose proof Hsside as Hss.
pose proof Hwin as Hw. pose proof Hspl as Hsp.
unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hlo, Hts, Hss, Hw.
pose proof HJc as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HARc) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof HnU as [Hn Hn8].
pose proof (tbl_off_rng (t + 384) ltac:(lia)) as To1. pose proof (tbl_off_rng (t + 387) ltac:(lia)) as To2.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HgotR, HcellR, To1, To2.
assert (E2 : ew EM 2 = getr regs 2)
  by (unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew EM 10 = Z_to_bv 64 t)
  by (unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew EM 11 = Z_to_bv 64 s)
  by (unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew EM 32 = Z_to_bv 64 SB)
  by (unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew EM 33 = Z_to_bv 64 (disco_table_c.u_at T 384 4))
  by (unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew EM (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (unfold EM; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew EM (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (unfold EM; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew EM 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew EM n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val EM (Some n) = v).
{ intros n v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (Rt : 0 <= t < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
assert (Ht8' : 8 <= t) by (pose proof (Z.div_mod t 8 ltac:(lia)) as Hd; rewrite Ht8 in Hd; lia).
assert (Hs8' : 8 <= s) by (pose proof (Z.div_mod s 8 ltac:(lia)) as Hd; rewrite Hs8 in Hd; lia).
rewrite restrict_mkst_fx.
split.
- unfold ss_M. apply pa_entry_st_ok_full.
  + unfold EM. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rg_M, stack_region, got_regionP, bcell_regionP, rM_head, ckv.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS EM _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS EM _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * rewrite (VB 10%nat t E10 Rt). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS EM _ t 384 4 (SOff 33 0) (disco_table_c.u_at T 384 4));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | exact (reac_disco_table_observe.u32_range T 384) | zside
      | apply garr8_u_at; [exact HTg | lia | rewrite HTl; lia]].
  + apply pairwise_disjoint_of_extents. unfold rg_M, stack_region, got_regionP, bcell_regionP, rM_head, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat t E10 Rt), (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold rs_hold in Hts, Hss. repeat split; rlia.
  + split; [|split; [exact I | exact I]].
    unfold fa_M. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E32, E33. rewrite !unsigned_lit_small by (first [unfold SB; lia | lia]).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamt, Hams.
    unfold rs_hold in Hal, Ht8, Hs8.
    repeat match goal with |- _ /\ _ => split end; try rlia; unfold SB; rlia.
- unfold sh_ok, SH_M. repeat apply Forall_cons; try apply Forall_nil; unfold shent_ok, app_apart, BxM;
  cbn [she_m she_lo she_hi].
  rewrite (U_atom _ 32 SB E32) by (unfold SB; lia). rewrite (U_atom _ 10 t E10) by lia. split.
  + replace (t + 0) with t by lia. replace (400 - 0) with 400 by lia. exact Htra.
  + intros a Ha. unfold SB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. cbn [Z.min Z.max] in Ha. lia.
Qed.
Lemma awr_M : forall E rs, bv_unsigned (ew E 2) = spZ regs ->
  Forall (fun x : YP09.region => YP09.r_whi x <= YP09.r_wlo x \/
     (YP09.r_base x = Some 2%nat /\ -112 <= YP09.r_wlo x /\ YP09.r_whi x <= 0)) rs ->
  awr_ok E rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
intros E rs H2 HF. induction HF as [|x rs Hx HF IH]; [apply awr_ok_nil|].
destruct Hx as [Hro | (Hb & Hl & Hh)].
- apply awr_ok_cons_ro; [exact Hro | exact IH].
- eapply awr_ok_cons_gen; [exact Hb | exact H2 | | exact IH]. intros a Ha. left.
  pose proof Hwin as Hw. pose proof Hspl as Hs. unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hw. lia.
Qed.
Definition WM (a : Z) : Prop := spZ regs - 112 <= a < spZ regs.
Lemma run_memM : forall E rs m1 m2,
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> WM a) ->
  tPR m1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ WM a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) memc a) ->
  tPR m2 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ WM a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a).
Proof.
intros E rs m1 m2 HF HG Hwn HP HO.
pose proof (kept_of_frame (segs := SEGS) E rs (w_H W) m1 m2 WM HF Hwn) as HKF.
split.
- intros a Hp. eapply apresent_grows; [exact HG | apply HP; exact Hp].
- intros a Ha Hw. rewrite (HKF a Ha Hw). apply HO; assumption.
Qed.
Lemma memM_kept : forall m, (forall a, 0 <= a < 2 ^ 64 -> ~ WM a -> aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) ->
  tKP m /\ tTB m T.
Proof.
intros m HO. pose proof Htside as Hts. unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hts. split.
- intros a Ha Hn Ht. apply HO; [exact Ha|]. unfold WM. unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hn. lia.
- split; [|exact HTl]. apply (garr8_aview_kept SEGS (w_H W) (w_H W) memc m t); [|exact HTg].
  intros a Ha. rewrite length_map, HTl in Ha. apply HO; [unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia |].
  unfold WM. lia.
Qed.
Ltac awrMt Usp := apply (awr_M _ _ ltac:(cbn [ew ewset extK Nat.eqb]; exact Usp));
  lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_whi YP09.r_wlo YP09.r_base];
  first [left; apply Z.leb_le; reflexivity | right; split; [reflexivity | split; apply Z.leb_le; reflexivity] | left; lia | right; split; [reflexivity | lia]].
Ltac kwinM Usp := intros b_ wlo_ whi_ a_ Hin_ Hr_; vm_compute in Hin_;
  repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val ew ewset extK Nat.eqb] in Hr_;
    rewrite ?Usp in Hr_; unfold WM; first [clear - Hr_; lia | lia] |]); destruct Hin_.
Ltac mreg := lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict ?H ?msx) |- getr _ ?q = _ =>
  let Q := fresh "Q" in pose proof (st_ok_pi_restrict_reg H Ex ss msx q HS) as Q;
  let v := eval vm_compute in (sr_get (ss_regs ss) q) in change (sr_get (ss_regs ss) q) with v in Q; rewrite Q; clear Q end.
Ltac mval := cbn [sv_denot ew ewset extK Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  first [assumption | reflexivity | ekr; reflexivity
    | ekr; rewrite unsigned_lit_small by (unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia); reflexivity].
Ltac msv1 HE RS Usp E12 :=
  lazymatch goal with |- val_mem _ _ (spZ regs - 112 + ?o) _ (bv_unsigned ?w) =>
    let V := fresh "V" in
    epose proof (field_of_region_any (segs := SEGS) _ _ 2%nat (spZ regs) _ (-112) 0 (-112) 0 (o - 112) 8%N _ RS
      ltac:(cbn [ew ewset extK Nat.eqb]; exact Usp) ltac:(cbv [In]; repeat first [left; reflexivity | right]) ltac:(lia)) as V;
    replace (spZ regs - 112 + o) with (spZ regs + (o - 112)) by lia;
    cbn [sv_denot ew ewset extK Nat.eqb] in V;
    first [ rewrite E12 in V
          | lazymatch type of V with context [ew ?E0 ?n] => lazymatch w with getr regs ?q =>
              rewrite HE in V; unfold EM in V; rewrite Eimg_low in V by (unfold A_TEXT; lia);
              rewrite (ew_Ereg_nat regs _ n q eq_refl) in V end end ];
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned in V; change (8 * Z.of_N 8) with 64 in V;
    rewrite Z.mod_small in V by (pose proof (bv_unsigned_in_range 64 w) as Bw; unfold bv_modulus in Bw; exact Bw);
    exact V end.
Ltac msv HE RS Usp E12 := let o := fresh "o" in let q := fresh "q" in let Hin := fresh "Hin" in let Hq := fresh "Hq" in
  intros o q Hin; cbv [SAVSL In] in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; msv1 HE RS Usp E12 |]); destruct Hin.
Lemma main_ok : loop_stmt -> append_stmt -> main_stmt.
Proof.
intros HLP HAP. unfold main_stmt, cfg_at.
rs_hide_all. apply rs_hide in Rnow.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct mst_ok as [HS SHOK].
pose proof HJc as HJ.
pose proof HnU as [Hn Hn8].
pose proof stk_lo as [Hlo Hhi]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold REAC_DISCO_TABLE_OBSERVE_STK, ESTACK in Hlo.
remember EM as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Rt : 0 <= t < 2 ^ 64) by (unfold amem_range, kLowMemEnd, kHighMemEnd in Htam; lia).
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E3 : ew E 3 = getr regs 3)
  by (subst E; unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (subst E; unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t)
  by (subst E; unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 s)
  by (subst E; unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 ow)
  by (subst E; unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 now)
  by (subst E; unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (disco_table_c.u_at T 384 4))
  by (subst E; unfold EM; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HOM : forall a, 0 <= a < 2 ^ 64 -> ~ WM a -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (HPM : tPR memc) by (intros a Ha; exact Ha).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5054; [awrMt Usp|].
destruct (run_memM _ _ memc _ HFr HG ltac:(kwinM Usp) HPM HOM) as (HP1 & HO1). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite (br_ge0 _ 33 _ ltac:(cbn [ew ewset extK Nat.eqb]; exact E33) ltac:(lia)) in Hc. apply Z.leb_le in Hc.
  assert (Hn0 : disco_table_c.n_of T = 0) by lia.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x50bc; [awrMt Usp|].
  destruct (run_memM _ _ _ _ HFr HG ltac:(kwinM Usp) HP1 HO1) as (HP2 & HO2). clear HF HFr HG.
  destruct (memM_kept _ HO2) as [HK2 HTB2].
  lazymatch goal with HS0 : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) |- _ =>
    let rS := eval vm_compute in (nth 0 (ss_mem ss) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth Ex ss (restrict (w_H W) msx) 0 rS HS0 ltac:(vm_compute; reflexivity)) as RS;
    cbn [ms_mem restrict] in RS end.
  pmkst HS.
  apply HAP.
  + left. split; [reflexivity|]. intros j Hj. lia.
  + lia.
  + exact HJ.
  + exact HK2.
  + exact HP2.
  + exact HTB2.
  + msv HE RS Usp E12.
  + lazymatch goal with HS0 : st_ok_pi _ _ ?Ex ?ss (restrict ?H ?msx) |- _ =>
      pose proof (st_ok_pi_restrict_reg H Ex ss msx 2%bv HS0) as Q2;
      let v := eval vm_compute in (sr_get (ss_regs ss) 2%bv) in change (sr_get (ss_regs ss) 2%bv) with v in Q2;
      change (spZ (ms_regs msx)) with (bv_unsigned (getr (ms_regs msx) 2)) end.
    rewrite Q2. cbn [sv_denot ew ewset extK Nat.eqb].
    rewrite Usp. rewrite unsigned_lit_small by lia. lia.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. unfold w64. apply bv_eq_U; [lia | exact (U_not _ 10 t ltac:(cbn [ew ewset extK Nat.eqb]; exact E10) Rt)].
  + mreg. cbn [sv_denot ew ewset extK Nat.eqb]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned, Hn. reflexivity.
  + mreg. rewrite (denot_shx _ 10 32 384 t SB ltac:(cbn [ew ewset extK Nat.eqb]; exact E10)
      ltac:(cbn [ew ewset extK Nat.eqb]; exact E32)) by (unfold SB, amem_range, kLowMemEnd, kHighMemEnd in *; lia).
    unfold w64. f_equal. lia.
- rewrite (br_ge0 _ 33 _ ltac:(cbn [ew ewset extK Nat.eqb]; exact E33) ltac:(lia)) in Hc. apply Z.leb_gt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5054; [awrMt Usp|].
  destruct (run_memM _ _ _ _ HFr HG ltac:(kwinM Usp) HP1 HO1) as (HP2 & HO2). clear HF HFr HG.
  destruct (memM_kept _ HO2) as [HK2 HTB2].
  lazymatch goal with HS0 : st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) |- _ =>
    let rS := eval vm_compute in (nth 0 (ss_mem ss) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth Ex ss (restrict (w_H W) msx) 0 rS HS0 ltac:(vm_compute; reflexivity)) as RS;
    cbn [ms_mem restrict] in RS end.
  pmkst HS.
  apply (HLP 0).
  + lia.
  + intros j Hj. lia.
  + exact HJ.
  + exact HK2.
  + exact HP2.
  + exact HTB2.
  + msv HE RS Usp E12.
  + unfold tOW. msv1 HE RS Usp E12.
  + lazymatch goal with HS0 : st_ok_pi _ _ ?Ex ?ss (restrict ?H ?msx) |- _ =>
      pose proof (st_ok_pi_restrict_reg H Ex ss msx 2%bv HS0) as Q2;
      let v := eval vm_compute in (sr_get (ss_regs ss) 2%bv) in change (sr_get (ss_regs ss) 2%bv) with v in Q2;
      change (spZ (ms_regs msx)) with (bv_unsigned (getr (ms_regs msx) 2)) end.
    rewrite Q2. cbn [sv_denot ew ewset extK Nat.eqb].
    rewrite Usp. rewrite unsigned_lit_small by lia. lia.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. mval.
  + mreg. unfold w64. apply bv_eq_U; [lia | exact (U_not _ 10 t ltac:(cbn [ew ewset extK Nat.eqb]; exact E10) Rt)].
  + mreg. cbn [sv_denot ew ewset extK Nat.eqb]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned, Hn. reflexivity.
  + mreg. rewrite (denot_shx _ 10 32 384 t SB ltac:(cbn [ew ewset extK Nat.eqb]; exact E10)
      ltac:(cbn [ew ewset extK Nat.eqb]; exact E32)) by (unfold SB, amem_range, kLowMemEnd, kHighMemEnd in *; lia).
    unfold w64. f_equal. lia.
  + mreg. reflexivity.
  + mreg. rewrite Hn. apply (n48 _ _ ltac:(cbn [ew ewset extK Nat.eqb]; exact E33)). lia.
Qed.
Lemma k1_ok : k1_stmt.
Proof. exact k1. Qed.
Lemma w_ok : loop_stmt -> append_stmt -> SRr SEGS W (cfg_at SEGS (BASE + AF_both3_reac_disco_table_observe) regs memc mdc) tQ.
Proof. exact main_ok. Qed.
End w.
Theorem pb_reac_disco_table_observe : treac_disco_table_observe_spec.
Proof.
unfold treac_disco_table_observe_spec. intros.
eapply w_ok; try eassumption.
- eapply lp_loop; try eassumption.
  + eapply k1_ok; eassumption.
  + eapply ap_append; eassumption.
- eapply ap_append; eassumption.
Qed.
End h.
End f.
End d.
