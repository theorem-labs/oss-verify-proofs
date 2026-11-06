(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, ex_string's walk on image A' (#102 pin asan 1be0f53d96cb): the journal-level
   helpers every cut file uses. The geometry of the entry (ES_PRE), the facts a cut state has from ESB (the text kept,
   the text's and the scratch's shadow from AR_laws_x, the stack's shadow), the ledger across scratch writes, and the
   passage from the end of a run to the kit's post (es_finish).
   PORTED from lib/B/Prog/ExsB_Lib.v at a Theorem Labs lane's batch-kit re-fit (a working branch 66eac2b9522a, blob of
   record): the same lemmas, image-free in content, at image A's listing, segments and statics (S1ImgA.pst_in_img_A,
   A_prog_segs_low); es_geom carries a Theorem Labs lane's re-fit of the cut's relaxed src_rd (x0 + len + 8 <= alloc_ceiling from
   the text's own live block by AR_laws_x field 24 alx_blocks_ceil8; TESTED HERE: the text is in a live block by
   ES_PRE's prhex_inblk x0 len, and 0 < len by ES_PRE's 0 <= i0 < len). CHANGED for A': es_esb_step's frame clause
   (A spills four words, 0(sp) .. 24(sp), where B spills three) and its register clause (ExsA_Sym.v ES_REGS).
   Numerals: 144 (LENGTH: frame), 160 (DERIVED: STK_ex_string at prh_img_A, vm_compute), 8, 16, 24, 32, 40 (LENGTH: slots
   and struct ex); 2 ^ 44, 2 ^ 46, 2 ^ 47, 2 ^ 64 (LENGTH: address-space widths). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA ExsA_Stmt ExsA_Sym.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExsB_Model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_A.
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).

(* ---- the listing offsets ---- *)
Definition ES_PC : Z := A_prog_sigma AS_ex_string - A_prog_base.
Lemma es_pc_eq {rc : YM05.RunCeil} : forall off, es_pc off = BASE + (ES_PC + off).
Proof. intros off. unfold es_pc, ES_PC. change BASE with A_prog_base. lia. Qed.
Lemma es_stk_val : @STK_ex_string prh_img_A = 160.
Proof. vm_compute. reflexivity. Qed.

(* ---- journal-free helpers (ExwB.v's ew_ lemmas) ---- *)
Lemma es_w64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.
Lemma es_aview_garr8 : forall (W : world rsegs) m p l j, garr8 rsegs (mrestrict (w_H W) m) p l -> (j < length l)%nat ->
  aview rsegs (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold aview. rewrite (garr8_mbyte rsegs _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.
Lemma es_val1_of_aview : forall H (m : word -> option byte) a z,
  aview rsegs H m a = Some z -> val_mem rsegs (mrestrict H m) a 1 z /\ 0 <= z < 256.
Proof.
intros H m a z Ha. unfold aview in Ha.
destruct (mbyte rsegs (mrestrict H m) a) as [b|] eqn:Hb; cbn [option_map] in Ha; [|discriminate].
injection Ha as <-. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr]. intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r. rewrite Hb. f_equal.
rewrite (le_byte_small (bv_unsigned b) 1 0) by (change (2 ^ (8 * Z.of_nat 1)) with 256; lia).
cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma es_vm_same : forall H (m m' : word -> option byte) a n v,
  val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H m') a n v ->
  forall x, a <= x < a + Z.of_nat n -> aview rsegs H m' x = aview rsegs H m x.
Proof.
intros H m m' a n v V V' x Hx. unfold aview. f_equal.
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (V (Z.to_nat (x - a)) ltac:(lia)), (V' (Z.to_nat (x - a)) ltac:(lia)). reflexivity.
Qed.
Lemma es_val_kept : forall H (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview rsegs H m' x = aview rsegs H m x) ->
  val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H m') a n v.
Proof.
intros H m m' a n v HE Hv kk Hk. rewrite (mbyte_of_aview rsegs H H m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma es_garr8_kept : forall H (m m' : word -> option byte) p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview rsegs H m' a = aview rsegs H m a) ->
  garr8 rsegs (mrestrict H m) p l -> garr8 rsegs (mrestrict H m') p l.
Proof.
intros H m m' p l HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. cbn in Hk. rewrite (mbyte_of_aview rsegs H H m m' (p + Z.of_nat j + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma es_garr8_app : forall mm p (l1 l2 : list Z),
  garr8 rsegs mm p l1 -> garr8 rsegs mm (p + Z.of_nat (length l1)) l2 -> garr8 rsegs mm p (l1 ++ l2).
Proof.
intros mm p l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hl|Hl].
- rewrite app_nth1 by exact Hl. exact (H1 j Hl).
- rewrite app_nth2 by exact Hl. destruct (H2 (j - length l1)%nat ltac:(lia)) as [V R]. split; [|exact R].
  replace (p + Z.of_nat j) with (p + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. exact V.
Qed.
Lemma es_garr8_one : forall mm a v, val_mem rsegs mm a 1 v -> 0 <= v < 256 -> garr8 rsegs mm a [v].
Proof.
intros mm a v Hv Hr j Hj. cbn [length] in Hj. assert (j = 0%nat) as -> by lia. cbn [nth Z.of_nat]. rewrite Z.add_0_r.
split; [exact Hv | exact Hr].
Qed.
Lemma es_garr8_length_bytes : forall mm p l, garr8 rsegs mm p l -> Forall (fun b => 0 <= b < 256) l.
Proof.
intros mm p l H. apply Forall_forall. intros b Hb. apply In_nth with (d := 0) in Hb as (j & Hj & <-).
exact (proj2 (H j Hj)).
Qed.

(* the text from a position: one byte, then the rest *)
Lemma es_skipn_cons : forall (l : list Z) n, (n < length l)%nat -> skipn n l = nth n l 0 :: skipn (S n) l.
Proof.
induction l as [|a l IH]; intros [|n] Hn; cbn in Hn |- *; try lia; [reflexivity|]. apply IH. lia.
Qed.
Lemma es_rest_cons : forall E p, e_x0 E <= p < e_x0 E + es_len E ->
  es_rest E p = es_byte E p :: es_rest E (p + 1).
Proof.
intros E p Hp. unfold es_rest, es_byte, es_len in *.
replace (Z.to_nat (p + 1 - e_x0 E)) with (S (Z.to_nat (p - e_x0 E))) by lia.
apply es_skipn_cons. lia.
Qed.
Lemma es_rest_end : forall E p, e_x0 E + es_len E <= p -> es_rest E p = [].
Proof.
intros E p Hp. unfold es_rest, es_len in *. apply skipn_all2. lia.
Qed.

(* a sub-range of an ASan application range *)
Lemma es_amem_sub : forall a n b m, amem_range a n -> a <= b -> b + m <= a + n -> amem_range b m.
Proof. unfold amem_range. intros a n b m [H | [H1 H2]] Hb Hm; [left; lia | right; split; lia]. Qed.

(* ---- the text from a position: its length, its first bytes ---- *)
Lemma es_rest_length : forall E a, e_x0 E <= a <= e_x0 E + es_len E ->
  Z.of_nat (length (es_rest E a)) = e_x0 E + es_len E - a.
Proof. intros E a Ha. unfold es_rest, es_len in *. rewrite length_skipn. lia. Qed.
Lemma es_nth_firstn : forall (l : list Z) n j, (j < n)%nat -> nth j (firstn n l) 0 = nth j l 0.
Proof.
induction l as [|x l IH]; intros [|n] [|j] Hj; cbn; try lia; try reflexivity. apply IH. lia.
Qed.
Lemma es_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
intros l k. revert l. induction k as [|k IH]; intros l j; [reflexivity|].
destruct l as [|x l]; [destruct j; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma es_text_garr8 : forall E (mm : word -> option byte) a n,
  (forall b, e_x0 E <= b < e_x0 E + es_len E -> val_mem rsegs mm b 1 (es_byte E b) /\ 0 <= es_byte E b < 256) ->
  e_x0 E <= a -> 0 <= n -> a + n <= e_x0 E + es_len E ->
  garr8 rsegs mm a (firstn (Z.to_nat n) (es_rest E a)).
Proof.
intros E mm a n HTX Ha Hn Han j Hj. rewrite length_firstn in Hj.
pose proof (es_rest_length E a ltac:(lia)) as HL.
assert (Hj' : (j < Z.to_nat n)%nat) by lia.
rewrite (es_nth_firstn _ _ _ Hj'). unfold es_rest. rewrite es_nth_skipn.
destruct (HTX (a + Z.of_nat j) ltac:(lia)) as [V R]. unfold es_byte in V, R.
replace (Z.to_nat (a + Z.of_nat j - e_x0 E)) with (Z.to_nat (a - e_x0 E) + j)%nat in V, R by lia.
split; [exact V | exact R].
Qed.

(* the twelve bytes of a surrogate pair `\uXXXX\uYYYY` at p *)
Lemma es_rest_pair : forall E p, e_x0 E <= p -> p + 12 <= e_x0 E + es_len E ->
  skipn 4 (es_rest E (p + 2)) =
  es_byte E (p + 6) :: es_byte E (p + 7) :: es_byte E (p + 8) :: es_byte E (p + 9) :: es_byte E (p + 10) ::
  es_byte E (p + 11) :: es_rest E (p + 12).
Proof.
intros E p H1 H2. unfold es_rest at 1. rewrite exs_skipn_skipn.
replace (4 + Z.to_nat (p + 2 - e_x0 E))%nat with (Z.to_nat (p + 6 - e_x0 E)) by lia. fold (es_rest E (p + 6)).
rewrite (es_rest_cons E (p + 6)) by lia. rewrite (es_rest_cons E (p + 6 + 1)) by lia.
rewrite (es_rest_cons E (p + 6 + 1 + 1)) by lia. rewrite (es_rest_cons E (p + 6 + 1 + 1 + 1)) by lia.
rewrite (es_rest_cons E (p + 6 + 1 + 1 + 1 + 1)) by lia. rewrite (es_rest_cons E (p + 6 + 1 + 1 + 1 + 1 + 1)) by lia.
repeat match goal with |- context [p + 6 + 1 + 1 + 1 + 1 + 1 + 1] => replace (p + 6 + 1 + 1 + 1 + 1 + 1 + 1) with (p + 12) by ring end.
replace (p + 6 + 1 + 1 + 1 + 1 + 1) with (p + 11) by ring. replace (p + 6 + 1 + 1 + 1 + 1) with (p + 10) by ring.
replace (p + 6 + 1 + 1 + 1) with (p + 9) by ring. replace (p + 6 + 1 + 1) with (p + 8) by ring.
replace (p + 6 + 1) with (p + 7) by ring. reflexivity.
Qed.
Lemma es_hex4_at : forall E a, e_x0 E <= a -> a + 4 <= e_x0 E + es_len E ->
  PjGrammar.hex4 [es_byte E a; es_byte E (a + 1); es_byte E (a + 2); es_byte E (a + 3)] = PjGrammar.hex4 (es_rest E a).
Proof.
intros E a H1 H2. rewrite (es_rest_cons E a) by lia. rewrite (es_rest_cons E (a + 1)) by lia.
rewrite (es_rest_cons E (a + 1 + 1)) by lia. rewrite (es_rest_cons E (a + 1 + 1 + 1)) by lia.
replace (a + 1 + 1 + 1) with (a + 3) by ring. replace (a + 1 + 1) with (a + 2) by ring. reflexivity.
Qed.

(* the code's low-surrogate test (A 0x84200-0x8420c: lui a1,0xffff2; addw a1,lo,a1; bltu a1,-1024) against the grammar's *)
Lemma es_lo_check : forall lo, 0 <= lo < 65536 ->
  ((lo - 57344) mod 2 ^ 64 <? 2 ^ 64 - 1024) = negb ((56320 <=? lo) && (lo <=? 57343)).
Proof.
intros lo Hlo.
assert (HM : (lo - 57344) mod 2 ^ 64 = if lo <? 57344 then lo - 57344 + 2 ^ 64 else lo - 57344).
{ destruct (Z.ltb_spec lo 57344) as [H|H].
  - symmetry. apply (Z.mod_unique _ _ (-1)); [left; lia | lia].
  - apply Z.mod_small. lia. }
rewrite HM. destruct (Z.ltb_spec lo 57344), (Z.leb_spec 56320 lo), (Z.leb_spec lo 57343); cbn [andb negb];
  first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

(* ---- the grammar invariant across one arm of the loop ---- *)
Lemma es_esg_step : forall E p acc n out,
  ESG E p acc -> p + n <= e_x0 E + es_len E -> (Z.of_nat (length out) <= n) ->
  PjGrammar.decode (es_rest E p) = PjGrammar.emit out (PjGrammar.decode (es_rest E (p + n))) ->
  ESG E (p + n) (acc ++ out).
Proof.
intros E p acc n out (H1 & H2 & H3) Hn Hl Hd. unfold ESG. rewrite length_app.
split; [lia|]. split; [lia|]. rewrite H3, Hd, exs_emit_app. reflexivity.
Qed.
Lemma es_fail_of : forall E p acc, ESG E p acc -> PjGrammar.decode (es_rest E p) = None ->
  PjGrammar.decode (es_xs E) = None.
Proof. intros E p acc (_ & _ & H3) Hd. rewrite H3, Hd. reflexivity. Qed.
Lemma es_rest_esc : forall E p, e_x0 E <= p -> p + 1 < e_x0 E + es_len E ->
  es_rest E p = es_byte E p :: es_byte E (p + 1) :: es_rest E (p + 2).
Proof.
intros E p H1 H2. rewrite (es_rest_cons E p) by lia. rewrite (es_rest_cons E (p + 1)) by lia.
replace (p + 1 + 1) with (p + 2) by ring. reflexivity.
Qed.

(* ---- the entry geometry ---- *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition ES_GEOM (E : es_e) : Prop :=
  let sp := es_sp E in let q := e_q E in let x0 := e_x0 E in let len := es_len E in let scr := e_scr E in
  sp mod 16 = 0 /\ alloc_ceiling <= ly_stk_lo (e_ly E) /\ ly_stk_lo (e_ly E) + 160 <= sp /\
  sp + e_d E <= ly_top (e_ly E) /\ ly_top (e_ly E) <= ly_stk_hi (e_ly E) /\ ly_stk_hi (e_ly E) <= 2 ^ 47 /\
  sp + 64 <= ly_stk_hi (e_ly E) /\ 0 <= e_d E /\
  sp <= q /\ q + 32 <= sp + e_d E /\ q mod 8 = 0 /\
  4096 <= x0 /\ x0 + len + 8 <= alloc_ceiling /\ 0 <= e_i0 E < len /\ len <= 3 * 2 ^ 20 /\
  4096 <= scr /\ scr + len + 1 <= alloc_ceiling /\
  (scr + len + 1 <= x0 \/ x0 + len <= scr) /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.

Lemma es_geom : forall E, ES_PRE B ARx E -> ES_GEOM E.
Proof.
intros E HP. unfold ES_PRE in HP. cbv zeta in HP.
destruct HP as ((HFN & HROD & HTOP) & H10 & Vp & Ve & Vs & Hq8 & Hspq & Hqd & HWIN & HSRC & HINBx & Hlen3 & Hi0 &
  HWD & HINBs & Hdx & Hdq & HLED).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite es_stk_val in Hstk.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct HSRC as (GT & Hx4 & Hxceil & Hxam & Hxra & Hxhull).
destruct HWD as (Hs0 & Hsceil & Hsam & Hswr & Hsra & Hshull).
destruct HINBs as (b & m & Hbm & Hbs & Hsm & Hhd).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbm) as (_ & Hb4096 & _).
pose proof alloc_ceiling_value as [[CA CB] _].
(* The batch kit (the internal file MIGRATION.md section 1: src_rd's + 8 RELAXED, Hxceil is now x0 + len <= alloc_ceiling): ES_GEOM's
   x0 + len + 8 <= alloc_ceiling from the text's own block (prhex_inblk) and AR_laws_x field 24 alx_blocks_ceil8 *)
destruct HINBx as (bx & mx & Hbmx & Hbx & Hxm & _).
pose proof (alx_blocks_ceil8 _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbmx) as Hc8x.
assert (Hrqx : mx <= req_size mx) by (unfold req_size; destruct (Z.eqb_spec mx 0); lia).
unfold ES_GEOM, es_sp. cbv zeta. unfold es_len in *. repeat split; lia.
Qed.

(* ---- ESB at a cut: the current allocator state, and the facts the cuts derive from it ---- *)
Lemma es_cur_ar : forall E lyc Sc Hpc regs memc mdc k,
  ESB B ARx SK E lyc Sc Hpc regs memc mdc k -> ARx lyc Sc Hpc (e_W E) memc mdc.
Proof. intros E lyc Sc Hpc regs memc mdc k HB. exact (proj1 (proj1 HB)). Qed.

(* every hidden head is a live block's base (the ledger's Permutation and hblocks) *)
Lemma es_hp_base : forall ly S Hp (W : world rsegs) mem Lam peak cnt fail ran most own h,
  prh_ledger (L := A_prog_listing) (PA := PI_prog_A) B ly S Hp W mem Lam peak cnt fail ran most own -> In h Hp ->
  exists k, 0 <= k /\ In (h, k + cf_head) (ablocks B ly S).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own h (_ & _ & HF & HP) Hh.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & <- & Hin).
pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (K0 & Kin & _). cbn [fst snd] in *.
exists k. split; [exact K0 | exact Kin].
Qed.

(* the shadow of bytes inside a live block outside its hidden head: addressable, hull visible *)
Lemma es_inblk_ra : forall ly S Hp (W : world rsegs) mem md Lam peak cnt fail ran most own a n,
  8 <= cf_head -> ARx ly S Hp W mem md ->
  prh_ledger (L := A_prog_listing) (PA := PI_prog_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_inblk B ly S Hp a n -> 0 < n ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview rsegs (w_H W) mem) a n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a n Hhead HAR HLED (b & m & Hbm & Hba & Han & Hhd) Hn.
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (BS : exists p0 n0, block_shadow (aview rsegs (w_H W) mem) SHADOW_OFF p0 n0 /\
  shadow_hull_vis (aview rsegs (w_H W) mem) p0 n0 /\ p0 <= a /\ a + n <= p0 + n0).
{ destruct (in_dec Z.eq_dec b Hp) as [Hin|Hnin].
  - destruct (alx_hshadow _ _ _ LAWS ly S Hp W mem md b m HAR Hbm Hin) as [BSh HV].
    specialize (Hhd Hin). exists (b + cf_head), (req_size m - cf_head).
    split; [exact BSh|]. split; [apply HV; lia|]. lia.
  - assert (HnoH : forall h, In h Hp -> ~ (b <= h < b + req_size m)).
    { intros h Hh Hr. destruct (es_hp_base ly S Hp W mem Lam peak cnt fail ran most own h HLED Hh) as (k' & Hk' & Hm').
      destruct (Z.eq_dec h b) as [->|Hne]; [exact (Hnin Hh)|].
      assert (Hneq : (b, m) <> (h, k' + cf_head)) by (intros E; injection E as E1 _; lia).
      pose proof (sep_blocks_x rsegs B ARx LAWS ly S Hp W mem md b m h (k' + cf_head) HAR Hbm Hm' Hneq) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      assert (req_size (k' + cf_head) = k' + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
      lia. }
    destruct (alx_shadow _ _ _ LAWS ly S Hp W mem md b m HAR Hbm HnoH) as [BSh HV].
    exists b, (req_size m). split; [exact BSh|]. split; [exact HV|]. lia. }
destruct BS as (p0 & n0 & (Hp8 & Hn0 & BSh) & HV & H1 & H2).
split.
- intros x Hx. set (i := x / 8 - p0 / 8).
  assert (Hi : 0 <= i < (n0 + 7) / 8) by (subst i; lia).
  specialize (BSh i Hi). exists (if i <? n0 / 8 then 0 else n0 mod 8). split.
  + unfold shadow_of_addr in *. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + p0 / 8 + i) by (subst i; lia). exact BSh.
  + unfold saddr_ok. destruct (Z.ltb_spec i (n0 / 8)); [left; reflexivity|]. right. subst i. lia.
- intros s Hs. apply HV. pose proof (shadow_mono p0 a H1) as M1.
  pose proof (shadow_mono (a + n - 1) (p0 + n0 - 1) ltac:(lia)) as M2.
  assert (R8 : forall u w, u <= w -> u / 8 * 8 <= w / 8 * 8)
    by (intros u w Huw; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* the text's bytes at a cut are the entry's: a live block of the entry and of the cut, outside FP *)
Lemma es_text_kept : forall E lyc Sc Hpc regs memc mdc k,
  ES_PRE B ARx E -> ESB B ARx SK E lyc Sc Hpc regs memc mdc k ->
  forall a, e_x0 E <= a < e_x0 E + es_len E -> aview rsegs (w_H (e_W E)) memc a = aview rsegs (w_H (e_W E)) (e_mem E) a.
Proof.
intros E lyc Sc Hpc regs memc mdc k HP HB a Ha.
pose proof (es_geom E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HP as HP0. unfold ES_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (b & m & Hbm & Hba & Ham & _) & _).
pose proof HB as (HJ & _ & _ & _ & HAB & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HKB & _).
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
replace a with (b + (a - b)) by lia.
apply (HKB b m (a - b) Hbm); [rewrite HAB; exact Hbm | lia |].
intros (r & Hr & Hra). cbn [In es_FP] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra; unfold es_len in *; lia.
Qed.

(* the text and the scratch at a cut: their blocks, their shadow, the text's bytes *)
Lemma es_cut_mem : forall E lyc Sc Hpc regs memc mdc k,
  8 <= cf_head -> ES_PRE B ARx E -> ESB B ARx SK E lyc Sc Hpc regs memc mdc k ->
  range_addressable (aview rsegs (w_H (e_W E)) memc) SHADOW_OFF (e_x0 E) (es_len E) /\
  range_addressable (aview rsegs (w_H (e_W E)) memc) SHADOW_OFF (e_scr E) (es_len E + 1) /\
  (forall a, e_x0 E <= a < e_x0 E + es_len E ->
     val_mem rsegs (rdW (e_W E) memc) a 1 (es_byte E a) /\ 0 <= es_byte E a < 256) /\
  (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= e_x0 E /\ e_x0 E + es_len E <= b + m /\
     (In b Hpc -> b + cf_head <= e_x0 E)) /\
  (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= e_scr E /\ e_scr E + es_len E + 1 <= b + m /\
     (In b Hpc -> b + cf_head <= e_scr E)).
Proof.
intros E lyc Sc Hpc regs memc mdc k Hhead HP HB.
pose proof HP as HP0. unfold ES_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (GT & _) & HINBx & _ & Hi0 & _ & HINBs & _).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & _).
pose proof (es_cur_ar E lyc Sc Hpc regs memc mdc k HB) as HAR.
assert (HXc : prhex_inblk B lyc Sc Hpc (e_x0 E) (es_len E)).
{ destruct HINBx as (b & m & Hbm & Hbs & Hsm & Hhd). exists b, m. rewrite HAB, HHp. auto. }
assert (HSc : prhex_inblk B lyc Sc Hpc (e_scr E) (es_len E + 1)).
{ destruct HINBs as (b & m & Hbm & Hbs & Hsm & Hhd). exists b, m. rewrite HAB, HHp. auto. }
split; [exact (proj1 (es_inblk_ra lyc Sc Hpc (e_W E) memc mdc _ _ _ _ _ _ _ _ _ Hhead HAR HLED HXc ltac:(lia)))|].
split; [exact (proj1 (es_inblk_ra lyc Sc Hpc (e_W E) memc mdc _ _ _ _ _ _ _ _ _ Hhead HAR HLED HSc ltac:(lia)))|].
split.
{ intros a Ha. unfold es_len in Ha.
  assert (Hj : (Z.to_nat (a - e_x0 E) < length (e_x E))%nat) by lia.
  pose proof (es_aview_garr8 (e_W E) (e_mem E) (e_x0 E) (e_x E) _ GT Hj) as HA0.
  replace (e_x0 E + Z.of_nat (Z.to_nat (a - e_x0 E))) with a in HA0 by lia.
  rewrite <- (es_text_kept E lyc Sc Hpc regs memc mdc k HP HB a ltac:(unfold es_len; lia)) in HA0.
  destruct (es_val1_of_aview _ _ _ _ HA0) as [V R]. unfold es_byte. split; [exact V | exact R]. }
split; [destruct HXc as (b & m & Hbm & Hbs & Hsm & Hhd); exists b, m; exact (conj Hbm (conj Hbs (conj Hsm Hhd)))|].
destruct HSc as (b & m & Hbm & Hbs & Hsm & Hhd); exists b, m.
split; [exact Hbm|]. split; [exact Hbs|]. split; [lia | exact Hhd].
Qed.

(* a write in the scratch, or in ex_string's frame (below the callee's sp included), is allowed by the journal *)
Lemma es_awr_scr : forall E (blc : list (Z * Z)) bl0 lyc own b m a,
  In (b, m) blc -> b <= e_scr E -> e_scr E + es_len E + 1 <= b + m ->
  e_scr E <= a < e_scr E + es_len E + 1 ->
  awr_byte (STK_ex_string + e_d E) (es_sp E + e_d E) (es_FP E) bl0 blc lyc own a.
Proof.
intros E blc bl0 lyc own b m a Hin Hb Hm Ha. right. left. split.
- exists (e_scr E, e_scr E + es_len E + 1). split; [left; reflexivity | cbn [fst snd]; lia].
- exists b, m. split; [exact Hin|]. assert (m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
Qed.
Lemma es_awr_stk : forall E (blc : list (Z * Z)) bl0 lyc own a,
  es_sp E - 160 <= a < es_sp E + e_d E ->
  awr_byte (STK_ex_string + e_d E) (es_sp E + e_d E) (es_FP E) bl0 blc lyc own a.
Proof. intros E blc bl0 lyc own a Ha. left. rewrite es_stk_val. lia. Qed.

(* the stack's shadow at any ARx state of the walk (AR_laws_x alx_zshadow_byte) *)
Lemma es_stk_ra : forall ly S Hp (W : world rsegs) mem md a n,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S Hp W mem md a n HAR Hlo Hhi z Hz. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
apply (alx_zshadow_byte _ _ _ LAWS ly S Hp W mem md z HAR). lia.
Qed.

(* ---- the ledger across a run that writes nothing below the ceiling (ex_ws_x.v exw_ledger_kept, restated) ---- *)
Lemma es_ledger_same : forall ly S Hp (W : world rsegs) mem md mem' Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  (forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
  prh_ledger (L := A_prog_listing) (PA := PI_prog_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (L := A_prog_listing) (PA := PI_prog_A) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR HK (HG & HND & HB & HP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as (AC1 & AC2).
assert (VK : forall a n v, 0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
  val_mem rsegs (rdW W mem) a n v -> val_mem rsegs (rdW W mem') a n v).
{ intros a n v Ha Hn. apply (es_val_kept (w_H W) mem mem' a n v). intros x Hx. apply HK. lia. }
split; [|split; [exact HND|split; [|exact HP]]].
- destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6b) & (G7 & G7b) & GR).
  refine (conj (VK _ _ _ _ _ G1) (conj (VK _ _ _ _ _ G2) (conj (VK _ _ _ _ _ G3) (conj (VK _ _ _ _ _ G4)
    (conj (VK _ _ _ _ _ G5) (conj (conj (VK _ _ _ _ _ G6) G6b) (conj (conj (VK _ _ _ _ _ G7) G7b) GR))))))).
  all: cbn [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out pi_gz_live pi_gz_peak
    pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_A]; try change (Z.of_nat 8) with 8;
    try change (Z.of_nat 1) with 1; lia.
- revert HB. apply Forall_impl. intros [a k] (K0 & Kin & Khp & Kal & Kv). cbn [fst snd] in *.
  refine (conj K0 (conj Kin (conj Khp (conj Kal _)))).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Kin) as (B1 & B2 & B3 & _).
  apply (VK (a - cf_head) 8%nat k); [lia | | exact Kv]. change (Z.of_nat 8) with 8.
  pose proof (@cf_head_nonneg cp) as CH0.
  assert (HU : exists u, a - cf_head = 16 * u).
  { exists ((a - cf_head) / 16). rewrite (Z.div_mod (a - cf_head) 16) at 1 by discriminate. rewrite B1, Z.add_0_r. reflexivity. }
  assert (HV : exists v, alloc_ceiling = 4096 * v).
  { exists (alloc_ceiling / 4096). rewrite (Z.div_mod alloc_ceiling 4096) at 1 by discriminate. rewrite AC2, Z.add_0_r. reflexivity. }
  destruct HU as [u Hu]. destruct HV as [v Hv]. clear B1 AC2.
  revert B3. unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0) as [Hz|Hz]; intros B3; lia.
Qed.

(* ---- the ledger across writes that miss the statics and every hidden head word ---- *)
Lemma es_ledger_keep : forall ly S Hp (W : world rsegs) mem md mem' Lam peak cnt fail ran most own (C : Z -> Prop) b m,
  8 <= cf_head -> ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) ->
  (forall a, C a -> b <= a < b + m) -> (In b Hp -> forall a, C a -> b + cf_head <= a) ->
  (forall a, 0 <= a < alloc_ceiling -> ~ C a -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
  prh_ledger (L := A_prog_listing) (PA := PI_prog_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (L := A_prog_listing) (PA := PI_prog_A) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md mem' Lam peak cnt fail ran most own C b m Hh HAR Hbm HCb HCh HK (HG & HND & HF & HP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (VK : forall a (w : nat) v, val_mem rsegs (rdW W mem) a w v ->
  (forall x, a <= x < a + Z.of_nat w -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) mem x) ->
  val_mem rsegs (rdW W mem') a w v).
{ intros a w v Hv HE. exact (es_val_kept (w_H W) mem mem' a w v HE Hv). }
assert (KS : forall x, Exists (in_zr x) (@prh_pst prh_img_A) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) mem x).
{ intros x Hx. pose proof (pst_in_img_A x Hx) as Himg. pose proof (A_prog_segs_low x Himg) as Hlow.
  unfold kLowMemEnd in Hlow. apply HK; [lia|]. intros Hc. specialize (HCb x Hc).
  exact (blk_img_x rsegs B ARx LAWS ly S Hp W mem md b m x HAR Hbm ltac:(lia) Himg). }
unfold prh_ledger. split; [|split; [exact HND | split; [|exact HP]]].
- destruct HG as (VL & VP & VC & VF & VR & (VM & VMb) & (VO & VOb) & Hb).
  split; [apply (VK _ _ _ VL); intros x Hx; apply KS; unfold prh_pst; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx|].
  split; [apply (VK _ _ _ VP); intros x Hx; apply KS; unfold prh_pst; apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx|].
  split; [apply (VK _ _ _ VC); intros x Hx; apply KS; unfold prh_pst; do 2 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx|].
  split; [apply (VK _ _ _ VF); intros x Hx; apply KS; unfold prh_pst; do 3 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx|].
  split; [apply (VK _ _ _ VR); intros x Hx; apply KS; unfold prh_pst; do 4 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx|].
  (* #102's g_most and g_own_ran_out (prh_most / prh_own, PRH_Base.v): prh_pst's sixth and seventh cells *)
  split; [split; [apply (VK _ _ _ VM); intros x Hx; apply KS; unfold prh_pst; do 5 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx | exact VMb]|].
  split; [split; [apply (VK _ _ _ VO); intros x Hx; apply KS; unfold prh_pst; do 6 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Hx | exact VOb]|].
  exact Hb.
- revert HF. apply Forall_impl. intros [a kk] (K0 & Kin & Khp & Kal & Kv). cbn [fst snd] in *.
  refine (conj K0 (conj Kin (conj Khp (conj Kal _)))).
  apply (VK _ _ _ Kv). intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Kin) as (B1 & B2 & B3 & Bapp & Bown & _).
  assert (Hreq2 : req_size (kk + cf_head) = kk + cf_head) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
  rewrite Hreq2 in B3.
  apply HK; [lia|]. intros Hc. pose proof (HCb x Hc) as Hxb.
  destruct (Z.eq_dec (a - cf_head) b) as [Heq|Hne].
  + rewrite Heq in Khp. pose proof (HCh Khp x Hc). lia.
  + assert (Hneq : (b, m) <> (a - cf_head, kk + cf_head)) by (intros E; injection E as E1 _; lia).
    pose proof (sep_blocks_x rsegs B ARx LAWS ly S Hp W mem md b m (a - cf_head) (kk + cf_head) HAR Hbm Kin Hneq) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq2 in Hd. lia.
Qed.

(* ---- the memory invariant every run of the walk carries (YSRrMemnorm.v's keep form at the entry memory) ---- *)
Definition es_P (E : es_e) : (word -> option byte) -> Prop :=
  fun m => YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs m.
Lemma es_plaw : forall E, srr_inv_laws rsegs (es_P E).
Proof.
intros E. exact (YSRrMemnorm.srr_inv_laws_imp rsegs _ (e_mem E) (YSRrMemnorm.srr_inv_laws_memnorm_k rsegs)).
Qed.

(* ---- the passage from the end of the walk to the kit's post ---- *)
Lemma es_res_q : forall E (W' : world rsegs) mem' (regs' : bvmap 5 word) r ly' S' Hp' md',
  getr regs' 10 = w64 r -> ES_RES E W' mem' r ->
  (room_live_cf (e_S E) -> room_live_cf S') -> Hp' = e_Hp E -> S' = e_S E -> ablocks B ly' S' = ablocks B (e_ly E) (e_S E) ->
  prh_ledger (L := A_prog_listing) (PA := PI_prog_A) B ly' S' Hp' W' mem' (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E)
    (e_most E) (e_own E) ->
  ES_Q B E ly' S' Hp' W' regs' mem' md'.
Proof.
intros E W' mem' regs' r ly' S' Hp' md' H10 HR HRm HHp HSc HAB HL. unfold ES_Q, ES_RES in *.
split; [exact HRm|]. split; [exact HHp|]. split; [exact HSc|]. split; [exact HAB|]. split; [exact HL|].
revert HR. destruct (fst (fst (PjGrammar.jr_string (es_xs E) []))) as [[s rest]|]; intros HR.
- destruct HR as (-> & HR). split; [exact H10 | exact HR].
- destruct HR as (-> & HR). split; [exact H10 | exact HR].
Qed.

Lemma es_finish : forall E lyc Sc Hpc (regs' : bvmap 5 word) mem' md' k r,
  ajournal_x (SK := SK) rsegs B prh_pst ARx (STK_ex_string + e_d E) (es_sp E + e_d E) (es_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [] lyc Sc Hpc (e_W E) mem' md' k ->
  (forall a, es_sp E <= a < es_sp E + e_d E -> ~ inFP (es_FP E) a ->
     aview rsegs (w_H (e_W E)) mem' a = aview rsegs (w_H (e_W E)) (e_mem E) a) ->
  aregs_preserved (e_regs E) regs' ->
  Hpc = e_Hp E -> ablocks B lyc Sc = ablocks B (e_ly E) (e_S E) -> (room_live_cf (e_S E) -> room_live_cf Sc) ->
  Sc = e_S E -> (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs mem') ->
  prh_ledger (L := A_prog_listing) (PA := PI_prog_A) B lyc Sc Hpc (e_W E) mem' (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E)
    (e_most E) (e_own E) ->
  getr regs' 10 = w64 r -> ES_RES E (e_W E) mem' r ->
  ES_POST B ARx SK E (e_W E) (mkCfg (mkst regs' (getr (e_regs E) 1) mem' (seg_rom rsegs)) md').
Proof.
intros E lyc Sc Hpc regs' mem' md' k r HJ HWIN HAR HHp HAB HRm HSc HMN HL H10 HR.
unfold ES_POST, fpostWm, fpostW. exists lyc, Sc, Hpc, regs', mem', md', k.
split; [reflexivity|]. split; [exact HJ|]. split; [exact HWIN|]. split; [exact HAR|].
unfold fQmn. split; [|exact HMN].
exact (es_res_q E (e_W E) mem' regs' r lyc Sc Hpc md' H10 HR HRm HHp HSc HAB HL).
Qed.

(* ---- ESB from one cut state to the next: the journal at the new state, the bytes written only in the scratch, the
   callee frame below sp or the two hex4 out-slots 32(sp) .. 39(sp), and ESB's registers kept ---- *)
Definition ES_WR (E : es_e) (a : Z) : Prop :=
  (e_scr E <= a < e_scr E + es_len E + 1) \/ (es_SP E - 16 <= a < es_SP E) \/ (es_SP E + 32 <= a < es_SP E + 40).


Lemma es_esb_step : forall E lyc Sc Hpc regs memc mdc k (regs' : bvmap 5 word) mem' md' (C : Z -> Prop),
  8 <= cf_head -> ES_PRE B ARx E -> ESB B ARx SK E lyc Sc Hpc regs memc mdc k ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (STK_ex_string + e_d E) (es_sp E + e_d E) (es_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [] lyc Sc Hpc (e_W E) mem' md' k ->
  (forall a, C a -> ES_WR E a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ C a -> aview rsegs (w_H (e_W E)) mem' a = aview rsegs (w_H (e_W E)) memc a) ->
  (forall r, In r ES_REGS -> getr regs' r = getr regs r) ->
  (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs mem') ->
  ESB B ARx SK E lyc Sc Hpc regs' mem' md' k.
Proof.
intros E lyc Sc Hpc regs memc mdc k regs' mem' md' C Hhead HP HB HJ' HCW HK HR HMN'.
pose proof (es_geom E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HP as HP0. unfold ES_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (b & m & Hbm & Hbs & Hsm & Hhd) & _).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC0 & HC8 & HC16 & HC24 & R2 & R8 & R18 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof (es_cur_ar E lyc Sc Hpc regs memc mdc k HB) as HAR.
assert (Hbm' : In (b, m) (ablocks B lyc Sc)) by (rewrite HAB; exact Hbm).
assert (HnC : forall a, (e_scr E + es_len E + 1 <= a \/ a < e_scr E) -> (es_SP E <= a \/ a < es_SP E - 16) ->
  (es_SP E + 40 <= a \/ a < es_SP E + 32) -> 0 <= a < 2 ^ 64 -> aview rsegs (w_H (e_W E)) mem' a = aview rsegs (w_H (e_W E)) memc a).
{ intros a H1 H2 H3 H4. apply HK; [exact H4|]. intros Hc. destruct (HCW a Hc) as [Hw|[Hw|Hw]]; lia. }
unfold es_SP in *.
assert (VK : forall a (w : nat) v, val_mem rsegs (rdW (e_W E) memc) a w v ->
  (forall x, a <= x < a + Z.of_nat w -> aview rsegs (w_H (e_W E)) mem' x = aview rsegs (w_H (e_W E)) memc x) ->
  val_mem rsegs (rdW (e_W E) mem') a w v) by (intros a w v Hv HE; exact (es_val_kept (w_H (e_W E)) memc mem' a w v HE Hv)).
unfold ESB. cbv zeta. unfold es_SP.
refine (conj HJ' _). split.
{ intros a Ha Hn. rewrite HnC; [exact (HWIN a Ha Hn) | | lia | lia | lia].
  destruct (Z_lt_le_dec a (e_scr E)) as [h|h]; [right; exact h|]. left.
  destruct (Z_lt_le_dec a (e_scr E + es_len E + 1)) as [h2|h2]; [|exact h2]. exfalso. apply Hn.
  exists (e_scr E, e_scr E + es_len E + 1). split; [left; reflexivity | cbn [fst snd]; lia]. }
split; [intros a Ha; rewrite HnC; [exact (HQP a Ha) | unfold es_len in *; lia | lia | lia | lia]|].
split; [exact HHp|]. split; [exact HAB|]. split; [exact HRK|].
split.
{ apply (es_ledger_keep lyc Sc Hpc (e_W E) memc mdc mem' _ _ _ _ _ _ _ (fun a => C a /\ a < alloc_ceiling) b m Hhead HAR Hbm').
  - intros a (Hc & Ha). destruct (HCW a Hc) as [Hw|[Hw|Hw]]; unfold es_SP in *; lia.
  - intros Hb a (Hc & Ha). rewrite HHp in Hb. specialize (Hhd Hb).
    destruct (HCW a Hc) as [Hw|[Hw|Hw]]; unfold es_SP in *; lia.
  - intros a Ha Hn. apply HK; [lia|]. intros Hc. exact (Hn (conj Hc (proj2 Ha))).
  - exact HLED. }
split.
{ intros o r Hin. apply VK; [exact (HSAV o r Hin)|]. intros x Hx.
  assert (Hfo : Forall (fun pr : Z * Z => 40 <= fst pr <= 136) es_saved) by (repeat constructor; cbn; lia).
  pose proof (proj1 (Forall_forall _ _) Hfo _ Hin) as Ho. cbn [fst] in Ho.
  apply HnC; unfold es_len in *; lia. }
split; [apply VK; [exact HC0|]; intros x Hx; apply HnC; unfold es_len in *; cbn in Hx; lia|].
split; [apply VK; [exact HC8|]; intros x Hx; apply HnC; unfold es_len in *; cbn in Hx; lia|].
split; [apply VK; [exact HC16|]; intros x Hx; apply HnC; unfold es_len in *; cbn in Hx; lia|].
split; [apply VK; [exact HC24|]; intros x Hx; apply HnC; unfold es_len in *; cbn in Hx; lia|].
assert (HR' : forall r, In r ES_REGS -> forall v, getr regs r = v -> getr regs' r = v)
  by (intros r Hr v Hv; rewrite (HR r Hr); exact Hv).
repeat match goal with |- _ /\ _ => split end;
  first [ exact HSc | exact HMN' | apply (HR' 2%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); assumption
        | apply (HR' 3%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); assumption
        | apply (HR' 4%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); assumption
        | apply (HR' 8%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); assumption
        | apply (HR' 18%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); assumption
        | apply (HR' 22%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); assumption
        | apply (HR' 23%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); assumption
        | apply (HR' 24%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); assumption
        | apply (HR' 25%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); assumption
        | apply (HR' 26%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); assumption
        | apply (HR' 27%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); assumption ].
Qed.

(* ---- one byte v stored at the output position o = scr + |acc|: ESB at the new state and the scratch acc ++ [v] ---- *)
Lemma es_store_step : forall E lyc Sc Hpc regs memc mdc k (regs' : bvmap 5 word) mem' md' acc v,
  8 <= cf_head -> ES_PRE B ARx E -> ESB B ARx SK E lyc Sc Hpc regs memc mdc k ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (STK_ex_string + e_d E) (es_sp E + e_d E) (es_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [] lyc Sc Hpc (e_W E) mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_scr E + Z.of_nat (length acc) ->
     aview rsegs (w_H (e_W E)) mem' a = aview rsegs (w_H (e_W E)) memc a) ->
  (forall r, In r ES_REGS -> getr regs' r = getr regs r) ->
  es_P E mem' ->
  Z.of_nat (length acc) <= es_len E ->
  garr8 rsegs (rdW (e_W E) memc) (e_scr E) acc ->
  val_mem rsegs (rdW (e_W E) mem') (e_scr E + Z.of_nat (length acc)) 1 v -> 0 <= v < 256 ->
  ESB B ARx SK E lyc Sc Hpc regs' mem' md' k /\ garr8 rsegs (rdW (e_W E) mem') (e_scr E) (acc ++ [v]).
Proof.
intros E lyc Sc Hpc regs memc mdc k regs' mem' md' acc v Hh HP HB HJ' HK HR HPM Hl GA VO Hv.
split.
- apply (es_esb_step E lyc Sc Hpc regs memc mdc k regs' mem' md' (fun a => a = e_scr E + Z.of_nat (length acc))
    Hh HP HB HJ'); [| | exact HR | exact HPM].
  + intros a ->. left. lia.
  + intros a Ha Hn. exact (HK a Ha Hn).
- apply es_garr8_app.
  + apply (es_garr8_kept (w_H (e_W E)) memc mem'); [|exact GA]. intros a Ha. apply HK; [|lia].
    pose proof (es_geom E HP) as G. unfold ES_GEOM in G. cbv zeta in G. lia.
  + apply es_garr8_one; [exact VO | exact Hv].
Qed.
End g.
