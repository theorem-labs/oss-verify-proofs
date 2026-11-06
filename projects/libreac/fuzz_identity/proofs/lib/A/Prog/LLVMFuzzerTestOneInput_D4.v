(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530,
   1556-1561, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Segment D4 of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan 0x81170 .. 0x813b4): the model-name case of
   the record switch. The case is entered only from 0x80d9c (beq s11,0x1000) and leaves only to the join 0x813b4.
     0x81170..0x81180  memchr(&id.model_name, 0, 17)          (MemchrDef.amemchr_realizes)
     0x81184 bnez s4   has_model_name; 0x8118c bnez a0 (a NUL was found); 0x811a0 bne a0,s2 (w <> 0)
     0x811b4 bgeu      n >= 1 + w;     0x811c8 bcmp(&id.model_name, pl + 1, w) == 0 (YG0d.abcmp_realizes)
     0x811e0 / 0x811e4 the stopped-early test w < 16 /\ 1 + w < n; then the shadow test of pl[1 + w]
                       (0x811ec..0x81200) and pl[1 + w] == 0 (0x813a4..0x813ac)
   Every abort branch is decided by a fact of the symbolic state: the plain model's ING_name record
   (RcIdentModel.ing_name) gives has_model_name = 1, the NUL at w = name_len pl with 1 <= w <= 16 and w + 1 <= n, the
   name bytes equal to pl[1 .. 1 + w), and pl[1 + w] = 0 when w < 16 and 1 + w < n.
   The walk runs on a sub-journal at sp = mf (YCbq.ajournal_sub_init, 2 * ESTACK, the bcmp window) and composes it
   with the boundary's journal at the end (YCbq.ajournal_sub). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import WrapRo MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model of the record (RcIdentModel.ing_name), as the walk reads it ------------------------------ *)
Module D4Model.
Import RcIdentModel.
Lemma fz_lt : forall (l : list byte) j, (j < first_zero l)%nat -> bz (nth j l (zb 0)) <> 0.
Proof.
induction l as [|x l IH]; intros j H; cbn [first_zero] in H; [lia|].
destruct (Z.eqb_spec (bz x) 0) as [E|E]; [lia|].
destruct j as [|j]; [exact E|]. cbn [nth]. apply IH. lia.
Qed.
Lemma fz_hit : forall (l : list byte), (first_zero l < length l)%nat -> bz (nth (first_zero l) l (zb 0)) = 0.
Proof.
induction l as [|x l IH]; intros H; cbn [first_zero length] in *; [lia|].
destruct (Z.eqb_spec (bz x) 0) as [E|E]; [exact E|]. cbn [nth]. apply IH. lia.
Qed.
Lemma nth_skip1 : forall (l : list byte) j d, nth j (skipn 1 l) d = nth (1 + j) l d.
Proof. intros [|x l] j d; [destruct j; reflexivity | reflexivity]. Qed.
Lemma nth_firstn_lt : forall (l : list byte) k j d, (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof. induction l as [|x l IH]; intros [|k] [|j] d H; cbn; try reflexivity; try lia. apply IH. lia. Qed.
Lemma bz_zb1 : bz (zb 1) = 1. Proof. reflexivity. Qed.
Lemma bz_zb0 : bz (zb 0) = 0. Proof. reflexivity. Qed.
(* ING's model-name case on a record it accepts. *)
Lemma d4_ing : forall (idb0 p : list byte), length idb0 = 38%nat -> fst (ING idb0 ADDR_MODEL_NAME p) = 1 ->
  (2 <= length p)%nat /\ (1 <= name_len p <= 16)%nat /\ (name_len p + 1 <= length p)%nat /\
  has_model_name (snd (ING idb0 ADDR_MODEL_NAME p)) = 1 /\
  (forall j, (j < name_len p)%nat ->
     nthb (snd (ING idb0 ADDR_MODEL_NAME p)) (3 + j) = nthb p (1 + j) /\ bz (nthb p (1 + j)) <> 0) /\
  bz (nthb (snd (ING idb0 ADDR_MODEL_NAME p)) (3 + name_len p)) = 0 /\
  ((name_len p <= 15)%nat -> (name_len p + 1 < length p)%nat -> bz (nthb p (1 + name_len p)) = 0).
Proof.
intros idb0 p Hl0 Hr.
change (ING idb0 ADDR_MODEL_NAME p) with (ing_name idb0 p) in *.
assert (Hw : name_len p = Nat.min (first_zero (firstn (Nat.min (length p - 1) 16) (skipn 1 p))) (Nat.min (length p - 1) 16))
  by reflexivity.
remember (name_len p) as w eqn:Ew in *.
unfold ing_name in *. cbv zeta in *. rewrite <- Ew in *.
destruct ((2 <=? length p)%nat && (1 <=? w)%nat) eqn:C; [|cbn [fst] in Hr; discriminate].
apply andb_true_iff in C as [C1 C2]. apply Nat.leb_le in C1, C2. cbn [snd]. unfold OFF_NAME, OFF_HAS_NAME.
remember (Nat.min (length p - 1) 16) as n' eqn:En' in *.
remember (firstn n' (skipn 1 p)) as l eqn:El in *.
assert (Ll : length l = n') by (rewrite El, length_firstn, length_skipn; lia).
assert (Hw16 : (w <= 16)%nat) by lia.
assert (Hwp : (w <= length p - 1)%nat) by lia.
assert (Hl : forall j, (j < n')%nat -> nth j l (zb 0) = nth (1 + j) p (zb 0)).
{ intros j Hj. rewrite El, nth_firstn_lt by exact Hj. apply nth_skip1. }
assert (Lf : length (firstn w (skipn 1 p)) = w) by (rewrite length_firstn, length_skipn; lia).
assert (Lbs : length (firstn w (skipn 1 p) ++ [zb 0]) = S w) by (rewrite length_app, Lf; cbn [length]; lia).
assert (L1 : length (upd idb0 3 (firstn w (skipn 1 p) ++ [zb 0])) = 38%nat) by (rewrite upd_length; [exact Hl0 | lia]).
assert (Hin : forall j, (j <= w)%nat ->
  nthb (upd (upd idb0 3 (firstn w (skipn 1 p) ++ [zb 0])) 20 [zb 1]) (3 + j) = nth j (firstn w (skipn 1 p) ++ [zb 0]) (zb 0)).
{ intros j Hj. unfold nthb. rewrite SlotModel.nth_upd_before by lia.
  rewrite SlotModel.nth_upd_in by lia. f_equal. lia. }
split; [exact C1|]. split; [split; [exact C2 | exact Hw16]|]. split; [lia|].
split.
{ unfold has_model_name, nthb, OFF_HAS_NAME.
  assert (H20 : (20 <= length (upd idb0 3 (firstn w (skipn 1 p) ++ [zb 0])))%nat) by (rewrite L1; lia).
  rewrite (SlotModel.nth_upd_in _ _ 20 20 (zb 0) H20) by (cbn [length]; lia).
  rewrite Nat.sub_diag. cbn [nth]. exact bz_zb1. }
split.
{ intros j Hj. rewrite (Hin j) by lia. rewrite app_nth1 by lia.
  rewrite nth_firstn_lt by exact Hj. rewrite nth_skip1. split; [reflexivity|].
  unfold nthb. rewrite <- (Hl j) by lia. apply fz_lt. lia. }
split.
{ rewrite (Hin w) by lia. rewrite app_nth2 by lia. rewrite Lf, Nat.sub_diag. exact bz_zb0. }
intros H15 Hlt. assert (Hwn : (w < n')%nat) by lia.
assert (Hfz : first_zero l = w) by lia.
unfold nthb. rewrite <- (Hl w Hwn). rewrite <- Hfz at 1. apply fz_hit. lia.
Qed.
(* A model-name record that ING accepts (r = 1) and what the harness's checks read of it. *)
Lemma d4_model : forall inp i,
  SlotModel.rec_addr inp i = ADDR_MODEL_NAME -> SlotModel.rec_r inp i = 1 ->
  (2 <= length (SlotModel.rec_pl inp i))%nat /\
  (1 <= name_len (SlotModel.rec_pl inp i) <= 16)%nat /\
  (name_len (SlotModel.rec_pl inp i) + 1 <= length (SlotModel.rec_pl inp i))%nat /\
  has_model_name (SlotModel.rec_id inp (S i)) = 1 /\
  (forall j, (j < name_len (SlotModel.rec_pl inp i))%nat ->
     nthb (SlotModel.rec_id inp (S i)) (3 + j) = nthb (SlotModel.rec_pl inp i) (1 + j) /\
     bz (nthb (SlotModel.rec_pl inp i) (1 + j)) <> 0) /\
  bz (nthb (SlotModel.rec_id inp (S i)) (3 + name_len (SlotModel.rec_pl inp i))) = 0 /\
  ((name_len (SlotModel.rec_pl inp i) <= 15)%nat ->
   (name_len (SlotModel.rec_pl inp i) + 1 < length (SlotModel.rec_pl inp i))%nat ->
   bz (nthb (SlotModel.rec_pl inp i) (1 + name_len (SlotModel.rec_pl inp i))) = 0).
Proof.
intros inp i Ha Hr.
change (SlotModel.rec_id inp (S i)) with
  (snd (ING (SlotModel.rec_id inp i) (SlotModel.rec_addr inp i) (SlotModel.rec_pl inp i))).
unfold SlotModel.rec_r in Hr. rewrite Ha in Hr |- *.
exact (d4_ing _ _ (SlotModel.rec_id_length inp i) Hr).
Qed.
End D4Model.

(* ---- the symbolic state at 0x81170 ------------------------------------------------------------------------------ *)
(* Atoms: 32 the shadow base, 33 pl, 34 &id.model_name (SF+355), 35 the record body's address, 36 &before (SF+32),
   37 the record index, 38 w = name_len pl, 39 pl + 1 + w. The machine frame (atom 9 = s1) is read only. *)
Definition d4_SB : Z := 0x7fff8000.
Definition d4_Bx : sv := SOff 32 0.
Definition d4_Bspan : Z * Z := (d4_SB, d4_SB + 2 ^ 44 - 1).
Definition d4_mfr : YP09.region :=
YP09.mkRegion (Some 9%nat) 88 184 88 88
[YP09.mkChunk 88 (CVal 8 (SOff 36 0)); YP09.mkChunk 128 (CVal 8 (SOff 34 0));
 YP09.mkChunk 136 (CVal 8 (SOff 35 0)); YP09.mkChunk 152 (CVal 8 (SOff 33 0));
 YP09.mkChunk 160 (CVal 8 (SOff 37 0)); YP09.mkChunk 176 (CVal 8 (SOff 32 0))].
(* pl[1 + w], added on the path that reads it (w < 16 and 1 + w < n). *)
Definition d4_plr : YP09.region := YP09.mkRegion (Some 39%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition d4_facts0 : facts :=
mkFacts [(32%nat, mkAF d4_SB d4_SB 0); (20%nat, mkAF 1 1 0); (22%nat, mkAF 2 255 0); (38%nat, mkAF 1 16 0);
 (39%nat, mkAF 4096 (2 ^ 47 - 16) 0)]
[mkAC BC_GEU (SOff 22 0) (SOff 38 1)]
[(SAlu ALU_ADD (SOff 33 0) (SOff 38 1), SOff 39 0)].
Definition d4_ss0 : sstate := mkSS 0xa64 sr_atoms [d4_mfr] None d4_facts0.
Definition d4_extra (pl NA BODY BEF I w T : Z) : list word := map (Z_to_bv 64) [d4_SB; pl; NA; BODY; BEF; I; w; T].

Lemma d4_Z_to_bv_mod64 : forall t, Z_to_bv 64 (t mod 2 ^ 64) = Z_to_bv 64 t.
Proof.
intros t. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition d4_E (regs : bvmap 5 word) (pl NA BODY BEF I w T : Z) : env :=
Eimg (Ereg regs (d4_extra pl NA BODY BEF I w T)).

Lemma d4_vm_mod64 : forall m a v, val_mem SEGS m a 8 v -> val_mem SEGS m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte.
assert (P : 2 ^ (8 * Z.of_nat 8) = 2 ^ 64) by reflexivity. rewrite !P.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma d4_bytes_aview : forall (W : world SEGS) mem a (bs : list byte) j,
  bytes_at8 W mem a bs -> (j < length bs)%nat ->
  aview SEGS (w_H W) mem (a + Z.of_nat j) = Some (RcIdentModel.bz (RcIdentModel.nthb bs j)).
Proof.
intros W mem a bs j Hb Hj. unfold bytes_at8, garr8 in Hb.
destruct (Hb j ltac:(rewrite length_map; exact Hj)) as [Hv Hr].
rewrite (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). f_equal.
unfold RcIdentModel.bz, RcIdentModel.nthb, RcIdentModel.zb.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). rewrite map_nth. reflexivity.
Qed.
Lemma d4_frame_ro : forall E (rs : smem) (m m' : word -> option byte) H a,
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs m m' H a Hro HF. apply (aview_eq_of SEGS). unfold mrestrict. rewrite HF; [reflexivity|].
intros (r & Hin & Ha). rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
(* The memory below the allocator's ceiling agrees: the walk writes only the machine stack below sp. *)
Definition d4_low (W : world SEGS) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Lemma d4_vm_keep : forall (W : world SEGS) m m' a n v,
  d4_low W m m' -> 0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof. intros W m m' a n v HL H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros k Hk. apply HL. lia. Qed.
Lemma d4_vm_keep_hi : forall (W : world SEGS) m m' lo hi a n v,
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= hi -> hi <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof. intros W m m' lo hi a n v HK Hh H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros k Hk. apply HK; lia. Qed.
Lemma d4_bytes_keep : forall (W : world SEGS) m m' a bs,
  d4_low W m m' -> 0 <= a -> a + Z.of_nat (length bs) <= alloc_ceiling ->
  bytes_at8 W m a bs -> bytes_at8 W m' a bs.
Proof.
intros W m m' a bs HL H0 H1 Hb j Hj. destruct (Hb j Hj) as [Hv Hr]. split; [|exact Hr].
rewrite length_map in Hj. eapply d4_vm_keep; [exact HL | lia | cbn; lia | exact Hv].
Qed.
Lemma d4_zs_keep : forall (W : world SEGS) m m' a n,
  d4_low W m m' -> 0 <= a -> 0 <= n -> a + n < 2 ^ 47 ->
  sh_zero W m a n -> sh_zero W m' a n.
Proof.
intros W m m' a n HL H0 Hn H1 Hz i Hi. unfold sh_zero, zero_shadow in *. rewrite HL; [exact (Hz i Hi)|].
pose proof (asan_consts) as (C1 & _). unfold shadow_of_addr, SHADOW_OFF.
assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= a / 8) by (apply Z.div_pos; lia).
assert (i < n / 8 + 1) by lia. assert (n / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
lia.
Qed.
Lemma d4_blk_keep : forall (W : world SEGS) m m' a n,
  d4_low W m m' -> 0 <= a -> 0 <= n -> a + n + 8 < 2 ^ 47 ->
  sh_blk W m a n -> sh_blk W m' a n.
Proof.
intros W m m' a n HL H0 Hn H1 Hb. unfold sh_blk in *. apply (block_shadow_agree (aview SEGS (w_H W) m)); [|exact Hb].
intros i Hi. apply HL. pose proof (asan_consts) as (C1 & _). unfold shadow_of_addr, SHADOW_OFF.
assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= a / 8) by (apply Z.div_pos; lia).
assert ((n + 7) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
lia.
Qed.
Lemma d4_low_of_keep : forall (W : world SEGS) m m' lo hi,
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  alloc_ceiling <= lo -> d4_low W m m'.
Proof.
intros W m m' lo hi HK Hlo a Ha. pose proof (asan_consts) as (C1 & _). apply HK; lia.
Qed.
Lemma d4_aro_keep : forall (B0 : asyms) (W : world SEGS) m m', d4_low W m m' ->
  aro_unowned SEGS B0 (aview SEGS (w_H W) m) -> aro_unowned SEGS B0 (aview SEGS (w_H W) m').
Proof.
intros B0 W m m' HL HR. apply (aro_unowned_keep SEGS B0 _ _ HR). intros a Ha _ _. apply HL.
destruct Ha as (sg & Hsg & _ & Hr).
assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
pose proof (pa_img_range a Hi). pose proof (asan_consts) as (C1 & _). lia.
Qed.
Lemma st_ok_pi_add_cond' : forall E ss ms c a b,
  st_ok_pi SEGS VAL E ss ms -> branch_taken c (sv_denot E a) (sv_denot E b) = true ->
  st_ok_pi SEGS VAL E (add_cond ss (mkAC c a b)) ms.
Proof. intros E ss ms c a b HS Hc. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_add_cond SEGS E _ ms c a b HS Hc). Qed.

Lemma d4_mod8 : forall x, x mod 32 = 0 -> (x + 352) mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
replace (x + 352) with ((4 * (x / 32) + 44) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma d4_ra_keep : forall (W : world SEGS) m m' a len,
  d4_low W m m' -> 0 <= a -> a + len <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a len -> range_addressable (aview SEGS (w_H W) m') SHADOW_OFF a len.
Proof.
intros W m m' a len HL H0 H1 HR. apply (range_addressable_agree (aview SEGS (w_H W) m)); [|exact HR].
intros x Hx. apply HL. pose proof (asan_consts) as (C1 & _). unfold shadow_of_addr, SHADOW_OFF.
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
Qed.
(* What the boundary's bytes say at 0x81170, through the plain model (D4Model.d4_model). *)
Lemma d4_state2 : forall g pos i pl (W2 : world SEGS) mem2,
  id_at g pos (S i) W2 mem2 -> bytes_at8 W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) ->
  SlotModel.rec_addr (e_pl g) i = RcIdentModel.ADDR_MODEL_NAME -> SlotModel.rec_r (e_pl g) i = 1 ->
  SFa g pos mod 32 = 0 ->
  forall w k, w = Z.of_nat (RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i)) -> k = SlotModel.rec_k (e_pl g) i ->
  (1 <= w <= 16 /\ w + 1 <= k /\ k <= 255 /\ RcIdentModel.has_model_name (m_id g (S i)) = 1) /\
  (forall a, SFa g pos + 352 <= a < SFa g pos + 390 -> aview SEGS (w_H W2) mem2 a <> None) /\
  (forall j, 0 <= j < w -> exists b, aview SEGS (w_H W2) mem2 (SFa g pos + 355 + j) = Some b /\ b <> 0 /\
     aview SEGS (w_H W2) mem2 (pl + 1 + j) = Some b) /\
  aview SEGS (w_H W2) mem2 (SFa g pos + 355 + w) = Some 0 /\
  (forall a, pl <= a < pl + k -> aview SEGS (w_H W2) mem2 a <> None) /\
  (w <= 15 -> w + 1 < k -> val_mem SEGS (mrestrict (w_H W2) mem2) (pl + 1 + w) 1 0) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (SFa g pos + 352) 32.
Proof.
intros g pos i pl W2 mem2 (Hidb & Hidz & _) Hpl Ha Hr H32 w k Ew Ek.
destruct (D4Model.d4_model (e_pl g) i Ha Hr) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
pose proof (SlotModel.rec_pl_length (e_pl g) i) as Lp. pose proof (SlotModel.rec_k_range (e_pl g) i) as Kr.
pose proof (SlotModel.rec_id_length (e_pl g) (S i)) as Lid. unfold RcIdentModel.ID_SIZE in Lid.
unfold m_id, V_id, N_id in *.
assert (Lk : Z.of_nat (length (SlotModel.rec_pl (e_pl g) i)) = k) by lia.
split; [split; [lia | split; [lia | split; [lia | exact M4]]] |].
refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
- intros a Ha0.
  assert (Ea : a = SFa g pos + 352 + Z.of_nat (Z.to_nat (a - (SFa g pos + 352)))) by lia.
  rewrite Ea, (d4_bytes_aview W2 mem2 _ _ _ Hidb) by lia. discriminate.
- intros j Hj. exists (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) (1 + Z.to_nat j))).
  destruct (M5 (Z.to_nat j) ltac:(lia)) as [Q1 Q2].
  assert (Ea : SFa g pos + 355 + j = SFa g pos + 352 + Z.of_nat (3 + Z.to_nat j)) by lia.
  assert (Eb : pl + 1 + j = pl + Z.of_nat (1 + Z.to_nat j)) by lia.
  rewrite Ea, Eb, (d4_bytes_aview W2 mem2 _ _ _ Hidb) by lia. rewrite (d4_bytes_aview W2 mem2 _ _ _ Hpl) by lia.
  rewrite Q1. split; [reflexivity|]. split; [|reflexivity]. intros E0. apply Q2. exact E0.
- assert (Ea : SFa g pos + 355 + w = SFa g pos + 352 + Z.of_nat (3 + RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i))) by lia.
  rewrite Ea, (d4_bytes_aview W2 mem2 _ _ _ Hidb) by lia. rewrite M6. reflexivity.
- intros a Ha0. assert (Ea : a = pl + Z.of_nat (Z.to_nat (a - pl))) by lia.
  rewrite Ea, (d4_bytes_aview W2 mem2 _ _ _ Hpl) by lia. discriminate.
- intros H15 Hlt.
  assert (Hj : (1 + RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i) < length (SlotModel.rec_pl (e_pl g) i))%nat) by lia.
  destruct (Hpl _ ltac:(rewrite length_map; exact Hj)) as [Hv _].
  assert (Ea : pl + 1 + w = pl + Z.of_nat (1 + RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i))) by lia.
  assert (Ev : nth (1 + RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i))
    (map (fun b : byte => bv_unsigned b) (SlotModel.rec_pl (e_pl g) i)) 0 = 0).
  { rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). rewrite map_nth.
    exact (M7 ltac:(lia) ltac:(lia)). }
  rewrite Ev in Hv. rewrite Ea. exact Hv.
- apply (zero_shadow_range _ _ (SFa g pos + 352) 32 (d4_mod8 _ H32) eq_refl). intros i0 Hi0. apply Hidz.
  change (32 / 8) with 4 in Hi0. change (38 / 8) with 4. exact Hi0.
Qed.
(* The two live tests of the stopped-early check. *)
Lemma d4_bc1 : forall Ex w, ew Ex 38 = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot Ex (SLit 15)) (sv_denot Ex (SOff 38 0)) = (15 <? w).
Proof.
intros Ex w H Hw. rewrite branch_ltu_U, U_SLit, U_SOff, H, unsigned_lit_small by lia.
unfold zcanon, M64. rewrite !Z.mod_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma d4_bc2 : forall Ex w k, ew Ex 38 = Z_to_bv 64 w -> ew Ex 22 = Z_to_bv 64 k -> 0 <= w < 2 ^ 63 -> 0 <= k < 2 ^ 63 ->
  branch_taken BC_GEU (sv_denot Ex (SOff 38 1)) (sv_denot Ex (SOff 22 0)) = negb (w + 1 <? k).
Proof.
intros Ex w k H1 H2 Hw Hk. rewrite branch_geu_U, !U_SOff, H1, H2, !unsigned_lit_small by lia.
unfold zcanon, M64. rewrite Z.add_0_r, !Z.mod_small by lia. reflexivity.
Qed.
(* pl[1 + w] as a region of the symbolic state, on the path that reads it. *)
Lemma d4_plr_ok : forall Ex (m : word -> option byte) T, ew Ex 39 = Z_to_bv 64 T -> 0 <= T -> T + 1 <= 2 ^ 64 ->
  val_mem SEGS m T 1 0 -> region_ok SEGS Ex m d4_plr.
Proof.
intros Ex m T H39 H0 H1 Hv. unfold region_ok, d4_plr.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H39, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS Ex m T 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Hv].
Qed.
Lemma d4_plr_disj : forall Ex T mf, ew Ex 39 = Z_to_bv 64 T -> ew Ex 9 = Z_to_bv 64 mf -> 0 <= T -> T + 1 <= mf + 88 ->
  0 <= mf -> mf + 184 <= 2 ^ 64 -> all_disjoint Ex d4_plr [d4_mfr].
Proof.
intros Ex T mf H39 H9 H0 H1 H2 H3. cbn [all_disjoint]. split; [|exact Logic.I].
unfold extent_disjoint, d4_plr, d4_mfr. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite H39, H9, !unsigned_lit_small by lia. lia.
Qed.

Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section the contract and the boundaries are stated in (LLVMFuzzerTestOneInput.v, _inv.v). *)
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation CASEM := (inv_caseM B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation TAIL := (inv_tail B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

(* ---- what the segment takes ------------------------------------------------------------------------------------- *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IS___interceptor_trampoline_memchr).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
(* the read-only image: the contract's arodata_okS gives IdentBase's arodata_okP (LLVMFuzzerTestOneInput.v:154) *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
(* cgif lib/A/ACfh.v:162-164 (LLVMFuzzerTestOneInput.v:196-198) *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The memchr wrapper in the journal form (as YCbq.aj_bcmp_at for bcmp). *)
Lemma d4_memchr_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 n ->
  0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  src_ok SEGS W regsT memT x n -> amem_range x n ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
  aro_unowned SEGS B (aview SEGS (w_H W) memT) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IS___interceptor_trampoline_memchr)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\
    (exists kk, first_byte SEGS W memT x n 0 kk /\ getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x n o raw
HJ Ha0 Ha1 Ha2 Hn Hx Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsrc Hmr Hrx Hhx Haro.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AMEMCHR lyc Sc W regsT memT mdc x 0 n HPRE Ha0 Ha1 Ha2 ltac:(lia) Hn Hx Hxn Hsrc Hmr Hrx Hhx Haro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _) & _ & HQT).
  eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left. unfold ESTACK in *. lia.
- exact HAR2.
- reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* ---- the facts of the boundary the walk uses, in one place --------------------------------------------------------- *)
Lemma d4_prep : forall g pos mf i pl ly2 S2 W2 regs2 mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) ->
  frames S2 = [(4, pos)] ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  P_body B g pos mf i pl ly2 S2 W2 regs2 mem2 ->
  (alloc_ceiling <= mf - 2 * ESTACK /\ mf + 320 <= 2 ^ 47 /\ mf mod 32 = 0 /\ e_sp0 g - 336 <= mf <= e_sp0 g - 320 /\
   e_sp0 g mod 16 = 0 /\ e_sp0 g - LLVMF_STK <= mf - 2 * ESTACK) /\
  (4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 32 = 0 /\
   frame_addr ly2 4 pos = SFa g pos /\ fs_frame_bytes 4 = 1024) /\
  (In (pl, SlotModel.rec_k (e_pl g) i) (ablocks B ly2 S2) /\ 4096 <= pl /\
   pl + req_size (SlotModel.rec_k (e_pl g) i) <= alloc_ceiling) /\
  (e_pl g = [] \/ (0 <= e_p g /\ e_p g + Z.of_nat (length (e_pl g)) <= alloc_ceiling)) /\
  aro_unowned SEGS B (aview SEGS (w_H W2) mem2).
Proof.
intros g pos mf i pl ly2 S2 W2 regs2 mem2 md2 HJ1 HFR HEC HPB.
pose proof HJ1 as (HAR2 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstat & _).
pose proof Hstat as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HEC as (Hsp & Hs1 & Hs0 & Hmf & Hmf32 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & HPRE & _ & _ & _).
destruct HPB as (_ & (Hperm & _) & _).
pose proof (asan_consts) as (C1 & _).
assert (ES : ESTACK = 4096) by reflexivity. assert (ESK : STK_LLVMF = 16720) by reflexivity.
assert (Hsp0 : e_sp0 g <= 2 ^ 47) by (unfold e_sp0 in *; lia).
assert (Efa : frame_addr ly2 4 pos = SFa g pos).
{ unfold SFa, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (F1 & F2 & F3).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (F32 & _).
assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity.
rewrite Hfb, Efa in *.
assert (Hplin : In (pl, SlotModel.rec_k (e_pl g) i) (ablocks B ly2 S2)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hplin) as (_ & P4096 & Pceil & _).
refine (conj _ (conj _ (conj (conj Hplin (conj P4096 Pceil)) (conj _ _)))).
- unfold ESTACK in *. repeat split; lia.
- exact (conj F1 (conj F2 (conj F3 (conj F32 (conj eq_refl eq_refl))))).
- unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
  destruct HPRE as ((HAR0 & _) & _ & _ & _ & Hinp & Hlen & _).
  destruct Hinp as [[Hn0 _] | [Hn Hpin]].
  + left. destruct (e_pl g); [reflexivity | cbn in Hlen; lia].
  + right. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hpin) as (_ & Q4096 & Qceil & _).
    unfold req_size in Qceil. destruct (Z.eqb_spec (e_n g) 0); [lia|]. rewrite <- Hlen. lia.
- unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
  destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
  pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 (HRO _ HAROS)) as HAP.
  exact (aro_unowned_of_arodata SEGS pa_relro_lo pa_relro_hi B _ HAP).
Qed.

(* ---- the entry: the symbolic state at 0x81170 ------------------------------------------------------------------------ *)
Lemma d4_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem mf pl NA BODY BEF I w T k,
  getr regs 9 = w64 mf -> 0 <= mf -> mf + 184 <= 2 ^ 64 ->
  val_mem SEGS (rd W mem) (mf + 88) 8 BEF -> val_mem SEGS (rd W mem) (mf + 128) 8 NA ->
  val_mem SEGS (rd W mem) (mf + 136) 8 BODY -> val_mem SEGS (rd W mem) (mf + 152) 8 pl ->
  val_mem SEGS (rd W mem) (mf + 160) 8 I -> val_mem SEGS (rd W mem) (mf + 176) 8 SHADOW_OFF ->
  getr regs 20 = w64 1 -> getr regs 22 = w64 k -> 2 <= k <= 255 -> 1 <= w <= 16 -> w + 1 <= k ->
  4096 <= T <= 2 ^ 47 - 16 -> T = pl + 1 + w -> 0 <= pl ->
  st_ok_pi SEGS VAL (d4_E regs pl NA BODY BEF I w T) d4_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xa64)) mem (seg_rom SEGS))).
Proof.
intros W regs mem mf pl NA BODY BEF I w T k H9 Hmf0 Hmf1 V88 V128 V136 V152 V160 V176 H20 H22 Hk Hw Hwk HT ET Hpl.
rewrite restrict_mkst_fx.
set (E := d4_E regs pl NA BODY BEF I w T).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (d4_extra pl NA BODY BEF I w T)) n)
  by (intros n Hn; subst E; unfold d4_E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = getr regs 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E20 : ew E 20 = getr regs 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 20 20%bv eq_refl)).
assert (E22 : ew E 22 = getr regs 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 d4_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pl) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 NA) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 BODY) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 BEF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 I) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 w) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 T) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (B9 : base_val E (Some 9%nat) = mf) by (cbn [base_val]; rewrite E9, H9; unfold w64; apply unsigned_lit_small; lia).
assert (CH : forall off a X, ew E a = Z_to_bv 64 X -> val_mem SEGS (mrestrict (w_H W) mem) (mf + off) 8 X ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) mf {| c_off := off; YP09.c_val := CVal 8 (SOff a 0) |}).
{ intros off a X Ha HX. apply (chunk_ok_val SEGS E _ mf off 8 (SOff a 0) (X mod 2 ^ 64)).
  - cbn [sv_denot]. rewrite Ha, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply d4_Z_to_bv_mod64.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
  - cbn. lia.
  - exact (d4_vm_mod64 _ _ _ HX). }
unfold d4_ss0. apply pa_entry_st_ok_full.
- subst E. unfold d4_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, d4_mfr.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (CH 88 36%nat BEF E36 V88).
  + apply (CH 128 34%nat NA E34 V128).
  + apply (CH 136 35%nat BODY E35 V136).
  + apply (CH 152 33%nat pl E33 V152).
  + apply (CH 160 37%nat I E37 V160).
  + apply (CH 176 32%nat SHADOW_OFF E32 V176).
- apply pairwise_disjoint_of_extents. cbn. split; exact Logic.I.
- unfold facts_ok, d4_facts0. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  assert (U20 : bv_unsigned (ew E 20) = 1) by (rewrite E20, H20; reflexivity).
  assert (U22 : bv_unsigned (ew E 22) = k) by (rewrite E22, H22; unfold w64; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = d4_SB) by (rewrite E32; reflexivity).
  assert (U33 : bv_unsigned (ew E 33) = pl) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U38 : bv_unsigned (ew E 38) = w) by (rewrite E38; apply unsigned_lit_small; lia).
  assert (U39 : bv_unsigned (ew E 39) = T) by (rewrite E39; apply unsigned_lit_small; lia).
  split; [|split].
  + unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite U20, U22, U32, U38, U39.
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold d4_SB. repeat split; lia.
  + split; [|exact Logic.I]. unfold acond_ok; cbn [ac_c ac_a ac_b].
    rewrite branch_geu_U, !U_SOff, U22, U38. unfold zcanon, M64. rewrite !Z.mod_small by lia.
    apply negb_true_iff. apply Z.ltb_ge. lia.
  + split; [|exact Logic.I]. apply U_inj. rewrite U_SAlu, !U_SOff, U33, U38, U39. cbn [zalu_raw].
    assert (A1 : zcanon (pl + 0) = pl) by (unfold zcanon, M64; rewrite Z.mod_small by lia; lia).
    assert (A2 : zcanon (w + 1) = w + 1) by (unfold zcanon, M64; rewrite Z.mod_small by lia; lia).
    assert (A3 : zcanon (T + 0) = T) by (unfold zcanon, M64; rewrite Z.mod_small by lia; lia).
    rewrite A1, A2, A3. unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.

(* ---- the end: the join's boundary from the walk's last state ------------------------------------------------------ *)
Lemma d4_finish : forall g pos mf i pl ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat i + 3 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat i + 3) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat i + 3)) * (mo_malloc MT 256 + mo_free MT)) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  P_body B g pos mf i pl ly2 S2 W2 regs2 mem2 -> hw_at g pos (S i) W2 mem2 ->
  ajournal SEGS B (2 * ESTACK) mf [] ly2 S2 W2 mem2 md2 [] ly2 S2 W2 mem3 md3 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 -> getr regs3 8 = getr regs2 8 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 -> getr regs3 19 = getr regs2 19 ->
  getr regs3 22 = getr regs2 22 ->
  getr regs3 26 = w64 (e_p g + SlotModel.rec_body (e_pl g) i) -> getr regs3 24 = w64 (SFa g pos + V_before) ->
  getr regs3 25 = w64 pl -> getr regs3 21 = w64 (Z.of_nat i) ->
  TAIL g pos mf i pl W2 (cfg_at SEGS (BASE + 0xca8) regs3 mem3 md3).
Proof.
intros g pos mf i pl ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HJ1 HFR HK HMLE HMOK HEC HPB HHW HJ3 KEEP
  R2 R9 R8 R3 R4 R19 R22 R26 R24 R25 R21.
destruct (d4_prep g pos mf i pl ly2 S2 W2 regs2 mem2 md2 HJ1 HFR HEC HPB) as
  ((Hac & Hmf47 & Hmf32 & Hmf & Hsp16 & Hstk) & (SF0 & SF1 & _ & _ & _ & _) & (_ & PL0 & PL1) & Hinb & _).
pose proof (asan_consts) as (C1 & _).
assert (ES : ESTACK = 4096) by reflexivity.
assert (HL : d4_low W2 mem2 mem3) by (apply (d4_low_of_keep W2 mem2 mem3 (mf - 2 * ESTACK) mf KEEP); lia).
assert (VK : forall a n v, mf <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v)
  by (intros a n v Ha Hn Hv; refine (d4_vm_keep_hi W2 mem2 mem3 _ _ a n v KEEP _ Ha Hn Hv); lia).
assert (VL : forall a n v, 0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v)
  by (intros a n v Ha Hn Hv; exact (d4_vm_keep W2 mem2 mem3 a n v HL Ha Hn Hv)).
assert (Hk3 : 4 * Z.of_nat i + 3 + 0 = 4 * Z.of_nat i + 3) by lia.
unfold inv_tail, acut.
exists ly2, S2, regs3, mem3, md3.
split; [reflexivity|].
split.
{ pose proof (ajournal_sub SEGS B LAWS pa_segs_low LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) (2 * ESTACK) mf [] [] ly2 S2 W2 mem3 md3 0 HJ1 HJ3
    ltac:(lia) ltac:(lia) ltac:(intros a (r & Hr & _); destruct Hr)) as HJ.
  rewrite Hk3 in HJ. exact HJ. }
split; [exact HFR|]. split; [exact HK|]. split; [exact HMLE|]. split; [exact HMOK|].
split.
- destruct HEC as (Hsp & Hs1 & Hs0 & Hmf' & Hmf32' & Hgp & Htp & H19 & V80 & V192 & V176 & Vra & Vs0 & W9 & W18 & W19 &
    W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & V24 & Vfl & HPRE & Hfds & Hfs & Hinp).
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Ifd Ifs].
  refine (conj _ (conj _ (conj _ (conj Hmf' (conj Hmf32' (conj _ (conj _ (conj _ _)))))))).
  + rewrite R2. exact Hsp.
  + rewrite R9. exact Hs1.
  + rewrite R8. exact Hs0.
  + rewrite R3. exact Hgp.
  + rewrite R4. exact Htp.
  + rewrite R19. exact H19.
  + repeat match goal with
      | |- _ /\ _ => split
      | |- e_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HPRE
      | |- forall fd, _ => intros fd; rewrite Ifd; apply Hfds
      | |- m_fs _ = _ => rewrite Ifs; exact Hfs
      | |- bytes_at8 _ _ (e_p g) _ => destruct Hinb as [Hnil | Hb];
          [rewrite Hnil in *; intros j Hj; cbn in Hj; lia | refine (d4_bytes_keep W2 mem2 mem3 _ _ HL _ _ Hinp); lia]
      | |- val_mem _ _ (SFa g pos + 1016) _ _ => apply VL; [lia | cbn; lia | exact Vfl]
      | |- val_mem _ _ ?a _ _ => apply VK; [cbn; lia | cbn; lia | assumption]
      end.
- split.
  + destruct HPB as (Hi & Hhb & Hpl & (Hidb & Hidz & Hidk) & V112 & (M32 & M40 & M48 & M72 & M88 & M96 & M104 & M120 & M128) &
      Mid & Mag & V136 & V144 & V152 & V160 & H22 & Hcur).
    assert (Lpl : Z.of_nat (length (SlotModel.rec_pl (e_pl g) i)) = SlotModel.rec_k (e_pl g) i).
    { rewrite SlotModel.rec_pl_length. pose proof (SlotModel.rec_k_range (e_pl g) i). lia. }
    assert (Lid : Z.of_nat (length (m_id g (S i))) = 38).
    { unfold m_id. rewrite SlotModel.rec_id_length. reflexivity. }
    assert (Rk : SlotModel.rec_k (e_pl g) i <= req_size (SlotModel.rec_k (e_pl g) i)) by (unfold req_size; destruct (Z.eqb_spec (SlotModel.rec_k (e_pl g) i) 0); lia).
    unfold mf_fixed, mf_id, mf_again, id_at in *. unfold V_id, N_id in *.
    refine (conj Hi (conj Hhb (conj _ (conj (conj _ (conj _ _)) _)))).
    * refine (d4_bytes_keep W2 mem2 mem3 _ _ HL _ _ Hpl); lia.
    * refine (d4_bytes_keep W2 mem2 mem3 _ _ HL _ _ Hidb); lia.
    * refine (d4_zs_keep W2 mem2 mem3 _ _ HL _ _ _ Hidz); lia.
    * refine (d4_blk_keep W2 mem2 mem3 _ _ HL _ _ _ Hidk); lia.
    * repeat match goal with
        | |- 0 <= m_cur _ _ <= _ => exact Hcur
        | |- _ /\ _ => split
        | |- getr _ 22 = _ => rewrite R22; exact H22
        | |- mf_fixed _ _ _ _ _ => unfold mf_fixed
        | |- mf_id _ _ _ _ _ => unfold mf_id
        | |- mf_again _ _ _ _ _ => unfold mf_again
        | |- val_mem _ _ ?a _ _ => apply VK; [cbn; lia | cbn; lia | assumption]
        end.
  + split.
    * destruct HHW as (Hh1 & Hh2 & Hh3 & Hh4). unfold V_hw, N_hw in *.
      assert (Lhw : Z.of_nat (length (m_hwb g (S i))) = 8).
      { unfold m_hwb, SlotModel.rec_hwb. destruct (SlotModel.rec_hw (e_pl g) (S i)) as [h|] eqn:Eh; [|reflexivity].
        clear - Eh. revert h Eh. generalize (S i). induction n as [|n IH]; intros h Eh; cbn [SlotModel.rec_hw] in Eh; [discriminate|].
        destruct (_ && _) eqn:C; [|exact (IH h Eh)]. injection Eh as <-. rewrite length_firstn.
        apply andb_true_iff in C as [_ C]. apply Z.leb_le in C. rewrite SlotModel.rec_pl_length. lia. }
      unfold hw_at, V_hw, N_hw. refine (conj _ (conj _ (conj _ _))).
      -- apply VL; [clear - SF0; lia | cbn; clear - SF1; lia | exact Hh1].
      -- refine (d4_bytes_keep W2 mem2 mem3 _ _ HL _ _ Hh2); lia.
      -- refine (d4_zs_keep W2 mem2 mem3 _ _ HL _ _ _ Hh3); lia.
      -- refine (d4_blk_keep W2 mem2 mem3 _ _ HL _ _ _ Hh4); lia.
    * exact (conj R26 (conj R24 (conj R25 R21))).
Qed.

(* The shadow test of pl[1 + w] (0x811ec..0x81200), left by the engine as an obligation: the byte is inside pl. *)
Lemma d4_obl : forall Ex (W : world SEGS) m ly S md pl k T,
  ew Ex 32 = Z_to_bv 64 d4_SB -> ew Ex 39 = Z_to_bv 64 T -> AR SEGS B ly S W m md -> In (pl, k) (ablocks B ly S) ->
  pl <= T -> T + 1 <= pl + req_size k -> 0 <= T < 2 ^ 64 ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) m)) (U Ex d4_Bx) (U Ex (SOff 39 0)) 1.
Proof.
intros Ex W m ly S md pl k T H32 H39 HAR Hin H1 H2 H3.
unfold d4_Bx. rewrite !U_SOff, H32, H39, !unsigned_lit_small by (unfold d4_SB; lia).
unfold zcanon, M64. rewrite !Z.add_0_r, !Z.mod_small by (unfold d4_SB; lia).
exact (range_addressable_of_block SEGS B LAWS ly S W m md pl k T 1 HAR Hin H1 H2).
Qed.

(* the frame update after an engine run: no region of the state is writable *)
Ltac d4_keep_run :=
  repeat match goal with H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with HFx : frame_of _ ?rs ?m0 ?m1,
    Kx : forall a, _ -> ~ (?lo <= a < ?hi) -> aview SEGS (w_H ?W) ?m0 a = aview SEGS (w_H ?W) ?mref a |- _ =>
    let K := fresh "KEEPN" in
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mref a)
      by (let a := fresh "a" in let h1 := fresh "h" in let h2 := fresh "h" in intros a h1 h2;
          rewrite (d4_frame_ro _ rs m0 m1 (w_H W) a ltac:(vm_compute; reflexivity) HFx); exact (Kx a h1 h2));
    clear HFx Kx; rename K into KEEP0
  end.
(* the region the case reads stays put across a wrapper call *)
Ltac d4_kept_mfr E9mf Hfr Hpres :=
  apply Forall_cons; [|apply Forall_nil]; cbn [ms_mem restrict];
  eapply region_kept_aview;
  [ cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; rewrite E9mf; apply unsigned_lit_small; lia
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; lia
  | exact Hpres ].
(* the end of a path: the join's boundary *)
Ltac d4_fin FIN E2 E9 E8 E3 E4 E19 E22 E35 E36 E33 E37 :=
  d4_keep_run;
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msF),
    HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msF) _ _,
    Kx : forall a, _ -> _ -> aview SEGS (w_H _) (ms_mem ?msF) a = _ |- _ =>
    let F2 := fresh "F" in let F3 := fresh "F" in let F4 := fresh "F" in let F8 := fresh "F" in
    let F9 := fresh "F" in let F19 := fresh "F" in let F21 := fresh "F" in let F22 := fresh "F" in
    let F24 := fresh "F" in let F25 := fresh "F" in let F26 := fresh "F" in
    prreg HSx (2%bv : bv 5) F2; prreg HSx (3%bv : bv 5) F3; prreg HSx (4%bv : bv 5) F4; prreg HSx (8%bv : bv 5) F8;
    prreg HSx (9%bv : bv 5) F9; prreg HSx (19%bv : bv 5) F19; prreg HSx (21%bv : bv 5) F21; prreg HSx (22%bv : bv 5) F22;
    prreg HSx (24%bv : bv 5) F24; prreg HSx (25%bv : bv 5) F25; prreg HSx (26%bv : bv 5) F26;
    pmkst HSx; apply SRr_ret; apply FIN;
    [ exact HJx | exact Kx
    | rewrite F2; exact E2 | rewrite F9; exact E9 | rewrite F8; exact E8 | rewrite F3; exact E3 | rewrite F4; exact E4
    | rewrite F19; exact E19 | rewrite F22; exact E22
    | rewrite F26; exact E35 | rewrite F24; exact E36 | rewrite F25; exact E33 | rewrite F21; exact E37 ]
  end.

(* ---- the walk, over the values of the boundary --------------------------------------------------------------------- *)
Lemma d4_core : forall (pos : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2
  (mf SF NA BEF BODY ix pl w k T : Z) (Q : world SEGS -> config -> Prop),
  ajournal SEGS B (2 * ESTACK) mf [] ly2 S2 W2 mem2 md2 [] ly2 S2 W2 mem2 md2 0 ->
  (forall regs3 mem3 md3,
    ajournal SEGS B (2 * ESTACK) mf [] ly2 S2 W2 mem2 md2 [] ly2 S2 W2 mem3 md3 0 ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
    getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 -> getr regs3 8 = getr regs2 8 ->
    getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 -> getr regs3 19 = getr regs2 19 ->
    getr regs3 22 = getr regs2 22 ->
    getr regs3 26 = w64 BODY -> getr regs3 24 = w64 BEF -> getr regs3 25 = w64 pl -> getr regs3 21 = w64 ix ->
    Q W2 (cfg_at SEGS (BASE + 0xca8) regs3 mem3 md3)) ->
  alloc_ceiling <= mf - 2 * ESTACK -> mf + 320 <= 2 ^ 47 ->
  4096 <= SF -> SF + 1024 <= alloc_ceiling -> in_app SF 1024 ->
  In (4, pos) (frames S2) -> frame_addr ly2 4 pos = SF -> NA = SF + 355 ->
  In (pl, k) (ablocks B ly2 S2) -> 4096 <= pl -> pl + req_size k <= alloc_ceiling ->
  1 <= w <= 16 -> w + 1 <= k -> k <= 255 -> T = pl + 1 + w ->
  (forall a, SF + 352 <= a < SF + 390 -> aview SEGS (w_H W2) mem2 a <> None) ->
  (forall j, 0 <= j < w -> exists b, aview SEGS (w_H W2) mem2 (NA + j) = Some b /\ b <> 0 /\
     aview SEGS (w_H W2) mem2 (pl + 1 + j) = Some b) ->
  aview SEGS (w_H W2) mem2 (NA + w) = Some 0 ->
  (forall a, pl <= a < pl + k -> aview SEGS (w_H W2) mem2 a <> None) ->
  (w <= 15 -> w + 1 < k -> val_mem SEGS (rd W2 mem2) (pl + 1 + w) 1 0) ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (SF + 352) 32 ->
  aro_unowned SEGS B (aview SEGS (w_H W2) mem2) ->
  getr regs2 2 = w64 mf -> getr regs2 9 = w64 mf -> getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
  getr regs2 20 = w64 1 -> getr regs2 22 = w64 k ->
  val_mem SEGS (rd W2 mem2) (mf + 88) 8 BEF -> val_mem SEGS (rd W2 mem2) (mf + 128) 8 NA ->
  val_mem SEGS (rd W2 mem2) (mf + 136) 8 BODY -> val_mem SEGS (rd W2 mem2) (mf + 152) 8 pl ->
  val_mem SEGS (rd W2 mem2) (mf + 160) 8 ix -> val_mem SEGS (rd W2 mem2) (mf + 176) 8 SHADOW_OFF ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0xa64) regs2 mem2 md2) Q.
Proof.
intros pos ly2 S2 W2 regs2 mem2 md2 mf SF NA BEF BODY ix pl w k T Q HJ2 FIN Hac Hmf47 SF0 SF1 SFapp Hin4 Efa ENA
  Hplin PL0 PL1 Hw Hwk Hk255 ET R1 R2 R3 R4 R5 R6 HROM2 Hsp Hs1 Hgp Htp H20 H22 V88 V128 V136 V152 V160 V176.
pose proof (asan_consts) as (C1 & _). assert (ES : ESTACK = 4096) by reflexivity.
assert (Rk : k <= req_size k) by (unfold req_size; destruct (Z.eqb_spec k 0); lia).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof (d4_entry W2 regs2 mem2 mf pl NA BODY BEF ix w T k Hs1 ltac:(lia) ltac:(lia) V88 V128 V136 V152 V160 V176 H20 H22
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ET ltac:(lia)) as HS.
remember (d4_E regs2 pl NA BODY BEF ix w T) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs2 (d4_extra pl NA BODY BEF ix w T)) n)
  by (intros n Hn; subst E; unfold d4_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs2 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs2 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs2 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs2 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regs2 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 9 9%bv eq_refl)).
assert (E19 : ew E 19 = getr regs2 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 19 19%bv eq_refl)).
assert (E22 : ew E 22 = getr regs2 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 22 22%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 d4_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pl) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 NA) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 BODY) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 BEF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 ix) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 w) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 T) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 7)).
assert (E22k : ew E 22 = Z_to_bv 64 k) by (rewrite E22; exact H22).
assert (E9mf : ew E 9 = Z_to_bv 64 mf) by (rewrite E9; exact Hs1).
assert (SHOK : sh_ok SEGS d4_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a)
  by (intros; reflexivity).
clear HE EL.
unfold cfg_at. change (w64 (BASE + 0xa64)) with (Z_to_bv 64 (BASE + 0xa64)).
(* run 1: 0x81170 .. the memchr call *)
paj_run_tok RUN HS HJ2 SHOK d4_Bspan; [awr_ok_tac |].
d4_keep_run.
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?ms1) |- _ => rename HSx into HS; rename ms1 into msA end.
pose proof HJ2 as (HARA & _).
assert (HLA : d4_low W2 mem2 (ms_mem msA)) by (apply (d4_low_of_keep W2 mem2 (ms_mem msA) (mf - 2 * ESTACK) mf KEEP0); lia).
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
rewrite E34 in Ra0. rewrite E2, Hsp in Q2. rewrite E3, Hgp in Q3. rewrite E4, Htp in Q4.
assert (Hspz : spZ (ms_regs msA) = mf + 0) by (unfold spZ; rewrite Q2; unfold w64; rewrite unsigned_lit_small by lia; lia).
pmkst HS.
eapply SRr_bind.
{ refine (d4_memchr_at W2 (ms_regs msA) (ms_mem msA) (2 * ESTACK) mf [] ly2 S2 W2 mem2 md2 [] ly2 S2 _ 0 NA 17 0
    (Z_to_bv 64 (BASE + 2680)) HJ2 Ra0 Ra1 Ra2 _ _ _ Hspz _ _ _ Q3 Q4 Q1 _ _ _ _ _ _).
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - lia.
  - lia.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold src_ok. intros a Ha. split; [rewrite HLA by lia; apply R1; lia | rewrite Hspz; lia].
  - apply (amem_range_sub_app SF 1024 NA 17 SFapp); lia.
  - apply (range_addressable_sub _ _ (SF + 352) 32); [| lia | lia].
    apply (d4_ra_keep W2 mem2 (ms_mem msA) _ _ HLA); [lia | lia | exact R6].
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 _ _ 4 pos NA 17 HARA Hin4); rewrite ?Efa, ?Hfb; lia.
  - exact (d4_aro_keep B W2 mem2 (ms_mem msA) HLA HROM2). }
cbv beta. intros W3 c3 _ Hpp. destruct Hpp as (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (kk & Hfbk & Ha03) & Hfr3 & Hpres3).
(* the NUL memchr finds is the model's: name_len pl *)
assert (Ekk : kk = w).
{ destruct Hfbk as (Hk0 & Hlt & Hat).
  destruct (Z.lt_trichotomy kk w) as [Hl | [He | Hg]]; [exfalso | exact He | exfalso].
  - pose proof (Hat ltac:(lia)) as Hz. rewrite HLA in Hz by lia.
    destruct (R2 kk ltac:(lia)) as (b & Hb & Hb0 & _). rewrite Hz in Hb. injection Hb as <-. exact (Hb0 eq_refl).
  - destruct (Hlt w ltac:(lia)) as (b & Hb & Hb0). rewrite HLA in Hb by lia. rewrite R3 in Hb. injection Hb as <-.
    exact (Hb0 eq_refl). }
subst kk. replace (w <? 17) with true in Ha03 by (symmetry; apply Z.ltb_lt; lia).
assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite (Hfr3 a Ha) by lia. apply KEEP0; assumption. }
clear KEEP0.
jafter_call_keep_pi HS 180%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat] HSB.
lazymatch type of HSB with ?Qk -> _ => let HQ := fresh "HQ" in assert (HQ : Qk); [| specialize (HSB HQ); clear HQ] end.
{ d4_kept_mfr E9mf Hfr3 Hpres3. }
rewrite <- restrict_mkst_fx in HSB. clear HS.
assert (X184 : ew (havoc E 180 (map (getr regs3) CLOB)) 184 = w64 (NA + w))
  by (cbn [ew havoc Nat.ltb Nat.leb Nat.sub nth map CLOB]; exact Ha03).
assert (X34 : ew (havoc E 180 (map (getr regs3) CLOB)) 34 = Z_to_bv 64 NA) by (rewrite ew_havoc_old by lia; exact E34).
assert (X38 : ew (havoc E 180 (map (getr regs3) CLOB)) 38 = Z_to_bv 64 w) by (rewrite ew_havoc_old by lia; exact E38).
assert (F184 : afact_ok (havoc E 180 (map (getr regs3) CLOB)) 184 (mkAF 4096 (2 ^ 47) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X184. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (st_ok_pi_add_fact _ _ _ 184%nat (mkAF 4096 (2 ^ 47) 0) HSB F184) as HSB1. clear HSB F184.
assert (C184 : branch_taken BC_NE (sv_denot (havoc E 180 (map (getr regs3) CLOB)) (SOff 184 0))
  (sv_denot (havoc E 180 (map (getr regs3) CLOB)) (SOff 34 0)) = true).
{ rewrite branch_ne_U, !U_SOff, X184, X34. unfold w64. rewrite !unsigned_lit_small by lia.
  unfold zcanon, M64. rewrite !Z.add_0_r. rewrite (Z.mod_small NA), (Z.mod_small (NA + w)) by lia.
  apply negb_true_iff, Z.eqb_neq. lia. }
pose proof (st_ok_pi_add_cond' _ _ _ BC_NE (SOff 184 0) (SOff 34 0) HSB1 C184) as HSB2. clear HSB1 C184.
assert (A184 : sv_denot (havoc E 180 (map (getr regs3) CLOB)) (SAlu ALU_SUB (SOff 184 0) (SOff 34 0)) =
  sv_denot (havoc E 180 (map (getr regs3) CLOB)) (SOff 38 0)).
{ apply U_inj. rewrite U_SAlu, !U_SOff, X184, X34, X38. unfold w64. rewrite !unsigned_lit_small by lia. cbn [zalu_raw].
  unfold zcanon, M64. rewrite !Z.add_0_r. rewrite (Z.mod_small NA), (Z.mod_small (NA + w)), (Z.mod_small w) by lia.
  replace (NA + w - NA) with w by lia. apply Z.mod_small. lia. }
pose proof (st_ok_pi_add_alias _ _ _ (SAlu ALU_SUB (SOff 184 0) (SOff 34 0)) (SOff 38 0) HSB2 A184) as HS. clear HSB2 A184.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
assert (HEIa : img_env VAL A_LIM (havoc E 180 (map (getr regs3) CLOB))) by (apply img_env_havoc; [exact HEI | cbn; unfold A_TEXT; lia]).
assert (SHOK1 : sh_ok SEGS d4_Bx [] (havoc E 180 (map (getr regs3) CLOB)) (mrestrict (w_H W2) mem3)) by apply Forall_nil.
clear SHOK Ra0 Ra1 Ra2 Q1 Q2 Q3 Q4 Hspz Hfr3 X184 Hfbk.
rename KEEPB into KEEP0.
(* run 2: 0x81184 .. the bcmp call *)
paj_run_tok RUN HS HJ3 SHOK1 d4_Bspan; [awr_ok_tac |].
d4_keep_run.
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?ms1) |- _ => rename HSx into HS; rename ms1 into msB end.
pose proof HJ3 as (HARB & _).
assert (HLB : d4_low W2 mem2 (ms_mem msB)) by (apply (d4_low_of_keep W2 mem2 (ms_mem msB) (mf - 2 * ESTACK) mf KEEP0); lia).
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
rewrite E34 in Ra0. rewrite E33, unsigned_lit_small in Ra1 by lia. rewrite E38 in Ra2.
rewrite E2, Hsp in Q2. rewrite E3, Hgp in Q3. rewrite E4, Htp in Q4.
assert (Hspz : spZ (ms_regs msB) = mf + 0) by (unfold spZ; rewrite Q2; unfold w64; rewrite unsigned_lit_small by lia; lia).
pmkst HS.
eapply SRr_bind.
{ refine (aj_bcmp_at SEGS B LAWS pa_segs_low _ ABCMP W2 (ms_regs msB) (ms_mem msB) (2 * ESTACK) mf [] ly2 S2 W2 mem2 md2
    [] ly2 S2 _ 0 NA (pl + 1) w 0 (Z_to_bv 64 (BASE + 2752)) HJ3 Ra0 Ra1 Ra2 _ _ _ _ _ Hspz _ _ _ Q3 Q4 Q1
    _ _ _ _ _ _ _ _ _ _ _).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - lia.
  - lia.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold src_ok. intros a Ha. split; [rewrite HLB by lia; apply R1; lia | rewrite Hspz; lia].
  - unfold src_ok. intros a Ha. split; [rewrite HLB by lia; apply R4; lia | rewrite Hspz; lia].
  - intros a Ha. lia.
  - intros a Ha. lia.
  - apply (amem_range_sub_app SF 1024 NA w SFapp); lia.
  - apply (amem_range_of_block SEGS B LAWS ly2 S2 W2 _ _ pl k (pl + 1) w HARB Hplin); lia.
  - apply (range_addressable_sub _ _ (SF + 352) 32); [| lia | lia].
    apply (d4_ra_keep W2 mem2 (ms_mem msB) _ _ HLB); [lia | lia | exact R6].
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 _ _ 4 pos NA w HARB Hin4); rewrite ?Efa, ?Hfb; lia.
  - apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 _ _ pl k (pl + 1) w HARB Hplin); lia.
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 _ _ pl k (pl + 1) w HARB Hplin); lia. }
cbv beta. intros W4 c4 _ Hpp. destruct Hpp as (-> & regs4 & mem4 & md4 & v & -> & HJ4 & HP4 & Hv & Hcmp & Hfr4 & Hpres4).
assert (Hv0 : v = w64 0).
{ apply Hcmp. intros i0 Hi0. rewrite !HLB by lia. destruct (R2 i0 Hi0) as (b & Hb1 & _ & Hb2). rewrite Hb1, Hb2. reflexivity. }
assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite (Hfr4 a Ha) by lia. apply KEEP0; assumption. }
clear KEEP0.
jafter_call_keep_pi HS 200%nat regs4 (mrestrict (w_H W2) mem4) HP4 [0%nat] HSB.
lazymatch type of HSB with ?Qk -> _ => let HQ := fresh "HQ" in assert (HQ : Qk); [| specialize (HSB HQ); clear HQ] end.
{ d4_kept_mfr E9mf Hfr4 Hpres4. }
rewrite <- restrict_mkst_fx in HSB. clear HS.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HSB ltac:(cbn [ms_regs restrict mkst]; rewrite Hv, Hv0; reflexivity) eq_refl) as HS.
clear HSB.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
assert (HEIb : img_env VAL A_LIM (havoc (havoc E 180 (map (getr regs3) CLOB)) 200 (map (getr regs4) CLOB)))
  by (apply img_env_havoc; [exact HEIa | cbn; unfold A_TEXT; lia]).
assert (SHOK2 : sh_ok SEGS d4_Bx [] (havoc (havoc E 180 (map (getr regs3) CLOB)) 200 (map (getr regs4) CLOB))
  (mrestrict (w_H W2) mem4)) by apply Forall_nil.
clear SHOK1 Ra0 Ra1 Ra2 Q1 Q2 Q3 Q4 Hspz Hfr4 Hcmp.
rename KEEPB into KEEP0.
(* run 3: 0x811cc .. the first live test (0x811e0, w <= 15) *)
paj_run_to_tok RUNTO HS HJ4 SHOK2 d4_Bspan 3240; [awr_ok_tac |].
d4_keep_run.
psrr_branch_tok RUNTO BR HS SHOK2 d4_Bspan.
- (* w = 16: to the join *)
  paj_run_to_tok RUNTO HS HJ4 SHOK2 d4_Bspan 3240; [awr_ok_tac |].
  d4_fin FIN E2 E9 E8 E3 E4 E19 E22 E35 E36 E33 E37.
- (* w <= 15: the second live test (0x811e4, 1 + w < n) *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = false =>
    rewrite (d4_bc1 Ex w ltac:(cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; exact E38) ltac:(lia)) in Hc end.
  apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ4 SHOK2 d4_Bspan 3240; [awr_ok_tac |].
  d4_keep_run.
  psrr_branch_tok RUNTO BR HS SHOK2 d4_Bspan.
  + (* 1 + w >= n: to the join *)
    paj_run_to_tok RUNTO HS HJ4 SHOK2 d4_Bspan 3240; [awr_ok_tac |].
    d4_fin FIN E2 E9 E8 E3 E4 E19 E22 E35 E36 E33 E37.
  + (* the stopped-early check reads pl[1 + w] *)
    lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ex _) _ = false =>
      rewrite (d4_bc2 Ex w k ltac:(cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; exact E38)
        ltac:(cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; exact E22k) ltac:(lia) ltac:(lia)) in Hc0 end.
    apply negb_false_iff, Z.ltb_lt in Hc0.
    lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msC),
      Kx : forall a, _ -> _ -> aview SEGS (w_H W2) (ms_mem ?msC) a = _ |- _ =>
      assert (HLC : d4_low W2 mem2 (ms_mem msC)) by (apply (d4_low_of_keep W2 mem2 (ms_mem msC) (mf - 2 * ESTACK) mf Kx); lia);
      pose proof (st_ok_pi_add_region Ex ssx (restrict (w_H W2) msC) d4_plr HSx ltac:(vm_compute; reflexivity)
        (d4_plr_ok Ex _ T ltac:(cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; exact E39) ltac:(lia) ltac:(lia)
          ltac:(cbn [ms_mem restrict]; rewrite ET; apply (d4_vm_keep W2 mem2 (ms_mem msC) (pl + 1 + w) 1 0 HLC); [lia | cbn; lia | apply R5; lia]))
        (d4_plr_disj Ex T mf ltac:(cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; exact E39)
          ltac:(cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; exact E9mf) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as HS';
      clear HSx; rename HS' into HS;
      pose proof HJ4 as (HARC & _)
    end.
    lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
    paj_run_to_tok RUNTO HS HJ4 SHOK2 d4_Bspan 3240.
    * lazymatch goal with |- range_addressable (rd_of _ (mrestrict _ ?m)) (U ?Ex _) _ _ =>
        exact (d4_obl Ex W2 m ly2 S2 _ pl k T ltac:(cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; exact E32)
          ltac:(cbn [ew havoc ewset Nat.ltb Nat.leb Nat.eqb]; exact E39) HARC Hplin ltac:(lia) ltac:(lia) ltac:(lia)) end.
    * awr_ok_tac.
    * d4_fin FIN E2 E9 E8 E3 E4 E19 E22 E35 E36 E33 E37.
Qed.

(* ---- the segment ---------------------------------------------------------------------------------------------------- *)
Theorem seg_D4_holds : seg_D4 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS.
Proof.
unfold seg_D4. intros g pos mf i pl W2 c2 HC.
unfold inv_caseM, acut in HC.
destruct HC as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HFR & HK & HMLE & HMOK & HEC & HPB & HHW & HR1 & HAD & H20).
destruct (d4_prep g pos mf i pl ly2 S2 W2 regs2 mem2 md2 HJ1 HFR HEC HPB) as
  ((Hac & Hmf47 & Hmf32 & Hmf & Hsp16 & Hstk) & (SF0 & SF1 & SFapp & SF32 & Efa & Hfb) & (Hplin & PL0 & PL1) & _ & HROM2).
pose proof HEC as (Hsp & Hs1 & _ & _ & _ & Hgp & Htp & _ & _ & _ & V176 & _).
pose proof HPB as (_ & _ & Hpl & Hid & _ & (_ & _ & _ & _ & V88 & _ & _ & _ & V128) & _ & _ & V136 & _ & V152 & V160 & H22 & _).
destruct (d4_state2 g pos i pl W2 mem2 Hid Hpl HAD HR1 SF32 _ _ eq_refl eq_refl) as
  ((Hw & Hwk & Hk255 & Hhm) & R1 & R2 & R3 & R4 & R5 & R6).
rewrite Hhm in H20.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
assert (Hm16 : (mf - e_sp0 g) mod 16 = 0).
{ rewrite Zminus_mod, Hsp16. pose proof (Z.div_mod mf 32 ltac:(lia)) as D. rewrite Hmf32, Z.add_0_r in D.
  replace (mf mod 16) with 0; [reflexivity|]. rewrite D. replace (32 * (mf / 32)) with ((2 * (mf / 32)) * 16) by lia.
  symmetry. apply Z_mod_mult. }
pose proof (ajournal_sub_init SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
  ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) (2 * ESTACK) mf [] (mf - e_sp0 g) HJ1 ltac:(lia) Hm16 ltac:(lia)
  ltac:(unfold ESTACK in *; lia) ltac:(unfold ESTACK in *; lia)) as HJ2.
apply (d4_core pos ly2 S2 W2 regs2 mem2 md2 mf (SFa g pos) (SFa g pos + V_id + 3) (SFa g pos + V_before)
  (e_p g + SlotModel.rec_body (e_pl g) i) (Z.of_nat i) pl (Z.of_nat (RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i)))
  (SlotModel.rec_k (e_pl g) i) (pl + 1 + Z.of_nat (RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i)))
  (TAIL g pos mf i pl) HJ2).
- intros regs3 mem3 md3 HJ3 KEEP R2' R9' R8' R3' R4' R19' R22' R26' R24' R25' R21'.
  exact (d4_finish g pos mf i pl ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HJ1 HFR HK HMLE HMOK HEC HPB HHW HJ3 KEEP
    R2' R9' R8' R3' R4' R19' R22' R26' R24' R25' R21').
- exact Hac.
- exact Hmf47.
- exact SF0.
- exact SF1.
- exact SFapp.
- exact Hin4.
- exact Efa.
- unfold V_id. lia.
- exact Hplin.
- exact PL0.
- exact PL1.
- exact Hw.
- exact Hwk.
- exact Hk255.
- reflexivity.
- exact R1.
- unfold V_id. replace (SFa g pos + 352 + 3) with (SFa g pos + 355) by lia. exact R2.
- unfold V_id. replace (SFa g pos + 352 + 3) with (SFa g pos + 355) by lia. exact R3.
- exact R4.
- exact R5.
- exact R6.
- exact HROM2.
- exact Hsp.
- exact Hs1.
- exact Hgp.
- exact Htp.
- exact H20.
- exact H22.
- exact V88.
- exact V128.
- exact V136.
- exact V152.
- exact V160.
- exact V176.
Qed.

End c.
End b.
End a.
