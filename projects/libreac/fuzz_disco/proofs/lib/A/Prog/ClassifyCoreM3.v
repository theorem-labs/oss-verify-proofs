(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 703 of its 736 lines of code are new or changed and 36 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacPortsParse ClassifyCore ClassifyCoreSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed RcParse RcLeaf disco_classify_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition m3_fbyte (i : Z) (a : nat) : YP09.chunk := YP09.mkChunk i (CVal 1 (SOff a 0)).
Definition m3_regions : smem :=
[ YP09.mkRegion (Some 24%nat) 0 24 8 17
    [YP09.mkChunk 6 (CZero 2); YP09.mkChunk 8 (CZero 4); YP09.mkChunk 12 (CZero 4);
     YP09.mkChunk 16 (CZero 1); YP09.mkChunk 17 (CZero 7)];
  YP09.mkRegion (Some 32%nat) 0 50 0 0
    [m3_fbyte 16 33; m3_fbyte 17 34; m3_fbyte 22 35; m3_fbyte 23 36;
     m3_fbyte 24 37; m3_fbyte 25 38; m3_fbyte 26 39; m3_fbyte 33 40];
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 32 0))] ].
Definition m3_facts : facts :=
mkFacts [ (21%nat, mkAF 50 (2 ^ 64 - 1) 0); (23%nat, mkAF SB SB 0); (24%nat, mkAF (2 ^ 12) (2 ^ 47 - 24) 2);
          (32%nat, mkAF 0 (2 ^ 47 - 50) 0);
          (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0);
          (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0) ] [] [].
Definition ss_m3 : sstate := mkSS PC_ROLE sr_atoms m3_regions None m3_facts.
Definition m3_Bx : sv := SOff 23 0.
Definition m3_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition m3_SH : list shent := [mkSHE 24 0 24; mkSHE 32 0 50].
Definition m3_FS : YP09.region := YP09.mkRegion (Some 27%nat) 14 16 14 16 [].

Lemma m3_len : forall F len U L, disco_classify_c.cm_ret F len U L = 0 -> 50 <= len.
Proof.
intros F len U L H. destruct (Z_lt_le_dec len 50) as [Hl|Hl]; [|exact Hl]. exfalso.
assert (Hk : disco_classify_c.dkind F len = 0) by (unfold disco_classify_c.dkind; apply RcParse.ctrlparse_none; lia).
unfold disco_classify_c.cm_ret, disco_classify_c.classify_model in H. rewrite Hk in H. cbn in H. lia.
Qed.

Lemma m3_role_range : forall F k, 0 <= disco_classify_c.role F k <= 2.
Proof.
intros F k. unfold disco_classify_c.role.
repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma m3_fb_range : forall l k, 0 <= CtrlParsed.fb l k < 256.
Proof.
intros l k. unfold CtrlParsed.fb. pose proof (bv_unsigned_in_range 8 (nth k l (CtrlParsed.zb 0))) as H.
change (bv_modulus 8) with 256 in H. lia.
Qed.

Lemma m3_slots_range : forall F, 0 <= disco_classify_c.slots F < 256.
Proof.
intros F. unfold disco_classify_c.slots. destruct (_ && _); [apply m3_fb_range | lia].
Qed.

Lemma m3_nth_bytes : forall l (k : nat), nth k (cls_bytes l) 0 = CtrlParsed.fb l k.
Proof.
intros l k. unfold cls_bytes, CtrlParsed.fb.
rewrite <- (map_nth (fun b : byte => bv_unsigned b) l (CtrlParsed.zb 0) k). reflexivity.
Qed.

Lemma m3_src_len : forall FB, length FB = 50%nat -> length (disco_classify_c.src FB) = 6%nat.
Proof.
intros FB H. unfold disco_classify_c.src, CtrlParsed.fld. rewrite firstn_length, skipn_length. lia.
Qed.

Lemma m3_orole_zero : forall FB (j : nat), length FB = 50%nat -> (6 <= j < 24)%nat ->
nth j (cls_bytes (cls_O_ROLE FB)) 0 = 0.
Proof.
intros FB j HL Hj. unfold cls_O_ROLE, cls_bytes. rewrite map_app.
rewrite app_nth2 by (rewrite map_length, m3_src_len by exact HL; lia).
rewrite map_length, m3_src_len by exact HL.
assert (Hin : In (nth (j - 6) (map (fun b : byte => bv_unsigned b) (repeat (CtrlParsed.zb 0) 18)) 0)
  (map (fun b : byte => bv_unsigned b) (repeat (CtrlParsed.zb 0) 18)))
by (apply nth_In; rewrite map_length, repeat_length; lia).
apply in_map_iff in Hin as (y & Hy & Hy2). apply repeat_spec in Hy2. subst y. rewrite <- Hy. reflexivity.
Qed.

Lemma m3_orole_len : forall FB, length FB = 50%nat -> length (cls_bytes (cls_O_ROLE FB)) = 24%nat.
Proof.
intros FB HL. unfold cls_bytes, cls_O_ROLE. rewrite map_length, app_length, m3_src_len by exact HL.
rewrite repeat_length. reflexivity.
Qed.

Lemma m3_S1_bounds : forall SP, SP - 192 < cls_S1 SP <= SP - 160 /\ cls_S1 SP mod 32 = 0.
Proof.
intros SP. unfold cls_S1. pose proof (Z.mod_pos_bound (SP - 160) 32 ltac:(lia)) as H1.
pose proof (Z.div_mod (SP - 160) 32 ltac:(lia)) as H2.
split; [lia|]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Lemma m3_div8 : forall F, F mod 32 = 0 -> F = 8 * (F / 8).
Proof.
intros F H. pose proof (Z.div_mod F 8 ltac:(lia)) as H2.
assert (H3 : F mod 8 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as H4. rewrite H in H4. rewrite H4.
  replace (32 * (F / 32) + 0) with ((4 * (F / 32)) * 8) by lia. apply Z_mod_mult. }
lia.
Qed.

Definition m3_W (o fs a : Z) : Prop := (o + 8 <= a < o + 17) \/ (fs + 14 <= a < fs + 16).
Definition m3_tail (r s : Z) : list Z := [0; 0; r; 0; 0; 0; 0; 0; 0; 0; s; 0; 0; 0; 0; 0; 0; 0].
Ltac m3_inl := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma m3_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small v 256), (Z.mod_small v 256) by lia. reflexivity.
Qed.

Lemma m3_le4 : forall r, 0 <= r <= 2 ->
cls_bytes (Mem.le4 (Z_to_bv 64 r)) = [r; 0; 0; 0] /\ (forall k, (k < 4)%nat -> le_byte r 4 k = nth k [r; 0; 0; 0] 0).
Proof.
intros r Hr. assert (Hc : r = 0 \/ r = 1 \/ r = 2) by lia.
destruct Hc as [ -> | [ -> | -> ] ]; (split; [vm_compute; reflexivity | intros k Hk; do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia]).
Qed.

Lemma m3_oq_bytes : forall F len, cls_bytes (cls_O_Q F len) =
cls_bytes (disco_classify_c.src F) ++ m3_tail (disco_classify_c.role F (disco_classify_c.dkind F len)) (disco_classify_c.slots F).
Proof.
intros F len. unfold cls_O_Q. unfold cls_bytes at 1. rewrite !map_app. unfold cls_bytes at 1. f_equal.
pose proof (m3_role_range F (disco_classify_c.dkind F len)) as Hr. pose proof (m3_slots_range F) as Hs.
destruct (m3_le4 _ Hr) as [H4 _]. unfold cls_bytes in H4. rewrite H4.
unfold m3_tail. cbn [map app]. unfold CtrlParsed.zb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. rewrite (Z.mod_small (disco_classify_c.slots F) 256) by lia. reflexivity.
Qed.

Lemma m3_orole_bytes : forall F, cls_bytes (cls_O_ROLE F) = cls_bytes (disco_classify_c.src F) ++ repeat 0 18.
Proof.
intros F. unfold cls_O_ROLE, cls_bytes. rewrite map_app. reflexivity.
Qed.

Lemma m3_pat : forall (j : nat), (j < 32)%nat -> j <> 14%nat -> j <> 15%nat -> nth j PAT_B 0 = nth j PAT_A 0.
Proof.
intros j Hj H14 H15. do 32 (destruct j as [|j]; [first [reflexivity | lia] |]). lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Definition m3_extra (cx : ccx) : list word :=
map (Z_to_bv 64) (x_f cx :: map (CtrlParsed.fb (x_FB cx)) [16; 17; 22; 23; 24; 25; 26; 33]%nat).
Definition m3_E (regs : bvmap 5 word) (cx : ccx) : env := Eimg (Ereg regs (m3_extra cx)).

Lemma m3_ew_reg : forall regs cx n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
ew (m3_E regs cx) n = getr regs r.
Proof.
intros regs cx n r Hr Hn. unfold m3_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr.
Qed.

Lemma m3_ew_x : forall regs cx j, (j < 9)%nat -> ew (m3_E regs cx) (32 + j) = nth j (m3_extra cx) (Z_to_bv 64 0).
Proof.
intros regs cx j Hj. unfold m3_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.

Lemma m3_den : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. Qed.

Lemma m3_U : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. apply unsigned_lit_small. exact Hv. Qed.

Lemma m3_fchunk : forall E m f FB (i : nat) a, (i < length FB)%nat ->
garr8 SEGS m f (cls_bytes FB) -> ew E a = Z_to_bv 64 (CtrlParsed.fb FB i) ->
YP09.chunk_ok SEGS E m f (m3_fbyte (Z.of_nat i) a).
Proof.
intros E m f FB i a Hi G Ha. unfold m3_fbyte.
apply (chunk_ok_val SEGS E m f (Z.of_nat i) 1 (SOff a 0) (CtrlParsed.fb FB i)).
- apply m3_den. exact Ha.
- pose proof (m3_fb_range FB i). cbn. lia.
- cbn. lia.
- destruct (G i ltac:(unfold cls_bytes; rewrite map_length; exact Hi)) as [V _].
  rewrite m3_nth_bytes in V. exact V.
Qed.

Lemma m3_orole_mbyte : forall m o FB, length FB = 50%nat -> garr8 SEGS m o (cls_bytes (cls_O_ROLE FB)) ->
forall i, 6 <= i < 24 -> mbyte SEGS m (o + i) = Some (Z_to_bv 8 0).
Proof.
intros m o FB HL G i Hi.
destruct (G (Z.to_nat i) ltac:(rewrite m3_orole_len by exact HL; lia)) as [V _].
rewrite m3_orole_zero in V by (exact HL || lia). rewrite Z2Nat.id in V by lia.
specialize (V 0%nat ltac:(lia)). rewrite Z.add_0_r in V. exact V.
Qed.

Lemma m3_mbyte_kept : forall (m m' : word -> option byte) (P : Z -> Prop) a,
(forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a < 2 ^ 64 -> ~ P a -> mbyte SEGS m' a = mbyte SEGS m a.
Proof. intros m m' P a H Ha Hn. unfold mbyte. rewrite H; [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn. Qed.

Lemma m3_val_mem_kept : forall (m m' : word -> option byte) (P : Z -> Prop) a n v,
(forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall k, 0 <= k < Z.of_nat n -> ~ P (a + k)) -> val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof.
intros m m' P a n v H Ha Hn HP V k Hk.
rewrite (m3_mbyte_kept m m' P _ H); [apply V; exact Hk | lia | apply HP; lia].
Qed.

Lemma m3_garr8_kept : forall (m m' : word -> option byte) (P : Z -> Prop) a l,
(forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
(forall k, 0 <= k < Z.of_nat (length l) -> ~ P (a + k)) -> garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof.
intros m m' P a l H Ha Hn HP G j Hj. destruct (G j Hj) as [V R]. split; [|exact R].
apply (m3_val_mem_kept m m' P _ 1 _ H); [lia | lia | | exact V].
intros k Hk. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply HP. lia.
Qed.

Lemma m3_aview_kept : forall H (m m' : word -> option byte) (P : Z -> Prop),
(forall x : word, ~ P (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' P HK a Ha Hn. unfold aview. rewrite (m3_mbyte_kept _ _ P a HK Ha Hn). reflexivity. Qed.

Lemma m3_present_grow : forall H (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a G [Ha [b Hb]]. split; [exact Ha|].
specialize (G (Z_to_bv 64 a)). unfold mrestrict in G. rewrite Ha, Hb in G.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; exact (G ltac:(discriminate) eq_refl)].
Qed.

Lemma m3_vm1 : forall m a v, mbyte SEGS m a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> val_mem SEGS m a 1 v.
Proof.
intros m a v H Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, m3_le_byte1 by exact Hv.
exact H.
Qed.

Lemma m3_tail_range : forall r s k, 0 <= r < 256 -> 0 <= s < 256 -> 0 <= nth k (m3_tail r s) 0 < 256.
Proof.
intros r s k Hr Hs. unfold m3_tail. do 18 (destruct k as [|k]; [cbn [nth]; lia|]). destruct k; cbn; lia.
Qed.

Lemma m3_by : forall m o r s, 0 <= r <= 2 -> 0 <= s < 256 ->
(forall i, 6 <= i < 8 \/ 12 <= i < 16 \/ 17 <= i < 24 -> mbyte SEGS m (o + i) = Some (Z_to_bv 8 0)) ->
val_mem SEGS m (o + 8) 4 r -> val_mem SEGS m (o + 16) 1 s ->
forall k, (k < 18)%nat -> mbyte SEGS m (o + 6 + Z.of_nat k) = Some (Z_to_bv 8 (nth k (m3_tail r s) 0)).
Proof.
intros m o r s Hr Hs Z0 V8 V16 k Hk.
destruct (m3_le4 r Hr) as [_ HLE].
assert (A8 : forall kk, (kk < 4)%nat -> mbyte SEGS m (o + 8 + Z.of_nat kk) = Some (Z_to_bv 8 (nth kk [r; 0; 0; 0] 0))).
{ intros kk Hkk. rewrite <- HLE by exact Hkk. apply V8. exact Hkk. }
assert (A16 : mbyte SEGS m (o + 16) = Some (Z_to_bv 8 s)).
{ pose proof (V16 0%nat ltac:(lia)) as W. rewrite m3_le_byte1 in W by exact Hs. cbn [Z.of_nat] in W.
  rewrite Z.add_0_r in W. exact W. }
assert (AZ : forall i, 6 <= i < 8 \/ 12 <= i < 16 \/ 17 <= i < 24 -> mbyte SEGS m (o + 6 + (i - 6)) = Some (Z_to_bv 8 0)).
{ intros i Hi. replace (o + 6 + (i - 6)) with (o + i) by lia. apply Z0. exact Hi. }
unfold m3_tail.
destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]]]]]]; cbn [nth].
- exact (AZ 6 ltac:(lia)).
- exact (AZ 7 ltac:(lia)).
- replace (o + 6 + Z.of_nat 2) with (o + 8 + Z.of_nat 0) by lia. exact (A8 0%nat ltac:(lia)).
- replace (o + 6 + Z.of_nat 3) with (o + 8 + Z.of_nat 1) by lia. exact (A8 1%nat ltac:(lia)).
- replace (o + 6 + Z.of_nat 4) with (o + 8 + Z.of_nat 2) by lia. exact (A8 2%nat ltac:(lia)).
- replace (o + 6 + Z.of_nat 5) with (o + 8 + Z.of_nat 3) by lia. exact (A8 3%nat ltac:(lia)).
- exact (AZ 12 ltac:(lia)).
- exact (AZ 13 ltac:(lia)).
- exact (AZ 14 ltac:(lia)).
- exact (AZ 15 ltac:(lia)).
- replace (o + 6 + Z.of_nat 10) with (o + 16) by lia. exact A16.
- exact (AZ 17 ltac:(lia)).
- exact (AZ 18 ltac:(lia)).
- exact (AZ 19 ltac:(lia)).
- exact (AZ 20 ltac:(lia)).
- exact (AZ 21 ltac:(lia)).
- exact (AZ 22 ltac:(lia)).
- exact (AZ 23 ltac:(lia)).
- lia.
Qed.

Lemma m3_zero_chunk : forall E m b off len i, YP09.chunk_ok SEGS E m b (YP09.mkChunk off (CZero len)) -> 0 <= i < len ->
mbyte SEGS m (b + off + i) = Some (Z_to_bv 8 0).
Proof.
intros E m b off len i H Hi. destruct (H i Hi) as (bb & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2.
injection Hb1 as <-. exact Hb2.
Qed.

Lemma m3_obytes : forall E m cs o r v, region_ok SEGS E m (YP09.mkRegion (Some 24%nat) 0 24 8 17 cs) ->
bv_unsigned (ew E 24) = o ->
In (YP09.mkChunk 6 (CZero 2)) cs -> In (YP09.mkChunk 12 (CZero 4)) cs -> In (YP09.mkChunk 17 (CZero 7)) cs ->
In (YP09.mkChunk 8 (CVal 4 (SOff 11 0))) cs -> ew E 11 = Z_to_bv 64 r -> 0 <= r <= 2 ->
((In (YP09.mkChunk 16 (CZero 1)) cs /\ v = 0) \/ (In (YP09.mkChunk 16 (CVal 1 (SOff 40 0))) cs /\ ew E 40 = Z_to_bv 64 v)) ->
0 <= v < 256 ->
(forall i, 6 <= i < 8 \/ 12 <= i < 16 \/ 17 <= i < 24 -> mbyte SEGS m (o + i) = Some (Z_to_bv 8 0)) /\
val_mem SEGS m (o + 8) 4 r /\ val_mem SEGS m (o + 16) 1 v.
Proof.
intros E m cs o r v HR Uo I6 I12 I17 I8 E11 Hr I16 Hv.
destruct HR as (_ & _ & _ & Hcs). cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. rewrite Uo in Hcs.
pose proof (fun c (Hc : In c cs) => proj1 (Forall_forall _ _) Hcs c Hc) as HC.
split; [|split].
- intros i Hi. destruct Hi as [Hi|[Hi|Hi]].
  + replace (o + i) with (o + 6 + (i - 6)) by lia. apply (m3_zero_chunk E m o 6 2); [exact (HC _ I6) | lia].
  + replace (o + i) with (o + 12 + (i - 12)) by lia. apply (m3_zero_chunk E m o 12 4); [exact (HC _ I12) | lia].
  + replace (o + i) with (o + 17 + (i - 17)) by lia. apply (m3_zero_chunk E m o 17 7); [exact (HC _ I17) | lia].
- exact (val_of_chunk_ok SEGS E m o 8 4 (SOff 11 0) r (HC _ I8) (m3_den E 11 r E11) ltac:(cbn; lia) ltac:(cbn; lia)).
- destruct I16 as [[I16 ->]|[I16 E40]].
  + apply m3_vm1; [|lia]. replace (o + 16) with (o + 16 + 0) by lia.
    apply (m3_zero_chunk E m o 16 1); [exact (HC _ I16) | lia].
  + exact (val_of_chunk_ok SEGS E m o 16 1 (SOff 40 0) v (HC _ I16) (m3_den E 40 v E40) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

Definition m3_rwin_ok (r : YP09.region) : bool :=
(YP09.r_whi r <=? YP09.r_wlo r) ||
(obase_eqb (YP09.r_base r) (Some 24%nat) && (8 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 17)) ||
(obase_eqb (YP09.r_base r) (Some 27%nat) && (14 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 16)).

Lemma m3_wr_ok : forall E rs o fs, forallb m3_rwin_ok rs = true ->
bv_unsigned (ew E 24) = o -> bv_unsigned (ew E 27) = fs -> forall a, in_wrange E rs a -> m3_W o fs a.
Proof.
intros E rs o fs Hok Ho Hf a (r & Hin & Ha).
pose proof (proj1 (forallb_forall _ _) Hok r Hin) as Hr. unfold m3_rwin_ok in Hr.
revert Ha. destruct (YP09.r_base r) as [n|]; intros Ha; cbn [obase_eqb base_val] in Hr, Ha.
- apply orb_true_iff in Hr as [Hr|Hr]; [apply orb_true_iff in Hr as [Hr|Hr]|].
  + apply Z.leb_le in Hr. lia.
  + apply andb_true_iff in Hr as [Hr H2]. apply andb_true_iff in Hr as [H0 H1].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Nat.eqb_eq in H0. subst n. rewrite Ho in Ha. left. lia.
  + apply andb_true_iff in Hr as [Hr H2]. apply andb_true_iff in Hr as [H0 H1].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Nat.eqb_eq in H0. subst n. rewrite Hf in Ha. right. lia.
- apply orb_true_iff in Hr as [Hr|Hr]; [apply orb_true_iff in Hr as [Hr|Hr]|].
  + apply Z.leb_le in Hr. lia.
  + apply andb_true_iff in Hr as [Hr _]. apply andb_true_iff in Hr as [H0 _]. discriminate H0.
  + apply andb_true_iff in Hr as [Hr _]. apply andb_true_iff in Hr as [H0 _]. discriminate H0.
Qed.

Lemma m3_inv_step : forall (m0 m1 m2 : word -> option byte) (P : Z -> Prop) E rs,
(forall x : word, ~ P (bv_unsigned x) -> m1 x = m0 x) -> frame_of E rs m1 m2 ->
(forall a, in_wrange E rs a -> P a) -> forall x : word, ~ P (bv_unsigned x) -> m2 x = m0 x.
Proof. intros m0 m1 m2 P E rs H1 HF HW x Hx. rewrite (HF x); [exact (H1 x Hx)|]. intros Hw. exact (Hx (HW _ Hw)). Qed.

Lemma m3_grow_step : forall m0 m1 m2 : word -> option byte, mem_grows m0 m1 -> mem_grows m1 m2 -> mem_grows m0 m2.
Proof. intros m0 m1 m2 H1 H2 x Hx. exact (H2 x (H1 x Hx)). Qed.

Lemma m3_cond : forall E n v c b, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> 0 <= c < 256 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = b -> (v =? c) = negb b.
Proof.
intros E n v c b Hn Hv Hc H. rewrite branch_ne_U in H. rewrite (U_atom E n v Hn) in H by lia.
rewrite U_lit in H by lia. rewrite <- H. destruct (v =? c); reflexivity.
Qed.

Lemma m3_add_fs : forall (fq : YK11.FPState) E ss (W : world SEGS) ms o f s1 fs (mem0 : word -> option byte),
st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) ->
map (fun r => (YP09.r_base r, YP09.r_lo r, YP09.r_hi r)) (ss_mem ss) =
  [(Some 24%nat, 0, 24); (Some 32%nat, 0, 50); (Some 9%nat, 24, 32)] ->
bv_unsigned (ew E 24) = o -> bv_unsigned (ew E 32) = f -> bv_unsigned (ew E 9) = s1 -> bv_unsigned (ew E 27) = fs ->
(fs + 16 <= o \/ o + 24 <= fs + 14) -> (fs + 16 <= f \/ f + 50 <= fs + 14) ->
(fs + 16 <= s1 + 24 \/ s1 + 32 <= fs + 14) -> 0 <= fs -> fs + 16 <= 2 ^ 64 ->
(forall i, 14 <= i < 16 -> apresent (w_H W) mem0 (fs + i)) ->
mem_grows (mrestrict (w_H W) mem0) (mrestrict (w_H W) (ms_mem ms)) ->
st_ok_pi (fx := fq) SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (m3_FS :: ss_mem ss) (ss_resv ss) (ss_facts ss))
  (restrict (w_H W) ms).
Proof.
intros fq E ss W ms o f s1 fs mem0 HS Hmap Uo Uf U9 Ufs D1 D2 D3 H0 H64 Hp HG.
apply st_ok_pi_add_region; [exact HS | reflexivity | |].
- unfold region_ok, m3_FS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Ufs.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros i Hi. change (ms_mem (restrict (w_H W) ms)) with (mrestrict (w_H W) (ms_mem ms)).
  apply (apresent_writable SEGS). apply (m3_present_grow _ mem0 _ _ HG). apply Hp. lia.
- destruct (ss_mem ss) as [|r1 [|r2 [|r3 [|r4 rs]]]]; cbn [map] in Hmap; try discriminate.
  destruct r1 as [b1 lo1 hi1 wl1 wh1 c1], r2 as [b2 lo2 hi2 wl2 wh2 c2], r3 as [b3 lo3 hi3 wl3 wh3 c3].
  cbn [YP09.r_base YP09.r_lo YP09.r_hi] in Hmap.
  injection Hmap as -> -> -> -> -> -> -> -> ->.
  cbn [all_disjoint]. unfold extent_disjoint, m3_FS. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Ufs, Uo, Uf, U9. repeat split; lia.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis NOW : cls_now_ok B.
Hypothesis KS : cls_kept_step_ok B.

Lemma m3_open : forall cx fpos W3 ly3 S3 regs3 mem3 md3,
cls_pre B cx -> cls_at_ROLE B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
st_ok_pi (fx := x_fq cx) SEGS VAL (m3_E regs3 cx) ss_m3
  (restrict (w_H W3) (mkst (fx := x_fq cx) regs3 (Z_to_bv 64 (BASE + PC_ROLE)) mem3 (seg_rom SEGS))) /\
sh_ok SEGS m3_Bx m3_SH (m3_E regs3 cx) (mrestrict (w_H W3) mem3).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HR.
pose proof (NOW cx fpos _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre (proj2 HR)) as HN. cbv zeta in HN.
destruct HR as (Hret & HC). unfold cRet in Hret.
pose proof (m3_len _ _ _ _ Hret) as H50.
destruct HN as (HFB & HFf & _ & _ & HOo & Ho4096 & Hoceil & _ & _).
destruct (HFf H50) as (GF & HFo).
destruct HFo as ((Hf0 & Hf47 & _ & _ & HfLS) & (Hfpres & HfRA & _) & _ & HfSP).
destruct HOo as ((Ho0 & Ho47 & _ & _ & HoLS) & (Hopres & HoRA & _) & _ & HoSP).
destruct HC as (HJ & _ & _ & _ & _ & _ & _ & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 & RV & _ &
  L16 & L24 & L48 & _ & _ & _ & _ & _ & LO3 & GO3 & _).
apply Forall_cons_iff in RV as [R11 RV]. apply Forall_cons_iff in RV as [R21 RV].
apply Forall_cons_iff in RV as [R22 RV]. apply Forall_cons_iff in RV as [R23 RV].
apply Forall_cons_iff in RV as [R24 RV]. apply Forall_cons_iff in RV as [R25 _].
cbn [fst snd] in R11, R21, R22, R23, R24, R25.
destruct Hpre as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp & _ & _ & Hlen & LFB & _ & _ &
  _ & _ & _ & _ & Hop & Ho4 & _ & _ & _ & _ & _ & _ & HOF & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _) & _).
specialize (HOF H50).
set (E := m3_E regs3 cx).
assert (E9 : ew E 9 = w64 (cS1 cx)) by (rewrite <- R9; apply m3_ew_reg; [reflexivity | lia]).
assert (E21 : ew E 21 = w64 (x_len cx)) by (rewrite <- R21; apply m3_ew_reg; [reflexivity | lia]).
assert (E23 : ew E 23 = w64 SHADOW_OFF) by (rewrite <- R23; apply m3_ew_reg; [reflexivity | lia]).
assert (E24 : ew E 24 = w64 (x_o cx)) by (rewrite <- R24; apply m3_ew_reg; [reflexivity | lia]).
assert (E32 : ew E 32 = Z_to_bv 64 (x_f cx)) by exact (m3_ew_x regs3 cx 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 16)) by exact (m3_ew_x regs3 cx 1 ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 17)) by exact (m3_ew_x regs3 cx 2 ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 22)) by exact (m3_ew_x regs3 cx 3 ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 23)) by exact (m3_ew_x regs3 cx 4 ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 24)) by exact (m3_ew_x regs3 cx 5 ltac:(lia)).
assert (E38 : ew E 38 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 25)) by exact (m3_ew_x regs3 cx 6 ltac:(lia)).
assert (E39 : ew E 39 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 26)) by exact (m3_ew_x regs3 cx 7 ltac:(lia)).
assert (E40 : ew E 40 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 33)) by exact (m3_ew_x regs3 cx 8 ltac:(lia)).
pose proof (m3_S1_bounds (cSP cx)) as (HS1 & _). change (cls_S1 (cSP cx)) with (cS1 cx) in HS1.
set (SP := cSP cx) in *. set (S1 := cS1 cx) in *. set (o := x_o cx) in *. set (f := x_f cx) in *.
assert (HSPr : spZ (x_regs cx) = SP) by reflexivity.
assert (HCS : CLS_STK = CLS_VIA_PARSE) by reflexivity.
unfold CLS_VIA_PARSE, CLS_PARSE_NEED, CLS_FRAME, ESTACK in HCS. rewrite HCS in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (US1 : bv_unsigned (ew E 9) = S1) by (apply (m3_U E 9 S1 E9); lia).
assert (Uo : bv_unsigned (ew E 24) = o) by (apply (m3_U E 24 o E24); lia).
assert (Uf : bv_unsigned (ew E 32) = f) by (apply (m3_U E 32 f E32); lia).
split.
- rewrite restrict_mkst_fx. unfold ss_m3, m3_regions. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Uo. split; [lia|]. split; [lia|]. split.
      -- intros i Hi. apply (apresent_writable SEGS). apply Hopres. lia.
      -- repeat apply Forall_cons; try apply Forall_nil; apply chunk_ok_zero; intros i Hi;
         rewrite <- Z.add_assoc; apply (m3_orole_mbyte _ o (x_FB cx) LFB GO3); lia.
    * rewrite Uf. split; [lia|]. split; [lia|]. split; [intros i Hi; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      first [ exact (m3_fchunk E _ f (x_FB cx) 16 33 ltac:(lia) GF E33)
            | exact (m3_fchunk E _ f (x_FB cx) 17 34 ltac:(lia) GF E34)
            | exact (m3_fchunk E _ f (x_FB cx) 22 35 ltac:(lia) GF E35)
            | exact (m3_fchunk E _ f (x_FB cx) 23 36 ltac:(lia) GF E36)
            | exact (m3_fchunk E _ f (x_FB cx) 24 37 ltac:(lia) GF E37)
            | exact (m3_fchunk E _ f (x_FB cx) 25 38 ltac:(lia) GF E38)
            | exact (m3_fchunk E _ f (x_FB cx) 26 39 ltac:(lia) GF E39)
            | exact (m3_fchunk E _ f (x_FB cx) 33 40 ltac:(lia) GF E40) ].
    * rewrite US1. split; [lia|]. split; [lia|]. split; [intros i Hi; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ S1 24 8 (SOff 32 0) f); [apply m3_den; exact E32 | cbn; lia | cbn; lia | exact L24].
  + apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Uo, Uf, US1. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; exact I]. unfold m3_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (m3_U E 21 (x_len cx) E21) by lia. rewrite (m3_U E 23 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia).
    rewrite Uo, Uf.
    rewrite (m3_U E 33 _ E33) by (pose proof (m3_fb_range (x_FB cx) 16); lia).
    rewrite (m3_U E 34 _ E34) by (pose proof (m3_fb_range (x_FB cx) 17); lia).
    rewrite (m3_U E 35 _ E35) by (pose proof (m3_fb_range (x_FB cx) 22); lia).
    rewrite (m3_U E 36 _ E36) by (pose proof (m3_fb_range (x_FB cx) 23); lia).
    rewrite (m3_U E 37 _ E37) by (pose proof (m3_fb_range (x_FB cx) 24); lia).
    rewrite (m3_U E 38 _ E38) by (pose proof (m3_fb_range (x_FB cx) 25); lia).
    rewrite (m3_U E 39 _ E39) by (pose proof (m3_fb_range (x_FB cx) 26); lia).
    rewrite (m3_U E 40 _ E40) by (pose proof (m3_fb_range (x_FB cx) 33); lia).
    pose proof (m3_fb_range (x_FB cx) 16). pose proof (m3_fb_range (x_FB cx) 17).
    pose proof (m3_fb_range (x_FB cx) 22). pose proof (m3_fb_range (x_FB cx) 23).
    pose proof (m3_fb_range (x_FB cx) 24). pose proof (m3_fb_range (x_FB cx) 25).
    pose proof (m3_fb_range (x_FB cx) 26). pose proof (m3_fb_range (x_FB cx) 33).
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 2) with 4. unfold SB, SHADOW_OFF.
    repeat split; lia.
- unfold sh_ok, m3_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (shent_ok_of_range SEGS (w_H W3) mem3 E m3_Bx 24 o 24 o 0 24 HoRA).
    * unfold m3_Bx. apply (U_atom E 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
    * apply (U_atom E 24 o E24). lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
  + apply (shent_ok_of_range SEGS (w_H W3) mem3 E m3_Bx 32 f 50 f 0 50 HfRA).
    * unfold m3_Bx. apply (U_atom E 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
    * apply (U_atom E 32 f E32). lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma m3_close : forall cx fpos W3 ly3 S3 regs3 mem3 md3 (regs4 : bvmap 5 word) mem4 md4,
cls_pre B cx -> cls_at_ROLE B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  ((2, fpos) :: x_own cx) ly3 S3 W3 mem4 md4 (x_k cx) ->
(forall x : word, ~ m3_W (x_o cx) (SHADOW_OFF + cF cx fpos / 8) (bv_unsigned x) ->
  mrestrict (w_H W3) mem4 x = mrestrict (w_H W3) mem3 x) ->
mem_grows (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) mem4) ->
(forall r : bv 5, In r ([2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 27]%bv : list (bv 5)) -> getr regs4 r = getr regs3 r) ->
getr regs4 1 = w64 (BASE + PC_R3) -> getr regs4 10 = w64 (x_f cx + 18) ->
getr regs4 11 = w64 (cF cx fpos + 112) -> getr regs4 22 = w64 (cF cx fpos + 112) ->
(forall i, 6 <= i < 8 \/ 12 <= i < 16 \/ 17 <= i < 24 ->
  mbyte SEGS (mrestrict (w_H W3) mem4) (x_o cx + i) = Some (Z_to_bv 8 0)) ->
val_mem SEGS (mrestrict (w_H W3) mem4) (x_o cx + 8) 4 (disco_classify_c.role (x_FB cx) (cK cx)) ->
val_mem SEGS (mrestrict (w_H W3) mem4) (x_o cx + 16) 1 (disco_classify_c.slots (x_FB cx)) ->
val_mem SEGS (mrestrict (w_H W3) mem4) (SHADOW_OFF + cF cx fpos / 8 + 14) 1 0 ->
val_mem SEGS (mrestrict (w_H W3) mem4) (SHADOW_OFF + cF cx fpos / 8 + 15) 1 4 ->
cls_at_Q B cx fpos W3 ly3 S3 regs4 mem4 md4.
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 regs4 mem4 md4 Hpre HR HJ4 INV GROW HRG H1 H10 H11 H22 Z0 V8 V16 V14 V15.
pose proof (NOW cx fpos _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre (proj2 HR)) as HN. cbv zeta in HN.
destruct HR as (Hret & HC). pose proof Hret as Hret0. unfold cRet in Hret.
pose proof (m3_len _ _ _ _ Hret) as H50.
destruct HN as ((HF4096 & HFceil & HF32 & _ & HFapp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) & _ & _ & _ & HOo &
  Ho4096 & Hoceil & _ & HNL).
destruct HOo as ((Ho0 & Ho47 & _ & _ & HoLS) & _ & HoF & HoSP).
destruct HC as (HJ & Hfrs & Hnin & Hperm & Hfa & Hfl & Hkept & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 & RV & SPL &
  L16 & L24 & L48 & _ & _ & GSHP & LFL & _ & LO3 & GO3 & GL).
apply Forall_cons_iff in RV as [R11 RV]. apply Forall_cons_iff in RV as [R21 RV].
apply Forall_cons_iff in RV as [R22 RV]. apply Forall_cons_iff in RV as [R23 RV].
apply Forall_cons_iff in RV as [R24 RV]. apply Forall_cons_iff in RV as [R25 _].
cbn [fst snd] in R11, R21, R22, R23, R24, R25.
pose proof Hpre as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp & _ & _ & Hlen & LFB & _ & _ &
  _ & _ & _ & _ & Hop & Ho4 & _ & _ & _ & _ & _ & _ & HOF & HLd).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _) & _).
pose proof (m3_S1_bounds (cSP cx)) as (HS1 & _). change (cls_S1 (cSP cx)) with (cS1 cx) in HS1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCS : CLS_STK = CLS_VIA_PARSE) by reflexivity.
unfold CLS_VIA_PARSE, CLS_PARSE_NEED, CLS_FRAME, ESTACK in HCS. rewrite HCS in *.
pose proof (m3_div8 _ HF32) as HF8.
unfold cls_at_Q, cls_cut. cbv zeta.
set (F := cF cx fpos) in *. set (FS := SHADOW_OFF + F / 8) in *.
set (SP := cSP cx) in *. set (S1 := cS1 cx) in *. set (o := x_o cx) in *.
assert (HFS : FS = SHADOW_OFF + F / 8) by reflexivity.
assert (HSPr : spZ (x_regs cx) = SP) by reflexivity.
pose proof SB_SHADOW_OFF as HSB. unfold SB in HSB.
unfold in_app, ASAN_CEIL in HFapp.
assert (NP : forall a, (SP - 192 <= a < SP \/ S1 + 16 <= a < S1 + 56 \/ (o <= a < o + 8) \/ (FS <= a < FS + 14) \/
  (FS + 16 <= a < FS + 32) \/ (F + 248 <= a < F + 256)) -> ~ m3_W o FS a).
{ unfold m3_W, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. intros a Ha [Hw|Hw]; lia. }
split; [exact Hret0|].
split; [exact HJ4|]. split; [exact Hfrs|]. split; [exact Hnin|]. split; [exact Hperm|].
split; [exact Hfa|]. split; [exact Hfl|].
split.
{ apply (KS cx fpos W3 ly3 S3 mem3 md3 mem4 (m3_W o FS) Hpre (proj1 HJ) Hfrs Hnin Hperm Hfa Hfl Hkept).
  - intros a Ha Hn. exact (m3_aview_kept (w_H W3) mem3 mem4 (m3_W o FS) INV a Ha Hn).
  - intros a Hp. exact (m3_present_grow _ _ _ a GROW Hp).
  - intros a [Ha|Ha]; fold F FS o; [right; left; unfold cls_wr; left; lia | right; right; right; left; lia]. }
split; [rewrite (HRG 2%bv) by m3_inl; exact R2|].
split; [rewrite (HRG 3%bv) by m3_inl; exact R3|].
split; [rewrite (HRG 4%bv) by m3_inl; exact R4|].
split; [rewrite (HRG 8%bv) by m3_inl; exact R8|].
split; [rewrite (HRG 9%bv) by m3_inl; exact R9|].
split; [rewrite (HRG 18%bv) by m3_inl; exact R18|].
split; [rewrite (HRG 19%bv) by m3_inl; exact R19|].
split; [rewrite (HRG 20%bv) by m3_inl; exact R20|].
split; [rewrite (HRG 27%bv) by m3_inl; exact R27|].
split.
{ apply Forall_cons; [exact H1|]. apply Forall_cons; [exact H10|]. apply Forall_cons; [exact H11|].
  apply Forall_cons; [cbv beta; cbn [fst snd]; transitivity (getr regs3 (Z_to_bv 5 21));
    [exact (HRG 21%bv ltac:(m3_inl)) | exact R21]|].
  apply Forall_cons; [exact H22|].
  apply Forall_cons; [cbv beta; cbn [fst snd]; transitivity (getr regs3 (Z_to_bv 5 23));
    [exact (HRG 23%bv ltac:(m3_inl)) | exact R23]|].
  apply Forall_cons; [cbv beta; cbn [fst snd]; transitivity (getr regs3 (Z_to_bv 5 24));
    [exact (HRG 24%bv ltac:(m3_inl)) | exact R24]|].
  apply Forall_cons; [cbv beta; cbn [fst snd]; transitivity (getr regs3 (Z_to_bv 5 25));
    [exact (HRG 25%bv ltac:(m3_inl)) | exact R25]|].
  apply Forall_nil. }
split.
{ apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) SPL p Hp) as V. cbv beta in V |- *.
  assert (Hoff : -104 <= snd p <= -8) by (unfold cls_spills in Hp; repeat (destruct Hp as [<-|Hp]; [cbn; lia|]); destruct Hp).
  apply (m3_val_mem_kept _ _ (m3_W o FS) _ 8 _ INV); [lia | lia | intros k Hk; apply NP; lia | exact V]. }
split; [apply (m3_val_mem_kept _ _ (m3_W o FS) _ 8 _ INV); [lia | lia | intros k Hk; apply NP; lia | exact L16]|].
split; [apply (m3_val_mem_kept _ _ (m3_W o FS) _ 8 _ INV); [lia | lia | intros k Hk; apply NP; lia | exact L24]|].
split; [apply (m3_val_mem_kept _ _ (m3_W o FS) _ 8 _ INV); [lia | lia | intros k Hk; apply NP; lia | exact L48]|].
split; [intros Hf; discriminate Hf|].
split; [reflexivity|].
split.
{ intros j Hj. cbn [length PAT_B] in Hj.
  destruct (Nat.eq_dec j 14) as [->|H14]; [split; [exact V14 | cbn; lia]|].
  destruct (Nat.eq_dec j 15) as [->|H15]; [split; [exact V15 | cbn; lia]|].
  rewrite (m3_pat j ltac:(lia) H14 H15). destruct (GSHP j ltac:(cbn [length PAT_A]; lia)) as [V R]. split; [|exact R].
  apply (m3_val_mem_kept _ _ (m3_W o FS) _ 1 _ INV); [lia | lia | intros k Hk; apply NP; lia | exact V]. }
split; [apply (m3_val_mem_kept _ _ (m3_W o FS) _ 8 _ INV); [lia | lia | intros k Hk; apply NP; lia | exact LFL]|].
split; [exact I|].
split.
{ unfold cls_O_Q. rewrite !app_length, m3_src_len by exact LFB. reflexivity. }
split.
{ rewrite m3_oq_bytes. change (disco_classify_c.dkind (x_FB cx) (x_len cx)) with (cK cx).
  pose proof (m3_role_range (x_FB cx) (cK cx)) as Hr. pose proof (m3_slots_range (x_FB cx)) as Hs.
  set (r := disco_classify_c.role (x_FB cx) (cK cx)) in *. set (s := disco_classify_c.slots (x_FB cx)) in *.
  assert (LS6 : length (cls_bytes (disco_classify_c.src (x_FB cx))) = 6%nat)
  by (unfold cls_bytes; rewrite map_length; exact (m3_src_len _ LFB)).
  pose proof (m3_by _ o r s Hr Hs Z0 V8 V16) as BY.
  intros j Hj. rewrite app_length, LS6 in Hj. cbn [length m3_tail] in Hj.
  destruct (Nat.lt_ge_cases j 6) as [Hj6|Hj6].
  - rewrite app_nth1 by (rewrite LS6; exact Hj6).
    destruct (GO3 j ltac:(rewrite m3_orole_len by exact LFB; lia)) as [V R].
    rewrite m3_orole_bytes, app_nth1 in V, R by (rewrite LS6; exact Hj6).
    split; [|exact R].
    apply (m3_val_mem_kept _ _ (m3_W o FS) _ 1 _ INV); [lia | lia | intros k Hk; apply NP; lia | exact V].
  - rewrite app_nth2 by (rewrite LS6; exact Hj6). rewrite LS6.
    pose proof (BY (j - 6)%nat ltac:(lia)) as W.
    replace (o + 6 + Z.of_nat (j - 6)) with (o + Z.of_nat j) in W by lia.
    pose proof (m3_tail_range r s (j - 6) ltac:(lia) Hs) as Hrg.
    split; [apply m3_vm1; [exact W | exact Hrg] | exact Hrg]. }
revert GL HNL HLd. destruct (x_L cx) as [Lb|]; destruct (cLock cx) as [Lb'|]; intros GL HNL HLd; try exact GL.
destruct GL as [GLl GLg]. split; [exact GLl|].
destruct HNL as (((Hk0 & Hk47 & _ & _ & HkLS) & _ & _ & _) & Hk4096 & Hkc & _).
destruct HLd as (HkO & _ & _).
apply (m3_garr8_kept _ _ (m3_W o FS) _ _ INV); [lia | unfold cls_bytes; rewrite map_length, GLl; lia | | exact GLg].
intros k Hk. unfold cls_bytes in Hk. rewrite map_length, GLl in Hk.
unfold m3_W, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. intros [Hw|Hw]; lia.
Qed.

Local Ltac m3_awr Uo Ufs AWo AWfs :=
  lazymatch goal with |- awr_ok ?E ?rs _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_gen; [reflexivity | exact Uo | intros a Ha; apply AWo; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |]
  | eapply awr_ok_cons_gen; [reflexivity | exact Ufs | intros a Ha; apply AWfs; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |] ].

Local Ltac m3_post Uo Ufs INV GROW HF HFr HG :=
  repeat match goal with H1 : img_env ?a ?b ?c, H2 : img_env ?a ?b ?c |- _ => clear H2 end;
  let WR := fresh "WR" in let INV2 := fresh "INV" in let GROW2 := fresh "GROW" in
  lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
    pose proof (m3_wr_ok Ex rsx _ _ ltac:(vm_compute; reflexivity) Uo Ufs) as WR end;
  pose proof (m3_inv_step _ _ _ _ _ _ INV HFr WR) as INV2;
  pose proof (m3_grow_step _ _ _ GROW HG) as GROW2;
  clear INV GROW HF HFr HG WR; rename INV2 into INV; rename GROW2 into GROW.

Local Ltac m3_cond_norm :=
  lazymatch goal with Hc : branch_taken BC_NE (sv_denot ?Ex (SOff ?n 0)) (sv_denot _ (SLit ?c)) = ?b |- _ =>
    lazymatch goal with Hn : ew Ex n = Z_to_bv 64 (CtrlParsed.fb _ ?i) |- _ =>
      let C := fresh "C" in
      pose proof (m3_cond Ex n _ c b Hn (m3_fb_range _ i) ltac:(lia) Hc) as C; cbn [negb] in C; clear Hc
    end
  end.

Local Ltac m3_slots :=
  unfold disco_classify_c.slots;
  repeat match goal with C : (CtrlParsed.fb _ _ =? _) = _ |- _ => rewrite C; clear C end;
  cbn [andb]; reflexivity.

Theorem cls_m3 : cls_from_Q B -> cls_from_ROLE B.
Proof.
intros HQ. unfold cls_from_ROLE, cls_from.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HR.
destruct (m3_open cx fpos W3 ly3 S3 regs3 mem3 md3 Hpre HR) as [HS SHOK].
pose proof (NOW cx fpos _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre (proj2 HR)) as HN. cbv zeta in HN.
pose proof HR as (Hret & HC). unfold cRet in Hret.
pose proof (m3_len _ _ _ _ Hret) as H50.
destruct HN as ((HF4096 & HFceil & HF32 & _ & HFapp & _ & HFSp & _ & _ & _ & _ & _ & _ & _ & _) & HFf & _ & _ & HOo &
  Ho4096 & Hoceil & AWo & _).
destruct (HFf H50) as (_ & (Hf0 & Hf47 & _ & _ & HfLS) & _ & _ & HfSP).
destruct HOo as ((Ho0 & Ho47 & _ & _ & HoLS) & _ & HoF & HoSP).
destruct HC as (HJ & _ & _ & _ & Hfa & _ & _ & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 & RV & _).
apply Forall_cons_iff in RV as [R11 RV]. apply Forall_cons_iff in RV as [R21 RV].
apply Forall_cons_iff in RV as [R22 RV]. apply Forall_cons_iff in RV as [R23 RV].
apply Forall_cons_iff in RV as [R24 RV]. apply Forall_cons_iff in RV as [R25 _].
cbn [fst snd] in R11, R21, R22, R23, R24, R25.
pose proof Hpre as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp & _ & _ & Hlen & LFB & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _) & _).
clear HJ0.
pose proof (m3_S1_bounds (cSP cx)) as (HS1 & _). change (cls_S1 (cSP cx)) with (cS1 cx) in HS1.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
assert (HCS : CLS_STK = CLS_VIA_PARSE) by reflexivity.
unfold CLS_VIA_PARSE, CLS_PARSE_NEED, CLS_FRAME, ESTACK in HCS. rewrite HCS in *.
pose proof (m3_div8 _ HF32) as HF8.
unfold in_app, ASAN_CEIL in HFapp. unfold kLowShadowBeg, kHighMemBeg in HFapp, HoLS, HfLS.
remember (m3_E regs3 cx) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs3 (m3_extra cx)) E)
by (subst E; split; [intros n Hn; unfold m3_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E9 : ew E 9 = w64 (cS1 cx)) by (subst E; rewrite <- R9; apply m3_ew_reg; [reflexivity | lia]).
assert (E11 : ew E 11 = w64 (disco_classify_c.role (x_FB cx) (cK cx)))
by (subst E; rewrite <- R11; apply m3_ew_reg; [reflexivity | lia]).
assert (E18 : ew E 18 = w64 (cF cx fpos)) by (subst E; rewrite <- R18; apply m3_ew_reg; [reflexivity | lia]).
assert (E24 : ew E 24 = w64 (x_o cx)) by (subst E; rewrite <- R24; apply m3_ew_reg; [reflexivity | lia]).
assert (E27 : ew E 27 = w64 (SHADOW_OFF + cF cx fpos / 8)) by (subst E; rewrite <- R27; apply m3_ew_reg; [reflexivity | lia]).
assert (E32 : ew E 32 = Z_to_bv 64 (x_f cx)) by (subst E; exact (m3_ew_x regs3 cx 0 ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 16)) by (subst E; exact (m3_ew_x regs3 cx 1 ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 17)) by (subst E; exact (m3_ew_x regs3 cx 2 ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 22)) by (subst E; exact (m3_ew_x regs3 cx 3 ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 23)) by (subst E; exact (m3_ew_x regs3 cx 4 ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 24)) by (subst E; exact (m3_ew_x regs3 cx 5 ltac:(lia))).
assert (E38 : ew E 38 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 25)) by (subst E; exact (m3_ew_x regs3 cx 6 ltac:(lia))).
assert (E39 : ew E 39 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 26)) by (subst E; exact (m3_ew_x regs3 cx 7 ltac:(lia))).
assert (E40 : ew E 40 = Z_to_bv 64 (CtrlParsed.fb (x_FB cx) 33)) by (subst E; exact (m3_ew_x regs3 cx 8 ltac:(lia))).
clear HE.
set (F := cF cx fpos) in *. set (FS := SHADOW_OFF + F / 8) in *.
set (SP := cSP cx) in *. set (S1 := cS1 cx) in *. set (o := x_o cx) in *. set (f := x_f cx) in *.
assert (HFS : FS = SHADOW_OFF + F / 8) by reflexivity.
assert (HSPr : spZ (x_regs cx) = SP) by reflexivity.
pose proof SB_SHADOW_OFF as HSB. unfold SB in HSB.
assert (U9 : bv_unsigned (ew E 9) = S1) by (apply (m3_U E 9 S1 E9); lia).
assert (U18 : bv_unsigned (ew E 18) = F) by (apply (m3_U E 18 F E18); lia).
assert (Uo : bv_unsigned (ew E 24) = o) by (apply (m3_U E 24 o E24); lia).
assert (Ufs : bv_unsigned (ew E 27) = FS) by (apply (m3_U E 27 FS E27); lia).
assert (Uf : bv_unsigned (ew E 32) = f) by (apply (m3_U E 32 f E32); lia).
assert (AWfs : forall a, FS <= a < FS + 32 ->
  awr_byte (x_STK cx) (x_sp0 cx) (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly3 S3) ly3 ((2, fpos) :: x_own cx) a).
{ intros a Ha. right; right; right. exists 2, fpos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  rewrite Hfa. unfold shadow_addr. change (fs_frame_bytes 2 / 8) with 32. lia. }
assert (INV : forall x : word, ~ m3_W o FS (bv_unsigned x) -> mrestrict (w_H W3) mem3 x = mrestrict (w_H W3) mem3 x)
by (intros; reflexivity).
assert (GROW : mem_grows (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) mem3)) by (intros x Hx; exact Hx).
pose (RUN := paj_run (fx := x_fq cx) B LAWS).
pose (BR := paj_branch (fx := x_fq cx) (PI := PI)).
unfold cfg_at. change (w64 (BASE + PC_ROLE)) with (Z_to_bv 64 (BASE + PC_ROLE)).
let leaf := idtac;
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let HS2 := fresh "HS2" in
  pose proof (m3_add_fs _ Ex ssx Wx msx o f S1 FS mem3 HS ltac:(vm_compute; reflexivity) Uo Uf U9 Ufs
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (fun i Hi => HFSp i ltac:(lia)) GROW) as HS2;
  clear HS;
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 _ =>
  let ss2v := eval vm_compute in ss2 in change ss2 with ss2v in HS2;
  let r := eval vm_compute in (sym_runN_pi disco_tpi FUEL ss2v) in
  lazymatch r with (?ss3, PRS_call ?s) =>
  let Hrun := fresh "Hrun" in
  assert (Hrun : sym_runN_pi (@pl_tpi disco_listing PL_disco) FUEL ss2v = (ss3, PRS_call s)) by (vm_compute; reflexivity);
  eapply (SRr_run_pi_AJ_call (fx := x_fq cx) (PI := PI) B LAWS Wx FUEL Ex ss2v ss3 s msx
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS2 Hrun HJ);
  [ m3_awr Uo Ufs AWo AWfs
  | clear Hrun HS2 HJ;
    let ms4 := fresh "ms" in let mat4 := fresh "mat" in
    intros ms4 mat4 HS HJ HF HFr HG; cbn [ms_mem mkst] in HF, HFr, HG, HJ;
    m3_post Uo Ufs INV GROW HF HFr HG;
    let RK := fresh "RK" in
    pose proof (regs_kept_of_st_ok SEGS Ex _ _ regs3 (m3_extra cx) [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 27]%bv
      HS HAE ltac:(vm_compute; reflexivity)) as RK;
    let G1 := fresh "Ga" in prreg HS (1%bv : bv 5) G1;
    let G10 := fresh "Gb" in prreg HS (10%bv : bv 5) G10;
    let G11 := fresh "Gc" in prreg HS (11%bv : bv 5) G11;
    let G22 := fresh "Gd" in prreg HS (22%bv : bv 5) G22;
    rewrite Uf in G10; rewrite U18 in G11; rewrite U18 in G22;
    let RFS := fresh "RFS" in let RO := fresh "RO" in
    pose proof (st_ok_region_nth Ex _ _ 0 _ HS eq_refl) as RFS;
    pose proof (st_ok_region_nth Ex _ _ 1 _ HS eq_refl) as RO;
    let V14 := fresh "Va" in let V15 := fresh "Vb" in
    pose proof (field_of_region Ex _ 27 FS _ 14 16 14 16 14 1 (SLit 0) 0 RFS Ufs ltac:(m3_inl) eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)) as V14;
    pose proof (field_of_region Ex _ 27 FS _ 14 16 14 16 15 1 (SLit 4) 4 RFS Ufs ltac:(m3_inl) eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)) as V15;
    let Z0 := fresh "Za" in let V8 := fresh "Vc" in let V16 := fresh "Vd" in
    destruct (m3_obytes Ex _ _ o _ (disco_classify_c.slots (x_FB cx)) RO Uo ltac:(m3_inl) ltac:(m3_inl) ltac:(m3_inl)
      ltac:(m3_inl) E11 (m3_role_range _ _)
      ltac:(first [ left; split; [m3_inl | m3_slots]
                  | right; split; [m3_inl | rewrite E40; f_equal; symmetry; m3_slots] ])
      (m3_slots_range _)) as (Z0 & V8 & V16);
    pmkst HS; rewrite pa_sigma_reac_ports_parse;
    apply (HQ cx fpos W3 ly3 S3 (ms_regs ms4) (ms_mem ms4) _ Hpre);
    apply (m3_close cx fpos W3 ly3 S3 regs3 mem3 md3 (ms_regs ms4) (ms_mem ms4) _ Hpre HR HJ INV GROW RK);
    [ rewrite G1; reflexivity | exact G10 | exact G11 | exact G22 | exact Z0 | exact V8 | exact V16 | exact V14 | exact V15 ] ]
  end end end in
let rec go := idtac;
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK m3_Bspan; [ m3_awr Uo Ufs AWo AWfs | ];
  m3_post Uo Ufs INV GROW HF HFr HG;
  lazymatch goal with HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
  let K := eval vm_compute in (run_K A_LIM m3_Bx m3_SH ss) in
  let why := lazymatch paj_tables RUN with (?tpi, ?tw) =>
    psym_why_tok tpi tw K m3_Bx m3_Bspan m3_SH (start K m3_Bx m3_Bspan m3_SH ss) end in
  lazymatch why with
  | SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' m3_Bspan; [m3_cond_norm; go | m3_cond_norm; go]
  | SR_store _ _ => leaf
  | _ => idtac "STUCK" why; fail
  end end end in
go.
Qed.

End h.
End f.
End d.
