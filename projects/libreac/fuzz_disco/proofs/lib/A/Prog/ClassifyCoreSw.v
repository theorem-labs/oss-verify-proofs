(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v, with its module paths changed; 1154 of its 1212 lines of code are new or changed and 433 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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

Ltac sw_lbz := unfold YO0f.le_byte; rewrite !Z.shiftr_div_pow2 by lia; cbn [Z.of_nat];
  cbn [Z.mul Z.pow Z.pow_pos Pos.mul Pos.iter Pos.add]; Z.div_mod_to_equations; lia.

Lemma sw_ps : forall len FB, fst (RcParse.ctrlparse len FB) <> 0 ->
let P := cls_bytes (snd (RcParse.ctrlparse len FB)) in
nth 0 P 0 = fst (RcParse.ctrlparse len FB) /\ nth 1 P 0 = 0 /\ nth 2 P 0 = 0 /\ nth 3 P 0 = 0 /\
nth 16 P 0 = (if RcParse.cp_bcast FB then 1 else 0) /\ nth 17 P 0 = 0 /\ nth 18 P 0 = 0 /\ nth 19 P 0 = 0 /\
nth 26 P 0 = RcParse.cp_v FB 22 /\ (forall j, (j < 6)%nat -> nth (4 + j) P 0 = RcParse.cp_v FB (6 + j)) /\
(fst (RcParse.ctrlparse len FB) = 5 -> nth 28 P 0 = RcParse.cp_v FB 35 /\ nth 29 P 0 = RcParse.cp_v FB 34).
Proof.
intros len FB Hk P. subst P.
pose proof (fun H5 => RcParse.ctrlparse_rec len FB (or_introl H5)) as R5.
pose proof (RcParse.cp_kind_range FB) as KR.
unfold RcParse.ctrlparse in *. destruct (RcParse.cp_hdr len FB) eqn:Hh; cbn [fst snd] in *; [|lia].
unfold cls_bytes, RcParse.cp_struct.
assert (K0 : bv_unsigned (Z_to_bv 8 (RcParse.cp_kind FB)) = RcParse.cp_kind FB).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia. }
assert (B16 : bv_unsigned (if RcParse.cp_bcast FB then Z_to_bv 8 1 else RcParse.cp_z) = (if RcParse.cp_bcast FB then 1 else 0))
  by (destruct (RcParse.cp_bcast FB); reflexivity).
destruct (RcParse.cp_rec FB) eqn:Hr; destruct (RcParse.cp_kind FB =? 6); cbn [map app nth];
(split; [exact K0|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]);
(split; [exact B16|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]);
(split; [reflexivity|]);
(split; [intros j Hj; do 6 (destruct j as [|j]; [reflexivity|]); lia|]);
intros H5; destruct (R5 H5) as (_ & HR & _); try discriminate HR; split; reflexivity.
Qed.

Lemma sw_ret0 : forall FB len U L, disco_classify_c.cm_ret FB len U L = 0 -> disco_classify_c.dkind FB len <> 0.
Proof.
intros FB len U L H Hk. unfold disco_classify_c.cm_ret, disco_classify_c.classify_model in H.
rewrite Hk in H. cbn in H. discriminate H.
Qed.

Lemma sw_role_hi : forall F k, 10 <= k <= 13 -> disco_classify_c.role F k = 0.
Proof.
intros F k Hk. assert (E : k = 10 \/ k = 11 \/ k = 12 \/ k = 13) by lia.
destruct E as [ -> | [ -> | [ -> | -> ] ] ]; reflexivity.
Qed.

Definition sw_lock (P : Prop) : Prop := P.

Definition SW_Bx : sv := SOff 32 0.
Definition SW_SH : list shent := [].
Definition SWspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

Definition sw_loc_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 8 24 8 8
  [YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
Definition sw_q_region : YP09.region :=
YP09.mkRegion (Some 22%nat) 0 36 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 35 0)); YP09.mkChunk 16 (CVal 4 (SOff 36 0));
   YP09.mkChunk 26 (CVal 1 (SOff 37 0)); YP09.mkChunk 28 (CVal 2 (SOff 38 0))].
Definition sw_tab_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 35)) 0 36 0 0
  (map (fun i => YP09.mkChunk (4 * Z.of_nat i) (CVal 4 (SOff (39 + i) 0))) (seq 0 9)).
Definition sw_facts : facts :=
mkFacts [(32%nat, mkAF SB SB 0); (35%nat, mkAF 0 13 0); (36%nat, mkAF 0 255 0);
         (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 (2 ^ 16 - 1) 0)] [] [].
Definition ss_sw : sstate := mkSS PC_SW sr_atoms [sw_loc_region; sw_q_region] None sw_facts.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Definition sw_tab (i : nat) : Z := (BASE + AF_classify_core + nth i CLS_SW_ARMS 0 - VAL (A_OBJ 35)) mod 2 ^ 32.
Definition sw_extra (len o k bc fb tg : Z) : list word :=
map (Z_to_bv 64) ([SB; len; o; k; bc; fb; tg] ++ map sw_tab (seq 0 9)).
Definition SWE (regs : bvmap 5 word) (len o k bc fb tg : Z) : env := Eimg (Ereg regs (sw_extra len o k bc fb tg)).

Lemma sw_vm2 : forall (m : word -> option byte) a b0 b1,
val_mem SEGS m a 1 b0 -> val_mem SEGS m (a + 1) 1 b1 -> 0 <= b0 < 256 -> 0 <= b1 < 256 ->
val_mem SEGS m a 2 (b0 + 256 * b1).
Proof.
intros m a b0 b1 H0 H1 R0 R1 j Hj.
destruct j as [|[|j]]; [| | lia].
- specialize (H0 0%nat ltac:(lia)). rewrite H0. do 2 f_equal. sw_lbz.
- specialize (H1 0%nat ltac:(lia)). replace (a + Z.of_nat 1) with (a + 1 + Z.of_nat 0) by lia. rewrite H1.
  do 2 f_equal. sw_lbz.
Qed.

Lemma sw_vm4z : forall (m : word -> option byte) a b0,
val_mem SEGS m a 1 b0 -> val_mem SEGS m (a + 1) 1 0 -> val_mem SEGS m (a + 2) 1 0 -> val_mem SEGS m (a + 3) 1 0 ->
0 <= b0 < 256 -> val_mem SEGS m a 4 b0.
Proof.
intros m a b0 H0 H1 H2 H3 R0 j Hj.
destruct j as [|[|[|[|j]]]]; [| | | | lia].
- specialize (H0 0%nat ltac:(lia)). rewrite H0. do 2 f_equal. sw_lbz.
- specialize (H1 0%nat ltac:(lia)). replace (a + Z.of_nat 1) with (a + 1 + Z.of_nat 0) by lia. rewrite H1.
  do 2 f_equal. sw_lbz.
- specialize (H2 0%nat ltac:(lia)). replace (a + Z.of_nat 2) with (a + 2 + Z.of_nat 0) by lia. rewrite H2.
  do 2 f_equal. sw_lbz.
- specialize (H3 0%nat ltac:(lia)). replace (a + Z.of_nat 3) with (a + 3 + Z.of_nat 0) by lia. rewrite H3.
  do 2 f_equal. sw_lbz.
Qed.

Lemma sw_ew : forall (regs : bvmap 5 word) len o k bc fb tg,
ew (SWE regs len o k bc fb tg) 32 = Z_to_bv 64 SB /\ ew (SWE regs len o k bc fb tg) 33 = Z_to_bv 64 len /\
ew (SWE regs len o k bc fb tg) 34 = Z_to_bv 64 o /\ ew (SWE regs len o k bc fb tg) 35 = Z_to_bv 64 k /\
ew (SWE regs len o k bc fb tg) 36 = Z_to_bv 64 bc /\ ew (SWE regs len o k bc fb tg) 37 = Z_to_bv 64 fb /\
ew (SWE regs len o k bc fb tg) 38 = Z_to_bv 64 tg /\
(forall i, (i < 9)%nat -> ew (SWE regs len o k bc fb tg) (39 + i) = Z_to_bv 64 (sw_tab i)) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (SWE regs len o k bc fb tg) n = getr regs r).
Proof.
intros regs len o k bc fb tg. unfold SWE.
assert (X : forall j, (j < 16)%nat ->
  ew (Eimg (Ereg regs (sw_extra len o k bc fb tg))) (32 + j) = nth j (sw_extra len o k bc fb tg) (Z_to_bv 64 0)).
{ intros j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
split; [exact (X 0%nat ltac:(lia))|]. split; [exact (X 1%nat ltac:(lia))|].
split; [exact (X 2%nat ltac:(lia))|]. split; [exact (X 3%nat ltac:(lia))|].
split; [exact (X 4%nat ltac:(lia))|]. split; [exact (X 5%nat ltac:(lia))|].
split; [exact (X 6%nat ltac:(lia))|].
split.
- intros i Hi. replace (39 + i)%nat with (32 + (7 + i))%nat by lia. rewrite X by lia.
  unfold sw_extra. rewrite map_nth. f_equal. cbn [app nth Nat.add].
  rewrite (nth_indep _ 0 (sw_tab 0)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
- intros n r Hn. apply ew_Eimg_Ereg_nat. exact Hn.
Qed.

Lemma sw_entry : forall (fq : YK11.FPState) (W3 : world SEGS) (mem3 : word -> option byte) (regs3 : bvmap 5 word)
  S1 F len o k bc fb tg,
getr regs3 9 = w64 S1 -> getr regs3 22 = w64 (F + 32) ->
0 <= S1 -> S1 + 24 <= 2 ^ 64 -> 0 <= F -> F + 68 <= 2 ^ 64 ->
(S1 + 24 <= F + 32 \/ F + 68 <= S1 + 8) ->
0 <= len < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= k <= 13 -> 0 <= bc < 256 -> 0 <= fb < 256 -> 0 <= tg < 2 ^ 16 ->
val_mem SEGS (mrestrict (w_H W3) mem3) (S1 + 8) 8 len -> val_mem SEGS (mrestrict (w_H W3) mem3) (S1 + 16) 8 o ->
val_mem SEGS (mrestrict (w_H W3) mem3) (F + 32) 4 k -> val_mem SEGS (mrestrict (w_H W3) mem3) (F + 48) 4 bc ->
val_mem SEGS (mrestrict (w_H W3) mem3) (F + 58) 1 fb -> val_mem SEGS (mrestrict (w_H W3) mem3) (F + 60) 2 tg ->
st_ok_pi SEGS VAL (SWE regs3 len o k bc fb tg) ss_sw
  (restrict (w_H W3) (mkst (fx := fq) regs3 (Z_to_bv 64 (BASE + PC_SW)) mem3 (seg_rom SEGS))) /\
sh_ok SEGS SW_Bx SW_SH (SWE regs3 len o k bc fb tg) (mrestrict (w_H W3) mem3).
Proof.
intros fq W3 mem3 regs3 S1 F len o k bc fb tg H9 H22 RS0 RS1 RF0 RF1 HD Rlen Ro Rk Rbc Rfb Rtg
  Mlen Mo Mk Mbc Mfb Mtg.
destruct (sw_ew regs3 len o k bc fb tg) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & _ & ER).
set (E := SWE regs3 len o k bc fb tg) in *.
assert (E9 : ew E 9 = Z_to_bv 64 S1) by (rewrite (ER 9%nat 9%bv eq_refl); exact H9).
assert (E22 : ew E 22 = Z_to_bv 64 (F + 32)) by (rewrite (ER 22%nat 22%bv eq_refl); exact H22).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx.
split.
- unfold ss_sw. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold sw_loc_region, sw_q_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 9%nat S1 E9) by lia. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ S1 8 8 (SOff 33 0) len);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mlen].
      -- apply (chunk_ok_val SEGS E _ S1 16 8 (SOff 34 0) o);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mo].
    * rewrite (VB 22%nat (F + 32) E22) by lia. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      -- apply (chunk_ok_val SEGS E _ (F + 32) 0 4 (SOff 35 0) k);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Mk.
      -- apply (chunk_ok_val SEGS E _ (F + 32) 16 4 (SOff 36 0) bc);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         replace (F + 32 + 16) with (F + 48) by lia. exact Mbc.
      -- apply (chunk_ok_val SEGS E _ (F + 32) 26 1 (SOff 37 0) fb);
         [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         replace (F + 32 + 26) with (F + 58) by lia. exact Mfb.
      -- apply (chunk_ok_val SEGS E _ (F + 32) 28 2 (SOff 38 0) tg);
         [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         replace (F + 32 + 28) with (F + 60) by lia. exact Mtg.
  + apply pairwise_disjoint_of_extents. unfold sw_loc_region, sw_q_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat S1 E9) by lia. rewrite (VB 22%nat (F + 32) E22) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + unfold sw_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by (unfold SB; lia);
            rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E35, unsigned_lit_small by lia;
            rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E36, unsigned_lit_small by lia;
            rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E37, unsigned_lit_small by lia;
            rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia;
            rewrite Z.pow_0_r; split; [lia|]; split; [apply Z.mod_1_r | lia]|].
    exact I.
- unfold sh_ok, SW_SH. apply Forall_nil.
Qed.

Lemma sw_aview_of_vm1 : forall H (m : word -> option byte) a v,
val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hr. unfold aview. specialize (Hv 0%nat ltac:(lia)). replace (a + Z.of_nat 0) with a in Hv by lia.
rewrite Hv. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.

Lemma sw_gb : forall (m : word -> option byte) a l, garr8 SEGS m a l ->
forall j a', (j < length l)%nat -> a' = a + Z.of_nat j -> val_mem SEGS m a' 1 (nth j l 0) /\ 0 <= nth j l 0 < 256.
Proof. intros m a l H j a' Hj ->. exact (H j Hj). Qed.

Lemma sw_aview_pres : forall H (m : word -> option byte) a, apresent H m a -> aview SEGS H m a <> None.
Proof.
intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

Lemma sw_shz : forall x, 0 <= x < 2 ^ 47 -> SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < kHighMemBeg.
Proof.
intros x Hx. unfold shadow_of_addr. assert (0 <= x / 8) by (apply Z.div_pos; lia).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold SHADOW_OFF, kHighMemBeg. lia.
Qed.

Lemma sw_SBdiv : forall y, 0 <= y -> (SHADOW_OFF + y) / 8 = SHADOW_OFF / 8 + y / 8.
Proof.
intros y Hy. assert (S8 : SHADOW_OFF = SHADOW_OFF / 8 * 8) by reflexivity.
rewrite S8 at 1. rewrite Z.div_add_l by lia. reflexivity.
Qed.

Lemma sw_hullz : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 - 1 ->
shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> SHADOW_OFF <= s < kHighMemBeg.
Proof.
intros x n s Hx Hn Hxn Hs. unfold shadow_addr in Hs.
rewrite !sw_SBdiv in Hs by (apply Z.div_pos; lia).
assert (A1 : 0 <= x / 8 / 8) by (apply Z.div_pos; [apply Z.div_pos|]; lia).
assert (A2 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (A3 : (x + n - 1) / 8 / 8 < 2 ^ 41) by (apply Z.div_lt_upper_bound; lia).
assert (S8 : SHADOW_OFF / 8 * 8 = SHADOW_OFF) by reflexivity.
assert (KH : kHighMemBeg = SHADOW_OFF + 2 ^ 44) by reflexivity. lia.
Qed.

Lemma sw_ra_sub : forall rd b a len a' len', range_addressable rd b a len -> a <= a' -> a' + len' <= a + len ->
range_addressable rd b a' len'.
Proof. intros rd b a len a' len' H H1 H2 x Hx. apply H. lia. Qed.

Lemma sw_hull_sub : forall rd a len a' len', shadow_hull_vis rd a len -> a <= a' -> a' + len' <= a + len ->
shadow_hull_vis rd a' len'.
Proof.
intros rd a len a' len' H H1 H2 s Hs. apply H.
assert (M1 : shadow_addr a / 8 <= shadow_addr a' / 8) by (apply Z.div_le_mono; [lia | apply shadow_mono; lia]).
assert (M2 : shadow_addr (a' + len' - 1) / 8 <= shadow_addr (a + len - 1) / 8)
  by (apply Z.div_le_mono; [lia | apply shadow_mono; lia]).
lia.
Qed.

Lemma sw_ra_tr : forall (rd rd' : Z -> option Z) a len, (forall s, SHADOW_OFF <= s < kHighMemBeg -> rd' s = rd s) ->
0 <= a -> a + len <= 2 ^ 47 -> range_addressable rd SHADOW_OFF a len -> range_addressable rd' SHADOW_OFF a len.
Proof.
intros rd rd' a len Hq Ha Hl H. apply (range_addressable_agree rd rd' SHADOW_OFF a len); [|exact H].
intros x Hx. apply Hq. apply sw_shz. lia.
Qed.

Lemma sw_hull_tr : forall (rd rd' : Z -> option Z) a len, (forall s, SHADOW_OFF <= s < kHighMemBeg -> rd' s = rd s) ->
0 <= a -> 0 < len -> a + len <= 2 ^ 47 - 1 -> shadow_hull_vis rd a len -> shadow_hull_vis rd' a len.
Proof. intros rd rd' a len Hq Ha Hn Hl H s Hs. rewrite Hq by exact (sw_hullz a len s Ha Hn Hl Hs). exact (H s Hs). Qed.

Lemma sw_fsrc : forall (H : word -> bool) (m : word -> option byte) F,
0 <= F -> F mod 32 = 0 -> garr8 SEGS (mrestrict H m) (SHADOW_OFF + F / 8) PAT_A ->
(forall i, 0 <= i < 32 -> apresent H m (SHADOW_OFF + F / 8 + i)) ->
range_addressable (aview SEGS H m) SHADOW_OFF (F + 36) 6 /\ shadow_hull_vis (aview SEGS H m) (F + 36) 6.
Proof.
intros H m F HF0 HF32 HG HP.
destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) HF32) as [c Hc].
assert (HF8 : F / 8 = 4 * c) by (symmetry; apply (Z.div_unique F 8 (4 * c) 0); lia).
split.
- intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  assert (Hx8 : x / 8 = 4 * c + 4 \/ x / 8 = 4 * c + 5).
  { destruct (Z.lt_ge_cases x (32 * c + 40)) as [Hl|Hl]; [left; symmetry; apply (Z.div_unique x 8 _ (x - 8 * (4 * c + 4)))
      | right; symmetry; apply (Z.div_unique x 8 _ (x - 8 * (4 * c + 5)))]; lia. }
  destruct Hx8 as [Hx8 | Hx8]; rewrite Hx8.
  + destruct (HG 4%nat ltac:(cbn; lia)) as [Hv Hr]. apply sw_aview_of_vm1 in Hv; [|exact Hr].
    rewrite HF8 in Hv. cbn [nth PAT_A] in Hv. rewrite <- Hv. f_equal. lia.
  + destruct (HG 5%nat ltac:(cbn; lia)) as [Hv Hr]. apply sw_aview_of_vm1 in Hv; [|exact Hr].
    rewrite HF8 in Hv. cbn [nth PAT_A] in Hv. rewrite <- Hv. f_equal. lia.
- intros s Hs. unfold shadow_addr in Hs. rewrite !sw_SBdiv in Hs by (apply Z.div_pos; lia).
  assert (E1 : (F + 36) / 8 = 4 * c + 4) by (symmetry; apply (Z.div_unique _ 8 _ 4); lia).
  assert (E2 : (F + 36 + 6 - 1) / 8 = 4 * c + 5) by (symmetry; apply (Z.div_unique _ 8 _ 1); lia).
  rewrite E1, E2 in Hs.
  pose proof (Z.div_mod (4 * c + 4) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (4 * c + 4) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod (4 * c + 5) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (4 * c + 5) 8 ltac:(lia)) as B2.
  pose proof (Z.div_mod (c + 1) 2 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (c + 1) 2 ltac:(lia)) as B3.
  assert (E3 : (4 * c + 4) / 8 = (c + 1) / 2).
  { symmetry; apply (Z.div_unique _ 8 _ (4 * ((c + 1) mod 2))); lia. }
  rewrite E3 in Hs.
  apply sw_aview_pres. replace s with (SHADOW_OFF + F / 8 + (s - (SHADOW_OFF + F / 8))) by lia. apply HP.
  assert (S8 : SHADOW_OFF / 8 * 8 = SHADOW_OFF) by reflexivity. rewrite HF8. lia.
Qed.

Lemma sw_orole : forall FB i, length FB = 50%nat ->
nth i (cls_bytes (cls_O_ROLE FB)) 0 = (if (i <? 6)%nat then RcParse.cp_v FB (6 + i) else 0).
Proof.
intros FB i HL. unfold cls_bytes, cls_O_ROLE, disco_classify_c.src, CtrlParsed.fld.
destruct FB as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 FB]]]]]]]]]]]]; cbn in HL; try lia.
do 24 (destruct i as [|i]; [reflexivity|]). cbn. destruct i; reflexivity.
Qed.

Lemma sw_frame_ro : forall E rs (m m' : word -> option byte),
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> m' = m.
Proof.
intros E rs m m' Hro HF. extensionality x. apply HF. intros (r & Hin & Hr).
pose proof (proj1 (forallb_forall _ rs) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.

Lemma sw_slot_img : forall k e, 0 <= k < 2 ^ 40 -> plookup pl_tpi k = Some e -> IMG_LO <= BASE + k < IMG_TOP.
Proof.
intros k e Hk40 Hk. pose proof pa_B_ok as HB. rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot dsym (clookup pa_tbl) VAL SIGMA disco_listing pa_cert k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
assert (Himg : in_img SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k)))).
{ exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
pose proof (pa_img_range _ Himg) as HR.
rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
rewrite Z.mod_small in HR by lia. lia.
Qed.

Lemma sw_slot_img' : forall k, 0 <= k < 2 ^ 40 ->
(match plookup pl_tpi k with Some _ => true | None => false end) = true -> IMG_LO <= BASE + k < IMG_TOP.
Proof. intros k Hk H. destruct (plookup pl_tpi k) as [e|] eqn:He; [exact (sw_slot_img k e Hk He) | discriminate]. Qed.

Lemma sw_even : forall t, t mod 2 = 0 -> (BASE + t) mod 2 = 0.
Proof.
intros t Ht. pose proof pa_B_ok as (_ & _ & HB4).
assert (HB2 : BASE mod 2 = 0).
{ apply Z.mod_divide in HB4; [|lia]. apply Z.mod_divide; [lia|]. destruct HB4 as [q Hq]. exists (2 * q). lia. }
rewrite Z.add_mod, HB2, Ht by lia. reflexivity.
Qed.

Lemma sw_jr_val : forall V T, -2^31 <= T - V < 2^31 ->
  alu64 ALU_ADD (sext 64 (bv_extract 0 32 (Z_to_bv 64 ((T - V) mod 2 ^ 32)))) (Z_to_bv 64 V) = Z_to_bv 64 T.
Proof.
intros V T H.
assert (X : bv_extract 0 32 (Z_to_bv 64 ((T - V) mod 2 ^ 32)) = bv_extract 0 32 (Z_to_bv 64 (T - V))).
{ apply bv_eq. rewrite !bv_extract_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). rewrite !Z.shiftr_0_r.
  rewrite (Z.mod_small ((T - V) mod 2 ^ 32) (2 ^ 64)) by (pose proof (Z.mod_pos_bound (T - V) (2 ^ 32)); lia).
  rewrite Z.mod_mod by lia. symmetry. apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity. }
rewrite X, sext32_small by exact H. rewrite alu64_add_lit. f_equal. lia.
Qed.

Ltac sw_srg := lazymatch goal with |- context [sr_get ?rs ?r] => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end.

Definition SW_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 25; 27]%bv.

Lemma sw_vm_tr : forall H (m m' : word -> option byte) a n v,
(forall i, 0 <= i < Z.of_nat n -> aview SEGS H m' (a + i) = aview SEGS H m (a + i)) ->
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hq Hv j Hj. rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat j)).
- exact (Hv j Hj).
- apply Hq. lia.
Qed.

Lemma sw_garr8_tr : forall H (m m' : word -> option byte) a l,
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H m' (a + i) = aview SEGS H m (a + i)) ->
garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
intros H m m' a l Hq Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (sw_vm_tr H m m'); [|exact Hv]. intros i Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi.
replace (a + Z.of_nat j + i) with (a + (Z.of_nat j + i)) by lia. apply Hq. lia.
Qed.

Lemma sw_vm1_of_aview : forall H (m : word -> option byte) a v,
aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v /\ 0 <= v < 256.
Proof.
intros H m a v Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; [|discriminate]. cbn [option_map] in Hv. injection Hv as <-.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|lia].
intros j Hj. assert (j = 0%nat) by lia. subst j. replace (a + Z.of_nat 0) with a by lia. rewrite Hb. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r. rewrite !(Z.mod_small (bv_unsigned b)) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : forall fq, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis AMEMSET : forall fq, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis NOW : cls_now_ok B.
Hypothesis KS : cls_kept_step_ok B.
Hypothesis ROM : cls_rom_ok B.

Lemma sw_close : forall cx fpos W3 ly3 S3 regs3 mem3 md3 regs6 mem6 md6,
cls_from_ROLE B -> cls_pre B cx -> cls_at_SW B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  ((2, fpos) :: x_own cx) ly3 S3 W3 mem6 md6 (x_k cx) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_o cx <= a < x_o cx + 24) -> ~ (cS1 cx - ESTACK <= a < cS1 cx) ->
  aview SEGS (w_H W3) mem6 a = aview SEGS (w_H W3) mem3 a) ->
(forall i, 0 <= i < 24 -> aview SEGS (w_H W3) mem6 (x_o cx + i) =
  Some (nth (Z.to_nat i) (cls_bytes (cls_O_ROLE (x_FB cx))) 0)) ->
(forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem6 a) ->
(forall r, In r SW_KEPT -> getr regs6 r = getr regs3 r) ->
getr regs6 11 = w64 (disco_classify_c.role (x_FB cx) (cK cx)) -> getr regs6 21 = w64 (x_len cx) ->
getr regs6 23 = w64 SHADOW_OFF -> getr regs6 24 = w64 (x_o cx) ->
SRr SEGS W3 (mkCfg (mkst (fx := x_fq cx) regs6 (Z_to_bv 64 (BASE + PC_ROLE)) mem6 (seg_rom SEGS)) md6) (cls_Q B cx).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 regs6 mem6 md6 HROLE HPRE HAT HJ6 HK6 HO6 HP6 HR6 R11 R21 R23 R24.
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 HPRE (proj2 HAT)) as HN.
destruct HAT as [Hret HCUT].
pose proof HPRE as HPRE0.
unfold cls_pre in HPRE0. cbv zeta in HPRE0.
destruct HPRE0 as (HJ0 & HROD & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & H14 & Hch & Hsp16 & Hstk & Hsp0 &
  Htop & Hdep & Hlen & HFBl & HUl & HOBl & Hf50 & Hur & Hus & Hug & Ho0 & Ho4 & Hor & Hog & How & Hoff & HL &
  Hdou & Hdof & HdL).
pose proof HCUT as HCUT0.
unfold cls_cut in HCUT0. cbv zeta in HCUT0.
destruct HCUT0 as (HJ & Hfr & Hnin & Hperm & Hfa & Hfl & Hkept & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 &
  HRV & Hspill & Mo & Mf & MF & MLS & HSHPl & HSHP & MFL & HPS & HO3l & HO3 & HL3).
cbv zeta in HN.
destruct HN as ((HF4096 & HFceil & HF32 & HFz & HFapp & HFpres & HFSpres & HFL4096 & HFLz & HFLc & HFLp & HFLo &
  HFLn & HFb & HFf) & _ & _ & _ & (Hoa & Hol & HoF & HoS) & Ho4096 & Hoc & Hoawr & HNL).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
pose proof Hastk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCS : CLS_STK = 8512) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
set (SP := cSP cx) in *. set (S1 := cS1 cx) in *. set (F := cF cx fpos) in *. set (o := x_o cx) in *.
change (spZ (x_regs cx)) with SP in *.
assert (HS1 : SP - 192 < S1 <= SP - 160).
{ subst S1. unfold cS1, cls_S1. fold SP. pose proof (Z.mod_pos_bound (SP - 160) 32 ltac:(lia)).
  pose proof (Z.div_mod (SP - 160) 32 ltac:(lia)). lia. }
assert (HSP : alloc_ceiling + CLS_STK <= SP <= 2 ^ 47) by lia.
destruct Hoa as (Ho0' & Ho47 & Hoamr & Hooff & Hoband).
assert (HoW : forall a, o <= a < o + 24 -> SP <= a \/ a < SP - CLS_STK) by lia.
assert (TR : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall x, a <= x < a + n -> ~ (o <= x < o + 24) /\ ~ (S1 - ESTACK <= x < S1)) ->
  forall i, 0 <= i < n -> aview SEGS (w_H W3) mem6 (a + i) = aview SEGS (w_H W3) mem3 (a + i)).
{ intros a n Ha Han Hx i Hi. destruct (Hx (a + i) ltac:(lia)) as [X1 X2]. apply HK6; [lia | exact X1 | exact X2]. }
apply (HROLE cx fpos W3 ly3 S3 regs6 mem6 md6 HPRE).
unfold cls_at_ROLE, cls_cut. cbv zeta. split; [exact Hret|].
try change (cF cx fpos) with F. try change (cSP cx) with SP. try change (cS1 cx) with S1. try change (x_o cx) with o.
assert (KP : forall r, In r SW_KEPT -> getr regs6 r = getr regs3 r) by exact HR6.
assert (INK : forall r : bv 5, In r SW_KEPT -> In r SW_KEPT) by (intros; assumption).
split; [exact HJ6|]. split; [exact Hfr|]. split; [exact Hnin|]. split; [exact Hperm|].
split; [exact Hfa|]. split; [exact Hfl|].
split.
{ apply (KS cx fpos W3 ly3 S3 mem3 md3 mem6 (fun a => (o <= a < o + 24) \/ (S1 - ESTACK <= a < S1))
    HPRE (proj1 HJ) Hfr Hnin Hperm Hfa Hfl Hkept).
  - intros a Ha Hn. apply HK6; [exact Ha | intros X; apply Hn; left; exact X | intros X; apply Hn; right; exact X].
  - exact HP6.
  - intros a [Ha | Ha]; [right; left; unfold cls_wr; left; exact Ha | left; lia]. }
split; [rewrite (HR6 2%bv) by (unfold SW_KEPT; cbn [In]; repeat (first [left; reflexivity | right])); exact R2|].
split; [rewrite (HR6 3%bv) by (unfold SW_KEPT; cbn [In]; repeat (first [left; reflexivity | right])); exact R3|].
split; [rewrite (HR6 4%bv) by (unfold SW_KEPT; cbn [In]; repeat (first [left; reflexivity | right])); exact R4|].
split; [rewrite (HR6 8%bv) by (unfold SW_KEPT; cbn [In]; repeat (first [left; reflexivity | right])); exact R8|].
split; [rewrite (HR6 9%bv) by (unfold SW_KEPT; cbn [In]; repeat (first [left; reflexivity | right])); exact R9|].
split; [rewrite (HR6 18%bv) by (unfold SW_KEPT; cbn [In]; repeat (first [left; reflexivity | right])); exact R18|].
split; [rewrite (HR6 19%bv) by (unfold SW_KEPT; cbn [In]; repeat (first [left; reflexivity | right])); exact R19|].
split; [rewrite (HR6 20%bv) by (unfold SW_KEPT; cbn [In]; repeat (first [left; reflexivity | right])); exact R20|].
split; [rewrite (HR6 27%bv) by (unfold SW_KEPT; cbn [In]; repeat (first [left; reflexivity | right])); exact R27|].
rewrite !Forall_cons_iff in HRV. cbn [fst snd] in HRV. destruct HRV as (V21 & V22 & V25 & _).
split.
{ repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - exact R11.
  - exact R21.
  - rewrite (HR6 22%bv) by (unfold SW_KEPT; cbn [In]; repeat (first [left; reflexivity | right])). exact V22.
  - exact R23.
  - exact R24.
  - rewrite (HR6 25%bv) by (unfold SW_KEPT; cbn [In]; repeat (first [left; reflexivity | right])). exact V25. }
split.
{ apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) Hspill p Hp) as Hv.
  assert (Hb : -104 <= snd p <= -8)
    by (unfold cls_spills in Hp; cbn [In] in Hp; repeat (destruct Hp as [<-|Hp]; [cbn [snd]; lia|]); destruct Hp).
  apply (sw_vm_tr _ mem3 mem6); [|exact Hv].
  apply TR; [lia | lia | intros x Hx; split; lia]. }
split.
{ apply (sw_vm_tr _ mem3 mem6); [|exact Mo]. apply TR; [lia | lia | intros x Hx; split; lia]. }
split.
{ apply (sw_vm_tr _ mem3 mem6); [|exact Mf]. apply TR; [lia | lia | intros x Hx; split; lia]. }
split.
{ apply (sw_vm_tr _ mem3 mem6); [|exact MF]. apply TR; [lia | lia | intros x Hx; split; lia]. }
split; [intros X; discriminate X|].
split; [exact HSHPl|].
split.
{ apply (sw_garr8_tr _ mem3 mem6); [|exact HSHP]. rewrite HSHPl. change (Z.of_nat 32) with 32.
  assert (HF8 : F / 8 < 2 ^ 44 - 2 ^ 20) by (apply Z.div_lt_upper_bound; lia).
  assert (HF80 : 0 <= F / 8) by (apply Z.div_pos; lia).
  apply TR; [unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia |].
  intros x Hx. unfold SHADOW_OFF in Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hoamr.
  split; lia. }
split.
{ apply (sw_vm_tr _ mem3 mem6); [|exact MFL]. apply TR; [lia | lia | intros x Hx; split; lia]. }
split; [exact I|].
assert (HOL : length (cls_O_ROLE (x_FB cx)) = 24%nat).
{ unfold cls_O_ROLE, disco_classify_c.src, CtrlParsed.fld. rewrite length_app, repeat_length, length_firstn, length_skipn.
  rewrite HFBl. reflexivity. }
split; [exact HOL|].
split.
{ intros j Hj. unfold cls_bytes in Hj. rewrite length_map, HOL in Hj.
  destruct (sw_vm1_of_aview _ _ _ _ (HO6 (Z.of_nat j) ltac:(lia))) as [Hv Hr]. rewrite Nat2Z.id in Hv, Hr.
  split; [exact Hv | exact Hr]. }
destruct (x_L cx) as [Lx|] eqn:EL; destruct (cLock cx) as [Lb|]; [| exact HL3 | exact HL3 | exact I].
destruct HL3 as [HLl HLg]. split; [exact HLl|].
destruct HNL as ((Hla & _ & HlF & HlS) & _ & _ & _).
destruct HdL as (Hdlo & _ & _).
apply (sw_garr8_tr _ mem3 mem6); [|exact HLg].
assert (HLc : length (cls_bytes Lb) = 12%nat) by (unfold cls_bytes; rewrite length_map; exact HLl). rewrite HLc.
destruct Hla as (Hl0 & Hl47 & _).
apply TR; [clear - Hl0; lia | clear - Hl47; lia | intros x Hx; split; [clear - Hx Hdlo; lia | clear - Hx HlS HS1 HCS HES; lia]].
Qed.

Lemma sw_leaf : forall cx fpos W3 ly3 S3 regs3 mem3 md3 E (ss : sstate) ms md extra,
cls_from_ROLE B -> cls_pre B cx -> cls_at_SW B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
st_ok_pi (fx := x_fq cx) SEGS VAL E ss (restrict (w_H W3) ms) -> ss_pc ss = PC_ROLE -> ss_resv ss = None ->
env_agree 32 (Ereg regs3 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) SW_KEPT = true ->
sv_denot E (sr_get (ss_regs ss) 11) = w64 (disco_classify_c.role (x_FB cx) (cK cx)) ->
sv_denot E (sr_get (ss_regs ss) 21) = w64 (x_len cx) ->
sv_denot E (sr_get (ss_regs ss) 23) = w64 SHADOW_OFF ->
sv_denot E (sr_get (ss_regs ss) 24) = w64 (x_o cx) ->
ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  ((2, fpos) :: x_own cx) ly3 S3 W3 (ms_mem ms) md (x_k cx) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_o cx <= a < x_o cx + 24) -> ~ (cS1 cx - ESTACK <= a < cS1 cx) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a) ->
(forall i, 0 <= i < 24 -> aview SEGS (w_H W3) (ms_mem ms) (x_o cx + i) =
  Some (nth (Z.to_nat i) (cls_bytes (cls_O_ROLE (x_FB cx))) 0)) ->
(forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a) ->
SRr SEGS W3 (mkCfg ms md) (cls_Q B cx).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 E ss ms md extra HROLE HPRE HAT HS Hpc Hrv HAE Hkb R11 R21 R23 R24 HJ HK HO HP.
rewrite (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv). rewrite Hpc.
apply (sw_close cx fpos W3 ly3 S3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) md HROLE HPRE HAT HJ HK HO HP).
- intros r Hr. exact (regs_kept_of_st_ok_pi E ss (restrict (w_H W3) ms) regs3 extra SW_KEPT HS HAE Hkb r Hr).
- rewrite (st_ok_pi_restrict_reg (w_H W3) E ss ms 11%bv HS). exact R11.
- rewrite (st_ok_pi_restrict_reg (w_H W3) E ss ms 21%bv HS). exact R21.
- rewrite (st_ok_pi_restrict_reg (w_H W3) E ss ms 23%bv HS). exact R23.
- rewrite (st_ok_pi_restrict_reg (w_H W3) E ss ms 24%bv HS). exact R24.
Qed.




#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Theorem cls_sw : cls_from_ROLE B -> cls_from_SW B.
Proof.
intros HROLE. unfold cls_from_SW, cls_from.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 HPRE HAT.
pose proof HAT as HAT0.
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 HPRE (proj2 HAT)) as HN.
destruct HAT as [Hret HCUT].
pose proof HPRE as HPRE0.
unfold cls_pre in HPRE0. cbv zeta in HPRE0.
destruct HPRE0 as (HJ0 & HROD & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & H14 & Hch & Hsp16 & Hstk & Hsp0 &
  Htop & Hdep & Hlen & HFBl & HUl & HOBl & Hf50 & Hur & Hus & Hug & Ho0 & Ho4 & Hor & Hog & How & Hoff & HL &
  Hdou & Hdof & HdL).
pose proof HCUT as HCUT0.
unfold cls_cut in HCUT0. cbv zeta in HCUT0.
destruct HCUT0 as (HJ & Hfr & Hnin & Hperm & Hfa & Hfl & Hkept & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R27 &
  HRV & Hspill & Mo & Mf & MF & MLS & HSHPl & HSHP & MFL & HPS & HO3l & HO3 & HL3).
cbv zeta in HN.
destruct HN as ((HF4096 & HFceil & HF32 & HFz & HFapp & HFpres & HFSpres & HFL4096 & HFLz & HFLc & HFLp & HFLo &
  HFLn & HFb & HFf) & _ & _ & _ & (Hoa & Hol & HoF & HoS) & Ho4096 & Hoc & Hoawr & HNL).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hastk & _ & _).
pose proof Hastk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
assert (HCS : CLS_STK = 8512) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
set (fq := x_fq cx) in *.
set (SP := cSP cx) in *. set (S1 := cS1 cx) in *. set (F := cF cx fpos) in *. set (o := x_o cx) in *.
set (len := x_len cx) in *. set (FB := x_FB cx) in *.
change (spZ (x_regs cx)) with SP in *.
assert (HS1 : SP - 192 < S1 <= SP - 160 /\ S1 mod 32 = 0).
{ subst S1. unfold cS1, cls_S1. fold SP. pose proof (Z.mod_pos_bound (SP - 160) 32 ltac:(lia)).
  pose proof (Z.div_mod (SP - 160) 32 ltac:(lia)). split; [lia|]. rewrite Z.mul_comm. apply Z.mod_mul; lia. }
assert (HSP : alloc_ceiling + CLS_STK <= SP <= 2 ^ 47) by lia.
destruct Hoa as (Ho0' & Ho47 & Hoamr & Hooff & Hoband).
clear Hoband Hoff Hdou Hdof HdL HL.
change (sw_lock (o + 24 <= F \/ F + 256 <= o)) in HoF. change (sw_lock (SP <= o \/ o + 24 <= SP - CLS_STK)) in HoS.
rewrite !Forall_cons_iff in HRV. cbn [fst snd] in HRV. destruct HRV as (V21 & V22 & V25 & _).
change (getr regs3 21 = w64 SHADOW_OFF) in V21. change (getr regs3 22 = w64 (F + 32)) in V22.
change (getr regs3 25 = w64 (F + 36)) in V25.
assert (Hk0 : fst (RcParse.ctrlparse len FB) <> 0) by exact (sw_ret0 _ _ _ _ Hret).
pose proof (RcParse.ctrlparse_kind_range len FB) as Hkr.
destruct (sw_ps len FB Hk0) as (P0 & P1 & P2 & P3 & P16 & P17 & P18 & P19 & P26 & Psrc & P5).
destruct HPS as (HPSl & HPSg). unfold cPS in HPSl, HPSg. fold len FB in HPSl, HPSg.
set (PB := cls_bytes (snd (RcParse.ctrlparse len FB))) in *.
assert (HPBl : length PB = 36%nat) by (subst PB; unfold cls_bytes; rewrite length_map; exact HPSl).
set (kv := fst (RcParse.ctrlparse len FB)) in *.
set (bc := nth 16 PB 0). set (fb := nth 26 PB 0). set (tg := nth 28 PB 0 + 256 * nth 29 PB 0).
pose proof (fun j a' Hj Ha => sw_gb _ _ _ HPSg j a' ltac:(rewrite HPBl; exact Hj) Ha) as GB.
assert (Mk : val_mem SEGS (mrestrict (w_H W3) mem3) (F + 32) 4 kv).
{ destruct (GB 0%nat (F + 32) ltac:(lia) ltac:(lia)) as [G0 _]. rewrite P0 in G0.
  destruct (GB 1%nat (F + 32 + 1) ltac:(lia) ltac:(lia)) as [G1 _]. rewrite P1 in G1.
  destruct (GB 2%nat (F + 32 + 2) ltac:(lia) ltac:(lia)) as [G2 _]. rewrite P2 in G2.
  destruct (GB 3%nat (F + 32 + 3) ltac:(lia) ltac:(lia)) as [G3 _]. rewrite P3 in G3.
  apply sw_vm4z; [exact G0 | exact G1 | exact G2 | exact G3 | lia]. }
assert (Mbc : val_mem SEGS (mrestrict (w_H W3) mem3) (F + 48) 4 bc).
{ destruct (GB 16%nat (F + 48) ltac:(lia) ltac:(lia)) as [G0 R0].
  destruct (GB 17%nat (F + 48 + 1) ltac:(lia) ltac:(lia)) as [G1 _]. rewrite P17 in G1.
  destruct (GB 18%nat (F + 48 + 2) ltac:(lia) ltac:(lia)) as [G2 _]. rewrite P18 in G2.
  destruct (GB 19%nat (F + 48 + 3) ltac:(lia) ltac:(lia)) as [G3 _]. rewrite P19 in G3.
  apply sw_vm4z; [exact G0 | exact G1 | exact G2 | exact G3 | exact R0]. }
assert (Mfb : val_mem SEGS (mrestrict (w_H W3) mem3) (F + 58) 1 fb /\ 0 <= fb < 256)
  by exact (GB 26%nat (F + 58) ltac:(lia) ltac:(lia)).
destruct Mfb as [Mfb Rfb].
assert (Mtg : val_mem SEGS (mrestrict (w_H W3) mem3) (F + 60) 2 tg /\ 0 <= tg < 2 ^ 16).
{ destruct (GB 28%nat (F + 60) ltac:(lia) ltac:(lia)) as [G0 R0].
  destruct (GB 29%nat (F + 60 + 1) ltac:(lia) ltac:(lia)) as [G1 R1].
  split; [apply sw_vm2; assumption | subst tg; lia]. }
destruct Mtg as [Mtg Rtg].
assert (Rbc : 0 <= bc < 256) by (subst bc; rewrite P16; destruct (RcParse.cp_bcast FB); lia).
assert (Rlen : 0 <= len < 2 ^ 64) by exact Hlen.
assert (Ro : 0 <= o < 2 ^ 64) by lia.
assert (Rk : 0 <= kv <= 13) by exact Hkr.
destruct (sw_entry fq W3 mem3 regs3 S1 F len o kv bc fb tg R9 V22 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) Rlen Ro Rk Rbc Rfb Rtg (MLS eq_refl) Mo Mk Mbc Mfb Mtg) as [HS SHOK].
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
destruct (sw_ew regs3 len o kv bc fb tg) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & ETB & ER).
remember (SWE regs3 len o kv bc fb tg) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold SWE; apply Eimg_env).
unfold cfg_at. change (w64 (BASE + PC_SW)) with (Z_to_bv 64 (BASE + PC_SW)).
paj_run_tok RUN HS HJ SHOK SWspan; [awr_ok_tac|].
assert (EM : ms_mem ms = mem3).
{ extensionality x. apply HF. intros (r & Hin & Hr). unfold ss_sw in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [sw_loc_region sw_q_region YP09.r_wlo YP09.r_whi] in Hr; lia. }
clear HF HFr HG.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp2.
prreg HS (3%bv : bv 5) Rgp2. prreg HS (4%bv : bv 5) Rtp2.
rewrite EM in HJ.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA DS___asan_memset) (AMEMSET fq) W3 rT mT
   (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) ((2, fpos) :: x_own cx) ly3 S3 dT (x_k cx)
   (o + 6) 0 18 (S1 - x_sp0 cx) _ ltac:(rewrite EM; exact HJ)) | ] end.
- rewrite Ra0, E34, unsigned_lit_small by lia. reflexivity.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- lia.
- lia.
- lia.
- unfold spZ. rewrite Rsp2, (ER 2%nat 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
- apply Z.mod_divide; [lia|].
  destruct (proj1 (Z.mod_divide S1 32 ltac:(lia)) (proj2 HS1)) as [a1 Ha1].
  destruct (proj1 (Z.mod_divide (x_sp0 cx) 16 ltac:(lia)) Hsp0al) as [b1 Hb1]. exists (2 * a1 - b1). lia.
- lia.
- lia.
- rewrite Rgp2, (ER 3%nat 3%bv eq_refl), R3. exact Hgp.
- rewrite Rtp2, (ER 4%nat 4%bv eq_refl), R4. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [apply Hoawr; lia | unfold sw_lock in HoS; lia].
- unfold amem_range in *. lia.
- rewrite EM. intros x Hx. apply (proj1 (proj2 Hol)). lia.
- rewrite EM. intros _ s Hs. apply (proj2 (proj2 Hol)).
  assert (M1 : shadow_addr o / 8 <= shadow_addr (o + 6) / 8) by (apply Z.div_le_mono; [lia | apply shadow_mono; lia]).
  replace (o + 24 - 1) with (o + 6 + 18 - 1) by lia. lia.
- exact I.
- cbv beta. intros W2 c2 _ Hpost.
  destruct Hpost as (HW2 & regs4 & mem4 & md4 & Hc2 & HJ4 & HP4 & Ha04 & Heff4 & Hfr4 & Hpres4).
  subst W2 c2. rewrite EM in Hfr4, Hpres4.
  jafter_call_keep_pi HS 48%nat regs4 (mrestrict (w_H W3) mem4) HP4 [0; 1]%nat HSX.
  lazymatch type of HSX with ?T -> _ => assert (HRK : T) end.
  { cbn [ms_mem restrict]. rewrite EM. repeat apply Forall_cons; try apply Forall_nil.
    - eapply region_kept_aview; [rewrite (ER 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia
        | intros a Ha; apply Hfr4; lia | exact Hpres4].
    - eapply region_kept_aview; [rewrite (ER 22%nat 22%bv eq_refl), V22; unfold w64; apply unsigned_lit_small; lia
        | intros a Ha; apply Hfr4; unfold sw_lock in HoF; clear - Ha HoF HFceil HSP HS1 HCS HES C1 HF4096; lia | exact Hpres4]. }
  specialize (HSX HRK). clear HRK. rewrite <- restrict_mkst_fx in HSX.
  assert (HEI4 : img_env VAL A_LIM (havoc E 48 (map (getr regs4) CLOB))) by (apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (SHOK4 : sh_ok SEGS SW_Bx SW_SH (havoc E 48 (map (getr regs4) CLOB)) (mrestrict (w_H W3) mem4))
    by (unfold sh_ok, SW_SH; apply Forall_nil).
  remember (havoc E 48 (map (getr regs4) CLOB)) as E4 eqn:HE4.
  assert (AG4 : forall n, (n < 48)%nat -> ew E4 n = ew E n) by (intros n Hn; subst E4; apply ew_havoc_old; lia).
  clear HS SHOK.
  paj_run_tok RUN HSX HJ4 SHOK4 SWspan; [awr_ok_tac|].
  assert (EM4 : ms_mem ms0 = mem4).
  { extensionality x. apply HF. intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
    destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_wlo YP09.r_whi] in Hr; lia. }
  clear HF HFr HG.
  pmkst HSX.
  prreg HSX (10%bv : bv 5) Rb0. prreg HSX (11%bv : bv 5) Rb1. prreg HSX (12%bv : bv 5) Rb2.
  prreg HSX (1%bv : bv 5) Rrb. prreg HSX (2%bv : bv 5) Rspb.
  prreg HSX (3%bv : bv 5) Rgpb. prreg HSX (4%bv : bv 5) Rtpb.
  assert (HspT : spZ (ms_regs ms0) = S1).
  { unfold spZ. rewrite Rspb, AG4 by lia. rewrite (ER 2%nat 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
  assert (SZ4 : forall s, SHADOW_OFF <= s < kHighMemBeg -> aview SEGS (w_H W3) mem4 s = aview SEGS (w_H W3) mem3 s).
  { intros s Hs. apply Hfr4; unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF in *; lia. }
  destruct (sw_fsrc (w_H W3) mem3 F ltac:(lia) HF32 HSHP HFSpres) as [FRA FHV].
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply SRr_bind;
  [ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA DS___asan_memcpy) (AMEMCPY fq) W3 rT mT
     (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) ((2, fpos) :: x_own cx) ly3 S3 dT (x_k cx)
     o (F + 36) 6 (S1 - x_sp0 cx) _ HJ4) | ] end.
  + rewrite Rb0, AG4, E34 by lia. reflexivity.
  + rewrite Rb1, AG4 by lia. rewrite (ER 25%nat 25%bv eq_refl), V25. reflexivity.
  + rewrite Rb2. reflexivity.
  + lia.
  + lia.
  + lia.
  + rewrite HspT. lia.
  + apply Z.mod_divide; [lia|].
    destruct (proj1 (Z.mod_divide S1 32 ltac:(lia)) (proj2 HS1)) as [a1 Ha1].
    destruct (proj1 (Z.mod_divide (x_sp0 cx) 16 ltac:(lia)) Hsp0al) as [b1 Hb1]. exists (2 * a1 - b1). lia.
  + lia.
  + lia.
  + rewrite Rgpb, AG4 by lia. rewrite (ER 3%nat 3%bv eq_refl), R3. exact Hgp.
  + rewrite Rtpb, AG4 by lia. rewrite (ER 4%nat 4%bv eq_refl), R4. exact Htp.
  + exact Rrb.
  + apply ret_ok_codeptr_v; [lia | reflexivity].
  + intros a Ha. split; [apply Hoawr; lia | unfold sw_lock in HoS; lia].
  + unfold amem_range in *. lia.
  + rewrite EM4. apply (sw_ra_tr (aview SEGS (w_H W3) mem3)); [exact SZ4 | lia | lia |].
    apply (sw_ra_sub _ _ o 24); [exact (proj1 (proj2 Hol)) | lia | lia].
  + intros _. rewrite EM4. apply (sw_hull_tr (aview SEGS (w_H W3) mem3)); [exact SZ4 | lia | lia | unfold amem_range, kHighMemEnd, kLowMemEnd in Hoamr; lia |].
    apply (sw_hull_sub _ o 24); [exact (proj2 (proj2 Hol)) | lia | lia].
  + unfold sw_lock in HoF. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [rewrite EM4; apply sw_aview_pres; apply Hpres4; apply HFpres; lia | rewrite HspT; lia]. }
    split; [lia|]. split; [unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia|].
    split; [rewrite EM4; apply (sw_ra_tr (aview SEGS (w_H W3) mem3)); [exact SZ4 | lia | lia | exact FRA]|].
    intros _. rewrite EM4. apply (sw_hull_tr (aview SEGS (w_H W3) mem3)); [exact SZ4 | lia | lia | lia | exact FHV].
  + cbv beta. intros W2 c2 _ Hpost.
    destruct Hpost as (HW2 & regs5 & mem5 & md5 & Hc2 & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5).
    subst W2 c2. rewrite EM4 in Hfr5, Heff5, Hpres5.
    assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 24) -> ~ (S1 - ESTACK <= a < S1) ->
      aview SEGS (w_H W3) mem5 a = aview SEGS (w_H W3) mem3 a).
    { intros a Ha Hn1 Hn2. rewrite Hfr5 by lia. apply Hfr4; lia. }
    assert (O5 : forall i, 0 <= i < 24 -> aview SEGS (w_H W3) mem5 (o + i) =
      Some (nth (Z.to_nat i) (cls_bytes (cls_O_ROLE FB)) 0)).
    { intros i Hi. unfold sw_lock in HoF. rewrite sw_orole by exact HFBl. destruct (Z.ltb_spec i 6) as [Hi6|Hi6].
      - replace (Z.to_nat i <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite Heff5 by lia. rewrite Hfr4 by lia.
        destruct (GB (4 + Z.to_nat i)%nat (F + 36 + i) ltac:(lia) ltac:(lia)) as [Gv Gr].
        rewrite (sw_aview_of_vm1 _ _ _ _ Gv Gr). rewrite Psrc by lia. reflexivity.
      - replace (Z.to_nat i <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
        rewrite Hfr5 by lia. replace (o + i) with (o + 6 + (i - 6)) by lia. rewrite Heff4 by lia. reflexivity. }
    assert (PR5 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem5 a)
      by (intros a Ha; apply Hpres5; apply Hpres4; exact Ha).
    jafter_call_keep_pi HSX 64%nat regs5 (mrestrict (w_H W3) mem5) HP5 [0; 1]%nat HSY.
    lazymatch type of HSY with ?T -> _ => assert (HRK : T) end.
    { cbn [ms_mem restrict]. rewrite EM4. repeat apply Forall_cons; try apply Forall_nil.
      - eapply region_kept_aview; [rewrite AG4 by lia; rewrite (ER 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia
          | intros a Ha; apply Hfr5; lia | exact Hpres5].
      - eapply region_kept_aview; [rewrite AG4 by lia; rewrite (ER 22%nat 22%bv eq_refl), V22; unfold w64; apply unsigned_lit_small; lia
          | intros a Ha; apply Hfr5; unfold sw_lock in HoF; clear - Ha HoF HFceil HSP HS1 HCS HES C1 HF4096; lia | exact Hpres5]. }
    specialize (HSY HRK). clear HRK. rewrite <- restrict_mkst_fx in HSY.
    assert (HEI5 : img_env VAL A_LIM (havoc E4 64 (map (getr regs5) CLOB))) by (apply img_env_havoc; [exact HEI4 | cbv; lia]).
    remember (havoc E4 64 (map (getr regs5) CLOB)) as E5 eqn:HE5.
    assert (AG5 : forall n, (n < 48)%nat -> ew E5 n = ew E n)
      by (intros n Hn; subst E5; rewrite ew_havoc_old by lia; apply AG4; exact Hn).
    assert (ARO5 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem5)).
    { intros a Hro Hown Herr.
      assert (Himg : in_img SEGS a).
      { destruct Hro as [(sg & Hsg & _ & Hr) | Hrel]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hrel)]. }
      pose proof (pa_img_range a Himg) as HIR. pose proof (Hsegs a Himg) as HIL.
      rewrite K5 by (clear - HIR HIL Hooff HS1 HSP HES HCS C1 C5; unfold off_img, IMG_LO, IMG_TOP, kLowMemEnd in *; lia).
      destruct Hkept as (_ & _ & Kimg & _). rewrite (Kimg a Himg Hown Herr). exact (HROD a Hro Hown Herr). }
    destruct (ROM (w_H W3) mem5 ARO5) as [_ TAB].
    pose proof (pa_obj_img 35%nat ltac:(unfold disco_nobj; lia)) as HOB35. unfold IMG_LO, IMG_TOP in HOB35.
    pose proof (pa_val_range (A_OBJ 35)) as HV35.
    assert (B35 : base_val E5 (Some (A_OBJ 35)) = VAL (A_OBJ 35))
      by (cbn [base_val]; exact (HEI5 (A_OBJ 35) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
    assert (B9 : base_val E5 (Some 9%nat) = S1)
      by (cbn [base_val]; rewrite AG5 by lia; rewrite (ER 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
    assert (B22 : base_val E5 (Some 22%nat) = F + 32)
      by (cbn [base_val]; rewrite AG5 by lia; rewrite (ER 22%nat 22%bv eq_refl), V22; unfold w64; apply unsigned_lit_small; lia).
    assert (HFo : F + 256 <= IMG_LO \/ IMG_TOP <= F) by exact (proj1 HFz).
    apply st_ok_pi_add_region with (r := sw_tab_region) in HSY.
    2: { vm_compute. reflexivity. }
    2: { unfold sw_tab_region, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
         rewrite B35. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|].
         apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
         apply (chunk_ok_val SEGS E5 _ (VAL (A_OBJ 35)) (4 * Z.of_nat i) 4 (SOff (39 + i) 0) (sw_tab i)).
         - cbn [sv_denot]. rewrite AG5 by lia. rewrite ETB by lia. rewrite unsigned_lit_small.
           + rewrite Z.add_0_r. reflexivity.
           + unfold sw_tab. pose proof (Z.mod_pos_bound (BASE + AF_classify_core + nth i CLS_SW_ARMS 0 - VAL (A_OBJ 35)) (2 ^ 32) ltac:(lia)). lia.
         - unfold sw_tab. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). apply Z.mod_pos_bound. lia.
         - cbn. lia.
         - exact (TAB i ltac:(lia)). }
    2: { apply all_disjoint_of_extents. unfold sw_tab_region, extent_of_region. cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi].
         rewrite B35, B9, B22. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
         clear - HOB35 HFo HS1 HSP C1 HCS. unfold IMG_LO, IMG_TOP in HFo. repeat split; lia. }
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSY.
    assert (SHOK5 : sh_ok SEGS SW_Bx SW_SH E5 (mrestrict (w_H W3) mem5)) by (unfold sh_ok, SW_SH; apply Forall_nil).
    clear HSX SHOK4.
    paj_run_tok RUN HSY HJ5 SHOK5 SWspan; [awr_ok_tac|].
    apply sw_frame_ro in HF; [rename HF into EM5 | vm_compute; reflexivity]. clear HFr HG.
    assert (HAE5 : env_agree 32 (Ereg regs3 (sw_extra len o kv bc fb tg)) E5).
    { split.
      - intros n Hn. rewrite AG5 by lia. rewrite HE. unfold SWE. apply Eimg_low. unfold A_TEXT. lia.
      - rewrite HE5, HE4, HE. reflexivity. }
    assert (D21 : sv_denot E5 (SOff 33 0) = w64 len).
    { cbn [sv_denot]. rewrite AG5, E33 by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
    assert (D23 : sv_denot E5 (SOff 21 0) = w64 SHADOW_OFF).
    { cbn [sv_denot]. rewrite AG5 by lia. rewrite (ER 21%nat 21%bv eq_refl), V21. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
    assert (D24 : sv_denot E5 (SOff 34 0) = w64 o).
    { cbn [sv_denot]. rewrite AG5, E34 by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
    psrr_branch_tok RUN BR HSY SHOK5 SWspan.
    * rewrite branch_ltu_U, U_SLit, U_SOff in Hc. rewrite AG5, E35 in Hc by lia. rewrite unsigned_lit_small in Hc by lia.
      apply Z.ltb_lt in Hc. unfold zcanon, M64 in Hc.
      assert (Hk10 : 10 <= kv) by (rewrite (Z.mod_small 8) in Hc by lia; rewrite Z.mod_small in Hc by lia; lia).
      paj_run_to_tok RUNTO HSY HJ5 SHOK5 SWspan PC_ROLE; [awr_ok_tac|].
      apply sw_frame_ro in HF; [rename HF into EM6 | vm_compute; reflexivity]. clear HFr HG.
      apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HSY eq_refl eq_refl HAE5
        ltac:(vm_compute; reflexivity)).
      -- sw_srg. change (cK cx) with kv. rewrite sw_role_hi by lia. reflexivity.
      -- sw_srg. exact D21.
      -- sw_srg. exact D23.
      -- sw_srg. exact D24.
      -- exact HJ5.
      -- rewrite EM6, EM5. exact K5.
      -- rewrite EM6, EM5. exact O5.
      -- rewrite EM6, EM5. exact PR5.
    * rewrite branch_ltu_U, U_SLit, U_SOff in Hc. rewrite AG5, E35 in Hc by lia. rewrite unsigned_lit_small in Hc by lia.
      apply Z.ltb_ge in Hc. unfold zcanon, M64 in Hc.
      assert (Hk9 : 1 <= kv <= 9) by (rewrite (Z.mod_small 8) in Hc by lia; rewrite Z.mod_small in Hc by lia; lia).
      prreg HSY (10%bv : bv 5) Ra0k. rewrite AG5, E35 in Ra0k by lia. rewrite unsigned_lit_small in Ra0k by lia.

      assert (EV35 : ew E5 (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35))).
      { rewrite <- (HEI5 (A_OBJ 35) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). symmetry. apply Z_to_bv_bv_unsigned. }
      assert (KC : kv = 1 \/ kv = 2 \/ kv = 3 \/ kv = 4 \/ kv = 5 \/ kv = 6 \/ kv = 7 \/ kv = 8 \/ kv = 9) by lia.
      destruct KC as [Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|Hk]]]]]]]].
      ++ apply (st_ok_pi_pin_reg' _ _ _ 10%bv 0) in HSY; [| refine (eq_trans Ra0k _); rewrite Hk; reflexivity | reflexivity].
        paj_run_tok RUN HSY HJ5 SHOK5 SWspan; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM6 | vm_compute; reflexivity]. clear HFr HG.
        prreg HSY (10%bv : bv 5) Rj.
        rewrite (AG5 39%nat ltac:(lia)), (ETB 0%nat ltac:(lia) : ew E 39 = _), (EV35 : ew E5 276 = _) in Rj.
        unfold sw_tab in Rj.
        rewrite sw_jr_val in Rj by (pose proof (sw_slot_img' (AF_classify_core + nth 0 CLS_SW_ARMS 0)
          ltac:(unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia) ltac:(vm_compute; reflexivity)); unfold IMG_LO, IMG_TOP in *; lia).
        rewrite <- Z.add_assoc in Rj.
        lazymatch type of HSY with st_ok_pi _ _ _ ?ssj _ =>
          let wj := eval vm_compute in (match plookup pl_tpi (ss_pc ssj) with Some (PW w) => w | _ => 0 end) in
          eapply (SRr_jr_pi W3 E5 _ _ _ _ wj 10%bv (BASE + (AF_classify_core + nth 0 CLS_SW_ARMS 0)) HSY eq_refl) end;
          [vm_compute; reflexivity | vm_refl_bv | exact Rj
          | pose proof pa_B_ok; unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia
          | apply sw_even; reflexivity | ].
        intros mat' ms3 Hms3 HS3.
        lazymatch type of HS3 with st_ok ?sg ?Ee (mkSST (BASE + ?t) ?R ?Fr ?M ?Rv ?G) ?X =>
          change (st_ok_pi sg VAL Ee (mkSST t R Fr M Rv G) X) in HS3 end.
        pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ5) as HJ6.
        assert (EM7 : ms_mem ms3 = ms_mem ms2) by (subst ms3; reflexivity). rewrite <- EM7 in HJ6.
        assert (SHOK6 : sh_ok SEGS SW_Bx SW_SH E5 (mrestrict (w_H W3) (ms_mem ms3))) by (unfold sh_ok, SW_SH; apply Forall_nil).
        clear HSY SHOK5.
        paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM8 | vm_compute; reflexivity]. clear HFr HG.
        apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
          ltac:(vm_compute; reflexivity)).
        -- sw_srg. change (cK cx) with kv. rewrite Hk. cbn [sv_denot]. rewrite AG5, E36 by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
           change (x_FB cx) with FB. change (disco_classify_c.role FB 1) with (if RcParse.cp_bcast FB then 0 else 1).
           change bc with (nth 16 PB 0). rewrite P16. destruct (RcParse.cp_bcast FB); vm_refl_bv.

        -- sw_srg. exact D21.
        -- sw_srg. exact D23.
        -- sw_srg. exact D24.
        -- exact HJ6.
        -- rewrite EM8, EM7, EM6, EM5. exact K5.
        -- rewrite EM8, EM7, EM6, EM5. exact O5.
        -- rewrite EM8, EM7, EM6, EM5. exact PR5.
      ++ apply (st_ok_pi_pin_reg' _ _ _ 10%bv 1) in HSY; [| refine (eq_trans Ra0k _); rewrite Hk; reflexivity | reflexivity].
        paj_run_tok RUN HSY HJ5 SHOK5 SWspan; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM6 | vm_compute; reflexivity]. clear HFr HG.
        prreg HSY (10%bv : bv 5) Rj.
        rewrite (AG5 40%nat ltac:(lia)), (ETB 1%nat ltac:(lia) : ew E 40 = _), (EV35 : ew E5 276 = _) in Rj.
        unfold sw_tab in Rj.
        rewrite sw_jr_val in Rj by (pose proof (sw_slot_img' (AF_classify_core + nth 1 CLS_SW_ARMS 0)
          ltac:(unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia) ltac:(vm_compute; reflexivity)); unfold IMG_LO, IMG_TOP in *; lia).
        rewrite <- Z.add_assoc in Rj.
        lazymatch type of HSY with st_ok_pi _ _ _ ?ssj _ =>
          let wj := eval vm_compute in (match plookup pl_tpi (ss_pc ssj) with Some (PW w) => w | _ => 0 end) in
          eapply (SRr_jr_pi W3 E5 _ _ _ _ wj 10%bv (BASE + (AF_classify_core + nth 1 CLS_SW_ARMS 0)) HSY eq_refl) end;
          [vm_compute; reflexivity | vm_refl_bv | exact Rj
          | pose proof pa_B_ok; unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia
          | apply sw_even; reflexivity | ].
        intros mat' ms3 Hms3 HS3.
        lazymatch type of HS3 with st_ok ?sg ?Ee (mkSST (BASE + ?t) ?R ?Fr ?M ?Rv ?G) ?X =>
          change (st_ok_pi sg VAL Ee (mkSST t R Fr M Rv G) X) in HS3 end.
        pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ5) as HJ6.
        assert (EM7 : ms_mem ms3 = ms_mem ms2) by (subst ms3; reflexivity). rewrite <- EM7 in HJ6.
        apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
          ltac:(vm_compute; reflexivity)).
        -- sw_srg. change (cK cx) with kv. rewrite Hk. reflexivity.

        -- sw_srg. exact D21.
        -- sw_srg. exact D23.
        -- sw_srg. exact D24.
        -- exact HJ6.
        -- rewrite EM7, EM6, EM5. exact K5.
        -- rewrite EM7, EM6, EM5. exact O5.
        -- rewrite EM7, EM6, EM5. exact PR5.
      ++ apply (st_ok_pi_pin_reg' _ _ _ 10%bv 2) in HSY; [| refine (eq_trans Ra0k _); rewrite Hk; reflexivity | reflexivity].
        paj_run_tok RUN HSY HJ5 SHOK5 SWspan; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM6 | vm_compute; reflexivity]. clear HFr HG.
        prreg HSY (10%bv : bv 5) Rj.
        rewrite (AG5 41%nat ltac:(lia)), (ETB 2%nat ltac:(lia) : ew E 41 = _), (EV35 : ew E5 276 = _) in Rj.
        unfold sw_tab in Rj.
        rewrite sw_jr_val in Rj by (pose proof (sw_slot_img' (AF_classify_core + nth 2 CLS_SW_ARMS 0)
          ltac:(unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia) ltac:(vm_compute; reflexivity)); unfold IMG_LO, IMG_TOP in *; lia).
        rewrite <- Z.add_assoc in Rj.
        lazymatch type of HSY with st_ok_pi _ _ _ ?ssj _ =>
          let wj := eval vm_compute in (match plookup pl_tpi (ss_pc ssj) with Some (PW w) => w | _ => 0 end) in
          eapply (SRr_jr_pi W3 E5 _ _ _ _ wj 10%bv (BASE + (AF_classify_core + nth 2 CLS_SW_ARMS 0)) HSY eq_refl) end;
          [vm_compute; reflexivity | vm_refl_bv | exact Rj
          | pose proof pa_B_ok; unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia
          | apply sw_even; reflexivity | ].
        intros mat' ms3 Hms3 HS3.
        lazymatch type of HS3 with st_ok ?sg ?Ee (mkSST (BASE + ?t) ?R ?Fr ?M ?Rv ?G) ?X =>
          change (st_ok_pi sg VAL Ee (mkSST t R Fr M Rv G) X) in HS3 end.
        pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ5) as HJ6.
        assert (EM7 : ms_mem ms3 = ms_mem ms2) by (subst ms3; reflexivity). rewrite <- EM7 in HJ6.
        apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
          ltac:(vm_compute; reflexivity)).
        -- sw_srg. change (cK cx) with kv. rewrite Hk. reflexivity.

        -- sw_srg. exact D21.
        -- sw_srg. exact D23.
        -- sw_srg. exact D24.
        -- exact HJ6.
        -- rewrite EM7, EM6, EM5. exact K5.
        -- rewrite EM7, EM6, EM5. exact O5.
        -- rewrite EM7, EM6, EM5. exact PR5.
      ++ apply (st_ok_pi_pin_reg' _ _ _ 10%bv 3) in HSY; [| refine (eq_trans Ra0k _); rewrite Hk; reflexivity | reflexivity].
        paj_run_tok RUN HSY HJ5 SHOK5 SWspan; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM6 | vm_compute; reflexivity]. clear HFr HG.
        prreg HSY (10%bv : bv 5) Rj.
        rewrite (AG5 42%nat ltac:(lia)), (ETB 3%nat ltac:(lia) : ew E 42 = _), (EV35 : ew E5 276 = _) in Rj.
        unfold sw_tab in Rj.
        rewrite sw_jr_val in Rj by (pose proof (sw_slot_img' (AF_classify_core + nth 3 CLS_SW_ARMS 0)
          ltac:(unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia) ltac:(vm_compute; reflexivity)); unfold IMG_LO, IMG_TOP in *; lia).
        rewrite <- Z.add_assoc in Rj.
        lazymatch type of HSY with st_ok_pi _ _ _ ?ssj _ =>
          let wj := eval vm_compute in (match plookup pl_tpi (ss_pc ssj) with Some (PW w) => w | _ => 0 end) in
          eapply (SRr_jr_pi W3 E5 _ _ _ _ wj 10%bv (BASE + (AF_classify_core + nth 3 CLS_SW_ARMS 0)) HSY eq_refl) end;
          [vm_compute; reflexivity | vm_refl_bv | exact Rj
          | pose proof pa_B_ok; unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia
          | apply sw_even; reflexivity | ].
        intros mat' ms3 Hms3 HS3.
        lazymatch type of HS3 with st_ok ?sg ?Ee (mkSST (BASE + ?t) ?R ?Fr ?M ?Rv ?G) ?X =>
          change (st_ok_pi sg VAL Ee (mkSST t R Fr M Rv G) X) in HS3 end.
        pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ5) as HJ6.
        assert (EM7 : ms_mem ms3 = ms_mem ms2) by (subst ms3; reflexivity). rewrite <- EM7 in HJ6.
        apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
          ltac:(vm_compute; reflexivity)).
        -- sw_srg. change (cK cx) with kv. rewrite Hk. reflexivity.

        -- sw_srg. exact D21.
        -- sw_srg. exact D23.
        -- sw_srg. exact D24.
        -- exact HJ6.
        -- rewrite EM7, EM6, EM5. exact K5.
        -- rewrite EM7, EM6, EM5. exact O5.
        -- rewrite EM7, EM6, EM5. exact PR5.
      ++ apply (st_ok_pi_pin_reg' _ _ _ 10%bv 4) in HSY; [| refine (eq_trans Ra0k _); rewrite Hk; reflexivity | reflexivity].
        paj_run_tok RUN HSY HJ5 SHOK5 SWspan; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM6 | vm_compute; reflexivity]. clear HFr HG.
        prreg HSY (10%bv : bv 5) Rj.
        rewrite (AG5 43%nat ltac:(lia)), (ETB 4%nat ltac:(lia) : ew E 43 = _), (EV35 : ew E5 276 = _) in Rj.
        unfold sw_tab in Rj.
        rewrite sw_jr_val in Rj by (pose proof (sw_slot_img' (AF_classify_core + nth 4 CLS_SW_ARMS 0)
          ltac:(unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia) ltac:(vm_compute; reflexivity)); unfold IMG_LO, IMG_TOP in *; lia).
        rewrite <- Z.add_assoc in Rj.
        lazymatch type of HSY with st_ok_pi _ _ _ ?ssj _ =>
          let wj := eval vm_compute in (match plookup pl_tpi (ss_pc ssj) with Some (PW w) => w | _ => 0 end) in
          eapply (SRr_jr_pi W3 E5 _ _ _ _ wj 10%bv (BASE + (AF_classify_core + nth 4 CLS_SW_ARMS 0)) HSY eq_refl) end;
          [vm_compute; reflexivity | vm_refl_bv | exact Rj
          | pose proof pa_B_ok; unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia
          | apply sw_even; reflexivity | ].
        intros mat' ms3 Hms3 HS3.
        lazymatch type of HS3 with st_ok ?sg ?Ee (mkSST (BASE + ?t) ?R ?Fr ?M ?Rv ?G) ?X =>
          change (st_ok_pi sg VAL Ee (mkSST t R Fr M Rv G) X) in HS3 end.
        pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ5) as HJ6.
        assert (EM7 : ms_mem ms3 = ms_mem ms2) by (subst ms3; reflexivity). rewrite <- EM7 in HJ6.
        assert (SHOK6 : sh_ok SEGS SW_Bx SW_SH E5 (mrestrict (w_H W3) (ms_mem ms3))) by (unfold sh_ok, SW_SH; apply Forall_nil).
        clear HSY SHOK5.
        paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM8 | vm_compute; reflexivity]. clear HFr HG.
        destruct (P5 Hk) as (P28 & P29).
        assert (HTG : disco_classify_c.tag FB = tg).
        { unfold disco_classify_c.tag. change tg with (nth 28 PB 0 + 256 * nth 29 PB 0). rewrite P28, P29.
          change (CtrlParsed.fb FB 34) with (RcParse.cp_v FB 34). change (CtrlParsed.fb FB 35) with (RcParse.cp_v FB 35). lia. }
        assert (HFB22 : CtrlParsed.fb FB 22 = fb) by (change (CtrlParsed.fb FB 22) with (RcParse.cp_v FB 22); rewrite <- P26; reflexivity).
        psrr_branch_tok RUN BR HS3 SHOK6 SWspan.
        -- rewrite branch_eq_U, U_SOff, U_SLit in Hc0. rewrite (AG5 37%nat ltac:(lia)), E37 in Hc0.
            rewrite unsigned_lit_small in Hc0 by lia. unfold zcanon, M64 in Hc0. rewrite Z.add_0_r in Hc0.
            rewrite !Z.mod_small in Hc0 by lia. apply Z.eqb_eq in Hc0. change (0 mod 2 ^ 64) with 0 in Hc0.
            paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
            apply sw_frame_ro in HF; [|vm_compute; reflexivity]. rewrite EM8 in HF. clear EM8. rename HF into EM8. clear HFr HG.
            psrr_branch_tok RUN BR HS3 SHOK6 SWspan.
            --- rewrite branch_eq_U, U_SOff, U_SLit in Hc1. rewrite (AG5 38%nat ltac:(lia)), E38 in Hc1.
            rewrite unsigned_lit_small in Hc1 by lia. unfold zcanon, M64 in Hc1. rewrite Z.add_0_r in Hc1.
            rewrite !Z.mod_small in Hc1 by lia. apply Z.eqb_eq in Hc1.
            paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
            apply sw_frame_ro in HF; [|vm_compute; reflexivity]. rewrite EM8 in HF. clear EM8. rename HF into EM8. clear HFr HG.
            apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
              ltac:(vm_compute; reflexivity)).
            { sw_srg. change (cK cx) with kv. rewrite Hk. change (x_FB cx) with FB.
           change (disco_classify_c.role FB 5) with (if (CtrlParsed.fb FB 22 =? 0) && ((disco_classify_c.tag FB =? 256) ||
             (disco_classify_c.tag FB =? 770) || (disco_classify_c.tag FB =? 1280)) then 1 else 2).
           rewrite HFB22, HTG. replace (fb =? 0) with true by (symmetry; apply Z.eqb_eq; lia). replace (tg =? 256) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb orb]. reflexivity. }
            { sw_srg. exact D21. }
            { sw_srg. exact D23. }
            { sw_srg. exact D24. }
            { exact HJ6. }
            { rewrite EM8, EM7, EM6, EM5. exact K5. }
            { rewrite EM8, EM7, EM6, EM5. exact O5. }
            { rewrite EM8, EM7, EM6, EM5. exact PR5. }

            --- rewrite branch_eq_U, U_SOff, U_SLit in Hc1. rewrite (AG5 38%nat ltac:(lia)), E38 in Hc1.
            rewrite unsigned_lit_small in Hc1 by lia. unfold zcanon, M64 in Hc1. rewrite Z.add_0_r in Hc1.
            rewrite !Z.mod_small in Hc1 by lia. apply Z.eqb_neq in Hc1.
            paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
            apply sw_frame_ro in HF; [|vm_compute; reflexivity]. rewrite EM8 in HF. clear EM8. rename HF into EM8. clear HFr HG.
            psrr_branch_tok RUN BR HS3 SHOK6 SWspan.
            ---- rewrite branch_eq_U, U_SOff, U_SLit in Hc2. rewrite (AG5 38%nat ltac:(lia)), E38 in Hc2.
            rewrite unsigned_lit_small in Hc2 by lia. unfold zcanon, M64 in Hc2. rewrite Z.add_0_r in Hc2.
            rewrite !Z.mod_small in Hc2 by lia. apply Z.eqb_eq in Hc2.
            paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
            apply sw_frame_ro in HF; [|vm_compute; reflexivity]. rewrite EM8 in HF. clear EM8. rename HF into EM8. clear HFr HG.
            apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
              ltac:(vm_compute; reflexivity)).
            { sw_srg. change (cK cx) with kv. rewrite Hk. change (x_FB cx) with FB.
           change (disco_classify_c.role FB 5) with (if (CtrlParsed.fb FB 22 =? 0) && ((disco_classify_c.tag FB =? 256) ||
             (disco_classify_c.tag FB =? 770) || (disco_classify_c.tag FB =? 1280)) then 1 else 2).
           rewrite HFB22, HTG. replace (fb =? 0) with true by (symmetry; apply Z.eqb_eq; lia). replace (tg =? 256) with false by (symmetry; apply Z.eqb_neq; lia). replace (tg =? 770) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb orb]. reflexivity. }
            { sw_srg. exact D21. }
            { sw_srg. exact D23. }
            { sw_srg. exact D24. }
            { exact HJ6. }
            { rewrite EM8, EM7, EM6, EM5. exact K5. }
            { rewrite EM8, EM7, EM6, EM5. exact O5. }
            { rewrite EM8, EM7, EM6, EM5. exact PR5. }

            ---- rewrite branch_eq_U, U_SOff, U_SLit in Hc2. rewrite (AG5 38%nat ltac:(lia)), E38 in Hc2.
            rewrite unsigned_lit_small in Hc2 by lia. unfold zcanon, M64 in Hc2. rewrite Z.add_0_r in Hc2.
            rewrite !Z.mod_small in Hc2 by lia. apply Z.eqb_neq in Hc2.
            paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
            apply sw_frame_ro in HF; [|vm_compute; reflexivity]. rewrite EM8 in HF. clear EM8. rename HF into EM8. clear HFr HG.
            psrr_branch_tok RUN BR HS3 SHOK6 SWspan.
            ----- rewrite branch_eq_U, U_SOff, U_SLit in Hc3. rewrite (AG5 38%nat ltac:(lia)), E38 in Hc3.
            rewrite unsigned_lit_small in Hc3 by lia. unfold zcanon, M64 in Hc3. rewrite Z.add_0_r in Hc3.
            rewrite !Z.mod_small in Hc3 by lia. apply Z.eqb_eq in Hc3.
            paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
            apply sw_frame_ro in HF; [|vm_compute; reflexivity]. rewrite EM8 in HF. clear EM8. rename HF into EM8. clear HFr HG.
            apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
              ltac:(vm_compute; reflexivity)).
            { sw_srg. change (cK cx) with kv. rewrite Hk. change (x_FB cx) with FB.
           change (disco_classify_c.role FB 5) with (if (CtrlParsed.fb FB 22 =? 0) && ((disco_classify_c.tag FB =? 256) ||
             (disco_classify_c.tag FB =? 770) || (disco_classify_c.tag FB =? 1280)) then 1 else 2).
           rewrite HFB22, HTG. replace (fb =? 0) with true by (symmetry; apply Z.eqb_eq; lia). replace (tg =? 256) with false by (symmetry; apply Z.eqb_neq; lia). replace (tg =? 770) with false by (symmetry; apply Z.eqb_neq; lia). replace (tg =? 1280) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb orb]. reflexivity. }
            { sw_srg. exact D21. }
            { sw_srg. exact D23. }
            { sw_srg. exact D24. }
            { exact HJ6. }
            { rewrite EM8, EM7, EM6, EM5. exact K5. }
            { rewrite EM8, EM7, EM6, EM5. exact O5. }
            { rewrite EM8, EM7, EM6, EM5. exact PR5. }

            ----- rewrite branch_eq_U, U_SOff, U_SLit in Hc3. rewrite (AG5 38%nat ltac:(lia)), E38 in Hc3.
            rewrite unsigned_lit_small in Hc3 by lia. unfold zcanon, M64 in Hc3. rewrite Z.add_0_r in Hc3.
            rewrite !Z.mod_small in Hc3 by lia. apply Z.eqb_neq in Hc3.
            paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
            apply sw_frame_ro in HF; [|vm_compute; reflexivity]. rewrite EM8 in HF. clear EM8. rename HF into EM8. clear HFr HG.
            apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
              ltac:(vm_compute; reflexivity)).
            { sw_srg. change (cK cx) with kv. rewrite Hk. change (x_FB cx) with FB.
           change (disco_classify_c.role FB 5) with (if (CtrlParsed.fb FB 22 =? 0) && ((disco_classify_c.tag FB =? 256) ||
             (disco_classify_c.tag FB =? 770) || (disco_classify_c.tag FB =? 1280)) then 1 else 2).
           rewrite HFB22, HTG. replace (fb =? 0) with true by (symmetry; apply Z.eqb_eq; lia). replace (tg =? 256) with false by (symmetry; apply Z.eqb_neq; lia). replace (tg =? 770) with false by (symmetry; apply Z.eqb_neq; lia). replace (tg =? 1280) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb]. reflexivity. }
            { sw_srg. exact D21. }
            { sw_srg. exact D23. }
            { sw_srg. exact D24. }
            { exact HJ6. }
            { rewrite EM8, EM7, EM6, EM5. exact K5. }
            { rewrite EM8, EM7, EM6, EM5. exact O5. }
            { rewrite EM8, EM7, EM6, EM5. exact PR5. }

        -- rewrite branch_eq_U, U_SOff, U_SLit in Hc0. rewrite (AG5 37%nat ltac:(lia)), E37 in Hc0.
            rewrite unsigned_lit_small in Hc0 by lia. unfold zcanon, M64 in Hc0. rewrite Z.add_0_r in Hc0.
            rewrite !Z.mod_small in Hc0 by lia. apply Z.eqb_neq in Hc0. change (0 mod 2 ^ 64) with 0 in Hc0.
            paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
            apply sw_frame_ro in HF; [|vm_compute; reflexivity]. rewrite EM8 in HF. clear EM8. rename HF into EM8. clear HFr HG.
            apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
              ltac:(vm_compute; reflexivity)).
            { sw_srg. change (cK cx) with kv. rewrite Hk. change (x_FB cx) with FB.
           change (disco_classify_c.role FB 5) with (if (CtrlParsed.fb FB 22 =? 0) && ((disco_classify_c.tag FB =? 256) ||
             (disco_classify_c.tag FB =? 770) || (disco_classify_c.tag FB =? 1280)) then 1 else 2).
           rewrite HFB22, HTG. replace (fb =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. reflexivity. }
            { sw_srg. exact D21. }
            { sw_srg. exact D23. }
            { sw_srg. exact D24. }
            { exact HJ6. }
            { rewrite EM8, EM7, EM6, EM5. exact K5. }
            { rewrite EM8, EM7, EM6, EM5. exact O5. }
            { rewrite EM8, EM7, EM6, EM5. exact PR5. }
      ++ apply (st_ok_pi_pin_reg' _ _ _ 10%bv 5) in HSY; [| refine (eq_trans Ra0k _); rewrite Hk; reflexivity | reflexivity].
        paj_run_tok RUN HSY HJ5 SHOK5 SWspan; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM6 | vm_compute; reflexivity]. clear HFr HG.
        prreg HSY (10%bv : bv 5) Rj.
        rewrite (AG5 44%nat ltac:(lia)), (ETB 5%nat ltac:(lia) : ew E 44 = _), (EV35 : ew E5 276 = _) in Rj.
        unfold sw_tab in Rj.
        rewrite sw_jr_val in Rj by (pose proof (sw_slot_img' (AF_classify_core + nth 5 CLS_SW_ARMS 0)
          ltac:(unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia) ltac:(vm_compute; reflexivity)); unfold IMG_LO, IMG_TOP in *; lia).
        rewrite <- Z.add_assoc in Rj.
        lazymatch type of HSY with st_ok_pi _ _ _ ?ssj _ =>
          let wj := eval vm_compute in (match plookup pl_tpi (ss_pc ssj) with Some (PW w) => w | _ => 0 end) in
          eapply (SRr_jr_pi W3 E5 _ _ _ _ wj 10%bv (BASE + (AF_classify_core + nth 5 CLS_SW_ARMS 0)) HSY eq_refl) end;
          [vm_compute; reflexivity | vm_refl_bv | exact Rj
          | pose proof pa_B_ok; unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia
          | apply sw_even; reflexivity | ].
        intros mat' ms3 Hms3 HS3.
        lazymatch type of HS3 with st_ok ?sg ?Ee (mkSST (BASE + ?t) ?R ?Fr ?M ?Rv ?G) ?X =>
          change (st_ok_pi sg VAL Ee (mkSST t R Fr M Rv G) X) in HS3 end.
        pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ5) as HJ6.
        assert (EM7 : ms_mem ms3 = ms_mem ms2) by (subst ms3; reflexivity). rewrite <- EM7 in HJ6.
        apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
          ltac:(vm_compute; reflexivity)).
        -- sw_srg. change (cK cx) with kv. rewrite Hk. reflexivity.

        -- sw_srg. exact D21.
        -- sw_srg. exact D23.
        -- sw_srg. exact D24.
        -- exact HJ6.
        -- rewrite EM7, EM6, EM5. exact K5.
        -- rewrite EM7, EM6, EM5. exact O5.
        -- rewrite EM7, EM6, EM5. exact PR5.
      ++ apply (st_ok_pi_pin_reg' _ _ _ 10%bv 6) in HSY; [| refine (eq_trans Ra0k _); rewrite Hk; reflexivity | reflexivity].
        paj_run_tok RUN HSY HJ5 SHOK5 SWspan; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM6 | vm_compute; reflexivity]. clear HFr HG.
        prreg HSY (10%bv : bv 5) Rj.
        rewrite (AG5 45%nat ltac:(lia)), (ETB 6%nat ltac:(lia) : ew E 45 = _), (EV35 : ew E5 276 = _) in Rj.
        unfold sw_tab in Rj.
        rewrite sw_jr_val in Rj by (pose proof (sw_slot_img' (AF_classify_core + nth 6 CLS_SW_ARMS 0)
          ltac:(unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia) ltac:(vm_compute; reflexivity)); unfold IMG_LO, IMG_TOP in *; lia).
        rewrite <- Z.add_assoc in Rj.
        lazymatch type of HSY with st_ok_pi _ _ _ ?ssj _ =>
          let wj := eval vm_compute in (match plookup pl_tpi (ss_pc ssj) with Some (PW w) => w | _ => 0 end) in
          eapply (SRr_jr_pi W3 E5 _ _ _ _ wj 10%bv (BASE + (AF_classify_core + nth 6 CLS_SW_ARMS 0)) HSY eq_refl) end;
          [vm_compute; reflexivity | vm_refl_bv | exact Rj
          | pose proof pa_B_ok; unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia
          | apply sw_even; reflexivity | ].
        intros mat' ms3 Hms3 HS3.
        lazymatch type of HS3 with st_ok ?sg ?Ee (mkSST (BASE + ?t) ?R ?Fr ?M ?Rv ?G) ?X =>
          change (st_ok_pi sg VAL Ee (mkSST t R Fr M Rv G) X) in HS3 end.
        pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ5) as HJ6.
        assert (EM7 : ms_mem ms3 = ms_mem ms2) by (subst ms3; reflexivity). rewrite <- EM7 in HJ6.
        assert (SHOK6 : sh_ok SEGS SW_Bx SW_SH E5 (mrestrict (w_H W3) (ms_mem ms3))) by (unfold sh_ok, SW_SH; apply Forall_nil).
        clear HSY SHOK5.
        paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM8 | vm_compute; reflexivity]. clear HFr HG.
        apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
          ltac:(vm_compute; reflexivity)).
        -- sw_srg. change (cK cx) with kv. rewrite Hk. reflexivity.

        -- sw_srg. exact D21.
        -- sw_srg. exact D23.
        -- sw_srg. exact D24.
        -- exact HJ6.
        -- rewrite EM8, EM7, EM6, EM5. exact K5.
        -- rewrite EM8, EM7, EM6, EM5. exact O5.
        -- rewrite EM8, EM7, EM6, EM5. exact PR5.
      ++ apply (st_ok_pi_pin_reg' _ _ _ 10%bv 7) in HSY; [| refine (eq_trans Ra0k _); rewrite Hk; reflexivity | reflexivity].
        paj_run_tok RUN HSY HJ5 SHOK5 SWspan; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM6 | vm_compute; reflexivity]. clear HFr HG.
        prreg HSY (10%bv : bv 5) Rj.
        rewrite (AG5 46%nat ltac:(lia)), (ETB 7%nat ltac:(lia) : ew E 46 = _), (EV35 : ew E5 276 = _) in Rj.
        unfold sw_tab in Rj.
        rewrite sw_jr_val in Rj by (pose proof (sw_slot_img' (AF_classify_core + nth 7 CLS_SW_ARMS 0)
          ltac:(unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia) ltac:(vm_compute; reflexivity)); unfold IMG_LO, IMG_TOP in *; lia).
        rewrite <- Z.add_assoc in Rj.
        lazymatch type of HSY with st_ok_pi _ _ _ ?ssj _ =>
          let wj := eval vm_compute in (match plookup pl_tpi (ss_pc ssj) with Some (PW w) => w | _ => 0 end) in
          eapply (SRr_jr_pi W3 E5 _ _ _ _ wj 10%bv (BASE + (AF_classify_core + nth 7 CLS_SW_ARMS 0)) HSY eq_refl) end;
          [vm_compute; reflexivity | vm_refl_bv | exact Rj
          | pose proof pa_B_ok; unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia
          | apply sw_even; reflexivity | ].
        intros mat' ms3 Hms3 HS3.
        lazymatch type of HS3 with st_ok ?sg ?Ee (mkSST (BASE + ?t) ?R ?Fr ?M ?Rv ?G) ?X =>
          change (st_ok_pi sg VAL Ee (mkSST t R Fr M Rv G) X) in HS3 end.
        pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ5) as HJ6.
        assert (EM7 : ms_mem ms3 = ms_mem ms2) by (subst ms3; reflexivity). rewrite <- EM7 in HJ6.
        assert (SHOK6 : sh_ok SEGS SW_Bx SW_SH E5 (mrestrict (w_H W3) (ms_mem ms3))) by (unfold sh_ok, SW_SH; apply Forall_nil).
        clear HSY SHOK5.
        paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM8 | vm_compute; reflexivity]. clear HFr HG.
        apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
          ltac:(vm_compute; reflexivity)).
        -- sw_srg. change (cK cx) with kv. rewrite Hk. reflexivity.

        -- sw_srg. exact D21.
        -- sw_srg. exact D23.
        -- sw_srg. exact D24.
        -- exact HJ6.
        -- rewrite EM8, EM7, EM6, EM5. exact K5.
        -- rewrite EM8, EM7, EM6, EM5. exact O5.
        -- rewrite EM8, EM7, EM6, EM5. exact PR5.
      ++ apply (st_ok_pi_pin_reg' _ _ _ 10%bv 8) in HSY; [| refine (eq_trans Ra0k _); rewrite Hk; reflexivity | reflexivity].
        paj_run_tok RUN HSY HJ5 SHOK5 SWspan; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM6 | vm_compute; reflexivity]. clear HFr HG.
        prreg HSY (10%bv : bv 5) Rj.
        rewrite (AG5 47%nat ltac:(lia)), (ETB 8%nat ltac:(lia) : ew E 47 = _), (EV35 : ew E5 276 = _) in Rj.
        unfold sw_tab in Rj.
        rewrite sw_jr_val in Rj by (pose proof (sw_slot_img' (AF_classify_core + nth 8 CLS_SW_ARMS 0)
          ltac:(unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia) ltac:(vm_compute; reflexivity)); unfold IMG_LO, IMG_TOP in *; lia).
        rewrite <- Z.add_assoc in Rj.
        lazymatch type of HSY with st_ok_pi _ _ _ ?ssj _ =>
          let wj := eval vm_compute in (match plookup pl_tpi (ss_pc ssj) with Some (PW w) => w | _ => 0 end) in
          eapply (SRr_jr_pi W3 E5 _ _ _ _ wj 10%bv (BASE + (AF_classify_core + nth 8 CLS_SW_ARMS 0)) HSY eq_refl) end;
          [vm_compute; reflexivity | vm_refl_bv | exact Rj
          | pose proof pa_B_ok; unfold AF_classify_core, CLS_SW_ARMS; cbn [nth]; lia
          | apply sw_even; reflexivity | ].
        intros mat' ms3 Hms3 HS3.
        lazymatch type of HS3 with st_ok ?sg ?Ee (mkSST (BASE + ?t) ?R ?Fr ?M ?Rv ?G) ?X =>
          change (st_ok_pi sg VAL Ee (mkSST t R Fr M Rv G) X) in HS3 end.
        pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ5) as HJ6.
        assert (EM7 : ms_mem ms3 = ms_mem ms2) by (subst ms3; reflexivity). rewrite <- EM7 in HJ6.
        assert (SHOK6 : sh_ok SEGS SW_Bx SW_SH E5 (mrestrict (w_H W3) (ms_mem ms3))) by (unfold sh_ok, SW_SH; apply Forall_nil).
        clear HSY SHOK5.
        paj_run_to_tok RUNTO HS3 HJ6 SHOK6 SWspan PC_ROLE; [awr_ok_tac|].
        apply sw_frame_ro in HF; [rename HF into EM8 | vm_compute; reflexivity]. clear HFr HG.
        apply (sw_leaf cx fpos W3 ly3 S3 regs3 mem3 md3 _ _ _ _ _ HROLE HPRE HAT0 HS3 eq_refl eq_refl HAE5
          ltac:(vm_compute; reflexivity)).
        -- sw_srg. change (cK cx) with kv. rewrite Hk. reflexivity.

        -- sw_srg. exact D21.
        -- sw_srg. exact D23.
        -- sw_srg. exact D24.
        -- exact HJ6.
        -- rewrite EM8, EM7, EM6, EM5. exact K5.
        -- rewrite EM8, EM7, EM6, EM5. exact O5.
        -- rewrite EM8, EM7, EM6, EM5. exact PR5.
Qed.

End h.
End f.
End d.
