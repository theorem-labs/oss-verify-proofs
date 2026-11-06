(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d7f488d30, twin c90d4fa54d43160b), this
   file: put_string's walk, the LOOP segment, over PutStringB_Base.v, toward the #102 tput_string_specX
   (PRH_FnWriter.v 2b497bc72172). Two stretches:
   - psl_head_step, the loop head (+ 0x180, AF_put_string + 384): `addi s10, s4, -1`, u's shadow byte unpoisoned
     (`sb zero, 4(s6)`), the byte tests (+ 0x18c `beq s9, 34`, + 0x194 `beq s9, 92`, + 0x19c `bgeu 31, s9`); a special
     byte goes to + 0x1b4: s11 := zext.b s9, put(o, s + j, i - j) (`jal put` + 0x1c4) and the escape join (+ 0x1c8,
     AF + 456, ps_esc); an ordinary byte re-poisons u's granule (+ 0x1a4) and passes the UBSan pointer-overflow check
     (+ 0x1ac `bne s10, -1`) to the next join (+ 0x27c, AF + 636, ps_next). NOT TAKEN: the check's fall-through (+ 0x1b0
     `j + 0x38c`, the UBSan trap `unimp` at + 0x38c): s10 = s + i, and s + n + 1 <= the allocation ceiling < 2^64 - 1
     (psl_str_now: the string's home, kept_at_bounds), so s + i <> 2^64 - 1.
   - psl_next_step, the next join (+ 0x27c): s[i + 1]'s shadow-checked load (+ 0x27c .. + 0x290, the slow path + 0x2a4
     `andi (s + i + 1) 7` / + 0x2a8 `blt`), then `bnez s9` (+ 0x29c) to the head at i + 1 (+ 0x180) or, on the NUL,
     + 0x2b4 .. + 0x2c0 (s4 -= 1, s5 := R[16] = F, s8 := R[8] = F) to the tail join (+ 0x2c8, AF + 712, ps_tail).
     NOT TAKEN: the report branch (+ 0x2ac `addi a0, s8, 1`, + 0x2b0 `jal __asan_report_load1`): s[i + 1] is
     addressable (i + 1 <= n; psl_str_now's range_addressable, saddr_ok), so a nonzero shadow byte v has
     (s + i + 1) mod 8 < v and the `blt` at + 0x2a8 is taken (psl_slow_lt).
   Seats MEASURED (log, the internal file zfb-20261029T194501Z.log, the symbolic probe of both stretches).
   PORTED (reuse, not trust) from image A's walk lib/A/Prog/PRW_put_string_l.v: the seats, the pure
   plan lemmas; B' differs: the next join (+ 0x27c) is AFTER the re-poison, the head has the UBSan check, the run put's
   a2 is `sub a2, s8, s2`. No address literal: entries and return sites by name (AF_put_string + k, k a B' offset).
   The re-hiding move: the whole loop lies after the opening-quote put (put reallocs when it grows, a crossing call),
   so its joins are ps_commonR at wle' SEGS RZ_cf, its stretches and branches run at that relation, and the two steps
   and their continuations conclude SRr' SEGS RZ_cf. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* the step relation over a world relation and the re-hiding relation (SRrG, wle', SRr'), the fixed zone RZ_cf and
   the branch over a world relation (paj_branchR) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomPre YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutStringB_CallerJ PutStringB_S7bKit PutStringB_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutStringB_Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutStringB_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia must see the division equations: the realignment and the shadow addresses are mod / div 8 and 32 *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's generated numbers (lib/B/PRH_ImgB.v, the #102 B' table) are the PrhImg the texts read *)
#[local] Existing Instance prh_img_B.

(* ---- the seats (MEASURED, zfb-20261029T194501Z: the head's four stretches and the next join's five) ---- *)
(* u's shadow granule (F + 32's cell, SHF + 4, s6 = atom 22): the only byte the head writes *)
Definition psl_shf : YP09.region := YP09.mkRegion (Some 22%nat) 4 5 4 5 [].
(* the loop head (+ 0x180): the registers as atoms, that one shadow byte *)
Definition psl_ssH : sstate := mkSS (AF_put_string + 384) sr_atoms [psl_shf] None (mkFacts [] [] []).
(* the next join (+ 0x27c): s[i + 1]'s shadow cell (atom 33, its value atom 34), s[i + 1] itself at s4 (atom 20; its
   value atom 35), the two words R + 8 / R + 16 (the frame F, atom 32); the alias declares atom 33 as the shadow
   address of s8 + 1 (`addi a0, s8, 1; srli; add s7; lb`). The stretch writes nothing. *)
Definition psl_shb : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition psl_byt : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition psl_rblk : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 32 0))].
Definition psl_factsN : facts :=
  mkFacts [(34%nat, mkAF 0 7 0); (35%nat, mkAF 0 255 0)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 24 1) (SLit 3)) (SOff 23 0), SOff 33 0)].
Definition psl_ssN : sstate := mkSS (AF_put_string + 636) sr_atoms [psl_shb; psl_byt; psl_rblk] None psl_factsN.

(* ---- pure facts about the string and the plan ---- *)
Lemma psl_byte_in : forall (bs : list Z) k, (k <= length bs)%nat -> nth k (bs ++ [0]) 0 <> 0 ->
  (k < length bs)%nat /\ nth k (bs ++ [0]) 0 = nth k bs 0.
Proof.
intros bs k Hk Hc. destruct (Nat.eq_dec k (length bs)) as [-> | Hne].
- exfalso. rewrite nth_middle in Hc. exact (Hc eq_refl).
- assert (Hlt : (k < length bs)%nat) by (clear - Hk Hne; lia). split; [exact Hlt | apply app_nth1; exact Hlt].
Qed.
Lemma psl_byte_nul : forall (bs : list Z) k, Forall (fun x => x <> 0) bs -> (k <= length bs)%nat ->
  nth k (bs ++ [0]) 0 = 0 -> k = length bs.
Proof.
intros bs k Hnz Hk Hc. destruct (Nat.eq_dec k (length bs)) as [-> | Hne]; [reflexivity|].
exfalso. assert (Hlt : (k < length bs)%nat) by (clear - Hk Hne; lia). rewrite app_nth1 in Hc by exact Hlt.
rewrite Forall_forall in Hnz. exact (Hnz (nth k bs 0) (nth_In bs 0 Hlt) Hc).
Qed.
(* the head's plan at a byte put as itself: the same plan at the next join *)
Lemma psl_plan_ns : forall (bs : list Z) P i j, (j <= i)%nat -> (i < length bs)%nat ->
  WriterSpec.special (nth i bs 0) = false ->
  [34] :: WriterSpec.spieces_run [] bs = P ++ WriterSpec.spieces_run (firstn (i - j) (skipn j bs)) (skipn i bs) ->
  [34] :: WriterSpec.spieces_run [] bs =
    P ++ WriterSpec.spieces_run (firstn (S i - j) (skipn j bs)) (skipn (S i) bs).
Proof.
intros bs P i j Hji Hi Hsp Heq. rewrite Heq. f_equal.
rewrite (skipn_nth_cons bs i Hi), (sr_nonspec _ _ _ Hsp), (firstn_skipn_snoc bs i j Hji Hi). reflexivity.
Qed.
(* the next join's plan when the string is consumed: the pending run is its tail *)
Lemma psl_plan_tail : forall (bs : list Z) P i j, (j <= S i)%nat -> S i = length bs ->
  [34] :: WriterSpec.spieces_run [] bs =
    P ++ WriterSpec.spieces_run (firstn (S i - j) (skipn j bs)) (skipn (S i) bs) ->
  [34] :: WriterSpec.spieces_run [] bs = P ++ [skipn j bs].
Proof.
intros bs P i j Hji Hlen Heq. rewrite Heq. f_equal.
rewrite (skipn_all2 (n := S i) bs) by (clear - Hlen; lia). cbn [WriterSpec.spieces_run]. f_equal.
apply firstn_all2. rewrite length_skipn. clear - Hlen; lia.
Qed.
(* the head's plan at a special byte: the pending run is one piece, the escape the next *)
Lemma psl_plan_esc : forall (bs : list Z) P i j, (j <= i)%nat -> (i < length bs)%nat ->
  WriterSpec.special (nth i bs 0) = true ->
  [34] :: WriterSpec.spieces_run [] bs = P ++ WriterSpec.spieces_run (firstn (i - j) (skipn j bs)) (skipn i bs) ->
  WriterSpec.spieces bs =
    P ++ firstn (i - j) (skipn j bs)
         :: WriterSpec.esc (nth i bs 0) :: WriterSpec.spieces_run [] (skipn (S i) bs) ++ [[34]] /\
  [34] :: WriterSpec.spieces_run [] bs =
    (P ++ [firstn (i - j) (skipn j bs)]) ++
      WriterSpec.esc (nth i bs 0) :: WriterSpec.spieces_run [] (skipn (S i) bs).
Proof.
intros bs P i j Hji Hi Hsp Heq.
assert (HE : [34] :: WriterSpec.spieces_run [] bs =
  P ++ firstn (i - j) (skipn j bs) :: WriterSpec.esc (nth i bs 0) :: WriterSpec.spieces_run [] (skipn (S i) bs)).
{ rewrite Heq. f_equal. rewrite (skipn_nth_cons bs i Hi). exact (sr_spec _ _ _ Hsp). }
split.
- unfold WriterSpec.spieces.
  change ([34] :: WriterSpec.spieces_run [] bs ++ [[34]]) with (([34] :: WriterSpec.spieces_run [] bs) ++ [[34]]).
  rewrite HE, <- app_assoc. reflexivity.
- rewrite <- app_assoc. exact HE.
Qed.

(* ---- small closed facts (no lia in a large context) ---- *)
Lemma psl_456 : 0 <= 456 < 928 /\ 456 mod 2 = 0.
Proof. split; [lia | reflexivity]. Qed.
Lemma psl_w1 : Z.of_N 1 <= 8.
Proof. cbn. lia. Qed.
Lemma psl_w8 : Z.of_N 8 <= 8.
Proof. cbn. lia. Qed.
Lemma psl_rng_b : forall v, 0 <= v < 256 -> 0 <= v < 2 ^ (8 * Z.of_N 1).
Proof. intros v Hv. change (2 ^ (8 * Z.of_N 1)) with 256. exact Hv. Qed.
Lemma psl_rng_w : forall v, 0 <= v < 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_N 8).
Proof. intros v Hv. change (8 * Z.of_N 8) with 64. exact Hv. Qed.
Lemma psl_rng0 : 0 <= 0 < 256.
Proof. lia. Qed.
(* the callee-saved registers of the ABI (YG0d.v acallee_saved), by a boolean test *)
Lemma psl_cs : forall z, existsb (Z.eqb z) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true ->
  acallee_saved z.
Proof.
intros z H. unfold acallee_saved. cbn [existsb] in H.
repeat (apply Bool.orb_true_iff in H; destruct H as [H | H]; [apply Z.eqb_eq in H; clear - H; lia |]).
discriminate H.
Qed.

(* ---- arithmetic the engine's values need ---- *)
Lemma psl_and255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof.
intros c Hc. replace 255 with (Z.ones 8) by reflexivity. rewrite Z.land_ones by (clear; lia).
change (2 ^ 8) with 256. apply Z.mod_small. exact Hc.
Qed.
Lemma psl_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v Hn Hv. rewrite denot_lit_U. f_equal. apply U_atom; assumption. Qed.
Lemma psl_atom_offv : forall E n v c w, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> w = v + c -> 0 <= w < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 w.
Proof. intros E n v c w Hn Hv -> Hw. rewrite denot_lit_U. f_equal. apply U_atom_off; assumption. Qed.
(* s11 at the run put (+ 0x1b4 `zext.b s11, s9`, the engine's `andi s11, s9, 255`) *)
Lemma psl_and_val : forall E p (c : Z), ew E p = Z_to_bv 64 c -> 0 <= c < 256 ->
  sv_denot E (SAlu ALU_AND (SOff p 0) (SLit 255)) = Z_to_bv 64 c.
Proof.
intros E p c Hp Hc. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SLit, (U_atom E p c Hp) by (clear - Hc; lia). cbn [zalu_raw].
assert (H255 : zcanon 255 = 255) by (unfold zcanon, M64; reflexivity).
rewrite H255, psl_and255 by exact Hc. apply zcanon_id. unfold M64. clear - Hc; lia.
Qed.
(* a2 at the run put (+ 0x1b8 `sub a2, s8, s2`, the engine's (-s2) + s8): the run's length *)
Lemma psl_sub_val : forall E p q (a b : Z), ew E p = Z_to_bv 64 a -> ew E q = Z_to_bv 64 b ->
  0 <= b -> b <= a -> a < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff q 0) (SLit (-1))) (SOff p 0)) = Z_to_bv 64 (a - b).
Proof.
intros E p q a b Hp Hq Hb Hba Ha. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite U_SLit.
rewrite (U_atom E p a Hp) by (clear - Hb Hba Ha; lia). rewrite (U_atom E q b Hq) by (clear - Hb Hba Ha; lia).
unfold zcanon, M64. replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
rewrite Z.add_mod_idemp_l by (clear; lia).
replace (b * (2 ^ 64 - 1) + a) with ((a - b) + b * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. clear - Hb Hba Ha; lia.
Qed.
(* the partial granule's test of the shadow-checked load of s[i + 1] (+ 0x2a8 `blt ((s8 + 1) & 7), shadow`) *)
Lemma psl_slow_lt : forall E p q (v sv : Z), ew E p = Z_to_bv 64 v -> ew E q = Z_to_bv 64 sv ->
  0 <= v -> v + 1 < 2 ^ 64 -> 0 < sv < 8 -> (v + 1) mod 8 < sv ->
  branch_taken BC_LT (sv_denot E (SAlu ALU_AND (SOff p 1) (SLit 7))) (sv_denot E (SOff q 0)) = true.
Proof.
intros E p q v sv Hp Hq Hv Hv1 Hsv Hlt.
cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned.
fold (U E (SOff q 0)). fold (U E (SAlu ALU_AND (SOff p 1) (SLit 7))).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E p v 1 Hp) by (clear - Hv Hv1; lia).
rewrite U_SLit, (U_atom E q sv Hq) by (clear - Hsv; lia).
change (zcanon 7) with 7.
assert (Hl : 0 <= Z.land (v + 1) 7 < 2 ^ 64).
{ change 7 with (Z.ones 3). rewrite Z.land_ones by (clear; lia). change (2 ^ 3) with 8.
  pose proof (Z.mod_pos_bound (v + 1) 8 ltac:(clear; lia)). clear - H; lia. }
rewrite (YP0e.zcanon_id (Z.land (v + 1) 7)) by (unfold M64; exact Hl).
change 7 with (Z.ones 3). rewrite Z.land_ones by (clear; lia). change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound (v + 1) 8 ltac:(clear; lia)) as Hm.
rewrite !YP0e.swrap64_id by (unfold half64; clear - Hm Hsv; lia). apply Z.ltb_lt. clear - Hlt; lia.
Qed.
(* the shadow address of s[i + 1], as the next seat's alias declares it *)
Lemma psl_shadow_decl1 : forall E (p b s : nat) (pv Bs : Z),
  ew E p = Z_to_bv 64 pv -> 0 <= pv -> pv + 1 < 2 ^ 64 -> ew E b = Z_to_bv 64 Bs ->
  ew E s = Z_to_bv 64 (Bs + (pv + 1) / 8) ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p 1) (SLit 3)) (SOff b 0)) = sv_denot E (SOff s 0).
Proof.
intros E p b s pv Bs Hp Hpv Hpv2 Hb Hs. apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hp, Hb, Hs, !Z.add_0_r.
rewrite (unsigned_lit_small pv) by (clear - Hpv Hpv2; lia).
rewrite (zcanon_id (pv + 1)) by (unfold M64; clear - Hpv Hpv2; lia).
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold zcanon, M64. rewrite (Z.mod_mod Bs) by (clear; lia). rewrite Z.add_mod_idemp_r by (clear; lia).
rewrite (Z.mod_mod (Bs + (pv + 1) / 8)) by (clear; lia). f_equal. clear; lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
(* the kit's non-primary room invariant (PRH_Base.v PrhRoomLive) *)
Context {RL : PrhRoomLive}.
Section f.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

(* ---- the view and the env of a seat ---- *)
(* one zero byte read back through the view *)
Lemma psl_aview0 : forall (H : word -> bool) (mem : word -> option byte) a,
  val_mem SEGS (mrestrict H mem) a 1 0 -> aview SEGS H mem a = Some 0.
Proof.
intros H mem a Hm. pose proof (Hm 0%nat ltac:(clear; lia)) as Hb.
replace (a + Z.of_nat 0) with a in Hb by (clear; lia).
unfold aview. rewrite Hb. vm_compute. reflexivity.
Qed.
(* a byte the loop's stretches keep: outside their write windows *)
Lemma psl_keep_av : forall E rs (H : word -> bool) (m m' : word -> option byte) (lo hi : Z),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall x, in_wrange E rs x -> lo <= x < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> (a < lo \/ hi <= a) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo hi Hfr Hw a Ha Hout.
apply (kept_of_frame E rs H m m' (fun x => x = a) Hfr); [|reflexivity].
intros x ->. split; [exact Ha|]. intros Hin. pose proof (Hw a Hin) as Hx. clear - Hx Hout; lia.
Qed.
(* the R block's words the loop reads, at a later memory that agrees on [R + 8, R + 64) *)
Lemma psl_rblock_keep : forall X pos (W1 W2 : world SEGS) (m1 m2 : word -> option byte),
  ps_rblock X pos W1 m1 ->
  (forall a, x_R X + 8 <= a < x_R X + 64 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
  ps_rblock X pos W2 m2.
Proof.
intros X pos W1 W2 m1 m2 (A8 & A16 & A24 & A32 & A40 & A48 & A56) K.
unfold ps_rblock.
split; [rewrite <- A8; apply rdword_eq_of; intros k Hk; apply K; clear - Hk; lia|].
split; [rewrite <- A16; apply rdword_eq_of; intros k Hk; apply K; clear - Hk; lia|].
split; [rewrite <- A24; apply rdword_eq_of; intros k Hk; apply K; clear - Hk; lia|].
split; [rewrite <- A32; apply rdword_eq_of; intros k Hk; apply K; clear - Hk; lia|].
split; [rewrite <- A40; apply rdword_eq_of; intros k Hk; apply K; clear - Hk; lia|].
split; [rewrite <- A48; apply rdword_eq_of; intros k Hk; apply K; clear - Hk; lia|].
rewrite <- A56; apply rdword_eq_of; intros k Hk; apply K; clear - Hk; lia.
Qed.
(* the loop registers at a later register file that agrees on them *)
Lemma psl_lregs_eq : forall X pos (regs regs' : bvmap 5 word),
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  ps_lregs X pos regs -> ps_lregs X pos regs'.
Proof.
intros X pos regs regs' E2 E3 E4 E8 E9 E19 E21 E22 E23 (R2 & R3 & R4 & R8 & R9 & R19 & R21 & R22 & R23).
unfold ps_lregs. rewrite E2, E3, E4, E8, E9, E19, E21, E22, E23.
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
split; [exact R19|]. split; [exact R21|]. split; [exact R22 | exact R23].
Qed.
(* a seat's env: the join's registers are atoms 0 .. 31, the extras atoms 32 .. *)
Lemma psl_ewv : forall regs extra n (r : bv 5) v, (n <? 32)%nat = true -> Z.of_nat n = bv_unsigned r ->
  getr regs r = w64 v -> ew (Eimg (Ereg regs extra)) n = Z_to_bv 64 v.
Proof.
intros regs extra n r v Hn Hr Hv. apply Nat.ltb_lt in Hn.
rewrite Eimg_low by (unfold A_TEXT; clear - Hn; lia). rewrite (ew_Ereg_nat regs extra n r Hr). exact Hv.
Qed.
Lemma psl_ewx : forall regs extra k v, (k <? 8)%nat = true -> nth k extra (Z_to_bv 64 0) = Z_to_bv 64 v ->
  ew (Eimg (Ereg regs extra)) (32 + k) = Z_to_bv 64 v.
Proof.
intros regs extra k v Hk Hv. apply Nat.ltb_lt in Hk.
rewrite Eimg_low by (unfold A_TEXT; clear - Hk; lia). rewrite ew_Ereg_extra. exact Hv.
Qed.
(* a register of a seated state: the join's own (an atom), or a symbolic value *)
Lemma psl_reg_keep : forall (H : word -> bool) regs0 extra ss ms (r : bv 5),
  st_ok_pi SEGS VAL (Eimg (Ereg regs0 extra)) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros H regs0 extra ss ms r HS Hr.
rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
pose proof (u5_range r) as Hr5. rewrite Eimg_low by (unfold A_TEXT; clear - Hr5; lia). apply ew_Ereg_reg.
Qed.
Lemma psl_reg_keep_ok : forall (H : word -> bool) regs0 extra ss ms (r : bv 5),
  st_ok SEGS (Eimg (Ereg regs0 extra)) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros H regs0 extra ss ms r HS Hr.
rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
pose proof (u5_range r) as Hr5. rewrite Eimg_low by (unfold A_TEXT; clear - Hr5; lia). apply ew_Ereg_reg.
Qed.
Lemma psl_reg_val : forall (H : word -> bool) E ss ms (r : bv 5) e v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = Z_to_bv 64 v ->
  getr (ms_regs ms) r = w64 v.
Proof. intros H E ss ms r e v HS Hr He. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr, He. reflexivity. Qed.
Lemma psl_reg_val_ok : forall (H : word -> bool) E ss ms (r : bv 5) e v,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = Z_to_bv 64 v ->
  getr (ms_regs ms) r = w64 v.
Proof. intros H E ss ms r e v HS Hr He. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr, He. reflexivity. Qed.
(* a callee-saved register across a call, read at the call's seated state *)
Lemma psl_pres_keep : forall (H : word -> bool) regs0 extra ss ms regs2 (r : bv 5),
  st_ok SEGS (Eimg (Ereg regs0 extra)) ss (restrict H ms) -> aregs_preserved (ms_regs ms) regs2 ->
  existsb (Z.eqb (bv_unsigned r)) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr regs2 r = getr regs0 r.
Proof.
intros H regs0 extra ss ms regs2 r HS HP Hc Hr.
pose proof (HP (bv_unsigned r) (psl_cs _ Hc)) as E. rewrite !Z_to_bv_bv_unsigned in E. rewrite E.
exact (psl_reg_keep_ok H regs0 extra ss ms r HS Hr).
Qed.
Lemma psl_pres_val : forall (H : word -> bool) E ss ms regs2 (r : bv 5) e v,
  st_ok SEGS E ss (restrict H ms) -> aregs_preserved (ms_regs ms) regs2 ->
  existsb (Z.eqb (bv_unsigned r)) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true ->
  sr_get (ss_regs ss) r = e -> sv_denot E e = Z_to_bv 64 v -> getr regs2 r = w64 v.
Proof.
intros H E ss ms regs2 r e v HS HP Hc Hr He.
pose proof (HP (bv_unsigned r) (psl_cs _ Hc)) as Ex. rewrite !Z_to_bv_bv_unsigned in Ex. rewrite Ex.
exact (psl_reg_val_ok H E ss ms r e v HS Hr He).
Qed.

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the allocator relation's laws (YCbqG.v AR_laws_x; ARx and its laws are the instance's, supplied at the walk's top as
   for every segment file of the walk) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the engine's / instance's side conditions of the frame-area step (YGcallSx.v Section x) *)
Hypothesis segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling, discharged by CfParamsPreset.v's preset_head_wide) *)
Hypothesis HW : prh_head_wide.
(* the registered zero-shadow ranges are granule-aligned (YG0f.v asyms_ok's aso_zshadow; image fact of the instance,
   discharged at PI_prog_B) *)
Hypothesis ASO : asyms_ok B.
(* the image's shadow is visible over the instance's bounds (PutStringB_Base.v HIMGSH: YGcfAmx2.img_shadow_vis_cf
   at IMG_LO_B / IMG_TOP_B; discharged at PI_prog_B) *)
Hypothesis HIMGSH : forall ly S Hp (W : world SEGS) mem md a, ARx ly S Hp W mem md ->
  @pa_lo _ B_prog_listing PA <= a < @pa_hi _ B_prog_listing PA -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the instance's image bounds (IMAGE FACT, PI_prog_B: IMG_LO_B / IMG_TOP_B, below the low shadow) *)
Hypothesis HPAB : 4096 <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= kLowShadowBeg.
(* alloc.c's six statics and fuzz_preset.c's g_own_ran_out (the ledger's globals, prh_pst, PRH_Base.v:752-755) are image bytes the runtime does not own, apart from errno, and none
   lies in the read-only band (YC1fPx's PST_ok; PRW_pj_write.v's pj_write walk takes the same texts less the errno conjunct; image facts) *)
Hypothesis PST_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_B).
(* the generic memory invariant (the 12:18Z ruling) and its laws; the walk crosses calls *)
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.
(* the tokenless runner and the branch at the re-hiding relation: every stretch of this file runs after a put *)
Let NTRUNTOI := SRr_run_to_pi_AJx_invR B ARx LAWS Pm PLAW (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Let BR := paj_branchR (PI := PA) (wle' SEGS RZ_cf).
Local Notation AJ := (ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx).
Variable CTX0 : list (list Z).
(* put's text (the #102 tput_specX), at this Section's float state: the ONE callee-text use of put in this file *)
Hypothesis PUT : tput_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* FRM0-ENTRY (fpre's last conjunct) at this Section's float state: the rounding mode is 0 at the run put's
   entry (the assembly supplies it from psK_head's float facts) *)
Hypothesis HFRMx : frm_zero (@fp_csr fx).
(* the base file's lemmas at this section's variables and hypotheses; put's call step: its join premise, its
   continuation's join and its conclusion SRr' are at wle' SEGS RZ_cf *)
Local Notation ps_put_step := (ps_put_step B ARx LAWS segs_low HPAB HPSTRO Pm PCALL CTX0 PUT).
Local Notation ps_pre := (ps_pre B ARx CTX0).
Local Notation ps_head := (ps_head B ARx Pm).
Local Notation ps_tail := (ps_tail B ARx Pm).
Local Notation ps_commonR := (ps_commonR B ARx Pm).
Local Notation ps_esc := (ps_esc B ARx Pm).
Local Notation ps_next := (ps_next B ARx Pm).
Local Notation ps_Qfin := (ps_Qfin B ARx Pm).
Local Notation kept_at_bounds := (kept_at_bounds B ARx LAWS HPAB).
Local Notation str_notin_fp := (str_notin_fp B ARx LAWS).
Local Notation cstr_from_entryR := (cstr_from_entryR B ARx HPSTRO).
Local Notation str_shadow_at := (str_shadow_at B ARx LAWS ASO HIMGSH HPAB).
Local Notation kept_at_loc := (kept_at_loc B ARx LAWS HPAB).
Local Notation ps_common_frameR := (ps_common_frameR B ARx LAWS segs_low HW PST_ok Pm CTX0).

(* ---- the walk's facts at a join of the loop (after a put: the join at wle' SEGS RZ_cf) ---- *)
Lemma psl_frame_facts : forall X ch pos P lyc Sc Hpc Wc memc mdc kc,
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc ->
  In (0, pos) (frames Sc) /\ frame_addr lyc 0 pos = x_F X pos /\
  4096 <= x_F X pos /\ x_F X pos + 64 <= YM05.alloc_ceiling /\
  (forall k, 0 <= k < 8 -> apresent (w_H Wc) memc (x_SHF X pos + k)) /\
  x_SHF X pos = SHADOW_OFF + x_F X pos / 8.
Proof.
intros X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM.
pose proof HCOM as (HJ & _).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as HLLE. pose proof (ajxR_frs HJ) as HFRS.
pose proof HLLE as (_ & _ & _ & _ & _ & HlyF & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite HFRS; left; reflexivity).
assert (EF : frame_addr lyc 0 pos = x_F X pos) by (unfold x_F, frame_addr; rewrite HlyF; reflexivity).
destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR Hin) as (_ & _ & _ & HFsh).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite EF in HFsh, HF4096, HFceil. change (fs_frame_bytes 0) with 64 in HFsh, HFceil.
change (64 / 8) with 8 in HFsh.
assert (HSHF : x_SHF X pos = SHADOW_OFF + x_F X pos / 8) by (unfold x_SHF, PS_SB; reflexivity).
split; [exact Hin|]. split; [exact EF|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [intros k Hk; rewrite HSHF; exact (proj1 (HFsh k Hk)) | exact HSHF].
Qed.

(* the string at a join of the loop: its bytes, its shadow, its home's bounds and location *)
Lemma psl_str_now : forall X ch pos P lyc Sc Hpc Wc memc mdc kc,
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc ->
  cstr Wc memc (x_s X) (x_bs X) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (x_s X) (x_n X + 1) /\
  shadow_hull_vis (aview SEGS (w_H Wc) memc) (x_s X) (x_n X + 1) /\
  4096 <= x_s X /\ x_s X + x_n X + 1 <= ASAN_CEIL /\
  (x_s X + (x_n X + 1) <= kLowShadowBeg \/ kHighMemBeg <= x_s X).
Proof.
intros X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM.
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & _ & Ho1 & _ & Hout0 & Hled0 & Hcstr0 & Hkept0 & Hdisj0 & _).
destruct HFPRE as (HPRE & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
pose proof HCOM as (HJ & _ & _ & _ & _ & (ok & ranc & bufc & Lamc & peakc & _ & _ & Hled & _ & Hkept & Hlive & _) & _).
pose proof (ajxR_ar HJ) as HARc.
destruct (psl_frame_facts X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM) as (Hin & _).
assert (Hn1 : 0 < x_n X + 1) by (clear - X; unfold x_n; lia).
destruct (kept_at_bounds (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X) (x_Lam X) (x_peak X) _ _ (x_ran X)
  (x_s X) _ HAR0 Hled0 Hkept0 Hn1) as (Hs4096 & HsC).
assert (HSPc : ASAN_CEIL + STK_put_string <= x_sp X) by (clear - Hceil Hslo; unfold ASAN_CEIL, x_sp; lia).
assert (Hso : x_s X + (x_n X + 1) <= x_o X) by (clear - HsC HSPc Ho1 HSTK208; lia).
assert (Hcase0 : WriterApp.w_cap (x_st X) <> 0 -> In (x_buf X, WriterApp.w_cap (x_st X)) (x_Lam X)).
{ intros Hc0. destruct Hout0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz0 & _) | (_ & HinL & _)]);
    [clear - Hc0 Hz0; lia | exact HinL]. }
assert (Hdisj0' : WriterApp.w_cap (x_st X) = 0 \/ x_s X + (x_n X + 1) <= x_buf X \/
  x_buf X + WriterApp.w_cap (x_st X) <= x_s X) by (clear - Hdisj0; lia).
assert (Hnfp : forall a, x_s X <= a < x_s X + x_n X + 1 -> ~ inFP (x_FP X) a).
{ intros a Ha. unfold x_FP.
  apply (str_notin_fp (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X) (x_Lam X) (x_peak X) _ _ (x_ran X)
    (x_o X) (x_buf X) (WriterApp.w_cap (x_st X)) (x_s X) _ HAR0 Hled0 Hkept0 Hn1 Hdisj0' Hcase0 Hso a).
  clear - Ha; lia. }
assert (HCSTR : cstr Wc memc (x_s X) (x_bs X)).
{ apply (cstr_from_entryR (wle' SEGS RZ_cf) _ _ (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X) _ lyc Sc
    Hpc Wc memc mdc kc
    (x_Lam X) (x_peak X) _ _ (x_ran X) Lamc peakc _ _ ranc (x_s X) (x_bs X) HJ Hled0 Hled (proj1 Hcstr0) Hkept0
    Hlive Hnfp).
  exact (ps_fp_closed B ARx LAWS CTX0 X ch Hpre). }
destruct (str_shadow_at lyc Sc Hpc Wc memc mdc Lamc peakc _ _ ranc (x_s X) (x_n X + 1) HARc Hled Hkept Hn1)
  as (HRA & HHV).
destruct (kept_at_loc lyc Sc Hpc Wc memc mdc Lamc peakc _ _ ranc (x_s X) (x_n X + 1) 0 pos HARc Hled Hkept Hn1 Hin
  ltac:(vm_compute; reflexivity)) as (Hsapp & _).
split; [exact HCSTR|]. split; [exact HRA|]. split; [exact HHV|]. split; [exact Hs4096|].
split; [clear - HsC; lia | exact Hsapp].
Qed.

(* ---- the pending run [j, i) of a special byte i: its bytes and its home (ps_put_step's premises) ---- *)
Lemma psl_kept_sub : forall Lam p n p' n', kept_at B Lam p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  kept_at B Lam p' n'.
Proof.
intros Lam p n p' n' Hk H1 H2 H3.
destruct Hk as [(b & m & Hin & Hb & Hpe) | [(Hzs & Hlo & Hhi & Hall) | (Hlo & Hhi & Hall)]].
- left. exists b, m. split; [exact Hin|]. clear - Hb Hpe H1 H2 H3; lia.
- right; left. split; [|split; [clear - Hlo H1; lia | split; [clear - Hhi H2 H3; lia |]]].
  + destruct Hzs as (q & m & Hin & Hq & Hqm). exists q, m. split; [exact Hin | clear - Hq Hqm H1 H2 H3; lia].
  + intros a Ha. apply Hall. clear - Ha H1 H3; lia.
- right; right. split; [clear - Hlo H1; lia | split; [clear - Hhi H2 H3; lia |]].
  intros a Ha. apply Hall. clear - Ha H1 H3; lia.
Qed.

Lemma psl_home_run : forall X lyc Sc Lamc bufc capc (i j : nat), (j <= i)%nat -> (i <= length (x_bs X))%nat ->
  kept_at B Lamc (x_s X) (x_n X + 1) -> (capc = 0 \/ x_s X + x_n X + 1 <= bufc \/ bufc + capc <= x_s X) ->
  prhWriter_src_home B lyc Sc Lamc bufc capc (x_s X + Z.of_nat j)
    (Z.of_nat (length (firstn (i - j) (skipn j (x_bs X))))).
Proof.
intros X lyc Sc Lamc bufc capc i j Hji Hi Hk Hd. rewrite length_firstn, length_skipn. unfold x_n in *.
split.
- left. apply (psl_kept_sub Lamc (x_s X) (Z.of_nat (length (x_bs X)) + 1));
    [exact Hk | clear - Hji Hi; lia | clear - Hji Hi; lia | clear - Hji Hi; lia].
- clear - Hd Hji Hi; lia.
Qed.

Lemma psl_src_run : forall X ch pos P lyc Sc Hpc Wc memc mdc kc (i j : nat),
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc -> (j <= i)%nat ->
  (i <= length (x_bs X))%nat ->
  src_rd Wc memc (x_s X + Z.of_nat j) (firstn (i - j) (skipn j (x_bs X))).
Proof.
intros X ch pos P lyc Sc Hpc Wc memc mdc kc i j Hpre HCOM Hji Hi.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcstr0 & _).
pose proof Hcstr0 as (_ & Hs4096 & Hsceil & _ & Har8 & _).
destruct (psl_str_now X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM) as (Hcs & HRA & HHV & _).
assert (Hlen : length (firstn (i - j) (skipn j (x_bs X))) = (i - j)%nat)
  by (rewrite length_firstn, length_skipn; clear - Hji Hi; lia).
unfold src_rd, bytes_at. rewrite Hlen.
destruct Hcs as (Hg & _).
split.
{ rewrite <- (firstn_skipn j (x_bs X)) in Hg. rewrite <- app_assoc in Hg.
  apply (proj1 (garr8_app SEGS _ _ _ _)) in Hg. destruct Hg as (_ & Hg). rewrite length_firstn in Hg.
  replace (Nat.min j (length (x_bs X))) with j in Hg by (clear - Hji Hi; lia).
  rewrite <- (firstn_skipn (i - j) (skipn j (x_bs X))) in Hg. rewrite <- app_assoc in Hg.
  apply (proj1 (garr8_app SEGS _ _ _ _)) in Hg. destruct Hg as (Hg & _). exact Hg. }
unfold x_n in *.
split; [clear - Hs4096; lia|]. split; [clear - Hsceil Hji Hi; lia|].
split; [unfold amem_range; unfold YGcfStr.amem_range8 in Har8; clear - Har8 Hji Hi Hs4096; lia|].
split; [intros x Hx; apply HRA; clear - Hx Hji Hi; lia|].
intros _. apply (hull_sub _ (x_s X) (Z.of_nat (length (x_bs X)) + 1));
  [exact HHV | clear - Hji; lia | clear - Hji Hi; lia].
Qed.

(* ---- the seats ---- *)
Lemma psl_seat_H : forall X ch pos P lyc Sc Hpc Wc regsc memc mdc kc,
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc -> getr regsc 22 = w64 (x_SHF X pos) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [])) psl_ssH
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + 384))) memc (seg_rom SEGS))).
Proof.
intros X ch pos P lyc Sc Hpc Wc regsc memc mdc kc Hpre HCOM R22.
destruct (psl_frame_facts X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM) as (_ & _ & HF4096 & HFceil & HFsh & HSHF).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSHFr : SHADOW_OFF + 512 <= x_SHF X pos /\ x_SHF X pos + 8 <= kHighMemBeg).
{ rewrite HSHF. clear - HF4096 HFceil HC. unfold kHighMemBeg, SHADOW_OFF in *. split; lia. }
assert (R22b : base_val (Eimg (Ereg regsc [])) (Some 22%nat) = x_SHF X pos).
{ cbn [base_val]. rewrite (psl_ewv regsc [] 22 22%bv (x_SHF X pos) eq_refl eq_refl R22).
  apply unsigned_lit_small. clear - HSHFr. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
rewrite restrict_mkst_fx. unfold psl_ssH. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, psl_shf.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite R22b.
  split; [clear - HSHFr; unfold SHADOW_OFF in *; lia|].
  split; [clear - HSHFr; unfold kHighMemBeg in *; lia|].
  split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). exact (HFsh o ltac:(clear - Ho; lia)).
- apply pairwise_disjoint_of_extents. cbn. repeat constructor.
- split; [exact I | split; exact I].
Qed.

Lemma psl_seat_N : forall X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc SHS sv b,
  ps_pre X ch -> ps_next X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
  SHS = SHADOW_OFF + (x_s X + Z.of_nat i + 1) / 8 -> 0 <= sv < 8 -> 0 <= b < 256 ->
  aview SEGS (w_H Wc) memc SHS = Some sv ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (x_s X + Z.of_nat i + 1) 1 b ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [Z_to_bv 64 (x_F X pos); Z_to_bv 64 SHS; Z_to_bv 64 sv; Z_to_bv 64 b])) psl_ssN
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + 636))) memc (seg_rom SEGS))).
Proof.
intros X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc SHS sv b Hpre Hn HSe Hsvr Hbr Hsh Hby.
pose proof Hn as (HCOM & _ & Hi & _ & HLR & _ & R20 & R24 & HRB).
pose proof HLR as (_ & _ & _ & _ & R9 & _ & _ & _ & R23).
pose proof HRB as (W8 & W16 & _).
pose proof Hpre as (HFPRE & _).
destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
destruct (psl_frame_facts X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM) as (_ & _ & HF4096 & HFceil & _ & _).
destruct (psl_str_now X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOM) as (_ & _ & _ & Hs4096 & HsC & Hsloc).
unfold ASAN_CEIL in HsC.
assert (Har : 4096 <= x_s X + Z.of_nat i + 1 /\ x_s X + Z.of_nat i + 1 < YM05.alloc_ceiling)
  by (clear - Hs4096 HsC Hi; unfold x_n in *; lia).
assert (Hdl : x_s X + Z.of_nat i + 1 < kLowShadowBeg \/ kHighMemBeg <= x_s X + Z.of_nat i + 1)
  by (clear - Hsloc Hi; unfold x_n in *; lia).
assert (Hspr : YM05.alloc_ceiling + 208 <= x_sp X <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 HSTK208; unfold x_sp; lia).
assert (HRr : YM05.alloc_ceiling <= x_R X /\ x_R X + 88 <= x_sp X) by (clear - HR Hspr; unfold x_R; lia).
assert (HSHSr : SHADOW_OFF <= SHS < kHighMemBeg).
{ rewrite HSe. clear - Har Hdl HC. unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *. lia. }
assert (HFr64 : 0 <= x_F X pos < 2 ^ 64) by (clear - HF4096 HFceil HC; lia).
assert (HRr64 : 0 <= x_R X < 2 ^ 64) by (clear - HRr Hspr HC; lia).
lazymatch goal with |- st_ok_pi _ _ ?Ev _ _ =>
  assert (E9 : ew Ev 9 = Z_to_bv 64 (x_R X)) by exact (psl_ewv regsc _ 9 9%bv _ eq_refl eq_refl R9);
  assert (E20 : ew Ev 20 = Z_to_bv 64 (x_s X + Z.of_nat i + 1))
    by exact (psl_ewv regsc _ 20 20%bv _ eq_refl eq_refl R20);
  assert (E23 : ew Ev 23 = Z_to_bv 64 PS_SB) by exact (psl_ewv regsc _ 23 23%bv _ eq_refl eq_refl R23);
  assert (E24 : ew Ev 24 = Z_to_bv 64 (x_s X + Z.of_nat i))
    by exact (psl_ewv regsc _ 24 24%bv _ eq_refl eq_refl R24);
  assert (E32 : ew Ev 32 = Z_to_bv 64 (x_F X pos)) by (apply (psl_ewx regsc _ 0); reflexivity);
  assert (E33 : ew Ev 33 = Z_to_bv 64 SHS) by (apply (psl_ewx regsc _ 1); reflexivity);
  assert (E34 : ew Ev 34 = Z_to_bv 64 sv) by (apply (psl_ewx regsc _ 2); reflexivity);
  assert (E35 : ew Ev 35 = Z_to_bv 64 b) by (apply (psl_ewx regsc _ 3); reflexivity);
  assert (R9b : base_val Ev (Some 9%nat) = x_R X)
    by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; exact HRr64);
  assert (R20b : base_val Ev (Some 20%nat) = x_s X + Z.of_nat i + 1)
    by (cbn [base_val]; rewrite E20; apply unsigned_lit_small; clear - Har HC; lia);
  assert (R33b : base_val Ev (Some 33%nat) = SHS)
    by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; clear - HSHSr; unfold SHADOW_OFF, kHighMemBeg in *; lia)
end.
rewrite restrict_mkst_fx. unfold psl_ssN. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold psl_shb, psl_byt, psl_rblk.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
    unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite R33b.
    split; [clear - HSHSr; unfold SHADOW_OFF in *; lia|].
    split; [clear - HSHSr; unfold kHighMemBeg in *; lia|].
    split; [intros o Ho; exfalso; clear - Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ SHS 0 1 (SOff 34 0) sv (psl_atom _ 34 sv E34 ltac:(clear - Hsvr; lia))
      (psl_rng_b sv ltac:(clear - Hsvr; lia)) psl_w1).
    rewrite Z.add_0_r. exact (val_mem1_of_aview _ _ _ _ Hsh).
  + rewrite R20b.
    split; [clear - Har; lia|]. split; [clear - Har HC; lia|].
    split; [intros o Ho; exfalso; clear - Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ (x_s X + Z.of_nat i + 1) 0 1 (SOff 35 0) b
      (psl_atom _ 35 b E35 ltac:(clear - Hbr; lia)) (psl_rng_b b Hbr) psl_w1).
    rewrite Z.add_0_r. exact Hby.
  + rewrite R9b.
    split; [clear - HRr64; lia|]. split; [clear - HRr Hspr; lia|].
    split; [intros o Ho; exfalso; clear - Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS _ _ (x_R X) 8 8 (SOff 32 0) (x_F X pos) (psl_atom _ 32 _ E32 HFr64)
        (psl_rng_w _ HFr64) psl_w8).
      exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W8).
    * apply (chunk_ok_val SEGS _ _ (x_R X) 16 8 (SOff 32 0) (x_F X pos) (psl_atom _ 32 _ E32 HFr64)
        (psl_rng_w _ HFr64) psl_w8).
      exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W16).
- apply pairwise_disjoint_of_extents.
  unfold psl_shb, psl_byt, psl_rblk, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite R33b, R20b, R9b.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  clear - HSHSr Hdl Har HRr HC. unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *. repeat split; lia.
- unfold psl_factsN. split; [|split].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E34, E35, !unsigned_lit_small by (clear - Hsvr Hbr; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
    clear - Hsvr Hbr. repeat split; lia.
  + exact I.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply (psl_shadow_decl1 _ 24 23 33 (x_s X + Z.of_nat i) PS_SB E24 ltac:(clear - Har; lia)
      ltac:(clear - Har HC; lia) E23).
    rewrite E33, HSe. reflexivity.
Qed.

(* ---- THE LOOP HEAD (+ 0x180): the byte tests, then the run put of a special byte (+ 0x1c4) and the escape join
   (+ 0x1c8), or the re-poison, the UBSan overflow check (+ 0x1ac) and the next join (+ 0x27c). All after a put: the
   stretches, the branches and the run put at wle' SEGS RZ_cf, the continuations and the conclusion SRr' ---- *)
Lemma psl_head_step : forall (fx0 : YK11.FPState) X ch, ps_pre X ch -> ps_s0 X -> forall i,
  (forall pos P lyc Sc Hpc Wc regsc memc mdc kc, ps_esc X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regsc (Z_to_bv 64 (BASE + (AF_put_string + 456))) memc (seg_rom SEGS)) mdc)
       (ps_Qfin fx0 X)) ->
  (forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_next X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regsc (Z_to_bv 64 (BASE + (AF_put_string + 636))) memc (seg_rom SEGS)) mdc)
       (ps_Qfin fx0 X)) ->
  forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_head X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regsc (Z_to_bv 64 (BASE + (AF_put_string + 384))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin fx0 X).
Proof.
intros fx0 X ch Hpre HS0 i ESC NEXT pos j P lyc Sc Hpc Wc regsc memc mdc kc Hh.
unfold SRr'.
destruct fx0 as [fr0 fc0].
pose proof Hh as (HCOMc & (Hji & Hi) & Hplan & HLR & R18 & R20 & R24 & R25 & HRB).
pose proof HLR as (R2 & R3 & R4 & R8 & R9 & R19 & R21 & R22 & R23).
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HWIN0 & Ho1 & Ho2 & _).
destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & _ & Htop2).
pose proof HWIN0 as (_ & _ & Hdtop & _).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
destruct (psl_frame_facts X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOMc) as (_ & EF & HF4096 & HFceil & _ & HSHF).
destruct (psl_str_now X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOMc) as (HCSTR & _ & _ & Hs4096 & HsC & _).
unfold ASAN_CEIL in HsC.
pose proof HCSTR as (Hg & _).
assert (Hcr : 0 <= nth i (x_bs X) 0 < 256).
{ destruct (Hg i ltac:(rewrite length_app; cbn [length]; clear - Hi; lia)) as (_ & Hr).
  rewrite app_nth1 in Hr by (clear - Hi; lia). exact Hr. }
assert (Hc64 : 0 <= nth i (x_bs X) 0 < 2 ^ 64) by (clear - Hcr; lia).
assert (Hile : (i <= length (x_bs X))%nat) by (clear - Hi; lia).
assert (Hn0 : Z.of_nat j <= Z.of_nat i < x_n X) by (clear - Hji Hi; unfold x_n; lia).
assert (HSHFr : SHADOW_OFF + 512 <= x_SHF X pos /\ x_SHF X pos + 8 <= kHighMemBeg).
{ rewrite HSHF. clear - HF4096 HFceil HC. unfold kHighMemBeg, SHADOW_OFF in *. split; lia. }
assert (Hspr : YM05.alloc_ceiling + 208 <= x_sp X <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 HSTK208; unfold x_sp; lia).
assert (HRr : YM05.alloc_ceiling <= x_R X /\ x_R X + 88 <= x_sp X) by (clear - HR Hspr; unfold x_R; lia).
assert (Horng : 0 <= x_o X < 2 ^ 64) by (clear - Ho1 Ho2 Hdtop Htop2 Hshi H47 Hspr HC; unfold x_sp in *; lia).
assert (Hsjr : 0 <= x_s X + Z.of_nat j < 2 ^ 64) by (clear - Hs4096 HsC HC Hn0; lia).
assert (Hsir : 0 <= x_s X + Z.of_nat i < 2 ^ 64) by (clear - Hs4096 HsC HC Hn0; lia).
assert (Hv20r : 0 <= x_s X + Z.of_nat i + 1 < 2 ^ 64) by (clear - Hs4096 HsC HC Hn0; lia).
assert (Hv20m : 0 <= x_s X + Z.of_nat i + 1 + -1 < 2 ^ 64) by (clear - Hs4096 HsC HC Hn0; lia).
assert (Hblen : length (firstn (i - j) (skipn j (x_bs X))) = (i - j)%nat)
  by (rewrite length_firstn, length_skipn; clear - Hji Hi; lia).
pose proof (AF_ps_ret_k 456 (proj1 psl_456) (proj2 psl_456)) as (H456 & H456b).
assert (H456c : BASE + (AF_put_string + 456) < YM05.alloc_ceiling) by (apply ps_ret_lt_ceil; cbn [In]; tauto).
(* the seat and its env's values *)
pose proof (psl_seat_H X ch pos P lyc Sc Hpc Wc regsc memc mdc kc Hpre HCOMc R22) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc []))) by apply Eimg_env.
assert (E18 : ew (Eimg (Ereg regsc [])) 18 = Z_to_bv 64 (x_s X + Z.of_nat j))
  by exact (psl_ewv regsc [] 18 18%bv _ eq_refl eq_refl R18).
assert (E19 : ew (Eimg (Ereg regsc [])) 19 = Z_to_bv 64 (x_o X))
  by exact (psl_ewv regsc [] 19 19%bv _ eq_refl eq_refl R19).
assert (E20 : ew (Eimg (Ereg regsc [])) 20 = Z_to_bv 64 (x_s X + Z.of_nat i + 1))
  by exact (psl_ewv regsc [] 20 20%bv _ eq_refl eq_refl R20).
assert (E24 : ew (Eimg (Ereg regsc [])) 24 = Z_to_bv 64 (x_s X + Z.of_nat i))
  by exact (psl_ewv regsc [] 24 24%bv _ eq_refl eq_refl R24).
assert (E25 : ew (Eimg (Ereg regsc [])) 25 = Z_to_bv 64 (nth i (x_bs X) 0))
  by exact (psl_ewv regsc [] 25 25%bv _ eq_refl eq_refl R25).
assert (R22u : bv_unsigned (ew (Eimg (Ereg regsc [])) 22) = x_SHF X pos).
{ rewrite (psl_ewv regsc [] 22 22%bv (x_SHF X pos) eq_refl eq_refl R22).
  apply unsigned_lit_small. clear - HSHFr. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
assert (R22b : base_val (Eimg (Ereg regsc [])) (Some 22%nat) = x_SHF X pos) by (cbn [base_val]; exact R22u).
(* the run put's arguments and the escape join's s10 / s11, as the engine computes them (MEASURED forms) *)
assert (Ha2 : sv_denot (Eimg (Ereg regsc [])) (SAlu ALU_ADD (SMd M_MUL (SOff 18 0) (SLit (-1))) (SOff 24 0)) =
  Z_to_bv 64 (Z.of_nat (i - j))).
{ rewrite (psl_sub_val _ 24 18 (x_s X + Z.of_nat i) (x_s X + Z.of_nat j) E24 E18) by (clear - Hsjr Hsir Hji; lia).
  f_equal. clear - Hji; lia. }
assert (Ha26 : sv_denot (Eimg (Ereg regsc [])) (SOff 20 (-1)) = Z_to_bv 64 (x_s X + Z.of_nat i))
  by (apply (psl_atom_offv _ 20 (x_s X + Z.of_nat i + 1)); [exact E20 | exact Hv20r | ring | exact Hsir]).
assert (Ha27 : sv_denot (Eimg (Ereg regsc [])) (SAlu ALU_AND (SOff 25 0) (SLit 255)) =
  Z_to_bv 64 (nth i (x_bs X) 0)) by exact (psl_and_val _ 25 _ E25 Hcr).
pose proof HCOMc as (HJ & _ & _ & _ & HPM & _).
idtac "PSL-HEAD-SETUP".
(* ---- the rest is ONE proof-mode command: its local closures are the head's leaves ---- *)
(* the stretches' one write window is u's shadow byte (SHF + 4), in F's shadow granules *)
let awrRun := fun _ => (let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in
  let Hx := fresh "Hx" in
  intros a (r & Hin & Hx); cbn [In ss_mem psl_ssH] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi psl_shf] in Hx; rewrite ?R22b in Hx;
      unfold awr_byte, in_frames; right; right; right; exists 0, pos; split; [left; reflexivity|];
      right; unfold in_zr; cbn [fst snd]; unfold shadow_addr; change (fs_frame_bytes 0) with 64;
      change (64 / 8) with 8; rewrite EF; rewrite HSHF in Hx; clear - Hx; lia | ]);
  try destruct Hin) in
let nwrW := fun _ => (let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros x (r & Hin & Hx); cbn [In ss_mem psl_ssH] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi psl_shf] in Hx; rewrite ?R22b in Hx; clear - Hx; lia | ]);
  try destruct Hin) in
let nwrQ := fun _ => (let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros x (r & Hin & Hx); cbn [In ss_mem psl_ssH] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi psl_shf] in Hx; rewrite ?R22b in Hx;
      right; right; clear - Hx HSHFr; unfold SHADOW_OFF, kHighMemBeg in *; lia | ]);
  try destruct Hin) in
(* the join invariant and the R block at the end memory of each stretch *)
let pcom := fun _ => (let H := fresh "HCOMn" in
  eassert (H : ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc _ _ kc);
  [ eapply ps_common_frameR; [exact Hpre | exact HCOMc | exact HJ | exact HPM | eassumption | nwrQ ()] | ];
  clear HCOMc; rename H into HCOMc) in
let prb := fun _ => (lazymatch goal with |- SRrG _ _ _ (mkCfg ?msx _) _ =>
  let H := fresh "HRBn" in
  assert (H : ps_rblock X pos Wc (ms_mem msx));
  [ apply (psl_rblock_keep X pos Wc Wc _ (ms_mem msx) HRB);
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    eapply (psl_keep_av _ _ _ _ _ (x_SHF X pos + 4) (x_SHF X pos + 5));
    [ eassumption | nwrW () | clear - Ha HRr Hspr HC; lia
    | right; clear - Ha HRr HSHFr HC; unfold SHADOW_OFF, kHighMemBeg in *; lia ]
  | ]; clear HRB; rename H into HRB end) in
(* ---- the leaf at the next join (+ 0x27c): the byte is put as itself, the run [j, i + 1) is pending ---- *)
let next_leaf := fun _ => (idtac "PSL-NEXT-LEAF";
  lazymatch goal with Hns : WriterSpec.special (nth i (x_bs X) 0) = false |- _ =>
  pcom (); prb (); pmkst HS;
  lazymatch goal with |- context [BASE + ?k] =>
    replace k with (AF_put_string + 636) by (unfold AF_put_string; rewrite (proj2 B_entry_put_string);
      vm_compute; reflexivity) end;
  eapply (NEXT pos j P lyc Sc Hpc Wc); unfold ps_next;
  split; [exact HCOMc|];
  split; [clear - Hji; lia|];
  split; [exact Hi|];
  split; [exact (psl_plan_ns (x_bs X) P i j Hji Hi Hns Hplan)|];
  split; [apply (psl_lregs_eq X pos regsc);
          [ exact (psl_reg_keep _ regsc _ _ _ 2%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 3%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 4%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 8%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 9%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 19%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 21%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 22%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 23%bv HS ltac:(vm_compute; reflexivity))
          | exact HLR ]|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 18%bv HS ltac:(vm_compute; reflexivity)); exact R18|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 20%bv HS ltac:(vm_compute; reflexivity)); exact R20|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 24%bv HS ltac:(vm_compute; reflexivity)); exact R24|];
  exact HRB end) in
(* ---- the leaf at the run put (+ 0x1c4), and the escape join it returns to (+ 0x1c8) ---- *)
let put_leaf := fun _ => (idtac "PSL-PUT-LEAF";
  lazymatch goal with
  | Hsp : WriterSpec.special (nth i (x_bs X) 0) = true |- SRrG _ _ _ (mkCfg ?msx _) _ =>
    pcom (); prb ();
    let HSH4 := fresh "HSH4" in
    assert (HSH4 : aview SEGS (w_H Wc) (ms_mem msx) (x_SHF X pos + 4) = Some 0);
    [ lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
        let rv := eval vm_compute in (nth_error (ss_mem ssx) 0) in
        lazymatch rv with
        | Some ?rg =>
          let Hrg := fresh "Hrg" in
          pose proof (st_ok_region_nth SEGS Ev ssx _ 0 rg HS ltac:(vm_compute; reflexivity)) as Hrg;
          cbn [ms_mem restrict mkst] in Hrg;
          apply psl_aview0;
          exact (field_of_region SEGS Ev _ 22%nat (x_SHF X pos) _ 4 5 4 5 4 1%N (SLit 0) 0 Hrg R22u
                   ltac:(cbn [In]; left; reflexivity) ltac:(cbn [sv_denot]; reflexivity)
                   (psl_rng_b 0 psl_rng0) psl_w1)
        end end
    | ];
    pmkst HS;
    apply (ps_put_step X ch pos P (firstn (i - j) (skipn j (x_bs X)))
             (WriterSpec.esc (nth i (x_bs X) 0) :: WriterSpec.spieces_run [] (skipn (S i) (x_bs X)) ++ [[34]])
             lyc Sc Hpc Wc (ms_regs msx) (ms_mem msx) _ kc
             (Z_to_bv 64 (BASE + (AF_put_string + 456))) (x_s X + Z.of_nat j));
    [ exact HFRMx
    | exact Hpre
    | exact HS0
    | exact HCOMc
    | exact (proj1 (psl_plan_esc (x_bs X) P i j Hji Hi Hsp Hplan))
    | unfold spZ; rewrite (psl_reg_keep_ok _ regsc _ _ _ 2%bv HS ltac:(vm_compute; reflexivity)), R2;
      unfold w64; apply unsigned_lit_small; clear - HRr Hspr HC; lia
    | rewrite (psl_reg_keep_ok _ regsc _ _ _ 3%bv HS ltac:(vm_compute; reflexivity)), R3; exact Hgp
    | rewrite (psl_reg_keep_ok _ regsc _ _ _ 4%bv HS ltac:(vm_compute; reflexivity)), R4; exact Htp
    | exact (psl_reg_val_ok _ _ _ _ 1%bv (SOff A_TEXT (AF_put_string + 456)) _ HS
               ltac:(vm_compute; reflexivity) (codeptr_val _ _ HEI))
    | apply ret_ok_codeptr_v; [exact (proj1 H456) | exact (proj2 H456)]
    | rewrite unsigned_lit_small by (clear - H456b H456c HC; lia); exact H456b
    | rewrite unsigned_lit_small by (clear - H456b H456c HC; lia); exact H456c
    | unfold s0Z; rewrite (psl_reg_keep_ok _ regsc _ _ _ 8%bv HS ltac:(vm_compute; reflexivity)), R8;
      unfold w64; apply unsigned_lit_small; clear - Hspr HC; lia
    | exact (psl_reg_val_ok _ _ _ _ 10%bv (SOff 19 0) (x_o X) HS ltac:(vm_compute; reflexivity)
               (psl_atom _ 19 _ E19 Horng))
    | exact (psl_reg_val_ok _ _ _ _ 11%bv (SOff 18 0) (x_s X + Z.of_nat j) HS ltac:(vm_compute; reflexivity)
               (psl_atom _ 18 _ E18 Hsjr))
    | rewrite Hblen;
      exact (psl_reg_val_ok _ _ _ _ 12%bv (SAlu ALU_ADD (SMd M_MUL (SOff 18 0) (SLit (-1))) (SOff 24 0))
               (Z.of_nat (i - j)) HS ltac:(vm_compute; reflexivity) Ha2)
    | exact (psl_src_run X ch pos P lyc Sc Hpc Wc (ms_mem msx) _ kc i j Hpre HCOMc Hji Hile)
    | let Lamx := fresh "Lamx" in let bufx := fresh "bufx" in let capx := fresh "capx" in
      let Hk := fresh "Hk" in let Hd := fresh "Hd" in
      intros Lamx bufx capx Hk Hd _ _; exact (psl_home_run X lyc Sc Lamx bufx capx i j Hji Hile Hk Hd)
    | (* the escape join (+ 0x1c8) *)
      let ly2 := fresh "ly2" in let S2 := fresh "S2" in let Hp2 := fresh "Hp2" in let W2 := fresh "W2" in
      let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
      let k2 := fresh "k2" in let HCOM2 := fresh "HCOM2" in let HP2 := fresh "HP2" in
      let KW2 := fresh "KW2" in let KP2 := fresh "KP2" in let KF2 := fresh "KF2" in
      intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HCOM2 HP2 KW2 KP2 KF2;
      idtac "PSL-ESC-JOIN";
      eapply (ESC pos (P ++ [firstn (i - j) (skipn j (x_bs X))]) ly2 S2 Hp2 W2 regs2 mem2 md2);
      unfold ps_esc;
      split; [exact HCOM2|];
      split; [exact Hi|];
      split; [exact Hsp|];
      split; [exact (proj2 (psl_plan_esc (x_bs X) P i j Hji Hi Hsp Hplan))|];
      split; [apply (psl_lregs_eq X pos regsc regs2);
              [ exact (psl_pres_keep _ regsc _ _ _ regs2 2%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity))
              | exact (psl_pres_keep _ regsc _ _ _ regs2 3%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity))
              | exact (psl_pres_keep _ regsc _ _ _ regs2 4%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity))
              | exact (psl_pres_keep _ regsc _ _ _ regs2 8%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity))
              | exact (psl_pres_keep _ regsc _ _ _ regs2 9%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity))
              | exact (psl_pres_keep _ regsc _ _ _ regs2 19%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity))
              | exact (psl_pres_keep _ regsc _ _ _ regs2 21%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity))
              | exact (psl_pres_keep _ regsc _ _ _ regs2 22%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity))
              | exact (psl_pres_keep _ regsc _ _ _ regs2 23%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity))
              | exact HLR ]|];
      split; [rewrite (psl_pres_keep _ regsc _ _ _ regs2 20%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity));
              exact R20|];
      split; [rewrite (psl_pres_keep _ regsc _ _ _ regs2 24%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity));
              exact R24|];
      split; [rewrite (psl_pres_keep _ regsc _ _ _ regs2 25%bv HS HP2 eq_refl ltac:(vm_compute; reflexivity));
              exact R25|];
      split; [exact (psl_pres_val _ _ _ _ regs2 26%bv (SOff 20 (-1)) _ HS HP2 eq_refl
                       ltac:(vm_compute; reflexivity) Ha26)|];
      split; [exact (psl_pres_val _ _ _ _ regs2 27%bv (SAlu ALU_AND (SOff 25 0) (SLit 255)) _ HS HP2 eq_refl
                       ltac:(vm_compute; reflexivity) Ha27)|];
      split; [rewrite (KF2 (x_SHF X pos + 4) ltac:(right; clear - HSHFr; lia)); exact HSH4|];
      apply (psl_rblock_keep X pos Wc W2 (ms_mem msx) mem2 HRB);
      let aa := fresh "aa" in let Haa := fresh "Haa" in
      intros aa Haa; apply KW2; clear - Haa HRr; lia ]
  end) in
(* ---- the byte tests (+ 0x18c `beq s9, 34`, + 0x194 `beq s9, 92`, + 0x19c `bgeu 31, s9`) and the UBSan check of the
   ordinary byte (+ 0x1ac `bne s10, -1`) ---- *)
pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 636);
[ awrRun ()
| pcom (); prb (); idtac "PSL-B1"; pnt_branch BR HS;
  [ (* the byte is a double quote *)
    lazymatch goal with Hb : branch_taken BC_EQ (sv_denot _ (SOff 25 0)) (sv_denot _ (SLit 34)) = true |- _ =>
      rewrite branch_eq_U, (U_atom _ 25 _ E25 Hc64), U_SLit in Hb; change (zcanon 34) with 34 in Hb;
      apply Z.eqb_eq in Hb;
      assert (Hsp : WriterSpec.special (nth i (x_bs X) 0) = true)
        by (unfold WriterSpec.special; rewrite Hb; reflexivity) end;
    pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 636); [ awrRun () | put_leaf () ]
  | lazymatch goal with Hb : branch_taken BC_EQ (sv_denot _ (SOff 25 0)) (sv_denot _ (SLit 34)) = false |- _ =>
      rewrite branch_eq_U, (U_atom _ 25 _ E25 Hc64), U_SLit in Hb; change (zcanon 34) with 34 in Hb;
      apply Z.eqb_neq in Hb; rename Hb into Hb1 end;
    pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 636);
    [ awrRun ()
    | pcom (); prb (); idtac "PSL-B2"; pnt_branch BR HS;
      [ (* the byte is a backslash *)
        lazymatch goal with Hb : branch_taken BC_EQ (sv_denot _ (SOff 25 0)) (sv_denot _ (SLit 92)) = true |- _ =>
          rewrite branch_eq_U, (U_atom _ 25 _ E25 Hc64), U_SLit in Hb; change (zcanon 92) with 92 in Hb;
          apply Z.eqb_eq in Hb;
          assert (Hsp : WriterSpec.special (nth i (x_bs X) 0) = true)
            by (unfold WriterSpec.special; rewrite Hb; reflexivity) end;
        pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 636); [ awrRun () | put_leaf () ]
      | lazymatch goal with Hb : branch_taken BC_EQ (sv_denot _ (SOff 25 0)) (sv_denot _ (SLit 92)) = false |- _ =>
          rewrite branch_eq_U, (U_atom _ 25 _ E25 Hc64), U_SLit in Hb; change (zcanon 92) with 92 in Hb;
          apply Z.eqb_neq in Hb; rename Hb into Hb2 end;
        pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 636);
        [ awrRun ()
        | pcom (); prb (); idtac "PSL-B3"; pnt_branch BR HS;
          [ (* the byte is a control character *)
            lazymatch goal with Hb : branch_taken BC_GEU (sv_denot _ (SLit 31)) (sv_denot _ (SOff 25 0)) = true |- _ =>
              rewrite branch_geu_U, U_SLit, (U_atom _ 25 _ E25 Hc64) in Hb; change (zcanon 31) with 31 in Hb;
              apply Bool.negb_true_iff, Z.ltb_ge in Hb;
              assert (Hsp : WriterSpec.special (nth i (x_bs X) 0) = true)
                by (unfold WriterSpec.special; apply Bool.orb_true_iff; right; apply Z.ltb_lt; clear - Hb; lia) end;
            pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 636); [ awrRun () | put_leaf () ]
          | (* the byte is put as itself: the re-poison (+ 0x1a4) and the UBSan check (+ 0x1ac) *)
            lazymatch goal with Hb : branch_taken BC_GEU (sv_denot _ (SLit 31)) (sv_denot _ (SOff 25 0)) = false |- _ =>
              rewrite branch_geu_U, U_SLit, (U_atom _ 25 _ E25 Hc64) in Hb; change (zcanon 31) with 31 in Hb;
              apply Bool.negb_false_iff, Z.ltb_lt in Hb; rename Hb into Hb3 end;
            assert (Hns : WriterSpec.special (nth i (x_bs X) 0) = false)
              by (unfold WriterSpec.special; apply Bool.orb_false_iff;
                  split; [apply Bool.orb_false_iff; split; apply Z.eqb_neq; [exact Hb1 | exact Hb2]
                         | apply Z.ltb_ge; clear - Hb3; lia]);
            pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 636);
            [ awrRun ()
            | pcom (); prb (); idtac "PSL-B4"; pnt_branch BR HS;
              [ (* s + i <> 2^64 - 1: to the next join (+ 0x27c) *)
                pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 636); [ awrRun () | next_leaf () ]
              | (* NOT TAKEN: the fall-through to the UBSan trap (+ 0x1b0 `j + 0x38c`): s10 = s + i lies below the
                   allocation ceiling, so it is not 2^64 - 1 *)
                exfalso;
                lazymatch goal with Hb : branch_taken BC_NE (sv_denot _ (SOff 20 (-1))) _ = false |- _ =>
                  rewrite branch_ne_U, (U_atom_off _ 20 _ (-1) E20 Hv20r Hv20m), U_SLit in Hb;
                  rewrite zcanon_id in Hb by (clear - HC; unfold M64; lia);
                  apply Bool.negb_false_iff, Z.eqb_eq in Hb;
                  clear - Hb Hs4096 HsC HC Hn0; lia end ] ] ] ] ] ] ] ].
Qed.

(* ---- THE NEXT JOIN (+ 0x27c): s[i + 1]'s shadow-checked load, then the head at i + 1 (+ 0x180) or, on the NUL, the
   tail join (+ 0x2c8). All after a put: the stretches and branches at wle' SEGS RZ_cf, the continuations and the
   conclusion SRr' ---- *)
Lemma psl_next_step : forall (fx0 : YK11.FPState) X ch, ps_pre X ch -> ps_s0 X -> forall i,
  (forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_head X pos (S i) j P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regsc (Z_to_bv 64 (BASE + (AF_put_string + 384))) memc (seg_rom SEGS)) mdc)
       (ps_Qfin fx0 X)) ->
  (forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_tail X pos j P lyc Sc Hpc Wc regsc memc mdc kc ->
     SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regsc (Z_to_bv 64 (BASE + (AF_put_string + 712))) memc (seg_rom SEGS)) mdc)
       (ps_Qfin fx0 X)) ->
  forall pos j P lyc Sc Hpc Wc regsc memc mdc kc, ps_next X pos i j P lyc Sc Hpc Wc regsc memc mdc kc ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regsc (Z_to_bv 64 (BASE + (AF_put_string + 636))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin fx0 X).
Proof.
intros fx0 X ch Hpre HS0 i KH KT pos j P lyc Sc Hpc Wc regsc memc mdc kc Hn.
unfold SRr'.
destruct fx0 as [fr0 fc0].
pose proof Hn as (HCOMc & Hji & Hi & Hplan & HLR & R18 & R20 & R24 & HRB).
pose proof HLR as (R2 & R3 & R4 & R8 & R9 & R19 & R21 & R22 & R23).
pose proof Hpre as (HFPRE & _).
destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
destruct (psl_frame_facts X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOMc) as (_ & _ & HF4096 & HFceil & _ & _).
destruct (psl_str_now X ch pos P lyc Sc Hpc Wc memc mdc kc Hpre HCOMc) as (HCSTR & HRA & _ & Hs4096 & HsC & _).
unfold ASAN_CEIL in HsC.
pose proof HCSTR as (Hg & Hnz).
assert (HSle : (S i <= length (x_bs X))%nat) by (clear - Hi; lia).
assert (Hspr : YM05.alloc_ceiling + 208 <= x_sp X <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 HSTK208; unfold x_sp; lia).
assert (HRr : YM05.alloc_ceiling <= x_R X /\ x_R X + 88 <= x_sp X) by (clear - HR Hspr; unfold x_R; lia).
assert (HFr64 : 0 <= x_F X pos < 2 ^ 64) by (clear - HF4096 HFceil HC; lia).
assert (Hsir : 0 <= x_s X + Z.of_nat i < 2 ^ 64) by (clear - Hs4096 HsC HC Hi; unfold x_n in *; lia).
assert (Hv20r : 0 <= x_s X + Z.of_nat i + 1 < 2 ^ 64) by (clear - Hs4096 HsC HC Hi; unfold x_n in *; lia).
(* s[i + 1] (the byte c1, possibly the NUL) and its shadow byte sv *)
destruct (Hg (S i) ltac:(rewrite length_app; cbn [length]; clear - Hi; lia)) as (Hbv & Hbr).
replace (x_s X + Z.of_nat (S i)) with (x_s X + Z.of_nat i + 1) in Hbv by (clear - Hi; lia).
set (c1 := nth (S i) (x_bs X ++ [0]) 0) in Hbv, Hbr.
assert (Ec1 : c1 = nth (S i) (x_bs X ++ [0]) 0) by reflexivity.
clearbody c1.
assert (Hc164 : 0 <= c1 < 2 ^ 64) by (clear - Hbr; lia).
destruct (HRA (x_s X + Z.of_nat i + 1) ltac:(clear - Hi; unfold x_n; lia)) as (sv & Hsv & Hsok).
set (SHS := shadow_of_addr SHADOW_OFF (x_s X + Z.of_nat i + 1)) in Hsv.
assert (ESHS : SHS = SHADOW_OFF + (x_s X + Z.of_nat i + 1) / 8) by reflexivity.
clearbody SHS.
assert (Hsvr : 0 <= sv < 8) by (unfold saddr_ok in Hsok; clear - Hsok; lia).
assert (Hsv64 : 0 <= sv < 2 ^ 64) by (clear - Hsvr; lia).
(* the seat and its env's values *)
pose proof (psl_seat_N X ch pos i j P lyc Sc Hpc Wc regsc memc mdc kc SHS sv c1 Hpre Hn ESHS Hsvr Hbr Hsv Hbv) as HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (HEI : img_env VAL A_LIM Ev) by apply Eimg_env;
  assert (E20 : ew Ev 20 = Z_to_bv 64 (x_s X + Z.of_nat i + 1))
    by exact (psl_ewv regsc _ 20 20%bv _ eq_refl eq_refl R20);
  assert (E24 : ew Ev 24 = Z_to_bv 64 (x_s X + Z.of_nat i))
    by exact (psl_ewv regsc _ 24 24%bv _ eq_refl eq_refl R24);
  assert (E32 : ew Ev 32 = Z_to_bv 64 (x_F X pos)) by (apply (psl_ewx regsc _ 0); reflexivity);
  assert (E34 : ew Ev 34 = Z_to_bv 64 sv) by (apply (psl_ewx regsc _ 2); reflexivity);
  assert (E35 : ew Ev 35 = Z_to_bv 64 c1) by (apply (psl_ewx regsc _ 3); reflexivity);
  assert (Hv20 : sv_denot Ev (SOff 20 1) = Z_to_bv 64 (x_s X + Z.of_nat (S i) + 1))
    by (apply (psl_atom_offv _ 20 (x_s X + Z.of_nat i + 1)); [exact E20 | exact Hv20r | clear - Hi; lia
        | clear - Hs4096 HsC HC Hi; unfold x_n in *; lia]);
  assert (Hv24 : sv_denot Ev (SOff 24 1) = Z_to_bv 64 (x_s X + Z.of_nat (S i)))
    by (apply (psl_atom_offv _ 24 (x_s X + Z.of_nat i)); [exact E24 | exact Hsir | clear - Hi; lia
        | clear - Hs4096 HsC HC Hi; unfold x_n in *; lia]);
  assert (HvF : sv_denot Ev (SOff 32 0) = Z_to_bv 64 (x_F X pos)) by exact (psl_atom _ 32 _ E32 HFr64)
end.
pose proof HCOMc as (HJ & _ & _ & _ & HPM & _).
idtac "PSL-NEXT-SETUP".
(* ---- the rest is ONE proof-mode command: its local closures are the two leaves ---- *)
(* the stretches write nothing (every region of the seat is read-only) *)
let awrN := fun _ => (let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros a (r & Hin & Hx); cbn [In ss_mem psl_ssN] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi psl_shb psl_byt psl_rblk] in Hx; exfalso; clear - Hx; lia | ]);
  try destruct Hin) in
let nwrN := fun _ => (let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros x (r & Hin & Hx); cbn [In ss_mem psl_ssN] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi psl_shb psl_byt psl_rblk] in Hx; exfalso; clear - Hx; lia | ]);
  try destruct Hin) in
let pcom := fun _ => (let H := fresh "HCOMn" in
  eassert (H : ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc _ _ kc);
  [ eapply ps_common_frameR; [exact Hpre | exact HCOMc | exact HJ | exact HPM | eassumption | nwrN ()] | ];
  clear HCOMc; rename H into HCOMc) in
let prb := fun _ => (lazymatch goal with |- SRrG _ _ _ (mkCfg ?msx _) _ =>
  let H := fresh "HRBn" in
  assert (H : ps_rblock X pos Wc (ms_mem msx));
  [ apply (psl_rblock_keep X pos Wc Wc _ (ms_mem msx) HRB);
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    eapply (psl_keep_av _ _ _ _ _ 0 0);
    [ eassumption | nwrN () | clear - Ha HRr Hspr HC; lia | right; clear - Ha HRr HC; lia ]
  | ]; clear HRB; rename H into HRB end) in
(* ---- the leaf at the head of byte i + 1 (+ 0x180) ---- *)
let leafH := fun _ => (idtac "PSL-LEAF-H";
  lazymatch goal with Hc1nz : c1 <> 0 |- _ =>
  pcom (); prb (); pmkst HS;
  lazymatch goal with |- context [BASE + ?k] =>
    replace k with (AF_put_string + 384) by (unfold AF_put_string; rewrite (proj2 B_entry_put_string);
      vm_compute; reflexivity) end;
  let HSi := fresh "HSi" in let Hbeq := fresh "Hbeq" in
  destruct (psl_byte_in (x_bs X) (S i) HSle ltac:(rewrite <- Ec1; exact Hc1nz)) as (HSi & Hbeq);
  eapply (KH pos j P lyc Sc Hpc Wc); unfold ps_head;
  split; [exact HCOMc|];
  split; [split; [exact Hji | exact HSi]|];
  split; [exact Hplan|];
  split; [apply (psl_lregs_eq X pos regsc);
          [ exact (psl_reg_keep _ regsc _ _ _ 2%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 3%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 4%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 8%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 9%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 19%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 21%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 22%bv HS ltac:(vm_compute; reflexivity))
          | exact (psl_reg_keep _ regsc _ _ _ 23%bv HS ltac:(vm_compute; reflexivity))
          | exact HLR ]|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 18%bv HS ltac:(vm_compute; reflexivity)); exact R18|];
  split; [exact (psl_reg_val _ _ _ _ 20%bv (SOff 20 1) _ HS ltac:(vm_compute; reflexivity) Hv20)|];
  split; [exact (psl_reg_val _ _ _ _ 24%bv (SOff 24 1) _ HS ltac:(vm_compute; reflexivity) Hv24)|];
  split; [rewrite (psl_reg_val _ _ _ _ 25%bv (SOff 35 0) c1 HS ltac:(vm_compute; reflexivity)
                     (psl_atom _ 35 c1 E35 Hc164)), Ec1, Hbeq; reflexivity|];
  exact HRB end) in
(* ---- the leaf at the tail join (+ 0x2c8): s[i + 1] is the NUL ---- *)
let leafT := fun _ => (idtac "PSL-LEAF-T";
  lazymatch goal with Hc10 : c1 = 0 |- _ =>
  pcom (); pmkst HS;
  lazymatch goal with |- context [BASE + ?k] =>
    replace k with (AF_put_string + 712) by (unfold AF_put_string; rewrite (proj2 B_entry_put_string);
      vm_compute; reflexivity) end;
  let Hlen := fresh "Hlen" in
  pose proof (psl_byte_nul (x_bs X) (S i) Hnz HSle ltac:(rewrite <- Ec1; exact Hc10)) as Hlen;
  eapply (KT pos j P lyc Sc Hpc Wc); unfold ps_tail;
  split; [exact HCOMc|];
  split; [rewrite <- Hlen; exact Hji|];
  split; [exact (psl_plan_tail (x_bs X) P i j Hji Hlen Hplan)|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 2%bv HS ltac:(vm_compute; reflexivity)); exact R2|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 3%bv HS ltac:(vm_compute; reflexivity)); exact R3|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 4%bv HS ltac:(vm_compute; reflexivity)); exact R4|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 8%bv HS ltac:(vm_compute; reflexivity)); exact R8|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 9%bv HS ltac:(vm_compute; reflexivity)); exact R9|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 19%bv HS ltac:(vm_compute; reflexivity)); exact R19|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 18%bv HS ltac:(vm_compute; reflexivity)); exact R18|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 20%bv HS ltac:(vm_compute; reflexivity)), R20; unfold w64;
          f_equal; clear - Hlen; unfold x_n; lia|];
  split; [exact (psl_reg_val _ _ _ _ 21%bv (SOff 32 0) _ HS ltac:(vm_compute; reflexivity) HvF)|];
  split; [rewrite (psl_reg_keep _ regsc _ _ _ 22%bv HS ltac:(vm_compute; reflexivity)); exact R22|];
  exact (psl_reg_val _ _ _ _ 24%bv (SOff 32 0) _ HS ltac:(vm_compute; reflexivity) HvF) end) in
(* ---- the test of s[i + 1] (+ 0x29c `bnez s9`) ---- *)
let leafB := fun _ => (
  pcom (); prb (); idtac "PSL-BYTE"; pnt_branch BR HS;
  [ lazymatch goal with Hb : branch_taken BC_NE (sv_denot _ (SOff 35 0)) (sv_denot _ (SLit 0)) = true |- _ =>
      rewrite branch_ne_U, (U_atom _ 35 c1 E35 Hc164), U_SLit in Hb; change (zcanon 0) with 0 in Hb;
      apply Bool.negb_true_iff, Z.eqb_neq in Hb; rename Hb into Hc1nz end;
    pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 384); [ awrN () | leafH () ]
  | lazymatch goal with Hb : branch_taken BC_NE (sv_denot _ (SOff 35 0)) (sv_denot _ (SLit 0)) = false |- _ =>
      rewrite branch_ne_U, (U_atom _ 35 c1 E35 Hc164), U_SLit in Hb; change (zcanon 0) with 0 in Hb;
      apply Bool.negb_false_iff, Z.eqb_eq in Hb; rename Hb into Hc10 end;
    pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 712); [ awrN () | leafT () ] ]) in
(* ---- s[i + 1]'s shadow check (+ 0x28c `bnez a1`, the slow path + 0x2a8 `blt`) ---- *)
pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 384);
[ awrN ()
| pcom (); prb (); idtac "PSL-SH"; pnt_branch BR HS;
  [ (* the shadow byte is nonzero: the partial granule's test *)
    lazymatch goal with Hb : branch_taken BC_NE (sv_denot _ (SOff 34 0)) (sv_denot _ (SLit 0)) = true |- _ =>
      rewrite branch_ne_U, (U_atom _ 34 sv E34 Hsv64), U_SLit in Hb; change (zcanon 0) with 0 in Hb;
      apply Bool.negb_true_iff, Z.eqb_neq in Hb; rename Hb into Hsvnz end;
    pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 384);
    [ awrN ()
    | pcom (); prb (); idtac "PSL-SLOW"; pnt_branch BR HS;
      [ (* (s + i + 1) & 7 < the shadow byte: the load (+ 0x290) *)
        pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 384); [ awrN () | leafB () ]
      | (* NOT TAKEN: the report (+ 0x2ac / + 0x2b0 `jal __asan_report_load1`): s[i + 1] is addressable *)
        exfalso;
        assert (Hlt : (x_s X + Z.of_nat i + 1) mod 8 < sv)
          by (unfold saddr_ok in Hsok; clear - Hsok Hsvnz; lia);
        lazymatch goal with Hb : branch_taken BC_LT _ _ = false |- _ =>
          rewrite (psl_slow_lt _ 24 34 (x_s X + Z.of_nat i) sv E24 E34 ltac:(clear - Hsir; lia)
                     ltac:(clear - Hv20r; lia) ltac:(clear - Hsvr Hsvnz; lia) Hlt) in Hb;
          discriminate Hb end ] ]
  | (* the shadow byte is zero: the load (+ 0x290) *)
    lazymatch goal with Hb : branch_taken BC_NE (sv_denot _ (SOff 34 0)) (sv_denot _ (SLit 0)) = false |- _ =>
      clear Hb end;
    pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 384); [ awrN () | leafB () ] ] ].
Qed.

End h.
End f.
End d.
