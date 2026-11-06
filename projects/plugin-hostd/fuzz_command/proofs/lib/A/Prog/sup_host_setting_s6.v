(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of joined on the ASan build of plugin-hostd/fuzz_command, in the
   shape of cgif_file_fuzzer's walks (lib/A/ACb8.v, lib/A/ACh2.v): the symbolic executor over the position-abstract
   listing (CmdPaLib.v, PaLibF.v, PaCallRun.v) with the shadow tokens of PaShadow.v, the malloc call through
   amalloc04_sub and the memcpy calls through aj_intrin_atS (PaCall.v), and the strlen calls through PaArt.v's
   aj_art_at (jw_art_at below also keeps the entry's promise that a present byte stays present). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/joined.v, with its module paths and module names changed; 1044 of its 1138 lines of code are new or changed and 1793 lines of the source are left out. *)
(* The segment lemmas of the join loop of sup_host_setting's ASan walk (plugin-hostd/fuzz_command, recorder.c:371-374):
   - hs_seg_l2s: from the strlen return at 0x8b20c (token n >= 1, a0 = |join_sp (firstn n toks)|) through the two
     store checks of the separator (0x8b210, 0x8b224), the stores w[L] := ' ' and w[L+1] := 0, the load check on
     &tok[n] and the call of the strcat wrapper (0x8b254) to the strcat return at 0x8b258;
   - hs_seg_l2c: from 0x8b258 through the loop's back edge (0x8b264): while tokens are left, to the next strlen
     return at 0x8b20c; after the last token, through the load check on c->nargs and the call of xstrdup (0x8b2a4)
     to its return at 0x8b2a8.
   The statements are sup_host_setting_s0.v's ST_L2S, ST_L2C and ST_XS. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_line_c arg_i_c xstrdup_c mix_call_c sup_host_setting_c sup_host_setting_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_host_setting_s0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* lia without the Euclidean-division equations, as this file was proved: PaDenot.v set the flag for every file
   that imported it until an earlier commit; now each file sets it for itself *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ---- words and lists ---- *)

Lemma hs6_add : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. rewrite alu_add. unfold v_add. apply Z_to_bv64_eq_mod.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma hs6_srl3 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 64) ltac:(lia) ltac:(lia)).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. symmetry. apply unsigned_lit_small. lia.
Qed.

(* the shadow byte's address of c + 4 (s8) *)
Definition hs6_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 4) (SLit 3)) (SOff 23 0).
Lemma hs6_shx_denot : forall E c, ew E 8 = Z_to_bv 64 c -> ew E 23 = Z_to_bv 64 HS_SB -> 0 <= c < 2 ^ 40 ->
sv_denot E hs6_shx = Z_to_bv 64 (HS_SB + (c + 4) / 8).
Proof.
intros E c Hc Hsb Hr. unfold hs6_shx. cbn [sv_denot]. rewrite Hc, Hsb.
rewrite !unsigned_lit_small by (unfold HS_SB; lia). rewrite Z.add_0_r.
rewrite hs6_srl3 by lia. rewrite hs6_add. f_equal. lia.
Qed.

Lemma hs6_join_snoc : forall X w, X <> [] -> join_sp (X ++ [w]) = join_sp X ++ SPACE :: w.
Proof.
induction X as [|x X IH]; intros w H; [congruence|].
destruct X as [|y X]; [reflexivity|].
specialize (IH w ltac:(discriminate)).
replace ((x :: y :: X) ++ [w]) with (x :: ((y :: X) ++ [w])) by reflexivity.
replace (join_sp (x :: ((y :: X) ++ [w]))) with (x ++ SPACE :: join_sp ((y :: X) ++ [w])) by reflexivity.
rewrite IH. replace (join_sp (x :: y :: X)) with (x ++ SPACE :: join_sp (y :: X)) by reflexivity.
rewrite <- app_assoc. reflexivity.
Qed.

Lemma hs6_join_len : forall X, X <> [] -> Z.of_nat (length (join_sp X)) + 1 = hs_words_len X.
Proof.
induction X as [|x X IH]; intros H; [congruence|].
destruct X as [|y X].
- unfold hs_words_len. cbn [join_sp fold_right]. lia.
- specialize (IH ltac:(discriminate)).
  replace (join_sp (x :: y :: X)) with (x ++ SPACE :: join_sp (y :: X)) by reflexivity.
  unfold hs_words_len in *. cbn [fold_right] in *. rewrite length_app. cbn [length]. lia.
Qed.

Lemma hs6_wl_nonneg : forall X, 0 <= hs_words_len X.
Proof. induction X as [|x X IH]; unfold hs_words_len in *; cbn [fold_right]; lia. Qed.

Lemma hs6_wl_app : forall X Y, hs_words_len (X ++ Y) = hs_words_len X + hs_words_len Y.
Proof. induction X as [|x X IH]; intros Y; unfold hs_words_len in *; cbn [fold_right app]; [lia | rewrite IH; lia]. Qed.

Lemma hs6_wl_firstn : forall X m, hs_words_len (firstn m X) <= hs_words_len X.
Proof.
intros X m. rewrite <- (firstn_skipn m X) at 2. rewrite hs6_wl_app. pose proof (hs6_wl_nonneg (skipn m X)). lia.
Qed.

Lemma hs6_firstn_S : forall {A : Type} (l : list A) n d, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
intros A l. induction l as [|a l IH]; intros [|n] d H; cbn [length] in H; [lia | lia | reflexivity |].
cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma hs6_wl_S : forall X n, (n < length X)%nat ->
hs_words_len (firstn (S n) X) = hs_words_len (firstn n X) + Z.of_nat (length (nth n X [])) + 1.
Proof.
intros X n Hn. rewrite (hs6_firstn_S X n [] Hn), hs6_wl_app. unfold hs_words_len at 2. cbn [fold_right]. lia.
Qed.

Lemma hs6_firstn_ne : forall {A : Type} (l : list A) n, (1 <= n <= length l)%nat -> firstn n l <> [].
Proof.
intros A l n Hn E. pose proof (f_equal (@length A) E) as HL. rewrite length_firstn in HL. cbn [length] in HL. lia.
Qed.

Lemma hs6_nth_error_nth : forall {A : Type} (l : list A) n d, (n < length l)%nat -> nth_error l n = Some (nth n l d).
Proof.
intros A l. induction l as [|a l IH]; intros [|n] d H; cbn [length] in H; [lia | lia | reflexivity |].
cbn [nth_error nth]. apply IH. lia.
Qed.

Lemma hs6_Forall2_nth : forall {A C : Type} (P : A -> C -> Prop) l1 l2 n a c,
Forall2 P l1 l2 -> nth_error l1 n = Some a -> nth_error l2 n = Some c -> P a c.
Proof.
intros A C P l1 l2 n a c H. revert n. induction H as [|x y l1 l2 Hxy H IH]; intros [|n] H1 H2; cbn in H1, H2;
  try discriminate; [injection H1 as <-; injection H2 as <-; exact Hxy | exact (IH n H1 H2)].
Qed.

Lemma hs6_space_nz : SPACE <> Z_to_bv 8 0.
Proof. intros H. apply (f_equal (@bv_unsigned 8)) in H. vm_compute in H. discriminate H. Qed.

(* a C string with one byte appended: the separator stores of 0x8b234 / 0x8b238 *)
Lemma hs6_astr_sep : forall (rd rd' : reader) p s, astr_atR rd p s ->
(forall i, 0 <= i < Z.of_nat (length s) -> rd' (p + i) = rd (p + i)) ->
rd' (p + Z.of_nat (length s)) = Some 32 -> rd' (p + Z.of_nat (length s) + 1) = Some 0 ->
astr_atR rd' p (s ++ [SPACE]).
Proof.
intros rd rd' p s [H1 H2] Hk Hsp Hz. split.
- intros i Hi. rewrite !length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i (length s)) as [Hl | Hl].
  + rewrite Hk by lia. rewrite (H1 i) by (rewrite length_app; cbn [length]; lia).
    rewrite <- app_assoc. rewrite !app_nth1 by lia. reflexivity.
  + destruct (Nat.eq_dec i (length s)) as [-> | Hne].
    * rewrite Hsp. rewrite <- app_assoc. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
    * assert (i = S (length s)) as -> by lia. replace (p + Z.of_nat (S (length s))) with (p + Z.of_nat (length s) + 1) by lia.
      rewrite Hz. rewrite <- app_assoc. rewrite app_nth2 by lia. replace (S (length s) - length s)%nat with 1%nat by lia.
      reflexivity.
- intros Hin. apply in_app_or in Hin as [Hin | [Hin | []]]; [exact (H2 Hin) | exact (hs6_space_nz Hin)].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---- the symbolic seeds (HsProbe.v's, measured to run) ---- *)
Definition hs6_Bx : sv := SOff 23 0.
Definition hs6_Bspan : Z * Z := (HS_SB, HS_SB + 2 ^ 44 - 1).
(* L2S (0x8b20c): s2 = s5 = &tok[n] (atom 21); atom 32 = w + a0, the separator's address; atom 33 = tok[n] *)
Definition hs6_regsS : list sv := sr_set sr_atoms 18 (SOff 21 0).
Definition hs6_fS : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (23%nat, mkAF HS_SB HS_SB 0);
  (20%nat, mkAF 4096 0x7fffff800000 4); (10%nat, mkAF 0 8192 0); (32%nat, mkAF 4096 0x7fffff802000 0);
  (21%nat, mkAF 4096 0x7fffff800000 3)] []
  [(SAlu ALU_ADD (SOff 20 0) (SOff 10 0), SOff 32 0)].
Definition hs6_ssS : sstate := mkSS HS_L2S hs6_regsS
  [YP09.mkRegion (Some 32%nat) 0 2 0 2 []; YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))]]
  None hs6_fS.
Definition hs6_SHS : list shent := [mkSHE 32 0 2; mkSHE 21 0 8].
Definition hs6_xS (sep pn : Z) : list word := [Z_to_bv 64 sep; Z_to_bv 64 pn].
(* L2C (0x8b258): s3 = c + 4, s8 its shadow byte's address; the slot c holds nargs = 2 *)
Definition hs6_regsC : list sv := sr_set (sr_set sr_atoms 24 hs6_shx) 19 (SOff 8 4).
Definition hs6_fC : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF (A_G_REC + 16) A_REC_SPILL 3);
  (23%nat, mkAF HS_SB HS_SB 0); (9%nat, mkAF 1 64 0); (25%nat, mkAF 0 63 0); (20%nat, mkAF 4096 0x7fffff800000 4)] [] [].
Definition hs6_ssC : sstate := mkSS HS_L2C hs6_regsC
  [YP09.mkRegion (Some 8%nat) 0 56 0 0 [YP09.mkChunk 4 (CVal 4 (SLit 2))]] None hs6_fC.
Definition hs6_SHC : list shent := [mkSHE 8 0 56].

Lemma hs6_rnz : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r H E. apply H. rewrite E. reflexivity. Qed.

Lemma hs6_EE : forall regs1 extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 extra)) n = getr regs1 r.
Proof.
intros regs1 extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Lemma hs6_EX : forall regs1 extra j, (32 + j < A_TEXT)%nat ->
ew (Eimg (Ereg regs1 extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs1 extra j Hj. rewrite Eimg_low by exact Hj. apply ew_Ereg_extra. Qed.

Lemma hs6_den_off0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma hs6_U_off : forall E n o v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + o < 2 ^ 64 -> U E (SOff n o) = v + o.
Proof.
intros E n o v Hn Hv Hvo. unfold U. cbn [sv_denot]. rewrite Hn. rewrite (unsigned_lit_small v) by lia.
apply unsigned_lit_small. exact Hvo.
Qed.

Lemma hs6_in_app_noshadow : forall lo len x, in_app lo len -> lo <= x < lo + len ->
~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof. intros lo len x [H0 H] Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. Qed.

(* a symbolic run whose regions have no write window keeps every byte *)
Lemma hs6_run_keeps_all : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hro a Ha. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros (r & Hin & Hr). rewrite Forall_forall in Hro. pose proof (Hro r Hin). lia.
Qed.

Lemma hs6_frame_kept : forall (rd rd' : reader) sp0 (regs : bvmap 5 word),
hs_frame rd sp0 regs -> (forall a, sp0 - 104 <= a < sp0 -> rd' a = rd a) -> hs_frame rd' sp0 regs.
Proof.
intros rd rd' sp0 regs H K j r Hj kk Hk.
assert (Hjl : (j < length HS_SAVED)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). cbn [length HS_SAVED] in Hjl.
rewrite K by lia. exact (H j r Hj kk Hk).
Qed.

Lemma hs6_bv_add : forall v o, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v) + o) = Z_to_bv 64 (v + o).
Proof.
intros v o. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma hs6_astr_kept : forall (rd rd' : reader) p s, astr_atR rd p s ->
(forall i, 0 <= i <= Z.of_nat (length s) -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H1 H2] Hk. split; [|exact H2]. intros i Hi.
rewrite (Hk (Z.of_nat i)) by (rewrite length_app in Hi; cbn [length] in Hi; lia). exact (H1 i Hi).
Qed.

Definition hs6_pair_dec (u v : Z * Z) : {u = v} + {u <> v}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* a callee-saved register across a call, from its value at the call as an atom of the seed's environment *)
Lemma hs6_cs_reg : forall (regsT regs2 regs1 : bvmap 5 word) extra (rr : bv 5),
aregs_preserved regsT regs2 -> acallee_saved (bv_unsigned rr) ->
getr regsT rr = ew (Eimg (Ereg regs1 extra)) (Z.to_nat (bv_unsigned rr)) -> getr regs2 rr = getr regs1 rr.
Proof.
intros regsT regs2 regs1 extra rr HP Hc Hr. pose proof (HP (bv_unsigned rr) Hc) as Hx. rewrite Z_to_bv_bv_unsigned in Hx.
rewrite Hx, Hr. apply hs6_EE. pose proof (bv_unsigned_in_range 5 rr). lia.
Qed.

Lemma hs6_cs_val : forall (regsT regs2 : bvmap 5 word) (rr : bv 5),
aregs_preserved regsT regs2 -> acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regsT rr.
Proof.
intros regsT regs2 rr HP Hc. pose proof (HP (bv_unsigned rr) Hc) as Hx. rewrite Z_to_bv_bv_unsigned in Hx. exact Hx.
Qed.

Lemma hs6_astr_some : forall (rd : reader) p s, astr_atR rd p s ->
forall a, p <= a < p + Z.of_nat (length s) + 1 -> rd a <> None.
Proof.
intros rd p s [H _] a Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (H (Z.to_nat (a - p))) by (rewrite length_app; cbn [length]; lia). discriminate.
Qed.

Lemma hs6_rd1 : forall (rd : reader) a v, aval_mem rd a 1 v -> rd a = Some (YO0f.le_byte v 1 0).
Proof.
intros rd a v H. pose proof (H 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r in H0. exact H0.
Qed.

Ltac hs6_ro_regions := apply Forall_forall; let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; vm_compute in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; lia|]); destruct Hr.
Ltac hs6_acs := cbv [acallee_saved]; first [rewrite bv_unsigned_BV; lia | cbn; lia | vm_compute; lia].

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* the step through a runtime entry with art_post (lib/A/Rt/RtDefs.v) whose writes [Eb] the walk may make (aj_art_at
   with the errno-only premise replaced by awr_byte, closed as aj_intrin_atS closes its own: ajournal_after_write) *)
Lemma hs6_art_wr : forall stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw
(Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
(forall a, Eb a -> awr_byte SEGS B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a) ->
SRr SEGS W (cfg_at SEGS pc regsT memT mdc) (art_post SEGS B stk lyc Sc W regsT memT mdc Eb Qr) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw Qr HJ Hsp Hneg Hstk Hbud Hraw HEb HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => Eb a \/ (sp0 + o - stk <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha).
    + intros H'. apply Hna. right. unfold ascratch_stk in H'. rewrite Hsp in H'. exact H'.
    + intros H'. apply Hna. left. exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (HEb a Ha) | left; lia].
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact HQ|].
intros a Ha Hw He. apply (Hfr a Ha); [unfold ascratch_stk; rewrite Hsp; exact Hw | exact He].
Qed.

(* g_rec and record.spill: image bytes, none of the runtime's statics, not errno *)
Lemma hs6_rec_unowned : forall ly S (W : world SEGS) mem md a, AR SEGS B ly S W mem md -> hs_in_rec a ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros ly S W mem md a HAR Ha.
assert (HP : Exists (in_zr a) recb_PG).
{ unfold recb_PG. destruct Ha as [Ha | Ha]; [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd];
  unfold in_zr; cbn [fst snd]; lia. }
split; [exact (hh_prog_img B MT HH a HP)|].
assert (HP' : Exists (in_zr a) (as_prog_static B)) by (rewrite (ts_prog B (hh_HB B MT HH)); exact HP).
destruct (prog_static_sep B a (am_syms _ _ _ _ (proj1 HAR)) HP') as (H1 & H2 & _). split; assumption.
Qed.

(* the read-only data at a state the call's journal reaches *)
Lemma hs6_rodata_now : forall x lyc Sc (Wc : world SEGS) memc mdc k,
hs_cx B MT x ->
ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros x lyc Sc Wc memc mdc k HCX HJ.
pose proof HCX as (HPRE & HROD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP0 & _).
eapply (arodata_ok_journalP SEGS RLO RHI (hh_RELRO_IMG B MT HH) (RO := hh_RRO B MT HH));
  [exact HJ | | exact HROD].
intros a Hro HF. destruct (hh_ro_prog_apart B MT HH a Hro) as [Hi Hn].
unfold hs_FP in HF. apply inFP_cons in HF as [HF|HF].
- apply Hn. unfold recb_PG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply inFP_cons in HF as [HF|HF].
  + apply Hn. unfold recb_PG. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + destruct (inFP_ablocks_fp_inv _ _ HF) as (q & m & Hqm & Hr).
    destruct (hs_rec_own B _ _ _ _ _ HREP0 (q, m) Hqm) as [Hqin _].
    pose proof (blk_off_imgP B _ _ _ _ _ q m (proj1 HPRE) Hqin) as Hoff.
    pose proof (pa_img_range a Hi). unfold off_img in Hoff. lia.
Qed.

Lemma hs6_seedC : forall (Wc : world SEGS) lyc Sc memc mdc (regs1 : bvmap 5 word) c ntok n wp,
AR SEGS B lyc Sc Wc memc mdc ->
2 ^ 46 <= spZ regs1 <= 2 ^ 47 -> spZ regs1 mod 16 = 0 ->
getr regs1 8 = w64 c -> getr regs1 9 = w64 ntok -> getr regs1 23 = w64 HS_SB -> getr regs1 25 = w64 n ->
getr regs1 20 = w64 wp -> getr regs1 19 = w64 (c + 4) -> getr regs1 24 = w64 (HS_SB + (c + 4) / 8) ->
(c = A_REC_SPILL \/ (A_G_REC + 16 <= c /\ c + 56 <= 0x5e3b00)) -> c mod 8 = 0 ->
1 <= ntok <= 64 -> 0 <= n <= 63 -> 4096 <= wp <= 0x7fffff800000 -> wp mod 16 = 0 ->
aval_mem (rdW Wc memc) (c + 4) 4 2 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) hs6_ssC
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_L2C)) memc (seg_rom SEGS))) /\
sh_ok SEGS hs6_Bx hs6_SHC (Eimg (Ereg regs1 [])) (mrestrict (w_H Wc) memc).
Proof.
intros Wc lyc Sc memc mdc regs1 c ntok n wp HAR Hsp Hsp16 R8 R9 R23 R25 R20 R19 R24 Hc Hc8 Hnt Hn Hw Hw16 Hv.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HGR : A_G_REC = 0x5e3740) by reflexivity. assert (HSP : A_REC_SPILL = 0x5e3be0) by reflexivity.
assert (HSB : HS_SB = 0x7fff8000) by reflexivity.
assert (Hcr : A_G_REC + 16 <= c <= A_REC_SPILL) by lia.
set (E := Eimg (Ereg regs1 [])).
assert (E2 : ew E 2 = getr regs1 2) by exact (hs6_EE _ _ 2 2%bv eq_refl).
assert (E8 : ew E 8 = Z_to_bv 64 c) by exact (eq_trans (hs6_EE _ _ 8 8%bv eq_refl) R8).
assert (E9 : ew E 9 = Z_to_bv 64 ntok) by exact (eq_trans (hs6_EE _ _ 9 9%bv eq_refl) R9).
assert (E20 : ew E 20 = Z_to_bv 64 wp) by exact (eq_trans (hs6_EE _ _ 20 20%bv eq_refl) R20).
assert (E23 : ew E 23 = Z_to_bv 64 HS_SB) by exact (eq_trans (hs6_EE _ _ 23 23%bv eq_refl) R23).
assert (E25 : ew E 25 = Z_to_bv 64 n) by exact (eq_trans (hs6_EE _ _ 25 25%bv eq_refl) R25).
assert (U2 : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
assert (U8 : bv_unsigned (ew E 8) = c) by (rewrite E8; apply unsigned_lit_small; unfold A_REC_SPILL in *; lia).
assert (U9 : bv_unsigned (ew E 9) = ntok) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = wp) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = HS_SB) by (rewrite E23; apply unsigned_lit_small; unfold HS_SB; lia).
assert (U25 : bv_unsigned (ew E 25) = n) by (rewrite E25; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. split.
- unfold hs6_ssC. apply pa_entry_st_ok_full.
  + unfold hs6_regsC. apply YI04.regs_ok_pin;
      [apply YI04.regs_ok_pin; [apply regs_ok_Eimg_Ereg | apply hs6_rnz; discriminate |] | apply hs6_rnz; discriminate |].
    * rewrite R24. symmetry. apply (hs6_shx_denot E c E8 E23). unfold A_REC_SPILL in *. lia.
    * rewrite R19. cbn [sv_denot]. rewrite U8. reflexivity.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U8.
    split; [lia|]. split; [unfold A_REC_SPILL in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ c 4 4 (SLit 2) 2); [reflexivity | cbn; lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H Wc) memc (c + 4) 4 2 Hv).
  + apply pairwise_disjoint_of_extents. cbn. tauto.
  + split; [|split; [exact I | exact I]].
    cbn [hs6_fC f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U8, U23, U9, U25, U20. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold A_G_REC, A_REC_SPILL, HS_SB in *. repeat split; lia.
- unfold sh_ok, hs6_SHC. apply Forall_cons; [|apply Forall_nil].
  destruct Hc as [Hc | Hc].
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E hs6_Bx 8 0x5e3be0 (0x5e3c18 - 0x5e3be0) c 0 56).
    * apply (cmd_addressable_in SEGS B LAWS (hh_HB B MT HH) lyc Sc Wc memc mdc (0x5e3be0, 0x5e3c18 - 0x5e3be0));
        [exact HAR | unfold Tfib_zero_shadow; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity
        | cbn; unfold A_REC_SPILL in *; lia | cbn; unfold A_REC_SPILL in *; lia].
    * unfold hs6_Bx. rewrite (hs6_U_off E 23 0 HS_SB E23) by (unfold HS_SB; lia). unfold HS_SB. reflexivity.
    * rewrite (hs6_U_off E 8 0 c E8) by (unfold A_REC_SPILL in *; lia). lia.
    * unfold A_REC_SPILL in *. lia.
    * unfold A_REC_SPILL in *. lia.
    * intros a Ha. unfold A_REC_SPILL, SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E hs6_Bx 8 0xada00 (0x5e3b00 - 0xada00) c 0 56).
    * apply (cmd_addressable_in SEGS B LAWS (hh_HB B MT HH) lyc Sc Wc memc mdc (0xada00, 0x5e3b00 - 0xada00));
        [exact HAR | unfold Tfib_zero_shadow; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity
        | cbn; unfold A_G_REC in *; lia | cbn; lia].
    * unfold hs6_Bx. rewrite (hs6_U_off E 23 0 HS_SB E23) by (unfold HS_SB; lia). unfold HS_SB. reflexivity.
    * rewrite (hs6_U_off E 8 0 c E8) by (unfold A_REC_SPILL in *; lia). lia.
    * unfold A_G_REC in *. lia.
    * lia.
    * intros a Ha. unfold A_REC_SPILL, SHADOW_OFF in *. lia.
Qed.

(* every byte the recorder's representation reads lies below the stack *)
Lemma hs6_rec_low : forall lyc Sc (Wc : world SEGS) memc mdc R O a, AR SEGS B lyc Sc Wc memc mdc ->
rec_repA B lyc Sc (rdW Wc memc) R O -> hs_in_rec a \/ hs_in_own O a -> 0 <= a < alloc_ceiling.
Proof.
intros lyc Sc Wc memc mdc R O a HAR HREP [Ha | (pn & Hpn & Ha)].
- pose proof asan_consts as (C1 & _). unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
- destruct (hs_rec_own B _ _ _ _ _ HREP pn Hpn) as [Hin _]. destruct pn as [p m]. cbn [fst snd] in Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & H4096 & Hc & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hq]. lia.
Qed.

(* a byte of an entry block the recorder does not own, or of a caller's frame, is none of the call's footprint *)
Lemma hs6_heap_notFP : forall x b kk a, hs_cx B MT x -> In (b, kk) (ablocks B (i_ly x) (i_S x)) ->
~ In (b, kk) (i_O x) -> b <= a < b + req_size kk -> ~ inFP (hs_FP (i_O x)) a.
Proof.
intros x b kk a HCX Hbk HbO Ha HF.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP0 & _).
pose proof (blk_off_imgP B _ _ _ _ _ b kk (proj1 HPRE) Hbk) as Hoff. unfold off_img in Hoff.
unfold hs_FP in HF. apply inFP_cons in HF as [HF|HF]; [unfold A_G_REC, REC_SIZE in HF; lia|].
apply inFP_cons in HF as [HF|HF]; [unfold A_REC_SPILL, SC_SIZE in HF; lia|].
destruct (inFP_ablocks_fp_inv _ _ HF) as (q & m & Hqm & Hr).
assert (Hne : (b, kk) <> (q, m)) by (intros E; rewrite E in HbO; exact (HbO Hqm)).
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ b kk q m (proj1 HPRE) Hbk
  (proj1 (hs_rec_own B _ _ _ _ _ HREP0 (q, m) Hqm)) Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma hs6_frame_notFP : forall x cid pos a, hs_cx B MT x -> In (cid, pos) (frames (i_S x)) ->
frame_addr (i_ly x) cid pos <= a < frame_addr (i_ly x) cid pos + fs_frame_bytes cid -> ~ inFP (hs_FP (i_O x)) a.
Proof.
intros x cid pos a HCX Hin Ha HF.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP0 & _).
pose proof (frm_img SEGS B LAWS _ _ _ _ _ cid pos a (proj1 HPRE) Hin Ha) as Hni.
unfold hs_FP in HF. apply inFP_cons in HF as [HF|HF].
- apply Hni. apply (hh_prog_img B MT HH). unfold recb_PG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply inFP_cons in HF as [HF|HF].
  + apply Hni. apply (hh_prog_img B MT HH). unfold recb_PG. apply Exists_cons_tl, Exists_cons_hd.
    unfold in_zr. cbn [fst snd]. lia.
  + destruct (inFP_ablocks_fp_inv _ _ HF) as (q & m & Hqm & Hr).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q m cid pos (proj1 HPRE)
      (proj1 (hs_rec_own B _ _ _ _ _ HREP0 (q, m) Hqm)) Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the word list's block is none of the recorder's *)
Lemma hs6_w_distinct : forall lyc Sc (Wc : world SEGS) memc mdc (b0 b1 wpw : Z * Z) Rest O1 pn,
AR SEGS B lyc Sc Wc memc mdc -> Permutation (ablocks B lyc Sc) ([b0; b1; wpw] ++ Rest) ->
(forall q, In q O1 -> In q Rest) -> In pn (O1 ++ [b0; b1]) -> pn <> wpw.
Proof.
intros lyc Sc Wc memc mdc b0 b1 wpw Rest O1 pn HAR HP HO1R Hpn E. subst pn.
pose proof (Permutation_NoDup HP (recb_ablocks_nodup_m B _ _ _ _ _ HAR)) as ND. cbn [app] in ND.
inversion ND as [|? ? Hn0 ND1]; subst. inversion ND1 as [|? ? Hn1 ND2]; subst. inversion ND2 as [|? ? Hn2 ND3]; subst.
apply in_app_or in Hpn as [Hpn | [Hpn | [Hpn | []]]].
- exact (Hn2 (HO1R _ Hpn)).
- apply Hn0. rewrite Hpn. right. left. reflexivity.
- apply Hn1. rewrite Hpn. left. reflexivity.
Qed.

(* the n-th token at a state the call's journal reaches: still where it was, readable, its tail visible, in an entry
   block the recorder does not own *)
Lemma hs6_tok_now : forall x lyc Sc (Wc : world SEGS) memc mdc k O1 Nw Rest n,
hs_cx B MT x ->
ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc memc mdc k ->
hs_ba B x lyc Sc O1 Nw Rest -> (n < length (i_toks x))%nat ->
astr_atR (rdW Wc memc) (hs_ptr x n) (hs_tok x n) /\ Z.of_nat (length (hs_tok x n)) <= LMAX /\
atail_vis SEGS Wc memc (hs_ptr x n + Z.of_nat (length (hs_tok x n))) /\
(exists b kk, In (b, kk) (ablocks B lyc Sc) /\ In (b, kk) (ablocks B (i_ly x) (i_S x)) /\ ~ In (b, kk) (i_O x) /\
   b <= hs_ptr x n /\ hs_ptr x n + Z.of_nat (length (hs_tok x n)) + 1 <= b + kk).
Proof.
intros x lyc Sc Wc memc mdc k O1 Nw Rest n HCX HJ HBA Hn.
pose proof HCX as (HPRE & HROD & _ & _ & _ & _ & _ & _ & Hnt & _ & _ & _ & _ & Hlen & _ & HTOKS & _ & HREP0 & _ & _ & _
  & _ & HTAIL).
pose proof HBA as (HP & HRst & HRst2 & _).
pose proof (proj1 HJ) as HARc. pose proof (proj1 HPRE) as HAR0.
assert (Hp : nth_error (i_ps x) n = Some (hs_ptr x n)) by (apply hs6_nth_error_nth; lia).
assert (Ht : nth_error (i_toks x) n = Some (hs_tok x n)) by (apply hs6_nth_error_nth; lia).
pose proof (hs6_Forall2_nth _ _ _ _ _ _ HTOKS Hp Ht) as HA.
pose proof (HTAIL n _ _ Hp Ht) as HT.
set (p := hs_ptr x n) in *. set (s := hs_tok x n) in *.
unfold hs_str in HA. cbv zeta in HA. destruct HA as (Hp0 & HS0 & HnL & HBL & HAP).
destruct HBL as (b & kk & Hbk & Hbp & Hpb).
assert (HbO : ~ In (b, kk) (i_O x)).
{ intros HO. rewrite Forall_forall in HAP. specialize (HAP (b, kk) HO). cbn [fst snd] in HAP. unfold iv_apart in HAP. lia. }
assert (Hbc : In (b, kk) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact (HRst2 _ Hbk HbO). }
destruct (al_blocks _ _ LAWS _ _ _ _ _ b kk HAR0 Hbk) as (_ & Hb4096 & Hbce & _ & _ & _ & Hkk).
pose proof (req_size_pos kk ltac:(lia)) as [_ Hreq].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (KEEP : forall i, 0 <= i <= Z.of_nat (length s) -> rdW Wc memc (p + i) = rdW (i_W x) (i_mem x) (p + i)).
{ intros i Hi. replace (p + i) with (b + (p + i - b)) by lia.
  apply (F2 b kk (p + i - b) Hbk Hbc); [lia|].
  replace (b + (p + i - b)) with (p + i) by lia. apply (hs6_heap_notFP x b kk); [exact HCX | exact Hbk | exact HbO | lia]. }
split; [apply (hs6_astr_kept _ _ _ _ HS0); intros i Hi; apply KEEP; lia|].
split; [lia|].
split.
{ apply (hh_atail_kept B MT HH (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) lyc Sc Wc memc mdc b kk);
    [exact HAR0 | exact HARc | left; split; [exact Hbk|]; split; [exact Hbc | lia] | exact HT]. }
exists b, kk. split; [exact Hbc|]. split; [exact Hbk|]. split; [exact HbO|]. lia.
Qed.

(* the token array's n-th slot at a state the call's journal reaches *)
Lemma hs6_arr_now : forall x lyc Sc (Wc : world SEGS) memc mdc k O1 Nw Rest n,
hs_cx B MT x ->
ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc memc mdc k ->
hs_ba B x lyc Sc O1 Nw Rest -> (n < length (i_toks x))%nat ->
aval_mem (rdW Wc memc) (i_ptok x + 8 * Z.of_nat n) 8 (hs_ptr x n) /\
range_addressable (rdW Wc memc) SHADOW_OFF (i_ptok x + 8 * Z.of_nat n) 8 /\
in_app (i_ptok x + 8 * Z.of_nat n) 8 /\
(forall q m, In (q, m) (ablocks B lyc Sc) -> (In (q, m) (ablocks B (i_ly x) (i_S x)) -> In (q, m) (i_O x)) ->
  i_ptok x + 8 * Z.of_nat n + 8 <= q \/ q + req_size m <= i_ptok x + 8 * Z.of_nat n).
Proof.
intros x lyc Sc Wc memc mdc k O1 Nw Rest n HCX HJ HBA Hn.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & Hnt & _ & Hp0 & Hp8 & HARR & Hlen & HPTR & _ & _ & HREP0 & _).
pose proof HBA as (HP & HRst & HRst2 & _).
pose proof (proj1 HJ) as HARc. pose proof (proj1 HPRE) as HAR0.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & F2 & _ & F4 & _).
assert (Hp : nth_error (i_ps x) n = Some (hs_ptr x n)) by (apply hs6_nth_error_nth; lia).
pose proof (HPTR n _ Hp) as HV.
set (pt := i_ptok x + 8 * Z.of_nat n) in *.
destruct HARR as [((cid & pos & Hfin & Hcid & Hfal & Hf1 & Hf2) & Hp8' & HRA) | ((b & kk & Hbk & Hb1 & Hb2) & HAP)].
- assert (Hfinc : In (cid, pos) (frames Sc)) by (rewrite Hfrs; exact Hfin).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR0 Hfin) as (Hf4096 & Hfc & Hfapp).
  pose proof (al_layout _ _ LAWS _ _ _ _ _ lyc HAR0 Hly) as (_ & HFA & _).
  split.
  { intros j Hj. rewrite (F4 cid pos _ Hfin); [exact (HV j Hj) | |].
    - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
    - apply (hs6_frame_notFP x cid pos); [exact HCX | exact Hfin | lia]. }
  split.
  { assert (HRAc : range_addressable (rdW Wc memc) SHADOW_OFF (i_ptok x) (8 * Z.of_nat (length (i_toks x)))).
    { apply (range_addressable_entry_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos _ _ HJ Hfin Hcid Hf1 Hf2 Hfal);
        [| exact HAR0 | exact HRA].
      intros a Ha. unfold hs_FP in Ha. apply inFP_cons in Ha as [Ha|Ha]; [unfold A_G_REC, REC_SIZE, kLowShadowBeg in *; lia|].
      apply inFP_cons in Ha as [Ha|Ha]; [unfold A_REC_SPILL, SC_SIZE, kLowShadowBeg in *; lia|].
      destruct (inFP_ablocks_fp_inv _ _ Ha) as (q & m & Hqm & Hr).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR0 (proj1 (hs_rec_own B _ _ _ _ _ HREP0 (q, m) Hqm)))
        as (_ & _ & _ & Happ & _).
      unfold in_app, kLowShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. lia. }
    eapply range_addressable_sub; [exact HRAc | lia | lia]. }
  split; [apply (in_app_sub _ _ _ _ Hfapp); lia|].
  intros q m Hq _. pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q m cid pos HARc Hq Hfinc) as Hd.
  rewrite HFA in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- assert (HbO : ~ In (b, kk) (i_O x)).
  { intros HO. rewrite Forall_forall in HAP. specialize (HAP (b, kk) HO). cbn [fst snd] in HAP. unfold iv_apart in HAP. lia. }
  assert (Hbc : In (b, kk) (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact (HRst2 _ Hbk HbO)).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b kk HAR0 Hbk) as (_ & Hb4096 & Hbce & Hbapp & _ & _ & Hkk).
  pose proof (req_size_pos kk ltac:(lia)) as [_ Hreq].
  split.
  { intros j Hj. replace (pt + Z.of_nat j) with (b + (pt + Z.of_nat j - b)) by lia.
    rewrite (F2 b kk (pt + Z.of_nat j - b) Hbk Hbc ltac:(lia)).
    - replace (b + (pt + Z.of_nat j - b)) with (pt + Z.of_nat j) by lia. exact (HV j Hj).
    - apply (hs6_heap_notFP x b kk); [exact HCX | exact Hbk | exact HbO | lia]. }
  split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc b kk pt 8 HARc Hbc ltac:(lia) ltac:(lia))|].
  split; [apply (in_app_sub _ _ _ _ Hbapp); lia|].
  intros q m Hq HqO.
  assert (Hne : (q, m) <> (b, kk)) by (intros E; rewrite E in HqO; exact (HbO (HqO Hbk))).
  pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ q m b kk HARc Hq Hbc Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma hs6_seedS : forall (Wc : world SEGS) lyc Sc memc mdc (regs1 : bvmap 5 word) wp wsz L pt pn,
AR SEGS B lyc Sc Wc memc mdc -> In (wp, wsz) (ablocks B lyc Sc) -> 0 <= L -> L + 2 <= wsz -> L <= 8192 ->
2 ^ 46 <= spZ regs1 <= 2 ^ 47 -> spZ regs1 mod 16 = 0 ->
getr regs1 23 = w64 HS_SB -> getr regs1 20 = w64 wp -> getr regs1 10 = w64 L ->
getr regs1 21 = w64 pt -> getr regs1 18 = w64 pt -> pt mod 8 = 0 -> in_app pt 8 ->
aval_mem (rdW Wc memc) pt 8 pn -> 0 <= pn < 2 ^ 64 ->
range_addressable (rdW Wc memc) SHADOW_OFF pt 8 ->
(pt + 8 <= wp \/ wp + req_size wsz <= pt) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (hs6_xS (wp + L) pn))) hs6_ssS
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_L2S)) memc (seg_rom SEGS))) /\
sh_ok SEGS hs6_Bx hs6_SHS (Eimg (Ereg regs1 (hs6_xS (wp + L) pn))) (mrestrict (w_H Wc) memc).
Proof.
intros Wc lyc Sc memc mdc regs1 wp wsz L pt pn HAR Hin HL0 HL2 HL8 Hsp Hsp16 R23 R20 R10 R21 R18 Hpt8 Happ Hv Hpn Hra Hdis.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSB : HS_SB = 0x7fff8000) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc wp wsz HAR Hin) as (Hw16 & Hw4096 & Hwc & Hwapp & Hwpres & _ & Hwn).
pose proof (req_size_pos wsz ltac:(lia)) as [_ Hreq].
assert (Hpt : 4096 <= pt /\ pt + 8 <= alloc_ceiling) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ; lia).
set (E := Eimg (Ereg regs1 (hs6_xS (wp + L) pn))).
assert (E2 : ew E 2 = getr regs1 2) by exact (hs6_EE _ _ 2 2%bv eq_refl).
assert (E10 : ew E 10 = Z_to_bv 64 L) by exact (eq_trans (hs6_EE _ _ 10 10%bv eq_refl) R10).
assert (E20 : ew E 20 = Z_to_bv 64 wp) by exact (eq_trans (hs6_EE _ _ 20 20%bv eq_refl) R20).
assert (E21 : ew E 21 = Z_to_bv 64 pt) by exact (eq_trans (hs6_EE _ _ 21 21%bv eq_refl) R21).
assert (E23 : ew E 23 = Z_to_bv 64 HS_SB) by exact (eq_trans (hs6_EE _ _ 23 23%bv eq_refl) R23).
assert (E32 : ew E 32 = Z_to_bv 64 (wp + L)) by exact (hs6_EX regs1 (hs6_xS (wp + L) pn) 0 ltac:(unfold A_TEXT; lia)).
assert (E33 : ew E 33 = Z_to_bv 64 pn) by exact (hs6_EX regs1 (hs6_xS (wp + L) pn) 1 ltac:(unfold A_TEXT; lia)).
assert (U2 : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = L) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = wp) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = pt) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = HS_SB) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = wp + L) by (rewrite E32; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. split.
- unfold hs6_ssS. apply pa_entry_st_ok_full.
  + unfold hs6_regsS. apply YI04.regs_ok_pin; [apply regs_ok_Eimg_Ereg | apply hs6_rnz; discriminate |].
    rewrite R18. symmetry. exact (hs6_den_off0 E 21 pt E21).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hwpres (wp + L + o) ltac:(lia))).
    * rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ pt 0 8 (SOff 33 0) pn); [exact (hs6_den_off0 E 33 pn E33) | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_view SEGS (w_H Wc) memc pt 8 pn Hv).
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U21.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [hs6_fS f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U23, U20, U10, U32, U21. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat split; lia.
    * cbn [hs6_fS f_alias alias_ok]. split; [|exact I]. cbn [sv_denot]. rewrite U20, U10, U32, !Z.add_0_r.
      apply hs6_add.
- unfold sh_ok, hs6_SHS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E hs6_Bx 32 wp (req_size wsz) (wp + L) 0 2).
    * exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc wp wsz wp (req_size wsz) HAR Hin
        ltac:(lia) ltac:(lia)).
    * unfold hs6_Bx. rewrite (hs6_U_off E 23 0 HS_SB E23) by lia. unfold HS_SB, SHADOW_OFF. lia.
    * rewrite (hs6_U_off E 32 0 (wp + L) E32) by lia. lia.
    * lia.
    * lia.
    * intros a Ha. apply (hs6_in_app_noshadow wp (req_size wsz)); [exact Hwapp | lia].
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E hs6_Bx 21 pt 8 pt 0 8).
    * exact Hra.
    * unfold hs6_Bx. rewrite (hs6_U_off E 23 0 HS_SB E23) by lia. unfold HS_SB, SHADOW_OFF. lia.
    * rewrite (hs6_U_off E 21 0 pt E21) by lia. lia.
    * lia.
    * lia.
    * intros a Ha. apply (hs6_in_app_noshadow pt 8); [exact Happ | lia].
Qed.

(* ---- L2C: from the strcat return (0x8b258) to the next strlen return (0x8b20c) or to the xstrdup return (0x8b2a8) ---- *)
Lemma hs_seg_l2c : forall x n, ((S n < length (i_toks x))%nat -> ST_L2S B MT x (S n)) ->
(S n = length (i_toks x) -> ST_XS B MT x) -> ST_L2C B MT x n.
Proof.
intros x n HNEXT HLAST. unfold ST_L2C.
intros lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 wp Hn HCX HMID Hb0 Hb1 HREP HSTR HR1 R20 Hw4 R25 R26 R18 R21.
pose proof HH as [hrcf harg_line harg_i hxstrdup hmix hmalloc hfree hstrlen hstrcat hvobjs hHB hTL hMTL hCL hsigp
  hprog_img hprog_wr hro_ok hRRO hRELRO hro_prog hatail hheap_tail hrom].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pal_env B hTL) as errno_low.
pose proof HCX as (HPRE & HROD & HRO & HROIN & HGRD & H10 & H11 & H12 & Hnt & HLINE & Hp0 & Hp8 & HARR & Hlen
  & HPTR & HTOKS & HWL & HREP0 & HFR8 & HEV & HLIVE & HMOK & HTAIL).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJ & Hk & MLE & HBB & HFRM & HBA).
pose proof HBA as (HP & HRst & HRst2 & HRO1 & HO1 & HNw & HO1R).
pose proof HR1 as ((R2 & R3 & R4 & R8 & R9 & R22 & R23) & R19 & R24).
pose proof (proj1 HJ) as HARc.
pose proof (hs_slot_bounds (i_R x)) as (Hc1 & Hc2 & Hc8 & Hc3).
set (sp0 := spZ (i_regs x)) in *.
set (c := hs_slot (i_R x)) in *.
set (wsz := hs_wsz x) in *.
assert (HTS1 : 112 + ASTACK <= SUP_HOST_SETTING_STK) by (unfold SUP_HOST_SETTING_STK; lia).
assert (HTS2 : 112 + XSTRDUP_STK <= SUP_HOST_SETTING_STK) by (unfold SUP_HOST_SETTING_STK; lia).
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hxs : XSTRDUP_STK = 32 + 16384) by reflexivity. assert (HLM : LMAX = 8192) by reflexivity.
assert (HGR : A_G_REC = 0x5e3740) by reflexivity. assert (HSP : A_REC_SPILL = 0x5e3be0) by reflexivity.
assert (HSB : HS_SB = 0x7fff8000) by reflexivity.
assert (Hcr : A_G_REC + 16 <= c /\ c + 56 <= A_REC_SPILL + 56) by (unfold OFF_CALLS, CALL_SIZE, SC_SIZE in *; lia).
assert (Hsp1 : spZ regs1 = sp0 - 112) by (unfold spZ at 1; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the word list's block *)
assert (Hinw : In (wp, wsz) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym HP)). cbn [app]. right; right; left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc wp wsz HARc Hinw) as (Hw16 & Hw4096 & Hwc & Hwapp & Hwpres & _ & Hwn).
pose proof (req_size_pos wsz ltac:(lia)) as [_ Hreq].
assert (Hne1 : firstn (S n) (i_toks x) <> []) by (apply hs6_firstn_ne; lia).
pose proof (hs6_join_len _ Hne1) as HJL.
pose proof (hs6_wl_firstn (i_toks x) (S n)) as HWF.
assert (Hwsz : wsz = hs_words_len (i_toks x) + 1) by reflexivity.
(* the slot's nargs: hs_A2 holds two arguments *)
destruct (hs_rec_last B lyc Sc (rdW Wc memc) (i_R x) (hs_A2 x) (O1 ++ [b0; b1]) HREP) as (P & HCA & _).
pose proof HCA as (_ & _ & _ & _ & HNA & _). cbn [snd hs_A2 length] in HNA. unfold CALL_OFF_NARGS in HNA.
destruct (hs6_seedC Wc lyc Sc memc mdc regs1 c (Z.of_nat (length (i_toks x))) (Z.of_nat n) wp HARc)
  as [HS SHOK]; try assumption.
{ rewrite Hsp1. lia. }
{ rewrite Hsp1. replace (sp0 - 112) with (sp0 + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
{ destruct Hc3 as [Hc3 | Hc3]; [right; unfold CALL_SIZE, OFF_ANSWER in Hc3; lia | left; exact Hc3]. }
{ lia. }
{ lia. }
{ lia. }
set (E := Eimg (Ereg regs1 [])) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 112)) by exact (eq_trans (hs6_EE _ _ 2 2%bv eq_refl) R2).
assert (E8 : ew E 8 = Z_to_bv 64 c) by exact (eq_trans (hs6_EE _ _ 8 8%bv eq_refl) R8).
assert (E9 : ew E 9 = Z_to_bv 64 (Z.of_nat (length (i_toks x)))) by exact (eq_trans (hs6_EE _ _ 9 9%bv eq_refl) R9).
assert (E18 : ew E 18 = Z_to_bv 64 (i_ptok x + 8 * Z.of_nat n)) by exact (eq_trans (hs6_EE _ _ 18 18%bv eq_refl) R18).
assert (E21 : ew E 21 = Z_to_bv 64 (i_ptok x + 8 * Z.of_nat n)) by exact (eq_trans (hs6_EE _ _ 21 21%bv eq_refl) R21).
assert (E23 : ew E 23 = Z_to_bv 64 HS_SB) by exact (eq_trans (hs6_EE _ _ 23 23%bv eq_refl) R23).
assert (E25 : ew E 25 = Z_to_bv 64 (Z.of_nat n)) by exact (eq_trans (hs6_EE _ _ 25 25%bv eq_refl) R25).
unfold hs_at.
(* 0x8b258 .. 0x8b264: s9 += 1, s5 += 8, s2 += 8, then bne s1, s9 *)
paj_run_tok RUN HS HJ SHOK hs6_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?bb0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp bb0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr1. rename ms into ms1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md1 := m) in *; clearbody md1 end.
psrr_branch_tok RUN BR HS SHOK hs6_Bspan.
- (* taken (s9 = n + 1 <> ntok): 0x8b200 beqz s9 (not taken), a0 := w, the strlen wrapper *)
  assert (Hlt : (S n < length (i_toks x))%nat).
  { rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc.
    rewrite (hs6_U_off E 9 0 (Z.of_nat (length (i_toks x))) E9) in Hc by lia.
    rewrite (hs6_U_off E 25 1 (Z.of_nat n) E25) in Hc by lia. lia. }
  paj_run_tok RUN HS HJ SHOK hs6_Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?bb0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp bb0 bc fr lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr2. rename ms into ms2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in *; clearbody md2 end.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26.
  pose proof (proj1 HJ) as HAR2.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
  { intros a Ha. rewrite (hs6_run_keeps_all _ _ _ _ _ HFr2) by (first [exact Ha | hs6_ro_regions]).
    apply (hs6_run_keeps_all _ _ _ _ _ HFr1); [hs6_ro_regions | exact Ha]. }
  assert (QSP : spZ (ms_regs ms2) = sp0 + -112) by (unfold spZ at 1; rewrite Q2, E2; rewrite unsigned_lit_small by lia; lia).
  assert (QRA : YK0s.ret_ok (getr (ms_regs ms2) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Q3' : getr (ms_regs ms2) 3 = w64 (as_gp B)) by exact (eq_trans (eq_trans Q3 (hs6_EE _ _ 3 3%bv eq_refl)) (eq_trans R3 Hgp)).
  assert (Q4' : getr (ms_regs ms2) 4 = w64 (as_tp B)) by exact (eq_trans (eq_trans Q4 (hs6_EE _ _ 4 4%bv eq_refl)) (eq_trans R4 Htp)).
  assert (Q10' : getr (ms_regs ms2) 10 = w64 wp) by exact (eq_trans Q10 (eq_trans (hs6_EE _ _ 20 20%bv eq_refl) R20)).
  (* the strlen wrapper on the word list, back at 0x8b20c *)
  eapply SRr_bind.
  { eapply (hs6_art_wr ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_strlen) Wc (ms_regs ms2) (ms_mem ms2)
      SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [] lyc Sc md2 k (-112)
      (Z_to_bv 64 (BASE + HS_L2S)) _ HJ QSP ltac:(lia) ltac:(lia) ltac:(lia) Q1 (fun a (H : False) => False_ind _ H)).
    apply (hstrlen fx lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 wp (join_sp (firstn (S n) (i_toks x)))).
    - exact (ecall_pre_stk_at SEGS B ESTACK SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x)
        (i_md x) [] lyc Sc Wc (ms_mem ms2) md2 k (ms_regs ms2) (-112) HJ QSP eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
        QRA Q3' Q4').
    - exact Q10'.
    - lia.
    - apply (astr_atR_view SEGS). apply (hs6_astr_kept _ _ _ _ HSTR). intros i Hi. apply KEEP2. lia.
    - unfold astr_len. apply (aread_ok_of_block SEGS B LAWS ESTACK lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 wp wsz);
        [exact HAR2 | exact Hinw | lia | lia | lia | rewrite QSP; lia].
    - unfold astr_len. apply (hheap_tail lyc Sc Wc (ms_mem ms2) md2 wp wsz); [exact HAR2 | exact Hinw | lia].
    - exact (hrom Wc (ms_mem ms2) (hs6_rodata_now x lyc Sc Wc (ms_mem ms2) md2 k HCX HJ)). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md3 & -> & HJ2 & HP2 & HQ2 & HK2).
  assert (KEEP3 : forall a, 0 <= a < sp0 - 112 - ESTACK \/ sp0 - 104 <= a < sp0 -> rdW Wc mem2 a = rdW Wc memc a).
  { intros a Ha. rewrite (HK2 a); [apply KEEP2; lia | lia | lia | tauto]. }
  apply (HNEXT Hlt lyc Sc Wc mem2 md3 regs2 k O1 Rest b0 b1 wp).
  + lia.
  + exact HCX.
  + split; [exact HJ2|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact HBB|]. split; [|exact HBA].
    apply (hs6_frame_kept _ _ _ _ HFRM). intros a Ha. apply KEEP3. right. exact Ha.
  + exact Hb0.
  + exact Hb1.
  + apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc mem2) _ _ HREP).
    * intros a Ha. pose proof (hs6_rec_low lyc Sc Wc memc mdc _ _ a HARc HREP Ha). apply KEEP3. left. lia.
    * intros pn Hpn. exact (proj1 (hs_rec_own B _ _ _ _ _ HREP pn Hpn)).
  + apply (hs6_astr_kept _ _ _ _ HSTR). intros i Hi. apply KEEP3. left. lia.
  + split; [split; [|split; [|split; [|split; [|split; [|split]]]]] | split].
    * rewrite (hs6_cs_reg _ _ _ _ 2%bv HP2 ltac:(hs6_acs) Q2). exact R2.
    * rewrite (hs6_cs_reg _ _ _ _ 3%bv HP2 ltac:(hs6_acs) Q3). exact R3.
    * rewrite (hs6_cs_reg _ _ _ _ 4%bv HP2 ltac:(hs6_acs) Q4). exact R4.
    * rewrite (hs6_cs_reg _ _ _ _ 8%bv HP2 ltac:(hs6_acs) Q8). exact R8.
    * rewrite (hs6_cs_reg _ _ _ _ 9%bv HP2 ltac:(hs6_acs) Q9). exact R9.
    * rewrite (hs6_cs_reg _ _ _ _ 22%bv HP2 ltac:(hs6_acs) Q22). exact R22.
    * rewrite (hs6_cs_reg _ _ _ _ 23%bv HP2 ltac:(hs6_acs) Q23). exact R23.
    * rewrite (hs6_cs_val _ _ 19%bv HP2 ltac:(hs6_acs)), Q19, E8, hs6_bv_add. reflexivity.
    * rewrite (hs6_cs_val _ _ 24%bv HP2 ltac:(hs6_acs)), Q24, E8, E23, hs6_bv_add.
      rewrite hs6_srl3 by lia. rewrite hs6_add. unfold w64. f_equal. change (hs_slot (i_R x)) with c. lia.
  + rewrite (hs6_cs_reg _ _ _ _ 20%bv HP2 ltac:(hs6_acs) Q20). exact R20.
  + lia.
  + exact HQ2.
  + rewrite (hs6_cs_val _ _ 25%bv HP2 ltac:(hs6_acs)), Q25, E25, hs6_bv_add. unfold w64. f_equal. lia.
  + rewrite (hs6_cs_reg _ _ _ _ 26%bv HP2 ltac:(hs6_acs) Q26). exact R26.
  + rewrite (hs6_cs_val _ _ 18%bv HP2 ltac:(hs6_acs)), Q18, E18, hs6_bv_add. unfold w64. f_equal. lia.
  + rewrite (hs6_cs_val _ _ 21%bv HP2 ltac:(hs6_acs)), Q21, E21, hs6_bv_add. unfold w64. f_equal. lia.
- (* not taken (s9 = n + 1 = ntok): 0x8b268 .. 0x8b2a4: the load check on c->nargs, nargs = 2 <= 5, a0 := w, xstrdup *)
  assert (Heq : S n = length (i_toks x)).
  { rewrite branch_ne_U in Hc. apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
    rewrite (hs6_U_off E 9 0 (Z.of_nat (length (i_toks x))) E9) in Hc by lia.
    rewrite (hs6_U_off E 25 1 (Z.of_nat n) E25) in Hc by lia. lia. }
  assert (Hfs : firstn (S n) (i_toks x) = i_toks x) by (apply firstn_all2; lia).
  rewrite Hfs in HSTR, HJL, HWF.
  paj_run_tok RUN HS HJ SHOK hs6_Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?bb0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp bb0 bc fr lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr2. rename ms into ms2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in *; clearbody md2 end.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  pose proof (proj1 HJ) as HAR2.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
  { intros a Ha. rewrite (hs6_run_keeps_all _ _ _ _ _ HFr2) by (first [exact Ha | hs6_ro_regions]).
    apply (hs6_run_keeps_all _ _ _ _ _ HFr1); [hs6_ro_regions | exact Ha]. }
  assert (HSTR2 : astr_atR (rdW Wc (ms_mem ms2)) wp (join_sp (i_toks x))).
  { apply (hs6_astr_kept _ _ _ _ HSTR). intros i Hi. apply KEEP2. lia. }
  assert (QSP : spZ (ms_regs ms2) = sp0 + -112) by (unfold spZ at 1; rewrite Q2, E2; rewrite unsigned_lit_small by lia; lia).
  assert (Q3' : getr (ms_regs ms2) 3 = w64 (as_gp B)) by exact (eq_trans (eq_trans Q3 (hs6_EE _ _ 3 3%bv eq_refl)) (eq_trans R3 Hgp)).
  assert (Q4' : getr (ms_regs ms2) 4 = w64 (as_tp B)) by exact (eq_trans (eq_trans Q4 (hs6_EE _ _ 4 4%bv eq_refl)) (eq_trans R4 Htp)).
  assert (Q10' : getr (ms_regs ms2) 10 = w64 wp) by exact (eq_trans Q10 (eq_trans (hs6_EE _ _ 20 20%bv eq_refl) R20)).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & HnevJ & _).
  pose proof HBB as HBB'. unfold bsum in HBB'. cbn [fold_right snd] in HBB'. rewrite Hb0, Hb1 in HBB'.
  (* the call of xstrdup, back at 0x8b2a8 *)
  rewrite (hsigp CS_xstrdup ltac:(vm_compute; tauto)).
  change (pa_val A_TEXT + cmd_af CS_xstrdup) with (BASE + AF_xstrdup).
  eapply SRr_bind.
  { eapply (cl_callS B LAWS Wc (ms_regs ms2) (ms_mem ms2) _ SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x)) (i_ly x) (i_S x)
      (i_W x) (i_mem x) (i_md x) [] lyc Sc md2 k XSTRDUP_STK [] EV_XSTRDUP (-112) (Z_to_bv 64 (BASE + HS_XS)) []
      (fun ly2 S2 W2 regs2 mem2 md3 => exists p : Z,
        getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
        Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP (join_sp (i_toks x))) :: ablocks B lyc Sc) /\
        Forall (fun qk => iv_apart p (LIVE_XSTRDUP (join_sp (i_toks x))) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
        in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP (join_sp (i_toks x))) /\
        astr_atR (rdW W2 mem2) p (join_sp (i_toks x)) /\ astr_atR (rdW W2 mem2) wp (join_sp (i_toks x)) /\
        blocks_bytes S2 <= blocks_bytes Sc + LIVE_XSTRDUP (join_sp (i_toks x)) /\
        mo_le MT Sc S2 (XM_XSTRDUP MT (join_sp (i_toks x)))) HJ QSP).
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - exact Q3'.
    - exact Q4'.
    - exact Q1.
    - apply ret_ok_codeptr_v; [unfold HS_XS; lia | reflexivity].
    - rewrite unsigned_lit_small by (unfold HS_XS; lia). unfold HS_XS. lia.
    - apply achain_low. unfold s0Z. rewrite Q8, E8. rewrite unsigned_lit_small by lia. lia.
    - intros HPRE1. eapply SRr_mono.
      + apply (hxstrdup fx lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 [] wp (join_sp (i_toks x)) HPRE1).
        * exact (hs6_rodata_now x lyc Sc Wc (ms_mem ms2) md2 k HCX HJ).
        * exact Q10'.
        * left. cbn [astr_argA]. split; [lia|]. split; [exact HSTR2|]. split; [lia|].
          left. split; [exists wp, wsz; split; [exact Hinw | lia] | constructor].
        * exact (hheap_tail lyc Sc Wc (ms_mem ms2) md2 wp wsz (wp + Z.of_nat (length (join_sp (i_toks x)))) HAR2 Hinw
            ltac:(lia)).
        * unfold hs_k3, hs_k2, hs_k0, EV_SUP_HOST_SETTING, EV_XSTRDUP in *. lia.
        * unfold LIVE_SUP_HOST_SETTING in HLIVE. lia.
        * apply (mok_station MT (i_S x) Sc (XM_SUP_HOST_SETTING MT (i_R x) (i_line x) (i_toks x)) (hs_m3 MT x) _ hMTL HMOK MLE).
          -- unfold XM_XSTRDUP. apply (mo_malloc_nonneg MT hMTL). lia.
          -- unfold hs_m3, hs_m2, hs_m0, XM_SUP_HOST_SETTING. pose proof (mo_free_nonneg MT hMTL). lia.
      + cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HPr & HKr).
        exists ly3, S3, regs3, mem3, md3. split; [rewrite Q1; reflexivity|]. split; [exact HJ1|]. split; [exact HPr | exact HKr].
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md3 & -> & HJ2 & HJc2 & HP2 &
    (q & Hq10 & Hq4 & Hperm2 & Hfresh2 & Hqblk & Hqstr & Hwstr & HBB2 & MLE2)).
  pose proof HJc2 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _).
  apply (HLAST Heq ly2 S2 W2 mem2 md3 regs2 (k + EV_XSTRDUP) O1 Rest b0 b1 wp q).
  + exact HCX.
  + split; [exact HJ2|]. split; [unfold hs_k4, EV_XSTRDUP; lia|].
    split; [exact (mle_station MT _ _ _ _ _ hMTL MLE MLE2)|].
    split.
    { assert (BB2 : blocks_bytes S2 = LIVE_XSTRDUP (join_sp (i_toks x)) + blocks_bytes Sc).
      { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ Hperm2). reflexivity. }
      rewrite BB2. unfold bsum in HBB |- *. cbn [fold_right snd] in HBB |- *. lia. }
    split.
    { apply (hs6_frame_kept _ _ _ _ HFRM). intros a Ha.
      rewrite (F1 a) by (first [lia | apply inFP_nil]). apply KEEP2. lia. }
    split; [|split; [exact HRst|split; [exact HRst2|split; [exact HRO1|split; [exact HO1|split; [|exact HO1R]]]]]].
    * eapply Permutation_trans; [exact Hperm2|]. eapply Permutation_trans; [apply perm_skip; exact HP|].
      exact (Permutation_middle [b0; b1; (wp, wsz)] Rest (q, LIVE_XSTRDUP (join_sp (i_toks x)))).
    * intros pn Hpn Hin0. destruct Hpn as [<- | [<- | [<- | [<- | []]]]].
      -- apply HNw; [left; reflexivity | exact Hin0].
      -- apply HNw; [right; left; reflexivity | exact Hin0].
      -- apply HNw; [right; right; left; reflexivity | exact Hin0].
      -- destruct (in_dec hs6_pair_dec (q, LIVE_XSTRDUP (join_sp (i_toks x))) (i_O x)) as [HinO | HnO]; [exact HinO|].
         exfalso. pose proof (HRst2 _ Hin0 HnO) as HinR.
         assert (HinC : In (q, LIVE_XSTRDUP (join_sp (i_toks x))) (ablocks B lyc Sc))
           by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact HinR).
         rewrite Forall_forall in Hfresh2. pose proof (Hfresh2 _ HinC) as Hd. cbn [fst snd] in Hd.
         unfold iv_apart, LIVE_XSTRDUP in Hd. lia.
  + exact Hb0.
  + exact Hb1.
  + apply (hs_rec_kept B lyc Sc ly2 S2 (rdW Wc memc) (rdW W2 mem2) _ _ HREP).
    * intros a Ha. pose proof (hs6_rec_low lyc Sc Wc memc mdc _ _ a HARc HREP Ha) as Hlo.
      destruct Ha as [Ha | (pn & Hpn & Ha)].
      -- destruct (hs6_rec_unowned lyc Sc Wc (ms_mem ms2) md2 a HAR2 Ha) as (Hi & Hno & Hne).
         rewrite (F3 a Hi Hno Hne (fp_spares_closed [] a (sink_closed_ablocks_fp [] (Forall_nil _)) (inFP_nil a))).
         apply KEEP2. lia.
      -- destruct (hs_rec_own B _ _ _ _ _ HREP pn Hpn) as [Hin1 _].
         assert (Hin2 : In pn (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm2)); right; exact Hin1).
         destruct pn as [p0 n0]. cbn [fst snd] in Ha.
         destruct (al_blocks _ _ LAWS _ _ _ _ _ p0 n0 HARc Hin1) as (_ & _ & _ & _ & _ & _ & Hn0).
         pose proof (req_size_pos n0 ltac:(lia)) as [_ Hq0].
         replace a with (p0 + (a - p0)) by lia.
         rewrite (F2 p0 n0 (a - p0) Hin1 Hin2 ltac:(lia) (inFP_nil _)).
         apply KEEP2. lia.
    * intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm2)). right.
      exact (proj1 (hs_rec_own B _ _ _ _ _ HREP pn Hpn)).
  + exact Hqstr.
  + apply Forall_forall. intros pn Hpn. rewrite Forall_forall in Hfresh2. apply Hfresh2.
    exact (proj1 (hs_rec_own B _ _ _ _ _ HREP pn Hpn)).
  + split; [split; [|split; [|split; [|split; [|split; [|split]]]]] | split].
    * rewrite (hs6_cs_reg _ _ _ _ 2%bv HP2 ltac:(hs6_acs) Q2). exact R2.
    * rewrite (hs6_cs_reg _ _ _ _ 3%bv HP2 ltac:(hs6_acs) Q3). exact R3.
    * rewrite (hs6_cs_reg _ _ _ _ 4%bv HP2 ltac:(hs6_acs) Q4). exact R4.
    * rewrite (hs6_cs_reg _ _ _ _ 8%bv HP2 ltac:(hs6_acs) Q8). exact R8.
    * rewrite (hs6_cs_reg _ _ _ _ 9%bv HP2 ltac:(hs6_acs) Q9). exact R9.
    * rewrite (hs6_cs_reg _ _ _ _ 22%bv HP2 ltac:(hs6_acs) Q22). exact R22.
    * rewrite (hs6_cs_reg _ _ _ _ 23%bv HP2 ltac:(hs6_acs) Q23). exact R23.
    * rewrite (hs6_cs_val _ _ 19%bv HP2 ltac:(hs6_acs)), Q19, E8, hs6_bv_add. reflexivity.
    * rewrite (hs6_cs_val _ _ 24%bv HP2 ltac:(hs6_acs)), Q24, E8, E23, hs6_bv_add.
      rewrite hs6_srl3 by lia. rewrite hs6_add. unfold w64. f_equal. change (hs_slot (i_R x)) with c. lia.
  + rewrite (hs6_cs_reg _ _ _ _ 20%bv HP2 ltac:(hs6_acs) Q20). exact R20.
  + lia.
  + exact Hq10.
  + exact (proj1 Hq4).
Qed.

(* a range inside a live block is one the entries may write, at a state whose sp lies above the heap *)
Lemma hs6_wr_block : forall stk lyc Sc (Wc : world SEGS) memc mdc (regs : bvmap 5 word) p k d m,
AR SEGS B lyc Sc Wc memc mdc -> In (p, k) (ablocks B lyc Sc) -> p <= d -> d + m <= p + k -> 0 <= m < 2 ^ 32 ->
alloc_ceiling <= spZ regs - stk ->
awrite_ok SEGS B stk lyc Sc Wc regs memc d m.
Proof.
intros stk lyc Sc Wc memc mdc regs p k d m HAR Hin Hd Hdm Hm Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hin) as (_ & H4096 & Hce & _ & Hpres & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
unfold awrite_ok. split; [lia|]. split; [lia|]. split; [exact Hm|]. split.
- intros a Ha. split; [apply (apresent_writable SEGS); exact (proj1 (Hpres a ltac:(lia)))|].
  split; [exact (proj2 (Hpres a ltac:(lia))) | unfold ascratch_stk; lia].
- split; [exact (amem_range_of_block SEGS B LAWS lyc Sc Wc memc mdc p k d m HAR Hin Hd ltac:(lia))|].
  split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc p k d m HAR Hin Hd ltac:(lia))|].
  intros Hm0. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc p k d m HAR Hin Hd ltac:(lia) Hm0).
Qed.
(* ---- L2S: from the strlen return (0x8b20c) through the separator stores and the strcat wrapper to 0x8b258 ---- *)
Lemma hs_seg_l2s : forall x n, ST_L2C B MT x n -> ST_L2S B MT x n.
Proof.
intros x n HL2C. unfold ST_L2S.
intros lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 wp [Hn1 Hn] HCX HMID Hb0 Hb1 HREP HSTR HR1 R20 Hw4 R10 R25 R26 R18 R21.
pose proof HH as [hrcf harg_line harg_i hxstrdup hmix hmalloc hfree hstrlen hstrcat hvobjs hHB hTL hMTL hCL hsigp
  hprog_img hprog_wr hro_ok hRRO hRELRO hro_prog hatail hheap_tail hrom].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCX as (HPRE & HROD & HRO & HROIN & HGRD & H10 & H11 & H12 & Hnt & HLINE & Hp0 & Hp8 & HARR & Hlen
  & HPTR & HTOKS & HWL & HREP0 & HFR8 & HEV & HLIVE & HMOK & HTAIL).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJ & Hk & MLE & HBB & HFRM & HBA).
pose proof HBA as (HP & HRst & HRst2 & HRO1 & HO1 & HNw & HO1R).
pose proof HR1 as ((R2 & R3 & R4 & R8 & R9 & R22 & R23) & R19 & R24).
pose proof (proj1 HJ) as HARc.
pose proof (hs_slot_bounds (i_R x)) as (Hc1 & Hc2 & Hc8 & Hc3).
assert (Hne : firstn n (i_toks x) <> []) by (apply hs6_firstn_ne; lia).
pose proof (hs6_join_len _ Hne) as HJL.
pose proof (hs6_wl_S (i_toks x) n Hn) as HWS. change (nth n (i_toks x) []) with (hs_tok x n) in HWS.
pose proof (hs6_wl_firstn (i_toks x) (S n)) as HWF.
set (sp0 := spZ (i_regs x)) in *.
set (c := hs_slot (i_R x)) in *.
set (wsz := hs_wsz x) in *.
set (L := Z.of_nat (length (join_sp (firstn n (i_toks x))))) in *.
set (pt := i_ptok x + 8 * Z.of_nat n) in *.
assert (HTS1 : 112 + ASTACK <= SUP_HOST_SETTING_STK) by (unfold SUP_HOST_SETTING_STK; lia).
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HLM : LMAX = 8192) by reflexivity.
assert (HGR : A_G_REC = 0x5e3740) by reflexivity. assert (HSP : A_REC_SPILL = 0x5e3be0) by reflexivity.
assert (HSB : HS_SB = 0x7fff8000) by reflexivity.
assert (Hcr : A_G_REC + 16 <= c /\ c + 56 <= A_REC_SPILL + 56) by (unfold OFF_CALLS, CALL_SIZE, SC_SIZE in *; lia).
assert (Hsp1 : spZ regs1 = sp0 - 112) by (unfold spZ at 1; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hsp16 : spZ regs1 mod 16 = 0)
  by (rewrite Hsp1; replace (sp0 - 112) with (sp0 + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16).
assert (Hwsz : wsz = hs_words_len (i_toks x) + 1) by reflexivity.
assert (HLT : L + Z.of_nat (length (hs_tok x n)) + 2 <= hs_words_len (i_toks x)) by lia.
(* the word list's block: new in this call, or one of the recorder's *)
assert (Hinw : In (wp, wsz) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym HP)). cbn [app]. right; right; left. reflexivity. }
assert (HwO : In (wp, wsz) (ablocks B (i_ly x) (i_S x)) -> In (wp, wsz) (i_O x))
  by (intros Hi; apply HNw; [right; right; left; reflexivity | exact Hi]).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc wp wsz HARc Hinw) as (Hw16 & Hw4096 & Hwc & Hwapp & Hwpres & _ & Hwn).
pose proof (req_size_pos wsz ltac:(lia)) as [_ Hreq].
assert (AWRW : forall a, wp <= a < wp + req_size wsz ->
  awr_byte SEGS B SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x)) (ablocks B (i_ly x) (i_S x)) (ablocks B lyc Sc)
    (frames (i_S x)) lyc [] a).
{ intros a Ha. destruct (in_dec hs6_pair_dec (wp, wsz) (ablocks B (i_ly x) (i_S x))) as [Hi | Hni].
  - right. left. split; [|exists wp, wsz; split; [exact Hinw | exact Ha]].
    unfold hs_FP. apply inFP_cons. right. apply inFP_cons. right.
    replace a with (wp + (a - wp)) by lia. apply (inFP_ablocks_fp _ wp wsz (a - wp) (HwO Hi)). lia.
  - right. right. left. exists wp, wsz. split; [exact Hinw|]. split; [exact Hni | exact Ha]. }
(* the token array's slot and the token *)
destruct (hs6_arr_now x lyc Sc Wc memc mdc k O1 _ Rest n HCX HJ HBA Hn) as (HV & HRA & Happ & HAPT).
destruct (hs6_tok_now x lyc Sc Wc memc mdc k O1 _ Rest n HCX HJ HBA Hn) as (_ & HtL & _ & Harm0).
set (pn := hs_ptr x n) in *. set (s := hs_tok x n) in *.
assert (Hpn : 4096 <= pn /\ pn + Z.of_nat (length s) + 1 <= 0x7fffff800000).
{ destruct Harm0 as (bb & kb & Hbc & _ & _ & Hb1' & Hb2').
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bb kb HARc Hbc) as (_ & H4 & Hce & _ & _ & _ & Hkb).
  pose proof (req_size_pos kb ltac:(lia)) as [_ Hq]. lia. }
assert (Hpt8 : pt mod 8 = 0).
{ unfold pt. replace (i_ptok x + 8 * Z.of_nat n) with (i_ptok x + Z.of_nat n * 8) by lia.
  rewrite Z_mod_plus_full. exact Hp8. }
destruct (hs6_seedS Wc lyc Sc memc mdc regs1 wp wsz L pt pn HARc Hinw ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(rewrite Hsp1; lia) Hsp16 R23 R20 R10 R21 R18 Hpt8 Happ HV ltac:(lia) HRA (HAPT wp wsz Hinw HwO))
  as [HS SHOK].
set (E := Eimg (Ereg regs1 (hs6_xS (wp + L) pn))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 112)) by exact (eq_trans (hs6_EE _ _ 2 2%bv eq_refl) R2).
assert (E21 : ew E 21 = Z_to_bv 64 pt) by exact (eq_trans (hs6_EE _ _ 21 21%bv eq_refl) R21).
assert (E26 : ew E 26 = Z_to_bv 64 32) by exact (eq_trans (hs6_EE _ _ 26 26%bv eq_refl) R26).
assert (E32 : ew E 32 = Z_to_bv 64 (wp + L)) by exact (hs6_EX regs1 (hs6_xS (wp + L) pn) 0 ltac:(unfold A_TEXT; lia)).
assert (E33 : ew E 33 = Z_to_bv 64 pn) by exact (hs6_EX regs1 (hs6_xS (wp + L) pn) 1 ltac:(unfold A_TEXT; lia)).
assert (U32 : bv_unsigned (ew E 32) = wp + L) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = pt) by (rewrite E21; apply unsigned_lit_small; unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ; lia).
unfold hs_at.
(* 0x8b20c .. 0x8b254: a0 := w + L, the two store checks, w[L] := ' ', w[L+1] := 0, the load check on &tok[n],
   a1 := tok[n], a0 := w, then the strcat wrapper *)
paj_run_tok RUN HS HJ SHOK hs6_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?bb0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp bb0 bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AWRW. lia. }
clear HF HG. rename HFr into HFr1. rename ms into ms1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md1 := m) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26.
(* bridges and the stack-above-ceiling fact *)
assert (HLdef : L = Z.of_nat (length (join_sp (firstn n (i_toks x))))) by reflexivity.
change (hs_tok x n) with s in HLT.
assert (Hac : alloc_ceiling + 16496 <= sp0) by lia.
assert (Hdl : astr_len (join_sp (firstn n (i_toks x)) ++ [SPACE]) = L + 1)
  by (unfold astr_len; rewrite length_app; cbn [length]; lia).
(* register facts at the strcat call *)
assert (QSP : spZ (ms_regs ms1) = sp0 + -112) by (unfold spZ at 1; rewrite Q2, E2; rewrite unsigned_lit_small by lia; lia).
assert (QRA : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [unfold HS_L2C; lia | reflexivity]).
assert (Q3' : getr (ms_regs ms1) 3 = w64 (as_gp B))
  by exact (eq_trans Q3 (eq_trans (hs6_EE _ _ 3 3%bv eq_refl) (eq_trans R3 Hgp))).
assert (Q4' : getr (ms_regs ms1) 4 = w64 (as_tp B))
  by exact (eq_trans Q4 (eq_trans (hs6_EE _ _ 4 4%bv eq_refl) (eq_trans R4 Htp))).
assert (Q10' : getr (ms_regs ms1) 10 = w64 wp) by exact (eq_trans Q10 (eq_trans (hs6_EE _ _ 20 20%bv eq_refl) R20)).
assert (Q11' : getr (ms_regs ms1) 11 = w64 pn) by exact (eq_trans Q11 E33).
(* the written separator bytes and the kept memory *)
lazymatch type of HS with
| st_ok _ ?Env _ _ =>
  assert (EA : forall nn, (nn < 1024)%nat -> ew Env nn = ew E nn)
    by (intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity);
  assert (EcU32 : bv_unsigned (ew Env 32) = wp + L)
    by (rewrite (EA 32%nat ltac:(lia)), E32; apply unsigned_lit_small; lia);
  pose proof (st_ok_region_nth Env _ _ 0%nat _ HS ltac:(cbn; reflexivity)) as HRg0;
  cbn [ms_mem restrict] in HRg0;
  assert (Dval0 : bv_unsigned (sv_denot Env (SOff 26 0)) mod 2 ^ (8 * Z.of_N 1) = 32)
    by (cbn [sv_denot]; rewrite (EA 26%nat ltac:(lia)), E26; vm_compute; reflexivity);
  assert (Dval1 : bv_unsigned (sv_denot Env (SLit 0)) mod 2 ^ (8 * Z.of_N 1) = 0)
    by (cbn [sv_denot]; vm_compute; reflexivity);
  assert (B0v : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms1)) (wp + L) 1 32)
    by (pose proof (field_of_region_any Env _ 32 (wp + L) _ 0 2 0 2 0 1%N (SOff 26 0) HRg0 EcU32 ltac:(cbn; tauto)
          ltac:(cbn; lia)) as V0;
        rewrite Z.add_0_r, Dval0 in V0; cbn [N.to_nat] in V0; exact V0);
  assert (B1v : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms1)) (wp + L + 1) 1 0)
    by (pose proof (field_of_region_any Env _ 32 (wp + L) _ 0 2 0 2 1 1%N (SLit 0) HRg0 EcU32 ltac:(cbn; tauto)
          ltac:(cbn; lia)) as V1;
        rewrite Dval1 in V1; cbn [N.to_nat] in V1; exact V1)
end.
assert (B0 : rdW Wc (ms_mem ms1) (wp + L) = Some 32)
  by (pose proof (hs6_rd1 _ _ _ (aval_mem_view SEGS (w_H Wc) (ms_mem ms1) (wp + L) 1 32 B0v)) as HHb; rewrite HHb; vm_compute; reflexivity).
assert (B1 : rdW Wc (ms_mem ms1) (wp + L + 1) = Some 0)
  by (pose proof (hs6_rd1 _ _ _ (aval_mem_view SEGS (w_H Wc) (ms_mem ms1) (wp + L + 1) 1 0 B1v)) as HHb; rewrite HHb; vm_compute; reflexivity).
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (wp + L <= a < wp + L + 2) -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha Hna.
  apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms1) (fun a0 => wp + L <= a0 < wp + L + 2) HFr1);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U32, ?U21 in Hrr; lia|]);
      destruct Hin
    | exact Ha | exact Hna ]. }
(* the destination string after the separator stores, and the token at the current state *)
assert (HDST : astr_atR (rdW Wc (ms_mem ms1)) wp (join_sp (firstn n (i_toks x)) ++ [SPACE])).
{ apply (hs6_astr_sep (rdW Wc memc) (rdW Wc (ms_mem ms1)) wp (join_sp (firstn n (i_toks x))) HSTR).
  - intros i Hi. apply KEEP2; [lia | lia].
  - exact B0.
  - exact B1. }
destruct (hs6_tok_now x lyc Sc Wc (ms_mem ms1) md1 k O1 _ Rest n HCX HJ HBA Hn) as (HSsrc1 & HsL1 & HTsrc1 & Harm1).
change (hs_ptr x n) with pn in HSsrc1, HsL1, HTsrc1, Harm1.
change (hs_tok x n) with s in HSsrc1, HsL1, HTsrc1, Harm1.
(* the source string's read-ok and the disjointness of the two blocks *)
assert (Hsrc : (pn + Z.of_nat (length s) + 1 <= wp \/ wp + wsz <= pn) /\
               aread_ok SEGS (2 * ESTACK) Wc (ms_regs ms1) (ms_mem ms1) pn (astr_len s + 1)).
{ destruct Harm1 as (bb & kb & Hbc & Hbe & HbO & Hbb1 & Hbb2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bb kb (proj1 HJ) Hbc) as (_ & _ & _ & _ & _ & _ & Hkb0).
  pose proof (req_size_pos kb ltac:(lia)) as [_ Hkreq]. pose proof (req_size_pos wsz ltac:(lia)) as [_ Hwr].
  assert (Hwbne : (wp, wsz) <> (bb, kb)) by (intros Eq; injection Eq as Ew Ek; subst bb kb; exact (HbO (HwO Hbe))).
  pose proof (sep_blocks SEGS B LAWS lyc Sc Wc (ms_mem ms1) md1 wp wsz bb kb (proj1 HJ) Hinw Hbc Hwbne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. split; [lia|].
  apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc Wc (ms_regs ms1) (ms_mem ms1) md1 bb kb pn (astr_len s + 1)
    (proj1 HJ) Hbc); [lia | unfold astr_len; lia | unfold astr_len; lia | rewrite QSP; lia]. }
destruct Hsrc as [Hdisj Hrdsrc].
(* the strcat wrapper on (w holding join_sp (firstn n toks) ++ [' '], tok n), back at 0x8b258 *)
eapply SRr_bind.
{ eapply (hs6_art_wr (2 * ESTACK)
    (fun a => wp + astr_len (join_sp (firstn n (i_toks x)) ++ [SPACE]) <= a
              < wp + astr_len (join_sp (firstn n (i_toks x)) ++ [SPACE]) + astr_len s + 1)
    (SIG CS___interceptor_trampoline_strcat) Wc (ms_regs ms1) (ms_mem ms1) SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x))
    (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [] lyc Sc md1 k (-112) (Z_to_bv 64 (BASE + HS_L2C)) _ HJ QSP ltac:(lia)
    ltac:(lia) ltac:(lia) Q1).
  - intros a HE. rewrite Hdl in HE. apply AWRW. unfold astr_len in HE. lia.
  - apply (hstrcat fx lyc Sc Wc (ms_regs ms1) (ms_mem ms1) md1 wp pn (join_sp (firstn n (i_toks x)) ++ [SPACE]) s).
    + exact (ecall_pre_stk_at SEGS B (2 * ESTACK) SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x)
        (i_mem x) (i_md x) [] lyc Sc Wc (ms_mem ms1) md1 k (ms_regs ms1) (-112) HJ QSP eq_refl ltac:(lia) ltac:(lia)
        ltac:(lia) QRA Q3' Q4').
    + exact Q10'.
    + exact Q11'.
    + lia.
    + lia.
    + apply (astr_atR_view SEGS). exact HDST.
    + apply (astr_atR_view SEGS). exact HSsrc1.
    + rewrite Hdl. apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc Wc (ms_regs ms1) (ms_mem ms1) md1 wp wsz wp
        (L + 1 + 1) (proj1 HJ) Hinw); [lia | lia | lia | rewrite QSP; lia].
    + (* to = the word list, a heap block: 8 bytes of band room past its string (band-premise survey, call site 19) *)
      rewrite Hdl. apply (amem8_of_blockA SEGS B LAWS lyc Sc Wc (ms_mem ms1) md1 wp (L + 1) (proj1 HJ)); [|lia].
      exists wp, wsz. split; [exact Hinw | split; lia].
    + exact Hrdsrc.
    + (* from = tok[n], in an entry block *)
      destruct Harm1 as (bb & kb & Hbc & _ & _ & Hbb1 & Hbb2).
      apply (amem8_of_blockA SEGS B LAWS lyc Sc Wc (ms_mem ms1) md1 pn (astr_len s) (proj1 HJ)); [|unfold astr_len; lia].
      exists bb, kb. split; [exact Hbc | unfold astr_len; split; lia].
    + rewrite Hdl. apply (hs6_wr_block (2 * ESTACK) lyc Sc Wc (ms_mem ms1) md1 (ms_regs ms1) wp wsz (wp + (L + 1))
        (astr_len s + 1) (proj1 HJ) Hinw); [lia | unfold astr_len; lia | unfold astr_len; lia | rewrite QSP; lia].
    + (* the written range words + dlen, in the word list's block *)
      rewrite Hdl. apply (amem8_of_blockA SEGS B LAWS lyc Sc Wc (ms_mem ms1) md1 (wp + (L + 1)) (astr_len s) (proj1 HJ));
        [|unfold astr_len; lia].
      exists wp, wsz. split; [exact Hinw | unfold astr_len; split; lia].
    + (* the written range is the word list's block: a heap byte is no image byte, and a read-only byte is one *)
      rewrite Hdl. intros a Ha _ (sg & Hsg & _ & Hrg). unfold astr_len in Ha.
      exact (recb_heap_noimg_m B lyc Sc Wc (ms_mem ms1) md1 wp wsz a (proj1 HJ) Hinw ltac:(lia)
        (ex_intro _ sg (conj Hsg Hrg))).
    + rewrite Hdl. apply (hheap_tail lyc Sc Wc (ms_mem ms1) md1 wp wsz (wp + (L + 1)) (proj1 HJ) Hinw). lia.
    + exact HTsrc1.
    + rewrite Hdl. unfold astr_len. lia.
    + (* the destination tail does not start inside the token's last word: the token's block and the word list's
         are apart and the word list's block is 16-aligned, so the token's rounded end is at or below it *)
      rewrite Hdl. unfold astr_len, aword_end. destruct Hdisj as [Hdj | Hdj]; [right | left; lia].
      pose proof (Z.mod_pos_bound (- (pn + (Z.of_nat (length s) + 1))) 8 ltac:(lia)) as Hmb.
      pose proof (Z.div_mod (- (pn + (Z.of_nat (length s) + 1))) 8 ltac:(discriminate)) as Hdm.
      pose proof (Z.div_mod wp 16 ltac:(discriminate)) as Hdw. rewrite Hw16 in Hdw. lia.
    + exact (hrom Wc (ms_mem ms1) (hs6_rodata_now x lyc Sc Wc (ms_mem ms1) md1 k HCX HJ)). }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQr & KEEPS).
destruct HQr as [Hq10f HDSTab].
(* memory kept across the strcat: below the ceiling and off the word list, and the frame below sp0 *)
assert (KEEPall : forall a, 0 <= a < alloc_ceiling -> ~ (wp <= a < wp + wsz) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hnw.
  rewrite (KEEPS a ltac:(lia) ltac:(lia) ltac:(intros HE; apply Hnw; rewrite Hdl in HE; unfold astr_len in HE; lia)).
  apply KEEP2; [lia | intros HR; apply Hnw; lia]. }
assert (KEEPrec : forall a, hs_in_rec a \/ hs_in_own (O1 ++ [b0; b1]) a -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a HR. assert (Hnw : ~ (wp <= a < wp + wsz)).
  { destruct HR as [Ha | (pm & Hpm & Ha)].
    - pose proof (blk_off_imgP B lyc Sc Wc memc mdc wp wsz HARc Hinw) as Hoff. unfold off_img in Hoff.
      pose proof (req_size_pos wsz ltac:(lia)) as [_ Hwr].
      unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
    - destruct pm as [q m]. cbn [fst snd] in Ha.
      pose proof (proj1 (hs_rec_own B lyc Sc (rdW Wc memc) _ _ HREP (q, m) Hpm)) as Hqin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hqin) as (_ & _ & _ & _ & _ & _ & Hm0).
      pose proof (req_size_pos m ltac:(lia)) as [_ Hmr]. pose proof (req_size_pos wsz ltac:(lia)) as [_ Hwr].
      assert (Hqwne : (q, m) <> (wp, wsz))
        by (apply (hs6_w_distinct lyc Sc Wc memc mdc b0 b1 (wp, wsz) Rest O1 (q, m) HARc HP HO1R Hpm)).
      pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc q m wp wsz HARc Hqin Hinw Hqwne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  apply KEEPall; [exact (hs6_rec_low lyc Sc Wc memc mdc _ _ a HARc HREP HR) | exact Hnw]. }
assert (KEEPfr : forall a, sp0 - 104 <= a < sp0 -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha.
  rewrite (KEEPS a ltac:(lia) ltac:(lia) ltac:(intros HE; rewrite Hdl in HE; unfold astr_len in HE; lia)).
  apply KEEP2; [lia | lia]. }
(* the join_sp of the first (S n) tokens, now in the word list *)
assert (HListEq : (join_sp (firstn n (i_toks x)) ++ [SPACE]) ++ s ++ [Z_to_bv 8 0]
                  = join_sp (firstn (S n) (i_toks x)) ++ [Z_to_bv 8 0]).
{ rewrite (hs6_firstn_S (i_toks x) n [] Hn). change (nth n (i_toks x) []) with s.
  rewrite hs6_join_snoc by (apply hs6_firstn_ne; lia). rewrite <- !app_assoc. reflexivity. }
assert (HDnz : ~ In (Z_to_bv 8 0) (join_sp (firstn (S n) (i_toks x)))).
{ rewrite (hs6_firstn_S (i_toks x) n [] Hn). change (nth n (i_toks x) []) with s.
  rewrite hs6_join_snoc by (apply hs6_firstn_ne; lia).
  intros HIn. apply in_app_or in HIn as [HIn | [HIn | HIn]].
  - destruct HSTR as [_ Hnz]. exact (Hnz HIn).
  - exact (hs6_space_nz HIn).
  - destruct HSsrc1 as [_ Hnz]. exact (Hnz HIn). }
assert (HDSTfin : astr_atR (rdW Wc mem2) wp (join_sp (firstn (S n) (i_toks x)))).
{ split; [| exact HDnz]. rewrite <- HListEq. apply (abytes_atR_view SEGS). exact HDSTab. }
(* apply ST_L2C at the strcat return (0x8b258) *)
apply (HL2C lyc Sc Wc mem2 md2 regs2 k O1 Rest b0 b1 wp Hn HCX).
- split; [exact HJ2|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact HBB|]. split; [|exact HBA].
  apply (hs6_frame_kept (rdW Wc memc) (rdW Wc mem2) sp0 (i_regs x) HFRM). exact KEEPfr.
- exact Hb0.
- exact Hb1.
- apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc mem2) _ _ HREP);
    [ exact KEEPrec | intros pn0 Hpn0; exact (proj1 (hs_rec_own B _ _ _ _ _ HREP pn0 Hpn0)) ].
- exact HDSTfin.
- split; [split; [|split; [|split; [|split; [|split; [|split]]]]] | split].
  * rewrite (hs6_cs_reg _ _ _ _ 2%bv HP2 ltac:(hs6_acs) Q2). exact R2.
  * rewrite (hs6_cs_reg _ _ _ _ 3%bv HP2 ltac:(hs6_acs) Q3). exact R3.
  * rewrite (hs6_cs_reg _ _ _ _ 4%bv HP2 ltac:(hs6_acs) Q4). exact R4.
  * rewrite (hs6_cs_reg _ _ _ _ 8%bv HP2 ltac:(hs6_acs) Q8). exact R8.
  * rewrite (hs6_cs_reg _ _ _ _ 9%bv HP2 ltac:(hs6_acs) Q9). exact R9.
  * rewrite (hs6_cs_reg _ _ _ _ 22%bv HP2 ltac:(hs6_acs) Q22). exact R22.
  * rewrite (hs6_cs_reg _ _ _ _ 23%bv HP2 ltac:(hs6_acs) Q23). exact R23.
  * rewrite (hs6_cs_reg _ _ _ _ 19%bv HP2 ltac:(hs6_acs) Q19). exact R19.
  * rewrite (hs6_cs_reg _ _ _ _ 24%bv HP2 ltac:(hs6_acs) Q24). exact R24.
- rewrite (hs6_cs_reg _ _ _ _ 20%bv HP2 ltac:(hs6_acs) Q20). exact R20.
- lia.
- rewrite (hs6_cs_reg _ _ _ _ 25%bv HP2 ltac:(hs6_acs) Q25). exact R25.
- rewrite (hs6_cs_reg _ _ _ _ 26%bv HP2 ltac:(hs6_acs) Q26). exact R26.
- rewrite (hs6_cs_val _ _ 18%bv HP2 ltac:(hs6_acs)), Q18, E21. reflexivity.
- rewrite (hs6_cs_val _ _ 21%bv HP2 ltac:(hs6_acs)), Q21, E21. reflexivity.
Qed.

End e.
End f.
End d.
