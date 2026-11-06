(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the member loop of sup_chain's ASan walk (plugin-hostd/fuzz_command,
   0x8c2b4): from the loop-skip test (0x8c3c4) through the per-member sprintf loop to the loop exit (0x8c438),
   in the continuation style of lib/A/Prog/sup_chain.v's sc_segA_table and lib/A/Prog/check_reply_s4.v's
   step through a runtime entry that writes a live block (s4_art_own). *)
(* Modified by Theorem Labs, 2026-10: re-fitted to statement passes 4, 4b and 5:
   the sprintf wrapper's contract is the shared RtPFCmd.asprintf_sh taken at every FP state
   and its post is FP-existential, so each pass returns at some fx1 with fxrel fxk fx1; scl_pass, sc_loop_body and
   scl_loop_from take the FP state of the pass explicitly, and sc_loop's continuation takes the FP state at the exit;
   PaFx.v's st_ok_restrict_xfx takes the call site's symbolic state to the FP state each pass returns. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_chain_s5.v, with its module paths and module names changed; 1026 of its 1134 lines of code are new or changed and 1086 lines of the source are left out. *)
(* The segment lemmas of the join loop of sup_host_setting's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, recorder.c:371-374), on the points and statements of sup_host_setting_s0.v:
   - hs_seg_l2s: from L2S n (0x8b744, back from the strlen wrapper on the word list w, token n >= 1,
     a0 = |join_sp (firstn n toks)|) through `add a0,s6,a0`, the two store_n checks of the separator bytes
     (0x8b748 .. 0x8b768, decided by the token executor from the shadow of w's block), the stores w[L] := ' ' and
     w[L+1] := 0 (0x8b76c, 0x8b770), the UBSan check of &tok[n] (0x8b774 `bltu s5,s7`, split and refuted), the
     load8 check of &tok[n] (0x8b77c .. 0x8b788), a1 := tok[n], a0 := w and the strcat wrapper (0x45220, at
     0x8b794), back at L2C n (0x8b798);
   - hs_seg_l2c: from L2C n (0x8b798) through the back edge `bne s2,s11` (0x8b7a0, split): while tokens are left,
     `beqz s11` (not taken) and the strlen wrapper on w (0x4517c, at 0x8b740), back at L2S (n + 1) (0x8b744); after
     the last token, the reloads of c, F, F from the realigned stack (0x8b7c8 .. 0x8b7d0) and the call of
     arg_s(c, w) (0x8a820, at 0x8b800) through cl_callS_wide (arg_s writes c->nargs and c->args[2], program
     statics in the whole call's footprint), back at AS2 (0x8b804).
   The B twin of the ASan walk's lib/A/Prog/sup_host_setting_s6.v (a working branch e323bbe76d2):
   B's loop keeps w in s6, 8n in s7, n in s11, ntok in s2, ' ' in s4, ~tok in s5 and the shadow base in s10, makes
   every call at the realigned sp1 = hs_sp1 sp0 with s0 = sp0 and the class-0 side-stack frame (0, fpos) owned by
   the whole call's journal, and records the joined words with a call of arg_s where A inlines xstrdup. Shared
   helpers of the walk come from sup_host_setting_s3.v (prefix hs3_) and sup_host_setting_aux.v (prefix hsb_). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c record_c arg_line_c arg_s_c xmalloc_c mix_call_c sup_host_setting_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_host_setting_aux sup_host_setting_s1 sup_host_setting_s0 sup_host_setting_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- words and lists ---- *)

Lemma hsb6_add : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. rewrite alu_add. unfold v_add. apply Z_to_bv64_eq_mod.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.

(* s5 = ~tok (0x8b72c `xori s5,s8,-1`) as the value 2^64 - 1 - tok that hs_regsL2 states *)
Lemma hsb6_xor_ones : forall t, 0 <= t < 2 ^ 64 ->
  alu64 ALU_XOR (Z_to_bv 64 t) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - t).
Proof.
intros t Ht. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small t) by lia.
replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
rewrite hsb_lxor_ones by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
symmetry. apply unsigned_lit_small. lia.
Qed.

Lemma hsb6_join_len : forall X, X <> [] -> Z.of_nat (length (join_sp X)) + 1 = hs_words_len X.
Proof.
induction X as [|x X IH]; intros H; [congruence|].
destruct X as [|y X].
- unfold hs_words_len. cbn [join_sp fold_right]. lia.
- specialize (IH ltac:(discriminate)).
  replace (join_sp (x :: y :: X)) with (x ++ SPACE :: join_sp (y :: X)) by reflexivity.
  unfold hs_words_len in *. cbn [fold_right] in *. rewrite length_app. cbn [length]. lia.
Qed.

Lemma hsb6_wl_app : forall X Y, hs_words_len (X ++ Y) = hs_words_len X + hs_words_len Y.
Proof. induction X as [|x X IH]; intros Y; unfold hs_words_len in *; cbn [fold_right app]; [lia | rewrite IH; lia]. Qed.

Lemma hsb6_wl_firstn : forall X m, hs_words_len (firstn m X) <= hs_words_len X.
Proof.
intros X m. rewrite <- (firstn_skipn m X) at 2. rewrite hsb6_wl_app. pose proof (hs3_wl_nonneg (skipn m X)). lia.
Qed.

Lemma hsb6_wl_S : forall X n, (n < length X)%nat ->
hs_words_len (firstn (S n) X) = hs_words_len (firstn n X) + Z.of_nat (length (nth n X [])) + 1.
Proof.
intros X n Hn. rewrite (hsb_firstn_S X n [] Hn), hsb6_wl_app. unfold hs_words_len at 2. cbn [fold_right]. lia.
Qed.

Lemma hsb6_firstn_ne : forall {A : Type} (l : list A) n, (1 <= n <= length l)%nat -> firstn n l <> [].
Proof.
intros A l n Hn E. pose proof (f_equal (@length A) E) as HL. rewrite length_firstn in HL. cbn [length] in HL. lia.
Qed.

Lemma hsb6_nth_error_nth : forall {A : Type} (l : list A) n d, (n < length l)%nat -> nth_error l n = Some (nth n l d).
Proof.
intros A l. induction l as [|a l IH]; intros [|n] d H; cbn [length] in H; [lia | lia | reflexivity |].
cbn [nth_error nth]. apply IH. lia.
Qed.

Lemma hsb6_Forall2_nth : forall {A C : Type} (P : A -> C -> Prop) l1 l2 n a c,
Forall2 P l1 l2 -> nth_error l1 n = Some a -> nth_error l2 n = Some c -> P a c.
Proof.
intros A C P l1 l2 n a c H. revert n. induction H as [|x y l1 l2 Hxy H IH]; intros [|n] H1 H2; cbn in H1, H2;
  try discriminate; [injection H1 as <-; injection H2 as <-; exact Hxy | exact (IH n H1 H2)].
Qed.

Lemma hsb6_space_nz : SPACE <> Z_to_bv 8 0.
Proof. intros H. apply (f_equal (@bv_unsigned 8)) in H. vm_compute in H. discriminate H. Qed.

(* a C string with one byte appended: the separator stores of 0x8b76c / 0x8b770 *)
Lemma hsb6_astr_sep : forall (rd rd' : reader) p s, astr_atR rd p s ->
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
- intros Hin. apply in_app_or in Hin as [Hin | [Hin | []]]; [exact (H2 Hin) | exact (hsb6_space_nz Hin)].
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

(* ---- the symbolic seeds ---- *)
(* the shadow base atom (s10) and its span, the token executor's Bx / Bspan *)
Definition hsb6_Bx : sv := SOff 26 0.
Definition hsb6_Bspan : Z * Z := (HS_SB, HS_SB + 2 ^ 44 - 1).
(* L2S (0x8b744): every register its own atom; atom 32 = w + L, the separator's address (`add a0,s6,a0`), atom 33 =
   &tok[n] = tok + 8n (`add a0,s8,s7`), atom 34 = tok[n], the word there *)
Definition hsb6_fS : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (26%nat, mkAF HS_SB HS_SB 0);
  (22%nat, mkAF 4096 0x7fffff800000 4); (10%nat, mkAF 0 8192 0); (32%nat, mkAF 4096 0x7fffff802000 0);
  (33%nat, mkAF 4096 0x7fffff800000 3)] []
  [(SAlu ALU_ADD (SOff 22 0) (SOff 10 0), SOff 32 0); (SAlu ALU_ADD (SOff 24 0) (SOff 23 0), SOff 33 0)].
Definition hsb6_ssS : sstate := mkSS HS_L2S sr_atoms
  [YP09.mkRegion (Some 32%nat) 0 2 0 2 []; YP09.mkRegion (Some 33%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))]]
  None hsb6_fS.
Definition hsb6_SHS : list shent := [mkSHE 32 0 2; mkSHE 33 0 8].
Definition hsb6_xS (sep pt pn : Z) : list word := [Z_to_bv 64 sep; Z_to_bv 64 pt; Z_to_bv 64 pn].
(* L2C (0x8b798): every register its own atom; the realigned stack's spill words at s1 + 8 (c, atom 32), s1 + 16 and
   s1 + 24 (F, atom 33) *)
Definition hsb6_fC : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF (2^46) (2^47) 4);
  (18%nat, mkAF 1 64 0); (27%nat, mkAF 0 63 0)] [] [].
Definition hsb6_ssC : sstate := mkSS HS_L2C sr_atoms
  [YP09.mkRegion (Some 9%nat) 8 32 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
     YP09.mkChunk 24 (CVal 8 (SOff 33 0))]]
  None hsb6_fC.
Definition hsb6_xC (c F : Z) : list word := [Z_to_bv 64 c; Z_to_bv 64 F].

Lemma hsb6_EE : forall regs1 extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 extra)) n = getr regs1 r.
Proof.
intros regs1 extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Lemma hsb6_EX : forall regs1 extra j, (32 + j < A_TEXT)%nat ->
ew (Eimg (Ereg regs1 extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs1 extra j Hj. rewrite Eimg_low by exact Hj. apply ew_Ereg_extra. Qed.

Lemma hsb6_den_off0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma hsb6_U_off : forall E n o v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + o < 2 ^ 64 -> U E (SOff n o) = v + o.
Proof.
intros E n o v Hn Hv Hvo. unfold U. cbn [sv_denot]. rewrite Hn. rewrite (unsigned_lit_small v) by lia.
apply unsigned_lit_small. exact Hvo.
Qed.

Lemma hsb6_in_app_noshadow : forall lo len x, in_app lo len -> lo <= x < lo + len ->
~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof. intros lo len x [H0 H] Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. Qed.

Lemma hsb6_val_of_aval : forall (W : world SEGS) mem a n v,
aval_mem (rdW W mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate]. cbn [option_map] in Hb.
injection Hb as Hb. f_equal. transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned|].
f_equal. rewrite Hb. reflexivity.
Qed.

Lemma hsb6_aval_of_val : forall (W : world SEGS) mem a n v,
val_mem SEGS (mrestrict (w_H W) mem) a n v -> aval_mem (rdW W mem) a n v.
Proof.
intros W mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte, YO0f.le_byte.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* a symbolic run whose regions have no write window keeps every byte *)
Lemma hsb6_run_keeps_all : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hro a Ha. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros (r & Hin & Hr). rewrite Forall_forall in Hro. pose proof (Hro r Hin). lia.
Qed.

Lemma hsb6_bv_add : forall v o, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v) + o) = Z_to_bv 64 (v + o).
Proof.
intros v o. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma hsb6_astr_kept : forall (rd rd' : reader) p s, astr_atR rd p s ->
(forall i, 0 <= i <= Z.of_nat (length s) -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H1 H2] Hk. split; [|exact H2]. intros i Hi.
rewrite (Hk (Z.of_nat i)) by (rewrite length_app in Hi; cbn [length] in Hi; lia). exact (H1 i Hi).
Qed.

(* a callee-saved register across a call, from its value at the call as an atom of the seed's environment *)
Lemma hsb6_cs_reg : forall (regsT regs2 regs1 : bvmap 5 word) extra (rr : bv 5),
aregs_preserved regsT regs2 -> acallee_saved (bv_unsigned rr) ->
getr regsT rr = ew (Eimg (Ereg regs1 extra)) (Z.to_nat (bv_unsigned rr)) -> getr regs2 rr = getr regs1 rr.
Proof.
intros regsT regs2 regs1 extra rr HP Hc Hr. pose proof (HP (bv_unsigned rr) Hc) as Hx. rewrite Z_to_bv_bv_unsigned in Hx.
rewrite Hx, Hr. apply hsb6_EE. pose proof (bv_unsigned_in_range 5 rr). lia.
Qed.

Lemma hsb6_cs_val : forall (regsT regs2 : bvmap 5 word) (rr : bv 5),
aregs_preserved regsT regs2 -> acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regsT rr.
Proof.
intros regsT regs2 rr HP Hc. pose proof (HP (bv_unsigned rr) Hc) as Hx. rewrite Z_to_bv_bv_unsigned in Hx. exact Hx.
Qed.

Lemma hsb6_rd1 : forall (rd : reader) a v, aval_mem rd a 1 v -> rd a = Some (YO0f.le_byte v 1 0).
Proof.
intros rd a v H. pose proof (H 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r in H0. exact H0.
Qed.

(* 0x8b774 `bltu s5,s7` in the executor's operands: s5 = ~tok (atom 21), s7 = 8n (atom 23) *)
Lemma hsb6_ub774 : forall E t k, bv_unsigned (ew E 21) = 2 ^ 64 - 1 - t -> bv_unsigned (ew E 23) = k ->
  0 <= t < 2 ^ 64 ->
  branch_taken BC_LTU (alu64 ALU_XOR (Z_to_bv 64 t) (Z_to_bv 64 (-1))) (Z_to_bv 64 k) = false ->
  branch_taken BC_LTU (sv_denot E (SOff 21 0)) (sv_denot E (SOff 23 0)) = false.
Proof.
intros E t k H21 H23 Ht HU. cbn [sv_denot]. rewrite H21, H23, !Z.add_0_r.
rewrite <- (hsb6_xor_ones t Ht). exact HU.
Qed.

Ltac hsb6_ro_regions := apply Forall_forall; let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; vm_compute in Hr; repeat (destruct Hr as [<- | Hr]; [cbn; lia|]); destruct Hr.
Ltac hsb6_acs := cbv [acallee_saved]; first [rewrite bv_unsigned_BV; lia | cbn; lia | vm_compute; lia].

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* every byte the recorder's representation reads lies below the heap's ceiling *)
Lemma hsb6_rec_low : forall lyc Sc (Wc : world SEGS) memc mdc R O a, AR SEGS B lyc Sc Wc memc mdc ->
rec_repA B lyc Sc (rdW Wc memc) R O -> hs_in_rec a \/ hs_in_own O a -> 0 <= a < alloc_ceiling.
Proof.
intros lyc Sc Wc memc mdc R O a HAR HREP [Ha | (pn & Hpn & Ha)].
- pose proof asan_consts as (C1 & _). unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
- destruct (hs_rec_own B _ _ _ _ _ HREP pn Hpn) as [Hin _]. destruct pn as [p m]. cbn [fst snd] in Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & H4096 & Hc & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hq]. lia.
Qed.

(* the step through a runtime entry with a Theorem Labs lane's art_post whose writes [Eb] the walk may make (aj_art_at with the
   errno-only premise replaced by awr_byte, closed as aj_intrin_atS closes its own: ajournal_after_write) *)
Lemma hsb6_art_wr : forall stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw
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

(* the runtime entries' read-only view (RtDefs.rt_rom_view) from arodata_okP *)
Lemma hsb6_rom_view : forall (W : world SEGS) mem, arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem.
Proof. intros W mem H a Hrom Ho He. apply H; [left; exact Hrom | exact Ho | exact He]. Qed.

(* the word list's block is none of the recorder's *)
Lemma hsb6_w_distinct : forall lyc Sc (Wc : world SEGS) memc mdc (pb0 pb1 pw : Z * Z) Rest O1 pn,
AR SEGS B lyc Sc Wc memc mdc -> Permutation (ablocks B lyc Sc) ([pb0; pb1; pw] ++ Rest) ->
(forall q, In q O1 -> In q Rest) -> In pn (pb1 :: pb0 :: O1) -> pn <> pw.
Proof.
intros lyc Sc Wc memc mdc pb0 pb1 pw Rest O1 pn HAR HP HO1R Hpn E. subst pn.
pose proof (Permutation_NoDup HP (RecBLemmas.recb_ablocks_nodup_m B _ _ _ _ _ HAR)) as ND. cbn [app] in ND.
apply NoDup_cons_iff in ND as [Hn0 ND1]. apply NoDup_cons_iff in ND1 as [Hn1 ND2].
apply NoDup_cons_iff in ND2 as [Hn2 _].
destruct Hpn as [Hpn | [Hpn | Hpn]].
- apply Hn1. rewrite Hpn. left. reflexivity.
- apply Hn0. rewrite Hpn. right. left. reflexivity.
- exact (Hn2 (HO1R _ Hpn)).
Qed.

(* a byte of a frame of the entry is none of the whole call's footprint *)
Lemma hsb6_frame_notFP : forall x cid pos a, hs_cx B MT x -> In (cid, pos) (frames (i_S x)) ->
frame_addr (i_ly x) cid pos <= a < frame_addr (i_ly x) cid pos + fs_frame_bytes cid -> ~ inFP (hs_FP (i_O x)) a.
Proof.
intros x cid pos a HCX Hin Ha HF.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP0 & _).
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

(* the n-th token at a state the call's journal reaches: readable, its tail visible, in a live block that is none
   of the recorder's *)
Lemma hsb6_tok_now : forall x fpos lyc Sc (Wc : world SEGS) memc mdc k O1 Nw Rest n,
hs_cx B MT x ->
ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)
  [(0, fpos)] lyc Sc Wc memc mdc k ->
hs_ba B x lyc Sc O1 Nw Rest -> (n < length (i_toks x))%nat ->
astr_atR (rdW Wc memc) (hs_ptr x n) (hs_tok x n) /\ Z.of_nat (length (hs_tok x n)) <= LMAX /\
atail_vis SEGS Wc memc (hs_ptr x n + Z.of_nat (length (hs_tok x n))) /\
(exists b kk, In (b, kk) (ablocks B lyc Sc) /\ In (b, kk) (ablocks B (i_ly x) (i_S x)) /\ ~ In (b, kk) (i_O x) /\
   b <= hs_ptr x n /\ hs_ptr x n + Z.of_nat (length (hs_tok x n)) + 1 <= b + kk).
Proof.
intros x fpos lyc Sc Wc memc mdc k O1 Nw Rest n HCX HJ HBA Hn.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen & _ & HTOKS & _ & HREP0 & _).
pose proof HBA as (HP & HRst & HRst2 & _).
pose proof (proj1 HJ) as HARc. pose proof (proj1 HPRE) as HAR0.
assert (HO : forall pn, In pn (i_O x) -> In pn (ablocks B (i_ly x) (i_S x)))
  by (intros pn Hpn; exact (proj1 (hs_rec_own B _ _ _ _ _ HREP0 pn Hpn))).
assert (Hp : nth_error (i_ps x) n = Some (hs_ptr x n)) by (apply hsb6_nth_error_nth; lia).
assert (Ht : nth_error (i_toks x) n = Some (hs_tok x n)) by (apply hsb6_nth_error_nth; lia).
pose proof (hsb6_Forall2_nth _ _ _ _ _ _ HTOKS Hp Ht) as HA.
set (p := hs_ptr x n) in *. set (s := hs_tok x n) in *.
unfold hs_str in HA. cbv zeta in HA. destruct HA as (Hp0 & HS0 & HnL & HBL & HAP).
destruct HBL as (b & kk & Hbk & Hbp & Hpb).
assert (HbO : ~ In (b, kk) (i_O x)).
{ intros HOb. rewrite Forall_forall in HAP. specialize (HAP (b, kk) HOb). cbn [fst snd] in HAP. unfold iv_apart in HAP.
  lia. }
assert (Hbc : In (b, kk) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact (HRst2 _ Hbk HbO). }
destruct (al_blocks _ _ LAWS _ _ _ _ _ b kk HAR0 Hbk) as (_ & Hb4096 & Hbce & _ & _ & _ & Hkk).
pose proof (req_size_pos kk ltac:(lia)) as [_ Hreq].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (KEEP : forall i, 0 <= i <= Z.of_nat (length s) -> rdW Wc memc (p + i) = rdW (i_W x) (i_mem x) (p + i)).
{ intros i Hi. replace (p + i) with (b + (p + i - b)) by lia.
  apply (F2 b kk (p + i - b) Hbk Hbc); [lia|].
  replace (b + (p + i - b)) with (p + i) by lia.
  exact (hs3_blk_outFP B MT HH _ _ _ _ _ (i_O x) b kk (p + i) HAR0 HO Hbk HbO ltac:(lia)). }
split; [apply (hsb6_astr_kept _ _ _ _ HS0); intros i Hi; apply KEEP; lia|].
split; [unfold LMAX in *; lia|].
split; [exact (hh_heap_tail B MT HH lyc Sc Wc memc mdc b kk (p + Z.of_nat (length s)) HARc Hbc ltac:(lia))|].
exists b, kk. split; [exact Hbc|]. split; [exact Hbk|]. split; [exact HbO|]. lia.
Qed.

(* the token array's n-th slot at a state the call's journal reaches *)
Lemma hsb6_arr_now : forall x fpos lyc Sc (Wc : world SEGS) memc mdc k O1 Nw Rest n,
hs_cx B MT x ->
ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)
  [(0, fpos)] lyc Sc Wc memc mdc k ->
hs_ba B x lyc Sc O1 Nw Rest -> (n < length (i_toks x))%nat ->
aval_mem (rdW Wc memc) (i_ptok x + 8 * Z.of_nat n) 8 (hs_ptr x n) /\
range_addressable (rdW Wc memc) SHADOW_OFF (i_ptok x + 8 * Z.of_nat n) 8 /\
in_app (i_ptok x + 8 * Z.of_nat n) 8 /\
(forall q m, In (q, m) (ablocks B lyc Sc) -> (In (q, m) (ablocks B (i_ly x) (i_S x)) -> In (q, m) (i_O x)) ->
  i_ptok x + 8 * Z.of_nat n + 8 <= q \/ q + req_size m <= i_ptok x + 8 * Z.of_nat n).
Proof.
intros x fpos lyc Sc Wc memc mdc k O1 Nw Rest n HCX HJ HBA Hn.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & Hnt & _ & Hp0 & Hp8 & HARR & Hlen & HPTR & _ & _ & HREP0 & _).
pose proof HBA as (HP & HRst & HRst2 & _).
pose proof (proj1 HJ) as HARc. pose proof (proj1 HPRE) as HAR0.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & F2 & _ & F4 & _).
assert (HO : forall pn, In pn (i_O x) -> In pn (ablocks B (i_ly x) (i_S x)))
  by (intros pn Hpn; exact (proj1 (hs_rec_own B _ _ _ _ _ HREP0 pn Hpn))).
assert (Hp : nth_error (i_ps x) n = Some (hs_ptr x n)) by (apply hsb6_nth_error_nth; lia).
pose proof (HPTR n _ Hp) as [_ HV].
set (pt := i_ptok x + 8 * Z.of_nat n) in *.
destruct HARR as [((cid & pos & Hfin & Hcid & Hfal & Hf1 & Hf2) & Hp8' & HRA) | ((b & kk & Hbk & Hb1 & Hb2) & HAP)].
- assert (Hfinc : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hfin).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR0 Hfin) as (Hf4096 & Hfc & Hfapp).
  pose proof (al_layout _ _ LAWS _ _ _ _ _ lyc HAR0 Hly) as (_ & HFA & _).
  split.
  { intros j Hj. rewrite (F4 cid pos _ Hfin); [exact (HV j Hj) | |].
    - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
    - apply (hsb6_frame_notFP x cid pos); [exact HCX | exact Hfin | lia]. }
  split.
  { assert (HRAc : range_addressable (rdW Wc memc) SHADOW_OFF (i_ptok x) (8 * Z.of_nat (length (i_toks x)))).
    { apply (range_addressable_entry_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos _ _ HJ Hfin Hcid Hf1 Hf2 Hfal);
        [| exact HAR0 | exact HRA].
      intros a Ha. unfold hs_FP in Ha. apply inFP_cons in Ha as [Ha|Ha]; [unfold A_G_REC, REC_SIZE, kLowShadowBeg in *; lia|].
      apply inFP_cons in Ha as [Ha|Ha]; [unfold A_REC_SPILL, SC_SIZE, kLowShadowBeg in *; lia|].
      destruct (inFP_ablocks_fp_inv _ _ Ha) as (q & m & Hqm & Hr).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR0 (HO (q, m) Hqm)) as (_ & _ & _ & Happ & _).
      unfold in_app, kLowShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. lia. }
    eapply range_addressable_sub; [exact HRAc | lia | lia]. }
  split; [apply (in_app_sub _ _ _ _ Hfapp); lia|].
  intros q m Hq _. pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q m cid pos HARc Hq Hfinc) as Hd.
  rewrite HFA in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- assert (HbO : ~ In (b, kk) (i_O x)).
  { intros HOb. rewrite Forall_forall in HAP. specialize (HAP (b, kk) HOb). cbn [fst snd] in HAP. unfold iv_apart in HAP. lia. }
  assert (Hbc : In (b, kk) (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact (HRst2 _ Hbk HbO)).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b kk HAR0 Hbk) as (_ & Hb4096 & Hbce & Hbapp & _ & _ & Hkk).
  pose proof (req_size_pos kk ltac:(lia)) as [_ Hreq].
  split.
  { intros j Hj. replace (pt + Z.of_nat j) with (b + (pt + Z.of_nat j - b)) by lia.
    rewrite (F2 b kk (pt + Z.of_nat j - b) Hbk Hbc ltac:(lia)).
    - replace (b + (pt + Z.of_nat j - b)) with (pt + Z.of_nat j) by lia. exact (HV j Hj).
    - exact (hs3_blk_outFP B MT HH _ _ _ _ _ (i_O x) b kk (b + (pt + Z.of_nat j - b)) HAR0 HO Hbk HbO ltac:(lia)). }
  split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc b kk pt 8 HARc Hbc ltac:(lia) ltac:(lia))|].
  split; [apply (in_app_sub _ _ _ _ Hbapp); lia|].
  intros q m Hq HqO.
  assert (Hne : (q, m) <> (b, kk)) by (intros E; rewrite E in HqO; exact (HbO (HqO Hbk))).
  pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ q m b kk HARc Hq Hbc Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the entry state of the run at L2S *)
Lemma hsb6_seedS : forall (Wc : world SEGS) lyc Sc memc mdc (regs1 : bvmap 5 word) wp wsz L ptok k8 pn,
AR SEGS B lyc Sc Wc memc mdc -> In (wp, wsz) (ablocks B lyc Sc) -> 0 <= L -> L + 2 <= wsz -> L <= 8192 ->
2 ^ 46 <= spZ regs1 <= 2 ^ 47 -> spZ regs1 mod 16 = 0 ->
getr regs1 26 = w64 HS_SB -> getr regs1 22 = w64 wp -> getr regs1 10 = w64 L ->
getr regs1 24 = w64 ptok -> getr regs1 23 = w64 k8 -> 0 <= ptok -> 0 <= k8 ->
(ptok + k8) mod 8 = 0 -> in_app (ptok + k8) 8 ->
aval_mem (rdW Wc memc) (ptok + k8) 8 pn -> 0 <= pn < 2 ^ 64 ->
range_addressable (rdW Wc memc) SHADOW_OFF (ptok + k8) 8 ->
(ptok + k8 + 8 <= wp \/ wp + req_size wsz <= ptok + k8) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (hsb6_xS (wp + L) (ptok + k8) pn))) hsb6_ssS
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_L2S)) memc (seg_rom SEGS))) /\
sh_ok SEGS hsb6_Bx hsb6_SHS (Eimg (Ereg regs1 (hsb6_xS (wp + L) (ptok + k8) pn))) (mrestrict (w_H Wc) memc).
Proof.
intros Wc lyc Sc memc mdc regs1 wp wsz L ptok k8 pn HAR Hin HL0 HL2 HL8 Hsp Hsp16 R26 R22 R10 R24 R23 Hpt0 Hk0
  Hpt8 Happ Hv Hpn Hra Hdis.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSB : HS_SB = 0x7fff8000) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc wp wsz HAR Hin) as (Hw16 & Hw4096 & Hwc & Hwapp & Hwpres & _ & Hwn).
pose proof (req_size_pos wsz ltac:(lia)) as [_ Hreq].
set (pt := ptok + k8) in *.
assert (Hpt : 4096 <= pt /\ pt + 8 <= 0x7fffff800000)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ; lia).
set (E := Eimg (Ereg regs1 (hsb6_xS (wp + L) pt pn))).
assert (E2 : ew E 2 = getr regs1 2) by exact (hsb6_EE _ _ 2 2%bv eq_refl).
assert (E10 : ew E 10 = Z_to_bv 64 L) by exact (eq_trans (hsb6_EE _ _ 10 10%bv eq_refl) R10).
assert (E22 : ew E 22 = Z_to_bv 64 wp) by exact (eq_trans (hsb6_EE _ _ 22 22%bv eq_refl) R22).
assert (E23 : ew E 23 = Z_to_bv 64 k8) by exact (eq_trans (hsb6_EE _ _ 23 23%bv eq_refl) R23).
assert (E24 : ew E 24 = Z_to_bv 64 ptok) by exact (eq_trans (hsb6_EE _ _ 24 24%bv eq_refl) R24).
assert (E26 : ew E 26 = Z_to_bv 64 HS_SB) by exact (eq_trans (hsb6_EE _ _ 26 26%bv eq_refl) R26).
assert (E32 : ew E 32 = Z_to_bv 64 (wp + L)) by exact (hsb6_EX regs1 (hsb6_xS (wp + L) pt pn) 0 ltac:(unfold A_TEXT; lia)).
assert (E33 : ew E 33 = Z_to_bv 64 pt) by exact (hsb6_EX regs1 (hsb6_xS (wp + L) pt pn) 1 ltac:(unfold A_TEXT; lia)).
assert (E34 : ew E 34 = Z_to_bv 64 pn) by exact (hsb6_EX regs1 (hsb6_xS (wp + L) pt pn) 2 ltac:(unfold A_TEXT; lia)).
assert (U2 : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = L) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = wp) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = k8) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = ptok) by (rewrite E24; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = HS_SB) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = wp + L) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = pt) by (rewrite E33; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. split.
- unfold hsb6_ssS. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hwpres (wp + L + o) ltac:(lia))).
    * rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ pt 0 8 (SOff 34 0) pn); [exact (hsb6_den_off0 E 34 pn E34) | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (hsb6_val_of_aval Wc memc pt 8 pn Hv).
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [hsb6_fS f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U26, U22, U10, U32, U33. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat split; lia.
    * cbn [hsb6_fS f_alias alias_ok]. split; [|split; [|exact I]]; cbn [sv_denot].
      -- rewrite U22, U10, U32, !Z.add_0_r. apply hsb6_add.
      -- rewrite U24, U23, U33, !Z.add_0_r. apply hsb6_add.
- unfold sh_ok, hsb6_SHS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E hsb6_Bx 32 wp (req_size wsz) (wp + L) 0 2).
    * exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc wp wsz wp (req_size wsz) HAR Hin
        ltac:(lia) ltac:(lia)).
    * unfold hsb6_Bx. rewrite (hsb6_U_off E 26 0 HS_SB E26) by lia. unfold HS_SB, SHADOW_OFF. lia.
    * rewrite (hsb6_U_off E 32 0 (wp + L) E32) by lia. lia.
    * lia.
    * lia.
    * intros a Ha. apply (hsb6_in_app_noshadow wp (req_size wsz)); [exact Hwapp | lia].
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E hsb6_Bx 33 pt 8 pt 0 8).
    * exact Hra.
    * unfold hsb6_Bx. rewrite (hsb6_U_off E 26 0 HS_SB E26) by lia. unfold HS_SB, SHADOW_OFF. lia.
    * rewrite (hsb6_U_off E 33 0 pt E33) by lia. lia.
    * lia.
    * lia.
    * intros a Ha. apply (hsb6_in_app_noshadow pt 8); [exact Happ | lia].
Qed.

(* the entry state of the run at L2C *)
Lemma hsb6_seedC : forall (Wc : world SEGS) memc (regs1 : bvmap 5 word) sp1 ntok n c F,
2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 16 = 0 ->
getr regs1 2 = w64 sp1 -> getr regs1 9 = w64 sp1 -> getr regs1 18 = w64 ntok -> getr regs1 27 = w64 n ->
1 <= ntok <= 64 -> 0 <= n <= 63 -> 0 <= c < 2 ^ 64 -> 0 <= F < 2 ^ 64 ->
aval_mem (rdW Wc memc) (sp1 + 8) 8 c -> aval_mem (rdW Wc memc) (sp1 + 16) 8 F ->
aval_mem (rdW Wc memc) (sp1 + 24) 8 F ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (hsb6_xC c F))) hsb6_ssC
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_L2C)) memc (seg_rom SEGS))).
Proof.
intros Wc memc regs1 sp1 ntok n c F Hsp Hsp16 R2 R9 R18 R27 Hnt Hn Hc HF V8 V16 V24.
set (E := Eimg (Ereg regs1 (hsb6_xC c F))).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by exact (eq_trans (hsb6_EE _ _ 2 2%bv eq_refl) R2).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by exact (eq_trans (hsb6_EE _ _ 9 9%bv eq_refl) R9).
assert (E18 : ew E 18 = Z_to_bv 64 ntok) by exact (eq_trans (hsb6_EE _ _ 18 18%bv eq_refl) R18).
assert (E27 : ew E 27 = Z_to_bv 64 n) by exact (eq_trans (hsb6_EE _ _ 27 27%bv eq_refl) R27).
assert (E32 : ew E 32 = Z_to_bv 64 c) by exact (hsb6_EX regs1 (hsb6_xC c F) 0 ltac:(unfold A_TEXT; lia)).
assert (E33 : ew E 33 = Z_to_bv 64 F) by exact (hsb6_EX regs1 (hsb6_xC c F) 1 ltac:(unfold A_TEXT; lia)).
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = ntok) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = n) by (rewrite E27; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold hsb6_ssC. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + apply (chunk_ok_val SEGS E _ sp1 8 8 (SOff 32 0) c); [exact (hsb6_den_off0 E 32 c E32) | cbn; lia | cbn; lia |].
    exact (hsb6_val_of_aval Wc memc (sp1 + 8) 8 c V8).
  + apply (chunk_ok_val SEGS E _ sp1 16 8 (SOff 33 0) F); [exact (hsb6_den_off0 E 33 F E33) | cbn; lia | cbn; lia |].
    exact (hsb6_val_of_aval Wc memc (sp1 + 16) 8 F V16).
  + apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 33 0) F); [exact (hsb6_den_off0 E 33 F E33) | cbn; lia | cbn; lia |].
    exact (hsb6_val_of_aval Wc memc (sp1 + 24) 8 F V24).
- apply pairwise_disjoint_of_extents. cbn. tauto.
- split; [|split; [exact I | exact I]].
  cbn [hsb6_fC f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U9, U18, U27. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
Qed.

(* a range inside a live block is one the entries may write, at a state whose sp lies above the heap *)
Lemma hsb6_wr_block : forall stk lyc Sc (Wc : world SEGS) memc mdc (regs : bvmap 5 word) p k d m,
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

(* ---- L2S n: from the strlen return (0x8b744) through the separator stores and the strcat wrapper to 0x8b798 ---- *)
Lemma hs_seg_l2s : forall x n, ST_L2C B MT x n -> ST_L2S B MT x n.
Proof.
intros x n HL2C. unfold ST_L2S.
intros fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 wp [Hn1 Hn] HCX FXR HMID HREP HSPILL HSTR Hw4 HR1 R10.
pose proof (hh_strcat B MT HH fx) as hstrcat. pose proof (hh_heap_tail B MT HH) as hheap_tail.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10 & H11 & H12 & Hnt & HLINE & Hp0 & Hp8 & HARR & Hlen
  & HPTR & HTOKS & HWL & HREP0 & HFR8 & HEV & HLIVE & HMOK & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJ & Hk & MLE & HBB & HFRM & HFLG & HBA).
pose proof HBA as (HP & HRst & HRst2 & HRO1 & HO1 & HNw & HO1R).
pose proof HR1 as ((R2 & R9 & R8 & R3 & R4 & R24 & R25 & R26) & R22 & R23 & R27 & R21 & R18 & R20).
pose proof HSPILL as (SP8 & SP16 & SP24).
pose proof (proj1 HJ) as HARc.
pose proof hs3_stk as FS.
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (S1a & S1b & S1c).
destruct (hs3_frame_facts B MT x fpos lyc Sc Wc memc mdc k HCX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
assert (HPT : 4096 <= i_ptok x /\ i_ptok x + 8 * Z.of_nat (length (i_toks x)) <= alloc_ceiling).
{ apply (hsb_arr_bound B (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) (i_ptok x) (8 * Z.of_nat (length (i_toks x)))
    ltac:(lia) HAR0).
  destruct HARR as [H | [H _]]; [left | right]; exact H. }
assert (Hes : ESTACK = 4096) by reflexivity. assert (HLM : LMAX = 8192) by reflexivity.
assert (HSB : HS_SB = 0x7fff8000) by reflexivity.
set (sp0 := spZ (i_regs x)) in *.
set (sp1 := hs_sp1 sp0) in *.
assert (Hsp1 : spZ regs1 = sp1) by (unfold spZ at 1; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the word list's block, new in this call or one of the recorder's *)
set (wsz := LIVE_XMALLOC (hs_wsz x)) in *.
assert (Hwsz : wsz = hs_words_len (i_toks x) + 1).
{ unfold wsz, LIVE_XMALLOC, hs_wsz. pose proof (hs3_wl_nonneg (i_toks x)). lia. }
assert (Hinw : In (wp, wsz) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym HP)). cbn [app]. right; right; left. reflexivity. }
assert (HwO : In (wp, wsz) (ablocks B (i_ly x) (i_S x)) -> In (wp, wsz) (i_O x))
  by (intros Hi; apply HNw; [right; right; left; reflexivity | exact Hi]).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc wp wsz HARc Hinw) as (Hw16 & Hw4096 & Hwc & Hwapp & Hwpres & _ & Hwn).
pose proof (req_size_pos wsz ltac:(lia)) as [_ Hreq].
(* the lengths along the join *)
assert (Hne : firstn n (i_toks x) <> []) by (apply hsb6_firstn_ne; lia).
pose proof (hsb6_join_len _ Hne) as HJL.
pose proof (hsb6_wl_S (i_toks x) n Hn) as HWS. change (nth n (i_toks x) []) with (hs_tok x n) in HWS.
pose proof (hsb6_wl_firstn (i_toks x) (S n)) as HWF.
pose proof (hsb_join_sep_in (i_toks x) n Hn1 Hn) as HSEP.
assert (Htne : i_toks x <> []) by (intros Et; rewrite Et in Hnt; cbn [length] in Hnt; lia).
pose proof (hsb6_join_len (i_toks x) Htne) as HJA.
set (L := Z.of_nat (length (join_sp (firstn n (i_toks x))))) in *.
assert (HLT : L + Z.of_nat (length (hs_tok x n)) + 2 <= hs_words_len (i_toks x)) by lia.
assert (AWRW : forall a, wp <= a < wp + req_size wsz ->
  awr_byte SEGS B SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x)) (ablocks B (i_ly x) (i_S x)) (ablocks B lyc Sc)
    (frames (i_S x)) lyc [(0, fpos)] a).
{ intros a Ha. destruct (in_dec hs3_pair_dec (wp, wsz) (ablocks B (i_ly x) (i_S x))) as [Hi | Hni].
  - right. left. split; [|exists wp, wsz; split; [exact Hinw | exact Ha]].
    unfold hs_FP. apply inFP_cons. right. apply inFP_cons. right.
    replace a with (wp + (a - wp)) by lia. apply (inFP_ablocks_fp _ wp wsz (a - wp) (HwO Hi)). lia.
  - right. right. left. exists wp, wsz. split; [exact Hinw|]. split; [exact Hni | exact Ha]. }
(* the token array's slot and the token *)
destruct (hsb6_arr_now x fpos lyc Sc Wc memc mdc k O1 _ Rest n HCX HJ HBA Hn) as (HV & HRA & Happ & HAPT).
assert (Hpn0 : nth_error (i_ps x) n = Some (hs_ptr x n)) by (apply hsb6_nth_error_nth; lia).
pose proof (proj1 (HPTR n _ Hpn0)) as Hpn64.
set (pn := hs_ptr x n) in *. set (s := hs_tok x n) in *.
set (pt := i_ptok x + 8 * Z.of_nat n) in *.
assert (Hpt8 : pt mod 8 = 0).
{ unfold pt. replace (i_ptok x + 8 * Z.of_nat n) with (i_ptok x + Z.of_nat n * 8) by lia.
  rewrite Z_mod_plus_full. exact Hp8. }
assert (Hsp16 : sp1 mod 16 = 0).
{ unfold sp1, hs_sp1. replace (32 * ((sp0 - 160) / 32)) with ((2 * ((sp0 - 160) / 32)) * 16) by ring.
  apply Z.mod_mul. lia. }
destruct (hsb6_seedS Wc lyc Sc memc mdc regs1 wp wsz L (i_ptok x) (8 * Z.of_nat n) pn HARc Hinw ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(rewrite Hsp1; lia) ltac:(rewrite Hsp1; exact Hsp16) R26 R22 R10 R24 R23 ltac:(lia) ltac:(lia) Hpt8 Happ HV
  Hpn64 HRA (HAPT wp wsz Hinw HwO)) as [HS SHOK].
fold pt in HS, SHOK.
set (E := Eimg (Ereg regs1 (hsb6_xS (wp + L) pt pn))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by exact (eq_trans (hsb6_EE _ _ 2 2%bv eq_refl) R2).
assert (E20 : ew E 20 = Z_to_bv 64 32) by exact (eq_trans (hsb6_EE _ _ 20 20%bv eq_refl) R20).
assert (E21 : ew E 21 = Z_to_bv 64 (2 ^ 64 - 1 - i_ptok x)) by exact (eq_trans (hsb6_EE _ _ 21 21%bv eq_refl) R21).
assert (E23 : ew E 23 = Z_to_bv 64 (8 * Z.of_nat n)) by exact (eq_trans (hsb6_EE _ _ 23 23%bv eq_refl) R23).
assert (E32 : ew E 32 = Z_to_bv 64 (wp + L)) by exact (hsb6_EX regs1 (hsb6_xS (wp + L) pt pn) 0 ltac:(unfold A_TEXT; lia)).
assert (E34 : ew E 34 = Z_to_bv 64 pn) by exact (hsb6_EX regs1 (hsb6_xS (wp + L) pt pn) 2 ltac:(unfold A_TEXT; lia)).
assert (U32 : bv_unsigned (ew E 32) = wp + L) by (rewrite E32; apply unsigned_lit_small; lia).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by (intros nn r Hnn; unfold E; apply hsb6_EE; exact Hnn).
clearbody E.
unfold hs_at.
(* 0x8b744 .. 0x8b770: a0 := w + L, the two store_n checks of [w + L, w + L + 2), w[L] := ' ', w[L+1] := 0; the run
   stops at the UBSan check 0x8b774.
   0x8b754/0x8b7ac: refuted by hsb6_seedS at sup_host_setting_s6.v:469, from range_addressable_of_block of the word
   list's block (hs_mid's Nw, ST_L2S) with L + 2 <= |join_sp toks| + 1 (hsb_join_sep_in): the token executor reads
   shadow byte 0 at (w + L) >> 3, `bnez a1` not taken.
   0x8b768/0x8b7b8: refuted by hsb6_seedS at sup_host_setting_s6.v:469, from the same block fact: shadow byte 0 at
   (w + L + 1) >> 3, `bnez a1` not taken. *)
paj_run_tok RUN HS HJ SHOK hsb6_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?bb0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp bb0 bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AWRW. lia. }
clear HF HG. rename HFr into HFr1. rename ms into ms1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md1 := m) in *; clearbody md1 end.
(* 0x8b774 `bltu s5,s7`: the UBSan check of &tok[n] *)
psrr_branch_tok RUN BR HS SHOK hsb6_Bspan.
- (* 0x8b774: refuted by hsb_ub_774 at sup_host_setting_aux.v:126 (through hsb_ubsan_tok, sup_host_setting_aux.v:210,
     and hsb6_ub774), from hs_cx's array premise (afobj or a live block, so ptok + 8 ntok <= alloc_ceiling,
     hsb_arr_bound) with n < ntok: s5 = ~tok, s7 = 8n, the trap arm to 0x8b8c0 is not taken *)
  exfalso.
  pose proof (hsb_ubsan_tok B (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) (i_O x) (i_ptok x) (Z.of_nat (length (i_toks x)))
    (Z.of_nat n) HAR0 Hp0 Hp8 HARR ltac:(lia)) as (_ & _ & _ & U774).
  lazymatch type of Hc with context [sv_denot ?Env (SOff 21 0)] =>
    assert (X21 : bv_unsigned (ew Env 21) = 2 ^ 64 - 1 - i_ptok x)
      by (rewrite ?ew_ewset_other by lia; rewrite E21; apply unsigned_lit_small; lia);
    assert (X23 : bv_unsigned (ew Env 23) = 8 * Z.of_nat n)
      by (rewrite ?ew_ewset_other by lia; rewrite E23; apply unsigned_lit_small; lia);
    rewrite (hsb6_ub774 Env (i_ptok x) (8 * Z.of_nat n) X21 X23 ltac:(lia) U774) in Hc; discriminate Hc
  end.
- (* not taken: 0x8b778 .. 0x8b794: a0 := tok + 8n, the load8 check of &tok[n], a1 := tok[n], a0 := w, strcat.
     0x8b788: refuted by hsb6_seedS at sup_host_setting_s6.v:469, from hsb6_arr_now (sup_host_setting_s6.v:407):
     the slot &tok[n] is addressable (afobj's range or a live block, hs_cx's array premise), so the token executor
     reads shadow byte 0 at (tok + 8n) >> 3, `bnez a1` not taken *)
  paj_run_tok RUN HS HJ SHOK hsb6_Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?bb0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp bb0 bc fr lyx own) end.
    eapply awr_ok_cons_gen; [reflexivity | rewrite ?ew_ewset_other by lia; exact U32 |
      | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply AWRW. lia. }
  clear HF HG. rename HFr into HFr2. rename ms into ms2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in *; clearbody md2 end.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  (* register facts at the strcat call *)
  assert (QSP : spZ (ms_regs ms2) = sp0 + (sp1 - sp0)).
  { unfold spZ at 1. rewrite Q2, (EE 2%nat 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (QRA : YK0s.ret_ok (getr (ms_regs ms2) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Q3' : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite Q3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
  assert (Q4' : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite Q4, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
  assert (Q10' : getr (ms_regs ms2) 10 = w64 wp) by (rewrite Q10, (EE 22%nat 22%bv eq_refl), R22; reflexivity).
  assert (Q11' : getr (ms_regs ms2) 11 = w64 pn) by (rewrite Q11, E34; reflexivity).
  (* the separator bytes the run wrote, and the bytes it kept *)
  lazymatch type of HS with
  | st_ok _ ?Env _ _ =>
    assert (EA : forall nn, (nn < 1024)%nat -> ew Env nn = ew E nn)
      by (intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity);
    assert (EcU32 : bv_unsigned (ew Env 32) = wp + L) by (rewrite (EA 32%nat ltac:(lia)); exact U32);
    pose proof (st_ok_region_nth Env _ _ 0%nat _ HS ltac:(cbn; reflexivity)) as HRg0;
    cbn [ms_mem restrict] in HRg0;
    assert (Dval0 : bv_unsigned (sv_denot Env (SOff 20 0)) mod 2 ^ (8 * Z.of_N 1) = 32)
      by (cbn [sv_denot]; rewrite (EA 20%nat ltac:(lia)), E20; vm_compute; reflexivity);
    assert (Dval1 : bv_unsigned (sv_denot Env (SLit 0)) mod 2 ^ (8 * Z.of_N 1) = 0)
      by (cbn [sv_denot]; vm_compute; reflexivity);
    assert (B0v : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms2)) (wp + L) 1 32)
      by (pose proof (field_of_region_any Env _ 32 (wp + L) _ 0 2 0 2 0 1%N (SOff 20 0) HRg0 EcU32 ltac:(cbn; tauto)
            ltac:(cbn; lia)) as V0;
          rewrite Z.add_0_r, Dval0 in V0; cbn [N.to_nat] in V0; exact V0);
    assert (B1v : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms2)) (wp + L + 1) 1 0)
      by (pose proof (field_of_region_any Env _ 32 (wp + L) _ 0 2 0 2 1 1%N (SLit 0) HRg0 EcU32 ltac:(cbn; tauto)
            ltac:(cbn; lia)) as V1;
          rewrite Dval1 in V1; cbn [N.to_nat] in V1; exact V1)
  end.
  assert (B0 : rdW Wc (ms_mem ms2) (wp + L) = Some 32).
  { pose proof (hsb6_rd1 _ _ _ (hsb6_aval_of_val Wc (ms_mem ms2) (wp + L) 1 32 B0v)) as HHb. rewrite HHb.
    vm_compute. reflexivity. }
  assert (B1 : rdW Wc (ms_mem ms2) (wp + L + 1) = Some 0).
  { pose proof (hsb6_rd1 _ _ _ (hsb6_aval_of_val Wc (ms_mem ms2) (wp + L + 1) 1 0 B1v)) as HHb. rewrite HHb.
    vm_compute. reflexivity. }
  assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (wp + L <= a < wp + L + 2) -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
  { intros a Ha Hna.
    apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms1) (fun a0 => wp + L <= a0 < wp + L + 2) HFr1);
      [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U32 in Hrr; lia|]);
        destruct Hin
      | exact Ha | exact Hna ]. }
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (wp + L <= a < wp + L + 2) ->
    rdW Wc (ms_mem ms2) a = rdW Wc (ms_mem ms1) a).
  { intros a Ha Hna.
    apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) (ms_mem ms1) (ms_mem ms2) (fun a0 => wp + L <= a0 < wp + L + 2) HFr2);
      [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
          rewrite ?ew_ewset_other in Hrr by lia; rewrite ?U32 in Hrr; lia|]);
        destruct Hin
      | exact Ha | exact Hna ]. }
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (wp + L <= a < wp + L + 2) -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
    by (intros a Ha Hna; rewrite (KR2 a Ha Hna); exact (KR1 a Ha Hna)).
  (* the destination string after the separator stores, and the token at the current state *)
  assert (HDST : astr_atR (rdW Wc (ms_mem ms2)) wp (join_sp (firstn n (i_toks x)) ++ [SPACE])).
  { apply (hsb6_astr_sep (rdW Wc memc) (rdW Wc (ms_mem ms2)) wp (join_sp (firstn n (i_toks x))) HSTR).
    - intros i Hi. apply KEEP2; [lia | unfold L in *; lia].
    - exact B0.
    - exact B1. }
  destruct (hsb6_tok_now x fpos lyc Sc Wc (ms_mem ms2) md2 k O1 _ Rest n HCX HJ HBA Hn) as (HSsrc1 & HsL1 & HTsrc1 & Harm1).
  change (hs_ptr x n) with pn in HSsrc1, HsL1, HTsrc1, Harm1.
  change (hs_tok x n) with s in HSsrc1, HsL1, HTsrc1, Harm1.
  assert (Hdl : astr_len (join_sp (firstn n (i_toks x)) ++ [SPACE]) = L + 1)
    by (unfold astr_len, L; rewrite length_app; cbn [length]; lia).
  assert (Hpn4 : 4096 <= pn).
  { destruct Harm1 as (bb & kb & Hbc & _ & _ & Hbb1 & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bb kb (proj1 HJ) Hbc) as (_ & Hb4 & _). lia. }
  (* the source string's read-ok and the disjointness of the two blocks *)
  assert (Hsrc : (pn + Z.of_nat (length s) + 1 <= wp \/ wp + req_size wsz <= pn) /\
                 aread_ok SEGS (2 * ESTACK) Wc (ms_regs ms2) (ms_mem ms2) pn (astr_len s + 1)).
  { destruct Harm1 as (bb & kb & Hbc & Hbe & HbO & Hbb1 & Hbb2).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bb kb (proj1 HJ) Hbc) as (_ & _ & _ & _ & _ & _ & Hkb0).
    pose proof (req_size_pos kb ltac:(lia)) as [_ Hkreq].
    assert (Hwbne : (wp, wsz) <> (bb, kb)) by (intros Eq; injection Eq as Ew Ek; subst bb kb; exact (HbO (HwO Hbe))).
    pose proof (sep_blocks SEGS B LAWS lyc Sc Wc (ms_mem ms2) md2 wp wsz bb kb (proj1 HJ) Hinw Hbc Hwbne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. split; [lia|].
    apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 bb kb pn (astr_len s + 1)
      (proj1 HJ) Hbc); [lia | unfold astr_len; lia | unfold astr_len; lia | rewrite QSP; lia]. }
  destruct Hsrc as [Hdisj Hrdsrc].
  (* the token's block again, for strcat's band and word-separation premises (RtString.v astrcat_realizes, B BASE 2) *)
  pose proof Harm1 as (tb & tk & Htbc & Htbe & HtbO & Htbb1 & Htbb2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ tb tk (proj1 HJ) Htbc) as (_ & _ & _ & _ & _ & _ & Htk0).
  pose proof (req_size_pos tk ltac:(lia)) as [_ Htkreq].
  assert (Htbwne : (tb, tk) <> (wp, wsz)) by (intros Eq; injection Eq as Ew Ek; subst tb tk; exact (HtbO (HwO Htbe))).
  (* the strcat wrapper on (w holding join_sp (firstn n toks) ++ [' '], tok n), back at 0x8b798 *)
  eapply SRr_bind.
  { eapply (hsb6_art_wr (2 * ESTACK)
      (fun a => wp + astr_len (join_sp (firstn n (i_toks x)) ++ [SPACE]) <= a
                < wp + astr_len (join_sp (firstn n (i_toks x)) ++ [SPACE]) + astr_len s + 1)
      (SIG CS___interceptor_trampoline_strcat) Wc (ms_regs ms2) (ms_mem ms2) SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x))
      (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc md2 k (sp1 - sp0) (Z_to_bv 64 (BASE + HS_L2C)) _
      HJ QSP ltac:(lia) ltac:(lia) ltac:(lia) Q1).
    - intros a HE. rewrite Hdl in HE. apply AWRW. unfold astr_len in HE. lia.
    - apply (hstrcat lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 wp pn (join_sp (firstn n (i_toks x)) ++ [SPACE]) s).
      + exact (ecall_pre_stk_at SEGS B (2 * ESTACK) SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x)
          (i_mem x) (i_md x) [(0, fpos)] lyc Sc Wc (ms_mem ms2) md2 k (ms_regs ms2) (sp1 - sp0) HJ QSP S1b ltac:(lia)
          ltac:(lia) ltac:(lia) QRA Q3' Q4').
      + exact Q10'.
      + exact Q11'.
      + lia.
      + lia.
      + apply (astr_atR_view SEGS). exact HDST.
      + apply (astr_atR_view SEGS). exact HSsrc1.
      + rewrite Hdl. apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 wp wsz wp
          (L + 1 + 1) (proj1 HJ) Hinw); [lia | lia | lia | rewrite QSP; lia].
      + (* the destination string's band: the word list's block *)
        rewrite Hdl. apply (amem8_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms2) md2 wp wsz wp (L + 1) (proj1 HJ) Hinw); lia.
      + exact Hrdsrc.
      + (* the source string's band: token n's block *)
        apply (amem8_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms2) md2 tb tk pn (astr_len s) (proj1 HJ) Htbc);
          unfold astr_len; lia.
      + rewrite Hdl. apply (hsb6_wr_block (2 * ESTACK) lyc Sc Wc (ms_mem ms2) md2 (ms_regs ms2) wp wsz (wp + (L + 1))
          (astr_len s + 1) (proj1 HJ) Hinw); [lia | unfold astr_len; lia | unfold astr_len; lia | rewrite QSP; lia].
      + (* the written range's band: the word list's block *)
        rewrite Hdl. apply (amem8_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms2) md2 wp wsz (wp + (L + 1)) (astr_len s)
          (proj1 HJ) Hinw); unfold astr_len; lia.
      + (* the written range holds no read-only image byte: the word list's heap block *)
        intros a Ha _. rewrite Hdl in Ha. apply (hs3_heap_norom B lyc Sc Wc (ms_mem ms2) md2 wp wsz a (proj1 HJ) Hinw).
        unfold astr_len in Ha. lia.
      + rewrite Hdl. apply (hheap_tail lyc Sc Wc (ms_mem ms2) md2 wp wsz (wp + (L + 1)) (proj1 HJ) Hinw). lia.
      + exact HTsrc1.
      + rewrite Hdl. unfold astr_len. lia.
      + (* the destination tail does not start inside the token's last word: two live blocks, 16-aligned *)
        rewrite Hdl. apply (hs3_word_sep B lyc Sc Wc (ms_mem ms2) md2 tb tk wp wsz pn (astr_len s) (wp + (L + 1))
          (proj1 HJ) Htbc Hinw Htbwne); unfold astr_len in *; lia.
      + exact (hsb6_rom_view Wc (ms_mem ms2) (proj1 (hs3_rod_now B MT HH x fpos lyc Sc Wc (ms_mem ms2) md2 k HCX HJ))). }
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md3 & -> & HJ2 & HP2 & HQr & KEEPS).
  destruct HQr as [Hq10f HDSTab].
  (* memory kept across the strcat: outside its scratch window and the word list's block *)
  assert (KEEPX : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) -> ~ (wp <= a < wp + req_size wsz) ->
    rdW Wc mem2 a = rdW Wc memc a).
  { intros a Ha Hs Hw.
    rewrite (KEEPS a Ha ltac:(lia) ltac:(intros HE; apply Hw; rewrite Hdl in HE; unfold astr_len in HE; lia)).
    apply KEEP2; [exact Ha | lia]. }
  assert (KEEPrec : forall a, hs_in_rec a \/ hs_in_own ((b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) a ->
    rdW Wc mem2 a = rdW Wc memc a).
  { intros a HR. apply KEEPX.
    - destruct HR as [Ha | ([q m] & Hpm & Ha)].
      + unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
      + cbn [fst snd] in Ha. destruct (hs_rec_own B lyc Sc (rdW Wc memc) _ _ HREP (q, m) Hpm) as [Hqin _].
        destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hqin) as (_ & Hq4 & Hqc & _ & _ & _ & Hm0).
        pose proof (req_size_pos m ltac:(lia)) as [_ Hmr]. lia.
    - destruct HR as [Ha | ([q m] & Hpm & Ha)].
      + unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
      + cbn [fst snd] in Ha. destruct (hs_rec_own B lyc Sc (rdW Wc memc) _ _ HREP (q, m) Hpm) as [Hqin _].
        destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hqin) as (_ & Hq4 & Hqc & _ & _ & _ & Hm0).
        pose proof (req_size_pos m ltac:(lia)) as [_ Hmr]. lia.
    - destruct HR as [Ha | ([q m] & Hpm & Ha)].
      + pose proof (blk_off_imgP B lyc Sc Wc memc mdc wp wsz HARc Hinw) as Hoff. unfold off_img in Hoff.
        unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
      + cbn [fst snd] in Ha.
        pose proof (proj1 (hs_rec_own B lyc Sc (rdW Wc memc) _ _ HREP (q, m) Hpm)) as Hqin.
        destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hqin) as (_ & _ & _ & _ & _ & _ & Hm0).
        pose proof (req_size_pos m ltac:(lia)) as [_ Hmr].
        assert (Hqwne : (q, m) <> (wp, wsz))
          by exact (hsb6_w_distinct lyc Sc Wc memc mdc (b0, hs_b0 x) (b1, hs_b1 x) (wp, wsz) Rest O1 (q, m) HARc HP HO1R Hpm).
        pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc q m wp wsz HARc Hqin Hinw Hqwne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  (* the join_sp of the first (S n) tokens, now in the word list *)
  assert (HListEq : (join_sp (firstn n (i_toks x)) ++ [SPACE]) ++ s ++ [Z_to_bv 8 0]
                    = join_sp (firstn (S n) (i_toks x)) ++ [Z_to_bv 8 0]).
  { rewrite (hsb_firstn_S (i_toks x) n [] Hn). change (nth n (i_toks x) []) with s.
    rewrite hsb_join_snoc by exact Hne. rewrite <- !app_assoc. reflexivity. }
  assert (HDnz : ~ In (Z_to_bv 8 0) (join_sp (firstn (S n) (i_toks x)))).
  { rewrite (hsb_firstn_S (i_toks x) n [] Hn). change (nth n (i_toks x) []) with s.
    rewrite hsb_join_snoc by exact Hne.
    intros HIn. apply in_app_or in HIn as [HIn | [HIn | HIn]].
    - destruct HSTR as [_ Hnz]. exact (Hnz HIn).
    - exact (hsb6_space_nz HIn).
    - destruct HSsrc1 as [_ Hnz]. exact (Hnz HIn). }
  assert (HDSTfin : astr_atR (rdW Wc mem2) wp (join_sp (firstn (S n) (i_toks x)))).
  { split; [| exact HDnz]. rewrite <- HListEq. apply (abytes_atR_view SEGS). exact HDSTab. }
  (* ST_L2C n at the strcat return (0x8b798) *)
  apply (HL2C fpos lyc Sc Wc mem2 md3 regs2 k O1 Rest b0 b1 wp Hn HCX FXR).
  + split; [exact HJ2|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact HBB|].
    split; [|split; [|exact HBA]].
    * apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFRM].
      intros bb Hbb. apply KEEPX; lia.
    * apply (hs3_aval_on (rdW Wc memc)); [|exact HFLG].
      intros bb Hbb. change (Z.of_nat 8) with 8 in Hbb.
      pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc wp wsz 0 fpos HARc Hinw HFin) as Hd.
      rewrite EFA in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd.
      apply KEEPX; lia.
  + apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc mem2) _ _ HREP);
      [ exact KEEPrec | intros pq Hpq; exact (proj1 (hs_rec_own B _ _ _ _ _ HREP pq Hpq)) ].
  + split; [|split].
    * apply (hs3_aval_on (rdW Wc memc)); [|exact SP8]. intros bb Hbb. change (Z.of_nat 8) with 8 in Hbb. fold sp0 in Hbb.
      apply KEEPX; lia.
    * apply (hs3_aval_on (rdW Wc memc)); [|exact SP16]. intros bb Hbb. change (Z.of_nat 8) with 8 in Hbb. fold sp0 in Hbb.
      apply KEEPX; lia.
    * apply (hs3_aval_on (rdW Wc memc)); [|exact SP24]. intros bb Hbb. change (Z.of_nat 8) with 8 in Hbb. fold sp0 in Hbb.
      apply KEEPX; lia.
  + exact HDSTfin.
  + exact Hw4.
  + refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))) (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    * rewrite (hsb6_cs_val _ _ 2%bv HP2 ltac:(hsb6_acs)), Q2, (EE 2%nat 2%bv eq_refl). exact R2.
    * rewrite (hsb6_cs_val _ _ 9%bv HP2 ltac:(hsb6_acs)), Q9, (EE 9%nat 9%bv eq_refl). exact R9.
    * rewrite (hsb6_cs_val _ _ 8%bv HP2 ltac:(hsb6_acs)), Q8, (EE 8%nat 8%bv eq_refl). exact R8.
    * rewrite (hsb6_cs_val _ _ 3%bv HP2 ltac:(hsb6_acs)), Q3, (EE 3%nat 3%bv eq_refl). exact R3.
    * rewrite (hsb6_cs_val _ _ 4%bv HP2 ltac:(hsb6_acs)), Q4, (EE 4%nat 4%bv eq_refl). exact R4.
    * rewrite (hsb6_cs_val _ _ 24%bv HP2 ltac:(hsb6_acs)), Q24, (EE 24%nat 24%bv eq_refl). exact R24.
    * rewrite (hsb6_cs_val _ _ 25%bv HP2 ltac:(hsb6_acs)), Q25, (EE 25%nat 25%bv eq_refl). exact R25.
    * rewrite (hsb6_cs_val _ _ 26%bv HP2 ltac:(hsb6_acs)), Q26, (EE 26%nat 26%bv eq_refl). exact R26.
    * rewrite (hsb6_cs_val _ _ 22%bv HP2 ltac:(hsb6_acs)), Q22, (EE 22%nat 22%bv eq_refl). exact R22.
    * rewrite (hsb6_cs_val _ _ 23%bv HP2 ltac:(hsb6_acs)), Q23, (EE 23%nat 23%bv eq_refl). exact R23.
    * rewrite (hsb6_cs_val _ _ 27%bv HP2 ltac:(hsb6_acs)), Q27, (EE 27%nat 27%bv eq_refl). exact R27.
    * rewrite (hsb6_cs_val _ _ 21%bv HP2 ltac:(hsb6_acs)), Q21, (EE 21%nat 21%bv eq_refl). exact R21.
    * rewrite (hsb6_cs_val _ _ 18%bv HP2 ltac:(hsb6_acs)), Q18, (EE 18%nat 18%bv eq_refl). exact R18.
    * rewrite (hsb6_cs_val _ _ 20%bv HP2 ltac:(hsb6_acs)), Q20, (EE 20%nat 20%bv eq_refl). exact R20.
Qed.

(* ---- L2C n: from the strcat return (0x8b798) to the next strlen return (0x8b744) or to the arg_s return (0x8b804) ---- *)
Lemma hs_seg_l2c : forall x n, ((S n < length (i_toks x))%nat -> ST_L2S B MT x (S n)) ->
(S n = length (i_toks x) -> ST_AS2 B MT x) -> ST_L2C B MT x n.
Proof.
intros x n HNEXT HLAST. unfold ST_L2C.
intros fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 wp Hn HCX FXR HMID HREP HSPILL HSTR Hw4 HR1.
pose proof (hh_strlen B MT HH fx) as hstrlen. pose proof (hh_arg_s B MT HH fx) as harg_s.
pose proof (hh_heap_tail B MT HH) as hheap_tail.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10 & H11 & H12 & Hnt & HLINE & Hp0 & Hp8 & HARR & Hlen
  & HPTR & HTOKS & HWL & HREP0 & HFR8 & HEV & HLIVE & HMOK & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJ & Hk & MLE & HBB & HFRM & HFLG & HBA).
pose proof HBA as (HP & HRst & HRst2 & HRO1 & HO1 & HNw & HO1R).
pose proof HR1 as ((R2 & R9 & R8 & R3 & R4 & R24 & R25 & R26) & R22 & R23 & R27 & R21 & R18 & R20).
pose proof HSPILL as (SP8 & SP16 & SP24).
pose proof (proj1 HJ) as HARc.
pose proof hs3_stk as FS.
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (S1a & S1b & S1c).
destruct (hs3_frame_facts B MT x fpos lyc Sc Wc memc mdc k HCX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
pose proof (hs_slot_bounds (i_R x)) as (Hc1 & Hc2 & Hc8 & _).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HLM : LMAX = 8192) by reflexivity.
set (sp0 := spZ (i_regs x)) in *.
set (sp1 := hs_sp1 sp0) in *.
assert (Hsp16 : sp1 mod 16 = 0).
{ unfold sp1, hs_sp1. replace (32 * ((sp0 - 160) / 32)) with ((2 * ((sp0 - 160) / 32)) * 16) by ring.
  apply Z.mod_mul. lia. }
(* the word list's block *)
set (wsz := LIVE_XMALLOC (hs_wsz x)) in *.
assert (Hwsz : wsz = hs_words_len (i_toks x) + 1).
{ unfold wsz, LIVE_XMALLOC, hs_wsz. pose proof (hs3_wl_nonneg (i_toks x)). lia. }
assert (Hinw : In (wp, wsz) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym HP)). cbn [app]. right; right; left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc wp wsz HARc Hinw) as (Hw16 & Hw4096 & Hwc & Hwapp & Hwpres & _ & Hwn).
pose proof (req_size_pos wsz ltac:(lia)) as [_ Hreq].
assert (Hne1 : firstn (S n) (i_toks x) <> []) by (apply hsb6_firstn_ne; lia).
pose proof (hsb6_join_len _ Hne1) as HJL.
pose proof (hsb6_wl_firstn (i_toks x) (S n)) as HWF.
(* the seed: every register its own atom, the spill words c (atom 32) and F (atom 33) at s1 + 8 .. s1 + 32 *)
pose proof (hsb6_seedC Wc memc regs1 sp1 (Z.of_nat (length (i_toks x))) (Z.of_nat n) (rec_slot (i_R x)) (hs_F x fpos)
  ltac:(lia) Hsp16 R2 R9 R18 R27 ltac:(lia) ltac:(lia)
  ltac:(unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia) ltac:(lia) SP8 SP16 SP24) as HS.
set (E := Eimg (Ereg regs1 (hsb6_xC (rec_slot (i_R x)) (hs_F x fpos)))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r)
  by (intros nn r Hnn; unfold E; apply hsb6_EE; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 (rec_slot (i_R x)))
  by exact (hsb6_EX regs1 (hsb6_xC (rec_slot (i_R x)) (hs_F x fpos)) 0 ltac:(unfold A_TEXT; lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (hs_F x fpos))
  by exact (hsb6_EX regs1 (hsb6_xC (rec_slot (i_R x)) (hs_F x fpos)) 1 ltac:(unfold A_TEXT; lia)).
clearbody E.
assert (SHOK : sh_ok SEGS hsb6_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold hs_at.
(* 0x8b798 .. 0x8b79c: s11 := n + 1, s7 := 8n + 8; the run stops at the back edge 0x8b7a0 `bne s2,s11` *)
paj_run_tok RUN HS HJ SHOK hsb6_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?bb0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp bb0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr1. rename ms into ms1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md1 := m) in *; clearbody md1 end.
psrr_branch_tok RUN BR HS SHOK hsb6_Bspan.
- (* taken (s11 = n + 1 <> ntok): 0x8b738 `beqz s11` (not taken: n + 1 >= 1, decided from the seed's fact on s11),
     a0 := w, the strlen wrapper (0x8b740), back at 0x8b744 *)
  assert (Hlt : (S n < length (i_toks x))%nat).
  { lazymatch type of Hc with context [sv_denot ?Env (SOff 18 0)] =>
      rewrite branch_ne_U in Hc; apply negb_true_iff in Hc; apply Z.eqb_neq in Hc;
      rewrite (hsb6_U_off Env 18 0 (Z.of_nat (length (i_toks x)))) in Hc
        by (first [rewrite ?ew_ewset_other by lia; rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity | lia]);
      rewrite (hsb6_U_off Env 27 1 (Z.of_nat n)) in Hc
        by (first [rewrite ?ew_ewset_other by lia; rewrite (EE 27%nat 27%bv eq_refl), R27; reflexivity | lia])
    end. lia. }
  paj_run_tok RUN HS HJ SHOK hsb6_Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?bb0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp bb0 bc fr lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr2. rename ms into ms2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in *; clearbody md2 end.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
  { intros a Ha. rewrite (hsb6_run_keeps_all _ _ _ _ _ HFr2) by (first [exact Ha | hsb6_ro_regions]).
    apply (hsb6_run_keeps_all _ _ _ _ _ HFr1); [hsb6_ro_regions | exact Ha]. }
  assert (QSP : spZ (ms_regs ms2) = sp0 + (sp1 - sp0)).
  { unfold spZ at 1. rewrite Q2, (EE 2%nat 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (QRA : YK0s.ret_ok (getr (ms_regs ms2) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Q3' : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite Q3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
  assert (Q4' : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite Q4, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
  assert (Q10' : getr (ms_regs ms2) 10 = w64 wp) by (rewrite Q10, (EE 22%nat 22%bv eq_refl), R22; reflexivity).
  (* the strlen wrapper on the word list, back at 0x8b744 *)
  eapply SRr_bind.
  { eapply (hsb6_art_wr ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_strlen) Wc (ms_regs ms2) (ms_mem ms2)
      SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc md2 k
      (sp1 - sp0) (Z_to_bv 64 (BASE + HS_L2S)) _ HJ QSP ltac:(lia) ltac:(lia) ltac:(lia) Q1
      (fun a (H : False) => False_ind _ H)).
    apply (hstrlen lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 wp (join_sp (firstn (S n) (i_toks x)))).
    - exact (ecall_pre_stk_at SEGS B ESTACK SUP_HOST_SETTING_STK sp0 (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x)
        (i_md x) [(0, fpos)] lyc Sc Wc (ms_mem ms2) md2 k (ms_regs ms2) (sp1 - sp0) HJ QSP S1b ltac:(lia) ltac:(lia)
        ltac:(lia) QRA Q3' Q4').
    - exact Q10'.
    - lia.
    - apply (astr_atR_view SEGS). apply (hsb6_astr_kept _ _ _ _ HSTR). intros i Hi. apply KEEP2. lia.
    - unfold astr_len. apply (aread_ok_of_block SEGS B LAWS ESTACK lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 wp wsz);
        [exact (proj1 HJ) | exact Hinw | lia | lia | lia | rewrite QSP; lia].
    - unfold astr_len. apply (hheap_tail lyc Sc Wc (ms_mem ms2) md2 wp wsz); [exact (proj1 HJ) | exact Hinw | lia].
    - exact (hsb6_rom_view Wc (ms_mem ms2) (proj1 (hs3_rod_now B MT HH x fpos lyc Sc Wc (ms_mem ms2) md2 k HCX HJ))). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md3 & -> & HJ2 & HP2 & HQ2 & HK2).
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1) -> rdW Wc mem2 a = rdW Wc memc a).
  { intros a Ha Hs. rewrite (HK2 a Ha ltac:(lia) ltac:(tauto)). apply KEEP2. exact Ha. }
  apply (HNEXT Hlt fpos lyc Sc Wc mem2 md3 regs2 k O1 Rest b0 b1 wp).
  + lia.
  + exact HCX.
  + exact FXR.
  + split; [exact HJ2|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact HBB|].
    split; [|split; [|exact HBA]].
    * apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFRM]. intros bb Hbb. apply KEEP3; lia.
    * apply (hs3_aval_on (rdW Wc memc)); [|exact HFLG]. intros bb Hbb. change (Z.of_nat 8) with 8 in Hbb. apply KEEP3; lia.
  + apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc mem2) _ _ HREP).
    * intros a Ha. pose proof (hsb6_rec_low lyc Sc Wc memc mdc _ _ a HARc HREP Ha). apply KEEP3; lia.
    * intros pn Hpn. exact (proj1 (hs_rec_own B _ _ _ _ _ HREP pn Hpn)).
  + split; [|split].
    * apply (hs3_aval_on (rdW Wc memc)); [|exact SP8]. intros bb Hbb. change (Z.of_nat 8) with 8 in Hbb. fold sp0 in Hbb.
      apply KEEP3; lia.
    * apply (hs3_aval_on (rdW Wc memc)); [|exact SP16]. intros bb Hbb. change (Z.of_nat 8) with 8 in Hbb. fold sp0 in Hbb.
      apply KEEP3; lia.
    * apply (hs3_aval_on (rdW Wc memc)); [|exact SP24]. intros bb Hbb. change (Z.of_nat 8) with 8 in Hbb. fold sp0 in Hbb.
      apply KEEP3; lia.
  + apply (hsb6_astr_kept _ _ _ _ HSTR). intros i Hi. apply KEEP3; lia.
  + exact Hw4.
  + refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))) (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    * rewrite (hsb6_cs_val _ _ 2%bv HP2 ltac:(hsb6_acs)), Q2, (EE 2%nat 2%bv eq_refl). exact R2.
    * rewrite (hsb6_cs_val _ _ 9%bv HP2 ltac:(hsb6_acs)), Q9, (EE 9%nat 9%bv eq_refl). exact R9.
    * rewrite (hsb6_cs_val _ _ 8%bv HP2 ltac:(hsb6_acs)), Q8, (EE 8%nat 8%bv eq_refl). exact R8.
    * rewrite (hsb6_cs_val _ _ 3%bv HP2 ltac:(hsb6_acs)), Q3, (EE 3%nat 3%bv eq_refl). exact R3.
    * rewrite (hsb6_cs_val _ _ 4%bv HP2 ltac:(hsb6_acs)), Q4, (EE 4%nat 4%bv eq_refl). exact R4.
    * rewrite (hsb6_cs_val _ _ 24%bv HP2 ltac:(hsb6_acs)), Q24, (EE 24%nat 24%bv eq_refl). exact R24.
    * rewrite (hsb6_cs_val _ _ 25%bv HP2 ltac:(hsb6_acs)), Q25, (EE 25%nat 25%bv eq_refl). exact R25.
    * rewrite (hsb6_cs_val _ _ 26%bv HP2 ltac:(hsb6_acs)), Q26, (EE 26%nat 26%bv eq_refl). exact R26.
    * rewrite (hsb6_cs_val _ _ 22%bv HP2 ltac:(hsb6_acs)), Q22, (EE 22%nat 22%bv eq_refl). exact R22.
    * rewrite (hsb6_cs_val _ _ 23%bv HP2 ltac:(hsb6_acs)), Q23, (EE 23%nat 23%bv eq_refl), R23.
      unfold w64. rewrite hsb6_bv_add. f_equal. lia.
    * rewrite (hsb6_cs_val _ _ 27%bv HP2 ltac:(hsb6_acs)), Q27, (EE 27%nat 27%bv eq_refl), R27.
      unfold w64. rewrite hsb6_bv_add. f_equal. lia.
    * rewrite (hsb6_cs_val _ _ 21%bv HP2 ltac:(hsb6_acs)), Q21, (EE 21%nat 21%bv eq_refl). exact R21.
    * rewrite (hsb6_cs_val _ _ 18%bv HP2 ltac:(hsb6_acs)), Q18, (EE 18%nat 18%bv eq_refl). exact R18.
    * rewrite (hsb6_cs_val _ _ 20%bv HP2 ltac:(hsb6_acs)), Q20, (EE 20%nat 20%bv eq_refl). exact R20.
  + exact HQ2.
- (* not taken (s11 = n + 1 = ntok): 0x8b7a4 `j 0x8b7c8`, s3 := F, s4 := F, s11 := c reloaded from the realigned
     stack (0x8b7c8 .. 0x8b7d0), `j 0x8b7f8`, a0 := c, a1 := w, the call of arg_s (0x8b800), back at 0x8b804 *)
  assert (Heq : S n = length (i_toks x)).
  { lazymatch type of Hc with context [sv_denot ?Env (SOff 18 0)] =>
      rewrite branch_ne_U in Hc; apply negb_false_iff in Hc; apply Z.eqb_eq in Hc;
      rewrite (hsb6_U_off Env 18 0 (Z.of_nat (length (i_toks x)))) in Hc
        by (first [rewrite ?ew_ewset_other by lia; rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity | lia]);
      rewrite (hsb6_U_off Env 27 1 (Z.of_nat n)) in Hc
        by (first [rewrite ?ew_ewset_other by lia; rewrite (EE 27%nat 27%bv eq_refl), R27; reflexivity | lia])
    end. lia. }
  assert (Hfs : firstn (S n) (i_toks x) = i_toks x) by (apply firstn_all2; lia).
  rewrite Hfs in HSTR, HJL, HWF.
  paj_run_tok RUN HS HJ SHOK hsb6_Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?bb0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp bb0 bc fr lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr2. rename ms into ms2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in *; clearbody md2 end.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
  { intros a Ha. rewrite (hsb6_run_keeps_all _ _ _ _ _ HFr2) by (first [exact Ha | hsb6_ro_regions]).
    apply (hsb6_run_keeps_all _ _ _ _ _ HFr1); [hsb6_ro_regions | exact Ha]. }
  assert (QSP : spZ (ms_regs ms2) = sp0 + (sp1 - sp0)).
  { unfold spZ at 1. rewrite Q2, (EE 2%nat 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (QSP1 : spZ (ms_regs ms2) = sp1) by (rewrite QSP; lia).
  assert (Q8' : getr (ms_regs ms2) 8 = w64 sp0) by (rewrite Q8, (EE 8%nat 8%bv eq_refl); exact R8).
  assert (Q10' : getr (ms_regs ms2) 10 = w64 (rec_slot (i_R x))) by (rewrite Q10, E32; reflexivity).
  assert (Q11' : getr (ms_regs ms2) 11 = w64 wp) by (rewrite Q11, (EE 22%nat 22%bv eq_refl), R22; reflexivity).
  assert (SIGAS : SIG CS_arg_s = BASE + AF_arg_s).
  { rewrite (hh_sigp B MT HH CS_arg_s ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right])));
    try (f_equal; vm_compute; reflexivity). }
  rewrite SIGAS.
  (* arg_s's premises at the call *)
  assert (HPSB : as_prog_static B = recb_PG) by (rewrite (ts_prog B (hh_HB B MT HH)); reflexivity).
  assert (HASS2 : ARG_S_STK = 16464) by (vm_compute; reflexivity).
  destruct (hs3_rod_now B MT HH x fpos lyc Sc Wc (ms_mem ms2) md2 k HCX HJ) as [HRODc HROc].
  assert (HFRc : hs_frame (rdW Wc (ms_mem ms2)) (spZ (i_regs x)) (i_regs x)).
  { apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFRM]. intros bb Hbb. apply KEEP2. lia. }
  destruct (hs3_achain B MT x fpos lyc Sc Wc (ms_mem ms2) md2 k (ms_regs ms2) HCX HJ HFRc QSP1 Q8') as (ch1 & HCH).
  assert (REPc : rec_repA B lyc Sc (rdW Wc (ms_mem ms2)) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x))
    ((b1, hs_b1 x) :: (b0, hs_b0 x) :: O1)).
  { apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc (ms_mem ms2)) _ _ HREP).
    - intros a Ha. pose proof (hsb6_rec_low lyc Sc Wc memc mdc _ _ a HARc HREP Ha). apply KEEP2. lia.
    - intros pn Hpn. exact (proj1 (hs_rec_own B _ _ _ _ _ HREP pn Hpn)). }
  assert (HSTR2 : astr_atR (rdW Wc (ms_mem ms2)) wp (join_sp (i_toks x))).
  { apply (hsb6_astr_kept _ _ _ _ HSTR). intros i Hi. apply KEEP2. lia. }
  assert (HARGA : astr_argA B lyc Sc (rdW Wc (ms_mem ms2)) (in_roP SEGS RLO RHI) [] wp (Some (join_sp (i_toks x)))).
  { cbn [astr_argA]. split; [lia|]. split; [exact HSTR2|]. split; [lia|].
    left. split; [exists wp, wsz; split; [exact Hinw | lia] | constructor]. }
  assert (HTAILS : forall y, Some (join_sp (i_toks x)) = Some y -> atail_vis SEGS Wc (ms_mem ms2) (wp + Z.of_nat (length y))).
  { intros y Hy. injection Hy as <-.
    exact (hheap_tail lyc Sc Wc (ms_mem ms2) md2 wp wsz (wp + Z.of_nat (length (join_sp (i_toks x)))) (proj1 HJ) Hinw
      ltac:(lia)). }
  assert (HEVc : st_nev Sc + EV_ARG_S <= EV_MAX).
  { pose proof HJ as (_ & _ & _ & _ & _ & _ & HnevJ & _).
    unfold EV_SUP_HOST_SETTING, hs_k3, hs_k2, hs_k1, hs_k0 in *. unfold EV_ARG_S, EV_XMALLOC in *. lia. }
  assert (HLIVEc : blocks_bytes Sc + LIVE_ARG_S (Some (join_sp (i_toks x))) <= LIVE_MAX).
  { unfold LIVE_SUP_HOST_SETTING, hs_l3, hs_l2, hs_l1, hs_wsz in *. lia. }
  assert (HMOc : mo_ok MT Sc (XM_ARG_S MT (Some (join_sp (i_toks x))))).
  { pose proof (hh_MTL B MT HH) as ML.
    apply (mok_station MT (i_S x) Sc (XM_SUP_HOST_SETTING MT (i_R x) (i_line x) (i_toks x)) (hs_m3 MT x) _ ML HMOK MLE).
    - exact (hs3_xs_nonneg B MT HH (Some (join_sp (i_toks x)))).
    - unfold XM_SUP_HOST_SETTING, hs_m3, hs_m2, hs_m1, hs_m0, hs_wsz. pose proof (mo_free_nonneg MT ML). lia. }
  (* arg_s writes c->nargs and c->args[2] *)
  pose (FP1 := if Z.of_nat (length (hs_A2 x)) <? REC_ARGS_MAX
    then [(rec_slot (i_R x) + CALL_OFF_NARGS, rec_slot (i_R x) + CALL_OFF_NARGS + 4);
          (rec_slot (i_R x) + CALL_OFF_ARGS + 8 * Z.of_nat (length (hs_A2 x)),
           rec_slot (i_R x) + CALL_OFF_ARGS + 8 * Z.of_nat (length (hs_A2 x)) + 8)]
    else []).
  assert (HFP1 : forall a, inFP FP1 a -> rec_slot (i_R x) <= a < rec_slot (i_R x) + CALL_SIZE).
  { intros a (r & Hr & Ha). unfold FP1 in Hr. cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha;
    unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia. }
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS Wc (ms_regs ms2) (ms_mem ms2) (Z_to_bv 64 (BASE + AF_arg_s)) SUP_HOST_SETTING_STK
      sp0 (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc _ k
      ARG_S_STK FP1 EV_ARG_S (sp1 - sp0) (getr (ms_regs ms2) 1) ch1 _ HJ QSP S1b ltac:(lia) ltac:(rewrite HASS2; lia)
      ltac:(rewrite HASS2, FS; lia)).
    - rewrite Q3, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
    - rewrite Q4, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Q1, unsigned_lit_small by lia. lia.
    - replace (sp0 + (sp1 - sp0)) with (spZ (ms_regs ms2)) by lia. exact HCH.
    - intros HPRE1.
      exact (harg_s lyc Sc Wc (ms_regs ms2) (ms_mem ms2) _ ch1 (rec_slot (i_R x)) wp REC_HOST_SETTING (hs_A2 x)
        (Some (join_sp (i_toks x))) (i_R x) ((b1, hs_b1 x) :: (b0, hs_b0 x) :: O1)
        HPRE1 HRODc HROc Q10' Q11' eq_refl REPc (or_introl HARGA) HTAILS HEVc HLIVEc HMOc).
    - intros a Ha. right; right; right; right; left.
      destruct (hs3_rec_fp (i_O x) a (hs3_slot_rec (i_R x) a (HFP1 a Ha))) as [Hfp Hpg].
      split; [exact Hfp|]. split; [rewrite HPSB; exact Hpg | exact (hh_prog_img B MT HH a Hpg)].
    - intros ly2 S2 W2 regs2 mem2 md3 _ a Ha Hw _. exfalso. pose proof (HFP1 a Ha).
      rewrite FS in Hw. unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
  (* back at 0x8b804 *)
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md3 & -> & HJ2 & HJ2c & HP2 & HK2).
  cbv zeta in HK2.
  destruct HK2 as (HBB2 & HMLE2 & [(Hm6 & _) | (_ & p & Hp4096 & HPERM2 & HAPART & HREP2)]);
    [cbn in Hm6; unfold REC_ARGS_MAX in Hm6; lia|].
  pose proof HJ2c as (HAR2 & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
  rewrite Q1.
  apply (HLAST Heq fpos ly2 S2 W2 mem2 md3 regs2 (k + EV_ARG_S) O1 Rest b0 b1 wp p HCX FXR).
  + refine (conj HJ2 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    * unfold hs_k4. unfold EV_ARG_S, EV_XMALLOC. lia.
    * exact (mle_station MT _ _ _ _ _ (hh_MTL B MT HH) MLE HMLE2).
    * unfold hs_l4. lia.
    * apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFRM].
      intros bb Hbb. rewrite <- (KEEP2 bb ltac:(lia)). apply J1; [lia | rewrite HASS2; lia |].
      intros Hin. apply HFP1 in Hin. unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
    * apply (hs3_aval_on (rdW Wc memc)); [|exact HFLG].
      intros bb Hbb. change (Z.of_nat 8) with 8 in Hbb. rewrite <- (KEEP2 bb ltac:(lia)). apply (J4 0 fpos bb HFin).
      -- left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 0) with 64. lia.
      -- intros Hin. apply HFP1 in Hin.
         apply (frm_img SEGS B LAWS lyc Sc Wc (ms_mem ms2) md2 0 fpos bb (proj1 HJ) HFin);
           [rewrite EFA; change (fs_frame_bytes 0) with 64; lia|].
         destruct (hs3_rec_fp (i_O x) bb (hs3_slot_rec (i_R x) bb Hin)) as [_ Hpg]. exact (hh_prog_img B MT HH bb Hpg).
    * split; [|split; [exact HRst|split; [exact HRst2|split; [exact HRO1|split; [exact HO1|split; [|exact HO1R]]]]]].
      -- eapply Permutation_trans; [exact HPERM2|]. eapply Permutation_trans; [apply perm_skip; exact HP|].
         exact (Permutation_middle [(b0, hs_b0 x); (b1, hs_b1 x); (wp, wsz)] Rest (p, hs_b3 x)).
      -- intros pn Hpn Hin0. destruct Hpn as [<- | [<- | [<- | [<- | []]]]].
         ++ apply HNw; [left; reflexivity | exact Hin0].
         ++ apply HNw; [right; left; reflexivity | exact Hin0].
         ++ apply HNw; [right; right; left; reflexivity | exact Hin0].
         ++ destruct (in_dec hs3_pair_dec (p, hs_b3 x) (i_O x)) as [HinO | HnO]; [exact HinO|].
            exfalso. pose proof (HRst2 _ Hin0 HnO) as HinR.
            assert (HinC : In (p, hs_b3 x) (ablocks B lyc Sc))
              by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact HinR).
            rewrite Forall_forall in HAPART. pose proof (HAPART _ HinC) as Hd. cbn [fst snd] in Hd.
            unfold iv_apart, hs_b3 in Hd. lia.
  + exact HREP2.
  + exact Hw4.
  + refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))) (conj _ (conj _ _))).
    * rewrite (hsb6_cs_val _ _ 2%bv HP2 ltac:(hsb6_acs)), Q2, (EE 2%nat 2%bv eq_refl). exact R2.
    * rewrite (hsb6_cs_val _ _ 9%bv HP2 ltac:(hsb6_acs)), Q9, (EE 9%nat 9%bv eq_refl). exact R9.
    * rewrite (hsb6_cs_val _ _ 8%bv HP2 ltac:(hsb6_acs)), Q8, (EE 8%nat 8%bv eq_refl). exact R8.
    * rewrite (hsb6_cs_val _ _ 3%bv HP2 ltac:(hsb6_acs)), Q3, (EE 3%nat 3%bv eq_refl). exact R3.
    * rewrite (hsb6_cs_val _ _ 4%bv HP2 ltac:(hsb6_acs)), Q4, (EE 4%nat 4%bv eq_refl). exact R4.
    * rewrite (hsb6_cs_val _ _ 24%bv HP2 ltac:(hsb6_acs)), Q24, (EE 24%nat 24%bv eq_refl). exact R24.
    * rewrite (hsb6_cs_val _ _ 25%bv HP2 ltac:(hsb6_acs)), Q25, (EE 25%nat 25%bv eq_refl). exact R25.
    * rewrite (hsb6_cs_val _ _ 26%bv HP2 ltac:(hsb6_acs)), Q26, (EE 26%nat 26%bv eq_refl). exact R26.
    * rewrite (hsb6_cs_val _ _ 19%bv HP2 ltac:(hsb6_acs)), Q19, E33. reflexivity.
    * rewrite (hsb6_cs_val _ _ 20%bv HP2 ltac:(hsb6_acs)), Q20, E33. reflexivity.
    * rewrite (hsb6_cs_val _ _ 27%bv HP2 ltac:(hsb6_acs)), Q27, E32. reflexivity.
  + rewrite (hsb6_cs_val _ _ 22%bv HP2 ltac:(hsb6_acs)), Q22, (EE 22%nat 22%bv eq_refl). exact R22.
Qed.

End e.
End f.
End d.
