(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL piece A2 (the key path): the straight runs of the
   piece over B_prog_tbl between its calls (ExvB_Loop_A2_ss.v's symbolic states), each seated from EXBs and the
   piece's state facts, and the exits to the cuts LR (ExvB_Loop_Stmt.v CUT_LR) and CX (ExvB_Stmt.v CUT_CX).
   Old-pin kit 4f18c75d4900 rebind: every run is ExvB_Loop_exw.v's SRr_run_to_tok_AJx_inv at P := exvl_P (e_mem E)
   (EXB's exv_rm keep), so a run's post a2_runpost carries the keep at its end memory, for KIT_RUNs.
   Rule 24: proves no function (kind: segment lemma).
   Numerals: 8, 16, 24, 32, 40, 56 (LENGTH: struct ex / node fields), 72, 80, 120, 128, 136, 144, 152 (LENGTH: B's
   spill slots, ExvB_Stmt.v CUT_CL), 34, 58, 123 (WORD: ASCII the code compares), 2, 9, 10, 18, 19, 20, 21, 22, 23,
   24, 25, 27, 32 .. 37 (WORD / DERIVED: register numbers and the symbolic atoms of ExvB_Loop_A2_ss.v), 4096, 2 ^ 46,
   2 ^ 47, 2 ^ 63, 2 ^ 64 (LENGTH: address-space bounds). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW YGcallMx YC88 YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_exw ExvB_Loop_kit ExvB_Loop_Stmt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Open_sh ExvB_Open_kt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_A2_ss ExvB_Loop_A2_call.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_kitL.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- pure ---- *)
Lemma a2_skip_suffix : forall l, exists k, PjGrammar.skip l = skipn k l.
Proof.
induction l as [|b l IH]; [exists 0%nat; reflexivity|]. cbn [PjGrammar.skip].
destruct (PjGrammar.ws b); [destruct IH as (k & Hk); exists (S k); exact Hk | exists 0%nat; reflexivity].
Qed.
Lemma a2_skipn_skipn : forall (l : list Z) a b, skipn a (skipn b l) = skipn (a + b) l.
Proof. intros l a b. rewrite skipn_skipn. reflexivity. Qed.
(* a suffix of a suffix of x, and its position *)
Lemma a2_skip_pos : forall (PSUF : PURE_SUFFIX) (x r : list Z) kr, r = skipn kr x ->
  skipn (length x - length (PjGrammar.skip r)) x = PjGrammar.skip r.
Proof.
intros PSUF x r kr Hr. destruct (a2_skip_suffix r) as (k & Hk). apply PSUF with (k := (k + kr)%nat).
rewrite Hk, Hr, a2_skipn_skipn. reflexivity.
Qed.
Lemma a2_skip_len : forall l, (length (PjGrammar.skip l) <= length l)%nat.
Proof. intros l. destruct (a2_skip_suffix l) as (k & ->). rewrite length_skipn. lia. Qed.
Lemma a2_nth_skipn : forall (l : list Z) k b rest, skipn k l = b :: rest -> nth k l 0 = b.
Proof.
induction l as [|x l IH]; intros [|k] b rest H; cbn in H; try discriminate.
- injection H as -> ->. reflexivity.
- cbn. exact (IH k b rest H).
Qed.
Lemma a2_skipn_S : forall (l : list Z) k b rest, skipn k l = b :: rest -> skipn (S k) l = rest.
Proof. induction l as [|x l IH]; intros [|k] b rest H; cbn in H |- *; try discriminate; [injection H as -> ->; reflexivity | exact (IH k b rest H)]. Qed.

Lemma a2_utf8 : forall cp, 0 < cp -> Forall (fun c => c <> 0) (PjGrammar.utf8 cp) /\ (length (PjGrammar.utf8 cp) <= 4)%nat.
Proof.
intros cp Hcp. unfold PjGrammar.utf8.
destruct (cp <? 128) eqn:H1; [|destruct (cp <? 2048) eqn:H2; [|destruct (cp <? 65536) eqn:H3]];
  cbn [length]; (split; [repeat constructor | lia]);
  pose proof (Z.div_pos cp 64 ltac:(lia) ltac:(lia)); pose proof (Z.div_pos cp 4096 ltac:(lia) ltac:(lia));
  pose proof (Z.div_pos cp 262144 ltac:(lia) ltac:(lia));
  pose proof (Z.mod_pos_bound cp 64 ltac:(lia)); pose proof (Z.mod_pos_bound (cp / 64) 64 ltac:(lia));
  pose proof (Z.mod_pos_bound (cp / 4096) 64 ltac:(lia)); lia.
Qed.
Lemma a2_hexval : forall b v, PjGrammar.hexval b = Some v -> 0 <= v.
Proof.
intros b v H. unfold PjGrammar.hexval in H.
repeat match type of H with context [if ?c then _ else _] => destruct c eqn:?; [injection H as <-; lia|] end.
discriminate.
Qed.
Lemma a2_hex4 : forall l v, PjGrammar.hex4 l = Some v -> 0 <= v.
Proof.
intros l v H. unfold PjGrammar.hex4 in H.
destruct l as [|h0 [|h1 [|h2 [|h3 l]]]]; try discriminate.
destruct (PjGrammar.hexval h0) as [v0|] eqn:E0; [|discriminate].
destruct (PjGrammar.hexval h1) as [v1|] eqn:E1; [|discriminate].
destruct (PjGrammar.hexval h2) as [v2|] eqn:E2; [|discriminate].
destruct (PjGrammar.hexval h3) as [v3|] eqn:E3; [|discriminate].
injection H as <-. apply a2_hexval in E0, E1, E2, E3. lia.
Qed.
Lemma a2_emit : forall bs d s r, PjGrammar.emit bs d = Some (s, r) ->
  exists s', d = Some (s', r) /\ s = bs ++ s'.
Proof. intros bs [[s' r']|] s r H; cbn in H; [injection H as <- <-; exists s'; auto | discriminate]. Qed.
Lemma a2_low : forall z lo, PjGrammar.low z = Some lo -> 56320 <= lo.
Proof.
intros z lo H. unfold PjGrammar.low in H. destruct z as [|b1 [|b2 r]]; try discriminate.
destruct ((b1 =? 92) && (b2 =? 117)); [|discriminate].
destruct (PjGrammar.hex4 r) as [v|]; [|discriminate].
destruct ((56320 <=? v) && (v <=? 57343)) eqn:Hv; [|discriminate]. injection H as <-.
apply andb_prop in Hv as [Hv _]. lia.
Qed.
(* decode emits non-zero bytes, no more than it reads *)
Lemma a2_decode : forall n x s r, (length x <= n)%nat -> PjGrammar.decode x = Some (s, r) ->
  Forall (fun c => c <> 0) s /\ (length s <= length x)%nat.
Proof.
induction n as [|n IH]; intros x s r Hn H.
{ destruct x; [discriminate | cbn in Hn; lia]. }
destruct x as [|b x']; [discriminate|]. cbn [PjGrammar.decode] in H. cbn [length] in Hn |- *.
destruct (b =? 34) eqn:Hq; [injection H as <- <-; split; [apply Forall_nil | cbn; lia]|].
destruct (b <? 32) eqn:Hlt; [discriminate|].
destruct (negb (b =? 92)) eqn:Hbs.
{ apply a2_emit in H as (s' & Hd & ->). destruct (IH x' s' r ltac:(lia) Hd) as (F & L).
  split; [constructor; [lia | exact F] | cbn; lia]. }
destruct x' as [|e r2]; [discriminate|].
destruct (e =? 117) eqn:Hu.
- destruct r2 as [|h0 [|h1 [|h2 [|h3 r3]]]]; try discriminate.
  destruct (PjGrammar.hex4 (h0 :: h1 :: h2 :: h3 :: r3)) as [cp|] eqn:Hh; [|discriminate].
  pose proof (a2_hex4 _ _ Hh) as Hcp0.
  destruct (cp =? 0) eqn:Hc0; [discriminate|].
  destruct ((55296 <=? cp) && (cp <? 56320)) eqn:Hhi.
  + destruct r3 as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 r4]]]]]]; try discriminate.
    destruct (PjGrammar.low (g0 :: g1 :: g2 :: g3 :: g4 :: g5 :: r4)) as [lo|] eqn:Hlo; [|discriminate].
    apply a2_emit in H as (s' & Hd & ->). cbn [length] in Hn.
    destruct (IH r4 s' r ltac:(lia) Hd) as (F & L).
    apply a2_low in Hlo. apply andb_prop in Hhi as [Hhi _].
    destruct (a2_utf8 (PjGrammar.pair_cp cp lo) ltac:(unfold PjGrammar.pair_cp; lia)) as (F8 & L8).
    split; [apply Forall_app; split; [exact F8 | exact F]|]. rewrite length_app. cbn [length]. lia.
  + destruct ((56320 <=? cp) && (cp <? 57344)); [discriminate|].
    apply a2_emit in H as (s' & Hd & ->). cbn [length] in Hn.
    destruct (IH r3 s' r ltac:(lia) Hd) as (F & L).
    destruct (a2_utf8 cp ltac:(lia)) as (F8 & L8).
    split; [apply Forall_app; split; [exact F8 | exact F]|]. rewrite length_app. cbn [length]. lia.
- destruct (PjGrammar.escape e) as [c|] eqn:He; [|discriminate].
  apply a2_emit in H as (s' & Hd & ->). destruct (IH r2 s' r ltac:(cbn in Hn; lia) Hd) as (F & L).
  assert (Hc : c <> 0).
  { unfold PjGrammar.escape in He.
    repeat match type of He with context [if ?t then _ else _] => destruct t; [injection He as <-; lia|] end.
    discriminate. }
  split; [constructor; [exact Hc | exact F] | cbn [length app]; lia].
Qed.
Lemma a2_jr_string : forall z s r, exv_run0 (PjGrammar.jr_string z) = Some (s, r) ->
  Forall (fun c => c <> 0) s /\ (length s <= length z)%nat.
Proof.
intros z s r H. unfold exv_run0, PjGrammar.jr_string in H.
destruct (PjGrammar.scan z) as [q|]; [|discriminate].
unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take in H. cbn in H.
destruct (PjGrammar.decode z) as [[s' r']|] eqn:Hd.
- cbn in H. injection H as <- <-. exact (a2_decode (length z) z s' r' (le_n _) Hd).
- cbn in H. discriminate.
Qed.

(* ---- symbolic-value denotations ---- *)
Lemma a2_denot_shx : forall E m c v, ew E m = Z_to_bv 64 v -> ew E 25 = Z_to_bv 64 SHADOW_OFF ->
  0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> sv_denot E (a2_shx m c) = Z_to_bv 64 (shadow_addr (v + c)).
Proof.
intros E m c v Hn Hm Hv Hc Hvc. unfold a2_shx, shadow_addr.
assert (Hsb : 0 <= SHADOW_OFF < 2 ^ 32) by (unfold SHADOW_OFF; lia).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 25 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff 25 0)) = SHADOW_OFF + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm.
rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (v + c)) by (unfold M64; lia).
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite (zcanon_id SHADOW_OFF) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma a2_denot_off : forall E m c v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff m c) = Z_to_bv 64 (v + c).
Proof. intros E m c v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma a2_ew_reg : forall regs extra n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
  ew (Ereg regs extra) n = Z_to_bv 64 v.
Proof. intros regs extra n r v Hn H. rewrite (ew_Ereg_nat regs extra n r Hn). exact H. Qed.
Lemma a2_denot_sub : forall E m n a b, ew E m = Z_to_bv 64 a -> ew E n = Z_to_bv 64 b -> 0 <= b <= a -> a < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SUB (SOff m 0) (SOff n 0)) = Z_to_bv 64 (a - b).
Proof.
intros E m n a b Hm Hn Hb Ha.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_SUB (SOff m 0) (SOff n 0)))). f_equal.
change (U E (SAlu ALU_SUB (SOff m 0) (SOff n 0)) = a - b).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E m a Hm), (U_atom E n b Hn) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma a2_srl_i : forall E (i : Z), ew E 34 = Z_to_bv 64 i -> 0 <= i <= 2 ^ 47 ->
  U E (SAlu ALU_SRL (SOff 34 (2 ^ 60)) (SLit 61)) = 0.
Proof.
intros E i H Hi. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E 34 i (2 ^ 60) H) by lia. rewrite U_lit by lia.
change (Z.land 61 63) with 61. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* ---- pure helpers of the composition ---- *)
Lemma a2_pres : forall (regs regs2 : bvmap 5 word) (r : bv 5) z, aregs_preserved regs regs2 -> acallee_saved z ->
  bv_unsigned r = z -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 r z HPR Hz Hr.
assert (Hrz : r = Z_to_bv 5 z).
{ apply bv_eq. rewrite Z_to_bv_unsigned, <- Hr. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. }
rewrite Hrz. exact (HPR z Hz).
Qed.
Ltac a2_prese HPR z := match goal with |- getr _ ?r = _ =>
  exact (a2_pres _ _ r z HPR ltac:(unfold acallee_saved; lia) eq_refl) end.
Ltac a2_presr HPR z := match goal with |- getr _ ?r = _ =>
  rewrite (a2_pres _ _ r z HPR ltac:(unfold acallee_saved; lia) eq_refl) end.
Lemma a2_w64_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> w64 a = w64 b -> a = b.
Proof.
intros a b Ha Hb H. apply (f_equal bv_unsigned) in H. unfold w64 in H.
rewrite !unsigned_lit_small in H by lia. exact H.
Qed.
Lemma a2_w64_dec : forall v : word, v = w64 0 \/ v <> w64 0.
Proof.
intros v. destruct (Z.eq_dec (bv_unsigned v) 0) as [H0|H0].
- left. apply bv_eq. rewrite H0. reflexivity.
- right. intros ->. apply H0. reflexivity.
Qed.
Lemma a2_scan_lt : forall n z c, (length z <= n)%nat -> PjGrammar.scan z = Some c -> (c < length z)%nat.
Proof.
induction n as [|n IH]; intros z c Hn H.
- destruct z; [discriminate | cbn in Hn; lia].
- destruct z as [|b r]; [discriminate|]. cbn [PjGrammar.scan] in H. cbn [length] in Hn |- *.
  destruct (b =? 34); [injection H as <-; lia|].
  destruct (b =? 92).
  + destruct r as [|b2 r2]; [discriminate|].
    destruct (PjGrammar.scan r2) as [q|] eqn:Hq; cbn in H; [|discriminate].
    injection H as <-. cbn [length] in Hn |- *. pose proof (IH r2 q ltac:(lia) Hq). lia.
  + destruct (PjGrammar.scan r) as [q|] eqn:Hq; cbn in H; [|discriminate]. injection H as <-.
    pose proof (IH r q ltac:(lia) Hq). lia.
Qed.
Lemma a2_obj_tag : forall t, PjTree.tag t = 6 -> exists ms, t = PjTree.JObj ms.
Proof. intros [] H; cbn in H; try discriminate; eexists; reflexivity. Qed.
Lemma a2_same_iff : forall ms i s u, fst (nth i ms ([], PjTree.JNull)) = s ->
  (exv_same true (PjTree.JObj ms) i s u <-> exv_kidt (PjTree.JObj ms) i = u).
Proof.
intros ms i s u Hf. unfold exv_same, exv_kidt. destruct (nth i ms ([], PjTree.JNull)) as (a, b).
cbn in Hf |- *. subst a. split; [intros H; injection H as H; exact H | intros ->; reflexivity].
Qed.
Lemma a2_same_fst : forall ms i s u, exv_same true (PjTree.JObj ms) i s u -> fst (nth i ms ([], PjTree.JNull)) = s.
Proof. intros ms i s u H. unfold exv_same in H. rewrite H. reflexivity. Qed.
Lemma a2_pc_vals : A2_W1 = 539436 /\ A2_S = 539512 /\ A2_C = 539656 /\ A2_W2 = 539692.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---- the walk ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis KCALL : forall fx : YK11.FPState, KIT_CALLs (fx := fx) B ARx SK.
Hypothesis KRUN : forall fx : YK11.FPState, KIT_RUNs (fx := fx) B ARx SK.
Hypothesis KCH : forall fx : YK11.FPState, KIT_CALL_CHAIN (fx := fx) B ARx SK.
Hypothesis KROD : forall fx : YK11.FPState, KIT_RODATA (fx := fx) B ARx SK.
Hypothesis KWD : forall fx : YK11.FPState, KIT_WDEST (fx := fx) B ARx SK.
Hypothesis KOFS : forall fx : YK11.FPState, KIT_EXB_OF_S (fx := fx) B ARx SK.
Hypothesis PLS : PURE_L_STEP.
Hypothesis PSUF : PURE_SUFFIX.
(* every lemma of this section takes every section variable and hypothesis (one argument list for the next file) *)
#[local] Set Default Proof Using "All".
Local Abbreviation LAWS := (eh_laws B ARx SK HYP).
Local Abbreviation GEOM := (a2_geom (fx := fx) B ARx SK HYP KCALL KRUN KCH KROD KWD).
Local Abbreviation EXBSREG := (a2_exbs_reg (fx := fx) B ARx SK HYP KCALL KRUN KCH KROD KWD).
Local Abbreviation RUNTO_T m0 := (SRr_run_to_tok_AJx_inv (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS
  B_prog_segs_low B_prog_tbl B_prog_tbl_ok B_prog_wx (exvl_P m0) (exvl_PLAW m0)).
Local Abbreviation CALLWS := (a2_call_ws (fx := fx) B ARx SK HYP KCALL KRUN KCH KROD KWD).
Local Abbreviation CALLSTR := (a2_call_str (fx := fx) B ARx SK HYP KCALL KRUN KCH KROD KWD).
Local Abbreviation CALLCMP := (a2_call_cmp (fx := fx) B ARx SK HYP KCALL KRUN KCH KROD KWD).
Local Abbreviation NODE := (a2_node (fx := fx) B ARx SK HYP KCALL KRUN KCH KROD KWD).
Local Abbreviation KEY := (a2_key (fx := fx) B ARx SK HYP KCALL KRUN KCH KROD KWD).
Local Abbreviation SCR := (a2_scr (fx := fx) B ARx SK HYP KCALL KRUN KCH KROD KWD).
Local Abbreviation GARRK := (a2_garr8_kept (fx := fx) B ARx SK HYP KCALL KRUN KCH KROD KWD).
Ltac a2_incl := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [In] in Hr |- *; tauto.
Ltac a2_inl := cbn [In]; repeat (first [left; reflexivity | right]).

(* the static facts of the piece: CUT_LK's premises that no step changes (c = 123: the object arm) *)
Variables (n : nat) (m : Z) (E : exv_e) (i cap : nat) (acc : list (list Z * PjTree.jv)) (ip vv dlc kid fl kids : Z)
  (tk : PjTree.jv).
Hypothesis HX : CUT_CX (fx := fx) B ARx SK n.
Hypothesis HLR : CUT_LR (fx := fx) B ARx SK n m.
Hypothesis Hn : e_n E = n.
Hypothesis HP : EXV_PRE B ARx E.
Hypothesis Hi1 : exv_i1 E < exv_len E.
Hypothesis Hc : nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = 123.
Hypothesis Hdep : e_dep E + 1 <= 32.
Hypothesis Hacc : length acc = i.
Hypothesis Hip : 0 <= ip <= exv_len E.
Hypothesis Hii : Z.of_nat i <= ip.
Hypothesis Hm : exv_len E - ip <= m.
Hypothesis HV : exv_V E = exv_L (S (Z.to_nat (e_dep E))) true i cap acc (skipn (Z.to_nat ip) (e_x E)).
Hypothesis Hfl : (kid = 0 /\ fl = 1) \/
  (fl = 0 /\ vv = e_v E /\ PjTree.tag (e_t E) = 6 /\ e_v E <> 0 /\ (i < exv_count (e_t E))%nat /\
   tk = exv_kidt (e_t E) i /\ 0 <= kids < 2 ^ 64 /\ kid = kids + 56 * Z.of_nat i /\ kid <> 0).
Hypothesis Hdif : forall nm u dl', (dl' = 0 \/ dl' = 1) ->
  (dl' = 1 <-> dlc = 1 \/ (kid <> 0 /\ ~ exv_same true (e_t E) i nm u)) -> exv_dif E true vv dl' ((nm, u) :: acc).

(* the state facts every stretch starts from: EXBs, the loop registers, the spills, the cursor (in->p at x0 + p,
   in->differs dl), the kids word when there is a node *)
Definition a2_st lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos (p dl : Z) : Prop :=
  EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos /\
  getr regs 27 = w64 123 /\ getr regs 22 = w64 (shadow_addr (e_q E + 8)) /\ getr regs 23 = w64 (e_q E + 8) /\
  getr regs 20 = w64 kid /\ exv_spills E Wc memc lyc pos 123 vv i /\
  prhex_cur Wc memc (e_q E) (e_x0 E + p) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dl /\
  0 <= p <= exv_len E /\ (dl = 0 \/ dl = 1) /\
  (fl = 0 -> val_mem rsegs (mrestrict (w_H Wc) memc) (e_v E + 24) 8 kids).

(* CX from a state with EXB: the grammar refuses the item's name *)
Lemma a2_cx : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl,
  EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> getr regs 21 = w64 (-1) ->
  prhex_cur Wc memc (e_q E) (e_x0 E + p) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dl ->
  0 <= p <= exv_len E -> (dl = 0 \/ dl = 1) -> exv_name true (skipn (Z.to_nat ip) (e_x E)) = None ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_CX regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl HB H21 HCUR Hp Hdl HN.
apply (HX E lyc Sc Hpc Wc regs memc mdc k pos (-1) Hn HP HB H21).
exists p, (e_dep E + 1), dl. split; [exact HCUR|]. split; [exact Hdl|].
unfold exv_V in HV. unfold exv_V. rewrite HV, PLS, HN.
pose proof HP as HP'. unfold EXV_PRE in HP'. cbv zeta in HP'.
destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PDEP & _).
split; [reflexivity|]. split; [exact Hp | lia].
Qed.
(* what a straight run leaves: the journal and the memnorm keep (exvl_P) at the new memory, every byte outside Wq
   kept, presence grown, the registers of l unchanged *)
Definition a2_runpost lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc k pos (regs' : bvmap 5 word) mem' md'
  (l : list (bv 5)) (Wq : Z -> Prop) : Prop :=
  (ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E)
    (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc mem' md' k /\ exvl_P (e_mem E) mem') /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wq a -> aview rsegs (w_H Wc) mem' a = aview rsegs (w_H Wc) memc a) /\
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) mem' a) /\
  (forall r, In r l -> getr regs' r = getr regs r).

Lemma a2_in_bregs : forall r : bv 5, In r exv_bregs -> r <> 24%bv ->
  In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv.
Proof.
intros r Hr H24. unfold exv_bregs in Hr.
repeat (destruct Hr as [<- | Hr]; [first [exfalso; apply H24; reflexivity | cbn [In]; repeat (first [left; reflexivity | right])] |]).
destruct Hr.
Qed.

(* the state facts across a straight run that writes only the cursor cells *)
Lemma a2_runpost_st : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (regs' : bvmap 5 word) mem' md'
    (l : list (bv 5)) (Wq : Z -> Prop) p' dl',
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl ->
  a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' l Wq ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv -> In r l) ->
  (forall a, Wq a -> (e_q E <= a < e_q E + 8) \/ (e_q E + 32 <= a < e_q E + 36)) ->
  val_mem rsegs (mrestrict (w_H Wc) mem') (e_q E) 8 (e_x0 E + p') ->
  val_mem rsegs (mrestrict (w_H Wc) mem') (e_q E + 32) 4 dl' ->
  0 <= p' <= exv_len E -> (dl' = 0 \/ dl' = 1) ->
  a2_st lyc Sc Hpc Wc regs' mem' md' k pos p' dl'.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl regs' mem' md' l Wq p' dl' HST ((HJ' & HPM') & HK & HG & HR) Hincl HWq
  Vp' Vl' Hp' Hdl'.
destruct HST as (HBs & H27 & H22 & H23 & H20 & HSP & HCUR & Hpr & Hdlr & HKD).
assert (HR' : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv -> getr regs' r = getr regs r)
  by (intros r Hr; apply HR, Hincl, Hr).
destruct (EXBSREG E lyc Sc Hpc Wc regs memc mdc k pos HBs)
  as (regs0 & HB & R2 & R8 & R9 & R3 & R4 & R19 & R25 & R18 & R26 & Hrr).
pose proof (GEOM E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & _ & _ & GAR & _ & _).
pose proof asan_consts as (C1 & _).
assert (KQ : forall a, 0 <= a < 2 ^ 64 -> ~ (e_q E <= a < e_q E + 8) -> ~ (e_q E + 32 <= a < e_q E + 36) ->
  aview rsegs (w_H Wc) mem' a = aview rsegs (w_H Wc) memc a).
{ intros a Ha H1 H2. apply HK; [exact Ha|]. intros Hw. destruct (HWq a Hw); tauto. }
assert (KS : forall o v, 8 <= o <= 152 -> exv_spill E Wc memc o v -> exv_spill E Wc mem' o v).
{ intros o v Ho Hv. unfold exv_spill in *. apply (exw_val_kept rsegs (w_H Wc) memc mem'); [|exact Hv].
  intros z Hz. change (Z.of_nat 8) with 8 in Hz. apply KQ; lia. }
split.
{ apply (KRUN fx E lyc Sc Hpc Wc regs memc mdc k pos regs' mem' md' HP HBs HJ').
  - intros a Ha _ Hq1 Hq2. apply KQ; assumption.
  - exact HG.
  - exact HPM'.
  - intros r Hr H24. apply HR'. exact (a2_in_bregs r Hr H24). }
split; [rewrite HR' by (cbn [In]; repeat (first [left; reflexivity | right])); exact H27|].
split; [rewrite HR' by (cbn [In]; repeat (first [left; reflexivity | right])); exact H22|].
split; [rewrite HR' by (cbn [In]; repeat (first [left; reflexivity | right])); exact H23|].
split; [rewrite HR' by (cbn [In]; repeat (first [left; reflexivity | right])); exact H20|].
split.
{ destruct HSP as (S152 & S88 & S56 & S48 & S40 & S80 & S24 & S16 & S72 & S8 & S32 & S136 & S112 & S128 & S64 & S104 &
    S96 & S120 & S144).
  repeat split; apply KS; first [lia | assumption]. }
destruct HCUR as (Vp & Ve & Vd & Vs & Vl).
split.
{ split; [exact Vp'|]. split.
  { apply (exw_val_kept rsegs (w_H Wc) memc mem'); [|exact Ve]. intros z Hz. change (Z.of_nat 8) with 8 in Hz. apply KQ; lia. }
  split.
  { apply (exw_val_kept rsegs (w_H Wc) memc mem'); [|exact Vd]. intros z Hz. change (Z.of_nat 4) with 4 in Hz. apply KQ; lia. }
  split; [|exact Vl'].
  apply (exw_val_kept rsegs (w_H Wc) memc mem'); [|exact Vs]. intros z Hz. change (Z.of_nat 8) with 8 in Hz. apply KQ; lia. }
split; [exact Hp'|]. split; [exact Hdl'|].
intros Hfl0. apply (exw_val_kept rsegs (w_H Wc) memc mem'); [|exact (HKD Hfl0)].
intros z Hz. change (Z.of_nat 8) with 8 in Hz.
destruct Hfl as [(_ & Hf1) | (_ & _ & _ & Hv0 & _)]; [lia|].
pose proof HP as HP'. unfold EXV_PRE in HP'. cbv zeta in HP'.
destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PV & _).
destruct PV as [PV | (PT & _ & PDJ)]; [exfalso; exact (Hv0 PV)|].
destruct (PDJ z ltac:(left; lia)) as (_ & Dq & _).
assert (Hz64 : 0 <= z < 2 ^ 64).
{ pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
  destruct HB' as (_ & _ & _ & _ & _ & _ & _ & HLED & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & HTREE).
  destruct HTREE as [HT0 | (Hnd & Hhome & _)]; [exfalso; exact (Hv0 HT0)|].
  pose proof (exv_foot_rng B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
    regs0 (e_v E) (e_t E) (e_D E) GAR HLED Hnd Hhome G6 z ltac:(left; lia)). lia. }
apply KQ; [exact Hz64 | lia | lia].
Qed.
(* a register the run never wrote but the seat pinned to a value term: its value after the run is the term's *)
Lemma a2_reg_pin : forall E0 E' ss ms (r : bv 5) (H : word -> bool),
  st_ok rsegs E' ss (restrict H ms) -> env_agree 32 E0 E' -> sv_atoms_lt 32 (sr_get (ss_regs ss) r) = true ->
  getr (ms_regs ms) r = sv_denot E0 (sr_get (ss_regs ss) r).
Proof.
intros E0 E' ss ms r H HS HA Hl. rewrite (st_ok_restrict_reg rsegs H E' ss ms r HS).
apply (sv_denot_agree 32 E0 E' _ HA Hl).
Qed.

(* after a run: the registers the piece keeps are the seat's (atoms, and the pinned s6 / s7) *)
Ltac a2_kregs HS AG AG0 H22 H23 E19 E25 :=
  let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ match goal with |- getr _ ?rr = _ =>
        first
        [ exact (regs_kept_of_st_ok rsegs _ _ _ _ _ [rr] HS AG ltac:(vm_compute; reflexivity) rr (or_introl eq_refl))
        | rewrite (a2_reg_pin _ _ _ _ rr _ HS AG0 ltac:(vm_compute; reflexivity));
          lazymatch goal with |- sv_denot _ (sr_get ?l ?r0) = _ =>
            let e := eval vm_compute in (sr_get l r0) in change (sr_get l r0) with e end;
          first
          [ rewrite H22; apply a2_denot_shx; [exact E19 | exact E25 | lia | lia | lia]
          | rewrite H23; apply a2_denot_off; [exact E19 | lia]
          | cbn [sv_denot]; symmetry; assumption ] ]
      end |]);
  destruct Hr.
Ltac a2_awr U19 :=
  lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (first
    [ apply awr_ok_cons_ro; [cbn; lia|]
    | apply exw_awr_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        rewrite ?U19 in Ha; left; lia | ] ]);
  apply awr_ok_nil.

(* the seat facts a run reads from the state: registers, slot 120 / 144, the cursor's p and end, bounds *)
Lemma a2_seat : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl,
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl ->
  exists regs0, EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs0 memc mdc k pos /\
  getr regs 2 = w64 (exv_s1 E) /\ getr regs 9 = w64 (exv_s1 E) /\ getr regs 18 = w64 (frame_addr lyc 1 pos) /\
  getr regs 19 = w64 (e_q E) /\ getr regs 25 = w64 SHADOW_OFF /\
  alloc_ceiling <= exv_s1 E /\ exv_s1 E + 288 <= exv_sp E /\ exv_s1 E mod 32 = 0 /\ exv_sp E <= e_q E /\
  e_q E + 40 <= exv_sp E + e_d E /\ exv_sp E + e_d E <= 2 ^ 47 /\ e_q E mod 8 = 0 /\
  4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling /\
  4096 <= e_x0 E /\ e_x0 E + exv_len E <= alloc_ceiling /\
  (forall a, exv_sp E <= a < exv_sp E + e_d E -> apresent (w_H Wc) memc a) /\
  range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (e_q E) 40 /\
  range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (e_x0 E) (exv_len E) /\
  garr8 rsegs (mrestrict (w_H Wc) memc) (e_x0 E) (e_x E) /\
  (e_x0 E + exv_len E <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= e_x0 E).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl HST.
destruct HST as (HBs & _).
destruct (EXBSREG E lyc Sc Hpc Wc regs memc mdc k pos HBs)
  as (regs0 & HB & R2 & R8 & R9 & R3 & R4 & R19 & R25 & R18 & R26 & Hrr).
pose proof (GEOM E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & _ & _ & GAR & _ & _).
pose proof asan_consts as (C1 & _).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _ & _ &
  _ & HQRA & _).
destruct HSRC as (HBY & Hx4 & Hxce & Hxam & Hxra & _).
pose proof HJ as (_ & _ & _ & _ & _ & HFRS & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
destruct (frames_bounds_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc 1 pos GAR ltac:(rewrite HFRS; left; reflexivity))
  as (F1 & F2 & _).
change (fs_frame_bytes 1) with 128 in F2.
exists regs0. split; [exact HB|].
do 5 (split; [assumption|]).
repeat (split; [unfold exv_len; lia|]).
split; [intros a Ha; apply HPRES; lia|].
split; [exact HQRA|]. split; [exact Hxra|]. split; [exact HBY|].
pose proof asan_consts as (_ & _ & K3 & K4 & K5).
unfold amem_range in Hxam. rewrite K3, K4, K5 in Hxam. unfold SHADOW_OFF, exv_len. lia.
Qed.

(* the environment facts of a seat over Ereg regs (p :: end :: _) *)
Ltac a2_E0facts E0 regs f R2 R9 R18 R19 R25 :=
  assert (E2 : ew E0 2 = Z_to_bv 64 (exv_s1 E)) by (subst E0; exact (a2_ew_reg regs _ 2 2%bv _ eq_refl R2));
  assert (E9 : ew E0 9 = Z_to_bv 64 (exv_s1 E)) by (subst E0; exact (a2_ew_reg regs _ 9 9%bv _ eq_refl R9));
  assert (E18 : ew E0 18 = Z_to_bv 64 f) by (subst E0; exact (a2_ew_reg regs _ 18 18%bv _ eq_refl R18));
  assert (E19 : ew E0 19 = Z_to_bv 64 (e_q E)) by (subst E0; exact (a2_ew_reg regs _ 19 19%bv _ eq_refl R19));
  assert (E25 : ew E0 25 = Z_to_bv 64 SHADOW_OFF) by (subst E0; exact (a2_ew_reg regs _ 25 25%bv _ eq_refl R25));
  assert (U2 : bv_unsigned (ew E0 2) = exv_s1 E) by (rewrite E2; apply unsigned_lit_small; lia);
  assert (U9 : bv_unsigned (ew E0 9) = exv_s1 E) by (rewrite E9; apply unsigned_lit_small; lia);
  assert (U19 : bv_unsigned (ew E0 19) = e_q E) by (rewrite E19; apply unsigned_lit_small; lia);
  assert (U25 : bv_unsigned (ew E0 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia);
  assert (HBx : U E0 A2_SB = SHADOW_OFF)
    by (unfold A2_SB; rewrite (U_atom E0 25 SHADOW_OFF E25) by (unfold SHADOW_OFF; lia); reflexivity).

(* the regs, the s1 and q regions of the R2 / R5 states *)
Ltac a2_regsok H22 H23 E19 E25 :=
  unfold a2_regs; apply regs_ok_pin;
  [ apply regs_ok_pin;
    [ apply regs_ok_Ereg | intros X; discriminate X
    | rewrite H22; symmetry; apply a2_denot_shx; [exact E19 | exact E25 | lia | lia | lia] ]
  | intros X; discriminate X
  | rewrite H23; symmetry; apply a2_denot_off; [exact E19 | lia] ].
Ltac a2_reg_s1 f S120 S144 E18 E19 E25 U9 :=
  rewrite U9; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
  constructor;
  [ apply (chunk_ok_val rsegs _ _ (exv_s1 E) 120 8 (SOff 18 0) f);
      [rewrite (a2_denot_off _ 18 0 _ E18) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | zside | exact S120]
  | constructor;
    [ apply (chunk_ok_val rsegs _ _ (exv_s1 E) 144 8 (a2_shx 19 0) (shadow_addr (e_q E)));
        [rewrite (a2_denot_shx _ 19 0 _ E19 E25) by lia; rewrite Z.add_0_r; reflexivity
        | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside | exact S144]
    | constructor ] ].
Ltac a2_reg_q p Vp Ve HPRQ E32 E33 U19 :=
  rewrite U19; split; [lia|]; split; [lia|]; split;
  [ intros o Ho; apply (apresent_writable rsegs); apply HPRQ; lia |];
  constructor;
  [ apply (chunk_ok_val rsegs _ _ (e_q E) 0 8 (SOff 32 0) (e_x0 E + p));
      [rewrite (a2_denot_off _ 32 0 _ E32) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | zside |
       rewrite Z.add_0_r; exact Vp]
  | constructor;
    [ apply (chunk_ok_val rsegs _ _ (e_q E) 8 8 (SOff 33 0) (e_x0 E + exv_len E));
        [rewrite (a2_denot_off _ 33 0 _ E33) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | zside | exact Ve]
    | constructor ] ].

Ltac a2_pre HST :=
  pose proof HST as (HBs & H27 & H22 & H23 & H20 & HSP & HCUR & Hpr & Hdlr & HKD);
  lazymatch type of HST with a2_st ?lyc ?Sc ?Hpc ?Wc ?regs ?memc ?mdc ?k ?pos ?p ?dl =>
    destruct (a2_seat lyc Sc Hpc Wc regs memc mdc k pos p dl HST) as (regs0 & HB & R2 & R9 & R18 & R19 & R25 & B1 & B2 &
      B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & HPRQ & HQRA & HXRA & HBY & HXSB) end;
  pose proof asan_consts as (C1 & _);
  destruct HSP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S120 & S144);
  destruct HCUR as (Vp & Ve & _ & _ & _);
  assert (Hlen : exv_len E = Z.of_nat (length (e_x E))) by reflexivity.

(* pa: in->p at or past in->end *)
Lemma a2_seat_pa : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl pc,
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> exv_len E <= p ->
  st_ok rsegs (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) (ss_a2_pa pc)
    (restrict (w_H Wc) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))) /\
  sh_ok rsegs A2_SB a2_SH2a (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)])
    (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl pc HST Hp.
a2_pre HST.
remember (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) as E0 eqn:HE0.
a2_E0facts E0 regs (frame_addr lyc 1 pos) R2 R9 R18 R19 R25.
assert (E32 : ew E0 32 = Z_to_bv 64 (e_x0 E + p)) by (subst E0; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 (e_x0 E + exv_len E)) by (subst E0; exact (ew_Ereg_extra regs _ 1)).
assert (U32 : bv_unsigned (ew E0 32) = e_x0 E + p) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = e_x0 E + exv_len E) by (rewrite E33; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_a2_pa. apply exw_st_ok_full.
  + subst E0. a2_regsok H22 H23 E19 E25.
  + vm_compute. reflexivity.
  + unfold a2_r5_s1, a2_r5_q. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * a2_reg_s1 (frame_addr lyc 1 pos) S120 S144 E18 E19 E25 U9.
    * a2_reg_q p Vp Ve HPRQ E32 E33 U19.
  + apply pairwise_disjoint_of_extents. unfold a2_r5_s1, a2_r5_q. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [|exact I]].
    * cbn [f_atoms atoms_ok a2_r2_fp a2_fb]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U9, U19, U25, U32, U33. change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
    * cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_geu_U, (U_atom _ 32 _ E32), (U_atom _ 33 _ E33) by lia. apply negb_true_iff, Z.ltb_ge. lia.
- unfold a2_SH2a, a2_SHq. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H Wc) memc E0 A2_SB 19 (e_q E) 40 (e_q E) 0 40 HQRA HBx);
    [rewrite (U_atom E0 19 _ E19) by lia; reflexivity | lia | lia |].
  intros z Hz. unfold SHADOW_OFF. lia.
Qed.

(* pb: in->p before in->end, the byte there not c *)
Lemma a2_seat_pb : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl pc c,
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> p < exv_len E -> nth (Z.to_nat p) (e_x E) 0 <> c -> 0 <= c < 256 ->
  st_ok rsegs (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E);
      Z_to_bv 64 (nth (Z.to_nat p) (e_x E) 0)]) (ss_a2_pb pc c)
    (restrict (w_H Wc) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))) /\
  sh_ok rsegs A2_SB a2_SH2b (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E);
      Z_to_bv 64 (nth (Z.to_nat p) (e_x E) 0)]) (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl pc c HST Hp Hb Hcr.
a2_pre HST.
destruct (HBY (Z.to_nat p) ltac:(lia)) as (Vb & Hb8). rewrite Z2Nat.id in Vb by lia.
remember (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E);
  Z_to_bv 64 (nth (Z.to_nat p) (e_x E) 0)]) as E0 eqn:HE0.
a2_E0facts E0 regs (frame_addr lyc 1 pos) R2 R9 R18 R19 R25.
assert (E32 : ew E0 32 = Z_to_bv 64 (e_x0 E + p)) by (subst E0; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 (e_x0 E + exv_len E)) by (subst E0; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (nth (Z.to_nat p) (e_x E) 0)) by (subst E0; exact (ew_Ereg_extra regs _ 2)).
assert (U32 : bv_unsigned (ew E0 32) = e_x0 E + p) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = e_x0 E + exv_len E) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E0 34) = nth (Z.to_nat p) (e_x E) 0) by (rewrite E34; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_a2_pb. apply exw_st_ok_full.
  + subst E0. a2_regsok H22 H23 E19 E25.
  + vm_compute. reflexivity.
  + unfold a2_r5_s1, a2_r5_q. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * a2_reg_s1 (frame_addr lyc 1 pos) S120 S144 E18 E19 E25 U9.
    * a2_reg_q p Vp Ve HPRQ E32 E33 U19.
    * rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (e_x0 E + p) 0 1 (SOff 34 0) (nth (Z.to_nat p) (e_x E) 0));
        [rewrite (a2_denot_off _ 34 0 _ E34) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | zside |
         rewrite Z.add_0_r; exact Vb].
  + apply pairwise_disjoint_of_extents. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val a2_r5_s1 a2_r5_q]. rewrite U9, U19, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [|exact I]].
    * cbn [f_atoms atoms_ok a2_r2_fp a2_fb]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U9, U19, U25, U32, U33, U34. change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
    * cbn [f_conds conds_ok]. split; [|split; [|exact I]]; unfold acond_ok; cbn [ac_c ac_a ac_b].
      { rewrite branch_ltu_U, (U_atom _ 32 _ E32), (U_atom _ 33 _ E33) by lia. apply Z.ltb_lt. lia. }
      { rewrite branch_ne_U, (U_atom _ 34 _ E34), U_lit by lia. apply negb_true_iff, Z.eqb_neq. exact Hb. }
- unfold a2_SH2b, a2_SHq. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range rsegs (w_H Wc) memc E0 A2_SB 19 (e_q E) 40 (e_q E) 0 40 HQRA HBx);
      [rewrite (U_atom E0 19 _ E19) by lia; reflexivity | lia | lia |].
    intros z Hz. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range rsegs (w_H Wc) memc E0 A2_SB 32 (e_x0 E) (exv_len E) (e_x0 E + p) 0 1 HXRA HBx);
      [rewrite (U_atom E0 32 _ E32) by lia; reflexivity | lia | lia |].
    intros z Hz. revert HXSB. unfold SHADOW_OFF. lia.
Qed.

(* pc: in->p before in->end, the byte there c *)
Lemma a2_seat_pc : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl pc c,
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> p < exv_len E -> nth (Z.to_nat p) (e_x E) 0 = c ->
  st_ok rsegs (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) (ss_a2_pc pc c)
    (restrict (w_H Wc) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))) /\
  sh_ok rsegs A2_SB a2_SH2b (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)])
    (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl pc c HST Hp Hb.
a2_pre HST.
destruct (HBY (Z.to_nat p) ltac:(lia)) as (Vb & Hb8). rewrite Hb, Z2Nat.id in Vb by lia. rewrite Hb in Hb8.
remember (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) as E0 eqn:HE0.
a2_E0facts E0 regs (frame_addr lyc 1 pos) R2 R9 R18 R19 R25.
assert (E32 : ew E0 32 = Z_to_bv 64 (e_x0 E + p)) by (subst E0; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 (e_x0 E + exv_len E)) by (subst E0; exact (ew_Ereg_extra regs _ 1)).
assert (U32 : bv_unsigned (ew E0 32) = e_x0 E + p) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = e_x0 E + exv_len E) by (rewrite E33; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_a2_pc. apply exw_st_ok_full.
  + subst E0. a2_regsok H22 H23 E19 E25.
  + vm_compute. reflexivity.
  + unfold a2_r5_s1, a2_r5_q. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * a2_reg_s1 (frame_addr lyc 1 pos) S120 S144 E18 E19 E25 U9.
    * a2_reg_q p Vp Ve HPRQ E32 E33 U19.
    * rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (e_x0 E + p) 0 1 (SLit c) c); [reflexivity | cbn; lia | zside |
        rewrite Z.add_0_r; exact Vb].
  + apply pairwise_disjoint_of_extents. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val a2_r5_s1 a2_r5_q]. rewrite U9, U19, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [|exact I]].
    * cbn [f_atoms atoms_ok a2_r2_fp a2_fb]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U9, U19, U25, U32, U33. change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
    * cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_ltu_U, (U_atom _ 32 _ E32), (U_atom _ 33 _ E33) by lia. apply Z.ltb_lt. lia.
- unfold a2_SH2b, a2_SHq. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range rsegs (w_H Wc) memc E0 A2_SB 19 (e_q E) 40 (e_q E) 0 40 HQRA HBx);
      [rewrite (U_atom E0 19 _ E19) by lia; reflexivity | lia | lia |].
    intros z Hz. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range rsegs (w_H Wc) memc E0 A2_SB 32 (e_x0 E) (exv_len E) (e_x0 E + p) 0 1 HXRA HBx);
      [rewrite (U_atom E0 32 _ E32) by lia; reflexivity | lia | lia |].
    intros z Hz. revert HXSB. unfold SHADOW_OFF. lia.
Qed.
(* the common start and end of a run from a p / end seat *)
Ltac a2_run_pre HST lyc pos regs E0 HE0 R2 R9 R18 R19 R25 :=
  a2_E0facts E0 regs (frame_addr lyc 1 pos) R2 R9 R18 R19 R25;
  assert (E32 : ew E0 32 = Z_to_bv 64 (e_x0 E + _)) by (subst E0; exact (ew_Ereg_extra regs _ 0));
  assert (E33 : ew E0 33 = Z_to_bv 64 (e_x0 E + exv_len E)) by (subst E0; exact (ew_Ereg_extra regs _ 1)).
Ltac a2_post_common HS HFr E0 HE0 extras U19 :=
  exw_kept_of HFr (fun a => e_q E <= a < e_q E + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U19 in h);
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (AG0 : env_agree 32 E0 Ex)
      by (first [apply env_agree_refl | split; [intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity | reflexivity]]);
    assert (AG : env_agree 32 extras Ex) by (rewrite <- HE0; exact AG0)
  end;
  pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ; cbn [ms_mem restrict] in RQ.
Ltac a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 :=
  split; [split; [exact HJ | exact HPM]|]; split; [exact KEPT|]; split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (apresent_grows _ _ _ a HG Ha)
  | a2_kregs HS AG AG0 H22 H23 E19 E25 ].

(* R5a / R2a: in->p at or past in->end: s8 reloaded, to CX *)
Lemma a2_run5a : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> exv_len E <= p ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv
       (fun a => e_q E <= a < e_q E + 8) ->
     getr regs' 24 = w64 (frame_addr lyc 1 pos) ->
     val_mem rsegs (mrestrict (w_H Wc) mem') (e_q E) 8 (e_x0 E + p) ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_CX regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_W2 regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl Q HST Hp HK.
pose proof (a2_seat_pa lyc Sc Hpc Wc regs memc mdc k pos p dl A2_W2 HST Hp) as (HS & SHOK).
a2_pre HST.
remember (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) as E0 eqn:HE0.
a2_run_pre HST lyc pos regs E0 HE0 R2 R9 R18 R19 R25.
assert (U32 : bv_unsigned (ew E0 32) = e_x0 E + p) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_W2) with (Z_to_bv 64 A2_W2).
exw_run_to RUNTO HS HJ SHOK HPM A2_CX.
{ a2_awr U19. }
a2_post_common HS HFr E0 HE0 (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) U19.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 0 8 (SOff 32 0) (e_x0 E + p) RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(left; reflexivity)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U32; f_equal; lia) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
prreg HS (24%bv : bv 5) R24'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | rewrite R24'; exact E18 | exact VQ].
Qed.

Lemma a2_run2a : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> exv_len E <= p ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv
       (fun a => e_q E <= a < e_q E + 8) ->
     getr regs' 24 = w64 (frame_addr lyc 1 pos) -> getr regs' 21 = w64 (-1) ->
     val_mem rsegs (mrestrict (w_H Wc) mem') (e_q E) 8 (e_x0 E + p) ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_CX regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_W1 regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl Q HST Hp HK.
pose proof (a2_seat_pa lyc Sc Hpc Wc regs memc mdc k pos p dl A2_W1 HST Hp) as (HS & SHOK).
a2_pre HST.
remember (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) as E0 eqn:HE0.
a2_run_pre HST lyc pos regs E0 HE0 R2 R9 R18 R19 R25.
assert (U32 : bv_unsigned (ew E0 32) = e_x0 E + p) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_W1) with (Z_to_bv 64 A2_W1).
exw_run_to RUNTO HS HJ SHOK HPM A2_CX.
{ a2_awr U19. }
a2_post_common HS HFr E0 HE0 (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) U19.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 0 8 (SOff 32 0) (e_x0 E + p) RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(left; reflexivity)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U32; f_equal; lia) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
prreg HS (24%bv : bv 5) R24'. prreg HS (21%bv : bv 5) R21'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | rewrite R24'; exact E18 | | exact VQ].
rewrite R21'. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.

(* R5b / R2b: in->p before in->end, the byte there not c: to CX *)
Lemma a2_run5b : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> p < exv_len E -> nth (Z.to_nat p) (e_x E) 0 <> 58 ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv
       (fun a => e_q E <= a < e_q E + 8) ->
     getr regs' 24 = w64 (frame_addr lyc 1 pos) ->
     val_mem rsegs (mrestrict (w_H Wc) mem') (e_q E) 8 (e_x0 E + p) ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_CX regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_W2 regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl Q HST Hp Hb HK.
pose proof (a2_seat_pb lyc Sc Hpc Wc regs memc mdc k pos p dl A2_W2 58 HST Hp Hb ltac:(lia)) as (HS & SHOK).
a2_pre HST.
remember (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E);
  Z_to_bv 64 (nth (Z.to_nat p) (e_x E) 0)]) as E0 eqn:HE0.
a2_run_pre HST lyc pos regs E0 HE0 R2 R9 R18 R19 R25.
assert (U32 : bv_unsigned (ew E0 32) = e_x0 E + p) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_W2) with (Z_to_bv 64 A2_W2).
exw_run_to RUNTO HS HJ SHOK HPM A2_CX.
{ a2_awr U19. }
a2_post_common HS HFr E0 HE0 (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E);
  Z_to_bv 64 (nth (Z.to_nat p) (e_x E) 0)]) U19.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 0 8 (SOff 32 0) (e_x0 E + p) RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(left; reflexivity)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U32; f_equal; lia) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
prreg HS (24%bv : bv 5) R24'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | rewrite R24'; exact E18 | exact VQ].
Qed.

Lemma a2_run2b : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> p < exv_len E -> nth (Z.to_nat p) (e_x E) 0 <> 34 ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv
       (fun a => e_q E <= a < e_q E + 8) ->
     getr regs' 24 = w64 (frame_addr lyc 1 pos) -> getr regs' 21 = w64 (-1) ->
     val_mem rsegs (mrestrict (w_H Wc) mem') (e_q E) 8 (e_x0 E + p) ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_CX regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_W1 regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl Q HST Hp Hb HK.
pose proof (a2_seat_pb lyc Sc Hpc Wc regs memc mdc k pos p dl A2_W1 34 HST Hp Hb ltac:(lia)) as (HS & SHOK).
a2_pre HST.
remember (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E);
  Z_to_bv 64 (nth (Z.to_nat p) (e_x E) 0)]) as E0 eqn:HE0.
a2_run_pre HST lyc pos regs E0 HE0 R2 R9 R18 R19 R25.
assert (U32 : bv_unsigned (ew E0 32) = e_x0 E + p) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_W1) with (Z_to_bv 64 A2_W1).
exw_run_to RUNTO HS HJ SHOK HPM A2_CX.
{ a2_awr U19. }
a2_post_common HS HFr E0 HE0 (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E);
  Z_to_bv 64 (nth (Z.to_nat p) (e_x E) 0)]) U19.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 0 8 (SOff 32 0) (e_x0 E + p) RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(left; reflexivity)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U32; f_equal; lia) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
prreg HS (24%bv : bv 5) R24'. prreg HS (21%bv : bv 5) R21'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | rewrite R24'; exact E18 | | exact VQ].
rewrite R21'. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.

(* R2c: the opening quote: to ex_string (a0 = q, ra = B 0x83b78) *)
Lemma a2_run2c : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> p < exv_len E -> nth (Z.to_nat p) (e_x E) 0 = 34 ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv
       (fun a => e_q E <= a < e_q E + 8) ->
     getr regs' 10 = w64 (e_q E) -> getr regs' 1 = Z_to_bv 64 A2_S -> getr regs' 21 = w64 (-1) ->
     val_mem rsegs (mrestrict (w_H Wc) mem') (e_q E) 8 (e_x0 E + p) ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_STR regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_W1 regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl Q HST Hp Hb HK.
pose proof (a2_seat_pc lyc Sc Hpc Wc regs memc mdc k pos p dl A2_W1 34 HST Hp Hb) as (HS & SHOK).
a2_pre HST.
remember (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) as E0 eqn:HE0.
a2_run_pre HST lyc pos regs E0 HE0 R2 R9 R18 R19 R25.
assert (U32 : bv_unsigned (ew E0 32) = e_x0 E + p) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_W1) with (Z_to_bv 64 A2_W1).
exw_run_to RUNTO HS HJ SHOK HPM A2_STR.
{ a2_awr U19. }
a2_post_common HS HFr E0 HE0 (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) U19.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 0 8 (SOff 32 0) (e_x0 E + p) RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(left; reflexivity)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U32; f_equal; lia) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
prreg HS (10%bv : bv 5) R10'. prreg HS (1%bv : bv 5) R1'. prreg HS (21%bv : bv 5) R21'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | rewrite R10'; exact E19 | | | exact VQ].
- rewrite R1'. reflexivity.
- rewrite R21'. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.

(* R5c: the ':' : in->p += 1, to LR *)
Lemma a2_run5c : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> p < exv_len E -> nth (Z.to_nat p) (e_x E) 0 = 58 ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv
       (fun a => e_q E <= a < e_q E + 8) ->
     val_mem rsegs (mrestrict (w_H Wc) mem') (e_q E) 8 (e_x0 E + (p + 1)) ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_LR regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_W2 regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl Q HST Hp Hb HK.
pose proof (a2_seat_pc lyc Sc Hpc Wc regs memc mdc k pos p dl A2_W2 58 HST Hp Hb) as (HS & SHOK).
a2_pre HST.
remember (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) as E0 eqn:HE0.
a2_run_pre HST lyc pos regs E0 HE0 R2 R9 R18 R19 R25.
assert (U32 : bv_unsigned (ew E0 32) = e_x0 E + p) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_W2) with (Z_to_bv 64 A2_W2).
exw_run_to RUNTO HS HJ SHOK HPM A2_LR.
{ a2_awr U19. }
a2_post_common HS HFr E0 HE0 (Ereg regs [Z_to_bv 64 (e_x0 E + p); Z_to_bv 64 (e_x0 E + exv_len E)]) U19.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 0 8 (SOff 32 1) (e_x0 E + (p + 1)) RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(left; reflexivity)
  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U32; f_equal; lia) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | exact VQ].
Qed.
Ltac a2_agree HS E0 HE0 extras :=
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (AG0 : env_agree 32 E0 Ex)
      by (first [apply env_agree_refl | split; [intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity | reflexivity]]);
    assert (AG : env_agree 32 extras Ex) by (rewrite <- HE0; exact AG0)
  end.
Ltac a2_facts_fb U2 U9 U19 U25 :=
  cbn [f_atoms atoms_ok a2_fb]; unfold afact_ok; cbn [af_lo af_hi af_al2];
  rewrite U2, U9, U19, U25; change (2 ^ 4) with 16; change (2 ^ 5) with 32; change (2 ^ 3) with 8;
  rewrite ?Z.pow_0_r, ?Z.mod_1_r; unfold SHADOW_OFF; repeat split; lia.

(* R1 (B 0x83b1c -> ex_ws): c = '{' : the first ex_ws (a0 = q, ra = B 0x83b2c) *)
Lemma a2_run1 : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
       (fun _ => False) ->
     getr regs' 10 = w64 (e_q E) -> getr regs' 1 = Z_to_bv 64 A2_W1 ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_WS regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_LK regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl Q HST HK.
a2_pre HST.
remember (Ereg regs []) as E0 eqn:HE0.
a2_E0facts E0 regs (frame_addr lyc 1 pos) R2 R9 R18 R19 R25.
assert (HS : st_ok rsegs E0 ss_a2_r1 (restrict (w_H Wc) (mkst regs (Z_to_bv 64 A2_LK) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_a2_r1. apply exw_st_ok_full.
  - subst E0. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H27].
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. a2_facts_fb U2 U9 U19 U25. }
assert (SHOK : sh_ok rsegs A2_SB [] E0 (mrestrict (w_H Wc) memc)) by constructor.
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_LK) with (Z_to_bv 64 A2_LK).
exw_run_to RUNTO HS HJ SHOK HPM A2_WS.
{ a2_awr U19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => cbn [ew ewset Nat.eqb] in h).
a2_agree HS E0 HE0 (Ereg regs []).
prreg HS (10%bv : bv 5) R10'. prreg HS (1%bv : bv 5) R1'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | rewrite R10'; exact E19 | rewrite R1'; reflexivity].
Qed.

(* R3a (B 0x83b78 -> CX): ex_string returned -1 *)
Lemma a2_run3a : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> getr regs 10 = w64 (-1) ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv
       (fun _ => False) ->
     getr regs' 24 = w64 (frame_addr lyc 1 pos) ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_CX regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_S regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl Q HST H10 HK.
a2_pre HST.
remember (Ereg regs []) as E0 eqn:HE0.
a2_E0facts E0 regs (frame_addr lyc 1 pos) R2 R9 R18 R19 R25.
assert (HS : st_ok rsegs E0 ss_a2_r3a (restrict (w_H Wc) (mkst regs (Z_to_bv 64 A2_S) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_a2_r3a. apply exw_st_ok_full.
  - subst E0. apply regs_ok_pin; [a2_regsok H22 H23 E19 E25 | intros X; discriminate X |].
    cbn [sv_denot]. rewrite H10. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
  - vm_compute. reflexivity.
  - unfold a2_r3_s1x. constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ (exv_s1 E) 120 8 (SOff 18 0) (frame_addr lyc 1 pos));
      [rewrite (a2_denot_off _ 18 0 _ E18) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | zside | exact S120].
  - split; exact I.
  - split; [|split; exact I]. a2_facts_fb U2 U9 U19 U25. }
assert (SHOK : sh_ok rsegs A2_SB [] E0 (mrestrict (w_H Wc) memc)) by constructor.
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_S) with (Z_to_bv 64 A2_S).
exw_run_to RUNTO HS HJ SHOK HPM A2_CX.
{ a2_awr U19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => cbn [ew ewset Nat.eqb] in h).
a2_agree HS E0 HE0 (Ereg regs []).
prreg HS (24%bv : bv 5) R24'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | rewrite R24'; exact E18].
Qed.

(* R3b (B 0x83b78 -> ex_ws): ex_string returned 0, no node (s8 = 1): the second ex_ws (ra = B 0x83c2c) *)
Lemma a2_run3b : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> getr regs 10 = w64 0 -> getr regs 24 = w64 1 ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv
       (fun _ => False) ->
     getr regs' 10 = w64 (e_q E) -> getr regs' 1 = Z_to_bv 64 A2_W2 ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_WS regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_S regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl Q HST H10 H24 HK.
a2_pre HST.
remember (Ereg regs []) as E0 eqn:HE0.
a2_E0facts E0 regs (frame_addr lyc 1 pos) R2 R9 R18 R19 R25.
assert (HS : st_ok rsegs E0 ss_a2_r3b (restrict (w_H Wc) (mkst regs (Z_to_bv 64 A2_S) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_a2_r3b. apply exw_st_ok_full.
  - subst E0. apply regs_ok_pin; [apply regs_ok_pin; [a2_regsok H22 H23 E19 E25 | intros X; discriminate X |] |
      intros X; discriminate X |]; cbn [sv_denot]; assumption.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. a2_facts_fb U2 U9 U19 U25. }
assert (SHOK : sh_ok rsegs A2_SB [] E0 (mrestrict (w_H Wc) memc)) by constructor.
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_S) with (Z_to_bv 64 A2_S).
exw_run_to RUNTO HS HJ SHOK HPM A2_WS.
{ a2_awr U19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => cbn [ew ewset Nat.eqb] in h).
a2_agree HS E0 HE0 (Ereg regs []).
prreg HS (10%bv : bv 5) R10'. prreg HS (1%bv : bv 5) R1'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | rewrite R10'; exact E19 | rewrite R1'; reflexivity].
Qed.

(* R4a (B 0x83c08 -> ex_ws): strcmp returned 0: the second ex_ws *)
Lemma a2_run4a : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> getr regs 10 = w64 0 ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv
       (fun _ => False) ->
     getr regs' 10 = w64 (e_q E) -> getr regs' 1 = Z_to_bv 64 A2_W2 ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_WS regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_C regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl Q HST H10 HK.
a2_pre HST.
remember (Ereg regs []) as E0 eqn:HE0.
a2_E0facts E0 regs (frame_addr lyc 1 pos) R2 R9 R18 R19 R25.
assert (HS : st_ok rsegs E0 ss_a2_r4a (restrict (w_H Wc) (mkst regs (Z_to_bv 64 A2_C) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_a2_r4a. apply exw_st_ok_full.
  - subst E0. apply regs_ok_pin; [a2_regsok H22 H23 E19 E25 | intros X; discriminate X |]; cbn [sv_denot]; exact H10.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. a2_facts_fb U2 U9 U19 U25. }
assert (SHOK : sh_ok rsegs A2_SB [] E0 (mrestrict (w_H Wc) memc)) by constructor.
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_C) with (Z_to_bv 64 A2_C).
exw_run_to RUNTO HS HJ SHOK HPM A2_WS.
{ a2_awr U19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => cbn [ew ewset Nat.eqb] in h).
a2_agree HS E0 HE0 (Ereg regs []).
prreg HS (10%bv : bv 5) R10'. prreg HS (1%bv : bv 5) R1'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | rewrite R10'; exact E19 | rewrite R1'; reflexivity].
Qed.

(* R4b (B 0x83c08 -> ex_ws): strcmp returned non-zero: in->differs := 1, then the second ex_ws *)
Lemma a2_run4b : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (v : word) (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> getr regs 10 = v -> v <> w64 0 ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv
       (fun a => e_q E + 32 <= a < e_q E + 36) ->
     val_mem rsegs (mrestrict (w_H Wc) mem') (e_q E + 32) 4 1 ->
     getr regs' 10 = w64 (e_q E) -> getr regs' 1 = Z_to_bv 64 A2_W2 ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_WS regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_C regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl v Q HST H10 Hv0 HK.
pose proof HST as (_ & _ & _ & _ & _ & HSP0 & HCUR0 & _ & Hdl0 & _).
destruct HSP0 as (_ & _ & _ & _ & _ & S80 & _ & _ & S72 & _).
destruct HCUR0 as (_ & _ & _ & _ & Vl).
a2_pre HST.
assert (Hv : 1 <= bv_unsigned v < 2 ^ 64).
{ pose proof (bv_unsigned_in_range _ v) as R. unfold bv_modulus in R. cbn in R.
  destruct (Z.eq_dec (bv_unsigned v) 0) as [Hz|Hz]; [|lia].
  exfalso. apply Hv0. apply bv_eq. rewrite Hz. reflexivity. }
remember (Ereg regs [v; Z_to_bv 64 dl]) as E0 eqn:HE0.
a2_E0facts E0 regs (frame_addr lyc 1 pos) R2 R9 R18 R19 R25.
assert (E32 : ew E0 32 = v) by (subst E0; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 dl) by (subst E0; exact (ew_Ereg_extra regs _ 1)).
assert (U33 : bv_unsigned (ew E0 33) = dl) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E0 ss_a2_r4b (restrict (w_H Wc) (mkst regs (Z_to_bv 64 A2_C) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_a2_r4b. apply exw_st_ok_full.
  - apply regs_ok_pin; [subst E0; a2_regsok H22 H23 E19 E25 | intros X; discriminate X |].
    cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact H10.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs _ _ (exv_s1 E) 72 8 (a2_shx 19 32) (shadow_addr (e_q E + 32)));
          [rewrite (a2_denot_shx _ 19 32 _ E19 E25) by lia; reflexivity
          | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside | exact S72].
      * apply (chunk_ok_val rsegs _ _ (exv_s1 E) 80 8 (SOff 19 32) (e_q E + 32));
          [rewrite (a2_denot_off _ 19 32 _ E19) by lia; reflexivity | cbn; lia | zside | exact S80].
    + rewrite U19. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable rsegs). apply HPRQ. lia. }
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (e_q E) 32 4 (SOff 33 0) dl);
        [rewrite (a2_denot_off _ 33 0 _ E33) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | zside | exact Vl].
  - apply pairwise_disjoint_of_extents. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok a2_fb]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, U33, U2, U9, U19, U25. change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok rsegs A2_SB [a2_SHq] E0 (mrestrict (w_H Wc) memc)).
{ unfold a2_SHq. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H Wc) memc E0 A2_SB 19 (e_q E) 40 (e_q E) 0 40 HQRA HBx);
    [rewrite (U_atom E0 19 _ E19) by lia; reflexivity | lia | lia |].
  intros z Hz. unfold SHADOW_OFF. lia. }
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_C) with (Z_to_bv 64 A2_C).
exw_run_to RUNTO HS HJ SHOK HPM A2_WS.
{ a2_awr U19. }
exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36)
  ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U19 in h).
a2_agree HS E0 HE0 (Ereg regs [v; Z_to_bv 64 dl]).
pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 32 4 (SLit 1) 1 RQ
  ltac:(cbn [ew ewset Nat.eqb]; exact U19) ltac:(left; reflexivity)
  ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
prreg HS (10%bv : bv 5) R10'. prreg HS (1%bv : bv 5) R1'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | exact VQ | rewrite R10'; exact E19 |
  rewrite R1'; reflexivity].
Qed.
(* R3c (B 0x83b78 -> 0x83b9c): ex_string returned 0 and there is a node (s8 = 0): vv checked, the node's keys word
   loaded (a1 = keys) *)
Lemma a2_run3c : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (keys : Z)
    (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> getr regs 10 = w64 0 -> getr regs 24 = w64 0 ->
  vv = e_v E -> 4096 <= e_v E -> e_v E + 56 <= 2 ^ 47 -> e_v E mod 8 = 0 ->
  range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (e_v E) 56 ->
  (forall z, e_v E <= z < e_v E + 56 ->
     ~ (SHADOW_OFF <= z < SHADOW_OFF + 17592186044416) /\ ~ (exv_sp E - exv_STK E <= z < exv_sp E)) ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_v E + 32) 8 keys -> 0 <= keys < 2 ^ 64 ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv
       (fun _ => False) ->
     getr regs' 11 = w64 keys ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_K regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_S regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl keys Q HST H10 H24 Hvv Hv1 Hv47 Hv8 HVRA HVD VK Hk HK.
pose proof HST as (_ & _ & _ & _ & _ & HSP0 & _).
destruct HSP0 as (S152 & _ & _ & S48 & S40 & _).
a2_pre HST.
rewrite Hvv in S152, S48, S40.
pose proof (GEOM E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB)
  as (_ & _ & _ & _ & _ & _ & _ & (G8a & G8b) & _ & _ & _ & _ & G13 & _).
remember (Ereg regs [Z_to_bv 64 (e_v E); Z_to_bv 64 keys]) as E0 eqn:HE0.
a2_E0facts E0 regs (frame_addr lyc 1 pos) R2 R9 R18 R19 R25.
assert (E32 : ew E0 32 = Z_to_bv 64 (e_v E)) by (subst E0; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 keys) by (subst E0; exact (ew_Ereg_extra regs _ 1)).
assert (U32 : bv_unsigned (ew E0 32) = e_v E) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = keys) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (HVD (e_v E + 32) ltac:(lia)) as (_ & D1). pose proof (HVD (e_v E + 39) ltac:(lia)) as (_ & D2).
assert (HS : st_ok rsegs E0 ss_a2_r3c (restrict (w_H Wc) (mkst regs (Z_to_bv 64 A2_S) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_a2_r3c. apply exw_st_ok_full.
  - subst E0. apply regs_ok_pin; [apply regs_ok_pin; [a2_regsok H22 H23 E19 E25 | intros X; discriminate X |] |
      intros X; discriminate X |]; cbn [sv_denot]; assumption.
  - vm_compute. reflexivity.
  - unfold a2_r3c_rc. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs _ _ (exv_s1 E) 40 8 (a2_shx 32 32) (shadow_addr (e_v E + 32)));
          [rewrite (a2_denot_shx _ 32 32 _ E32 E25) by lia; reflexivity
          | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside | exact S40].
      * apply (chunk_ok_val rsegs _ _ (exv_s1 E) 48 8 (SOff 32 32) (e_v E + 32));
          [rewrite (a2_denot_off _ 32 32 _ E32) by lia; reflexivity | cbn; lia | zside | exact S48].
      * apply (chunk_ok_val rsegs _ _ (exv_s1 E) 152 8 (SOff 32 0) (e_v E));
          [rewrite (a2_denot_off _ 32 0 _ E32) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | zside | exact S152].
    + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (e_v E) 32 8 (SOff 33 0) keys);
        [rewrite (a2_denot_off _ 33 0 _ E33) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | zside | exact VK].
  - apply pairwise_disjoint_of_extents. unfold a2_r3c_rc. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    clear - G8a G8b G13 D1 D2 B2. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok a2_fb]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U19, U25, U32, U33.
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok rsegs A2_SB a2_SH3c E0 (mrestrict (w_H Wc) memc)).
{ unfold a2_SH3c. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H Wc) memc E0 A2_SB 32 (e_v E) 56 (e_v E) 0 56 HVRA HBx);
    [rewrite (U_atom E0 32 _ E32) by lia; reflexivity | lia | lia |].
  intros z Hz. apply (HVD z). lia. }
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_S) with (Z_to_bv 64 A2_S).
exw_run_to RUNTO HS HJ SHOK HPM A2_K.
{ a2_awr U19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => cbn [ew ewset Nat.eqb] in h).
a2_agree HS E0 HE0 (Ereg regs [Z_to_bv 64 (e_v E); Z_to_bv 64 keys]).
prreg HS (11%bv : bv 5) R11'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | rewrite R11'; exact E33].
Qed.

(* R3d (B 0x83b9c -> strcmp): the key slot keys + 8 i checked (UBSan B 0x83bac / 0x83bc0 / 0x83bc4 / 0x83bc8 /
   0x83bd8 not taken) and read, a0 = keys[i], a1 = in->scratch *)
Lemma a2_run3d : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (keys x : Z)
    (Q : world rsegs -> config -> Prop),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> getr regs 11 = w64 keys ->
  keys mod 8 = 0 -> 4096 <= keys -> keys + 8 * Z.of_nat i + 8 <= alloc_ceiling ->
  range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (keys + 8 * Z.of_nat i) 8 ->
  (forall z, keys + 8 * Z.of_nat i <= z < keys + 8 * Z.of_nat i + 8 ->
     ~ (SHADOW_OFF <= z < SHADOW_OFF + 17592186044416)) ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (keys + 8 * Z.of_nat i) 8 x -> 0 <= x < 2 ^ 64 -> 0 <= e_scr E < 2 ^ 64 ->
  (forall (regs' : bvmap 5 word) mem' md',
     a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv
       (fun _ => False) ->
     getr regs' 10 = w64 x -> getr regs' 11 = w64 (e_scr E) -> getr regs' 1 = Z_to_bv 64 A2_C ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_CMP regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_K regs memc mdc) Q.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl keys x Q HST H11 Hk8 Hk4 Hkce HSRA HSD VX Hx Hscr HK.
pose proof HST as (_ & _ & _ & _ & _ & HSP0 & HCUR0 & _ & _ & _).
destruct HSP0 as (_ & _ & _ & _ & _ & _ & S24 & S16 & _ & _ & S32 & S136 & _ & S128 & _).
destruct HCUR0 as (_ & _ & _ & Vs & _).
a2_pre HST.
assert (Hi47 : 0 <= Z.of_nat i <= 2 ^ 47) by (unfold exv_len in *; lia).
remember (Ereg regs [Z_to_bv 64 keys; Z_to_bv 64 (keys + 8 * Z.of_nat i); Z_to_bv 64 (Z.of_nat i); Z_to_bv 64 x;
  Z_to_bv 64 (e_scr E)]) as E0 eqn:HE0.
a2_E0facts E0 regs (frame_addr lyc 1 pos) R2 R9 R18 R19 R25.
assert (E32 : ew E0 32 = Z_to_bv 64 keys) by (subst E0; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E0 33 = Z_to_bv 64 (keys + 8 * Z.of_nat i)) by (subst E0; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 (Z.of_nat i)) by (subst E0; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E0 35 = Z_to_bv 64 x) by (subst E0; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E0 36 = Z_to_bv 64 (e_scr E)) by (subst E0; exact (ew_Ereg_extra regs _ 4)).
assert (U32 : bv_unsigned (ew E0 32) = keys) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E0 33) = keys + 8 * Z.of_nat i) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E0 34) = Z.of_nat i) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E0 35) = x) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E0 36) = e_scr E) by (rewrite E36; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E0 ss_a2_r3d (restrict (w_H Wc) (mkst regs (Z_to_bv 64 A2_K) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_a2_r3d. apply exw_st_ok_full.
  - subst E0. apply regs_ok_pin; [a2_regsok H22 H23 E19 E25 | intros X; discriminate X |].
    rewrite H11. symmetry. rewrite (a2_denot_off _ 32 0 _ E32) by lia. rewrite Z.add_0_r. reflexivity.
  - vm_compute. reflexivity.
  - unfold a2_r3d_rc. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs _ _ (exv_s1 E) 16 8 (a2_shx 19 24) (shadow_addr (e_q E + 24)));
          [rewrite (a2_denot_shx _ 19 24 _ E19 E25) by lia; reflexivity
          | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside | exact S16].
      * apply (chunk_ok_val rsegs _ _ (exv_s1 E) 24 8 (SOff 19 24) (e_q E + 24));
          [rewrite (a2_denot_off _ 19 24 _ E19) by lia; reflexivity | cbn; lia | zside | exact S24].
      * apply (chunk_ok_val rsegs _ _ (exv_s1 E) 32 8 (SLit (2 ^ 60)) (2 ^ 60)); [reflexivity | cbn; lia | zside | exact S32].
      * apply (chunk_ok_val rsegs _ _ (exv_s1 E) 128 8 (SAlu ALU_SUB (SOff 33 0) (SOff 32 0)) (8 * Z.of_nat i));
          [rewrite (a2_denot_sub _ 33 32 _ _ E33 E32) by lia; f_equal; lia | cbn; lia | zside | exact S128].
      * apply (chunk_ok_val rsegs _ _ (exv_s1 E) 136 8 (SOff 34 0) (Z.of_nat i));
          [rewrite (a2_denot_off _ 34 0 _ E34) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | zside | exact S136].
    + rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (keys + 8 * Z.of_nat i) 0 8 (SOff 35 0) x);
        [rewrite (a2_denot_off _ 35 0 _ E35) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | zside |
         rewrite Z.add_0_r; exact VX].
    + rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (e_q E) 24 8 (SOff 36 0) (e_scr E));
        [rewrite (a2_denot_off _ 36 0 _ E36) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | zside | exact Vs].
  - apply pairwise_disjoint_of_extents. unfold a2_r3d_rc. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    clear - B1 B2 B4 Hkce Hk4. repeat split; lia.
  - split; [|split; [|exact I]].
    + cbn [f_atoms atoms_ok a2_r3d_fc a2_fb]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U9, U19, U25, U32, U33, U34, U35, U36.
      change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
      rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
    + cbn [f_conds conds_ok]. split; [|split; [|exact I]]; unfold acond_ok; cbn [ac_c ac_a ac_b].
      { rewrite branch_geu_U, (U_atom _ 33 _ E33), (U_atom _ 32 _ E32) by lia. apply negb_true_iff, Z.ltb_ge. lia. }
      { unfold a2_cnd_i. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, (a2_srl_i _ (Z.of_nat i) E34 Hi47), U_lit by lia.
        reflexivity. } }
assert (SHOK : sh_ok rsegs A2_SB a2_SH3d E0 (mrestrict (w_H Wc) memc)).
{ unfold a2_SH3d, a2_SHq. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H Wc) memc E0 A2_SB 19 (e_q E) 40 (e_q E) 0 40 HQRA HBx);
      [rewrite (U_atom E0 19 _ E19) by lia; reflexivity | lia | lia |].
    intros z Hz. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range rsegs (w_H Wc) memc E0 A2_SB 33 (keys + 8 * Z.of_nat i) 8 (keys + 8 * Z.of_nat i) 0 8
      HSRA HBx); [rewrite (U_atom E0 33 _ E33) by lia; reflexivity | lia | lia |].
    intros z Hz. apply (HSD z). lia. }
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem E)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK E) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_K) with (Z_to_bv 64 A2_K).
exw_run_to RUNTO HS HJ SHOK HPM A2_CMP.
{ a2_awr U19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => cbn [ew ewset Nat.eqb] in h).
a2_agree HS E0 HE0 (Ereg regs [Z_to_bv 64 keys; Z_to_bv 64 (keys + 8 * Z.of_nat i); Z_to_bv 64 (Z.of_nat i);
  Z_to_bv 64 x; Z_to_bv 64 (e_scr E)]).
prreg HS (10%bv : bv 5) R10'. prreg HS (11%bv : bv 5) R11'. prreg HS (1%bv : bv 5) R1'.
pmkst HS.
apply HK; [a2_runpost_tac HJ HPM HS KEPT HG AG AG0 H22 H23 E19 E25 | rewrite R10'; exact E35 | rewrite R11'; exact E36 |
  rewrite R1'; reflexivity].
Qed.

(* ---- the composition of the object arm ---- *)

Lemma a2_fl0 : fl = 0 -> e_v E <> 0.
Proof. intros H0. destruct Hfl as [(_ & H1) | (_ & _ & _ & Hv & _)]; [lia | exact Hv]. Qed.

Lemma a2_frame_rng : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos,
  EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos HB.
pose proof (GEOM E lyc Sc Hpc Wc regs memc mdc k pos HP HB)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GAR & _).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & HFRS & _).
destruct (frames_bounds_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc 1 pos GAR ltac:(rewrite HFRS; left; reflexivity))
  as (F1 & F2 & _).
change (fs_frame_bytes 1) with 128 in F2. lia.
Qed.

Lemma a2_frame_eq : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos ly2 S2 Hp2 W2 (regs2 : bvmap 5 word)
    mem2 md2 k2,
  EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  EXBs (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos -> getr regs2 18 = getr regs 18 ->
  frame_addr ly2 1 pos = frame_addr lyc 1 pos.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HB1 HB2 H18.
destruct (EXBSREG E lyc Sc Hpc Wc regs memc mdc k pos HB1) as (r1 & HE1 & _ & _ & _ & _ & _ & _ & _ & F1 & _).
destruct (EXBSREG E ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos HB2) as (r2 & HE2 & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (a2_frame_rng lyc Sc Hpc Wc r1 memc mdc k pos HE1) as (A1 & A2).
pose proof (a2_frame_rng ly2 S2 Hp2 W2 r2 mem2 md2 k2 pos HE2) as (A3 & A4).
pose proof asan_consts as (C1 & _).
rewrite F1, F2 in H18. apply a2_w64_inj in H18; [exact H18 | lia | lia].
Qed.

Lemma a2_child : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl,
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> kid = 0 \/ exv_child E Wc memc i kid tk.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl HST.
destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HKD).
destruct Hfl as [(Hk & _) | (Hf0 & _ & _ & Hv0 & Hic & Htk & Hkr & Hkd & _)]; [left; exact Hk|].
right. split; [exact Hv0|]. split; [exact Hic|]. split; [exact Htk|].
exists kids. split; [exact (HKD Hf0)|]. split; [exact Hkr | exact Hkd].
Qed.

(* the state facts across a program call (or strcmp): the cursor's p moves, the rest is kept *)
Lemma a2_st_move : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl ly2 S2 Hp2 (W2 : world rsegs)
    (regs2 : bvmap 5 word) mem2 md2 k2 p',
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl ->
  EXBs (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos ->
  (forall r, In r [20; 22; 23; 27]%bv -> getr regs2 r = getr regs r) ->
  frame_addr ly2 1 pos = frame_addr lyc 1 pos ->
  (forall a, exv_s1 E + 8 <= a < exv_s1 E + 160 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
  (forall a, e_q E + 8 <= a < e_q E + 40 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
  (fl = 0 -> forall a, e_v E + 24 <= a < e_v E + 32 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_q E) 8 (e_x0 E + p') -> 0 <= p' <= exv_len E ->
  a2_st ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos p' dl.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl ly2 S2 Hp2 W2 regs2 mem2 md2 k2 p' HST HBs2 HR HFR KS KQ KV Vp' Hp'.
destruct HST as (HBs & H27 & H22 & H23 & H20 & HSP & HCUR & Hpr & Hdlr & HKD).
assert (KV8 : forall o v, 8 <= o <= 152 -> exv_spill E Wc memc o v -> exv_spill E W2 mem2 o v).
{ intros o v Ho Hv. unfold exv_spill in *.
  apply (YC88.val_mem_aview_kept_x rsegs (w_H Wc) (w_H W2) memc mem2); [|exact Hv].
  intros z Hz. change (Z.of_nat 8) with 8 in Hz. apply KS. lia. }
assert (KQ' : forall o n0 v, 8 <= o -> o + Z.of_nat n0 <= 40 ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_q E + o) n0 v -> val_mem rsegs (mrestrict (w_H W2) mem2) (e_q E + o) n0 v).
{ intros o n0 v Ho Hon Hv. apply (YC88.val_mem_aview_kept_x rsegs (w_H Wc) (w_H W2) memc mem2); [|exact Hv].
  intros z Hz. apply KQ. lia. }
split; [exact HBs2|].
split; [rewrite HR by a2_inl; exact H27|].
split; [rewrite HR by a2_inl; exact H22|].
split; [rewrite HR by a2_inl; exact H23|].
split; [rewrite HR by a2_inl; exact H20|].
split.
{ unfold exv_spills. cbv zeta. rewrite HFR.
  destruct HSP as (S152 & S88 & S56 & S48 & S40 & S80 & S24 & S16 & S72 & S8 & S32 & S136 & S112 & S128 & S64 & S104 &
    S96 & S120 & S144).
  repeat split; apply KV8; first [lia | assumption]. }
destruct HCUR as (Vp & Ve & Vd & Vs & Vl).
split.
{ split; [exact Vp'|].
  split; [apply KQ'; [lia | change (Z.of_nat 8) with 8; lia | exact Ve]|].
  split; [apply KQ'; [lia | change (Z.of_nat 4) with 4; lia | exact Vd]|].
  split; [apply KQ'; [lia | change (Z.of_nat 8) with 8; lia | exact Vs]|].
  apply KQ'; [lia | change (Z.of_nat 4) with 4; lia | exact Vl]. }
split; [exact Hp'|]. split; [exact Hdlr|].
intros Hf0. apply (YC88.val_mem_aview_kept_x rsegs (w_H Wc) (w_H W2) memc mem2); [|exact (HKD Hf0)].
intros z Hz. change (Z.of_nat 8) with 8 in Hz. apply (KV Hf0). lia.
Qed.

(* the state facts across a run that writes no byte *)
Lemma a2_st_run0 : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (regs' : bvmap 5 word) mem' md'
    (l : list (bv 5)),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl ->
  a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' l (fun _ => False) ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv -> In r l) ->
  a2_st lyc Sc Hpc Wc regs' mem' md' k pos p dl.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl regs' mem' md' l HST HRP Hincl.
pose proof HST as (_ & _ & _ & _ & _ & _ & HCUR & Hpr & Hdlr & _).
destruct HCUR as (Vp & _ & _ & _ & Vl).
destruct (a2_seat lyc Sc Hpc Wc regs memc mdc k pos p dl HST)
  as (regs0 & HB0 & R2 & R9 & R18 & R19 & R25 & B1 & B2 & B3 & B4 & B5 & B6 & _).
pose proof HRP as (_ & KEPT & _). pose proof asan_consts as (C1 & _).
apply (a2_runpost_st lyc Sc Hpc Wc regs memc mdc k pos p dl regs' mem' md' l (fun _ => False) p dl HST HRP Hincl).
- intros a [].
- apply (exw_val_kept rsegs (w_H Wc) memc mem'); [|exact Vp]. intros z Hz. change (Z.of_nat 8) with 8 in Hz.
  apply KEPT; [lia | intros []].
- apply (exw_val_kept rsegs (w_H Wc) memc mem'); [|exact Vl]. intros z Hz. change (Z.of_nat 4) with 4 in Hz.
  apply KEPT; [lia | intros []].
- exact Hpr.
- exact Hdlr.
Qed.

(* the state facts after a straight run that moves in->p only (in->differs kept) *)
Lemma a2_st_runq : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl (regs' : bvmap 5 word) mem' md'
    (l : list (bv 5)) p',
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl ->
  a2_runpost lyc Sc Hpc Wc regs memc k pos regs' mem' md' l (fun a => e_q E <= a < e_q E + 8) ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv -> In r l) ->
  val_mem rsegs (mrestrict (w_H Wc) mem') (e_q E) 8 (e_x0 E + p') -> 0 <= p' <= exv_len E ->
  a2_st lyc Sc Hpc Wc regs' mem' md' k pos p' dl.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl regs' mem' md' l p' HST HRP Hincl Vp' Hp'.
pose proof HST as (_ & _ & _ & _ & _ & _ & HCUR & Hpr & Hdlr & _).
destruct HCUR as (_ & _ & _ & _ & Vl).
destruct (a2_seat lyc Sc Hpc Wc regs memc mdc k pos p dl HST)
  as (regs0 & HB0 & R2 & R9 & R18 & R19 & R25 & B1 & B2 & B3 & B4 & B5 & B6 & _).
pose proof HRP as (_ & KEPT & _). pose proof asan_consts as (C1 & _).
apply (a2_runpost_st lyc Sc Hpc Wc regs memc mdc k pos p dl regs' mem' md' l _ p' dl HST HRP Hincl).
- intros a Ha. left. exact Ha.
- exact Vp'.
- apply (exw_val_kept rsegs (w_H Wc) memc mem'); [|exact Vl]. intros z Hz. change (Z.of_nat 4) with 4 in Hz.
  apply KEPT; [lia | cbv beta; lia].
- exact Hp'.
- exact Hdlr.
Qed.

(* after a program call (ex_ws, ex_string): the state facts at the callee's return *)
Lemma a2_st_call : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl ly2 S2 Hp2 (W2 : world rsegs)
    (regs2 : bvmap 5 word) mem2 md2 k2 p',
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl ->
  EXBs (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos -> aregs_preserved regs regs2 ->
  (forall a, exv_s1 E <= a < exv_sp E + e_d E -> ~ (e_q E <= a < e_q E + 8) ->
     aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
  (e_v E <> 0 -> forall a, e_v E <= a < e_v E + 56 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_q E) 8 (e_x0 E + p') -> 0 <= p' <= exv_len E ->
  a2_st ly2 S2 Hp2 W2 regs2 mem2 md2 k2 pos p' dl.
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl ly2 S2 Hp2 W2 regs2 mem2 md2 k2 p' HST HBs2 HPR HWIN HNODE Vp' Hp'.
pose proof HST as (HBs & _).
destruct (a2_seat lyc Sc Hpc Wc regs memc mdc k pos p dl HST)
  as (regs0 & HB0 & R2 & R9 & R18 & R19 & R25 & B1 & B2 & B3 & B4 & B5 & B6 & _).
apply (a2_st_move lyc Sc Hpc Wc regs memc mdc k pos p dl ly2 S2 Hp2 W2 regs2 mem2 md2 k2 p' HST HBs2).
- intros r Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]].
  + a2_prese HPR 20.
  + a2_prese HPR 22.
  + a2_prese HPR 23.
  + a2_prese HPR 27.
- apply (a2_frame_eq lyc Sc Hpc Wc regs memc mdc k pos ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HBs HBs2).
  a2_prese HPR 18.
- intros a Ha. apply HWIN; lia.
- intros a Ha. apply HWIN; lia.
- intros Hf0 a Ha. apply (HNODE (a2_fl0 Hf0)). lia.
- exact Vp'.
- exact Hp'.
Qed.

(* CX from the state facts with s8 back at the frame *)
Lemma a2_cx_st : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p dl,
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p dl -> getr regs 24 = w64 (frame_addr lyc 1 pos) ->
  getr regs 21 = w64 (-1) -> exv_name true (skipn (Z.to_nat ip) (e_x E)) = None ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_CX regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p dl HST H24 H21 HN.
destruct HST as (HBs & _ & _ & _ & _ & _ & HCUR & Hpr & Hdlr & _).
exact (a2_cx lyc Sc Hpc Wc regs memc mdc k pos p dl (KOFS fx E lyc Sc Hpc Wc regs memc mdc k pos HBs H24) H21 HCUR
  Hpr Hdlr HN).
Qed.

(* LR from the state facts: the name read, in->p past the ':' *)
Lemma a2_lr : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p1 dl1 nm,
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p1 dl1 -> ip <= p1 ->
  exv_name true (skipn (Z.to_nat ip) (e_x E)) = Some (nm, skipn (Z.to_nat p1) (e_x E)) ->
  (forall u dl', (dl' = 0 \/ dl' = 1) -> (dl' = 1 <-> dl1 = 1 \/ (kid <> 0 /\ tk <> u)) ->
     exv_dif E true vv dl' ((nm, u) :: acc)) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_LR regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p1 dl1 nm HST Hip1 HN HBK.
pose proof (a2_child lyc Sc Hpc Wc regs memc mdc k pos p1 dl1 HST) as HCH.
destruct HST as (HBs & H27 & H22 & H23 & H20 & HSP & HCUR & Hp1 & Hdl1 & _).
pose proof (HLR E lyc Sc Hpc Wc regs memc mdc k pos 123 i cap acc ip p1 vv dl1 kid tk nm) as HL.
cbv zeta in HL.
exact (HL Hn HP HBs Hi1 Hc (or_intror eq_refl) Hdep Hacc HCUR ltac:(lia) ltac:(lia) Hdl1 Hii ltac:(lia) HV HN HCH HBK
  H20 H27 H22 H23 HSP).
Qed.

(* phase 5 (B 0x83c2c): after the second ex_ws: ':' or CX *)
Lemma a2_ph5 : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p5 dl5 (z s rest : list Z),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p5 dl5 -> getr regs 21 = w64 (-1) ->
  PjGrammar.skip (skipn (Z.to_nat ip) (e_x E)) = 34 :: z ->
  exv_run0 (PjGrammar.jr_string z) = Some (s, rest) ->
  skipn (Z.to_nat p5) (e_x E) = PjGrammar.skip rest -> ip <= p5 ->
  (forall u dl', (dl' = 0 \/ dl' = 1) -> (dl' = 1 <-> dl5 = 1 \/ (kid <> 0 /\ tk <> u)) ->
     exv_dif E true vv dl' ((s, u) :: acc)) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_W2 regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p5 dl5 z s rest HST H21 Hsk Hjs Hp5 Hip5 HBK.
pose proof HST as (_ & _ & _ & _ & _ & _ & _ & Hpr5 & _).
assert (Hlen : exv_len E = Z.of_nat (length (e_x E))) by reflexivity.
assert (HN0 : forall b r1, PjGrammar.skip rest = b :: r1 ->
  exv_name true (skipn (Z.to_nat ip) (e_x E)) = if b =? 58 then Some (s, r1) else None).
{ intros b r1 Hsr. unfold exv_name. rewrite Hsk. cbv beta iota. change (34 =? 34) with true. cbv beta iota.
  rewrite Hjs. cbv beta iota. rewrite Hsr. reflexivity. }
destruct (Z_lt_le_dec p5 (exv_len E)) as [Hlt | Hge].
- destruct (PjGrammar.skip rest) as [|b r1] eqn:Hsr.
  { exfalso. apply (f_equal (@length Z)) in Hp5. rewrite length_skipn in Hp5. cbn [length] in Hp5. lia. }
  pose proof (a2_nth_skipn _ _ _ _ Hp5) as Hb.
  pose proof (a2_skipn_S _ _ _ _ Hp5) as Hr1.
  destruct (Z.eq_dec b 58) as [-> | Hb58].
  + apply (a2_run5c lyc Sc Hpc Wc regs memc mdc k pos p5 dl5 _ HST Hlt Hb).
    intros regs' mem' md' HRP VQ.
    pose proof (a2_st_runq lyc Sc Hpc Wc regs memc mdc k pos p5 dl5 regs' mem' md' _ (p5 + 1) HST HRP
      ltac:(a2_incl) VQ ltac:(lia)) as HST'.
    apply (a2_lr lyc Sc Hpc Wc regs' mem' md' k pos (p5 + 1) dl5 s HST' ltac:(lia)); [|exact HBK].
    rewrite (HN0 58 r1 eq_refl). change (58 =? 58) with true. cbv beta iota.
    replace (Z.to_nat (p5 + 1)) with (S (Z.to_nat p5)) by lia. rewrite Hr1. reflexivity.
  + apply (a2_run5b lyc Sc Hpc Wc regs memc mdc k pos p5 dl5 _ HST Hlt ltac:(rewrite Hb; exact Hb58)).
    intros regs' mem' md' HRP R24 VQ.
    pose proof HRP as (_ & _ & _ & HRR).
    pose proof (a2_st_runq lyc Sc Hpc Wc regs memc mdc k pos p5 dl5 regs' mem' md' _ p5 HST HRP
      ltac:(a2_incl) VQ ltac:(lia)) as HST'.
    apply (a2_cx_st lyc Sc Hpc Wc regs' mem' md' k pos p5 dl5 HST' R24); [rewrite HRR by a2_inl; exact H21|].
    rewrite (HN0 b r1 eq_refl). rewrite (proj2 (Z.eqb_neq b 58) Hb58). reflexivity.
- assert (Hsr : PjGrammar.skip rest = []) by (rewrite <- Hp5; apply skipn_all2; lia).
  apply (a2_run5a lyc Sc Hpc Wc regs memc mdc k pos p5 dl5 _ HST Hge).
  intros regs' mem' md' HRP R24 VQ.
  pose proof HRP as (_ & _ & _ & HRR).
  pose proof (a2_st_runq lyc Sc Hpc Wc regs memc mdc k pos p5 dl5 regs' mem' md' _ p5 HST HRP
    ltac:(a2_incl) VQ Hpr5) as HST'.
  apply (a2_cx_st lyc Sc Hpc Wc regs' mem' md' k pos p5 dl5 HST' R24); [rewrite HRR by a2_inl; exact H21|].
  unfold exv_name. rewrite Hsk. cbv beta iota. change (34 =? 34) with true. cbv beta iota.
  rewrite Hjs. cbv beta iota. rewrite Hsr. reflexivity.
Qed.

(* phase 4 (B 0x83c28): the second ex_ws *)
Lemma a2_ph4 : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p3 dl3 (z s rest : list Z),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p3 dl3 -> getr regs 10 = w64 (e_q E) -> getr regs 1 = Z_to_bv 64 A2_W2 ->
  getr regs 21 = w64 (-1) ->
  PjGrammar.skip (skipn (Z.to_nat ip) (e_x E)) = 34 :: z -> exv_run0 (PjGrammar.jr_string z) = Some (s, rest) ->
  rest = skipn (Z.to_nat p3) (e_x E) -> ip <= p3 ->
  (forall u dl', (dl' = 0 \/ dl' = 1) -> (dl' = 1 <-> dl3 = 1 \/ (kid <> 0 /\ tk <> u)) ->
     exv_dif E true vv dl' ((s, u) :: acc)) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_WS regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p3 dl3 z s rest HST H10 H1 H21 Hsk Hjs Hrest Hip3 HBK.
pose proof HST as (HBs & _ & _ & _ & _ & _ & HCUR & Hpr & _).
destruct HCUR as (Vp & Ve & _).
pose proof a2_pc_vals as (PW1 & PS & PC & PW2).
assert (Hlen : exv_len E = Z.of_nat (length (e_x E))) by reflexivity.
apply (CALLWS E lyc Sc Hpc Wc regs memc mdc k pos p3 A2_W2 _ HP HBs H10 H1 ltac:(vm_compute; reflexivity)
  ltac:(rewrite PW2; lia) Vp Ve Hpr).
intros ly2 S2 Hpz W2 regs2 mem2 md2 k1 HBs2 HPR HWIN HNODE Vq2.
pose proof (a2_skip_len (skipn (Z.to_nat p3) (e_x E))) as HL. rewrite length_skipn in HL.
set (p5 := exv_len E - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat p3) (e_x E))))).
assert (HST2 : a2_st ly2 S2 Hpz W2 regs2 mem2 md2 (k + k1) pos p5 dl3).
{ apply (a2_st_call lyc Sc Hpc Wc regs memc mdc k pos p3 dl3 ly2 S2 Hpz W2 regs2 mem2 md2 (k + k1) p5 HST HBs2 HPR
    HWIN HNODE).
  - replace (e_x0 E + p5) with (e_x0 E + exv_len E - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat p3) (e_x E)))))
      by (unfold p5; lia). exact Vq2.
  - unfold p5. lia. }
apply (a2_ph5 ly2 S2 Hpz W2 regs2 mem2 md2 (k + k1) pos p5 dl3 z s rest HST2).
- a2_presr HPR 21. exact H21.
- exact Hsk.
- exact Hjs.
- rewrite Hrest.
  rewrite <- (a2_skip_pos PSUF (e_x E) (skipn (Z.to_nat p3) (e_x E)) (Z.to_nat p3) eq_refl).
  f_equal. unfold p5. lia.
- unfold p5. lia.
- exact HBK.
Qed.

(* phase 3 (B 0x83b78): ex_string read the name s; the key compare when there is a node *)
Lemma a2_ph3 : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p3 (z s rest : list Z),
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p3 dlc -> getr regs 10 = w64 0 -> getr regs 24 = w64 fl ->
  getr regs 21 = w64 (-1) ->
  PjGrammar.skip (skipn (Z.to_nat ip) (e_x E)) = 34 :: z -> exv_run0 (PjGrammar.jr_string z) = Some (s, rest) ->
  rest = skipn (Z.to_nat p3) (e_x E) -> ip <= p3 ->
  bytes_at Wc memc (e_scr E) (s ++ [0]) -> (length z <= length (e_x E))%nat ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_S regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p3 z s rest HST H10 H24 H21 Hsk Hjs Hrest Hip3 HBY Hzl.
destruct (a2_jr_string z s rest Hjs) as (HSNZ & HSL).
assert (Hlen : exv_len E = Z.of_nat (length (e_x E))) by reflexivity.
pose proof Hfl as Hfl'.
destruct Hfl' as [(Hk0 & Hf1) | (Hf0 & Hvv & Htag & Hv0 & Hic & Htk & Hkr & Hkd & Hkn0)].
- (* no node: straight to the second ex_ws *)
  rewrite Hf1 in H24.
  apply (a2_run3b lyc Sc Hpc Wc regs memc mdc k pos p3 dlc _ HST H10 H24).
  intros regs' mem' md' HRP R10 R1.
  pose proof HRP as (_ & _ & _ & HRR).
  pose proof (a2_st_run0 lyc Sc Hpc Wc regs memc mdc k pos p3 dlc regs' mem' md' _ HST HRP ltac:(a2_incl)) as HST'.
  apply (a2_ph4 lyc Sc Hpc Wc regs' mem' md' k pos p3 dlc z s rest HST' R10 R1
    ltac:(rewrite HRR by a2_inl; exact H21) Hsk Hjs Hrest Hip3).
  intros u dl' Hd Hiff. apply Hdif; [exact Hd|]. rewrite Hiff. rewrite Hk0.
  split; intros [H | (H & _)]; [left; exact H | exfalso; exact (H eq_refl) | left; exact H | exfalso; exact (H eq_refl)].
- (* a node: the key compare *)
  rewrite Hf0 in H24.
  destruct (a2_obj_tag _ Htag) as (ms & Et).
  pose proof HST as (HBs & _).
  destruct HBs as (regs0 & HB0 & _).
  destruct (NODE E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB0 Hv0) as (N1 & N2 & N3 & N4 & N5).
  assert (Hims : (i < length ms)%nat) by (rewrite Et in Hic; exact Hic).
  destruct (KEY E lyc Sc Hpc Wc regs0 memc mdc k pos ms i HP HB0 Hv0 Et Hims) as (keys & x0 & kk0 & VK & Hkr0 & _).
  apply (a2_run3c lyc Sc Hpc Wc regs memc mdc k pos p3 dlc keys _ HST H10 H24 Hvv N1 N2 N3 N4
    (fun z Hz => conj (proj1 (N5 z Hz)) (proj1 (proj2 (N5 z Hz)))) VK Hkr0).
  intros regs1 mem1 md1 HRP1 R11.
  pose proof HRP1 as (_ & KEPT1 & _ & HRR1).
  pose proof (a2_st_run0 lyc Sc Hpc Wc regs memc mdc k pos p3 dlc regs1 mem1 md1 _ HST HRP1 ltac:(a2_incl)) as HST1.
  pose proof HST1 as (HBs1 & _).
  destruct HBs1 as (regs1' & HB1 & _).
  destruct (KEY E lyc Sc Hpc Wc regs1' mem1 md1 k pos ms i HP HB1 Hv0 Et Hims)
    as (keys' & x & kk & VK' & Hkr' & K8 & K4 & Kce & Kra & Kband & VX & Hxr & Hxin & X1 & X2 & Hxk & Hxb).
  assert (Hkk : keys' = keys).
  { apply (exvl_val8_det (mrestrict (w_H Wc) mem1) (e_v E + 32) keys' keys VK'); [|exact Hkr' | exact Hkr0].
    apply (exw_val_kept rsegs (w_H Wc) memc mem1); [|exact VK]. intros a Ha. change (Z.of_nat 8) with 8 in Ha.
    apply KEPT1; [lia | intros []]. }
  subst keys'.
  destruct (SCR E lyc Sc Hpc Wc regs1' mem1 md1 k pos HP HB1) as (SC1 & SC2).
  pose proof asan_consts as (C1 & _).
  apply (a2_run3d lyc Sc Hpc Wc regs1 mem1 md1 k pos p3 dlc keys x _ HST1 R11 K8 K4 ltac:(clear - Kce Hims; lia)
    Kra Kband VX Hxr ltac:(lia)).
  intros regs2 mem2 md2 HRP2 R10x R11s R1c.
  pose proof HRP2 as (_ & KEPT2 & _ & HRR2).
  pose proof (a2_st_run0 lyc Sc Hpc Wc regs1 mem1 md1 k pos p3 dlc regs2 mem2 md2 _ HST1 HRP2 ltac:(a2_incl)) as HST2.
  pose proof HST2 as (HBs2 & _).
  destruct Hxb as (HxF & HxG).
  assert (HxG2 : garr8 rsegs (mrestrict (w_H Wc) mem2) x (fst (nth i ms ([], PjTree.JNull)) ++ [0])).
  { apply (GARRK (w_H Wc) (w_H Wc) mem1 mem2); [|exact HxG]. intros a Ha. rewrite length_app in Ha.
    cbn [length] in Ha. apply KEPT2; [lia | intros []]. }
  assert (HSB2 : garr8 rsegs (mrestrict (w_H Wc) mem2) (e_scr E) (s ++ [0])).
  { apply (GARRK (w_H Wc) (w_H Wc) mem1 mem2); [|apply (GARRK (w_H Wc) (w_H Wc) memc mem1); [|exact HBY]].
    - intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEPT2; [lia | intros []].
    - intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply KEPT1; [lia | intros []]. }
  pose proof a2_pc_vals as (PW1 & PS & PC & PW2).
  apply (CALLCMP E lyc Sc Hpc Wc regs2 mem2 md2 k pos x A2_C kk (fst (nth i ms ([], PjTree.JNull))) s _ HP HBs2 R10x
    R11s R1c ltac:(vm_compute; reflexivity) Hxin Hxk (conj HxF HxG2) HSB2 HSNZ ltac:(lia)).
  intros regs3 mem3 md3 v HBs3 HPR3 Hfr3 R10v Hv.
  destruct (a2_seat lyc Sc Hpc Wc regs2 mem2 md2 k pos p3 dlc HST2)
    as (r0 & _ & _ & _ & _ & _ & _ & B1 & B2 & B3 & B4 & B5 & B6 & _).
  pose proof (GEOM E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB0)
    as (_ & _ & _ & _ & _ & _ & _ & (G8a & G8b) & _ & _ & _ & _ & G13 & _).
  assert (HST3 : a2_st lyc Sc Hpc Wc regs3 mem3 md3 k pos p3 dlc).
  { pose proof HST2 as (_ & _ & _ & _ & _ & _ & HCUR2 & Hpr2 & _).
    destruct HCUR2 as (Vp2 & _).
    apply (a2_st_move lyc Sc Hpc Wc regs2 mem2 md2 k pos p3 dlc lyc Sc Hpc Wc regs3 mem3 md3 k p3 HST2 HBs3).
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]].
      + a2_prese HPR3 20.
      + a2_prese HPR3 22.
      + a2_prese HPR3 23.
      + a2_prese HPR3 27.
    - reflexivity.
    - intros a Ha. apply Hfr3; lia.
    - intros a Ha. apply Hfr3; lia.
    - intros _ a Ha. pose proof (N5 a ltac:(lia)) as (_ & Hw & _). apply Hfr3; lia.
    - apply (YC88.val_mem_aview_kept_x rsegs (w_H Wc) (w_H Wc) mem2 mem3); [|exact Vp2].
      intros a Ha. change (Z.of_nat 8) with 8 in Ha. apply Hfr3; lia.
    - exact Hpr2. }
  assert (H21c : getr regs3 21 = w64 (-1)).
  { match goal with |- getr _ ?r = _ =>
      rewrite (a2_pres regs2 regs3 r 21 HPR3 ltac:(unfold acallee_saved; lia) eq_refl) end.
    rewrite HRR2 by a2_inl. rewrite HRR1 by a2_inl. exact H21. }
  destruct (a2_w64_dec v) as [-> | Hv1].
  + (* the key is the name *)
    assert (Hks : fst (nth i ms ([], PjTree.JNull)) = s) by (apply Hv; reflexivity).
    apply (a2_run4a lyc Sc Hpc Wc regs3 mem3 md3 k pos p3 dlc _ HST3 R10v).
    intros regs4 mem4 md4 HRP4 R10 R1.
    pose proof HRP4 as (_ & _ & _ & HRR4).
    pose proof (a2_st_run0 lyc Sc Hpc Wc regs3 mem3 md3 k pos p3 dlc regs4 mem4 md4 _ HST3 HRP4 ltac:(a2_incl)) as HST4.
    apply (a2_ph4 lyc Sc Hpc Wc regs4 mem4 md4 k pos p3 dlc z s rest HST4 R10 R1
      ltac:(rewrite HRR4 by a2_inl; exact H21c) Hsk Hjs Hrest Hip3).
    intros u dl' Hd Hiff. apply Hdif; [exact Hd|]. rewrite Hiff. rewrite Et. rewrite Et in Htk.
    rewrite (a2_same_iff ms i s u Hks). rewrite <- Htk. tauto.
  + (* the key differs: in->differs := 1 *)
    assert (Hks : fst (nth i ms ([], PjTree.JNull)) <> s) by (intros H; apply Hv1; apply Hv; exact H).
    apply (a2_run4b lyc Sc Hpc Wc regs3 mem3 md3 k pos p3 dlc v _ HST3 R10v Hv1).
    intros regs4 mem4 md4 HRP4 Vl4 R10 R1.
    pose proof HRP4 as (_ & KEPT4 & _ & HRR4).
    pose proof HST3 as (_ & _ & _ & _ & _ & _ & HCUR3 & Hpr3 & _).
    destruct HCUR3 as (Vp3 & _).
    assert (HST4 : a2_st lyc Sc Hpc Wc regs4 mem4 md4 k pos p3 1).
    { apply (a2_runpost_st lyc Sc Hpc Wc regs3 mem3 md3 k pos p3 dlc regs4 mem4 md4 _ _ p3 1 HST3 HRP4
        ltac:(a2_incl)).
      - intros a Ha. right. exact Ha.
      - apply (exw_val_kept rsegs (w_H Wc) mem3 mem4); [|exact Vp3]. intros a Ha. change (Z.of_nat 8) with 8 in Ha.
        apply KEPT4; [lia | cbv beta; lia].
      - exact Vl4.
      - exact Hpr3.
      - right. reflexivity. }
    apply (a2_ph4 lyc Sc Hpc Wc regs4 mem4 md4 k pos p3 1 z s rest HST4 R10 R1
      ltac:(rewrite HRR4 by a2_inl; exact H21c) Hsk Hjs Hrest Hip3).
    intros u dl' Hd Hiff. apply Hdif; [exact Hd|].
    assert (HR : dl' = 1) by (apply Hiff; left; reflexivity).
    split; intros _; [|exact HR].
    right. split; [exact Hkn0|]. intros Hs. apply Hks. rewrite Et in Hs. exact (a2_same_fst ms i s u Hs).
Qed.

(* phase 2 (B 0x83b2c): after the first ex_ws: the opening quote (34) and ex_string, or CX *)
Lemma a2_ph2 : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos p2,
  a2_st lyc Sc Hpc Wc regs memc mdc k pos p2 dlc -> getr regs 24 = w64 fl ->
  skipn (Z.to_nat p2) (e_x E) = PjGrammar.skip (skipn (Z.to_nat ip) (e_x E)) -> ip <= p2 ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_W1 regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos p2 HST H24 Hp2 Hip2.
pose proof HST as (_ & _ & _ & _ & _ & _ & _ & Hpr & Hdlr & _).
assert (Hlen : exv_len E = Z.of_nat (length (e_x E))) by reflexivity.
destruct (Z_lt_le_dec p2 (exv_len E)) as [Hlt | Hge].
- destruct (PjGrammar.skip (skipn (Z.to_nat ip) (e_x E))) as [|b z] eqn:Hsk.
  { exfalso. apply (f_equal (@length Z)) in Hp2. rewrite length_skipn in Hp2. cbn [length] in Hp2. lia. }
  pose proof (a2_nth_skipn _ _ _ _ Hp2) as Hb.
  pose proof (a2_skipn_S _ _ _ _ Hp2) as Hz.
  destruct (Z.eq_dec b 34) as [-> | Hb34].
  + apply (a2_run2c lyc Sc Hpc Wc regs memc mdc k pos p2 dlc _ HST Hlt Hb).
    intros regs1 mem1 md1 HRP1 R10 R1 R21 VQ.
    pose proof HRP1 as (_ & _ & _ & HRR1).
    pose proof (a2_st_runq lyc Sc Hpc Wc regs memc mdc k pos p2 dlc regs1 mem1 md1 _ p2 HST HRP1 ltac:(a2_incl) VQ
      ltac:(lia)) as HST1.
    pose proof HST1 as (HBs1 & _ & _ & _ & _ & _ & HCUR1 & _).
    destruct HCUR1 as (Vp1 & Ve1 & _ & Vs1 & _).
    pose proof a2_pc_vals as (PW1 & PS & PC & PW2).
    apply (CALLSTR E lyc Sc Hpc Wc regs1 mem1 md1 k pos p2 A2_S _ HP HBs1 R10 R1 ltac:(vm_compute; reflexivity)
      ltac:(rewrite PS; lia) Vp1 Ve1 Vs1 ltac:(lia)).
    intros ly2 S2 Hpz W2 regs2 mem2 md2 k1 HBs2 HPR HWIN HNODE HM.
    rewrite Hz in HM.
    assert (Hzl : (length z <= length (e_x E))%nat) by (rewrite <- Hz, length_skipn; lia).
    assert (Hzlen : length z = (length (e_x E) - S (Z.to_nat p2))%nat) by (rewrite <- Hz, length_skipn; reflexivity).
    assert (H21' : getr regs2 21 = w64 (-1))
      by (a2_presr HPR 21; exact R21).
    destruct (exv_run0 (PjGrammar.jr_string z)) as [[s rest]|] eqn:Hjs.
    * destruct HM as (R10' & (c & Hsc & Hrest & Vq2) & HBY).
      pose proof (a2_scan_lt (length z) z c (le_n _) Hsc) as Hcl.
      apply (a2_ph3 ly2 S2 Hpz W2 regs2 mem2 md2 (k + k1) pos (p2 + Z.of_nat c + 2) z s rest).
      -- apply (a2_st_call lyc Sc Hpc Wc regs1 mem1 md1 k pos p2 dlc ly2 S2 Hpz W2 regs2 mem2 md2 (k + k1)
           (p2 + Z.of_nat c + 2) HST1 HBs2 HPR HWIN HNODE); [|lia].
         replace (e_x0 E + (p2 + Z.of_nat c + 2)) with (e_x0 E + p2 + Z.of_nat c + 2) by lia. exact Vq2.
      -- exact R10'.
      -- match goal with |- getr _ ?r = _ =>
           rewrite (a2_pres regs1 regs2 r 24 HPR ltac:(unfold acallee_saved; lia) eq_refl) end.
         rewrite HRR1 by a2_inl. exact H24.
      -- exact H21'.
      -- exact Hsk.
      -- exact Hjs.
      -- rewrite Hrest, <- Hz, a2_skipn_skipn. f_equal. lia.
      -- lia.
      -- exact HBY.
      -- exact Hzl.
    * destruct HM as (R10' & Vq2).
      pose proof (a2_st_call lyc Sc Hpc Wc regs1 mem1 md1 k pos p2 dlc ly2 S2 Hpz W2 regs2 mem2 md2 (k + k1) p2 HST1
        HBs2 HPR HWIN HNODE Vq2 ltac:(lia)) as HST2.
      apply (a2_run3a ly2 S2 Hpz W2 regs2 mem2 md2 (k + k1) pos p2 dlc _ HST2 R10').
      intros regs3 mem3 md3 HRP3 R24'.
      pose proof HRP3 as (_ & _ & _ & HRR3).
      pose proof (a2_st_run0 ly2 S2 Hpz W2 regs2 mem2 md2 (k + k1) pos p2 dlc regs3 mem3 md3 _ HST2 HRP3
        ltac:(a2_incl)) as HST3.
      apply (a2_cx_st ly2 S2 Hpz W2 regs3 mem3 md3 (k + k1) pos p2 dlc HST3 R24');
        [rewrite HRR3 by a2_inl; exact H21'|].
      unfold exv_name. rewrite Hsk. cbv beta iota. change (34 =? 34) with true. cbv beta iota. rewrite Hjs.
      reflexivity.
  + apply (a2_run2b lyc Sc Hpc Wc regs memc mdc k pos p2 dlc _ HST Hlt ltac:(rewrite Hb; exact Hb34)).
    intros regs1 mem1 md1 HRP1 R24 R21 VQ.
    pose proof (a2_st_runq lyc Sc Hpc Wc regs memc mdc k pos p2 dlc regs1 mem1 md1 _ p2 HST HRP1 ltac:(a2_incl) VQ
      ltac:(lia)) as HST1.
    apply (a2_cx_st lyc Sc Hpc Wc regs1 mem1 md1 k pos p2 dlc HST1 R24 R21).
    unfold exv_name. rewrite Hsk. cbv beta iota. rewrite (proj2 (Z.eqb_neq b 34) Hb34). reflexivity.
- assert (Hsk : PjGrammar.skip (skipn (Z.to_nat ip) (e_x E)) = []) by (rewrite <- Hp2; apply skipn_all2; lia).
  apply (a2_run2a lyc Sc Hpc Wc regs memc mdc k pos p2 dlc _ HST Hge).
  intros regs1 mem1 md1 HRP1 R24 R21 VQ.
  pose proof (a2_st_runq lyc Sc Hpc Wc regs memc mdc k pos p2 dlc regs1 mem1 md1 _ p2 HST HRP1 ltac:(a2_incl) VQ Hpr)
    as HST1.
  apply (a2_cx_st lyc Sc Hpc Wc regs1 mem1 md1 k pos p2 dlc HST1 R24 R21).
  unfold exv_name. rewrite Hsk. reflexivity.
Qed.

(* the object arm from LK (B 0x83b1c): the first ex_ws, then phase 2 *)
Lemma a2_obj : forall lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos,
  a2_st lyc Sc Hpc Wc regs memc mdc k pos ip dlc -> getr regs 24 = w64 fl ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_LK regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros lyc Sc Hpc Wc regs memc mdc k pos HST H24.
assert (Hlen : exv_len E = Z.of_nat (length (e_x E))) by reflexivity.
apply (a2_run1 lyc Sc Hpc Wc regs memc mdc k pos ip dlc _ HST).
intros regs1 mem1 md1 HRP1 R10 R1.
pose proof HRP1 as (_ & _ & _ & HRR1).
pose proof (a2_st_run0 lyc Sc Hpc Wc regs memc mdc k pos ip dlc regs1 mem1 md1 _ HST HRP1 ltac:(a2_incl)) as HST1.
pose proof HST1 as (HBs1 & _ & _ & _ & _ & _ & HCUR1 & _).
destruct HCUR1 as (Vp1 & Ve1 & _).
pose proof a2_pc_vals as (PW1 & PS & PC & PW2).
apply (CALLWS E lyc Sc Hpc Wc regs1 mem1 md1 k pos ip A2_W1 _ HP HBs1 R10 R1 ltac:(vm_compute; reflexivity)
  ltac:(rewrite PW1; lia) Vp1 Ve1 Hip).
intros ly2 S2 Hpz W2 regs2 mem2 md2 k1 HBs2 HPR HWIN HNODE Vq2.
pose proof (a2_skip_len (skipn (Z.to_nat ip) (e_x E))) as HL. rewrite length_skipn in HL.
set (p2 := exv_len E - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat ip) (e_x E))))).
apply (a2_ph2 ly2 S2 Hpz W2 regs2 mem2 md2 (k + k1) pos p2).
- apply (a2_st_call lyc Sc Hpc Wc regs1 mem1 md1 k pos ip dlc ly2 S2 Hpz W2 regs2 mem2 md2 (k + k1) p2 HST1 HBs2 HPR
    HWIN HNODE).
  + replace (e_x0 E + p2) with (e_x0 E + exv_len E - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat ip) (e_x E)))))
      by (unfold p2; lia). exact Vq2.
  + unfold p2. lia.
- match goal with |- getr _ ?r = _ =>
    rewrite (a2_pres regs1 regs2 r 24 HPR ltac:(unfold acallee_saved; lia) eq_refl) end.
  rewrite HRR1 by a2_inl. exact H24.
- rewrite <- (a2_skip_pos PSUF (e_x E) (skipn (Z.to_nat ip) (e_x E)) (Z.to_nat ip) eq_refl).
  f_equal. unfold p2. lia.
- unfold p2. lia.
Qed.

(* R0 (B 0x83b1c -> 0x83c8c): an array item (s11 = '['), straight to LR. Stated for any Ex: it takes only the kits. *)
Lemma a2_run0 : forall Ex lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos (Q : world rsegs -> config -> Prop),
  EXV_PRE B ARx Ex -> EXBs (fx := fx) B ARx SK Ex lyc Sc Hpc Wc regs memc mdc k pos -> getr regs 27 = w64 91 ->
  (forall (regs' : bvmap 5 word) mem' md',
     ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK Ex + e_d Ex) (exv_sp Ex + e_d Ex) (exv_FP Ex) (e_ly Ex)
       (e_S Ex) (e_Hp Ex) (e_W Ex) (e_mem Ex) (e_md Ex) [(1, pos)] lyc Sc Hpc Wc mem' md' k ->
     exvl_P (e_mem Ex) mem' ->
     (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H Wc) mem' a = aview rsegs (w_H Wc) memc a) ->
     (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) mem' a) ->
     (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_LR regs' mem' md') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_LK regs memc mdc) Q.
Proof using B ARx SK HYP KCALL KRUN KCH KROD KWD ci.
clear HX HLR Hn HP Hi1 Hc Hdep Hacc Hip Hii Hm HV Hfl Hdif KOFS PLS PSUF.
clear n m E i cap acc ip vv dlc kid fl kids tk.
intros Ex lyc Sc Hpc Wc regs memc mdc k pos Q HPx HBs H27 HK.
destruct (EXBSREG Ex lyc Sc Hpc Wc regs memc mdc k pos HBs)
  as (regs0 & HB & R2 & R8 & R9 & R3 & R4 & R19 & R25 & R18 & R26 & Hrr).
pose proof (GEOM Ex lyc Sc Hpc Wc regs0 memc mdc k pos HPx HB)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & (G8a & G8b) & G9 & G10 & G11 & G12 & G13 & _).
pose proof asan_consts as (C1 & _).
remember (Ereg regs []) as E0 eqn:HE0.
assert (E2 : ew E0 2 = Z_to_bv 64 (exv_s1 Ex)) by (subst E0; exact (a2_ew_reg regs _ 2 2%bv _ eq_refl R2)).
assert (E9 : ew E0 9 = Z_to_bv 64 (exv_s1 Ex)) by (subst E0; exact (a2_ew_reg regs _ 9 9%bv _ eq_refl R9)).
assert (E19 : ew E0 19 = Z_to_bv 64 (e_q Ex)) by (subst E0; exact (a2_ew_reg regs _ 19 19%bv _ eq_refl R19)).
assert (E25 : ew E0 25 = Z_to_bv 64 SHADOW_OFF) by (subst E0; exact (a2_ew_reg regs _ 25 25%bv _ eq_refl R25)).
assert (E27 : ew E0 27 = Z_to_bv 64 91) by (subst E0; exact (a2_ew_reg regs _ 27 27%bv _ eq_refl H27)).
assert (U2 : bv_unsigned (ew E0 2) = exv_s1 Ex) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E0 9) = exv_s1 Ex) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E0 19) = e_q Ex) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E0 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E0 27) = 91) by (rewrite E27; reflexivity).
assert (HS : st_ok rsegs E0 ss_a2_r0 (restrict (w_H Wc) (mkst regs (Z_to_bv 64 A2_LK) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_a2_r0. apply exw_st_ok_full.
  - subst E0. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok a2_fb]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U27, U2, U9, U19, U25. change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok rsegs A2_SB [] E0 (mrestrict (w_H Wc) memc)) by constructor.
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'. destruct HB' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose proof (RUNTO_T (e_mem Ex)) as RUNTO.
assert (HSTK0 : 0 <= exv_STK Ex) by (unfold exv_STK; rewrite a2_stk; lia).
unfold cfg_at. change (w64 A2_LK) with (Z_to_bv 64 A2_LK).
exw_run_to RUNTO HS HJ SHOK HPM A2_LR.
{ a2_awr U19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => cbn [ew ewset Nat.eqb] in h).
a2_agree HS E0 HE0 (Ereg regs []).
pmkst HS.
apply HK; [exact HJ | exact HPM | | |].
- intros a Ha. apply KEPT; [exact Ha | intros []].
- intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
- intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ match goal with |- getr _ ?rr = _ =>
        exact (regs_kept_of_st_ok rsegs _ _ _ _ _ [rr] HS AG ltac:(vm_compute; reflexivity) rr (or_introl eq_refl))
      end |]).
  destruct Hr.
Qed.
End w.
