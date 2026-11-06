(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first half of a round of the split loop of LLVMFuzzerTestOneInput's inlined words_of (plugin-hostd/fuzz_command, 0x86850 .. 0x868a4: the strspn wrapper call, the exit when only separators are left, the 8-byte check and the store of the word's address, the strcspn wrapper call), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (a symbolic seed at a point of the function and the runs from it) and A/ACh2.v:122-290 (a call and back, with the facts carried over it); the two wrapper call steps aj_strspn_at_loc and aj_strcspn_at_loc are lib/A/Prog/check_words_art.v's aj_strspn_at and aj_strcspn_at (PaArt.v's aj_art_at), with the guard cells from CmdRecFacts' cmd_rec_cells. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaArt PaSB CmdGlob PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01 LLVMFuzzerTestOneInput_s40
LLVMFuzzerTestOneInput_s49.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the seats of the two stretches (listing offsets from BASE = 0x864e4) ---- *)
(* 0x86864: the strspn wrapper has returned; the run to the strcspn wrapper starts here *)
Definition WS_B : Z := 0x380.
(* s1 holds the shadow base all through the loop *)
Definition WSx : sv := SOff 9 0.
Definition WSspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the registers neither stretch nor the wrapper calls change, which the segment statements name *)
Definition WS_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 22; 23; 24; 25]%bv.
(* 0x86850 .. jal strspn: no memory access *)
Definition ws_atomsA : list (nat * afact) := [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF SB SB 0) ].
(* 0x86864 .. jal strcspn: s11 + a0 is the cursor past the separators (atom 32), its byte is atom 33; the 8-byte
   check reads the shadow of s2 and the store writes s10, both arr + 8 kw *)
Definition ws_aliasB : list (sv * sv) := [ (SAlu ALU_ADD (SOff 27 0) (SOff 10 0), SOff 32 0) ].
Definition ws_atomsB : list (nat * afact) := [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF SB SB 0);
  (18%nat, PTR 3); (26%nat, PTR 3); (27%nat, PTR 0); (32%nat, PTR 0); (33%nat, mkAF 0 255 0) ].
Definition ws_rB : smem := [ YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
  YP09.mkRegion (Some 26%nat) 0 8 0 8 [] ].
Definition ws_shB : list shent := [ mkSHE 18 0 8; mkSHE 26 0 8 ].

(* ---- small facts ---- *)
Lemma ws_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma ws_aval1 : forall (rd : reader) a v, rd a = Some v -> 0 <= v < 256 -> aval_mem rd a 1 v.
Proof.
intros rd a v H Hv k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r, H. f_equal.
unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small v (2 ^ 8)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ws_rdword_kept : forall (rd rd' : reader) a v, (forall x, a <= x < a + 8 -> rd' x = rd x) ->
  rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. unfold rdword in *. rewrite !HK by lia. exact H. Qed.
Lemma ws_nodup_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l2 -> ~ In x l1.
Proof.
intros A l1. induction l1 as [|y l1 IH]; intros l2 x H Hx Hin; [destruct Hin|].
cbn [app] in H. apply NoDup_cons_iff in H as [Hy H]. destruct Hin as [<-|Hin].
- apply Hy. apply in_or_app. right. exact Hx.
- exact (IH l2 x H Hx Hin).
Qed.
Lemma ws_mod8 : forall a k, a mod 16 = 0 -> (a + 8 * k) mod 2 ^ 3 = 0.
Proof.
intros a k H. change (2 ^ 3) with 8. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia].
destruct H as [c Hc]. exists (2 * c + k). lia.
Qed.
(* the 8-byte pointer slots: the ones already there, then one more *)
Lemma ws_arr_kept : forall (rd rd' : reader) arr wp, (forall x, arr <= x < arr + 8 * Z.of_nat (length wp) -> rd' x = rd x) ->
  aw_arr rd arr wp -> aw_arr rd' arr wp.
Proof.
intros rd rd' arr wp HK H t p Ht. assert (Hl : (t < length wp)%nat) by (apply nth_error_Some; rewrite Ht; discriminate).
apply (ws_rdword_kept rd rd'); [intros x Hx; apply HK; lia | exact (H t p Ht)].
Qed.
Lemma ws_arr_snoc : forall (rd : reader) arr wp p, aw_arr rd arr wp ->
  rdword rd (arr + 8 * Z.of_nat (length wp)) = Some p -> aw_arr rd arr (wp ++ [p]).
Proof.
intros rd arr wp p H Hp t p' Ht. destruct (Nat.lt_ge_cases t (length wp)) as [L|L].
- rewrite nth_error_app1 in Ht by exact L. exact (H t p' Ht).
- rewrite nth_error_app2 in Ht by exact L. destruct (t - length wp)%nat as [|u] eqn:Eu.
  + cbn in Ht. injection Ht as <-. replace t with (length wp) by lia. exact Hp.
  + cbn in Ht. destruct u; discriminate.
Qed.
Lemma ws_found_mono : forall copy ws C wp i j, aw_found copy ws C wp i -> (i <= j)%nat -> aw_found copy ws C wp j.
Proof.
intros copy ws C wp i j H Hij k' p w Ep Ew. destruct (H k' p w Ep Ew) as (H1 & H2 & H3).
split; [exact H1|]. split; [lia | exact H3].
Qed.
(* the bytes of the line from the cursor on, NUL included, where the copy buffer holds them *)
Lemma ws_tail_bytes : forall (rd : reader) copy (C L : list byte) j,
  abytes_atR rd copy C -> (j <= length L)%nat -> (length L + 1 <= length C)%nat ->
  (forall t, (j <= t <= length L)%nat -> nth_error C t = nth_error (L ++ [Z_to_bv 8 0]) t) ->
  abytes_atR rd (copy + Z.of_nat j) (skipn j L ++ [Z_to_bv 8 0]).
Proof.
intros rd copy C L j H Hj HC HF t Ht. rewrite length_app, length_skipn in Ht. cbn [length] in Ht.
replace (copy + Z.of_nat j + Z.of_nat t) with (copy + Z.of_nat (j + t)) by lia.
rewrite (H (j + t)%nat) by lia. f_equal. f_equal.
assert (E1 : nth_error C (j + t) = nth_error (skipn j L ++ [Z_to_bv 8 0]) t).
{ rewrite (HF (j + t)%nat) by lia. rewrite <- SlotWords.sw_skipn_app0 by exact Hj. rewrite SlotWords.sw_nth_skipn. reflexivity. }
destruct (nth_error (skipn j L ++ [Z_to_bv 8 0]) t) as [b|] eqn:Eb.
- rewrite (nth_error_nth _ _ _ E1), (nth_error_nth _ _ _ Eb). reflexivity.
- apply nth_error_None in Eb. rewrite length_app, length_skipn in Eb. cbn [length] in Eb. lia.
Qed.
(* the sum of two register atoms *)
Lemma ws_add_atoms : forall E (n1 n2 : nat) v1 v2,
  ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 -> 0 <= v1 -> 0 <= v2 -> v1 + v2 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (v1 + v2).
Proof.
intros E n1 n2 v1 v2 H1 H2 Hv1 Hv2 Hs.
rewrite (denot_lit_U E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0))). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n1 v1 H1 ltac:(lia)), (U_atom E n2 v2 H2 ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma ws_afact : forall E n v lo hi al, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof.
intros E n v lo hi al Hn Hv Hl Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hn, unsigned_lit_small by lia. auto.
Qed.
(* reading a callee-saved register out of aregs_preserved *)
Lemma ws_pres_get : forall (regs regs' : bvmap 5 word) (r : Z) (rr : bv 5),
  aregs_preserved regs regs' -> acallee_saved r -> Z_to_bv 5 r = rr -> getr regs' rr = getr regs rr.
Proof. intros regs regs' r rr HP Hr <-. exact (HP r Hr). Qed.
Lemma ws_pres_keep : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r, In r WS_KEEP -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr.
assert (Hc : acallee_saved (bv_unsigned r)).
{ cbn [WS_KEEP In] in Hr. unfold acallee_saved.
  repeat (destruct Hr as [Hr | Hr];
    [ subst r; lazymatch goal with |- context [bv_unsigned ?rr] =>
        let z := eval vm_compute in (bv_unsigned rr) in change (bv_unsigned rr) with z end; lia |]).
  destruct Hr. }
rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hc).
Qed.
(* a register the wrapper preserved, read through the run's register equation and the seat's atom *)
Ltac ws_reg HP z P Ez :=
  etransitivity; [exact (ws_pres_get _ _ z _ HP ltac:(unfold acallee_saved; lia) eq_refl)|];
  etransitivity; [exact P|]; rewrite Ez; reflexivity.

Ltac ws_inkeep := cbn [WS_KEEP In]; repeat (first [left; reflexivity | right]).
Ltac ws_agree HAE :=
  split;
  [ let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; cbn [ew ewset];
    repeat match goal with |- context [Nat.eqb n ?K] => destruct (Nat.eqb_spec n K); [lia|] end;
    apply (proj1 HAE); exact Hn
  | cbn [ed ewset]; exact (proj2 HAE) ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma ws_not_shadow : forall p n x, in_app p n -> p <= x < p + n -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof. intros p n x Ha Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. Qed.

(* ---- the fresh symbolic seat of a stretch: every register its own atom, atoms 32.. given ---- *)
Definition ws_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs extra).
Lemma ws_E_reg : forall regs extra n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (ws_E regs extra) n = getr regs rr.
Proof.
intros regs extra n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold ws_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma ws_E_extra : forall regs extra j, (j < 8)%nat -> ew (ws_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. unfold ws_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma ws_E_img : forall regs extra, img_env VAL A_LIM (ws_E regs extra).
Proof. intros regs extra. unfold ws_E. apply Eimg_env. Qed.
Lemma ws_E_agree : forall regs extra, env_agree 32 (Ereg regs extra) (ws_E regs extra).
Proof. intros regs extra. split; [intros n Hn; unfold ws_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.
Lemma ws_seat : forall (W : world SEGS) (regs : bvmap 5 word) mem pc extra rs ats al,
  regions_wf rs = true ->
  Forall (region_ok SEGS (ws_E regs extra) (mrestrict (w_H W) mem)) rs ->
  pairwise_disjoint (ws_E regs extra) rs ->
  atoms_ok (ws_E regs extra) ats -> alias_ok (ws_E regs extra) al ->
  st_ok_pi SEGS VAL (ws_E regs extra) (mkSS pc sr_atoms rs None (mkFacts ats [] al))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc extra rs ats al Hwf Hrs Hpd Hat Hal.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold ws_E. apply regs_ok_Eimg_Ereg.
- exact Hwf.
- exact Hrs.
- exact Hpd.
- split; [exact Hat | split; [exact I | exact Hal]].
Qed.
(* the image object the code names by an auipc pair, as its atom holds it *)
Lemma ws_ew_obj : forall E i v, cmd_val_objs -> img_env VAL A_LIM E -> (i < length cmd_objs)%nat ->
  nth i cmd_objs 0 = v -> (A_OBJ i < A_LIM)%nat -> ew E (A_OBJ i) = Z_to_bv 64 v.
Proof.
intros E i v HO HE Hi Hv Hl. pose proof (HE (A_OBJ i) ltac:(unfold A_OBJ, A_TEXT in *; lia)) as H.
rewrite (HO i Hi), Hv in H. pose proof (pa_val_range (A_OBJ i)) as R. rewrite (HO i Hi), Hv in R.
apply bv_eq. rewrite H. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
(* the regions of a seat *)
Lemma ws_rg_byte : forall E (W : world SEGS) mem (n bn : nat) x v,
  ew E n = Z_to_bv 64 x -> ew E bn = Z_to_bv 64 v -> 0 <= x -> x + 1 <= 2 ^ 64 -> 0 <= v < 256 ->
  rdW W mem x = Some v ->
  region_ok SEGS E (mrestrict (w_H W) mem) (YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff bn 0))]).
Proof.
intros E W mem n bn x v Hn Hb Hx0 Hx1 Hv Hrd. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hn, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ x 0 1 (SOff bn 0) v);
  [cbn [sv_denot]; rewrite Hb, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
rewrite Z.add_0_r. apply val_mem_of_aval. exact (ws_aval1 _ x v Hrd Hv).
Qed.
Lemma ws_rg_slot : forall E (W : world SEGS) mem (n : nat) x,
  ew E n = Z_to_bv 64 x -> 0 <= x -> x + 8 <= 2 ^ 64 -> (forall a, x <= a < x + 8 -> apresent (w_H W) mem a) ->
  region_ok SEGS E (mrestrict (w_H W) mem) (YP09.mkRegion (Some n) 0 8 0 8 []).
Proof.
intros E W mem n x Hn Hx0 Hx1 Hp. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hn, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hp. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the runtime entries this stretch calls: the statement's own hypotheses, word for word
   (LLVMFuzzerTestOneInput_c.v) *)
Hypothesis ASTRSPN : astrspn_realizes SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : astrcspn_realizes SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
(* the per-binary facts, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the two wrapper calls (check_words_art.v) ---- *)
Lemma aj_strspn_at_loc : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  astr_at SEGS W memT x sx -> astr_at SEGS W memT y sy ->
  aread_ok SEGS (2 * ESTACK) W regsT memT x (astr_len sx + 1) ->
  aread_ok SEGS (2 * ESTACK) W regsT memT y (astr_len sy + 1) ->
  amem_range x (astr_len sx + 8) -> amem_range y (astr_len sy + 8) ->
  atail_vis SEGS W memT (x + astr_len sx) -> atail_vis SEGS W memT (y + astr_len sy) ->
  rt_rom_view SEGS B W memT ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_strspn)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
  aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (PSpn.spn_len sy sx)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> ~ False ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy o raw
HJ Ha0 Ha1 Hx Hy Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hrx Hry Hmx Hmy Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (proj1 (proj2 (cmd_rec_cells SEGS B LAWS HB IMG lyc Sc W memT mdc (proj1 HJ)))) as HG.
apply (aj_art_at SEGS B LAWS pa_segs_low (cmd_cf_env SEGS B LAWS HB IMG) (2 * ESTACK) (fun _ => False) _ W regsT memT
STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw (fun regs2 _ => getr regs2 10 = w64 (Z.of_nat (PSpn.spn_len sy sx)))
HJ Hsp Hal Hneg ltac:(lia) Hbud Hra (fun a F => False_ind _ F)).
apply (ASTRSPN lyc Sc W regsT memT mdc x y sx sy); try assumption.
apply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.
Lemma aj_strcspn_at_loc : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  astr_at SEGS W memT x sx -> astr_at SEGS W memT y sy ->
  aread_ok SEGS (2 * ESTACK) W regsT memT x (astr_len sx + 1) ->
  aread_ok SEGS (2 * ESTACK) W regsT memT y (astr_len sy + 1) ->
  amem_range x (astr_len sx + 8) -> amem_range y (astr_len sy + 8) ->
  atail_vis SEGS W memT (x + astr_len sx) -> atail_vis SEGS W memT (y + astr_len sy) ->
  rt_rom_view SEGS B W memT ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_strcspn)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
  aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (PCspn.cspn_len sy sx)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> ~ False ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y sx sy o raw
HJ Ha0 Ha1 Hx Hy Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hrx Hry Hmx Hmy Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (proj1 (proj2 (cmd_rec_cells SEGS B LAWS HB IMG lyc Sc W memT mdc (proj1 HJ)))) as HG.
apply (aj_art_at SEGS B LAWS pa_segs_low (cmd_cf_env SEGS B LAWS HB IMG) (2 * ESTACK) (fun _ => False) _ W regsT memT
STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw (fun regs2 _ => getr regs2 10 = w64 (Z.of_nat (PCspn.cspn_len sy sx)))
HJ Hsp Hal Hneg ltac:(lia) Hbud Hra (fun a F => False_ind _ F)).
apply (ASTRCSPN lyc Sc W regsT memT mdc x y sx sy); try assumption.
apply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.

(* ---- what holds at every point of the stretch: the parts of AW_S_stmt that neither the runs nor the calls
   change ---- *)
Definition ws_inv (cx : lcx) (q : awm) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc text copy arr : Z) :
  Prop :=
  aw_ctx B MT cx q ly S W regs mem md k acc /\ aw_rec B cx q ly S W mem (aw_blocks cx q text copy arr) /\
  aw_wslots cx (rdW W mem) text copy arr /\
  getr regs 24 = w64 text /\ getr regs 23 = w64 copy /\ getr regs 25 = w64 arr /\
  getr regs 19 = w64 (lt_len (x_pl cx) (x_n cx) (q_r q)) /\ getr regs 20 = w64 (q_src cx q) /\
  rdword (rdW W mem) (x_sp1 cx + LT_SPILL5) = Some (q_r q - SlotSpec.hdr_n (q_r q)) /\
  rdword (rdW W mem) (x_sp1 cx + LT_SPILL11) = Some (Z.of_nat (q_m q)) /\
  aval_mem (rdW W mem) (x_sp1 cx + LT_W + 24) 4 0.

Lemma ws_inv_facts : forall cx q ly S W regs mem md k acc text copy arr,
  ws_inv cx q ly S W regs mem md k acc text copy arr ->
  AR SEGS B ly S W mem md /\
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k /\
  In (copy, q_L0 cx q + 1) (ablocks B ly S) /\ In (arr, SlotSpec.arr_size (q_L0 cx q)) (ablocks B ly S) /\
  ~ In (copy, q_L0 cx q + 1) (x_bl0 B cx) /\ ~ In (arr, SlotSpec.arr_size (q_L0 cx q)) (x_bl0 B cx) /\
  (copy + q_L0 cx q + 1 <= arr \/ arr + SlotSpec.arr_size (q_L0 cx q) <= copy) /\
  spZ regs = x_sp0 cx - 256 /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  alloc_ceiling <= x_sp0 cx - LTOI_STK /\ x_sp0 cx mod 16 = 0 /\ x_sp0 cx <= 2 ^ 47 /\
  lt_base B MT cx /\ 0 <= q_L0 cx q /\
  (length (q_LN cx q) <= Z.to_nat (q_L0 cx q))%nat /\
  copy mod 16 = 0 /\ 4096 <= copy /\ copy + q_L0 cx q + 1 <= alloc_ceiling /\
  arr mod 16 = 0 /\ 4096 <= arr /\ arr + SlotSpec.arr_size (q_L0 cx q) <= alloc_ceiling /\
  in_app copy (q_L0 cx q + 1) /\ in_app arr (SlotSpec.arr_size (q_L0 cx q)) /\
  (forall a, copy <= a < copy + q_L0 cx q + 1 -> apresent (w_H W) mem a) /\
  (forall a, arr <= a < arr + SlotSpec.arr_size (q_L0 cx q) -> apresent (w_H W) mem a) /\
  (forall pn, In pn (q_O1 q) -> In pn (ablocks B ly S) /\ pn <> (copy, q_L0 cx q + 1) /\
     pn <> (arr, SlotSpec.arr_size (q_L0 cx q))).
Proof.
intros cx q ly S W regs mem md k acc text copy arr HI.
destruct HI as (((HB0 & HF & HSl & R8 & R9 & R22 & Hm & Hn & Hp & Hr & Hh & Hs) & Hbud) & Hrec & _).
destruct HF as (HJ & Hsp & Hgp & Htp & Hsv).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HB0 as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
destruct Hrec as (_ & _ & _ & _ & _ & HP).
assert (HL0 : 0 <= q_L0 cx q) by (rewrite q_L0_U; lia).
assert (HLN : (length (q_LN cx q) <= Z.to_nat (q_L0 cx q))%nat).
{ rewrite q_L0_U, Nat2Z.id. unfold q_LN, q_U. apply SlotWords.sw_line_le. }
assert (Ein : forall x, In x (aw_blocks cx q text copy arr) -> In x (ablocks B ly S)).
{ intros x Hx. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. right. exact Hx. }
assert (Hcin : In (copy, q_L0 cx q + 1) (ablocks B ly S)) by (apply Ein; rewrite aw_blocks_eq; right; left; reflexivity).
assert (Hain : In (arr, SlotSpec.arr_size (q_L0 cx q)) (ablocks B ly S))
  by (apply Ein; rewrite aw_blocks_eq; right; right; left; reflexivity).
pose proof (Permutation_NoDup HP (lt_ablocks_NoDup B LAWS ly S W mem md HAR)) as HND.
assert (HND2 : List.NoDup (x_bl0 B cx ++ aw_blocks cx q text copy arr)) by exact (NoDup_app_remove_l _ _ HND).
assert (Hcn0 : ~ In (copy, q_L0 cx q + 1) (x_bl0 B cx))
  by (apply (ws_nodup_disj _ (aw_blocks cx q text copy arr)); [exact HND2 | rewrite aw_blocks_eq; right; left; reflexivity]).
assert (Han0 : ~ In (arr, SlotSpec.arr_size (q_L0 cx q)) (x_bl0 B cx))
  by (apply (ws_nodup_disj _ (aw_blocks cx q text copy arr)); [exact HND2 | rewrite aw_blocks_eq; right; right; left; reflexivity]).
assert (Hne : (copy, q_L0 cx q + 1) <> (arr, SlotSpec.arr_size (q_L0 cx q))).
{ intros Heq. injection Heq as _ Heq. unfold SlotSpec.arr_size in Heq.
  pose proof (Z.div_mod (q_L0 cx q) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (q_L0 cx q) 2 ltac:(lia)). lia. }
pose proof (sep_blocks SEGS B LAWS ly S W mem md _ _ _ _ HAR Hcin Hain Hne) as Hdis.
unfold zdisjoint in Hdis. cbn [fst snd] in Hdis.
rewrite (ws_req (q_L0 cx q + 1)) in Hdis by lia.
assert (HAS : 16 <= SlotSpec.arr_size (q_L0 cx q)).
{ unfold SlotSpec.arr_size. pose proof (Z.div_pos (q_L0 cx q) 2 ltac:(lia) ltac:(lia)). lia. }
rewrite (ws_req (SlotSpec.arr_size (q_L0 cx q))) in Hdis by lia.
destruct (al_blocks _ _ LAWS ly S W mem md copy _ HAR Hcin) as (Hc16 & Hc4 & Hcc & Hcapp & Hcpres & _).
destruct (al_blocks _ _ LAWS ly S W mem md arr _ HAR Hain) as (Ha16 & Ha4 & Hac & Haapp & Hapres & _).
rewrite (ws_req (q_L0 cx q + 1)) in Hcc, Hcapp, Hcpres by lia.
rewrite (ws_req (SlotSpec.arr_size (q_L0 cx q))) in Hac, Haapp, Hapres by lia.
split; [exact HAR|]. split; [exact HJ|]. split; [exact Hcin|]. split; [exact Hain|].
split; [exact Hcn0|]. split; [exact Han0|]. split; [lia|].
split; [rewrite Hsp; unfold x_sp1, x_sp0, LT_FRAME; lia|].
split; [rewrite Hgp; exact Hgp0|]. split; [rewrite Htp; exact Htp0|].
split; [unfold x_sp0, LTOI_STK in *; lia|]. split; [exact Hal16|]. split; [lia|].
split; [exact HB0|]. split; [exact HL0|]. split; [exact HLN|].
split; [exact Hc16|]. split; [exact Hc4|]. split; [lia|].
split; [exact Ha16|]. split; [exact Ha4|]. split; [lia|].
split; [exact Hcapp|]. split; [exact Haapp|].
split; [intros a Ha; exact (proj1 (Hcpres a ltac:(lia)))|]. split; [intros a Ha; exact (proj1 (Hapres a ltac:(lia)))|].
intros pn Hpn.
assert (HO : In pn (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hpn).
split; [exact HO|].
assert (HNO : forall x, In x (aw_blocks cx q text copy arr) -> ~ In x (q_O1 q)).
{ intros x Hx. apply (ws_nodup_disj (q_O1 q) (x_bl0 B cx ++ aw_blocks cx q text copy arr)); [exact HND|].
  apply in_or_app. right. exact Hx. }
split; intros ->; [apply (HNO (copy, q_L0 cx q + 1)); [rewrite aw_blocks_eq; right; left; reflexivity | exact Hpn]
  | apply (HNO (arr, SlotSpec.arr_size (q_L0 cx q))); [rewrite aw_blocks_eq; right; right; left; reflexivity | exact Hpn]].
Qed.

(* the saved registers and the eleven words are kept when the frame's bytes are (LLVMFuzzerTestOneInput_s30.v) *)
Lemma ws_saved_kept : forall cx (rd rd' : reader),
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rd' a = rd a) -> lt_saved cx rd -> lt_saved cx rd'.
Proof.
intros cx rd rd' Hk HS i r Hi.
assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
change (length LT_SAVED) with 13%nat in Hi13.
apply (ws_rdword_kept rd rd'); [intros x Hx; apply Hk; lia | exact (HS i r Hi)].
Qed.
Lemma ws_slots_kept : forall cx (rd rd' : reader),
  (forall a, x_sp1 cx <= a < x_sp1 cx + 88 -> rd' a = rd a) -> lt_slots cx rd -> lt_slots cx rd'.
Proof.
intros cx rd rd' Hk HS o v Hin.
assert (HF : forallb (fun ov => (0 <=? fst ov) && (fst ov <=? 80)) LT_SLOTS = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HF (o, v) Hin) as Ho. cbn [fst] in Ho.
apply andb_prop in Ho as [Ho1 Ho2]. apply Z.leb_le in Ho1. apply Z.leb_le in Ho2.
apply (ws_rdword_kept rd rd'); [intros x Hx; apply Hk; lia | exact (HS o v Hin)].
Qed.

(* the stretch's writes (the wrapper's scratch below the frame, the copy and pointer blocks) keep ws_inv *)
Lemma ws_inv_kept : forall cx q ly S W regs mem md k acc text copy arr regs' mem' md',
  ws_inv cx q ly S W regs mem md k acc text copy arr ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem' md' k ->
  (forall r, In r WS_KEEP -> getr regs' r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 - 2 * ESTACK <= a < x_sp0 cx - 256) ->
     ~ (copy <= a < copy + q_L0 cx q + 1) -> ~ (arr <= a < arr + SlotSpec.arr_size (q_L0 cx q)) ->
     rdW W mem' a = rdW W mem a) ->
  ws_inv cx q ly S W regs' mem' md' k acc text copy arr.
Proof.
intros cx q ly S W regs mem md k acc text copy arr regs' mem' md' HI HJ' HR HK.
pose proof (ws_inv_facts cx q ly S W regs mem md k acc text copy arr HI) as
  (HAR & HJ & Hcin & Hain & Hcn0 & Han0 & Hdis & Hsp & Hgp & Htp & Hceil & Hal16 & H47 & HB0 & HL0 & HLN &
   Hc16 & Hc4 & Hcc & Ha16 & Ha4 & Hac & Hcapp & Haapp & Hcpres & Hapres & HO).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_value as [HAC1 _].
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : LTOI_STK = 32768) by reflexivity.
destruct HI as (((HB0' & HF & HSl & R8 & R9 & R22 & Hm & Hn & Hp & Hr & Hh & Hs) & Hbud) & Hrec & Hws & R24 & R23 & R25 &
  R19 & R20 & HS5 & HS11 & HWN).
destruct HF as (_ & Hsp0 & Hgp0 & Htp0 & Hsv).
assert (KF : forall a, x_sp0 cx - 256 <= a < x_sp0 cx -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK; lia. }
assert (Hs1 : x_sp1 cx = x_sp0 cx - 256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
assert (E2 : spZ regs' = spZ regs) by (unfold spZ; rewrite (HR 2%bv) by ws_inkeep; reflexivity).
unfold ws_inv, aw_ctx, aw_ctx0, lt_frame.
rewrite (HR 8%bv), (HR 9%bv), (HR 22%bv), (HR 24%bv), (HR 23%bv), (HR 25%bv), (HR 19%bv), (HR 20%bv), (HR 3%bv),
  (HR 4%bv) by ws_inkeep.
split.
{ split; [|exact Hbud].
  split; [exact HB0'|].
  split.
  { split; [exact HJ'|]. split; [rewrite E2; exact Hsp0|]. split; [exact Hgp0|]. split; [exact Htp0|].
    apply (ws_saved_kept cx (rdW W mem)); [intros a Ha; apply KF; lia | exact Hsv]. }
  split; [apply (ws_slots_kept cx (rdW W mem)); [intros a Ha; apply KF; lia | exact HSl]|].
  split; [exact R8|]. split; [exact R9|]. split; [exact R22|].
  split; [exact Hm|]. split; [exact Hn|]. split; [exact Hp|]. split; [exact Hr|].
  split; [apply (ws_rdword_kept (rdW W mem)); [intros x Hx; apply KF; unfold LT_HOSTB in Hx; lia | exact Hh]|].
  apply (ws_rdword_kept (rdW W mem)); [intros x Hx; apply KF; unfold LT_STATEB in Hx; lia | exact Hs]. }
split.
{ apply (aw_rec_kept B cx q ly S W mem mem' _ Hrec).
  pose proof (blk_off_imgP B ly S W mem md copy _ HAR Hcin) as Hoc.
  pose proof (blk_off_imgP B ly S W mem md arr _ HAR Hain) as Hoa.
  rewrite (ws_req (q_L0 cx q + 1)) in Hoc by lia.
  rewrite (ws_req (SlotSpec.arr_size (q_L0 cx q))) in Hoa by (unfold SlotSpec.arr_size; pose proof (Z.div_pos (q_L0 cx q) 2 ltac:(lia) ltac:(lia)); lia).
  unfold off_img in Hoc, Hoa.
  intros a [Ha | [Ha | [Ha | Ha]]].
  - unfold A_G_REC, REC_SIZE in Ha. apply HK; lia.
  - unfold A_REC_SPILL, SC_SIZE in Ha. apply HK; lia.
  - unfold A_G_QUITTING in Ha. apply HK; lia.
  - destruct Ha as (r & Hr0 & Hlo & Hhi). unfold ablocks_fp in Hr0. apply in_map_iff in Hr0 as ([b nb] & Er & Hb).
    subst r. cbn [fst snd] in Hlo, Hhi.
    destruct (HO (b, nb) Hb) as (Hbin & Hbc & Hba).
    destruct (al_blocks _ _ LAWS ly S W mem md b nb HAR Hbin) as (_ & Hb4 & Hbc' & _).
    pose proof (sep_blocks SEGS B LAWS ly S W mem md _ _ _ _ HAR Hbin Hcin Hbc) as D1.
    pose proof (sep_blocks SEGS B LAWS ly S W mem md _ _ _ _ HAR Hbin Hain Hba) as D2.
    unfold zdisjoint in D1, D2. cbn [fst snd] in D1, D2.
    rewrite (ws_req (q_L0 cx q + 1)) in D1 by lia.
    rewrite (ws_req (SlotSpec.arr_size (q_L0 cx q))) in D2 by (unfold SlotSpec.arr_size; pose proof (Z.div_pos (q_L0 cx q) 2 ltac:(lia) ltac:(lia)); lia).
    apply HK; lia. }
destruct Hws as (W1 & W2 & W3).
split.
{ split; [apply (ws_rdword_kept (rdW W mem)); [intros x Hx; apply KF; unfold LT_W in Hx; rewrite Hs1 in Hx; lia | exact W1]|].
  split; [apply (ws_rdword_kept (rdW W mem)); [intros x Hx; apply KF; unfold LT_W in Hx; rewrite Hs1 in Hx; lia | exact W2]|].
  apply (ws_rdword_kept (rdW W mem)); [intros x Hx; apply KF; unfold LT_W in Hx; rewrite Hs1 in Hx; lia | exact W3]. }
split; [exact R24|]. split; [exact R23|]. split; [exact R25|]. split; [exact R19|]. split; [exact R20|].
split; [apply (ws_rdword_kept (rdW W mem)); [intros x Hx; apply KF; unfold LT_SPILL5 in Hx; rewrite Hs1 in Hx; lia | exact HS5]|].
split; [apply (ws_rdword_kept (rdW W mem)); [intros x Hx; apply KF; unfold LT_SPILL11 in Hx; rewrite Hs1 in Hx; lia | exact HS11]|].
apply (aval_mem_kept_r (rdW W mem)); [intros x Hx; apply KF; unfold LT_W in Hx; rewrite Hs1 in Hx; change (Z.of_nat 4) with 4 in Hx; lia | exact HWN].
Qed.

(* ---- the read-only facts the two wrappers ask of the set " \t" (0x210a0) and of the image ---- *)
Lemma ws_PG_static : forall a, inFP cmd_PG a -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a (r & Hr & Hlo & Hhi). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. apply Exists_exists.
unfold TFIB_PROG_STATIC.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo, Hhi.
- exists (0x5e3740, 960). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
- exists (0x5e3be0, 56). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
- exists (0x5e3c60, 4). split; [right; right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma ws_aro : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem).
Proof.
intros cx ly S W mem md k HB0 HJ. pose proof HB0 as (HPRE & HRO0 & _).
exact (cmd_rodata_kept SEGS B LAWS HB IMG _ _ _ _ _ _ _ _ _ _ _ _ _ [] k (proj1 HPRE) HJ
  (fun a Ha => or_introl (ws_PG_static a Ha)) HRO0).
Qed.
Lemma ws_sep : forall cx ly S (W : world SEGS) regs mem md k,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k ->
  ecall_pre_stk SEGS B (2 * ESTACK) ly S W regs mem md ->
  astr_at SEGS W mem 0x210a0 SlotWords.SEPS /\
  aread_ok SEGS (2 * ESTACK) W regs mem 0x210a0 (astr_len SlotWords.SEPS + 1) /\
  atail_vis SEGS W mem (0x210a0 + astr_len SlotWords.SEPS) /\ rt_rom_view SEGS B W mem /\
  amem_range 0x210a0 (astr_len SlotWords.SEPS + 8).
Proof.
intros cx ly S W regs mem md k HB0 HJ HPRE.
pose proof (proj1 HJ) as HAR.
pose proof (ws_aro cx ly S W mem md k HB0 HJ) as HRO.
assert (Hin : In (0x210a0, RO_lit_210a0) cmd_ro_list) by (unfold cmd_ro_list; repeat (first [left; reflexivity | right])).
pose proof (cmd_ro_obj_bytes SEGS B LAWS HB IMG ly S W mem md _ HAR HRO Hin) as HL. cbn [fst snd] in HL.
assert (HS : abytes_atR (rdW W mem) 0x210a0 (SlotWords.SEPS ++ [Z_to_bv 8 0])) by exact HL.
split; [apply (astr_atR_view SEGS); split; [exact HS|] |].
{ intros Hz. cbn [SlotWords.SEPS In] in Hz.
  destruct Hz as [Hz | [Hz | []]]; apply (f_equal (@bv_unsigned 8)) in Hz; vm_compute in Hz; discriminate. }
split; [|split; [|split]].
- change (astr_len SlotWords.SEPS + 1) with 3.
  apply (cmd_aread_ok_img SEGS B LAWS HB (2 * ESTACK) ly S W regs mem md 0x210a0 3 HPRE); [|vm_compute; reflexivity].
  intros a Ha. replace a with (0x210a0 + Z.of_nat (Z.to_nat (a - 0x210a0))) by lia.
  rewrite (HS (Z.to_nat (a - 0x210a0))) by (cbn [length app SlotWords.SEPS]; lia). discriminate.
- change (0x210a0 + astr_len SlotWords.SEPS) with 0x210a2.
  apply (cmd_tail_vis_at SEGS B LAWS HB IMG ly S W mem md 0x210a2 HAR). apply In_of_existsb. vm_compute. reflexivity.
- exact (cmd_rom_view_on SEGS B LAWS HB IMG CMD_RLO CMD_RHI W mem HRO).
- (* the set " \t" is a .rodata literal: low band *)
  change (astr_len SlotWords.SEPS) with 2. apply amem8_of_low; unfold kLowMemEnd; lia.
Qed.
(* the rest of the line from byte j of the copy buffer: the string a wrapper scans *)
Lemma ws_cursor : forall cx q ly S (W : world SEGS) regs mem md copy C (j : nat),
  AR SEGS B ly S W mem md -> In (copy, q_L0 cx q + 1) (ablocks B ly S) ->
  alloc_ceiling <= spZ regs - 2 * ESTACK ->
  abytes_atR (rdW W mem) copy C -> length C = Z.to_nat (q_L0 cx q + 1) ->
  (length (q_LN cx q) <= Z.to_nat (q_L0 cx q))%nat -> (j <= length (q_LN cx q))%nat ->
  (forall t, (j <= t <= length (q_LN cx q))%nat -> nth_error C t = nth_error (q_LN cx q ++ [Z_to_bv 8 0]) t) ->
  astr_at SEGS W mem (copy + Z.of_nat j) (skipn j (q_LN cx q)) /\
  aread_ok SEGS (2 * ESTACK) W regs mem (copy + Z.of_nat j) (astr_len (skipn j (q_LN cx q)) + 1) /\
  atail_vis SEGS W mem (copy + Z.of_nat j + astr_len (skipn j (q_LN cx q))) /\
  amem_range (copy + Z.of_nat j) (astr_len (skipn j (q_LN cx q)) + 8).
Proof.
intros cx q ly S W regs mem md copy C j HAR Hin Hsp HCB HCL HLN Hj HCF.
assert (HL0 : 0 <= q_L0 cx q) by (rewrite q_L0_U; lia).
assert (Hlen : astr_len (skipn j (q_LN cx q)) = Z.of_nat (length (q_LN cx q)) - Z.of_nat j)
  by (unfold astr_len; rewrite length_skipn; lia).
split; [|split; [|split]].
- apply (astr_atR_view SEGS). split.
  + apply (ws_tail_bytes _ copy C); [exact HCB | exact Hj | lia | exact HCF].
  + intros Hz. apply (SlotWords.sw_line_nz (q_D cx q) (Z_to_bv 8 0)); [exact (SlotWords.sw_in_skipn _ _ _ Hz) | reflexivity].
- rewrite Hlen. apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W regs mem md copy (q_L0 cx q + 1));
    [exact HAR | exact Hin | lia | lia | lia | exact Hsp].
- rewrite Hlen. apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md copy (q_L0 cx q + 1));
    [exact HAR | exact Hin | rewrite ws_req by lia; lia].
- (* the cursor is in words_of's copy block: heap band, also when the NUL is the block's last byte
     (kit PaLibH.amem8_of_block) *)
  rewrite Hlen. apply (amem8_of_block SEGS B LAWS ly S W mem md copy (q_L0 cx q + 1) (copy + Z.of_nat j)
    (Z.of_nat (length (q_LN cx q)) - Z.of_nat j) HAR Hin); [lia | rewrite ws_req by lia; lia | lia].
Qed.

(* ---- 0x86864: the strspn wrapper has returned s = aw_spn (skipn i LN); s5 = kw, s2 = s10 = arr + 8 kw,
   s11 = copy + i; memory is the head's below the wrapper's scratch ---- *)
Definition WS_B_stmt (m nm : nat) : Prop :=
  forall cx q ly S W regs mem md k acc text copy arr (i kw : nat) (C : list byte) (wp : list Z),
  q_m q = m -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  ws_inv cx q ly S W regs mem md k acc text copy arr ->
  getr regs 21 = w64 (Z.of_nat kw) -> getr regs 18 = w64 (arr + 8 * Z.of_nat kw) ->
  getr regs 26 = w64 (arr + 8 * Z.of_nat kw) -> getr regs 27 = w64 (copy + Z.of_nat i) ->
  getr regs 10 = w64 (Z.of_nat (aw_spn (skipn i (q_LN cx q)))) ->
  nm = (length (q_LN cx q) - i)%nat -> (i <= length (q_LN cx q))%nat -> (2 * kw <= i)%nat ->
  length wp = kw -> (kw <= length (q_ws cx q))%nat ->
  Verbs.words_acc [] (skipn i (q_LN cx q)) = skipn kw (q_ws cx q) ->
  abytes_atR (rdW W mem) copy C -> length C = Z.to_nat (q_L0 cx q + 1) ->
  (forall j, (i <= j <= length (q_LN cx q))%nat -> nth_error C j = nth_error (q_LN cx q ++ [Z_to_bv 8 0]) j) ->
  aw_arr (rdW W mem) arr wp -> aw_found copy (q_ws cx q) C wp i ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + WS_B)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* 0x86850 .. jal strspn (mv s5,a0; a1 = " \t"; a0 = s11), the call and back at 0x86864 *)
Lemma ws_A : forall m nm, WS_B_stmt m nm -> AW_S_stmt B MT m nm.
Proof.
intros m nm HB2 cx q ly S W regs mem md k acc text copy arr i kw C wp Hm HFP0 HC Hrec Hws R24 R23 R25 R10 R18 R26 R27
  R19 R20 HS5 HS11 Hnm Hi Hk Hwp Hkw HWA HCB HCL HCF HAA HFD HWN.
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_value as [[HAC1 HAC2] _].
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : LTOI_STK = 32768) by reflexivity.
assert (HI : ws_inv cx q ly S W regs mem md k acc text copy arr)
  by exact (conj HC (conj Hrec (conj Hws (conj R24 (conj R23 (conj R25 (conj R19 (conj R20 (conj HS5 (conj HS11 HWN)))))))))).
pose proof (ws_inv_facts cx q ly S W regs mem md k acc text copy arr HI) as
  (HAR & HJ & Hcin & Hain & Hcn0 & Han0 & Hdis & Hsp & Hgp & Htp & Hceil & Hal16 & H47 & HB0 & HL0 & HLN &
   Hc16 & Hc4 & Hcc & Ha16 & Ha4 & Hac & Hcapp & Haapp & Hcpres & Hapres & HO).
pose proof HB0 as (_ & _ & _ & HOBJ & _).
assert (R9 : getr regs 9 = w64 LT_SB) by (destruct HC as ((_ & _ & _ & _ & R9 & _) & _); exact R9).
unfold w64 in *.
assert (HAK : 8 * Z.of_nat kw <= SlotSpec.arr_size (q_L0 cx q)).
{ unfold SlotSpec.arr_size. pose proof (Z.div_mod (q_L0 cx q) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (q_L0 cx q) 2 ltac:(lia)). lia. }
(* the seat at 0x86850: no memory access up to the call *)
pose proof (ws_E_reg regs []) as EEo.
assert (E2 : ew (ws_E regs []) 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew (ws_E regs []) 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew (ws_E regs []) 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E9 : ew (ws_E regs []) 9 = Z_to_bv 64 LT_SB) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E10 : ew (ws_E regs []) 10 = Z_to_bv 64 (Z.of_nat kw)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E18 : ew (ws_E regs []) 18 = Z_to_bv 64 (arr + 8 * Z.of_nat kw)) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E26 : ew (ws_E regs []) 26 = Z_to_bv 64 (arr + 8 * Z.of_nat kw)) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
assert (E27 : ew (ws_E regs []) 27 = Z_to_bv 64 (copy + Z.of_nat i)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
pose proof (ws_E_img regs []) as HEI. pose proof (ws_E_agree regs []) as HAE.
pose proof (ws_ew_obj (ws_E regs []) 5 0x210a0 HOBJ HEI ltac:(vm_compute; lia) eq_refl ltac:(unfold A_OBJ, A_LIM; lia)) as E246.
change (A_OBJ 5) with 246%nat in E246.
assert (HAT : atoms_ok (ws_E regs []) ws_atomsA).
{ cbn [ws_atomsA atoms_ok]. split; [|split; [|exact I]].
  - apply (ws_afact _ 2 (spZ regs)); [rewrite E2; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
      | apply bv_unsigned_in_range | rewrite Hsp; lia | rewrite Hsp; change (2 ^ 4) with 16; rewrite Zminus_mod, Hal16; reflexivity | lia].
  - apply (ws_afact _ 9 LT_SB _ _ _ E9); [unfold LT_SB; lia | unfold LT_SB, SB; lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
pose proof (ws_seat W regs mem AW_S [] [] ws_atomsA [] eq_refl (Forall_nil _) I HAT I) as HS.
assert (SHOK : sh_ok SEGS WSx [] (ws_E regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
remember (ws_E regs []) as E eqn:HE.
paj_run_tok RUN HS HJ SHOK WSspan.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdA := d) in *; clearbody mdA end.
lazymatch type of HS with context [restrict _ ?mm] => rename mm into msA end.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem msA)) |- _ =>
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem msA) a = rdW W mem a)
  by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b wlo whi a' Hin' _; vm_compute in Hin'; destruct Hin' | exact Ha | intros F; exact F ])
end.
pose proof (regs_kept_of_st_ok SEGS E _ _ regs [] WS_KEEP HS HAE ltac:(vm_compute; reflexivity)) as RK.
cbn [ms_regs restrict] in RK.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21.
prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
assert (HspT : spZ (ms_regs msA) = x_sp0 cx + -256)
  by (unfold spZ at 1; rewrite P2, E2; change (bv_unsigned (getr regs 2)) with (spZ regs); rewrite Hsp; lia).
assert (P3' : getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
assert (P4' : getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite P4, E4; exact Htp).
assert (P10' : getr (ms_regs msA) 10 = w64 (copy + Z.of_nat i)) by (rewrite P10, E27; reflexivity).
assert (P11' : getr (ms_regs msA) 11 = w64 0x210a0) by (rewrite P11, E246; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs msA) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (HCB1 : abytes_atR (rdW W (ms_mem msA)) copy C) by (apply (abytes_atR_kept_r (rdW W mem)); [intros x Hx; apply KA; lia | exact HCB]).
pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
  (x_md cx) [] ly S W (ms_mem msA) mdA k (ms_regs msA) (-256) HJ HspT eq_refl ltac:(lia) ltac:(lia)
  ltac:(rewrite WS; lia) HraT P3' P4') as HPREc.
destruct (ws_cursor cx q ly S W (ms_regs msA) (ms_mem msA) mdA copy C i (proj1 HJ) Hcin ltac:(rewrite HspT; lia)
  HCB1 HCL HLN Hi HCF) as (Hstr & Hrd & Htl & Hm8).
destruct (ws_sep cx ly S W (ms_regs msA) (ms_mem msA) mdA k HB0 HJ HPREc) as (Hsstr & Hsrd & Hstl & Hrom & Hsm8).
eapply SRr_bind.
{ exact (aj_strspn_at_loc W (ms_regs msA) (ms_mem msA) LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx)
    (x_mem cx) (x_md cx) [] ly S mdA k (copy + Z.of_nat i) 0x210a0 (skipn i (q_LN cx q)) SlotWords.SEPS (-256)
    (getr (ms_regs msA) 1) HJ P10' P11' ltac:(lia) ltac:(lia) HspT eq_refl ltac:(lia) ltac:(rewrite WS, Hes; lia)
    P3' P4' eq_refl HraT Hstr Hsstr Hrd Hsrd Hm8 Hsm8 Htl Hstl Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
rewrite P1. change (BASE + 896) with (BASE + WS_B).
assert (K2 : forall a, 0 <= a < x_sp0 cx - 256 - 2 * ESTACK -> rdW W mem2 a = rdW W mem a).
{ intros a Ha. rewrite (HK2 a ltac:(lia) ltac:(lia) ltac:(tauto)). exact (KA a ltac:(lia)). }
apply (HB2 cx q ly S W regs2 mem2 md2 k acc text copy arr i kw C wp Hm HFP0).
- apply (ws_inv_kept cx q ly S W regs mem md k acc text copy arr regs2 mem2 md2 HI HJ2).
  + intros r Hr. rewrite (ws_pres_keep _ _ HP2 r Hr). exact (RK r Hr).
  + intros a Ha Hs _ _. rewrite (HK2 a Ha ltac:(lia) ltac:(tauto)). exact (KA a Ha).
- ws_reg HP2 21 P21 E10.
- ws_reg HP2 18 P18 E18.
- ws_reg HP2 26 P26 E26.
- ws_reg HP2 27 P27 E27.
- exact HQ2.
- exact Hnm.
- exact Hi.
- exact Hk.
- exact Hwp.
- exact Hkw.
- exact HWA.
- apply (abytes_atR_kept_r (rdW W mem)); [intros x Hx; apply K2; lia | exact HCB].
- exact HCL.
- exact HCF.
- apply (ws_arr_kept (rdW W mem)); [intros x Hx; apply K2; lia | exact HAA].
- exact HFD.
Qed.

(* 0x86864 .. jal strcspn: the cursor past the separators, its byte; the exit when it is the NUL; the 8-byte check
   and the store of the word's address at arr[kw]; the call and back at 0x868a4 *)
Lemma ws_B : forall m nm, AW_S2_stmt B MT m nm -> AW_E_stmt B MT m -> WS_B_stmt m nm.
Proof.
intros m nm HS2 HE cx q ly S W regs mem md k acc text copy arr i kw C wp Hm HFP0 HI R21 R18 R26 R27 R10 Hnm Hi Hk Hwp Hkw
  HWA HCB HCL HCF HAA HFD.
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_value as [[HAC1 HAC2] _].
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : LTOI_STK = 32768) by reflexivity.
pose proof (ws_inv_facts cx q ly S W regs mem md k acc text copy arr HI) as
  (HAR & HJ & Hcin & Hain & Hcn0 & Han0 & Hdis & Hsp & Hgp & Htp & Hceil & Hal16 & H47 & HB0 & HL0 & HLN &
   Hc16 & Hc4 & Hcc & Ha16 & Ha4 & Hac & Hcapp & Haapp & Hcpres & Hapres & HO).
pose proof HB0 as (_ & _ & _ & HOBJ & _).
assert (R9 : getr regs 9 = w64 LT_SB) by (destruct HI as (((_ & _ & _ & _ & R9 & _) & _) & _); exact R9).
unfold w64 in *.
assert (HAK : 8 * Z.of_nat kw + 8 <= SlotSpec.arr_size (q_L0 cx q)).
{ unfold SlotSpec.arr_size. pose proof (Z.div_mod (q_L0 cx q) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (q_L0 cx q) 2 ltac:(lia)). lia. }
(* the model: s separators, then the byte at i + s *)
remember (aw_spn (skipn i (q_LN cx q))) as s eqn:Es.
assert (Hs : (i + s <= length (q_LN cx q))%nat).
{ pose proof (SlotWords.sw_spn_le SlotWords.SEPS (skipn i (q_LN cx q))) as H. rewrite length_skipn in H.
  unfold aw_spn in Es. lia. }
assert (HNZ : forall b, In b (q_LN cx q) -> bv_unsigned b <> 0) by (intros b Hb; exact (SlotWords.sw_line_nz (q_D cx q) b Hb)).
destruct (SlotWords.sw_nth_z (q_LN cx q) (i + s) HNZ Hs) as (b1 & Eb1 & Hb1z).
assert (HC1 : nth_error C (i + s) = Some b1) by (rewrite HCF by lia; exact Eb1).
assert (HCL1 : (i + s < length C)%nat) by (apply nth_error_Some; rewrite HC1; discriminate).
assert (Hrd1 : rdW W mem (copy + Z.of_nat (i + s)) = Some (bv_unsigned b1)).
{ rewrite (HCB (i + s)%nat HCL1). rewrite (nth_error_nth _ _ _ HC1). reflexivity. }
pose proof (bv_unsigned_in_range 8 b1) as Rb1. change (bv_modulus 8) with 256 in Rb1.
(* the seat at 0x86864 *)
pose proof (ws_E_reg regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) as EEo.
assert (E2 : ew (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E9 : ew (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) 9 = Z_to_bv 64 LT_SB)
  by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E10 : ew (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) 10 = Z_to_bv 64 (Z.of_nat s))
  by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E18 : ew (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) 18 = Z_to_bv 64 (arr + 8 * Z.of_nat kw))
  by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E21 : ew (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) 21 = Z_to_bv 64 (Z.of_nat kw))
  by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E26 : ew (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) 26 = Z_to_bv 64 (arr + 8 * Z.of_nat kw))
  by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
assert (E27 : ew (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) 27 = Z_to_bv 64 (copy + Z.of_nat i))
  by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
assert (E32 : ew (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) 32 = Z_to_bv 64 (copy + Z.of_nat (i + s)))
  by exact (ws_E_extra regs _ 0 ltac:(lia)).
assert (E33 : ew (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) 33 = Z_to_bv 64 (bv_unsigned b1))
  by exact (ws_E_extra regs _ 1 ltac:(lia)).
pose proof (ws_E_img regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) as HEI.
pose proof (ws_E_agree regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) as HAE.
pose proof (ws_ew_obj _ 5 0x210a0 HOBJ HEI ltac:(vm_compute; lia) eq_refl ltac:(unfold A_OBJ, A_LIM; lia)) as E246.
change (A_OBJ 5) with 246%nat in E246.
remember (ws_E regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) as E eqn:HE0.
assert (HRS : Forall (region_ok SEGS E (mrestrict (w_H W) mem)) ws_rB).
{ unfold ws_rB. constructor; [|constructor; [|constructor]].
  - apply (ws_rg_byte E W mem 32 33 (copy + Z.of_nat (i + s)) (bv_unsigned b1) E32 E33); [lia | lia | lia | exact Hrd1].
  - apply (ws_rg_slot E W mem 26 (arr + 8 * Z.of_nat kw) E26); [lia | lia | intros a Ha; apply Hapres; lia]. }
assert (HPD : pairwise_disjoint E ws_rB).
{ apply pairwise_disjoint_of_extents. unfold ws_rB, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E32, E26, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
assert (HAT : atoms_ok E ws_atomsB).
{ cbn [ws_atomsB atoms_ok]. unfold PTR.
  split; [apply (ws_afact _ 2 (spZ regs)); [rewrite E2; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
      | apply bv_unsigned_in_range | rewrite Hsp; lia | rewrite Hsp; change (2 ^ 4) with 16; rewrite Zminus_mod, Hal16; reflexivity | lia]|].
  split; [apply (ws_afact _ 9 LT_SB _ _ _ E9); [unfold LT_SB; lia | unfold LT_SB, SB; lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (ws_afact _ 18 _ _ _ _ E18); [lia | lia | apply ws_mod8; exact Ha16 | lia]|].
  split; [apply (ws_afact _ 26 _ _ _ _ E26); [lia | lia | apply ws_mod8; exact Ha16 | lia]|].
  split; [apply (ws_afact _ 27 _ _ _ _ E27); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (ws_afact _ 32 _ _ _ _ E32); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (ws_afact _ 33 _ _ _ _ E33); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  exact I. }
assert (HAL : alias_ok E ws_aliasB).
{ cbn [ws_aliasB alias_ok]. split; [|exact I].
  rewrite (ws_add_atoms E 27 10 (copy + Z.of_nat i) (Z.of_nat s) E27 E10) by lia.
  cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. f_equal. lia. }
assert (UBx : U E WSx = SHADOW_OFF) by (unfold WSx; rewrite (U_atom E 9 LT_SB E9) by (unfold LT_SB; lia); reflexivity).
assert (HRA8 : range_addressable (rdW W mem) SHADOW_OFF (arr + 8 * Z.of_nat kw) 8)
  by (apply (range_addressable_of_block SEGS B LAWS ly S W mem md arr (SlotSpec.arr_size (q_L0 cx q)));
      [exact HAR | exact Hain | lia | rewrite ws_req by lia; lia]).
assert (HSH : sh_ok SEGS WSx ws_shB E (mrestrict (w_H W) mem)).
{ unfold sh_ok, ws_shB. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range SEGS (w_H W) mem E WSx 18 (arr + 8 * Z.of_nat kw) 8 (arr + 8 * Z.of_nat kw) 0 8 HRA8 UBx);
      [apply U_atom; [exact E18 | lia] | lia | lia |].
    intros x Hx. apply (ws_not_shadow arr (SlotSpec.arr_size (q_L0 cx q)) x Haapp). lia.
  - apply (shent_ok_of_range SEGS (w_H W) mem E WSx 26 (arr + 8 * Z.of_nat kw) 8 (arr + 8 * Z.of_nat kw) 0 8 HRA8 UBx);
      [apply U_atom; [exact E26 | lia] | lia | lia |].
    intros x Hx. apply (ws_not_shadow arr (SlotSpec.arr_size (q_L0 cx q)) x Haapp). lia. }
pose proof (ws_seat W regs mem WS_B [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)] ws_rB ws_atomsB
  ws_aliasB eq_refl) as HS. rewrite <- HE0 in HS. specialize (HS HRS HPD HAT HAL).
(* the run to the test of the byte (0x86864 .. 0x8687c) *)
paj_run_tok RUN HS HJ HSH WSspan.
{ cbn [ms_mem]. unfold WSx. rewrite (U_atom E 9 LT_SB E9), (U_atom E 32 (copy + Z.of_nat (i + s)) E32) by (unfold LT_SB; lia).
  exact (range_addressable_of_block SEGS B LAWS ly S W mem md copy (q_L0 cx q + 1) (copy + Z.of_nat (i + s)) 1 HAR Hcin
    ltac:(lia) ltac:(rewrite ws_req by lia; lia)). }
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (YCbq.awr_ok_cons_gen SEGS B E) with (k := 26%nat) (b := arr + 8 * Z.of_nat kw);
    [reflexivity | rewrite E26; apply unsigned_lit_small; lia | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left.
  exists arr, (SlotSpec.arr_size (q_L0 cx q)). split; [exact Hain|]. split; [exact Han0|]. rewrite ws_req by lia. lia. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdB1 := d) in *; clearbody mdB1 end.
lazymatch type of HS with context [restrict _ ?mm] => rename mm into msB1 end.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem msB1)) |- _ =>
  assert (KB1 : forall a, 0 <= a < 2 ^ 64 -> ~ (arr + 8 * Z.of_nat kw <= a < arr + 8 * Z.of_nat kw + 8) ->
    rdW W (ms_mem msB1) a = rdW W mem a)
  by (intros a Ha Hn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
        (fun a => arr + 8 * Z.of_nat kw <= a < arr + 8 * Z.of_nat kw + 8) HFr);
      [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin';
        repeat (destruct Hin' as [Hq0 | Hin']; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr';
          rewrite ?E26 in Hrr'; rewrite ?unsigned_lit_small in Hrr' by lia; lia|]);
        destruct Hin'
      | exact Ha | exact Hn ])
end.
psrr_branch_tok RUN BR HS HSH WSspan.
- (* the byte is the NUL: only separators were left; beqz -> 0x8692c with s5 = kw *)
  assert (Hb0 : bv_unsigned b1 = 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite U_SOff, U_lit in Hc by lia. cbn [ew ewset Nat.eqb] in Hc.
    rewrite E33, Z.add_0_r, unsigned_lit_small in Hc by lia. rewrite zcanon_id in Hc by (unfold M64; lia). exact Hc. }
  assert (Esl : (i + s)%nat = length (q_LN cx q)) by (apply Hb1z; exact Hb0).
  assert (Hall : forall x, In x (skipn i (q_LN cx q)) -> Verbs.is_sep x = true).
  { intros y Hy. destruct (SlotWords.sw_spn_split SlotWords.SEPS (skipn i (q_LN cx q))) as [SP1 _].
    unfold aw_spn in Es. rewrite <- Es in SP1. rewrite firstn_all2 in SP1 by (rewrite length_skipn; lia).
    rewrite <- SlotWords.sw_in_set_seps. exact (SP1 y Hy). }
  assert (Hkw2 : length (q_ws cx q) = kw).
  { pose proof (SlotWords.sw_words_seps (skipn i (q_LN cx q)) [] Hall) as E0. rewrite app_nil_r, HWA in E0.
    cbn [Verbs.words_acc] in E0. apply (f_equal (@length _)) in E0. rewrite length_skipn in E0. cbn [length] in E0. lia. }
  paj_run_to_tok RUNTO HS HJ HSH WSspan AW_E.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_cons_ro; [cbn; lia|].
    apply (YCbq.awr_ok_cons_gen SEGS B) with (k := 26%nat) (b := arr + 8 * Z.of_nat kw);
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E26; apply unsigned_lit_small; lia | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left.
    exists arr, (SlotSpec.arr_size (q_L0 cx q)). split; [exact Hain|]. split; [exact Han0|]. rewrite ws_req by lia. lia. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdB2 := d) in *; clearbody mdB2 end.
  lazymatch type of HS with context [restrict _ ?mm] => rename mm into msB2 end.
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem msB2)) |- _ =>
    assert (KB2 : forall a, 0 <= a < 2 ^ 64 -> ~ (arr + 8 * Z.of_nat kw <= a < arr + 8 * Z.of_nat kw + 8) ->
      rdW W (ms_mem msB2) a = rdW W mem a)
    by (intros a Ha Hn; rewrite <- (KB1 a Ha Hn); apply (kept_of_frame (segs := SEGS) _ _ _ _ _
          (fun a => arr + 8 * Z.of_nat kw <= a < arr + 8 * Z.of_nat kw + 8) HFr);
        [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin';
          repeat (destruct Hin' as [Hq0 | Hin']; [injection Hq0 as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr';
            rewrite ?E26 in Hrr'; rewrite ?unsigned_lit_small in Hrr' by lia; lia|]);
          destruct Hin'
        | exact Ha | exact Hn ])
  end.
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) E2)
      by ws_agree HAE
  end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ WS_KEEP HS HAE2 ltac:(vm_compute; reflexivity)) as RK.
  cbn [ms_regs restrict] in RK.
  pmkst HS.
  prreg HS (21%bv : bv 5) Q21.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 - 2 * ESTACK <= a < x_sp0 cx - 256) ->
    ~ (copy <= a < copy + q_L0 cx q + 1) -> ~ (arr <= a < arr + SlotSpec.arr_size (q_L0 cx q)) ->
    rdW W (ms_mem msB2) a = rdW W mem a) by (intros a Ha _ _ Hn; apply KB2; [exact Ha | lia]).
  pose proof (ws_inv_kept cx q ly S W regs mem md k acc text copy arr (ms_regs msB2) (ms_mem msB2) mdB2 HI HJ RK KM) as HI2.
  destruct HI2 as (HC2 & Hrec2 & Hws2 & R24' & R23' & R25' & R19' & R20' & HS5' & HS11' & _).
  apply (HE cx q ly S W (ms_regs msB2) (ms_mem msB2) mdB2 k acc text copy arr C wp Hm HFP0 HC2 Hrec2 Hws2 R24' R23' R25' R19' R20').
  + etransitivity; [exact Q21|]. rewrite E21, Hkw2. reflexivity.
  + exact HS5'.
  + exact HS11'.
  + rewrite Hwp. exact (eq_sym Hkw2).
  + apply (abytes_atR_kept_r (rdW W mem)); [intros x Hx; apply KB2; lia | exact HCB].
  + exact HCL.
  + apply (ws_arr_kept (rdW W mem)); [intros x Hx; apply KB2; lia | exact HAA].
  + apply (ws_found_mono copy (q_ws cx q) C wp i); [exact HFD | lia].
- (* a word starts at i + s: the 8-byte check of s2 vanishes, arr[kw] := s11, then the strcspn call *)
  assert (Hb0 : bv_unsigned b1 <> 0).
  { intros Hz. rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc. rewrite U_SOff, U_lit by lia.
    cbn [ew ewset Nat.eqb]. rewrite E33, Z.add_0_r, unsigned_lit_small by lia. rewrite zcanon_id by (unfold M64; lia). exact Hz. }
  assert (Hlt : (i + s < length (q_LN cx q))%nat).
  { assert ((i + s)%nat <> length (q_LN cx q)) by (intros Eq; apply Hb0, Hb1z, Eq). lia. }
  paj_run_tok RUN HS HJ HSH WSspan.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_cons_ro; [cbn; lia|].
    apply (YCbq.awr_ok_cons_gen SEGS B) with (k := 26%nat) (b := arr + 8 * Z.of_nat kw);
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E26; apply unsigned_lit_small; lia | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left.
    exists arr, (SlotSpec.arr_size (q_L0 cx q)). split; [exact Hain|]. split; [exact Han0|]. rewrite ws_req by lia. lia. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdB3 := d) in *; clearbody mdB3 end.
  lazymatch type of HS with context [restrict _ ?mm] => rename mm into msB3 end.
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem msB3)) |- _ =>
    assert (KB3 : forall a, 0 <= a < 2 ^ 64 -> ~ (arr + 8 * Z.of_nat kw <= a < arr + 8 * Z.of_nat kw + 8) ->
      rdW W (ms_mem msB3) a = rdW W mem a)
    by (intros a Ha Hn; rewrite <- (KB1 a Ha Hn); apply (kept_of_frame (segs := SEGS) _ _ _ _ _
          (fun a => arr + 8 * Z.of_nat kw <= a < arr + 8 * Z.of_nat kw + 8) HFr);
        [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin';
          repeat (destruct Hin' as [Hq0 | Hin']; [injection Hq0 as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hrr';
            rewrite ?E26 in Hrr'; rewrite ?unsigned_lit_small in Hrr' by lia; lia|]);
          destruct Hin'
        | exact Ha | exact Hn ])
  end.
  (* arr[kw] holds the cursor *)
  lazymatch type of HS with st_ok _ ?E3 ?ss3 _ =>
    pose proof (st_ok_region_nth E3 ss3 _ 1%nat
      (YP09.mkRegion (Some 26%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]) HS eq_refl) as Hreg;
    assert (HAE3 : env_agree 32 (Ereg regs [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1)]) E3)
      by ws_agree HAE;
    assert (E26' : ew E3 26 = Z_to_bv 64 (arr + 8 * Z.of_nat kw)) by (cbn [ew ewset Nat.eqb]; exact E26);
    assert (E32' : ew E3 32 = Z_to_bv 64 (copy + Z.of_nat (i + s))) by (cbn [ew ewset Nat.eqb]; exact E32);
    pose proof (field_of_region_any E3 _ 26 (arr + 8 * Z.of_nat kw) _ 0 8 0 8 0 8%N (SOff 32 0) Hreg
      ltac:(rewrite E26'; apply unsigned_lit_small; lia) (or_introl eq_refl) ltac:(cbn; lia)) as Hv;
    change (bv_unsigned (sv_denot E3 (SOff 32 0))) with (U E3 (SOff 32 0)) in Hv;
    rewrite (U_atom E3 32 _ E32') in Hv by lia
  end.
  cbn [ms_mem restrict] in Hv.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Hv. rewrite Z.mod_small, Z.add_0_r in Hv by lia.
  pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem msB3) _ _ Hv ltac:(lia)) as Hslot.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ WS_KEEP HS HAE3 ltac:(vm_compute; reflexivity)) as RK.
  cbn [ms_regs restrict] in RK.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21.
  prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  assert (HspT : spZ (ms_regs msB3) = x_sp0 cx + -256)
    by (unfold spZ at 1; rewrite P2, E2; change (bv_unsigned (getr regs 2)) with (spZ regs); rewrite Hsp; lia).
  assert (P3' : getr (ms_regs msB3) 3 = w64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
  assert (P4' : getr (ms_regs msB3) 4 = w64 (as_tp B)) by (rewrite P4, E4; exact Htp).
  assert (P10' : getr (ms_regs msB3) 10 = w64 (copy + Z.of_nat (i + s))) by (rewrite P10, E32; reflexivity).
  assert (P11' : getr (ms_regs msB3) 11 = w64 0x210a0) by (rewrite P11, E246; reflexivity).
  assert (HraT : YK0s.ret_ok (getr (ms_regs msB3) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (HCB3 : abytes_atR (rdW W (ms_mem msB3)) copy C)
    by (apply (abytes_atR_kept_r (rdW W mem)); [intros x Hx; apply KB3; lia | exact HCB]).
  pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [] ly S W (ms_mem msB3) mdB3 k (ms_regs msB3) (-256) HJ HspT eq_refl ltac:(lia) ltac:(lia)
    ltac:(rewrite WS; lia) HraT P3' P4') as HPREc.
  destruct (ws_cursor cx q ly S W (ms_regs msB3) (ms_mem msB3) mdB3 copy C (i + s) (proj1 HJ) Hcin
    ltac:(rewrite HspT; lia) HCB3 HCL HLN ltac:(lia) ltac:(intros t Ht; apply HCF; lia)) as (Hstr & Hrd & Htl & Hm8).
  destruct (ws_sep cx ly S W (ms_regs msB3) (ms_mem msB3) mdB3 k HB0 HJ HPREc) as (Hsstr & Hsrd & Hstl & Hrom & Hsm8).
  eapply SRr_bind.
  { exact (aj_strcspn_at_loc W (ms_regs msB3) (ms_mem msB3) LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx)
      (x_mem cx) (x_md cx) [] ly S mdB3 k (copy + Z.of_nat (i + s)) 0x210a0 (skipn (i + s) (q_LN cx q))
      SlotWords.SEPS (-256) (getr (ms_regs msB3) 1) HJ P10' P11' ltac:(lia) ltac:(lia) HspT eq_refl ltac:(lia)
      ltac:(rewrite WS, Hes; lia) P3' P4' eq_refl HraT Hstr Hsstr Hrd Hsrd Hm8 Hsm8 Htl Hstl Hrom). }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3 & HK3).
  rewrite P1. change (BASE + 960) with (BASE + AW_S2).
  assert (K3 : forall a, 0 <= a < x_sp0 cx - 256 - 2 * ESTACK -> rdW W mem3 a = rdW W (ms_mem msB3) a).
  { intros a Ha. exact (HK3 a ltac:(lia) ltac:(lia) ltac:(tauto)). }
  assert (RK3 : forall r, In r WS_KEEP -> getr regs3 r = getr regs r)
    by (intros r Hr; rewrite (ws_pres_keep _ _ HP3 r Hr); exact (RK r Hr)).
  assert (KM3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 - 2 * ESTACK <= a < x_sp0 cx - 256) ->
    ~ (copy <= a < copy + q_L0 cx q + 1) -> ~ (arr <= a < arr + SlotSpec.arr_size (q_L0 cx q)) ->
    rdW W mem3 a = rdW W mem a)
    by (intros a Ha Hs1 _ Hn; rewrite (HK3 a Ha ltac:(lia) ltac:(tauto)); apply KB3; [exact Ha | lia]).
  pose proof (ws_inv_kept cx q ly S W regs mem md k acc text copy arr regs3 mem3 md3 HI HJ3 RK3 KM3) as HI3.
  destruct HI3 as (HC3 & Hrec3 & Hws3 & R24' & R23' & R25' & R19' & R20' & HS5' & HS11' & HWN').
  apply (HS2 cx q ly S W regs3 mem3 md3 k acc text copy arr i s kw C wp Hm HFP0 HC3 Hrec3 Hws3 R24' R23' R25').
  + ws_reg HP3 21 P21 E21.
  + ws_reg HP3 18 P18 E18.
  + ws_reg HP3 26 P26 E26.
  + ws_reg HP3 27 P27 E32.
  + exact HQ3.
  + exact R19'.
  + exact R20'.
  + exact HS5'.
  + exact HS11'.
  + exact Hnm.
  + exact Hk.
  + exact Hwp.
  + exact Hkw.
  + exact HWA.
  + apply (abytes_atR_kept_r (rdW W (ms_mem msB3))); [intros x Hx; apply K3; lia | exact HCB3].
  + exact HCL.
  + exact HCF.
  + exact HFD.
  + exact HWN'.
  + exact Es.
  + exact Hlt.
  + apply ws_arr_snoc.
    * apply (ws_arr_kept (rdW W mem)); [intros x Hx; rewrite (K3 x) by lia; apply KB3; lia | exact HAA].
    * rewrite Hwp. apply (ws_rdword_kept (rdW W (ms_mem msB3))); [intros x Hx; apply K3; lia | exact Hslot].
Qed.

(* the first half of a round of the split loop, from its head to 0x868a4 or to the exit 0x8692c *)
Lemma aw_seg_S1 : forall m nm, AW_S2_stmt B MT m nm -> AW_E_stmt B MT m -> AW_S_stmt B MT m nm.
Proof. intros m nm H2 HE. exact (ws_A m nm (ws_B m nm H2 HE)). Qed.

End e.
End f.
End d.
