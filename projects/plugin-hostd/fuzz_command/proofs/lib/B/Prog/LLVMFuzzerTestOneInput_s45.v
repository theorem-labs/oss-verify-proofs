(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first half of a round of the split loop of LLVMFuzzerTestOneInput's inlined words_of on the ASan+UBSan image B (plugin-hostd/fuzz_command, 0x868e4 .. 0x8698c: the *t test, the strspn wrapper call, its UBSan pointer-overflow test, the exit when only separators are left, w.n + 1 and &w.v[n] behind their UBSan tests, the 8-byte check and the store of the word's address, the strcspn wrapper call), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s45.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (a symbolic seed at a point of the function and the runs from it) and A/ACh2.v:122-290 (a call and back, with the facts carried over it). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaArt PaSB CmdGlob PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01 LLVMFuzzerTestOneInput_s40
LLVMFuzzerTestOneInput_s49.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the seats of the two stretches (listing offsets from BASE = 0x86530) ---- *)
(* 0x868fc: the strspn wrapper has returned; the run to the strcspn wrapper starts here *)
Definition WS_B : Z := 0x3cc.
(* s9 holds the shadow base all through the loop *)
Definition WSx : sv := SOff 25 0.
Definition WSspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
(* the registers neither stretch nor the wrapper calls change, which the segment statements name (lt_frame,
   lt_body, lt_msg_regs) *)
Definition WS_KEEP : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]%bv.
(* 0x868e4 .. jal strspn: the byte at s7 = copy + i is atom 32 (no inline check: the head's byte was checked
   before the head) *)
Definition ws_atomsA : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (25%nat, mkAF LT_SB LT_SB 0); (23%nat, PTR 0); (32%nat, mkAF 0 255 0) ].
Definition ws_rA : smem := [ YP09.mkRegion (Some 23%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
(* 0x868fc .. jal strcspn: s7 + a0 is the cursor past the separators (atom 32), its byte is atom 33; 136(sp) holds
   arr (atom 34) and 144(sp) w.n = kw (atom 35, written to kw + 1); &w.v[kw] = arr + 8 kw is atom 36, the 8-byte
   check reads its shadow and the store writes it *)
Definition ws_aliasB : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 23 0) (SOff 10 0), SOff 32 0);
    (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 3)), SOff 36 0) ].
Definition ws_atomsB : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (25%nat, mkAF LT_SB LT_SB 0); (23%nat, PTR 0); (10%nat, mkAF 0 8192 0);
    (32%nat, PTR 0); (33%nat, mkAF 0 255 0); (34%nat, PTR 4); (35%nat, mkAF 0 4097 0); (36%nat, PTR 3) ].
Definition ws_rframe : YP09.region :=
  YP09.mkRegion (Some 2%nat) 136 148 144 148
    [YP09.mkChunk 136 (CVal 8 (SOff 34 0)); YP09.mkChunk 144 (CVal 4 (SOff 35 0))].
Definition ws_rB : smem := [ YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
  ws_rframe; YP09.mkRegion (Some 36%nat) 0 8 0 8 [] ].
Definition ws_shB : list shent := [ mkSHE 36 0 8 ].

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
(* the sum of two register atoms, and arr + (kw << 3) *)
Lemma ws_add_atoms : forall E (n1 n2 : nat) v1 v2,
  ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 -> 0 <= v1 -> 0 <= v2 -> v1 + v2 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (v1 + v2).
Proof.
intros E n1 n2 v1 v2 H1 H2 Hv1 Hv2 Hs.
rewrite (denot_lit_U E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0))). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n1 v1 H1 ltac:(lia)), (U_atom E n2 v2 H2 ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma ws_add_sll3 : forall E (n1 n2 : nat) v1 v2,
  ew E n1 = Z_to_bv 64 v1 -> ew E n2 = Z_to_bv 64 v2 -> 0 <= v1 -> 0 <= v2 -> v1 + 8 * v2 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n1 0) (SAlu ALU_SLL (SOff n2 0) (SLit 3))) = Z_to_bv 64 (v1 + 8 * v2).
Proof.
intros E n1 n2 v1 v2 H1 H2 Hv1 Hv2 Hs.
rewrite (denot_lit_U E (SAlu ALU_ADD (SOff n1 0) (SAlu ALU_SLL (SOff n2 0) (SLit 3)))). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
rewrite (U_atom E n1 v1 H1 ltac:(lia)), (U_atom E n2 v2 H2 ltac:(lia)).
rewrite (zcanon_id (v2 * 8)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
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
(* a 4-byte field written through the symbolic memory, read back through the ASan view *)
Lemma ws_aval_of_val : forall segs H (mem : word -> option byte) a n v,
  val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte, YG0f.le_byte. apply Z.mod_mod. lia.
Qed.
(* the two blocks copy and arr do not overlap (kept opaque: lia splits every disjunction it is given) *)
Definition ws_apart (c n a m : Z) : Prop := c + n <= a \/ a + m <= c.
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
(* an atom of the seat, read in the env of a later state of the same run *)
Ltac ws_ew F := cbn [ew ewset havoc extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add]; exact F.

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
(* the length of the line's copy: strnlen's answer is at most the message's length, at most 8192 *)
Lemma ws_L0_le : forall cx q, q_L0 cx q <= 8192.
Proof.
intros cx q. rewrite q_L0_U. unfold q_U, Verbs.upto0.
assert (H1 : forall p (l : list byte), (length (Verbs.upto p l) <= length l)%nat).
{ intros p l. induction l as [|b l IH]; cbn [Verbs.upto length]; [lia|]. destruct (p b); cbn [length]; lia. }
assert (H3 : lt_len (x_pl cx) (x_n cx) (q_r q) <= 8192) by (unfold lt_len, SlotSpec.msg_len; apply Z.le_min_r).
assert (H2 : Z.of_nat (length (q_D cx q)) <= 8192).
{ unfold q_D, lt_D. rewrite length_firstn.
  generalize (length (skipn (Z.to_nat (SlotSpec.hdr_n (q_r q))) (lt_rest (x_pl cx) (x_n cx) (q_r q)))).
  generalize (lt_len (x_pl cx) (x_n cx) (q_r q)) H3. intros z Hz u. lia. }
pose proof (H1 (fun b : byte => (bv_unsigned b =? 0)%Z) (q_D cx q)) as H4.
remember (length (Verbs.upto (fun b : byte => (bv_unsigned b =? 0)%Z) (q_D cx q))) as v eqn:Ev.
remember (length (q_D cx q)) as u eqn:Eu. clear Ev Eu H1 H3. lia.
Qed.

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
(* the frame words 136(sp) (arr) and 144(sp) (w.n, 4 bytes, written) *)
Lemma ws_rg_frame : forall E (W : world SEGS) mem (sp arr kw : Z),
  ew E 2 = Z_to_bv 64 sp -> ew E 34 = Z_to_bv 64 arr -> ew E 35 = Z_to_bv 64 kw ->
  0 <= sp -> sp + 148 <= 2 ^ 64 -> 0 <= arr < 2 ^ 64 -> 0 <= kw < 2 ^ 32 ->
  (forall a, sp + 144 <= a < sp + 148 -> apresent (w_H W) mem a) ->
  rdword (rdW W mem) (sp + 136) = Some arr -> aval_mem (rdW W mem) (sp + 144) 4 kw ->
  region_ok SEGS E (mrestrict (w_H W) mem) ws_rframe.
Proof.
intros E W mem sp arr kw H2 H34 H35 Hs0 Hs1 Ha Hk Hp Hrd Hwn. unfold region_ok, ws_rframe.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H2, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply Hp; lia|].
constructor; [|constructor; [|constructor]].
- apply (chunk_ok_val SEGS E _ sp 136 8 (SOff 34 0) arr);
    [cbn [sv_denot]; rewrite H34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS _ _ _ _ Hrd).
- apply (chunk_ok_val SEGS E _ sp 144 4 (SOff 35 0) kw);
    [cbn [sv_denot]; rewrite H35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
  apply val_mem_of_aval. exact Hwn.
Qed.

(* the stretch from 0x868fc writes only w.n (144(sp)) and arr[kw]: each of its runs keeps the memory outside those
   two windows *)
Lemma ws_kept_B : forall E rs H (m m' : word -> option byte) sp a8,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  windows rs = [(Some 32%nat, 0, 0); (Some 2%nat, 144, 148); (Some 36%nat, 0, 8)] ->
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 36) = a8 ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 144 <= a < sp + 148) -> ~ (a8 <= a < a8 + 8) ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' sp a8 HFr Hw H2 H36 a Ha Hn1 Hn2.
apply (kept_of_frame (segs := SEGS) E rs H m m' (fun a => (sp + 144 <= a < sp + 148) \/ (a8 <= a < a8 + 8)) HFr);
  [| exact Ha | intros [Hq | Hq]; [exact (Hn1 Hq) | exact (Hn2 Hq)]].
intros b wlo whi a' Hin Hr. rewrite Hw in Hin.
destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-; cbn [base_val] in Hr.
- lia.
- left. rewrite H2 in Hr. lia.
- right. rewrite H36 in Hr. lia.
Qed.
(* w.n and the pointer slot, read back from a seat's region through the ASan view *)
Lemma ws_wn_of_region : forall E (W : world SEGS) m sp cs e v,
  region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) 136 148 144 148 cs) ->
  bv_unsigned (ew E 2) = sp -> In (YP09.mkChunk 144 (CVal 4 e)) cs ->
  bv_unsigned (sv_denot E e) = v -> 0 <= v < 2 ^ 32 ->
  aval_mem (rdW W m) (sp + 144) 4 v.
Proof.
intros E W m sp cs e v Hreg H2 Hin Hv Hr.
pose proof (field_of_region_any E _ 2 sp cs 136 148 144 148 144 4%N e Hreg H2 Hin ltac:(cbn; lia)) as Hf.
rewrite Hv in Hf. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Hf. rewrite Z.mod_small in Hf by lia.
exact (ws_aval_of_val SEGS (w_H W) m _ 4 v Hf).
Qed.
Lemma ws_slot_of_region : forall E (W : world SEGS) m a8 cs e v,
  region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 36%nat) 0 8 0 8 cs) ->
  bv_unsigned (ew E 36) = a8 -> In (YP09.mkChunk 0 (CVal 8 e)) cs ->
  bv_unsigned (sv_denot E e) = v -> 0 <= v < 2 ^ 64 ->
  rdword (rdW W m) a8 = Some v.
Proof.
intros E W m a8 cs e v Hreg H36 Hin Hv Hr.
pose proof (field_of_region_any E _ 36 a8 cs 0 8 0 8 0 8%N e Hreg H36 Hin ltac:(cbn; lia)) as Hf.
rewrite Hv in Hf. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Hf. rewrite Z.mod_small, Z.add_0_r in Hf by lia.
exact (rdword_of_val_mem SEGS (w_H W) m a8 v Hf Hr).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the runtime entries this stretch calls: the statement's own hypotheses, word for word
   (LLVMFuzzerTestOneInput_c.v:217-218) *)
Hypothesis ASTRSPN : forall fx0 : YK11.FPState,
  @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa6bf8 0x604158.
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState,
  @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
(* the per-binary facts, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the two wrapper calls: PaArt.v's aj_art_at, the guard cells from CmdRecFacts' cmd_rec_cells ---- *)
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
apply (aj_art_at (fx := fx) SEGS B LAWS pa_segs_low (cmd_cf_env SEGS B LAWS HB IMG) (2 * ESTACK) (fun _ => False)
  (SIG CS___interceptor_trampoline_strspn) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
  (fun regs2 _ => getr regs2 10 = w64 (Z.of_nat (PSpn.spn_len sy sx)))
  HJ Hsp Hal Hneg ltac:(lia) Hbud Hra (fun a F => False_ind _ F)).
apply (ASTRSPN fx lyc Sc W regsT memT mdc x y sx sy HG); try assumption.
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
apply (aj_art_at (fx := fx) SEGS B LAWS pa_segs_low (cmd_cf_env SEGS B LAWS HB IMG) (2 * ESTACK) (fun _ => False)
  (SIG CS___interceptor_trampoline_strcspn) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
  (fun regs2 _ => getr regs2 10 = w64 (Z.of_nat (PCspn.cspn_len sy sx)))
  HJ Hsp Hal Hneg ltac:(lia) Hbud Hra (fun a F => False_ind _ F)).
apply (ASTRCSPN fx lyc Sc W regsT memT mdc x y sx sy HG); try assumption.
apply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg
  ltac:(lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp].
Qed.

(* ---- what holds at every point of the stretch: the parts of AW_S_stmt that neither the runs nor the calls
   change ---- *)
Definition ws_inv (cx : lcx) (q : awm) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc text copy arr : Z) :
  Prop :=
  aw_ctx B MT cx q ly S W regs mem md k acc /\ aw_rec B cx q ly S W mem (aw_blocks cx q text copy arr) /\
  aw_wslots cx (rdW W mem) text copy arr.

Lemma ws_inv_facts : forall cx q ly S W regs mem md k acc text copy arr,
  ws_inv cx q ly S W regs mem md k acc text copy arr ->
  AR SEGS B ly S W mem md /\
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k /\
  In (copy, q_L0 cx q + 1) (ablocks B ly S) /\ In (arr, SlotSpec.arr_size (q_L0 cx q)) (ablocks B ly S) /\
  ~ In (copy, q_L0 cx q + 1) (x_bl0 B cx) /\ ~ In (arr, SlotSpec.arr_size (q_L0 cx q)) (x_bl0 B cx) /\
  ws_apart copy (q_L0 cx q + 1) arr (SlotSpec.arr_size (q_L0 cx q)) /\
  spZ regs = x_sp0 cx - 256 /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  alloc_ceiling <= x_sp0 cx - LTOI_STK /\ x_sp0 cx mod 16 = 0 /\ x_sp0 cx <= 2 ^ 47 /\
  lt_base B MT cx /\ 0 <= q_L0 cx q <= 8192 /\
  (length (q_LN cx q) <= Z.to_nat (q_L0 cx q))%nat /\
  copy mod 16 = 0 /\ 4096 <= copy /\ copy + q_L0 cx q + 1 <= alloc_ceiling /\
  arr mod 16 = 0 /\ 4096 <= arr /\ arr + SlotSpec.arr_size (q_L0 cx q) <= alloc_ceiling /\
  in_app copy (q_L0 cx q + 1) /\ in_app arr (SlotSpec.arr_size (q_L0 cx q)) /\
  (forall a, copy <= a < copy + q_L0 cx q + 1 -> apresent (w_H W) mem a) /\
  (forall a, arr <= a < arr + SlotSpec.arr_size (q_L0 cx q) -> apresent (w_H W) mem a) /\
  (forall a, x_sp0 cx - LTOI_STK <= a < x_sp0 cx -> apresent (w_H W) mem a).
Proof.
intros cx q ly S W regs mem md k acc text copy arr HI.
destruct HI as (((HB0 & ((HJ & Hsp & Hgp & Htp & Hsv) & HSl & _) & HMR) & Hbud) & Hrec & _).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSP & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HB0 as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
destruct Hrec as (_ & _ & _ & _ & _ & HP).
assert (HL0 : 0 <= q_L0 cx q) by (rewrite q_L0_U; lia).
pose proof (ws_L0_le cx q) as HL8.
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
split; [exact Hcn0|]. split; [exact Han0|]. split; [unfold ws_apart; lia|].
split; [rewrite Hsp; unfold x_sp1, x_sp0, LT_FRAME; lia|].
split; [rewrite Hgp; exact Hgp0|]. split; [rewrite Htp; exact Htp0|].
split; [unfold x_sp0, LTOI_STK in *; lia|]. split; [exact Hal16|]. split; [lia|].
split; [exact HB0|]. split; [lia|]. split; [exact HLN|].
split; [exact Hc16|]. split; [exact Hc4|]. split; [lia|].
split; [exact Ha16|]. split; [exact Ha4|]. split; [lia|].
split; [exact Hcapp|]. split; [exact Haapp|].
split; [intros a Ha; exact (proj1 (Hcpres a ltac:(lia)))|]. split; [intros a Ha; exact (proj1 (Hapres a ltac:(lia)))|].
exact HSP.
Qed.

(* the saved registers, the ten words and the host word are kept when the frame's bytes are *)
Lemma ws_saved_kept : forall cx (rd rd' : reader),
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rd' a = rd a) -> lt_saved cx rd -> lt_saved cx rd'.
Proof.
intros cx rd rd' Hk HS i r Hi.
assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
change (length LT_SAVED) with 13%nat in Hi13.
apply (ws_rdword_kept rd rd'); [intros x Hx; apply Hk; lia | exact (HS i r Hi)].
Qed.
Lemma ws_slots_kept : forall cx (rd rd' : reader),
  (forall a, x_sp1 cx <= a < x_sp1 cx + 112 -> rd' a = rd a) -> lt_slots cx rd -> lt_slots cx rd'.
Proof.
intros cx rd rd' Hk HS o v Hin.
assert (HF : forallb (fun ov => (0 <=? fst ov) && (fst ov <=? 104)) LT_SLOTS = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HF (o, v) Hin) as Ho. cbn [fst] in Ho.
apply andb_prop in Ho as [Ho1 Ho2]. apply Z.leb_le in Ho1. apply Z.leb_le in Ho2.
apply (ws_rdword_kept rd rd'); [intros x Hx; apply Hk; lia | exact (HS o v Hin)].
Qed.
(* a byte of the recorder's area is a byte below the allocator's ceiling, at 0 or above *)
Lemma ws_area_low : forall cx q ly S (W : world SEGS) mem md extra a,
  AR SEGS B ly S W mem md -> aw_rec B cx q ly S W mem extra -> aw_area (q_O1 q) a -> 0 <= a < alloc_ceiling.
Proof.
intros cx q ly S W mem md extra a HAR Hrec Ha.
assert (Hlo : a < alloc_ceiling).
{ destruct (Z_lt_le_dec a alloc_ceiling) as [Hl|Hl]; [exact Hl|].
  exfalso. exact (aw_area_stack B LAWS cx q ly S W mem md extra a HAR Hrec Hl Ha). }
split; [|exact Hlo].
destruct Hrec as (_ & _ & _ & _ & _ & HP).
destruct Ha as [Hg | [Hs | [Hq | (r & Hr & Hra)]]].
- unfold A_G_REC, REC_SIZE in Hg. lia.
- unfold A_REC_SPILL, SC_SIZE in Hs. lia.
- unfold A_G_QUITTING in Hq. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p k] & <- & Hpk). cbn [fst snd] in Hra.
  assert (Hin : In (p, k) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hpk. }
  destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (_ & Hp4 & _). lia.
Qed.

(* the stretch's writes (the wrapper's scratch below the frame, w.n, the copy and pointer blocks) keep ws_inv *)
Lemma ws_inv_kept : forall cx q ly S W regs mem md k acc text copy arr regs' mem' md',
  ws_inv cx q ly S W regs mem md k acc text copy arr ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem' md' k ->
  (forall r, In r WS_KEEP -> getr regs' r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 - 2 * ESTACK <= a < x_sp0 cx - 256) ->
     ~ (x_sp0 cx - 112 <= a < x_sp0 cx - 108) ->
     ~ (copy <= a < copy + q_L0 cx q + 1) -> ~ (arr <= a < arr + SlotSpec.arr_size (q_L0 cx q)) ->
     rdW W mem' a = rdW W mem a) ->
  ws_inv cx q ly S W regs' mem' md' k acc text copy arr.
Proof.
intros cx q ly S W regs mem md k acc text copy arr regs' mem' md' HI HJ' HR HK.
pose proof (ws_inv_facts cx q ly S W regs mem md k acc text copy arr HI) as
  (HAR & HJ & Hcin & Hain & Hcn0 & Han0 & Hdis & Hsp & Hgp & Htp & Hceil & Hal16 & H47 & HB0 & HL0 & HLN &
   Hc16 & Hc4 & Hcc & Ha16 & Ha4 & Hac & Hcapp & Haapp & Hcpres & Hapres & HSP).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_value as [HAC1 _].
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : LTOI_STK = 32768) by reflexivity.
destruct HI as (((HB0' & ((_ & Hsp0 & Hgp0 & Htp0 & Hsv) & HSl & R8 & R9 & R18 & R25 & R26 & R27 & Hm32) &
  (Hr & R19 & R20 & R21 & R22 & Hst & Hho & Hh)) & Hbud) & Hrec & Hws).
assert (KF : forall a, x_sp0 cx - 256 <= a < x_sp0 cx - 112 \/ x_sp0 cx - 108 <= a < x_sp0 cx ->
  rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK; lia. }
assert (Hs1 : x_sp1 cx = x_sp0 cx - 256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
assert (E2 : spZ regs' = spZ regs) by (unfold spZ; rewrite (HR 2%bv) by ws_inkeep; reflexivity).
unfold ws_inv, aw_ctx, aw_ctx0, lt_body, lt_frame, lt_msg_regs.
rewrite (HR 8%bv), (HR 9%bv), (HR 18%bv), (HR 25%bv), (HR 26%bv), (HR 27%bv), (HR 19%bv), (HR 20%bv), (HR 21%bv),
  (HR 22%bv), (HR 3%bv), (HR 4%bv) by ws_inkeep.
split.
{ split; [|exact Hbud].
  split; [exact HB0'|].
  split.
  { split.
    { split; [exact HJ'|]. split; [rewrite E2; exact Hsp0|]. split; [exact Hgp0|]. split; [exact Htp0|].
      apply (ws_saved_kept cx (rdW W mem)); [intros a Ha; apply KF; lia | exact Hsv]. }
    split; [apply (ws_slots_kept cx (rdW W mem)); [intros a Ha; apply KF; rewrite Hs1 in Ha; lia | exact HSl]|].
    split; [exact R8|]. split; [exact R9|]. split; [exact R18|]. split; [exact R25|]. split; [exact R26|].
    split; [exact R27|]. exact Hm32. }
  split; [exact Hr|]. split; [exact R19|]. split; [exact R20|]. split; [exact R21|]. split; [exact R22|].
  split; [exact Hst|]. split; [exact Hho|].
  apply (ws_rdword_kept (rdW W mem)); [intros x Hx; apply KF; unfold LT_HOSTB in Hx; rewrite Hs1 in Hx; lia | exact Hh]. }
split.
{ apply (aw_rec_kept B cx q ly S W mem mem' _ Hrec).
  intros a Ha.
  assert (Ha' : aw_area (q_O1 q) a) by exact Ha.
  pose proof (ws_area_low cx q ly S W mem md _ a HAR Hrec Ha') as [Ha0 Hac0].
  apply HK; [lia | lia | lia | |].
  - intros Hc. apply (aw_area_words B LAWS cx q ly S W mem md text copy arr copy (q_L0 cx q + 1) a HAR Hrec
      ltac:(rewrite aw_blocks_eq; right; left; reflexivity) ltac:(rewrite ws_req by lia; lia) Ha').
  - intros Hc. apply (aw_area_words B LAWS cx q ly S W mem md text copy arr arr (SlotSpec.arr_size (q_L0 cx q)) a HAR Hrec
      ltac:(rewrite aw_blocks_eq; right; right; left; reflexivity)
      ltac:(rewrite ws_req by (unfold SlotSpec.arr_size; pose proof (Z.div_pos (q_L0 cx q) 2 ltac:(lia) ltac:(lia)); lia); lia) Ha'). }
destruct Hws as (W1 & W2 & W3).
split; [apply (ws_rdword_kept (rdW W mem)); [intros x Hx; apply KF; unfold LT_W in Hx; rewrite Hs1 in Hx; lia | exact W1]|].
split; [apply (ws_rdword_kept (rdW W mem)); [intros x Hx; apply KF; unfold LT_W in Hx; rewrite Hs1 in Hx; lia | exact W2]|].
apply (ws_rdword_kept (rdW W mem)); [intros x Hx; apply KF; unfold LT_W in Hx; rewrite Hs1 in Hx; lia | exact W3].
Qed.

(* ---- the read-only facts the two wrappers ask of the set " \t" (0x210e0) and of the image ---- *)
Lemma ws_PG_static : forall a, inFP cmd_PG a -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a (r & Hr & Hlo & Hhi). apply Exists_exists.
assert (HF : forallb (fun r => existsb (fun z => (fst z <=? fst r) && (snd r <=? fst z + snd z)) TFIB_PROG_STATIC)
  cmd_PG = true) by (vm_compute; reflexivity).
rewrite forallb_forall in HF. specialize (HF r Hr). apply existsb_exists in HF as (z & Hz & Hzr).
apply andb_prop in Hzr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists z. split; [exact Hz | unfold in_zr; lia].
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
  astr_at SEGS W mem 0x210e0 SlotWords.SEPS /\
  aread_ok SEGS (2 * ESTACK) W regs mem 0x210e0 (astr_len SlotWords.SEPS + 1) /\
  atail_vis SEGS W mem (0x210e0 + astr_len SlotWords.SEPS) /\ rt_rom_view SEGS B W mem /\
  amem_range 0x210e0 (astr_len SlotWords.SEPS + 8).
Proof.
intros cx ly S W regs mem md k HB0 HJ HPRE.
pose proof (proj1 HJ) as HAR.
pose proof (ws_aro cx ly S W mem md k HB0 HJ) as HRO.
assert (Hin : In (0x210e0, RO_lit_210e0) cmd_ro_list) by (unfold cmd_ro_list; repeat (first [left; reflexivity | right])).
pose proof (cmd_ro_obj_bytes SEGS B LAWS HB IMG ly S W mem md _ HAR HRO Hin) as HL. cbn [fst snd] in HL.
assert (HS : abytes_atR (rdW W mem) 0x210e0 (SlotWords.SEPS ++ [Z_to_bv 8 0])) by exact HL.
split; [apply (astr_atR_view SEGS); split; [exact HS|] |].
{ intros Hz. cbn [SlotWords.SEPS In] in Hz.
  destruct Hz as [Hz | [Hz | []]]; apply (f_equal (@bv_unsigned 8)) in Hz; vm_compute in Hz; discriminate. }
split; [|split; [|split]].
- change (astr_len SlotWords.SEPS + 1) with 3.
  apply (cmd_aread_ok_img SEGS B LAWS HB (2 * ESTACK) ly S W regs mem md 0x210e0 3 HPRE); [|vm_compute; reflexivity].
  intros a Ha. replace a with (0x210e0 + Z.of_nat (Z.to_nat (a - 0x210e0))) by lia.
  rewrite (HS (Z.to_nat (a - 0x210e0))) by (cbn [length app SlotWords.SEPS]; lia). discriminate.
- change (0x210e0 + astr_len SlotWords.SEPS) with 0x210e2.
  apply (cmd_tail_vis_at SEGS B LAWS HB IMG ly S W mem md 0x210e2 HAR). apply In_of_existsb. vm_compute. reflexivity.
- exact (cmd_rom_view_on SEGS B LAWS HB IMG CMD_RLO CMD_RHI W mem HRO).
- (* the set " \t" is a .rodata literal: low band (a Theorem Labs lane's PASS4-REFIT.md E.0.1) *)
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
     (a Theorem Labs lane's PASS4-REFIT.md E.0.1, kit PaLibH.amem8_of_block) *)
  rewrite Hlen. apply (amem8_of_block SEGS B LAWS ly S W mem md copy (q_L0 cx q + 1) (copy + Z.of_nat j)
    (Z.of_nat (length (q_LN cx q)) - Z.of_nat j) HAR Hin); [lia | rewrite ws_req by lia; lia | lia].
Qed.

(* ---- 0x868fc: the strspn wrapper has returned s = aw_spn (skipn i LN); s7 = copy + i; memory is the head's
   below the wrapper's scratch ---- *)
Definition WS_B_stmt (m nm : nat) : Prop :=
  forall cx q ly S W regs mem md k acc text copy arr (i kw : nat) (C : list byte) (wp : list Z),
  q_m q = m -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  ws_inv cx q ly S W regs mem md k acc text copy arr ->
  getr regs 23 = w64 (copy + Z.of_nat i) ->
  getr regs 10 = w64 (Z.of_nat (aw_spn (skipn i (q_LN cx q)))) ->
  aw_wn cx (rdW W mem) (Z.of_nat kw) ->
  nm = (length (q_LN cx q) - i)%nat -> (i <= length (q_LN cx q))%nat -> (2 * kw <= i)%nat ->
  length wp = kw -> (kw <= length (q_ws cx q))%nat ->
  Verbs.words_acc [] (skipn i (q_LN cx q)) = skipn kw (q_ws cx q) ->
  abytes_atR (rdW W mem) copy C -> length C = Z.to_nat (q_L0 cx q + 1) ->
  (forall j, (i <= j <= length (q_LN cx q))%nat -> nth_error C j = nth_error (q_LN cx q ++ [Z_to_bv 8 0]) j) ->
  aw_arr (rdW W mem) arr wp -> aw_found copy (q_ws cx q) C wp i ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + WS_B)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

(* 0x868e4 .. jal strspn: the *t test (beqz to 0x86a04 when the line is used up), a1 = " \t", a0 = s7; the call
   and back at 0x868fc *)
Lemma ws_A : forall m nm, WS_B_stmt m nm -> AW_E_stmt B MT m -> AW_S_stmt B MT m nm.
Proof.
intros m nm HB2 HE cx q ly S W regs mem md k acc text copy arr i kw C wp Hm HFP0 HC Hrec Hws R23 HWN Hnm Hi Hk Hwp
  Hkw HWA HCB HCL HCF HAA HFD.
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_value as [[HAC1 HAC2] _].
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : LTOI_STK = 32768) by reflexivity.
assert (HI : ws_inv cx q ly S W regs mem md k acc text copy arr) by exact (conj HC (conj Hrec Hws)).
pose proof (ws_inv_facts cx q ly S W regs mem md k acc text copy arr HI) as
  (HAR & HJ & Hcin & Hain & Hcn0 & Han0 & Hdis & Hsp & Hgp & Htp & Hceil & Hal16 & H47 & HB0 & HL0 & HLN &
   Hc16 & Hc4 & Hcc & Ha16 & Ha4 & Hac & Hcapp & Haapp & Hcpres & Hapres & HSP).
pose proof HB0 as (_ & _ & _ & HOBJ & _).
assert (R25 : getr regs 25 = w64 LT_SB) by (destruct HC as ((_ & (_ & _ & _ & _ & _ & R25 & _) & _) & _); exact R25).
unfold w64 in *.
assert (Hs1 : x_sp1 cx = x_sp0 cx - 256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
assert (HAK : 8 * Z.of_nat kw <= SlotSpec.arr_size (q_L0 cx q)).
{ unfold SlotSpec.arr_size. pose proof (Z.div_mod (q_L0 cx q) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (q_L0 cx q) 2 ltac:(lia)). lia. }
(* the byte at i *)
assert (HNZ : forall b, In b (q_LN cx q) -> bv_unsigned b <> 0) by (intros b Hb; exact (SlotWords.sw_line_nz (q_D cx q) b Hb)).
destruct (SlotWords.sw_nth_z (q_LN cx q) i HNZ Hi) as (b0 & Eb0 & Hb0z).
assert (HC0 : nth_error C i = Some b0) by (rewrite HCF by lia; exact Eb0).
assert (HCL0 : (i < length C)%nat) by (apply nth_error_Some; rewrite HC0; discriminate).
assert (Hrd0 : rdW W mem (copy + Z.of_nat i) = Some (bv_unsigned b0)).
{ rewrite (HCB i HCL0). rewrite (nth_error_nth _ _ _ HC0). reflexivity. }
pose proof (bv_unsigned_in_range 8 b0) as Rb0. change (bv_modulus 8) with 256 in Rb0.
(* the seat at 0x868e4 *)
pose proof (ws_E_reg regs [Z_to_bv 64 (bv_unsigned b0)]) as EEo.
assert (E2 : ew (ws_E regs [Z_to_bv 64 (bv_unsigned b0)]) 2 = Z_to_bv 64 (x_sp0 cx - 256)).
{ rewrite (EEo 2%nat 2%bv eq_refl). apply bv_eq. rewrite unsigned_lit_small by lia. exact Hsp. }
assert (E3 : ew (ws_E regs [Z_to_bv 64 (bv_unsigned b0)]) 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew (ws_E regs [Z_to_bv 64 (bv_unsigned b0)]) 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E25 : ew (ws_E regs [Z_to_bv 64 (bv_unsigned b0)]) 25 = Z_to_bv 64 LT_SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E23 : ew (ws_E regs [Z_to_bv 64 (bv_unsigned b0)]) 23 = Z_to_bv 64 (copy + Z.of_nat i))
  by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E32 : ew (ws_E regs [Z_to_bv 64 (bv_unsigned b0)]) 32 = Z_to_bv 64 (bv_unsigned b0))
  by exact (ws_E_extra regs _ 0 ltac:(lia)).
pose proof (ws_E_img regs [Z_to_bv 64 (bv_unsigned b0)]) as HEI.
pose proof (ws_E_agree regs [Z_to_bv 64 (bv_unsigned b0)]) as HAE.
pose proof (ws_ew_obj (ws_E regs [Z_to_bv 64 (bv_unsigned b0)]) 5 0x210e0 HOBJ HEI ltac:(vm_compute; lia) eq_refl
  ltac:(unfold A_OBJ, A_LIM; lia)) as E246.
change (A_OBJ 5) with 246%nat in E246.
remember (ws_E regs [Z_to_bv 64 (bv_unsigned b0)]) as E eqn:HE0.
assert (HRS : Forall (region_ok SEGS E (mrestrict (w_H W) mem)) ws_rA).
{ unfold ws_rA. constructor; [|constructor].
  apply (ws_rg_byte E W mem 23 32 (copy + Z.of_nat i) (bv_unsigned b0) E23 E32); [lia | lia | lia | exact Hrd0]. }
assert (HAT : atoms_ok E ws_atomsA).
{ cbn [ws_atomsA atoms_ok]. unfold PTR.
  split; [apply (ws_afact _ 2 (x_sp0 cx - 256) _ _ _ E2); [lia | lia | change (2 ^ 4) with 16; rewrite Zminus_mod, Hal16; reflexivity | lia]|].
  split; [apply (ws_afact _ 25 LT_SB _ _ _ E25); [unfold LT_SB; lia | unfold LT_SB; lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (ws_afact _ 23 _ _ _ _ E23); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (ws_afact _ 32 _ _ _ _ E32); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  exact I. }
pose proof (ws_seat W regs mem AW_S [Z_to_bv 64 (bv_unsigned b0)] ws_rA ws_atomsA [] eq_refl) as HS.
rewrite <- HE0 in HS. specialize (HS HRS (conj I I) HAT I).
assert (SHOK : sh_ok SEGS WSx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
(* the run to the *t test (0x868e4 .. 0x868e8) *)
paj_run_tok RUN HS HJ SHOK WSspan.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdA1 := d) in *; clearbody mdA1 end.
lazymatch type of HS with context [restrict _ ?mm] => rename mm into msA1 end.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem msA1)) |- _ =>
  assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem msA1) a = rdW W mem a)
  by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' as [Hq0 | []]; injection Hq0 as <- <- <-; lia
      | exact Ha | intros F; exact F ])
end.
psrr_branch_tok RUN BR HS SHOK WSspan.
- (* the byte is the NUL: the line is used up (i = |LN|), every word found; beqz -> 0x86a04 *)
  assert (Hb0 : bv_unsigned b0 = 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite U_SOff, U_lit in Hc by lia.
    cbn [ew ewset havoc extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in Hc.
    rewrite E32, Z.add_0_r, unsigned_lit_small in Hc by lia. rewrite zcanon_id in Hc by (unfold M64; lia). exact Hc. }
  assert (Ei : i = length (q_LN cx q)) by (apply Hb0z; exact Hb0).
  assert (Hkw2 : length (q_ws cx q) = kw).
  { replace (skipn i (q_LN cx q)) with (@nil byte) in HWA by (symmetry; apply skipn_all2; lia).
    cbn [Verbs.words_acc] in HWA.
    apply (f_equal (@length _)) in HWA. rewrite length_skipn in HWA. cbn [length] in HWA. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK WSspan LO_K.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdA2 := d) in *; clearbody mdA2 end.
  lazymatch type of HS with context [restrict _ ?mm] => rename mm into msA2 end.
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem msA2)) |- _ =>
    assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem msA2) a = rdW W mem a)
    by (intros a Ha; rewrite <- (KA1 a Ha); apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
        [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' as [Hq0 | []]; injection Hq0 as <- <- <-; lia
        | exact Ha | intros F; exact F ])
  end.
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 (bv_unsigned b0)]) E2) by ws_agree HAE
  end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ WS_KEEP HS HAE2 ltac:(vm_compute; reflexivity)) as RK.
  cbn [ms_regs restrict] in RK.
  pmkst HS.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 - 2 * ESTACK <= a < x_sp0 cx - 256) ->
    ~ (x_sp0 cx - 112 <= a < x_sp0 cx - 108) ->
    ~ (copy <= a < copy + q_L0 cx q + 1) -> ~ (arr <= a < arr + SlotSpec.arr_size (q_L0 cx q)) ->
    rdW W (ms_mem msA2) a = rdW W mem a) by (intros a Ha _ _ _ _; exact (KA2 a Ha)).
  pose proof (ws_inv_kept cx q ly S W regs mem md k acc text copy arr (ms_regs msA2) (ms_mem msA2) mdA2 HI HJ RK KM) as HI2.
  destruct HI2 as (HC2 & Hrec2 & Hws2).
  apply (HE cx q ly S W (ms_regs msA2) (ms_mem msA2) mdA2 k acc text copy arr C wp Hm HFP0 HC2 Hrec2 Hws2).
  + rewrite Hkw2. unfold aw_wn in *. apply (aval_mem_kept_r (rdW W mem)); [|exact HWN].
    intros x Hx. apply KA2. unfold LT_W in Hx. rewrite Hs1 in Hx. change (Z.of_nat 4) with 4 in Hx. lia.
  + rewrite Hwp. exact (eq_sym Hkw2).
  + apply (abytes_atR_kept_r (rdW W mem)); [intros x Hx; apply KA2; lia | exact HCB].
  + exact HCL.
  + apply (ws_arr_kept (rdW W mem)); [intros x Hx; apply KA2; lia | exact HAA].
  + apply (ws_found_mono copy (q_ws cx q) C wp i); [exact HFD | lia].
- (* a byte of the line: a1 = " \t", a0 = s7, the strspn call *)
  assert (Hb0 : bv_unsigned b0 <> 0).
  { intros Hz. rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc. rewrite U_SOff, U_lit by lia.
    cbn [ew ewset havoc extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add].
    rewrite E32, Z.add_0_r, unsigned_lit_small by lia. rewrite zcanon_id by (unfold M64; lia). exact Hz. }
  assert (Hlt : (i < length (q_LN cx q))%nat).
  { assert (i <> length (q_LN cx q)) by (intros Eq; apply Hb0, Hb0z, Eq). lia. }
  paj_run_tok RUN HS HJ SHOK WSspan.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdA3 := d) in *; clearbody mdA3 end.
  lazymatch type of HS with context [restrict _ ?mm] => rename mm into msA3 end.
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem msA3)) |- _ =>
    assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem msA3) a = rdW W mem a)
    by (intros a Ha; rewrite <- (KA1 a Ha); apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
        [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' as [Hq0 | []]; injection Hq0 as <- <- <-; lia
        | exact Ha | intros F; exact F ])
  end.
  lazymatch type of HS with
  | st_ok_pi _ _ ?E3 _ _ =>
    assert (HAE3 : env_agree 32 (Ereg regs [Z_to_bv 64 (bv_unsigned b0)]) E3) by ws_agree HAE;
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ WS_KEEP HS HAE3 ltac:(vm_compute; reflexivity)) as RK
  | st_ok _ ?E3 _ _ =>
    assert (HAE3 : env_agree 32 (Ereg regs [Z_to_bv 64 (bv_unsigned b0)]) E3) by ws_agree HAE;
    pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ WS_KEEP HS HAE3 ltac:(vm_compute; reflexivity)) as RK
  end.
  cbn [ms_regs restrict] in RK.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (23%bv : bv 5) P23.
  assert (HspT : spZ (ms_regs msA3) = x_sp0 cx + -256)
    by (unfold spZ at 1; rewrite P2, E2, unsigned_lit_small by lia; lia).
  assert (P3' : getr (ms_regs msA3) 3 = w64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
  assert (P4' : getr (ms_regs msA3) 4 = w64 (as_tp B)) by (rewrite P4, E4; exact Htp).
  assert (P10' : getr (ms_regs msA3) 10 = w64 (copy + Z.of_nat i)) by (rewrite P10, E23; reflexivity).
  assert (P11' : getr (ms_regs msA3) 11 = w64 0x210e0) by (rewrite P11, E246; reflexivity).
  assert (HraT : YK0s.ret_ok (getr (ms_regs msA3) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (HCB1 : abytes_atR (rdW W (ms_mem msA3)) copy C)
    by (apply (abytes_atR_kept_r (rdW W mem)); [intros x Hx; apply KA3; lia | exact HCB]).
  pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [] ly S W (ms_mem msA3) mdA3 k (ms_regs msA3) (-256) HJ HspT eq_refl ltac:(lia) ltac:(lia)
    ltac:(rewrite WS; lia) HraT P3' P4') as HPREc.
  destruct (ws_cursor cx q ly S W (ms_regs msA3) (ms_mem msA3) mdA3 copy C i (proj1 HJ) Hcin ltac:(rewrite HspT; lia)
    HCB1 HCL HLN Hi HCF) as (Hstr & Hrd & Htl & Hm8).
  destruct (ws_sep cx ly S W (ms_regs msA3) (ms_mem msA3) mdA3 k HB0 HJ HPREc) as (Hsstr & Hsrd & Hstl & Hrom & Hsm8).
  eapply SRr_bind.
  { exact (aj_strspn_at_loc W (ms_regs msA3) (ms_mem msA3) LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx)
      (x_mem cx) (x_md cx) [] ly S mdA3 k (copy + Z.of_nat i) 0x210e0 (skipn i (q_LN cx q)) SlotWords.SEPS (-256)
      (getr (ms_regs msA3) 1) HJ P10' P11' ltac:(lia) ltac:(lia) HspT eq_refl ltac:(lia) ltac:(rewrite WS, Hes; lia)
      P3' P4' eq_refl HraT Hstr Hsstr Hrd Hsrd Hm8 Hsm8 Htl Hstl Hrom). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
  rewrite P1. change (BASE + 972) with (BASE + WS_B).
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 - 2 * ESTACK <= a < x_sp0 cx - 256) ->
    rdW W mem2 a = rdW W mem a).
  { intros a Ha Hn. rewrite (HK2 a Ha ltac:(lia) ltac:(tauto)). exact (KA3 a Ha). }
  apply (HB2 cx q ly S W regs2 mem2 md2 k acc text copy arr i kw C wp Hm HFP0).
  + apply (ws_inv_kept cx q ly S W regs mem md k acc text copy arr regs2 mem2 md2 HI HJ2).
    * intros r Hr. rewrite (ws_pres_keep _ _ HP2 r Hr). exact (RK r Hr).
    * intros a Ha Hs _ _ _. exact (K2 a Ha Hs).
  + ws_reg HP2 23 P23 E23.
  + exact HQ2.
  + unfold aw_wn in *. apply (aval_mem_kept_r (rdW W mem)); [|exact HWN].
    intros x Hx. apply K2; unfold LT_W in Hx; rewrite Hs1 in Hx; change (Z.of_nat 4) with 4 in Hx; lia.
  + exact Hnm.
  + exact Hi.
  + exact Hk.
  + exact Hwp.
  + exact Hkw.
  + exact HWA.
  + apply (abytes_atR_kept_r (rdW W mem)); [intros x Hx; apply K2; lia | exact HCB].
  + exact HCL.
  + exact HCF.
  + apply (ws_arr_kept (rdW W mem)); [intros x Hx; apply K2; lia | exact HAA].
  + exact HFD.
Qed.

(* the stretch from 0x868fc, from one run to the next: its write check (the byte read-only, w.n on the stack,
   arr[kw] in arr's block), the memory a run keeps (all but w.n and arr[kw]), a region of a state *)
Ltac ws_awrB sp a8 F2 F36 Hain Han0 arr asz :=
  lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  apply awr_ok_cons_ro; [cbn; lia|];
  apply (YCbq.awr_ok_cons_gen _ _) with (k := 2%nat) (b := sp);
    [reflexivity | cbn [ew ewset havoc extK Nat.eqb]; rewrite F2; apply unsigned_lit_small; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; lia |];
  apply (YCbq.awr_ok_cons_gen _ _) with (k := 36%nat) (b := a8);
    [reflexivity | cbn [ew ewset havoc extK Nat.eqb]; rewrite F36; apply unsigned_lit_small; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; left;
      exists arr, asz; split; [exact Hain|]; split; [exact Han0|]; rewrite ws_req by lia; lia |];
  apply awr_ok_nil.
Ltac ws_kB msN KBN sp a8 F2 F36 :=
  lazymatch goal with HFr : frame_of ?E0 ?rs0 (mrestrict _ _) (mrestrict _ (ms_mem msN)) |- _ =>
    pose proof (ws_kept_B E0 rs0 _ _ (ms_mem msN) sp a8 HFr ltac:(vm_compute; reflexivity)
      ltac:(cbn [ew ewset havoc extK Nat.eqb]; rewrite F2; apply unsigned_lit_small; lia)
      ltac:(cbn [ew ewset havoc extK Nat.eqb]; rewrite F36; apply unsigned_lit_small; lia)) as KBN
  end.
Ltac ws_reg_of HS idx Hreg :=
  lazymatch type of HS with
  | st_ok_pi _ ?val ?E3 ?ss3 _ =>
    let r := eval vm_compute in (nth_error (ss_mem (abs_ss val ss3)) idx) in
    lazymatch r with Some ?rr => pose proof (st_ok_region_nth E3 (abs_ss val ss3) _ idx rr HS eq_refl) as Hreg end
  | st_ok _ ?E3 ?ss3 _ =>
    let r := eval vm_compute in (nth_error (ss_mem ss3) idx) in
    lazymatch r with Some ?rr => pose proof (st_ok_region_nth E3 ss3 _ idx rr HS eq_refl) as Hreg end
  end;
  cbn [ms_mem restrict] in Hreg.
Ltac ws_side := first [ cbn [ew ewset havoc extK Nat.eqb]; assumption | lia ].

(* 0x868fc .. jal strcspn: the UBSan test of t + s (0x86900); s7 += s, the 1-byte check of the cursor and its byte;
   the exit when it is the NUL (0x8691c); w.n + 1 and its UBSan test (0x86928), &w.v[kw] = arr + 8 kw and its UBSan
   tests (null-ness 0x86944, direction 0x86958, arr null 0x8695c, alignment 0x86964), w.n := kw + 1 (0x86940), the
   8-byte check and arr[kw] := s7 (0x86978); the strcspn call and back at 0x8698c *)
Lemma ws_B : forall m nm, AW_S2_stmt B MT m nm -> AW_E_stmt B MT m -> WS_B_stmt m nm.
Proof.
intros m nm HS2 HE cx q ly S W regs mem md k acc text copy arr i kw C wp Hm HFP0 HI R23 R10 HWN Hnm Hi Hk Hwp Hkw
  HWA HCB HCL HCF HAA HFD.
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_value as [[HAC1 HAC2] _].
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : LTOI_STK = 32768) by reflexivity.
pose proof (ws_inv_facts cx q ly S W regs mem md k acc text copy arr HI) as
  (HAR & HJ & Hcin & Hain & Hcn0 & Han0 & Hdis & Hsp & Hgp & Htp & Hceil & Hal16 & H47 & HB0 & HL0 & HLN &
   Hc16 & Hc4 & Hcc & Ha16 & Ha4 & Hac & Hcapp & Haapp & Hcpres & Hapres & HSP).
pose proof HB0 as (_ & _ & _ & HOBJ & _).
assert (R25 : getr regs 25 = w64 LT_SB) by (destruct HI as (((_ & (_ & _ & _ & _ & _ & R25 & _) & _) & _) & _); exact R25).
assert (HW3 : rdword (rdW W mem) (x_sp1 cx + LT_W + 16) = Some arr) by (destruct HI as (_ & _ & _ & _ & HW3); exact HW3).
unfold w64 in *.
assert (Hs1 : x_sp1 cx = x_sp0 cx - 256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
assert (Hkw4 : (kw <= 4096)%nat) by lia.
assert (HAK : 8 * Z.of_nat kw + 8 <= SlotSpec.arr_size (q_L0 cx q)).
{ unfold SlotSpec.arr_size. pose proof (Z.div_mod (q_L0 cx q) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (q_L0 cx q) 2 ltac:(lia)). lia. }
assert (HCA : forall x, copy <= x < copy + q_L0 cx q + 1 -> ~ (arr + 8 * Z.of_nat kw <= x < arr + 8 * Z.of_nat kw + 8)).
{ intros x Hx Hy. unfold ws_apart in Hdis. lia. }
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
(* the seat at 0x868fc: atoms 32 .. 36 *)
pose (XS := [Z_to_bv 64 (copy + Z.of_nat (i + s)); Z_to_bv 64 (bv_unsigned b1); Z_to_bv 64 arr;
  Z_to_bv 64 (Z.of_nat kw); Z_to_bv 64 (arr + 8 * Z.of_nat kw)]).
pose proof (ws_E_reg regs XS) as EEo.
assert (E2 : ew (ws_E regs XS) 2 = Z_to_bv 64 (x_sp0 cx - 256)).
{ rewrite (EEo 2%nat 2%bv eq_refl). apply bv_eq. rewrite unsigned_lit_small by lia. exact Hsp. }
assert (E3 : ew (ws_E regs XS) 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew (ws_E regs XS) 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E25 : ew (ws_E regs XS) 25 = Z_to_bv 64 LT_SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E23 : ew (ws_E regs XS) 23 = Z_to_bv 64 (copy + Z.of_nat i)) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E10 : ew (ws_E regs XS) 10 = Z_to_bv 64 (Z.of_nat s)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E32 : ew (ws_E regs XS) 32 = Z_to_bv 64 (copy + Z.of_nat (i + s))) by exact (ws_E_extra regs XS 0 ltac:(lia)).
assert (E33 : ew (ws_E regs XS) 33 = Z_to_bv 64 (bv_unsigned b1)) by exact (ws_E_extra regs XS 1 ltac:(lia)).
assert (E34 : ew (ws_E regs XS) 34 = Z_to_bv 64 arr) by exact (ws_E_extra regs XS 2 ltac:(lia)).
assert (E35 : ew (ws_E regs XS) 35 = Z_to_bv 64 (Z.of_nat kw)) by exact (ws_E_extra regs XS 3 ltac:(lia)).
assert (E36 : ew (ws_E regs XS) 36 = Z_to_bv 64 (arr + 8 * Z.of_nat kw)) by exact (ws_E_extra regs XS 4 ltac:(lia)).
pose proof (ws_E_img regs XS) as HEI.
pose proof (ws_E_agree regs XS) as HAE.
pose proof (ws_ew_obj (ws_E regs XS) 5 0x210e0 HOBJ HEI ltac:(vm_compute; lia) eq_refl ltac:(unfold A_OBJ, A_LIM; lia)) as E246.
change (A_OBJ 5) with 246%nat in E246.
remember (ws_E regs XS) as E eqn:HE0.
assert (HRS : Forall (region_ok SEGS E (mrestrict (w_H W) mem)) ws_rB).
{ unfold ws_rB. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (ws_rg_byte E W mem 32 33 (copy + Z.of_nat (i + s)) (bv_unsigned b1) E32 E33); [lia | lia | lia | exact Hrd1].
  - apply (ws_rg_frame E W mem (x_sp0 cx - 256) arr (Z.of_nat kw) E2 E34 E35); [lia | lia | lia | lia | | |].
    + intros a Ha. apply HSP. lia.
    + replace (x_sp0 cx - 256 + 136) with (x_sp1 cx + LT_W + 16) by (unfold LT_W; lia). exact HW3.
    + replace (x_sp0 cx - 256 + 144) with (x_sp1 cx + LT_W + 24) by (unfold LT_W; lia). exact HWN.
  - apply (ws_rg_slot E W mem 36 (arr + 8 * Z.of_nat kw) E36); [lia | lia | intros a Ha; apply Hapres; lia]. }
assert (HPD : pairwise_disjoint E ws_rB).
{ pose proof Hdis as Hd'. unfold ws_apart in Hd'.
  apply pairwise_disjoint_of_extents. unfold ws_rB, ws_rframe, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E32, E2, E36, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
assert (HAT : atoms_ok E ws_atomsB).
{ cbn [ws_atomsB atoms_ok]. unfold PTR.
  split; [apply (ws_afact _ 2 (x_sp0 cx - 256) _ _ _ E2); [lia | lia | change (2 ^ 4) with 16; rewrite Zminus_mod, Hal16; reflexivity | lia]|].
  split; [apply (ws_afact _ 25 LT_SB _ _ _ E25); [unfold LT_SB; lia | unfold LT_SB; lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (ws_afact _ 23 _ _ _ _ E23); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (ws_afact _ 10 _ _ _ _ E10); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (ws_afact _ 32 _ _ _ _ E32); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (ws_afact _ 33 _ _ _ _ E33); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (ws_afact _ 34 _ _ _ _ E34); [lia | lia | change (2 ^ 4) with 16; exact Ha16 | lia]|].
  split; [apply (ws_afact _ 35 _ _ _ _ E35); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (ws_afact _ 36 _ _ _ _ E36); [lia | lia | apply ws_mod8; exact Ha16 | lia]|].
  exact I. }
assert (HAL : alias_ok E ws_aliasB).
{ cbn [ws_aliasB alias_ok]. split; [|split; [|exact I]].
  - rewrite (ws_add_atoms E 23 10 (copy + Z.of_nat i) (Z.of_nat s) E23 E10) by lia.
    cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. f_equal. lia.
  - rewrite (ws_add_sll3 E 34 35 arr (Z.of_nat kw) E34 E35) by lia.
    cbn [sv_denot]. rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (UBx : U E WSx = SHADOW_OFF) by (unfold WSx; rewrite (U_atom E 25 LT_SB E25) by (unfold LT_SB; lia); reflexivity).
assert (HRA8 : range_addressable (rdW W mem) SHADOW_OFF (arr + 8 * Z.of_nat kw) 8)
  by (apply (range_addressable_of_block SEGS B LAWS ly S W mem md arr (SlotSpec.arr_size (q_L0 cx q)));
      [exact HAR | exact Hain | lia | rewrite ws_req by lia; lia]).
assert (HSH : sh_ok SEGS WSx ws_shB E (mrestrict (w_H W) mem)).
{ unfold sh_ok, ws_shB. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E WSx 36 (arr + 8 * Z.of_nat kw) 8 (arr + 8 * Z.of_nat kw) 0 8 HRA8 UBx);
    [apply U_atom; [exact E36 | lia] | lia | lia |].
  intros x Hx. apply (ws_not_shadow arr (SlotSpec.arr_size (q_L0 cx q)) x Haapp). lia. }
pose proof (ws_seat W regs mem WS_B XS ws_rB ws_atomsB ws_aliasB eq_refl) as HS.
rewrite <- HE0 in HS. specialize (HS HRS HPD HAT HAL).
(* the run to the UBSan test of t + s (0x868fc .. 0x86900) *)
paj_run_tok RUN HS HJ HSH WSspan.
{ ws_awrB (x_sp0 cx - 256) (arr + 8 * Z.of_nat kw) E2 E36 Hain Han0 arr (SlotSpec.arr_size (q_L0 cx q)). }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdB1 := d) in *; clearbody mdB1 end.
lazymatch type of HS with context [restrict _ ?mm] => rename mm into msB1 end.
ws_kB msB1 KB1 (x_sp0 cx - 256) (arr + 8 * Z.of_nat kw) E2 E36.
psrr_branch_tok RUN BR HS HSH WSspan.
{ (* t + s wraps: no, t + s is a byte of copy *)
  exfalso. rewrite branch_ltu_U, YE2y.U_not, (U_atom _ 23 (copy + Z.of_nat i)), (U_atom _ 10 (Z.of_nat s)) in Hc by ws_side.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* s7 := t + s, its 1-byte check and its byte (0x86904 .. 0x8691c) *)
paj_run_tok RUN HS HJ HSH WSspan.
{ cbn [ms_mem]. unfold WSx.
  rewrite (U_atom _ 25 LT_SB), (U_atom _ 32 (copy + Z.of_nat (i + s))) by (first [ws_side | unfold LT_SB; lia]).
  exact (range_addressable_of_block SEGS B LAWS ly S W _ _ copy (q_L0 cx q + 1) (copy + Z.of_nat (i + s)) 1 (proj1 HJ) Hcin
    ltac:(lia) ltac:(rewrite ws_req by lia; lia)). }
{ ws_awrB (x_sp0 cx - 256) (arr + 8 * Z.of_nat kw) E2 E36 Hain Han0 arr (SlotSpec.arr_size (q_L0 cx q)). }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdB2 := d) in *; clearbody mdB2 end.
lazymatch type of HS with context [restrict _ ?mm] => rename mm into msB2 end.
ws_kB msB2 KB2 (x_sp0 cx - 256) (arr + 8 * Z.of_nat kw) E2 E36.
psrr_branch_tok RUN BR HS HSH WSspan.
- (* the byte is the NUL: only separators were left; beqz -> 0x86a04 *)
  assert (Hb0 : bv_unsigned b1 = 0).
  { rewrite branch_eq_U, U_SLit, (U_atom _ 33 (bv_unsigned b1)) in Hc by ws_side.
    apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc. exact Hc. }
  assert (Esl : (i + s)%nat = length (q_LN cx q)) by (apply Hb1z; exact Hb0).
  assert (Hall : forall x, In x (skipn i (q_LN cx q)) -> Verbs.is_sep x = true).
  { intros y Hy. destruct (SlotWords.sw_spn_split SlotWords.SEPS (skipn i (q_LN cx q))) as [SP1 _].
    unfold aw_spn in Es. rewrite <- Es in SP1. rewrite firstn_all2 in SP1 by (rewrite length_skipn; lia).
    rewrite <- SlotWords.sw_in_set_seps. exact (SP1 y Hy). }
  assert (Hkw2 : length (q_ws cx q) = kw).
  { pose proof (SlotWords.sw_words_seps (skipn i (q_LN cx q)) [] Hall) as E0. rewrite app_nil_r, HWA in E0.
    cbn [Verbs.words_acc] in E0. apply (f_equal (@length _)) in E0. rewrite length_skipn in E0. cbn [length] in E0. lia. }
  paj_run_to_tok RUNTO HS HJ HSH WSspan LO_K.
  { ws_awrB (x_sp0 cx - 256) (arr + 8 * Z.of_nat kw) E2 E36 Hain Han0 arr (SlotSpec.arr_size (q_L0 cx q)). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdB3 := d) in *; clearbody mdB3 end.
  lazymatch type of HS with context [restrict _ ?mm] => rename mm into msB3 end.
  ws_kB msB3 KB3 (x_sp0 cx - 256) (arr + 8 * Z.of_nat kw) E2 E36.
  assert (KBc : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 + 144 <= a < x_sp0 cx - 256 + 148) ->
    ~ (arr + 8 * Z.of_nat kw <= a < arr + 8 * Z.of_nat kw + 8) -> rdW W (ms_mem msB3) a = rdW W mem a)
    by (intros a Ha H1 H2; rewrite (KB3 a Ha H1 H2), (KB2 a Ha H1 H2); exact (KB1 a Ha H1 H2)).
  (* w.n still holds kw *)
  ws_reg_of HS 1%nat Hreg.
  assert (Hwn3 : aval_mem (rdW W (ms_mem msB3)) (x_sp0 cx - 256 + 144) 4 (Z.of_nat kw)).
  { apply (ws_wn_of_region _ W (ms_mem msB3) (x_sp0 cx - 256) _ (SOff 35 0) (Z.of_nat kw) Hreg);
      [cbn [ew ewset havoc extK Nat.eqb]; rewrite E2; apply unsigned_lit_small; lia
      | repeat (first [left; reflexivity | right])
      | cbn [sv_denot ew ewset havoc extK Nat.eqb]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E35; apply unsigned_lit_small; lia
      | lia]. }
  clear Hreg.
  lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
    assert (HAE3 : env_agree 32 (Ereg regs XS) E3) by ws_agree HAE
  end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ WS_KEEP HS HAE3 ltac:(vm_compute; reflexivity)) as RK.
  cbn [ms_regs restrict] in RK.
  pmkst HS.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 - 2 * ESTACK <= a < x_sp0 cx - 256) ->
    ~ (x_sp0 cx - 112 <= a < x_sp0 cx - 108) ->
    ~ (copy <= a < copy + q_L0 cx q + 1) -> ~ (arr <= a < arr + SlotSpec.arr_size (q_L0 cx q)) ->
    rdW W (ms_mem msB3) a = rdW W mem a) by (intros a Ha _ Hn1 _ Hn2; apply KBc; lia).
  pose proof (ws_inv_kept cx q ly S W regs mem md k acc text copy arr (ms_regs msB3) (ms_mem msB3) mdB3 HI HJ RK KM) as HI3.
  destruct HI3 as (HC3 & Hrec3 & Hws3).
  apply (HE cx q ly S W (ms_regs msB3) (ms_mem msB3) mdB3 k acc text copy arr C wp Hm HFP0 HC3 Hrec3 Hws3).
  + rewrite Hkw2. unfold aw_wn. replace (x_sp1 cx + LT_W + 24) with (x_sp0 cx - 256 + 144) by (unfold LT_W; lia).
    exact Hwn3.
  + rewrite Hwp. exact (eq_sym Hkw2).
  + apply (abytes_atR_kept_r (rdW W mem)); [intros x Hx; apply KBc; [lia | lia | apply HCA; lia] | exact HCB].
  + exact HCL.
  + apply (ws_arr_kept (rdW W mem)); [intros x Hx; apply KBc; lia | exact HAA].
  + apply (ws_found_mono copy (q_ws cx q) C wp i); [exact HFD | lia].
- (* a word starts at i + s *)
  assert (Hb0 : bv_unsigned b1 <> 0).
  { intros Hz. rewrite branch_eq_U, U_SLit, (U_atom _ 33 (bv_unsigned b1)) in Hc by ws_side.
    apply Z.eqb_neq in Hc. apply Hc. rewrite Hz. reflexivity. }
  clear Hc.
  assert (Hlt : (i + s < length (q_LN cx q))%nat).
  { assert ((i + s)%nat <> length (q_LN cx q)) by (intros Eq; apply Hb0, Hb1z, Eq). lia. }
  (* w.n + 1, &w.v[kw], w.n := kw + 1, up to the direction test (0x86920 .. 0x86958) *)
  paj_run_tok RUN HS HJ HSH WSspan.
  { ws_awrB (x_sp0 cx - 256) (arr + 8 * Z.of_nat kw) E2 E36 Hain Han0 arr (SlotSpec.arr_size (q_L0 cx q)). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdB4 := d) in *; clearbody mdB4 end.
  lazymatch type of HS with context [restrict _ ?mm] => rename mm into msB4 end.
  ws_kB msB4 KB4 (x_sp0 cx - 256) (arr + 8 * Z.of_nat kw) E2 E36.
  psrr_branch_tok RUN BR HS HSH WSspan.
  { (* arr + 8 kw moved below arr: no, it does not wrap *)
    exfalso. rewrite branch_eq_U, !U_SAlu, !U_SLit, (U_atom _ 36 (arr + 8 * Z.of_nat kw)), (U_atom _ 34 arr) in Hc
      by ws_side.
    cbn [zalu_raw] in Hc. replace (arr + 8 * Z.of_nat kw <? arr) with false in Hc by (symmetry; apply Z.ltb_ge; lia).
    vm_compute in Hc. discriminate Hc. }
  clear Hc.
  (* arr null, alignment, the 8-byte check, arr[kw] := s7, a1 = " \t", a0 = s7, the strcspn call (0x8695c .. 0x86988) *)
  paj_run_tok RUN HS HJ HSH WSspan.
  { ws_awrB (x_sp0 cx - 256) (arr + 8 * Z.of_nat kw) E2 E36 Hain Han0 arr (SlotSpec.arr_size (q_L0 cx q)). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdB5 := d) in *; clearbody mdB5 end.
  lazymatch type of HS with context [restrict _ ?mm] => rename mm into msB5 end.
  ws_kB msB5 KB5 (x_sp0 cx - 256) (arr + 8 * Z.of_nat kw) E2 E36.
  assert (KBc : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 + 144 <= a < x_sp0 cx - 256 + 148) ->
    ~ (arr + 8 * Z.of_nat kw <= a < arr + 8 * Z.of_nat kw + 8) -> rdW W (ms_mem msB5) a = rdW W mem a)
    by (intros a Ha H1 H2; rewrite (KB5 a Ha H1 H2), (KB4 a Ha H1 H2), (KB2 a Ha H1 H2); exact (KB1 a Ha H1 H2)).
  (* w.n holds kw + 1, arr[kw] holds the cursor *)
  ws_reg_of HS 1%nat Hreg1.
  assert (Hwn5 : aval_mem (rdW W (ms_mem msB5)) (x_sp0 cx - 256 + 144) 4 (Z.of_nat (kw + 1))).
  { apply (ws_wn_of_region _ W (ms_mem msB5) (x_sp0 cx - 256) _ (SOff 35 1) (Z.of_nat (kw + 1)) Hreg1);
      [cbn [ew ewset havoc extK Nat.eqb]; rewrite E2; apply unsigned_lit_small; lia
      | repeat (first [left; reflexivity | right])
      | cbn [sv_denot ew ewset havoc extK Nat.eqb]; rewrite E35, (unsigned_lit_small (Z.of_nat kw)) by lia;
        rewrite unsigned_lit_small by lia; lia
      | lia]. }
  ws_reg_of HS 2%nat Hreg2.
  assert (Hslot : rdword (rdW W (ms_mem msB5)) (arr + 8 * Z.of_nat kw) = Some (copy + Z.of_nat (i + s))).
  { apply (ws_slot_of_region _ W (ms_mem msB5) (arr + 8 * Z.of_nat kw) _ (SOff 32 0) (copy + Z.of_nat (i + s)) Hreg2);
      [cbn [ew ewset havoc extK Nat.eqb]; rewrite E36; apply unsigned_lit_small; lia
      | repeat (first [left; reflexivity | right])
      | cbn [sv_denot ew ewset havoc extK Nat.eqb]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E32; apply unsigned_lit_small; lia
      | lia]. }
  clear Hreg1 Hreg2.
  lazymatch type of HS with
  | st_ok_pi _ _ ?E5 _ _ =>
    assert (HAE5 : env_agree 32 (Ereg regs XS) E5) by ws_agree HAE;
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ WS_KEEP HS HAE5 ltac:(vm_compute; reflexivity)) as RK
  | st_ok _ ?E5 _ _ =>
    assert (HAE5 : env_agree 32 (Ereg regs XS) E5) by ws_agree HAE;
    pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ WS_KEEP HS HAE5 ltac:(vm_compute; reflexivity)) as RK
  end.
  cbn [ms_regs restrict] in RK.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (23%bv : bv 5) P23.
  assert (HspT : spZ (ms_regs msB5) = x_sp0 cx + -256)
    by (unfold spZ at 1; rewrite P2, E2, unsigned_lit_small by lia; lia).
  assert (P3' : getr (ms_regs msB5) 3 = w64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
  assert (P4' : getr (ms_regs msB5) 4 = w64 (as_tp B)) by (rewrite P4, E4; exact Htp).
  assert (P10' : getr (ms_regs msB5) 10 = w64 (copy + Z.of_nat (i + s))) by (rewrite P10, E32; reflexivity).
  assert (P11' : getr (ms_regs msB5) 11 = w64 0x210e0) by (rewrite P11, E246; reflexivity).
  assert (HraT : YK0s.ret_ok (getr (ms_regs msB5) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (HCB5 : abytes_atR (rdW W (ms_mem msB5)) copy C)
    by (apply (abytes_atR_kept_r (rdW W mem)); [intros x Hx; apply KBc; [lia | lia | apply HCA; lia] | exact HCB]).
  pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [] ly S W (ms_mem msB5) mdB5 k (ms_regs msB5) (-256) HJ HspT eq_refl ltac:(lia) ltac:(lia)
    ltac:(rewrite WS; lia) HraT P3' P4') as HPREc.
  destruct (ws_cursor cx q ly S W (ms_regs msB5) (ms_mem msB5) mdB5 copy C (i + s) (proj1 HJ) Hcin
    ltac:(rewrite HspT; lia) HCB5 HCL HLN ltac:(lia) ltac:(intros t Ht; apply HCF; lia)) as (Hstr & Hrd & Htl & Hm8).
  destruct (ws_sep cx ly S W (ms_regs msB5) (ms_mem msB5) mdB5 k HB0 HJ HPREc) as (Hsstr & Hsrd & Hstl & Hrom & Hsm8).
  eapply SRr_bind.
  { exact (aj_strcspn_at_loc W (ms_regs msB5) (ms_mem msB5) LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx)
      (x_mem cx) (x_md cx) [] ly S mdB5 k (copy + Z.of_nat (i + s)) 0x210e0 (skipn (i + s) (q_LN cx q))
      SlotWords.SEPS (-256) (getr (ms_regs msB5) 1) HJ P10' P11' ltac:(lia) ltac:(lia) HspT eq_refl ltac:(lia)
      ltac:(rewrite WS, Hes; lia) P3' P4' eq_refl HraT Hstr Hsstr Hrd Hsrd Hm8 Hsm8 Htl Hstl Hrom). }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3 & HK3).
  rewrite P1. change (BASE + 1116) with (BASE + AW_S2).
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 - 2 * ESTACK <= a < x_sp0 cx - 256) ->
    rdW W mem3 a = rdW W (ms_mem msB5) a).
  { intros a Ha Hn. exact (HK3 a Ha ltac:(lia) ltac:(tauto)). }
  assert (RK3 : forall r, In r WS_KEEP -> getr regs3 r = getr regs r)
    by (intros r Hr; rewrite (ws_pres_keep _ _ HP3 r Hr); exact (RK r Hr)).
  assert (KM3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 - 2 * ESTACK <= a < x_sp0 cx - 256) ->
    ~ (x_sp0 cx - 112 <= a < x_sp0 cx - 108) ->
    ~ (copy <= a < copy + q_L0 cx q + 1) -> ~ (arr <= a < arr + SlotSpec.arr_size (q_L0 cx q)) ->
    rdW W mem3 a = rdW W mem a)
    by (intros a Ha Hs3 Hn1 _ Hn2; rewrite (K3 a Ha Hs3); apply KBc; lia).
  pose proof (ws_inv_kept cx q ly S W regs mem md k acc text copy arr regs3 mem3 md3 HI HJ3 RK3 KM3) as HI3.
  destruct HI3 as (HC3 & Hrec3 & Hws3).
  apply (HS2 cx q ly S W regs3 mem3 md3 k acc text copy arr i s kw C wp Hm HFP0 HC3 Hrec3 Hws3).
  + ws_reg HP3 23 P23 E32.
  + exact HQ3.
  + unfold aw_wn. replace (x_sp1 cx + LT_W + 24) with (x_sp0 cx - 256 + 144) by (unfold LT_W; lia).
    apply (aval_mem_kept_r (rdW W (ms_mem msB5))); [|exact Hwn5].
    intros x Hx. apply K3; change (Z.of_nat 4) with 4 in Hx; lia.
  + exact Hnm.
  + exact Hk.
  + exact Hwp.
  + exact Hkw.
  + exact HWA.
  + apply (abytes_atR_kept_r (rdW W (ms_mem msB5))); [intros x Hx; apply K3; lia | exact HCB5].
  + exact HCL.
  + exact HCF.
  + exact HFD.
  + exact Es.
  + exact Hlt.
  + apply ws_arr_snoc.
    * apply (ws_arr_kept (rdW W mem)); [|exact HAA].
      intros x Hx. rewrite (K3 x) by lia. apply KBc; lia.
    * rewrite Hwp. apply (ws_rdword_kept (rdW W (ms_mem msB5))); [intros x Hx; apply K3; lia | exact Hslot].
Qed.

(* the first half of a round of the split loop, from its head to 0x8698c or to the exits to 0x86a04 *)
Lemma aw_seg_S1 : forall m nm, AW_S2_stmt B MT m nm -> AW_E_stmt B MT m -> AW_S_stmt B MT m nm.
Proof. intros m nm H2 HE. exact (ws_A m nm (ws_B m nm H2 HE) HE). Qed.

End e.
End f.
End d.
