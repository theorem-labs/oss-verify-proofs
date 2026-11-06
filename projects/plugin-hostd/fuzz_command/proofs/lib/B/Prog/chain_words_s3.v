(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment 3 of the walk of chain_words (0x8da84) on the ASan+UBSan build of
   plugin-hostd/fuzz_command (interface lib/B/Prog/chain_words_d.v): ONE pass of the member loop, from the loop
   head KL (+0x278, 0x8dcfc) at pass j. The 18 instructions walked are
     +0x278 bltu s10,s11      the UBSan trap check ~tok < 16 + 8 j   (refuted: tok + 8 ntok is in a live frame)
     +0x27c add  a0,s5,s11    &tok[2 + j]  (pinned to the walk's atom 32, so that the inline check below sees it)
     +0x280 srli a1,a0,3      the shadow address of &tok[2 + j]
     +0x284 add  a1,a1,s8
     +0x288 lbu  a1,0(a1)     the inline ASan check of the load (the shadow entry of the token array)
     +0x28c bnez a1           not taken
     +0x290 beqz s3           the UBSan trap check 65 - j = 0        (refuted: j <= ntok - 3 <= 61)
     +0x294 bltu s4,s9        the UBSan trap check ~(F + 32) < 4 j   (refuted: F + 512 <= alloc_ceiling)
     +0x298 ld   a0,0(a0)     tok[2 + j]
     +0x29c add  a1,s6,s9     &ids[j] = F + 32 + 4 j
     +0x2a0 jal  number       through cl_callS_wide (lib/B/Prog/PaNoChain.v), out = ids[j] in this call's frame
     +0x2a4 beqz a0           number refused the word -> KR2 (+0x2e8)
     +0x2a8 addi s9,s9,4
     +0x2ac addiw s3,s3,-1
     +0x2b0 ld   a0,24(s1)    ntok (the realigned frame's slot, cw_fi's fi_ntok)
     +0x2b4 addw a0,a0,s3
     +0x2b8 addi s11,s11,8
     +0x2bc bne  a0,s7        ntok + (64 - j) <> 67 -> KL at pass j + 1, else KD (+0x2c0)
   The proof skeleton is the A walk's chain_words_s3.v (a working branch 5e2cdad423e) with B's
   registers and the three UBSan branches refuted at their branch; B computes the shadow address inline, so the
   shadow base is s8's atom (24) and &tok[2 + j] is pinned to atom 32 after +0x27c (the technique of
   lib/A/Prog/sup_remove_all_refit_s4.v, sra_pin_append). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q YN01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
number_c sup_chain_c sup_resp_c chain_words_c chain_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the pc after `add a0,s5,s11` (where &tok[2 + j] is pinned) and the return point of the call of number *)
Definition CW3_PIN : Z := AF_chain_words + 0x280.
Definition CW3_RET : Z := AF_chain_words + 0x2a4.
(* the symbolic value of a0 at CW3_PIN and of a0 at the loop's exit test *)
Definition cw3_a0p : sv := SAlu ALU_ADD (SOff 21 0) (SOff 27 0).
Definition cw3_a0w : sv := SAluw ALU_ADD (SOff 32 0) (SAluw ALU_ADD (SOff 19 0) (SLit (-1))).

(* copied from the A walk's chain_words_s3.v (cw3_val_mem, cw3_afact) *)
Lemma cw3_val_mem : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb.
unfold val_mem.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb;
  cbn [option_map] in Hb; [|discriminate Hb].
injection Hb as Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, Hb. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
cbv [YO0f.le_byte YG0f.le_byte]. symmetry. apply Z.mod_mod. lia.
Qed.
Lemma cw3_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

(* the member words' values: numbers_m over an append, its length, a refused member *)
Lemma cw3_numbers_app : forall a b, Verbs.numbers_m (a ++ b) =
  match Verbs.numbers_m a, Verbs.numbers_m b with Some x, Some y => Some (x ++ y) | _, _ => None end.
Proof.
induction a as [|w a IH]; intros b; cbn [app Verbs.numbers_m].
- destruct (Verbs.numbers_m b); reflexivity.
- rewrite IH. destruct (Verbs.number_m w); destruct (Verbs.numbers_m a); destruct (Verbs.numbers_m b); reflexivity.
Qed.
Lemma cw3_numbers_len : forall ws vs, Verbs.numbers_m ws = Some vs -> length vs = length ws.
Proof.
induction ws as [|w ws IH]; intros vs H; cbn [Verbs.numbers_m] in H.
- injection H as <-. reflexivity.
- destruct (Verbs.number_m w) as [v|]; [|discriminate].
  destruct (Verbs.numbers_m ws) as [vs'|] eqn:E; [|discriminate].
  injection H as <-. cbn [length]. f_equal. exact (IH vs' eq_refl).
Qed.
Lemma cw3_numbers_none : forall l j w, nth_error l j = Some w -> Verbs.number_m w = None -> Verbs.numbers_m l = None.
Proof.
induction l as [|x l IH]; intros j w H Hw; [destruct j; discriminate|].
destruct j as [|j]; cbn [nth_error] in H; cbn [Verbs.numbers_m].
- injection H as ->. rewrite Hw. reflexivity.
- rewrite (IH j w H Hw). destruct (Verbs.number_m x); reflexivity.
Qed.
Lemma cw3_firstn_S : forall {A} (l : list A) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
intros A l. induction l as [|y l IH]; intros n x H; [destruct n; discriminate|].
destruct n as [|n]; cbn [nth_error] in H.
- injection H as ->. reflexivity.
- cbn [firstn app]. rewrite (IH n x H). reflexivity.
Qed.
Lemma cw3_nth_skipn : forall {A} (l : list A) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
intros A l n. revert l. induction n as [|n IH]; intros l i; [reflexivity|].
destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
(* a refused member makes chain_words_m refuse: the recorder answers err_invalid_operation *)
Lemma cw3_chain_none : forall R tks j w, (3 <= length tks)%nat -> nth_error tks (2 + j) = Some w ->
  Verbs.number_m w = None -> VerbsRun.chain_run R (tl tks) = sup_resp_m R Verbs.err_invalid_operation.
Proof.
intros R tks j w Hl Hn Hw. destruct tks as [|t0 [|t1 [|t2 tks]]]; cbn [length] in Hl; try lia.
cbn [tl]. unfold VerbsRun.chain_run, Verbs.chain_words_m.
rewrite (cw3_numbers_none (t2 :: tks) j w Hn Hw).
destruct (Verbs.number_m t1); reflexivity.
Qed.
(* the 4 little-endian bytes number stores are le32 of the value *)
Lemma cw3_byte_mod : forall v s, 0 <= s -> s + 8 <= 32 ->
  (Z.shiftr (v mod 2 ^ 64) s) mod 256 = (Z.shiftr (v mod 2 ^ 32) s) mod 256.
Proof.
intros v s Hs Hs8. change 256 with (2 ^ 8). apply Z.bits_inj'. intros n Hn.
destruct (Z.lt_ge_cases n 8) as [Hl|Hg].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma cw3_le32 : forall (rd : reader) a v, aval_mem rd a 4 v -> abytes_atR rd a (le32 v).
Proof.
intros rd a v H i Hi. unfold le32, OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Mem.le4 in Hi |- *.
rewrite length_Z_to_le_bytes in Hi.
rewrite (H i Hi). f_equal.
rewrite (nth_error_nth _ _ _ (YN01.nth_error_Z_to_le_bytes 4 _ i Hi)).
rewrite Z_to_bv_unsigned, unsigned_lit. unfold YG0f.le_byte, bv_wrap, bv_modulus, zcanon, M64.
change (2 ^ Z.of_N 8) with 256. change (8 * Z.of_nat 4) with 32.
symmetry. apply cw3_byte_mod; lia.
Qed.
Lemma cw3_abytes_app : forall (rd : reader) a l1 l2, abytes_atR rd a l1 ->
  abytes_atR rd (a + Z.of_nat (length l1)) l2 -> abytes_atR rd a (l1 ++ l2).
Proof.
intros rd a l1 l2 H1 H2 i Hi. rewrite length_app in Hi.
destruct (Nat.lt_ge_cases i (length l1)) as [Hl|Hg].
- rewrite app_nth1 by exact Hl. exact (H1 i Hl).
- rewrite app_nth2 by exact Hg.
  replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia.
  apply H2. lia.
Qed.
Lemma cw3_len_ids : forall vs, length (concat (map le32 vs)) = (4 * length vs)%nat.
Proof.
induction vs as [|x vs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold le32, OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Mem.le4. rewrite length_Z_to_le_bytes.
cbn [length]. lia.
Qed.
Lemma cw3_abytes_ext : forall (rd rd' : reader) a l, abytes_atR rd a l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H He i Hi. rewrite He by lia. exact (H i Hi). Qed.
Lemma cw3_aval_ext : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
  (forall i, 0 <= i < Z.of_nat n -> rd' (a + i) = rd (a + i)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H He k Hk. rewrite He by lia. exact (H k Hk). Qed.
(* the 32-bit arithmetic of the loop's exit test (addiw / addw on small non-negative values) *)
Lemma cw3_u_addiw : forall E a x, U E a = x -> 1 <= x < 2 ^ 31 ->
  U E (SAluw ALU_ADD a (SLit (-1))) = x - 1.
Proof.
intros E a x Hx Hr. rewrite U_of_S, S_SAluw, Hx, U_SLit.
cbn [zalu_raw].
rewrite (Z.mod_small x (2 ^ 32)) by lia.
replace (zcanon (-1) mod 2 ^ 32) with (2 ^ 32 - 1) by (vm_compute; reflexivity).
replace (x + (2 ^ 32 - 1)) with ((x - 1) + 1 * bv_modulus 32) by (change (bv_modulus 32) with (2 ^ 32); lia).
rewrite swrap_add_mod. rewrite swrap32_id by lia.
unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_small. lia.
Qed.
Lemma cw3_u_addw : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 31 ->
  U E (SAluw ALU_ADD a b) = x + y.
Proof.
intros E a b x y Hx Hy H1 H2 H3. rewrite U_of_S, S_SAluw, Hx, Hy. cbn [zalu_raw].
rewrite (Z.mod_small x (2 ^ 32)) by lia. rewrite (Z.mod_small y (2 ^ 32)) by lia.
rewrite swrap32_id by lia. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_small. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* app memory and the shadow of a side-stack frame are apart *)
Lemma cw3_app_shadow : forall x lo len g m i, in_app lo len -> lo <= x < lo + len ->
  4096 <= g -> g + m <= alloc_ceiling -> 0 <= i < m / 8 -> x <> shadow_addr g + i.
Proof.
intros x lo len g m i Happ Hx Hg Hgm Hi. pose proof asan_consts as (C1 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *.
assert (D : 0 <= g / 8 /\ g / 8 + i <= (g + m) / 8) by (split; [apply Z.div_pos; lia|]; Z.div_mod_to_equations; lia).
assert (D2 : (g + m) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 0xffffff00000 in D2. lia.
Qed.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the environment at KL: the registers, then atom 32 = &tok[2 + j] and atom 33 = tok[2 + j]; the shadow base is
   s8's own atom (24) *)
Definition cw3_EL (regs : bvmap 5 word) (x p : Z) : env := Eimg (Ereg regs [w64 x; w64 p]).
(* the environment after the call: the registers, then atom 32 = ntok (the word at s1 + 24) *)
Definition cw3_ER (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs [w64 n]).
Definition cw3_Bx : sv := SOff 24 0.
Definition cw3_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* &tok[2 + j]: 8 bytes holding tok[2 + j], read-only, and its shadow entry for the inline check at +0x288 *)
Definition cw3_tokR : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition cw3_factsL : facts := mkFacts [(24%nat, mkAF SB SB 0); (32%nat, mkAF 4096 (2 ^ 47 - 32) 3)] [] [].
Definition ss_cw3L : sstate := mkSS CW_KL sr_atoms [cw3_tokR] None cw3_factsL.
Definition cw3_SH : list shent := [mkSHE 32 0 8].
(* the word at s1 + 24 (ntok), read at +0x2b0 *)
Definition cw3_ntokR : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition cw3_factsR : facts := mkFacts [(9%nat, mkAF 4096 (2 ^ 47) 3)] [] [].
Definition ss_cw3R : sstate := mkSS CW3_RET sr_atoms [cw3_ntokR] None cw3_factsR.
Definition ss_cw3A (a0 : Z) : sstate := mkSS CW3_RET (sr_set sr_atoms 10 (SLit a0)) [cw3_ntokR] None cw3_factsR.
(* a register's symbolic value replaced by another of the same denotation (A/Prog/sup_remove_all_refit_s4.v) *)
Lemma cw3_set_reg : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> sv_denot E e = sv_denot E (sr_get (ss_regs ss) r) -> bv_eqb r 0 = false ->
st_ok_pi SEGS VAL E (mkSST (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS He Hr0. unfold st_ok_pi, abs_ss, setpc in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (VAL A_TEXT + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
(sr_set (ss_regs ss) r e) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. rewrite He. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Lemma cw3_regU : forall (H : word -> bool) E ss ms r, st_ok_pi SEGS VAL E ss (restrict H ms) ->
getr (ms_regs ms) r = Z_to_bv 64 (U E (sr_get (ss_regs ss) r)).
Proof. intros H E ss ms r HS. rewrite (st_ok_pi_restrict_reg H E ss ms r HS). unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma cw3_regU' : forall (H : word -> bool) E ss ms r, st_ok SEGS E ss (restrict H ms) ->
getr (ms_regs ms) r = Z_to_bv 64 (U E (sr_get (ss_regs ss) r)).
Proof. intros H E ss ms r HS. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS). unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Ltac cw3_rr HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (cw3_regU H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  | st_ok _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (cw3_regU' H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.
Ltac cw3_mdv nm := lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?md) ?mt ?md] =>
  set (nm := with_vm_backing (m_vm_lazy md) mt md) in *; clearbody nm end.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis NUMBER : forall fx0 : YK11.FPState, @tnumber_spec fx0 rc SK PI B MT.
Hypothesis TL : PALib B.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis TRANSP : cw_transportP B MT.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* copied from the A walk: the layout, the read-only run, the preserved registers *)
Lemma cw3_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity. Qed.
Lemma cw3_frame_ro : forall E rs (m m' : word -> option byte),
Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro H x. apply H. intros (r & Hr & Ha).
pose proof (proj1 (Forall_forall _ _) Hro r Hr) as Hw. cbn beta in Hw. lia.
Qed.
(* give the machine state a run reaches a stable name, and keep that the run wrote nothing *)
Ltac cw3_name HS nm :=
  lazymatch type of HS with context [restrict _ ?m] => rename m into nm end.
Ltac cw3_ro nm :=
  lazymatch goal with
  | H : frame_of ?E ?rs ?m (ms_mem ?y) |- _ =>
    pose proof (cw3_frame_ro E rs m (ms_mem y)
      ltac:(repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil) H) as nm;
    clear H
  end.
Lemma cw3_aview_ext : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' He a. unfold aview, mbyte, mrestrict. cbv beta. rewrite (He (Z_to_bv 64 a)). reflexivity. Qed.
Lemma cw3_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof.
intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.
(* the blocks the recorder owns are live blocks *)
Lemma cw3_O_blocks : forall ly S (rd : reader) R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O pn (Q & HA & HO) Hin. apply HO in Hin.
destruct HA as (_ & _ & _ & (Hn & HlQ & _ & Hcalls & Hsp & _) & Hans & Hrep & _ & _).
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hin). apply In_nth_error in HP as (i & HPi).
  destruct (nth_error (r_calls R) i) as [cc|] eqn:Hci.
  + destruct (Hcalls i cc P Hci HPi) as ((_ & _ & HlP & _ & _ & _ & Hargs) & _).
    apply In_nth_error in Hin as (kk & Hk).
    destruct (nth_error (snd cc) kk) as [s|] eqn:Hs.
    * exact (proj1 (proj2 (proj2 (Hargs kk s pn Hs Hk)))).
    * exfalso. apply nth_error_None in Hs. assert (Hx : nth_error P kk <> None) by congruence.
      apply nth_error_Some in Hx. lia.
  + exfalso. apply nth_error_None in Hci. assert (Hx : nth_error (l_calls Q) i <> None) by congruence.
    apply nth_error_Some in Hx. lia.
- apply in_app_or in Hin as [Hin | Hin].
  + destruct Hsp as (_ & _ & HlP & _ & _ & _ & Hargs).
    apply In_nth_error in Hin as (kk & Hk).
    destruct (nth_error (snd (r_spill R)) kk) as [s|] eqn:Hs.
    * exact (proj1 (proj2 (proj2 (Hargs kk s pn Hs Hk)))).
    * exfalso. apply nth_error_None in Hs. assert (Hx : nth_error (l_spill Q) kk <> None) by congruence.
      apply nth_error_Some in Hx. lia.
  + apply in_app_or in Hin as [Hin | Hin].
    * unfold aanswer_at in Hans. destruct (l_answer Q) as [q|]; cbn [oblk In] in Hin; [|contradiction].
      destruct Hin as [<- | []]. destruct (r_answer R); [|contradiction]. exact (proj1 (proj2 (proj2 Hans))).
    * unfold areply_at in Hrep. destruct (l_reply Q) as [q|]; cbn [oblk In] in Hin; [|contradiction].
      destruct Hin as [<- | []]. destruct (r_reply R); [|contradiction].
      exact (proj1 (proj2 (proj2 (proj2 (proj2 Hrep))))).
Qed.
(* the walk's footprint lies below the allocator's ceiling *)
Lemma cw3_FP_low : forall c a, cw_pre B MT c -> inFP (cw_FP c) a -> a < alloc_ceiling.
Proof.
intros c a HP (r & Hr & Ha). pose proof asan_consts as (C1 & _).
unfold cw_FP, CHAIN_WORDS_PG in Hr. apply in_app_or in Hr as [Hr | Hr].
- cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  pose proof (cw3_O_blocks _ _ _ _ _ _ (cp_rec _ _ _ HP) Hin) as Hb.
  pose proof (cp_afn _ _ _ HP) as (HAR & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb) as (_ & _ & Hc & _). lia.
Qed.
(* the frame record the prologue wrote (ra at sp0 - 8, s0 at sp0 - 16) extends the caller's chain *)
Lemma cw3_chain : forall c ly3 S3 W3 (m : word -> option byte) md3 k,
cw_pre B MT c ->
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly3 S3 W3 m md3 k ->
(forall j r, nth_error cw_saved j = Some r ->
  rdword (rdW W3 m) (cw_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)))) ->
exists ch1, achain ly3 (rdW W3 m) (cw_s1 c) (cw_sp0 c) ch1.
Proof.
intros c ly3 S3 W3 m md3 k HP HJ HSV.
pose proof (cp_afn _ _ _ HP) as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & G1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
assert (FS : 176 <= CHAIN_WORDS_STK) by (unfold CHAIN_WORDS_STK, NUMBER_STK, ESTACK; lia).
destruct (cw_s1_facts c Hal16) as (Hs1m & Hs1).
unfold cw_sp0 in *.
destruct (Z_lt_le_dec (spZ (x_regs c)) (ly_top (x_ly c) - 16)) as [Hlt | Hge].
- exists ((spZ (x_regs c), raZ (x_regs c), s0Z (x_regs c)) :: x_ch c).
  apply (achain_ly_top (x_ly c) ly3 _ _ _ _ Etop).
  pose proof (HSV 0%nat 1 eq_refl) as H0. pose proof (HSV 1%nat 8 eq_refl) as H1.
  change (Z.of_nat 0) with 0 in H0. change (Z.of_nat 1) with 1 in H1.
  replace (spZ (x_regs c) - 8 - 8 * 0) with (spZ (x_regs c) - 8) in H0 by lia.
  replace (spZ (x_regs c) - 8 - 8 * 1) with (spZ (x_regs c) - 16) in H1 by lia.
  assert (Q1 : getr (x_regs c) (Z_to_bv 5 1) = getr (x_regs c) 1) by (f_equal; apply bv_eq; reflexivity).
  assert (Q8 : getr (x_regs c) (Z_to_bv 5 8) = getr (x_regs c) 8) by (f_equal; apply bv_eq; reflexivity).
  rewrite Q1 in H0. rewrite Q8 in H1.
  apply (achain_push (x_ly c) (rdW (x_W c) (x_mem c)) (rdW W3 m) (spZ (x_regs c)) (s0Z (x_regs c)) (raZ (x_regs c))
    (x_ch c) (cw_s1 c) Hch).
  + lia.
  + intros a Ha. apply G1; [lia | lia | intros HF; pose proof (cw3_FP_low c a HP HF); lia].
  + exact H0.
  + exact H1.
  + exact Hra4.
  + lia.
  + Z.div_mod_to_equations. lia.
  + lia.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
(* a run that writes nothing keeps the frame part and the untouched part of a cut *)
Lemma cw3_un_ext : forall c ly S W (m m' : word -> option byte), (forall x, m' x = m x) ->
cw_un B MT c ly S W m -> cw_un B MT c ly S W m'.
Proof.
intros c ly S W m m' He [U1 U2 U3 U4 U5 U6 U7 U8]. constructor; try assumption.
- intros a Ha Hb Hc. rewrite (cw3_aview_ext (w_H W) m m' He). exact (U1 a Ha Hb Hc).
- intros p n i Hp Hi. rewrite (cw3_aview_ext (w_H W) m m' He). exact (U2 p n i Hp Hi).
- intros cid pos a Hin Ha. rewrite (cw3_aview_ext (w_H W) m m' He). exact (U3 cid pos a Hin Ha).
- intros i Hi. rewrite (cw3_aview_ext (w_H W) m m' He). exact (U8 i Hi).
Qed.
Lemma cw3_fi_ext : forall c k ly S W regs (m : word -> option byte) md regs' m' md',
cw_fi B c k ly S W regs m md ->
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly S W m' md' k ->
(forall x, m' x = m x) ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 8 = getr regs 8 ->
getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 24 = getr regs 24 ->
cw_fi B c k ly S W regs' m' md'.
Proof.
intros c k ly S W regs m md regs' m' md' [J1 G2 G3 G4 G8 G9 G18 G24 GNT GSV GFL] HJ He E2 E3 E4 E8 E9 E18 E24.
constructor.
- exact HJ.
- rewrite E2; exact G2.
- rewrite E3; exact G3.
- rewrite E4; exact G4.
- rewrite E8; exact G8.
- rewrite E9; exact G9.
- rewrite E18; exact G18.
- rewrite E24; exact G24.
- rewrite <- GNT. apply rdword_ext. intros kk Hk. apply (cw3_aview_ext (w_H W) m m' He).
- intros j r Hj. rewrite <- (GSV j r Hj). apply rdword_ext. intros kk Hk. apply (cw3_aview_ext (w_H W) m m' He).
- rewrite <- GFL. apply rdword_ext. intros kk Hk. apply (cw3_aview_ext (w_H W) m m' He).
Qed.
(* the frame part of a cut carried across a program call whose footprint lies below the allocator's ceiling, above
   the callee's window and clear of the frame's flag word *)
Lemma cw3_fi_call : forall c k k1 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 STK1 sp1 FP1,
cw_pre B MT c -> cw_fi B c k ly3 S3 W3 regs3 mem3 md3 ->
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
  [(3, x_fpos c)] ly4 S4 W4 mem4 md4 (k + k1) ->
ajournal SEGS B STK1 sp1 FP1 ly3 S3 W3 mem3 md3 [] ly4 S4 W4 mem4 md4 k1 ->
sp1 <= cw_s1 c ->
(forall a, inFP FP1 a -> a < alloc_ceiling) ->
(forall a, cw_F c + 504 <= a < cw_F c + 512 -> ~ inFP FP1 a) ->
aregs_preserved regs3 regs4 ->
cw_fi B c (k + k1) ly4 S4 W4 regs4 mem4 md4.
Proof.
intros c k k1 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 STK1 sp1 FP1 HP HF HJ HJc Hsp1 HFPlo HFPfl HPR.
pose proof (cp_afn _ _ _ HP) as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (H16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
assert (FS : 176 <= CHAIN_WORDS_STK) by (unfold CHAIN_WORDS_STK, NUMBER_STK, ESTACK; lia).
destruct (cw_s1_facts c H16) as (Hs1m & Hs1).
destruct HF as [HJ0 Hsp Hgp Htp Hs0 Hs1r Hs2 Hs8 Hntok Hsaved Hflag].
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _ & _ & K12 & _).
pose proof HJ0 as (_ & Hly3 & _ & _ & _ & Hfr3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _).
assert (CS : forall z, acallee_saved z -> forall r : bv 5, bv_unsigned r = z -> getr regs4 r = getr regs3 r).
{ intros z Hz r Hr. subst z. exact (cw3_pres regs3 regs4 r HPR Hz). }
unfold cw_sp0 in *.
constructor.
- exact HJ.
- rewrite (CS 2 ltac:(unfold acallee_saved; lia) 2%bv eq_refl). exact Hsp.
- rewrite (CS 3 ltac:(unfold acallee_saved; lia) 3%bv eq_refl). exact Hgp.
- rewrite (CS 4 ltac:(unfold acallee_saved; lia) 4%bv eq_refl). exact Htp.
- rewrite (CS 8 ltac:(unfold acallee_saved; lia) 8%bv eq_refl). exact Hs0.
- rewrite (CS 9 ltac:(unfold acallee_saved; lia) 9%bv eq_refl). exact Hs1r.
- rewrite (CS 18 ltac:(unfold acallee_saved; lia) 18%bv eq_refl). exact Hs2.
- rewrite (CS 24 ltac:(unfold acallee_saved; lia) 24%bv eq_refl). exact Hs8.
- rewrite <- Hntok. apply rdword_ext. intros i Hi.
  apply K9; [lia | lia | intros Hf; pose proof (HFPlo _ Hf); lia].
- intros j r Hj. rewrite <- (Hsaved j r Hj). apply rdword_ext. intros i Hi.
  assert (Hj13 : (j < 13)%nat).
  { pose proof (proj1 (nth_error_Some cw_saved j) ltac:(rewrite Hj; discriminate)) as Hl. exact Hl. }
  apply K9; [lia | lia | intros Hf; pose proof (HFPlo _ Hf); lia].
- rewrite <- Hflag. apply rdword_ext. intros i Hi.
  apply (K12 3 (x_fpos c)).
  + rewrite Hfr3. left. reflexivity.
  + left. unfold in_zr, frame_rng, cw_F, frame_addr in *. cbn [fst snd]. rewrite EF.
    change (fs_frame_bytes 3) with 512. lia.
  + apply HFPfl. lia.
Qed.
(* ids[j] is addressable: the shadow of ids[64] (frame + 32 .. frame + 288) says "usable" (cw_un's un_ids_sh) *)
Lemma cw3_ids_ra : forall (rd : reader) F j, F mod 8 = 0 -> 0 <= j <= 61 ->
  (forall i, 4 <= i < 36 -> rd (SB + F / 8 + i) = Some 0) ->
  range_addressable rd SHADOW_OFF (F + 32 + 4 * j) 4.
Proof.
intros rd F j HF Hj H x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by (unfold SB, SHADOW_OFF; lia).
apply H. Z.div_mod_to_equations. lia.
Qed.
(* errno is an image cell, a side-stack frame is not *)
Lemma cw3_apart_errno : forall ly S (W : world SEGS) mem md cid pos out,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= out -> out + 4 <= frame_addr ly cid pos + fs_frame_bytes cid ->
  iv_apart out 4 (as_errno B) 4.
Proof.
intros ly S W mem md cid pos out HAR Hin Hlo Hhi. unfold iv_apart.
destruct (Z_le_gt_dec (out + 4) (as_errno B)) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (as_errno B + 4) out) as [H2|H2]; [right; exact H2|].
exfalso. pose proof (pal_env B TL) as (_ & Himg & _).
assert (Ha1 : as_errno B <= Z.max out (as_errno B) < as_errno B + 4) by lia.
assert (Ha2 : frame_addr ly cid pos <= Z.max out (as_errno B) < frame_addr ly cid pos + fs_frame_bytes cid) by lia.
destruct (al_client_img _ _ LAWS ly S W mem md (Z.max out (as_errno B)) HAR
  (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Ha2)))))) as [_ Hni].
exact (Hni (Himg _ Ha1)).
Qed.
(* the untouched part of a cut after the call of number, whose footprint is a 4-byte cell of the walk's own frame
   and which changes only the side-stack frame state *)
Lemma cw3_un_call : forall c ly3 S3 W3 m3 md3 STK1 sp1 S2 W2 m2 md2 k1 k f out,
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly3 S3 W3 m3 md3 k ->
cw_un B MT c ly3 S3 W3 m3 ->
ajournal SEGS B STK1 sp1 [(out, out + 4)] ly3 S3 W3 m3 md3 [] ly3 S2 W2 m2 md2 k1 ->
cw_F c <= out -> out + 4 <= cw_F c + 512 ->
Permutation (ablocks B ly3 S2) (ablocks B ly3 S3) -> S2 = set_fs f S3 ->
cw_un B MT c ly3 S2 W2 m2.
Proof.
intros c ly3 S3 W3 m3 md3 STK1 sp1 S2 W2 m2 md2 k1 k f out HJ [U1 U2 U3 U4 U5 U6 U7 U8] HJc Hlo Hhi HPERM HS2.
pose proof HJ as (HAR3 & Hly & _ & _ & _ & Hfrs & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & K4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin3 : In (3, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (Hal32 & Happ & _).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 m3 md3 3 (x_fpos c) HAR3 Hin3) as (Hf0 & Hfc & _).
assert (EF3 : frame_addr ly3 3 (x_fpos c) = cw_F c) by (unfold cw_F; exact (cw3_frame_addr_le _ _ _ 3 (x_fpos c) Hly)).
assert (F512 : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
rewrite EF3 in Happ, Hf0, Hfc. rewrite F512 in Happ, Hfc.
assert (HFP : forall a, inFP [(out, out + 4)] a -> cw_F c <= a < cw_F c + 512).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [lia | exfalso; exact (inFP_nil a Ha)]. }
constructor.
- intros a Ha Hno Her. rewrite <- (U1 a Ha Hno Her). apply K3; [exact Ha | exact Hno | exact Her |].
  split.
  + intros (r & Hr & H0). exfalso.
    assert (HF0 : inFP [(out, out + 4)] 0) by (exists r; split; [exact Hr | exact H0]).
    specialize (HFP 0 HF0). lia.
  + intros HF. specialize (HFP a HF).
    assert (Ha2 : frame_addr ly3 3 (x_fpos c) <= a < frame_addr ly3 3 (x_fpos c) + fs_frame_bytes 3)
      by (rewrite EF3, F512; lia).
    destruct (al_client_img _ _ LAWS ly3 S3 W3 m3 md3 a HAR3
      (or_intror (or_introl (ex_intro _ 3 (ex_intro _ (x_fpos c) (conj Hin3 Ha2)))))) as [_ Hni].
    exact (Hni Ha).
- intros p n i Hin Hi. rewrite <- (U2 p n i Hin Hi).
  assert (Hin3b : In (p, n) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym U4)); exact Hin).
  assert (Hin2 : In (p, n) (ablocks B ly3 S2)) by (apply (Permutation_in _ (Permutation_sym HPERM)); exact Hin3b).
  apply (K2 p n i Hin3b Hin2 Hi). intros HF. specialize (HFP _ HF).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 m3 md3 p n 3 (x_fpos c) HAR3 Hin3b Hin3) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF3, F512 in Hd. lia.
- intros cid pos a Hin Ha. rewrite <- (U3 cid pos a Hin Ha).
  assert (Hin3c : In (cid, pos) (frames S3)) by (rewrite Hfrs; right; exact Hin).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 m3 md3 cid pos HAR3 Hin3c) as (Hg0 & Hgc & _).
  pose proof (cw3_frame_addr_le _ _ _ cid pos Hly) as EFg.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  apply (K4 cid pos a Hin3c).
  + unfold frame_rng in *. cbn [fst snd] in *. rewrite EFg. exact Ha.
  + intros HF. specialize (HFP a HF). unfold frame_rng in Ha. cbn [fst snd] in Ha. rewrite <- EFg in Ha.
    destruct Ha as [Ha | Ha].
    * apply in_split in Hin as (l2 & l3 & El).
      assert (Ef : frames S3 = [] ++ (3, x_fpos c) :: l2 ++ (cid, pos) :: l3) by (rewrite Hfrs, El; reflexivity).
      pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 m3 md3 (3, x_fpos c) (cid, pos) [] l2 l3 HAR3 Ef) as Hd.
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EF3, F512 in Hd.
      unfold in_zr in Ha. cbn [fst snd] in Ha. lia.
    * unfold in_zr in Ha. cbn [fst snd] in Ha.
      apply (cw3_app_shadow a (cw_F c) 512 (frame_addr ly3 cid pos) (fs_frame_bytes cid)
        (a - shadow_addr (frame_addr ly3 cid pos)) Happ ltac:(lia) Hg0 Hgc ltac:(lia)). lia.
- exact (Permutation_trans HPERM U4).
- subst S2. exact U5.
- subst S2. exact U6.
- subst S2. exact (mo_le_set_fs_r MT MTFL _ _ _ _ U7).
- intros i Hi. rewrite <- (U8 i Hi).
  assert (Hsh : in_zr (SB + cw_F c / 8 + i) (shadow_addr (frame_addr ly3 3 (x_fpos c)), fs_frame_bytes 3 / 8)).
  { unfold in_zr, shadow_addr, SB, SHADOW_OFF. cbn [fst snd]. rewrite EF3, F512. change (512 / 8) with 64. lia. }
  apply (K4 3 (x_fpos c) _ Hin3); [right; exact Hsh|].
  intros HF. specialize (HFP _ HF).
  apply (cw3_app_shadow (SB + cw_F c / 8 + i) (cw_F c) 512 (cw_F c) 512 i Happ ltac:(lia) Hf0 Hfc
    ltac:(change (512 / 8) with 64; lia)).
  unfold shadow_addr, SB, SHADOW_OFF. lia.
Qed.

(* the symbolic state at KL: &tok[2 + j] is atom 32 (no register holds it yet), its word atom 33, and s8's atom
   (24) is the shadow base of the inline check *)
Lemma cw3_seedL : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) tok ntok X p,
AR SEGS B ly S W mem md ->
getr regs 24 = w64 SB ->
afobj SEGS B ly S W mem tok (8 * ntok) -> tok + 16 <= X -> X + 8 <= tok + 8 * ntok -> X mod 8 = 0 ->
aval_mem (rdW W mem) X 8 p -> 0 <= p < 2 ^ 64 ->
st_ok_pi SEGS VAL (cw3_EL regs X p) ss_cw3L
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CW_KL)) mem (seg_rom SEGS))) /\
sh_ok SEGS cw3_Bx cw3_SH (cw3_EL regs X p) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs tok ntok X p HAR H24 ((cid & pos & Hfr & Hcid & Hfa8 & Hlo & Hhi) & Htok8 & Hra)
  HX1 HX2 HX8 HP Hp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfr) as (Hf0 & Hfc & Happ).
set (E := cw3_EL regs X p).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold cw3_EL. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew E 32 = w64 X) by (subst E; unfold cw3_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (X33 : ew E 33 = w64 p) by (subst E; unfold cw3_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E24 : ew E 24 = Z_to_bv 64 SB) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (U32 : base_val E (Some 32%nat) = X).
{ cbn [base_val]. rewrite X32. apply unsigned_lit_small. lia. }
split.
- rewrite restrict_mkst_fx. unfold ss_cw3L. apply pa_entry_st_ok_full.
  + subst E. unfold cw3_EL. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cw3_tokR. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ X 0 8 (SOff 33 0) p);
      [cbn [sv_denot]; rewrite X33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | rewrite Z.add_0_r; exact (cw3_val_mem SEGS (w_H W) mem _ 8%nat p HP)].
  + apply pairwise_disjoint_of_extents. unfold cw3_tokR, extent_of_region.
    cbn. repeat constructor.
  + split; [|split; [exact I | exact I]].
    cbn [cw3_factsL f_atoms atoms_ok].
    split; [apply (cw3_afact E 24%nat SB); [exact E24 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    split; [apply (cw3_afact E 32%nat X); [exact X32 | lia | lia | change (2 ^ 3) with 8; exact HX8 | lia]|].
    exact I.
- unfold sh_ok, cw3_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E cw3_Bx 32 tok (8 * ntok) X 0 8 Hra).
  + unfold cw3_Bx. apply U_atom; [exact E24 | cbv [SB SHADOW_OFF]; lia].
  + apply U_atom; [exact X32 | lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia.
Qed.
(* after the call: the registers, a0 pinned to number's result, and the word at s1 + 24 (ntok) *)
Lemma cw3_seedR : forall (W : world SEGS) mem (regs : bvmap 5 word) a0 s1 n,
getr regs 10 = Z_to_bv 64 a0 -> getr regs 9 = w64 s1 -> 4096 <= s1 -> s1 + 32 <= 2 ^ 47 -> s1 mod 8 = 0 ->
rdword (rdW W mem) (s1 + 24) = Some n -> 0 <= n <= 64 ->
st_ok_pi SEGS VAL (cw3_ER regs n) (ss_cw3A a0)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CW3_RET)) mem (seg_rom SEGS))) /\
sh_ok SEGS cw3_Bx [] (cw3_ER regs n) (mrestrict (w_H W) mem).
Proof.
intros W mem regs a0 s1 n H10 H9 Hs1a Hs1b Hs18 Hnt Hn. split; [|constructor].
set (E := cw3_ER regs n).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold cw3_ER. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew E 32 = w64 n) by (subst E; unfold cw3_ER; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (rewrite (EEo 9%nat 9%bv eq_refl); exact H9).
assert (U9 : base_val E (Some 9%nat) = s1).
{ cbn [base_val]. rewrite E9. apply unsigned_lit_small. lia. }
assert (HS : st_ok_pi SEGS VAL E ss_cw3R
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CW3_RET)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cw3R. apply pa_entry_st_ok_full.
  - subst E. unfold cw3_ER. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold cw3_ntokR. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ s1 24 8 (SOff 32 0) n);
      [cbn [sv_denot]; rewrite X32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Hnt)].
  - apply pairwise_disjoint_of_extents. unfold cw3_ntokR, extent_of_region. cbn. repeat constructor.
  - split; [|split; [exact I | exact I]].
    cbn [cw3_factsR f_atoms atoms_ok].
    split; [apply (cw3_afact E 9%nat s1); [exact E9 | lia | lia | change (2 ^ 3) with 8; exact Hs18 | lia]|].
    exact I. }
exact (st_ok_pi_pin_reg' _ _ _ 10%bv a0 HS H10 eq_refl).
Qed.

(* number's post (number_c.v:116-124) at a call with word wd and result cell out *)
Definition cw3_numQ (wd : list byte) (out : Z) (W : world SEGS) (mem : word -> option byte) (ly : alayout) (S : astate)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 match Verbs.number_m wd with
 | Some v => getr regs' 10 = w64 1 /\ aval_mem (rdW W' mem') out 4 v
 | None => getr regs' 10 = w64 0 /\ (forall i, 0 <= i < 4 -> rdW W' mem' (out + i) = rdW W mem (out + i))
 end /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 ly' = ly /\ (exists f, S' = set_fs f S).
Ltac cw3_q HP2 r :=
  apply (cw3_pres _ _ r HP2); cbv [acallee_saved];
  match goal with |- context [bv_unsigned ?x] => let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end;
  lia.

Lemma cw_S3 : cw_S3P B MT.
Proof.
intros c j HPRE HKR HKD HKL1. unfold from_KL, cw_from.
intros ly3 S3 W3 regs3 mem3 md3
  ((HFI & HUN) & HSPL & Hj & R19 & R20 & R21 & R22 & R23 & R25 & R26 & R27 & (id & vs & Hid & Hvs & Hidm & Hvsm)).
pose proof (TRANSP c 0 ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as (HTOK & HTOKS & HCB & HREC & HROD & HRO).
pose proof HFI as [HJ F2 F3 F4 F8 F9 F18 F24 FNT FSV FFLG].
pose proof (proj1 HJ) as HAR3.
pose proof (cp_ntok _ _ _ HPRE) as HN. pose proof (cp_ntokr _ _ _ HPRE) as HNR.
pose proof (cp_tok64 _ _ _ HPRE) as HT64.
pose proof HTOKS as (Htk8 & Hlen & Hptr & Hwd).
destruct (nth_error (x_ptrs c) (2 + Z.to_nat j)) as [p|] eqn:Hpn;
  [| exfalso; apply nth_error_None in Hpn; rewrite Hlen in Hpn; lia].
destruct (nth_error (x_tks c) (2 + Z.to_nat j)) as [wd|] eqn:Hwdn;
  [| exfalso; apply nth_error_None in Hwdn; lia].
pose proof (Hptr _ p Hpn) as HP.
replace (x_tok c + 8 * Z.of_nat (2 + Z.to_nat j)) with (x_tok c + 16 + 8 * j) in HP by lia.
destruct (Hwd _ p wd Hpn Hwdn) as (HSTR & HWL & HCBP & HPCB).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HCB) as (_ & Hcb4096 & Hcbc & _ & _ & _ & Hncb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (req_size_pos (x_ncb c) (proj1 Hncb)) as Hreqcb.
assert (Hp64 : 0 <= p < 2 ^ 64) by lia.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (Hal32 & Happ & _).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 3 (x_fpos c) HAR3 Hin3) as (Hf0 & Hfc & _).
assert (EF3 : frame_addr ly3 3 (x_fpos c) = cw_F c) by (unfold cw_F; exact (cw3_frame_addr_le _ _ _ 3 (x_fpos c) Hly)).
assert (F512 : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
rewrite EF3 in Happ, Hf0, Hfc, Hal32. rewrite F512 in Happ, Hfc.
pose proof HTOK as ((tcid & tpos & Htfr & _ & _ & Htlo & Hthi) & _ & _).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 tcid tpos HAR3 Htfr) as (Ht0 & Htc & _).
assert (HTR : 4096 <= x_tok c /\ x_tok c + 8 * x_ntok c <= alloc_ceiling) by lia.
clear tcid tpos Htfr Htlo Hthi Ht0 Htc.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (cw_s1_facts c Hal16) as (Hs1m & Hs1).
assert (FS : 176 + NUMBER_STK <= CHAIN_WORDS_STK) by (unfold CHAIN_WORDS_STK; lia).
assert (FN : 0 <= NUMBER_STK) by (unfold NUMBER_STK, ESTACK; lia).
set (out := cw_F c + 32 + 4 * j).
(* the seed at KL *)
destruct (cw3_seedL ly3 S3 W3 mem3 md3 regs3 (x_tok c) (x_ntok c) (x_tok c + 16 + 8 * j) p HAR3 F24 HTOK
  ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia) HP Hp64) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (cw3_EL regs3 (x_tok c + 16 + 8 * j) p)) by (unfold cw3_EL; apply Eimg_env).
set (E := cw3_EL regs3 (x_tok c + 16 + 8 * j) p) in *.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs3 rr).
{ intros m rr Hm. subst E. unfold cw3_EL. rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 rr) as Hr5;
    change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew E 32 = w64 (x_tok c + 16 + 8 * j))
  by (subst E; unfold cw3_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (X33 : ew E 33 = w64 p)
  by (subst E; unfold cw3_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
(* the loop registers as values of their atoms *)
assert (UA19 : U E (SOff 19 0) = 65 - j)
  by (apply U_atom; [rewrite (EEo 19%nat 19%bv eq_refl); exact R19 | lia]).
assert (UA20 : U E (SOff 20 0) = 2 ^ 64 - 1 - (cw_F c + 32))
  by (apply U_atom; [rewrite (EEo 20%nat 20%bv eq_refl); exact R20 | lia]).
assert (UA21 : U E (SOff 21 0) = x_tok c)
  by (apply U_atom; [rewrite (EEo 21%nat 21%bv eq_refl); exact R21 | lia]).
assert (UA22 : U E (SOff 22 0) = cw_F c + 32)
  by (apply U_atom; [rewrite (EEo 22%nat 22%bv eq_refl); exact R22 | lia]).
assert (UA25 : U E (SOff 25 0) = 4 * j)
  by (apply U_atom; [rewrite (EEo 25%nat 25%bv eq_refl); exact R25 | lia]).
assert (UA26 : U E (SOff 26 0) = 2 ^ 64 - 1 - x_tok c)
  by (apply U_atom; [rewrite (EEo 26%nat 26%bv eq_refl); exact R26 | lia]).
assert (UA27 : U E (SOff 27 0) = 16 + 8 * j)
  by (apply U_atom; [rewrite (EEo 27%nat 27%bv eq_refl); exact R27 | lia]).
assert (UA32 : U E (SOff 32 0) = x_tok c + 16 + 8 * j) by (apply U_atom; [exact X32 | lia]).
unfold cfg_at, w64.
(* +0x278: the UBSan trap check ~tok < 16 + 8 j *)
psrr_branch_tok RUN BR HS SHOK cw3_Bspan.
- exfalso. rewrite branch_ltu_U, UA26, UA27 in Hc. apply Z.ltb_lt in Hc. lia.
- (* +0x27c: &tok[2 + j]; pin it to atom 32 *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK cw3_Bspan CW3_PIN.
  { apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
  cw3_name HS msA. cw3_ro QA.
  cw3_mdv mdv.
  assert (HPIN : sv_denot E (SOff 32 0) = sv_denot E cw3_a0p).
  { rewrite !denot_lit_U. f_equal. unfold cw3_a0p. rewrite UA32, U_SAlu, UA21, UA27.
    cbn [zalu_raw]. rewrite zcanon_small by lia. lia. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    assert (HPIN' : sv_denot E (SOff 32 0) = sv_denot E (sr_get (ss_regs ss) 10%bv))
      by (replace (sr_get (ss_regs ss) 10%bv) with cw3_a0p by (vm_compute; reflexivity); exact HPIN) end.
  pose proof (cw3_set_reg E _ _ 10%bv (SOff 32 0) HS HPIN' eq_refl) as HS2.
  clear HS HPIN HPIN'. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?m => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
  (* +0x280..+0x28c: the shadow address, the inline check; stop at the trap check 65 - j = 0 *)
  paj_run_tok RUN HS HJ SHOK cw3_Bspan.
  { apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
  cw3_name HS msB. cw3_ro QB.
  cw3_mdv mdv2.
  psrr_branch_tok RUN BR HS SHOK cw3_Bspan.
  + exfalso. rewrite branch_eq_U, UA19, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    apply Z.eqb_eq in Hc. lia.
  + (* +0x294: the UBSan trap check ~(F + 32) < 4 j *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK cw3_Bspan.
    { apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
    cw3_name HS msC. cw3_ro QC.
    cw3_mdv mdv3.
    psrr_branch_tok RUN BR HS SHOK cw3_Bspan.
    * exfalso. rewrite branch_ltu_U, UA20, UA25 in Hc. apply Z.ltb_lt in Hc. lia.
    * (* +0x298..+0x2a0: the word, &ids[j], the call of number *)
      clear Hc.
      paj_run_tok RUN HS HJ SHOK cw3_Bspan.
      { apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
      cw3_name HS msD. cw3_ro QD.
      pmkst HS. cw3_mdv mdv4.
      prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
      prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
      prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
      prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
      prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
      prreg HS (27%bv : bv 5) P27.
      cw3_rr HS (10%bv : bv 5) T10. cw3_rr HS (11%bv : bv 5) T11.
      rewrite (EEo 2%nat 2%bv eq_refl) in P2. rewrite (EEo 3%nat 3%bv eq_refl) in P3.
      rewrite (EEo 4%nat 4%bv eq_refl) in P4. rewrite (EEo 8%nat 8%bv eq_refl) in P8.
      rewrite (EEo 9%nat 9%bv eq_refl) in P9. rewrite (EEo 18%nat 18%bv eq_refl) in P18.
      rewrite (EEo 19%nat 19%bv eq_refl) in P19. rewrite (EEo 20%nat 20%bv eq_refl) in P20.
      rewrite (EEo 21%nat 21%bv eq_refl) in P21. rewrite (EEo 22%nat 22%bv eq_refl) in P22.
      rewrite (EEo 23%nat 23%bv eq_refl) in P23. rewrite (EEo 24%nat 24%bv eq_refl) in P24.
      rewrite (EEo 25%nat 25%bv eq_refl) in P25. rewrite (EEo 26%nat 26%bv eq_refl) in P26.
      rewrite (EEo 27%nat 27%bv eq_refl) in P27.
      rewrite U_SOff, X33, unsigned_lit_small, Z.add_0_r, zcanon_small in T10 by lia.
      rewrite U_SAlu, UA22, UA25 in T11. cbn [zalu_raw] in T11. rewrite zcanon_small in T11 by lia.
      (* the four runs wrote nothing: the memory at the call is the cut's *)
      assert (HEQ : forall x, ms_mem msD x = mem3 x)
        by (intros x; rewrite (QD x), (QC x), (QB x); exact (QA x)).
      pose proof (cw3_fi_ext c 0 ly3 S3 W3 regs3 mem3 md3 (ms_regs msD) (ms_mem msD) mdv4 HFI HJ HEQ P2 P3 P4 P8 P9 P18 P24)
        as HFIc.
      pose proof (cw3_un_ext c ly3 S3 W3 mem3 (ms_mem msD) HEQ HUN) as HUNc.
      destruct (TRANSP c 0 ly3 S3 W3 (ms_regs msD) (ms_mem msD) mdv4 HPRE HFIc HUNc) as
        (HTOKc & HTOKSc & HCBc & HRECc & HRODc & HROc).
      pose proof HTOKSc as (_ & _ & _ & Hwdc).
      destruct (Hwdc _ p wd Hpn Hwdn) as (HSTRc & _ & _ & _).
      pose proof HFIc as [_ _ _ _ _ _ _ _ _ FSVc _].
      pose proof HUN as [U1 U2 U3 U4 U5 U6 U7 U8].
      pose proof HUNc as [_ _ _ _ _ _ _ U8c].
      assert (Ho16 : (cw_s1 c - cw_sp0 c) mod 16 = 0).
      { destruct Hs1 as [-> | ->]; [replace (cw_sp0 c - 160 - cw_sp0 c) with (-160) by lia
        | replace (cw_sp0 c - 176 - cw_sp0 c) with (-176) by lia]; reflexivity. }
      assert (HSPc : spZ (ms_regs msD) = cw_sp0 c + (cw_s1 c - cw_sp0 c)).
      { unfold spZ. rewrite P2, F2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
      destruct (cw3_chain c ly3 S3 W3 (ms_mem msD) mdv4 0 HPRE HJ FSVc) as (ch1 & HCH).
      assert (HCH' : achain ly3 (rdW W3 (ms_mem msD)) (cw_sp0 c + (cw_s1 c - cw_sp0 c)) (s0Z (ms_regs msD)) ch1).
      { replace (cw_sp0 c + (cw_s1 c - cw_sp0 c)) with (cw_s1 c) by lia.
        replace (s0Z (ms_regs msD)) with (cw_sp0 c)
          by (unfold s0Z; rewrite P8, F8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
        exact HCH. }
      assert (P3' : getr (ms_regs msD) 3 = w64 (as_gp B)) by (rewrite P3; exact F3).
      assert (P4' : getr (ms_regs msD) 4 = w64 (as_tp B)) by (rewrite P4; exact F4).
      pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
      assert (HRA : YK0s.ret_ok (getr (ms_regs msD) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
      assert (HRA4 : 4096 <= bv_unsigned (getr (ms_regs msD) 1))
        by (rewrite P1, unsigned_lit_small by lia; lia).
      assert (Hout64 : 0 <= out < 2 ^ 64) by (unfold out; lia).
      assert (HINB : in_blockA (ablocks B ly3 S3) p (Z.of_nat (length wd) + 1)).
      { exists (x_cb c), (x_ncb c). split; [exact HCB | lia]. }
      assert (HWL' : Z.of_nat (length wd) + 1 <= LMAX + 1) by (unfold LMAX; lia).
      assert (Hout4 : out mod 4 = 0) by (unfold out; clear - Hal32; Z.div_mod_to_equations; lia).
      assert (HOUT : ((exists cid pos, In (cid, pos) (frames S3) /\
         frame_addr ly3 cid pos <= out /\ out + 4 <= frame_addr ly3 cid pos + fs_frame_bytes cid) /\
        range_addressable (rdW W3 (ms_mem msD)) SHADOW_OFF out 4) \/
        (spZ (ms_regs msD) <= out /\ out + 4 <= ly_top ly3 /\ (forall i, 0 <= i < 4 -> apresent (w_H W3) (ms_mem msD) (out + i)))).
      { left. split.
        - exists 3, (x_fpos c). split; [exact Hin3|]. rewrite EF3, F512. unfold out. lia.
        - apply (cw3_ids_ra _ (cw_F c) j); [clear - Hal32; Z.div_mod_to_equations; lia | lia | exact U8c]. }
      assert (HAPART : iv_apart out 4 (as_errno B) 4).
      { apply (cw3_apart_errno ly3 S3 W3 (ms_mem msD) mdv4 3 (x_fpos c) out (proj1 HJ) Hin3);
        rewrite ?EF3, ?F512; unfold out; lia. }
      assert (HFR6 : Z.of_nat (length (frames S3)) <= 6).
      { rewrite Hfrs. cbn [app length]. pose proof (cp_frames _ _ _ HPRE). lia. }
      assert (EVR : 0 <= EV_SUP_RESP) by (apply Z.leb_le; vm_compute; reflexivity).
      assert (HNEV0 : st_nev S3 + EV_NUMBER <= EV_MAX).
      { pose proof (cp_nev _ _ _ HPRE). unfold EV_CHAIN_WORDS, EV_NUMBER in *. lia. }
      assert (HFPlo : forall a, inFP [(out, out + 4)] a -> cw_F c + 32 + 4 * j <= a < cw_F c + 32 + 4 * j + 4).
      { intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold out in Ha; lia | exfalso; exact (inFP_nil a Ha)]. }
      rewrite (proj1 (cw_sig_of SIGP)).
      eapply SRr_bind.
      { refine (cl_callS_wide B LAWS W3 (ms_regs msD) (ms_mem msD) (Z_to_bv 64 (BASE + AF_number)) CHAIN_WORDS_STK (cw_sp0 c)
          (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)] ly3 S3 mdv4 0 NUMBER_STK
          [(out, out + 4)] EV_NUMBER (cw_s1 c - cw_sp0 c) (getr (ms_regs msD) 1) ch1
          (cw3_numQ wd out W3 (ms_mem msD) ly3 S3)
          HJ HSPc Ho16 ltac:(lia) FN ltac:(lia) P3' P4' eq_refl HRA HRA4 HCH' _ _ _).
        - intros HPRE1. exact (NUMBER fx ly3 S3 W3 (ms_regs msD) (ms_mem msD) mdv4 ch1 p out wd HPRE1 HRODc T10 Hp64 T11
            Hout64 HINB HSTRc HWL' Hout4 HOUT HAPART HFR6 HNEV0).
        - intros a Ha. right; right; right; left. exists 3, (x_fpos c). split; [left; reflexivity|]. left.
          pose proof (HFPlo a Ha). unfold in_zr. cbn [fst snd]. rewrite EF3, F512. lia.
        - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. pose proof (HFPlo a Ha). lia. }
      cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
      replace (cw_sp0 c + (cw_s1 c - cw_sp0 c)) with (cw_s1 c) in HJc2 by lia.
      rewrite P1.
      unfold cw3_numQ in HK2. destruct HK2 as (HNUM & HPERM2 & -> & (f & ->)).
      assert (Q2 : getr regs2 2 = getr (ms_regs msD) 2) by cw3_q HP2 (2%bv : bv 5).
      assert (Q3 : getr regs2 3 = getr (ms_regs msD) 3) by cw3_q HP2 (3%bv : bv 5).
      assert (Q4 : getr regs2 4 = getr (ms_regs msD) 4) by cw3_q HP2 (4%bv : bv 5).
      assert (Q8 : getr regs2 8 = getr (ms_regs msD) 8) by cw3_q HP2 (8%bv : bv 5).
      assert (Q9 : getr regs2 9 = getr (ms_regs msD) 9) by cw3_q HP2 (9%bv : bv 5).
      assert (Q18 : getr regs2 18 = getr (ms_regs msD) 18) by cw3_q HP2 (18%bv : bv 5).
      assert (Q19 : getr regs2 19 = getr (ms_regs msD) 19) by cw3_q HP2 (19%bv : bv 5).
      assert (Q20 : getr regs2 20 = getr (ms_regs msD) 20) by cw3_q HP2 (20%bv : bv 5).
      assert (Q21 : getr regs2 21 = getr (ms_regs msD) 21) by cw3_q HP2 (21%bv : bv 5).
      assert (Q22 : getr regs2 22 = getr (ms_regs msD) 22) by cw3_q HP2 (22%bv : bv 5).
      assert (Q23 : getr regs2 23 = getr (ms_regs msD) 23) by cw3_q HP2 (23%bv : bv 5).
      assert (Q24 : getr regs2 24 = getr (ms_regs msD) 24) by cw3_q HP2 (24%bv : bv 5).
      assert (Q25 : getr regs2 25 = getr (ms_regs msD) 25) by cw3_q HP2 (25%bv : bv 5).
      assert (Q26 : getr regs2 26 = getr (ms_regs msD) 26) by cw3_q HP2 (26%bv : bv 5).
      assert (Q27 : getr regs2 27 = getr (ms_regs msD) 27) by cw3_q HP2 (27%bv : bv 5).
      assert (HFP1 : forall a, inFP [(out, out + 4)] a -> a < alloc_ceiling) by (intros a Ha; pose proof (HFPlo a Ha); lia).
      assert (HFP2 : forall a, cw_F c + 504 <= a < cw_F c + 512 -> ~ inFP [(out, out + 4)] a)
        by (intros a Ha Hf; pose proof (HFPlo a Hf); lia).
      pose proof (cw3_fi_call c 0 EV_NUMBER ly3 S3 W3 (ms_regs msD) (ms_mem msD) mdv4 ly3 (set_fs f S3) W2 regs2 mem2 md2
        NUMBER_STK (cw_s1 c) [(out, out + 4)] HPRE HFIc HJ2 HJc2 ltac:(lia) HFP1 HFP2 HP2) as HFI2.
      pose proof (cw3_un_call c ly3 S3 W3 (ms_mem msD) mdv4 NUMBER_STK (cw_s1 c) (set_fs f S3) W2 mem2 md2 EV_NUMBER 0 f out
        HJ HUNc HJc2 ltac:(unfold out; lia) ltac:(unfold out; lia) HPERM2 eq_refl) as HUN2.
      change (0 + EV_NUMBER) with 0 in HFI2, HJ2.
      (* what number kept: the caller's realigned frame (the spills, the id cell, ntok) and ids[0..j) *)
      pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & K1c & _ & _ & K4c & _).
      assert (HKs1 : forall a, cw_s1 c <= a < cw_s1 c + 56 -> rdW W2 mem2 a = rdW W3 mem3 a).
      { intros a Ha. rewrite K1c; [exact (cw3_aview_ext (w_H W3) mem3 (ms_mem msD) HEQ _) | lia | lia |].
        intros HF0. pose proof (HFP1 _ HF0). lia. }
      assert (HKvs : forall i, 0 <= i < 4 * j -> rdW W2 mem2 (cw_F c + 32 + i) = rdW W3 mem3 (cw_F c + 32 + i)).
      { intros i Hi. rewrite (K4c 3 (x_fpos c)); [exact (cw3_aview_ext (w_H W3) mem3 (ms_mem msD) HEQ _) | exact Hin3 | |].
        - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF3, F512. lia.
        - intros HF0. pose proof (HFPlo _ HF0). lia. }
      assert (Hlvs : length vs = Z.to_nat j).
      { rewrite (cw3_numbers_len _ _ Hvs), firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
      assert (Hidm2 : aval_mem (rdW W2 mem2) (cw_s1 c + 52) 4 id).
      { apply (cw3_aval_ext _ _ _ _ _ Hidm). intros i Hi. apply HKs1. lia. }
      assert (Hvsm2 : abytes_atR (rdW W2 mem2) (cw_F c + 32) (concat (map le32 vs))).
      { apply (cw3_abytes_ext _ _ _ _ Hvsm). intros i Hi. rewrite cw3_len_ids, Hlvs in Hi. apply HKvs. lia. }
      assert (HSPL2 : cw_spills c W2 mem2).
      { destruct HSPL as [Sp1 Sp2]. split.
        - rewrite <- Sp1. apply rdword_ext. intros i Hi. apply HKs1. lia.
        - rewrite <- Sp2. apply rdword_ext. intros i Hi. apply HKs1. lia. }
      assert (Hwds : nth_error (skipn 2 (x_tks c)) (Z.to_nat j) = Some wd) by (rewrite cw3_nth_skipn; exact Hwdn).
      clear HS SHOK HEI.
      (* the seed after the call *)
      pose proof HFI2 as [_ _ _ _ _ G9' _ _ GNT2 _ _].
      destruct (Verbs.number_m wd) as [v|] eqn:Hnum.
      -- (* number accepted tok[2 + j]: the advance and the loop's exit test *)
         destruct HNUM as (HA1 & HVAL).
         assert (Hvs1 : Verbs.numbers_m (firstn (S (Z.to_nat j)) (skipn 2 (x_tks c))) = Some (vs ++ [v])).
         { rewrite (cw3_firstn_S _ _ _ Hwds), cw3_numbers_app, Hvs. cbn [Verbs.numbers_m]. rewrite Hnum. reflexivity. }
         assert (Hidm3 : forall m', (forall x, m' x = mem2 x) -> aval_mem (rdW W2 m') (cw_s1 c + 52) 4 id).
         { intros m' Hm'. apply (cw3_aval_ext _ _ _ _ _ Hidm2). intros i Hi. exact (cw3_aview_ext (w_H W2) mem2 m' Hm' _). }
         assert (Hvsm3 : forall m', (forall x, m' x = mem2 x) ->
           abytes_atR (rdW W2 m') (cw_F c + 32) (concat (map le32 (vs ++ [v])))).
         { intros m' Hm'. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r.
           apply (cw3_abytes_ext (rdW W2 mem2)); [| intros i Hi; exact (cw3_aview_ext (w_H W2) mem2 m' Hm' _)].
           apply cw3_abytes_app; [exact Hvsm2|].
           replace (cw_F c + 32 + Z.of_nat (length (concat (map le32 vs)))) with out
             by (rewrite cw3_len_ids, Hlvs; unfold out; lia).
           exact (cw3_le32 _ _ _ HVAL). }
         destruct (cw3_seedR W2 mem2 regs2 1 (cw_s1 c) (x_ntok c) HA1 G9' ltac:(lia) ltac:(lia)
           ltac:(clear - Hs1m; Z.div_mod_to_equations; lia) GNT2 ltac:(lia)) as [HS2 SHOK2].
         assert (HEIR : img_env VAL A_LIM (cw3_ER regs2 (x_ntok c))) by (unfold cw3_ER; apply Eimg_env).
         set (E2 := cw3_ER regs2 (x_ntok c)) in *.
         assert (EEo2 : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E2 m = getr regs2 rr).
         { intros m rr Hm. subst E2. unfold cw3_ER. rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 rr) as Hr5;
             change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
         assert (Y32 : ew E2 32 = w64 (x_ntok c))
           by (subst E2; unfold cw3_ER; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
         assert (VA19 : U E2 (SOff 19 0) = 65 - j)
           by (apply U_atom; [rewrite (EEo2 19%nat 19%bv eq_refl), Q19, P19; exact R19 | lia]).
         assert (VA21 : U E2 (SOff 21 0) = x_tok c)
           by (apply U_atom; [rewrite (EEo2 21%nat 21%bv eq_refl), Q21, P21; exact R21 | lia]).
         assert (VA22 : U E2 (SOff 22 0) = cw_F c + 32)
           by (apply U_atom; [rewrite (EEo2 22%nat 22%bv eq_refl), Q22, P22; exact R22 | lia]).
         assert (VA23 : U E2 (SOff 23 0) = 67)
           by (apply U_atom; [rewrite (EEo2 23%nat 23%bv eq_refl), Q23, P23; exact R23 | lia]).
         assert (VA25 : U E2 (SOff 25 0) = 4 * j)
           by (apply U_atom; [rewrite (EEo2 25%nat 25%bv eq_refl), Q25, P25; exact R25 | lia]).
         assert (VA26 : U E2 (SOff 26 0) = 2 ^ 64 - 1 - x_tok c)
           by (apply U_atom; [rewrite (EEo2 26%nat 26%bv eq_refl), Q26, P26; exact R26 | lia]).
         assert (VA27 : U E2 (SOff 27 0) = 16 + 8 * j)
           by (apply U_atom; [rewrite (EEo2 27%nat 27%bv eq_refl), Q27, P27; exact R27 | lia]).
         assert (VA20 : U E2 (SOff 20 0) = 2 ^ 64 - 1 - (cw_F c + 32))
           by (apply U_atom; [rewrite (EEo2 20%nat 20%bv eq_refl), Q20, P20; exact R20 | lia]).
         assert (VA32 : U E2 (SOff 32 0) = x_ntok c) by (apply U_atom; [exact Y32 | lia]).
         assert (VAW : U E2 cw3_a0w = x_ntok c + 64 - j).
         { unfold cw3_a0w. rewrite (cw3_u_addw E2 _ _ (x_ntok c) (64 - j) VA32); [lia | | lia | lia | lia].
           rewrite (cw3_u_addiw E2 _ (65 - j) VA19) by lia. lia. }
         unfold cw3_a0w in VAW.
         (* +0x2a4: number accepted, so the branch to KR2 is not taken; run to the exit test *)
         paj_run_tok RUN HS2 HJ2 SHOK2 cw3_Bspan.
         { apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
         cw3_name HS2 msE. cw3_ro QE.
         cw3_mdv mdk.
         assert (HEQa : forall x, ms_mem msE x = mem2 x) by (intros x; exact (QE x)).
         psrr_branch_tok RUN BR HS2 SHOK2 cw3_Bspan.
         ++ (* bne taken: KL at pass j + 1 *)
            rename Hc into Hbr.
            paj_run_to_tok RUNTO HS2 HJ2 SHOK2 cw3_Bspan CW_KL.
            { apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
            cw3_name HS2 msF. cw3_ro QF.
            pmkst HS2. cw3_mdv mdk2.
            assert (HEQ2 : forall x, ms_mem msF x = mem2 x) by (intros x; rewrite (QF x); exact (HEQa x)).
            prreg HS2 (2%bv : bv 5) T2. prreg HS2 (3%bv : bv 5) T3. prreg HS2 (4%bv : bv 5) T4.
            prreg HS2 (8%bv : bv 5) T8. prreg HS2 (9%bv : bv 5) T9. prreg HS2 (18%bv : bv 5) T18.
            prreg HS2 (24%bv : bv 5) T24.
            rewrite (EEo2 2%nat 2%bv eq_refl) in T2. rewrite (EEo2 3%nat 3%bv eq_refl) in T3.
            rewrite (EEo2 4%nat 4%bv eq_refl) in T4. rewrite (EEo2 8%nat 8%bv eq_refl) in T8.
            rewrite (EEo2 9%nat 9%bv eq_refl) in T9. rewrite (EEo2 18%nat 18%bv eq_refl) in T18.
            rewrite (EEo2 24%nat 24%bv eq_refl) in T24.
            pose proof (cw3_fi_ext c 0 ly3 (set_fs f S3) W2 regs2 mem2 md2 _ _ mdk2 HFI2 HJ2 HEQ2 T2 T3 T4 T8 T9 T18 T24)
              as HFIk.
            pose proof (cw3_un_ext c ly3 (set_fs f S3) W2 mem2 _ HEQ2 HUN2) as HUNk.
            assert (HSPLk : cw_spills c W2 (ms_mem msF)).
            { destruct HSPL2 as [Sp1 Sp2]. split.
              - rewrite <- Sp1. apply rdword_ext. intros i Hi. exact (cw3_aview_ext (w_H W2) mem2 _ HEQ2 _).
              - rewrite <- Sp2. apply rdword_ext. intros i Hi. exact (cw3_aview_ext (w_H W2) mem2 _ HEQ2 _). }
            cw3_rr HS2 (19%bv : bv 5) N19. cw3_rr HS2 (20%bv : bv 5) N20. cw3_rr HS2 (21%bv : bv 5) N21.
            cw3_rr HS2 (22%bv : bv 5) N22. cw3_rr HS2 (23%bv : bv 5) N23. cw3_rr HS2 (25%bv : bv 5) N25.
            cw3_rr HS2 (26%bv : bv 5) N26. cw3_rr HS2 (27%bv : bv 5) N27.
            rewrite branch_ne_U, VAW, VA23 in Hbr. apply negb_true_iff, Z.eqb_neq in Hbr.
            unfold from_KL, cw_from in HKL1.
            apply (HKL1 ly3 (set_fs f S3) W2 (ms_regs msF) (ms_mem msF) mdk2). unfold INV_KL.
            split; [exact (conj HFIk HUNk)|]. split; [exact HSPLk|]. split; [lia|].
            split; [rewrite N19; unfold w64; f_equal;
              rewrite (cw3_u_addiw E2 _ (65 - j) VA19) by lia; lia|].
            split; [rewrite N20; unfold w64; f_equal; rewrite VA20; lia|].
            split; [rewrite N21; unfold w64; f_equal; rewrite VA21; lia|].
            split; [rewrite N22; unfold w64; f_equal; rewrite VA22; lia|].
            split; [rewrite N23; unfold w64; f_equal; rewrite VA23; lia|].
            split; [rewrite N25; unfold w64; f_equal; rewrite U_SOff, (EEo2 25%nat 25%bv eq_refl), Q25, P25, R25;
              unfold w64; rewrite unsigned_lit_small by lia; rewrite zcanon_small by lia; lia|].
            split; [rewrite N26; unfold w64; f_equal; rewrite VA26; lia|].
            split; [rewrite N27; unfold w64; f_equal; rewrite U_SOff, (EEo2 27%nat 27%bv eq_refl), Q27, P27, R27;
              unfold w64; rewrite unsigned_lit_small by lia; rewrite zcanon_small by lia; lia|].
            exists id, (vs ++ [v]). split; [exact Hid|].
            split; [replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia; exact Hvs1|].
            split; [exact (Hidm3 _ HEQ2) | exact (Hvsm3 _ HEQ2)].
         ++ (* bne not taken: KD, every member parsed *)
            rename Hc into Hbr.
            paj_run_to_tok RUNTO HS2 HJ2 SHOK2 cw3_Bspan CW_KD.
            { apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
            cw3_name HS2 msF. cw3_ro QF.
            pmkst HS2. cw3_mdv mdk2.
            assert (HEQ2 : forall x, ms_mem msF x = mem2 x) by (intros x; rewrite (QF x); exact (HEQa x)).
            prreg HS2 (2%bv : bv 5) T2. prreg HS2 (3%bv : bv 5) T3. prreg HS2 (4%bv : bv 5) T4.
            prreg HS2 (8%bv : bv 5) T8. prreg HS2 (9%bv : bv 5) T9. prreg HS2 (18%bv : bv 5) T18.
            prreg HS2 (24%bv : bv 5) T24.
            rewrite (EEo2 2%nat 2%bv eq_refl) in T2. rewrite (EEo2 3%nat 3%bv eq_refl) in T3.
            rewrite (EEo2 4%nat 4%bv eq_refl) in T4. rewrite (EEo2 8%nat 8%bv eq_refl) in T8.
            rewrite (EEo2 9%nat 9%bv eq_refl) in T9. rewrite (EEo2 18%nat 18%bv eq_refl) in T18.
            rewrite (EEo2 24%nat 24%bv eq_refl) in T24.
            pose proof (cw3_fi_ext c 0 ly3 (set_fs f S3) W2 regs2 mem2 md2 _ _ mdk2 HFI2 HJ2 HEQ2 T2 T3 T4 T8 T9 T18 T24)
              as HFIk.
            pose proof (cw3_un_ext c ly3 (set_fs f S3) W2 mem2 _ HEQ2 HUN2) as HUNk.
            assert (HSPLk : cw_spills c W2 (ms_mem msF)).
            { destruct HSPL2 as [Sp1 Sp2]. split.
              - rewrite <- Sp1. apply rdword_ext. intros i Hi. exact (cw3_aview_ext (w_H W2) mem2 _ HEQ2 _).
              - rewrite <- Sp2. apply rdword_ext. intros i Hi. exact (cw3_aview_ext (w_H W2) mem2 _ HEQ2 _). }
            cw3_rr HS2 (22%bv : bv 5) N22.
            rewrite branch_ne_U, VAW, VA23 in Hbr. apply negb_false_iff, Z.eqb_eq in Hbr.
            assert (Hvs2 : Verbs.numbers_m (skipn 2 (x_tks c)) = Some (vs ++ [v])).
            { assert (Eall : firstn (S (Z.to_nat j)) (skipn 2 (x_tks c)) = skipn 2 (x_tks c))
                by (apply firstn_all2; rewrite length_skipn; lia).
              rewrite <- Eall. exact Hvs1. }
            unfold from_KD, cw_from in HKD.
            apply (HKD ly3 (set_fs f S3) W2 (ms_regs msF) (ms_mem msF) mdk2). unfold INV_KD.
            split; [exact (conj HFIk HUNk)|]. split; [exact HSPLk|].
            split; [rewrite N22; unfold w64; f_equal; rewrite VA22; lia|].
            split; [lia|].
            exists id, (vs ++ [v]). split; [exact Hid|]. split; [exact Hvs2|].
            split; [exact (Hidm3 _ HEQ2) | exact (Hvsm3 _ HEQ2)].
      -- (* number refused tok[2 + j]: beqz a0 to KR2 *)
         destruct HNUM as (HA0 & _).
         destruct (cw3_seedR W2 mem2 regs2 0 (cw_s1 c) (x_ntok c) HA0 G9' ltac:(lia) ltac:(lia)
           ltac:(clear - Hs1m; Z.div_mod_to_equations; lia) GNT2 ltac:(lia)) as [HS2 SHOK2].
         assert (HEIR : img_env VAL A_LIM (cw3_ER regs2 (x_ntok c))) by (unfold cw3_ER; apply Eimg_env).
         set (E2 := cw3_ER regs2 (x_ntok c)) in *.
         assert (EEo2 : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E2 m = getr regs2 rr).
         { intros m rr Hm. subst E2. unfold cw3_ER. rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 rr) as Hr5;
             change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
         paj_run_to_tok RUNTO HS2 HJ2 SHOK2 cw3_Bspan CW_KR2.
         { apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
         cw3_name HS2 msE. cw3_ro QE.
         pmkst HS2. cw3_mdv mdk.
         assert (HEQ2 : forall x, ms_mem msE x = mem2 x) by (intros x; exact (QE x)).
         prreg HS2 (2%bv : bv 5) T2. prreg HS2 (3%bv : bv 5) T3. prreg HS2 (4%bv : bv 5) T4.
         prreg HS2 (8%bv : bv 5) T8. prreg HS2 (9%bv : bv 5) T9. prreg HS2 (18%bv : bv 5) T18.
         prreg HS2 (24%bv : bv 5) T24.
         rewrite (EEo2 2%nat 2%bv eq_refl) in T2. rewrite (EEo2 3%nat 3%bv eq_refl) in T3.
         rewrite (EEo2 4%nat 4%bv eq_refl) in T4. rewrite (EEo2 8%nat 8%bv eq_refl) in T8.
         rewrite (EEo2 9%nat 9%bv eq_refl) in T9. rewrite (EEo2 18%nat 18%bv eq_refl) in T18.
         rewrite (EEo2 24%nat 24%bv eq_refl) in T24.
         pose proof (cw3_fi_ext c 0 ly3 (set_fs f S3) W2 regs2 mem2 md2 _ _ mdk HFI2 HJ2 HEQ2 T2 T3 T4 T8 T9 T18 T24)
           as HFIk.
         pose proof (cw3_un_ext c ly3 (set_fs f S3) W2 mem2 _ HEQ2 HUN2) as HUNk.
         assert (HSPLk : cw_spills c W2 (ms_mem msE)).
         { destruct HSPL2 as [Sp1 Sp2]. split.
           - rewrite <- Sp1. apply rdword_ext. intros i Hi. exact (cw3_aview_ext (w_H W2) mem2 _ HEQ2 _).
           - rewrite <- Sp2. apply rdword_ext. intros i Hi. exact (cw3_aview_ext (w_H W2) mem2 _ HEQ2 _). }
         pose proof (cw3_chain_none (x_R c) (x_tks c) (Z.to_nat j) wd ltac:(lia) Hwdn Hnum) as HCR.
         unfold from_KR2, cw_from in HKR.
         apply (HKR ly3 (set_fs f S3) W2 (ms_regs msE) (ms_mem msE) mdk). unfold INV_KR2.
         exact (conj (conj HFIk HUNk) (conj HSPLk HCR)).
Qed.

End e.
End f.
End d.
