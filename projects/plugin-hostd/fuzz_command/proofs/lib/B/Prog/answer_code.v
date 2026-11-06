(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of answer_code on plugin-hostd/fuzz_command's ASan+UBSan build
   (fuzz_command.asan-ubsan): tanswer_code_spec of lib/B/Prog/answer_code_c.v (a Theorem Labs lane f490061c104, statement passes 4,
   4b and 5), re-walked from the ASan walk lib/A/Prog/answer_code.v (a working branch 2ba4488ce71) at B's
   addresses, in the same shape (entry state, side-stack frame by __asan_stack_malloc_1, the snprintf wrapper,
   hand_back, the free wrapper, the release by the flag store, return). The snprintf wrapper is the shared contract
   (RtPFCmd.asnprintf_sh) and returns at some FP state fx1: the walk is proved for any entry FP state
   (tanswer_code_holds_any) and runs the code after that call at fx1 (PaFx.st_ok_pi_restrict_xfx, ac_postF), as a Theorem Labs lane's
   PASS4-REFIT.md section A.5 (in place). The frame chains at the calls come from afn_pre's chain (achain_push at the
   frame pointer, achain_chain_pre for the free wrapper's chain_pre).
   B code (capstone over the pin's .symtab, sha256 658cefbe...): answer_code at 0x8c9f8 = BASE + AF_answer_code
   (0x86530 + 0x64c8), 496 bytes, 124 instructions, the same instruction stream as A's 0x8cac4 up to PC-relative
   immediates. Calls: __asan_stack_malloc_1 0x3fac8 (at 0x8ca50, return BASE + 25892), the snprintf trampoline
   0x451d0 (at 0x8cb04, return BASE + 26072), hand_back 0x8a978 (at 0x8cb0c, return BASE + 26080), the free trampoline
   0x589cc (at 0x8cb10, return BASE + 26084). No __asan_report_* call and no UBSan trap (unimp / ebreak) in the
   function, so no report edge. Branches: 0x8ca48 (use-after-return flag 0: not taken, the flag cell 0xb0c40 is the
   record's const cell 1, read through AR's const law at the entry, ac_entry's uar_cell_regionP chunk), 0x8ca64
   (side-stack frame null: taken to 0x8ca84, the frame is non-null by aj_stack_malloc_atS), 0x8ca7c (the page probe of
   the real-stack fallback 0x8ca68-0x8ca80: not reached), 0x8cb34 (real-stack epilogue: not taken, the release is the
   flag store 0x8cb7c-0x8cb80). GOT words: the use-after-return flag 0xa5fa8 (A_OBJ 1) and the shadow base 0xa5f50
   (A_OBJ 0), the shadow-base cell 0xb0c38 (A_OBJ 12), the format "resp %d" 0x21d40 (A_OBJ 47): the same object
   indices as A. The format literal's shadow (zsh_lit_21d40, ac_lit_hull) is proved from AR and the allocator record,
   where the A walk carried ZSH_lit_21d00 / HULL_lit_21d00 as hypotheses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05 YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFSx RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import hand_back_c answer_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require PaFx CmdSnText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a byte the reader shows is in [0, 256) *)
Lemma ac_aview_rng : forall (sg : list Segment) H mem a v, aview sg H mem a = Some v -> 0 <= v < 256.
Proof.
intros sg H mem a v Hv. unfold aview in Hv. destruct (mbyte sg (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.
(* the read-only ranges the snprintf chain names (RtPFCmd.CMD_SNP_CR, since a Theorem Labs lane 0934cb146c3 the image's two
   non-writable load segments, [0x10000, 0x33000) and [0x33000, 0xa5000)) lie in the image hull (decided on the closed
   list) *)
Lemma ac_snp_rng : forall r, In r RtPFCmd.CMD_SNP_CR -> 0x10000 <= fst r /\ fst r + snd r <= 0xa5000 /\ 0 <= snd r.
Proof.
intros r Hr.
assert (H : forallb (fun r : Z * Z => (0x10000 <=? fst r) && (fst r + snd r <=? 0xa5000) && (0 <=? snd r)) RtPFCmd.CMD_SNP_CR = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2, H3. lia.
Qed.
(* a low object (in the image hull) is apart from the snprintf chain's outputs: the scratch window below sp and the
   destination, which lies off the image hull *)
Lemma ac_lo_disj : forall a n K sp d w, 0 <= n -> 0x10000 <= a -> a + n <= 0x606000 -> a + n <= sp - K -> 0 <= K ->
(d + w <= 0x10000 \/ 0x606000 <= d) -> Forall (zdisjoint (a, n)) (snp_out K sp d w).
Proof.
intros a n K sp d w Hn Ha Han Hsp HK Hd. unfold snp_out.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd]; lia.
Qed.
(* the format "resp %d" as the shared contract reads it: the bytes of CmdRo's literal 0x21d40 *)
Lemma ac_fmt_bytes : forall rd, abytes_atR rd 0x21d40 RO_lit_21d40 ->
forall i, 0 <= i <= 7 -> rd (0x21d40 + i) = Some (nth (Z.to_nat i) (RecAns.RESP_FMT ++ [0]) 0).
Proof.
intros rd H i Hi.
assert (E : exists k, (k < 8)%nat /\ i = Z.of_nat k) by (exists (Z.to_nat i); split; lia).
destruct E as (k & Hk & ->). rewrite Nat2Z.id. rewrite (H k ltac:(unfold RO_lit_21d40; cbn [length map]; lia)).
do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

(* a register's symbolic value in a symbolic state, without normalising the denotation (CmdPaLib's prreg
   normalises it) *)
Ltac preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

Ltac norm_ssp HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
end.

(* an address outside every write window of a symbolic memory *)
Ltac nwin_tac rwt :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rwt Hr | ]);
destruct Hin.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---------- arithmetic and denotation facts ---------- *)

Lemma denot_and32 : forall E n v, ew E n = Z_to_bv 64 v -> 96 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n (-96)) (SLit (-32))) = Z_to_bv 64 (32 * ((v - 96) / 32)).
Proof.
intros E n v Hn Hv.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_AND (SOff n (-96)) (SLit (-32))))). f_equal.
change (U E (SAlu ALU_AND (SOff n (-96)) (SLit (-32))) = 32 * ((v - 96) / 32)).
rewrite U_SAlu, U_SOff, U_SLit, Hn. cbn [zalu_raw]. rewrite unsigned_lit_small by lia.
unfold zcanon, M64. rewrite (Z.mod_small (v + -96)) by lia.
replace (-32 mod 2 ^ 64) with (2 ^ 64 - 32) by reflexivity.
rewrite CmdSnText.snt_land_m32 by lia. replace (v + -96) with (v - 96) by lia.
pose proof (Z.div_pos (v - 96) 32 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le (v - 96) 32 ltac:(lia)).
apply Z.mod_small. lia.
Qed.

Lemma denot_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD e (SLit 0)))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E e)). f_equal.
change (U E (SAlu ALU_ADD e (SLit 0)) = U E e). rewrite U_SAlu, U_SLit. cbn [zalu_raw].
unfold zcanon, M64. rewrite (Z.mod_0_l (2 ^ 64)) by lia. rewrite Z.add_0_r.
apply Z.mod_small. pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as H. unfold U. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma sp1_facts : forall sp, sp mod 16 = 0 -> 2 ^ 46 <= sp ->
sp - 112 <= 32 * ((sp - 96) / 32) <= sp - 96 /\ (32 * ((sp - 96) / 32)) mod 32 = 0 /\
(32 * ((sp - 96) / 32) - sp) mod 16 = 0.
Proof.
intros sp H16 Hlo.
pose proof (Z.div_mod (sp - 96) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (sp - 96) 32 ltac:(lia)) as M.
assert (Hm : (sp - 96) mod 32 = 0 \/ (sp - 96) mod 32 = 16).
{ pose proof (Z.div_mod sp 16 ltac:(lia)) as D2. rewrite H16 in D2. lia. }
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
destruct Hm as [Hm|Hm].
- replace (32 * ((sp - 96) / 32) - sp) with (-96) by lia. reflexivity.
- replace (32 * ((sp - 96) / 32) - sp) with (-112) by lia. reflexivity.
Qed.

Lemma not_in_ranges : forall (L : list (Z * Z)) lo hi,
forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) L = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) L.
Proof.
intros L lo hi HL a Ha HE. apply Exists_exists in HE as (r & Hr & Hin).
pose proof (proj1 (forallb_forall _ _) HL r Hr) as Hb. cbn beta in Hb.
apply Bool.orb_true_iff in Hb. unfold in_zr in Hin.
destruct Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

Lemma in_filter_old : forall (old : Z) (O : list (Z * Z)) x, In x (filter (fun pn : Z * Z => fst pn =? old) O) -> In x O.
Proof.
intros old O x. induction O as [|y O IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) in H; [destruct H as [<- | H]; [left; reflexivity | right; apply IH; exact H] | right; apply IH; exact H].
Qed.
Lemma in_filter_old_intro : forall (old : Z) (O : list (Z * Z)) x, In x O -> fst x = old ->
In x (filter (fun pn : Z * Z => fst pn =? old) O).
Proof.
intros old O x. induction O as [|y O IH]; intros H Hx; [destruct H|].
cbn. destruct (decide _) as [Hd | Hd].
- destruct H as [<- | H]; [left; reflexivity | right; apply IH; [exact H | exact Hx]].
- destruct H as [<- | H]; [exfalso; apply Hd; rewrite Hx, Z.eqb_refl; first [exact I | reflexivity] | apply IH; [exact H | exact Hx]].
Qed.
Lemma aval_mem8_eq : forall rd a v1 v2, aval_mem rd a 8 v1 -> aval_mem rd a 8 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
intros rd a v1 v2 H1 H2 B1 B2.
assert (E : forall k, (k < 8)%nat -> YG0f.le_byte v1 8 k = YG0f.le_byte v2 8 k).
{ intros k Hk. pose proof (H1 k Hk) as X1. rewrite (H2 k Hk) in X1. injection X1 as X. symmetry. exact X. }
rewrite <- (le_bytes8 v1 B1), <- (le_bytes8 v2 B2).
rewrite (E 0%nat), (E 1%nat), (E 2%nat), (E 3%nat), (E 4%nat), (E 5%nat), (E 6%nat), (E 7%nat) by lia. reflexivity.
Qed.
Lemma Z_mod_16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. pose proof (Z.div_mod x 16 ltac:(lia)). rewrite H in H0. rewrite H0. replace (16 * (x / 16) + 0) with ((2 * (x / 16)) * 8) by lia. apply Z_mod_mult. Qed.
Lemma ro_lit_21d40 : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21d40 RO_lit_21d40.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. decompose [and] H. assumption. Qed.
Lemma resp_fmt_no0 : ~ In (Z_to_bv 8 0) (PF.pf_bytes RecAns.RESP_FMT).
Proof.
intros H. unfold PF.pf_bytes in H. apply in_map_iff in H as (z & Hz & Hin). apply (f_equal bv_unsigned) in Hz.
rewrite !Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz. cbn in Hin.
repeat (destruct Hin as [<- | Hin]; [vm_compute in Hz; discriminate | ]); destruct Hin.
Qed.
(* B's program statics against CmdBSyms' runtime-owned statics, and the format literal against its zero-shadow ranges
   (lib/B/YF0m.v): g_rec [0x5e32c0, +960) and record.spill [0x5e3760, +56) meet no owned static (the A walk's
   not_in_ranges checks at A's 0x5e3740 / 0x5e3be0), and "resp %d"'s 8 bytes at 0x21d40 are one zero-shadow range *)
Lemma grec_not_owned : forall a, A_G_REC <= a < A_G_REC + 960 -> ~ Exists (in_zr a) YF0m.Tfib_owned_static.
Proof. intros a Ha. unfold A_G_REC in Ha. apply (not_in_ranges _ 0x5e32c0 0x5e3680); [vm_compute; reflexivity | lia]. Qed.
Lemma spill_not_owned : forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> ~ Exists (in_zr a) YF0m.Tfib_owned_static.
Proof. intros a Ha. unfold A_REC_SPILL in Ha. apply (not_in_ranges _ 0x5e3760 0x5e3798); [vm_compute; reflexivity | lia]. Qed.
Lemma zsh_21d40_in : In (0x21d40, 8) YF0m.Tfib_zero_shadow.
Proof.
assert (H : existsb (fun r => (fst r =? 0x21d40) && (snd r =? 8)) YF0m.Tfib_zero_shadow = true) by (vm_compute; reflexivity).
apply existsb_exists in H as ([p n] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hp Hn]. apply Z.eqb_eq in Hp, Hn. subst p n. exact Hin.
Qed.

(* membership in the record's constant shadow, decided by computation on a closed goal (the form of
   a working branch 93eeb37e147 sup_reset_aux.v srb_cell_in) *)
Definition ac_cell_is (a v : Z) (c : acell) : bool :=
  match c with
  | ACell (ANum a') (S O) (AV (ANum v')) => (a' =? a) && (v' =? v)
  | _ => false
  end.
Lemma ac_cell_in : forall a v l, existsb (ac_cell_is a v) l = true -> In (z1 (ANum a) v) l.
Proof.
intros a v l. induction l as [|c l IH]; cbn [existsb In]; [discriminate|].
intros H. apply orb_true_iff in H as [H|H]; [left | right; exact (IH H)].
destruct c as [ca cw cv]. unfold ac_cell_is in H.
destruct ca; try discriminate H. destruct cw as [|[|cw]]; try discriminate H.
destruct cv as [e|m w]; try discriminate H. destruct e; try discriminate H.
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1, H2. subst. reflexivity.
Qed.
(* the value of the constant shadow byte at s in the format literal's hull 0x7fffc3a9 .. 0x7fffc3af
   (lib/B/YF0m.v:2608-2614: the redzone f9 after "resp %d", the granule 0x21d60 of "resp " at 6, its redzone) *)
Definition ac_hull_v (s : Z) : Z := if s =? 0x7fffc3ac then 6 else 0xf9.
Lemma ac_hull_cs : forall s, 0x7fffc3a9 <= s < 0x7fffc3b0 ->
In (z1 (ANum s) (ac_hull_v s)) YF0m.Tfib_const_shadow.
Proof.
intros s Hs.
assert (H7 : s = 0x7fffc3a9 \/ s = 0x7fffc3aa \/ s = 0x7fffc3ab \/ s = 0x7fffc3ac \/ s = 0x7fffc3ad \/
  s = 0x7fffc3ae \/ s = 0x7fffc3af) by lia.
destruct H7 as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; apply ac_cell_in; vm_compute; reflexivity.
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma region_kept_hi : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma region_kept_hi2 : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma aview_frame_pt : forall E rs H (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a HF Ha Hn. apply (aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.


Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (lib/B/Prog/answer_code_c.v, a Theorem Labs lane 713692f1e0c), with its names and its
   forall fx0 forms *)
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTACK1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : @cmd_val_objs rc PI.
(* the walk's own hypotheses: HB, the allocator record (lib/B/YF0m.v, Record CmdBSyms); TLF, the stack-malloc pcs and
   use-after-return cells the kit pins per binary (lib/B/Prog/PaLibF.v PALibF; a Theorem Labs lane has no lemma for it); MTL / MTLF,
   the meter's laws (MTLF: cgif's MLAWF, lib/Reusable/YC5d.v:50-53) *)
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis TLF : @PALibF rc cmd_listing PI B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
(* the facts a Theorem Labs lane proves only at its pinned instance (a working branch 713692f1e0c, lib/B/Prog/CmdRec*.v), each
   under the lemma's name with the lemma's statement at this walk's abstract instance, so that the closing file
   discharges each by `exact <lemma>`: cmd_palib, cmd_sig_prog_PB, cmd_frame_flag_law (CmdRecRest.v),
   cmd_img_facts_tfib (CmdRecImg.v). Every other record fact the walk uses (ROB, RELRO_IMG, cmd_ro_prog_apart,
   cmd_prog_img, cmd_ro_ok_of_aro, cmd_rec_cells, cmd_consts_view_snp) is a Theorem Labs lane's lemma over any segments, used by `exact`
   from LAWS, HB and the image facts IMG. *)
Hypothesis cmd_palib : forall B0 : asyms, YF0m.CmdBSyms B0 -> @PALib rc cmd_listing PI B0.
Hypothesis cmd_sig_prog_PB : @cmd_sig_prog rc PI.
Hypothesis cmd_img_facts_tfib : forall B0 : asyms, YF0m.CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis cmd_frame_flag_law : forall B0 : asyms, frame_flag_lawP SEGS B0.
Let TL : @PALib rc cmd_listing PI B := cmd_palib B HB.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.

(* ---------- the recorder's state survives writes outside g_rec, record.spill and its own blocks ---------- *)
Lemma aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma nodup_of_pairwise : forall (l : list (Z * Z)) (f : Z * Z -> Z * Z),
pairwise zdisjoint (map f l) -> (forall x, In x l -> 0 < snd (f x)) -> List.NoDup l.
Proof.
induction l as [|x t IH]; intros f Hp Hpos; [constructor|].
constructor.
- intros Hin. apply in_split in Hin as (t1 & t2 & Et).
assert (Hd : zdisjoint (f x) (f x)).
{ apply (pairwise_zdisjoint_split (map f (x :: t)) (f x) (f x) Hp).
exists [], (map f t1), (map f t2). left. rewrite Et. cbn. rewrite map_app. reflexivity. }
pose proof (Hpos x (or_introl eq_refl)). unfold zdisjoint in Hd. lia.
- apply (IH f); [| intros y Hy; apply Hpos; right; exact Hy].
change (map f (x :: t)) with ([f x] ++ map f t) in Hp. exact (proj2 (pairwise_app_l _ _ _ Hp)).
Qed.
Lemma rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. unfold lay_blocks in Hpn.
destruct HA as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
+ destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
* exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
* exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
+ exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
+ exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
+ exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R), (l_answer Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 Ha))).
- unfold areply_at in Hr. destruct (r_reply R), (l_reply Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hr))))).
Qed.
Lemma rec_repA_kept : forall ly S rd ly' S' rd' R O, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) Hbl Hg Hs Hb. exists Q. split; [|exact HO].
assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S')) by (intros pn Hpn; apply Hbl, HO, Hpn).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [p n] i Hpn Hi; apply (Hb p n i (proj2 (HO (p, n)) Hpn) Hi)).
unfold lay_blocks in HblQ, HbQ.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
unfold arep_at, ag1_calls, ag1_scalars, aanswer_at, areply_at in *.
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, CALL_SIZE in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk; apply Hg; lia]|].
split.
- intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
pose proof HC as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
+ intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact C5 | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
+ intros j Hj. apply Hs. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [|exact Hown].
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.

Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let ML : model_laws (as_universe B) := CmdRecRest.cmd_model_laws B HB.
Let SMP : stack_malloc_progressP B := CmdRecRest.cmd_stack_malloc_progress B.
(* the block the recorder's answer field points at is one of the recorder's blocks O (it is the only live block
   that starts at old: blocks are disjoint and old = 0 when there is no answer) *)
Lemma old_in_O : forall ly S (W : world SEGS) mem md R O old pn, AR SEGS B ly S W mem md -> rec_repA B ly S (rdW W mem) R O ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
In pn (ablocks B ly S) -> fst pn = old -> In pn O.
Proof.
intros ly S W mem md R O old [p n] HAR HREP HOLD Hold Hpn Hfst. cbn [fst] in Hfst. subst p.
pose proof HREP as (Q & HA & HO).
destruct HA as (_ & _ & _ & _ & Ha & _). unfold aanswer_at in Ha.
destruct (al_blocks _ _ LAWS _ _ _ _ _ old n HAR Hpn) as (_ & Hp4096 & Hpc & _ & _ & _ & Hn).
pose proof alloc_ceiling_lt as Hac.
destruct (r_answer R) as [x|], (l_answer Q) as [[q m]|] eqn:EQ; try contradiction.
- destruct Ha as (A1 & A2 & A3 & _). cbn [fst snd] in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR A3) as (_ & Hq4096 & Hqc & _ & _ & _ & Hm).
assert (Rq : 0 <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Eq : q = old) by (apply (aval_mem8_eq _ _ q old A1 HOLD); [lia | exact Hold]). subst q.
assert (HqO : In (old, m) O).
{ apply HO. unfold lay_blocks. rewrite EQ. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
destruct (Z.eq_dec n m) as [<- | Nnm]; [exact HqO|].
assert (Ne : (old, n) <> (old, m)) by (intros E; injection E; lia).
exfalso. pose proof (sep_blocks SEGS B LAWS ly S W mem md old n old m HAR Hpn A3 Ne) as Hd.
unfold zdisjoint, req_size in Hd. cbn [fst snd] in Hd. destruct (Z.eqb_spec n 0), (Z.eqb_spec m 0); lia.
- assert (E0 : old = 0) by (apply (aval_mem8_eq _ _ old 0 HOLD Ha); lia). lia.
Qed.
Lemma ablocks_nodup : forall ly S W mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
apply (nodup_of_pairwise _ (fun b0 : Z * Z => (fst b0, req_size (snd b0))) Hp).
intros [p n] Hin. cbn [fst snd]. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
unfold req_size. destruct (Z.eqb_spec n 0); lia.
Qed.
Let FFL : frame_flag_lawP SEGS B := cmd_frame_flag_law B.
(* the format literal's shadow is addressable: the A walk's provisional hypothesis ZSH_lit_21d00 is a lemma on B
   (CmdZsh's cmd_addressable_in over the zero-shadow range (0x21d40, 8)) *)
Lemma zsh_lit_21d40 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (rdW W mem) SHADOW_OFF 0x21d40 8.
Proof.
intros ly S W mem md HAR.
exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x21d40, 8) 0x21d40 8 HAR zsh_21d40_in eq_refl eq_refl
ltac:(cbn [fst snd]; lia) ltac:(cbn [fst snd]; lia)).
Qed.
(* a one-byte cell of the record's constant shadow holds under AR (AR's const-cell law am_const over CmdBSyms'
   ts_const) *)
Lemma ac_cshadow : forall ly S (W : world SEGS) mem md a v,
AR SEGS B ly S W mem md -> In (z1 (ANum a) v) YF0m.Tfib_const_shadow -> 0 <= v < 256 ->
rdW W mem a = Some v.
Proof.
intros ly S W mem md a v HAR Hin Hv. destruct HAR as (M & _).
pose proof (am_const _ _ _ _ M) as C. rewrite (YF0m.ts_const B HB ly) in C. rewrite Forall_forall in C.
specialize (C (z1 (ANum a) v) ltac:(unfold YF0m.Tfib_const; apply in_or_app; right; apply in_or_app; right; exact Hin)).
unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C.
specialize (C 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in C. rewrite Z.add_0_r in C. rewrite C. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. exact Hv.
Qed.
(* the format literal's shadow hull (0x7fffc3a8 .. 0x7fffc3af) is visible at every AR state: the granule's shadow
   byte from the zero-shadow range (0x21d40, 8), the other seven from the record's constant shadow. The A walk's
   provisional hypothesis HULL_lit_21d00 is a lemma here, from AR and HB alone. *)
Lemma ac_lit_hull : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (rdW W mem) 0x21d40 8.
Proof.
intros ly S W mem md HAR s Hs.
assert (E1 : shadow_addr 0x21d40 / 8 * 8 = 0x7fffc3a8) by (vm_compute; reflexivity).
assert (E2 : shadow_addr (0x21d40 + 8 - 1) / 8 * 8 + 8 = 0x7fffc3b0) by (vm_compute; reflexivity).
rewrite E1, E2 in Hs.
destruct (Z.eq_dec s 0x7fffc3a8) as [-> | Hne].
- pose proof (cmd_zshadow_rec SEGS B LAWS HB ly S W mem md (0x21d40, 8) HAR zsh_21d40_in 0
    ltac:(cbn [snd]; change (8 / 8) with 1; lia)) as Z0.
  change (rdW W mem 0x7fffc3a8 = Some 0) in Z0. rewrite Z0. discriminate.
- assert (Hv : 0 <= ac_hull_v s < 256) by (unfold ac_hull_v; destruct (s =? 0x7fffc3ac); lia).
  rewrite (ac_cshadow ly S W mem md s (ac_hull_v s) HAR (ac_hull_cs s ltac:(lia)) Hv). discriminate.
Qed.


(* the function's post after the FP state changed at the snprintf call: apost_base at the FP state fx1 the call
   returned, with the call's two FP clauses (f registers kept but f10, rounding mode 0), is apost_baseF at the entry's
   fx (fx' := fx1, right disjunct) *)
Lemma ac_postF : forall (fx fx1 : YK11.FPState) STK FP regs ly S W mem md k Q W' c',
@apost_base fx1 rc SK SEGS B STK FP regs ly S W mem md k Q W' c' ->
(forall k0 : bv 5, bv_unsigned k0 <> 10 -> Sem.reg_get (@fp_regs fx1) k0 = Sem.reg_get (@fp_regs fx) k0) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx1)) 5) 7 = 0 ->
@apost_baseF fx rc SK SEGS B STK FP regs ly S W mem md k Q W' c'.
Proof.
intros fx fx1 STK FP regs ly S W mem md k Q W' c' (ly' & S' & regs' & mem' & md' & Ec & HJ & HP & HQ) Hf Hc.
exists fx1, ly', S', regs', mem', md'. split; [exact Ec|]. split; [exact Hf|]. split; [right; exact Hc|].
split; [exact HJ|]. split; [exact HP | exact HQ].
Qed.

Definition fr_hdr : YP09.region := YP09.mkRegion (Some 1028%nat) 0 32 0 24 [].
Definition fr_flg : YP09.region := YP09.mkRegion (Some 1028%nat) 120 128 120 120 [YP09.mkChunk 120 (CVal 8 (SOff 1040 0))].
Definition fr_shd : YP09.region := YP09.mkRegion (Some 1041%nat) 0 16 0 16 [].
Definition shx_F : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0).
Definition ac_extra (sp1 : Z) : list word := map (Z_to_bv 64) [SB; as_uar_cell B; sp1].
Definition ac_regions0 : smem := [
 YP09.mkRegion (Some 2%nat) (-96) (-88) (-96) (-88) [];
 YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 [];
 YP09.mkRegion (Some 34%nat) 24 32 24 32 [];
 got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition ac_facts0 : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (34%nat, mkAF (2^46) (2^47) 5)] [] [].
Definition ss_ac0 : sstate := mkSS AF_answer_code sr_atoms ac_regions0 None ac_facts0.


Lemma ac_entry : forall (fx0 : YK11.FPState) STK W ly S regs mem md ch, 112 <= STK ->
afn_pre SEGS B STK ly S W regs mem md ch ->
@st_ok_pi SEGS VAL fx0 (Eimg (Ereg regs (ac_extra (32 * ((spZ regs - 96) / 32))))) ss_ac0
(restrict (w_H W) (@mkst fx0 regs (Z_to_bv 64 (BASE + AF_answer_code)) mem (seg_rom SEGS))).
Proof.
intros fx0 STK W ly S regs mem md ch HSTK HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 1 ltac:(lia)) as HO1. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
rewrite restrict_mkst_fx.
set (sp1 := 32 * ((spZ regs - 96) / 32)).
destruct (sp1_facts (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
set (E := Eimg (Ereg regs (ac_extra sp1))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (U34 : base_val E (Some 34%nat) = sp1) by (apply VB; [exact E34 | lia]).
assert (U0 : base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply VB; [exact E241 | lia]).
assert (U1 : base_val E (Some (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply VB; [exact E242 | lia]).
assert (U12 : base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply VB; [exact E253 | lia]).
assert (U33 : base_val E (Some 33%nat) = as_uar_cell B) by (apply VB; [exact E33 | lia]).
assert (U2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
unfold ss_ac0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ac_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U34. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[rewrite denot_off0; exact E253 | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
[rewrite denot_off0; exact E32 | unfold SB; lia | lia |].
rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite U1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
[rewrite denot_off0; exact E33 | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents. unfold ac_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, U34, U0, U1, U12, U33.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [ac_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
rewrite Hal16, Hsp1a. unfold SB. repeat split; lia.
Qed.

(* the write windows of the six regions the walk carries from the frame setup on (the frame's shadow, its flag
   word, its header, two pieces of the own stack frame, the realigned stack word) *)
Ltac awr6 fpos sp1 regs FS Vs Vf V2 V34 EFA :=
eapply (YCbq.awr_ok_cons_gen _ _) with (k := 1041%nat); [reflexivity | exact Vs |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA, <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia |];
apply (awr_ok_cons_ro _ _); [cbn; lia|];
eapply (YCbq.awr_ok_cons_gen _ _) with (k := 1028%nat); [reflexivity | exact Vf |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
left; unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 1) with 128; lia |];
eapply (awr_ok_cons_stack_off _ _) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |];
eapply (awr_ok_cons_stack_off _ _) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |];
eapply (awr_ok_cons_stack_off _ _) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite V34; lia | cbn; rewrite FS; lia | cbn; lia |];
apply (awr_ok_nil _ _).

(* the walk at any entry FP state fx: the snprintf call returns at some fx1, and the code after it (hand_back, the
   free wrapper, the release, the return) runs at fx1 *)
Theorem tanswer_code_holds_any : forall fx : YK11.FPState, @tanswer_code_spec fx rc SK PI B MT.
Proof using THAND_BACK AFREE4 ASTACK1 AFREE_LAW ASNPRINTF VOBJS HB TLF MTL MTLF cmd_palib cmd_sig_prog_PB
cmd_img_facts_tfib cmd_frame_flag_law.
intros fx. unfold tanswer_code_spec.
intros ly S W regs mem md ch code old R O HPRE HFRM HROD HRO H10 Hcode HREP HOLD Hold64 Hfr Hev Hlive MOK.
pose (RUNP := @SRr_run_pi_AJ fx rc SK cmd_listing PL_cmd PI B LAWS).
pose (RUNC := @SRr_run_pi_AJ_call fx rc SK cmd_listing PL_cmd PI B LAWS).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
assert (FS0 : ANSWER_CODE_STK = 16560) by (vm_compute; reflexivity).
pose proof (ac_entry fx ANSWER_CODE_STK W ly S regs mem md ch ltac:(rewrite FS0; lia) HPRE) as HS. clear FS0.
set (FP := (A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O)).
pose proof (ajournal_init SEGS B ANSWER_CODE_STK FP ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : ANSWER_CODE_STK = 16560) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
set (sp1 := 32 * ((spZ regs - 96) / 32)) in HS.
destruct (sp1_facts (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
remember (Eimg (Ereg regs (ac_extra sp1))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (ac_extra sp1)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
clear HE.
assert (Esp : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite Esp; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = sp1) by (rewrite E34; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_answer_code)) with (Z_to_bv 64 (BASE + AF_answer_code)).
(* run 1: the prologue, the use-after-return flag (1, pinned by the record) and the call of __asan_stack_malloc_1 *)
paj_run_shc RUNP RUNC HS HJ.
{ unfold ss_ac0, ac_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP. cbn [ss_mem].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite U34; lia | cbn; rewrite FS; lia | cbn; lia |].
repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pmkst HS.
preg HS (2%bv : bv 5) R2. preg HS (9%bv : bv 5) R9. preg HS (1%bv : bv 5) R1. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
rewrite (denot_and32 E 2 (spZ regs) Esp ltac:(lia)) in R2. fold sp1 in R2.
rewrite denot_add0, (denot_and32 E 2 (spZ regs) Esp ltac:(lia)) in R9. fold sp1 in R9.
cbn [sv_denot] in R1. rewrite (img_env_codeptr E HEI 25892) in R1.
rewrite denot_off0, (EE 3%nat 3%bv eq_refl) in R3. rewrite denot_off0, (EE 4%nat 4%bv eq_refl) in R4.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS E ssx msx (2%bv : bv 5) (SOff 34 0) HS eq_refl ltac:(rewrite denot_off0, E34; cbn [ms_regs restrict]; rewrite R2; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS E ssx msx (9%bv : bv 5) (SOff 34 0) HS eq_refl ltac:(rewrite denot_off0, E34; cbn [ms_regs restrict]; rewrite R9; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
pose proof (palf_sm B TLF 1 ltac:(cbn; tauto)) as SM1. change (cs_stack_malloc 1) with CS___asan_stack_malloc_1 in SM1.
rewrite SM1.
assert (Qsp : spZ (ms_regs ms1) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 1 (ASTACK1 fx) ltac:(lia) W (ms_regs ms1) (ms_mem ms1)
ANSWER_CODE_STK (spZ regs) FP ly S W mem md [] ly S _ 0 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 25892)) HJ);
[ exact Qsp | exact Hsp1b | lia | rewrite FS, Hes; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp
| exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
| pose proof (count_cid_le_length 1 (frames S)); change (fs_frames 1) with 8192; lia ]. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJS & (fS2 & ES2)).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
pose proof HK as (HK1 & _ & HK3 & _ & _ & _).
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
- eapply region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
- eapply region_kept_hi; [exact U34 | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
clear R1 R2 R3 R4 R9 Qsp.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HAE1 : env_agree 32 (Ereg regs (ac_extra sp1)) E1) by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
assert (OLD1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
assert (E1028 : ew E1 1028 = Z_to_bv 64 F).
{ rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
unfold CLOB. cbn [map nth]. exact Ha0. }
clear HE1.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres). fold F in HFal, HFapp, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin) as HFoff. fold F in HFoff. unfold off_img in HFoff.
destruct (frame_al64 SEGS B _ _ _ _ _ 1 fpos HAR2 Hfin) as (HF64 & _ & _). fold F in HF64.
destruct (FFL _ _ _ _ _ 1 fpos HAR2 Hfin) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)). fold FL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLceil.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
replace (F + 128 - 8) with (F + 120) in Hflag by lia.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HFin : in_app F 128) by exact HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFin.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1040 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as E2 eqn:HE2 in HS.
assert (HAE2 : env_agree 32 (Ereg regs (ac_extra sp1)) E2) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | unfold A_LIM; lia]).
assert (OLD2 : forall n, (n < 1024)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2, ew_havoc_old by lia; apply OLD1; exact Hn).
assert (E1040 : ew E2 1040 = Z_to_bv 64 FL) by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E1041 : ew E2 1041 = Z_to_bv 64 (SB + F / 8)) by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E2028 : ew E2 1028 = Z_to_bv 64 F) by (rewrite HE2, ew_havoc_old by lia; exact E1028).
clear HE2.
assert (E2_32 : ew E2 32 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E32).
assert (V2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (V34 : bv_unsigned (ew E2 34) = sp1) by (rewrite OLD2 by lia; exact U34).
assert (V1028 : bv_unsigned (ew E2 1028) = F) by (rewrite E2028; apply unsigned_lit_small; lia).
assert (V1040 : bv_unsigned (ew E2 1040) = FL) by (rewrite E1040; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (HF8b : F / 8 <= 17592185978880) by (apply Z.div_le_upper_bound; lia).
assert (V1041 : bv_unsigned (ew E2 1041) = SB + F / 8) by (rewrite E1041; apply unsigned_lit_small; unfold SB; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 1028 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite V1028; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_alias Ev _ msv shx_F (SOff 1041 0) HS (shadow_decl_ok Ev 1028 32 1041 F SB E2028 ltac:(lia) E2_32 E1041)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv fr_hdr HS eq_refl
ltac:(unfold region_ok, fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1028; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv fr_flg HS eq_refl
ltac:(unfold region_ok, fr_flg; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1028; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ F 120 8 (SOff 1040 0) FL); [rewrite denot_off0; exact E1040 | lia | lia |];
exact (val_mem_of_rdword SEGS _ _ _ _ Hflag))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, fr_flg, fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv fr_shd HS eq_refl
ltac:(unfold region_ok, fr_shd; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1041; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS);
replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
apply (proj1 (HFSpres o ltac:(lia))))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, fr_shd, fr_flg, fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1041, V1028, V2, V34; unfold SB; pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia));
repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
paj_run_shc RUNP RUNC HS HJ2.
{ eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1041%nat); [reflexivity | exact V1041 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
right; unfold in_zr, shadow_addr; cbn [fst snd]; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia |].
apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1028%nat); [reflexivity | exact V1028 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
left; unfold in_zr; cbn [fst snd]; fold F; change (fs_frame_bytes 1) with 128; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite V34; lia | cbn; rewrite FS; lia | cbn; lia |].
apply (awr_ok_nil SEGS B). }
rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
(* where the recorder's state, the format literal and the live blocks lie: none of them in the frame, its shadow,
   its flag or the stack *)
set (KA := fun a : Z => (A_G_REC <= a < A_G_REC + 960) \/ (A_REC_SPILL <= a < A_REC_SPILL + 56) \/
(exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n)).
assert (KIMG : forall a, KA a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(in_img SEGS a /\ 0x10000 <= a < 0x606000 /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))).
{ intros a Ha. rewrite (YF0m.ts_owned B HB), (YF0m.ts_errno B HB). unfold YF0m.TFIB_ERRNO.
destruct Ha as [Ha | [Ha | Ha]]; [right | right | left; exact Ha].
- split; [apply (cmd_prog_img SEGS B LAWS HB IMG); left; unfold in_zr, REC_SIZE; cbn [fst snd]; exact Ha|]. unfold A_G_REC in Ha. split; [lia|].
split; [apply (not_in_ranges _ 0x5e32c0 0x5e3680); [vm_compute; reflexivity | lia] | lia].
- split; [apply (cmd_prog_img SEGS B LAWS HB IMG); right; left; unfold in_zr, SC_SIZE; cbn [fst snd]; exact Ha|]. unfold A_REC_SPILL in Ha. split; [lia|].
split; [apply (not_in_ranges _ 0x5e3760 0x5e3798); [vm_compute; reflexivity | lia] | lia]. }
assert (KLOC : forall a, KA a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16) /\ a <> FL).
{ intros a Ha. destruct (KIMG a Ha) as [(p & n & Hpn & Hpa) | (Hi & Hr & _ & _)].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn) as (_ & Hp4096 & Hpceil & Hpapp & _ & _).
assert (Hpn2 : In (p, n) (ablocks B ly S2)) by (rewrite Eab; exact Hpn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR2 Hpn2) as (_ & _ & _ & _ & Hpres2 & _).
pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 p n 1 fpos HAR2 Hpn2 Hfin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 1) with 128 in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
intros ->. exact (proj2 (Hpres2 FL ltac:(lia)) HFLo).
- split; [lia|]. split; [lia|]. split; [unfold SB; lia|]. intros ->. exact (HFLimg Hi). }
assert (K01 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & _). apply (aview_frame_pt E _ (w_H W) mem (ms_mem ms1) a HFr1); [lia|].
nwin_tac ltac:(fun H => rewrite ?Usp, ?U34 in H; lia). }
assert (K12 : forall a, KA a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms1) a).
{ pose proof HK as (_ & HK2 & _ & _ & _ & _).
intros a Ha. destruct (KIMG a Ha) as [(p & n & Hpn & Hpa) | (Hi & _ & Ho & He)].
- replace a with (p + (a - p)) by lia. apply (HK2 p n (a - p) Hpn); [lia | intros []].
- exact (HK3 a Hi Ho He). }
assert (K23 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _). apply (aview_frame_pt E2 _ (w_H W) mem2 (ms_mem ms3) a HFr3); [lia|].
nwin_tac ltac:(fun H => rewrite ?V2, ?V34, ?V1028, ?V1041 in H; lia). }
assert (K03 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite (K23 a Ha), (K12 a Ha), (K01 a Ha); reflexivity).
(* the call of the snprintf wrapper: snprintf(buf = F + 32, 32, "resp %d", code) *)
assert (HFPB : forall ly' S' a, inFP FP a -> Exists (in_zr a) YF0m.TFIB_PROG_STATIC \/
exists b n, In (b, n) (ablocks B ly S ++ ablocks B ly' S') /\ b <= a < b + req_size n).
{ intros ly' S' a (r & Hr & Ha). destruct Hr as [<- | Hr].
- left. apply Exists_exists. exists (A_G_REC, REC_SIZE). split; [left; reflexivity|].
unfold in_zr, OFF_ANSWER, REC_SIZE in *. cbn [fst snd] in *. lia.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn).
apply in_filter_old in Hpn.
exists p, n. split; [apply in_or_app; left; exact (rec_repA_in _ _ _ _ _ HREP (p, n) Hpn) | cbn [fst snd] in Ha; exact Ha]. }
assert (HFPRO : forall a, in_roP SEGS RLO RHI a -> ~ inFP FP a).
{ intros a Hro (r & Hr0 & Hra0). destruct (cmd_ro_prog_apart SEGS B LAWS HB IMG a Hro) as [Hi Hpg]. pose proof (pa_img_range a Hi) as Hrg.
destruct Hr0 as [<- | Hr0].
- apply Hpg. apply Exists_exists. exists (A_G_REC, REC_SIZE). split; [left; reflexivity|].
unfold in_zr, REC_SIZE, OFF_ANSWER in *. cbn [fst snd] in *. lia.
- unfold ablocks_fp in Hr0. apply in_map_iff in Hr0 as ([p n] & <- & Hpn). apply in_filter_old in Hpn.
pose proof (blk_off_imgP B ly S W mem md p n HAR (rec_repA_in _ _ _ _ _ HREP (p, n) Hpn)) as Hoff.
unfold off_img in Hoff. cbn [fst snd] in Hra0. lia. }
pmkst HS.
preg HS (10%bv : bv 5) R10. preg HS (11%bv : bv 5) R11. preg HS (12%bv : bv 5) R12. preg HS (13%bv : bv 5) R13.
preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
cbn [sv_denot] in R10, R11, R1. rewrite V1028 in R10. rewrite (img_env_codeptr E2 HEI2 26072) in R1.
assert (VSTR : VAL (A_OBJ 47) = 0x21d40) by (rewrite (VOBJS 47%nat) by (apply Nat.ltb_lt; vm_compute; reflexivity); vm_compute; reflexivity).
rewrite denot_off0, (img_env_atomP E2 288 HEI2 ltac:(unfold A_TEXT, A_LIM; lia)) in R12.
change (VAL 288) with (VAL (A_OBJ 47)) in R12. rewrite VSTR in R12.
rewrite denot_off0, OLD2 in R13 by lia. rewrite (EE 10%nat 10%bv eq_refl), H10 in R13.
rewrite denot_off0, OLD2, E34 in R2 by lia.
rewrite denot_off0, OLD2, (EE 3%nat 3%bv eq_refl) in R3 by lia. rewrite denot_off0, OLD2, (EE 4%nat 4%bv eq_refl) in R4 by lia.
pose proof (proj1 HJ2) as HAR3.
assert (Qsp3 : spZ (ms_regs ms3) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms3))).
{ exact (arodata_ok_journalP SEGS RLO RHI (RELRO_IMG SEGS B LAWS HB IMG) (RO := ROB SEGS B LAWS HB IMG) B _ _ FP ly S W mem md _ ly S2 W (ms_mem ms3) _ 0 HJ2 HFPRO HROD). }
pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly S2 W (ms_mem ms3) _ HAR3 HROD3) as HRO3.
pose proof (ro_lit_21d40 _ HRO3) as HLIT3.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin) as (_ & _ & HFpres3 & _). fold F in HFpres3. change (fs_frame_bytes 1) with 128 in HFpres3.
assert (ZS3 : forall j, 4 <= j < 8 -> rdW W (ms_mem ms3) (SB + F / 8 + j) = Some 0).
{ intros j Hj. pose proof (st_ok_region_nth E2 _ _ 0 _ HS eq_refl) as HR0.
cbn [ms_mem restrict mkst] in HR0.
assert (Hj4 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
destruct Hj4 as [-> | [-> | [-> | ->]]];
(apply (aview_of_val_mem1 SEGS); [|lia]);
(lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
refine (field_of_region E2 _ 1041 (SB + F / 8) _ 0 16 0 16 od 1%N (SLit 0) 0 HR0 V1041 _ _ _ _) end;
[cbn [In]; tauto | reflexivity | lia | lia]). }
(* the call of the snprintf wrapper (0x8cb04): snprintf(buf = F + 32, 32, "resp %d", code), at the entry's FP state,
   through the shared contract (asnprintf_realizes = RtPFCmd.asnprintf_sh: sh_asnprintf_realizes at FR_cmd, window
   CMD_SNP_K = 2 * ESTACK); the text is T, 6 .. 16 bytes, so all of it and its terminator are written *)
set (T := RecAns.RESP_HEAD ++ PF.pf_dec code).
assert (HTL : (6 <= length T <= 16)%nat) by exact (RecAns.resp_len code Hcode).
assert (HSL : sn_len (32 - 1) T = Z.of_nat (length T) + 1).
{ unfold sn_len, sn_bytes. change (Z.to_nat (32 - 1)) with 31%nat. rewrite length_app, firstn_all2 by lia. cbn [length]. lia. }
assert (HSB : sn_bytes (32 - 1) T = T ++ [0]).
{ unfold sn_bytes. change (Z.to_nat (32 - 1)) with 31%nat. rewrite firstn_all2 by lia. reflexivity. }
assert (HDOFF : F + 32 + (Z.of_nat (length T) + 1) <= 0x10000 \/ 0x606000 <= F + 32) by (clear - HFoff HTL; lia).
assert (HDSP : F + 32 + (Z.of_nat (length T) + 1) <= spZ (ms_regs ms3) - CMD_SNP_K).
{ rewrite Qsp3. unfold CMD_SNP_K. rewrite Hes. rewrite FS in Hslo. clear - HFceil Hceil Hslo Hsp1 HTL. lia. }
assert (HSPK : 0x606000 <= spZ (ms_regs ms3) - CMD_SNP_K).
{ rewrite Qsp3. unfold CMD_SNP_K. rewrite Hes. rewrite FS in Hslo. pose proof alloc_ceiling_value as (Hacr & _).
  clear - Hceil Hslo Hsp1 Hacr. lia. }
destruct (cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HAR3) as (_ & (HGW & cval & HGV) & _).
pose proof (ecall_pre_stk_at SEGS B CMD_SNP_K ANSWER_CODE_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly S2 W (ms_mem ms3) _ 0
  (ms_regs ms3) (sp1 - spZ regs) HJ2 Qsp3 Hsp1b ltac:(lia) ltac:(unfold CMD_SNP_K; rewrite Hes; lia)
  ltac:(unfold CMD_SNP_K; rewrite Hes, FS; lia) ltac:(rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])
  ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp)) as (HECP & HSLO3 & HWIN3).
assert (E13 : Z_to_bv 5 (10 + 3) = (13%bv : bv 5)) by (apply bv_eq; reflexivity).
eapply SRr_bind.
{ eapply (ASNPRINTF fx ly S2 W (ms_regs ms3) (ms_mem ms3) _ (F + 32) 32 0x21d40 []
    (map (argZ (ms_regs ms3)) [3; 4; 5; 6; 7] ++ []) T cval).
  - exact HECP.
  - exact HSLO3.
  - exact HWIN3.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact (cmd_consts_view_snp SEGS B LAWS HB IMG RLO RHI W (ms_mem ms3) HROD3).
  - apply Forall_forall. intros r Hr. destruct (ac_snp_rng r Hr) as (A1 & A2 & A3). clear - A1 A2 A3. lia.
  - apply Forall_forall. intros r Hr. destruct (ac_snp_rng r Hr) as (A1 & A2 & A3). destruct r as [r1 r2].
    cbn [fst snd] in A1, A2, A3. rewrite HSL.
    apply ac_lo_disj; [clear - A3; lia | clear - A1; lia | clear - A2; lia | clear - A2 HSPK; lia
    | unfold CMD_SNP_K; rewrite Hes; clear - Hes; lia | exact HDOFF].
  - exact HGW.
  - exact HGV.
  - clear - Hes. lia.
  - clear - Hes. lia.
  - clear - Hes. lia.
  - clear - Hes. lia.
  - rewrite HSL. apply ac_lo_disj; [clear - Hes; lia | clear - Hes; lia | clear - Hes; lia | clear - HSPK; lia
    | unfold CMD_SNP_K; rewrite Hes; clear - Hes; lia | exact HDOFF].
  - rewrite HSL. apply ac_lo_disj; [clear - Hes; lia | clear - Hes; lia | clear - Hes; lia | clear - HSPK; lia
    | unfold CMD_SNP_K; rewrite Hes; clear - Hes; lia | exact HDOFF].
  - split; [reflexivity | intros i Hi; cbn [length] in Hi; exfalso; clear - Hi; lia].
  - cbn [length Z.of_nat]. rewrite Qsp3. clear - Hsp1 Hshi H47. lia.
  - cbn [length Z.of_nat]. rewrite HSL. unfold snp_out.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
    [unfold CMD_SNP_K; rewrite Hes; clear - Hes; lia | clear - HDSP Hes; unfold CMD_SNP_K in HDSP; rewrite Hes in HDSP; lia].
  - apply (FR_cmd_intro _ _ _ _ _ RecAns.RESP_FMT RecAns.RESP_PS [PF.AInt code]).
    + unfold fmt_at. change (Z.of_nat (length RecAns.RESP_FMT)) with 7.
      split; [clear - Hes; lia|]. split; [exact (ac_fmt_bytes _ HLIT3)|].
      split; [rewrite HSL; apply ac_lo_disj; [clear - Hes; lia | clear - Hes; lia | clear - Hes; lia | clear - HSPK; lia
        | unfold CMD_SNP_K; rewrite Hes; clear - Hes; lia | exact HDOFF]|].
      split; [left; unfold kLowMemEnd; clear - Hes; lia|].
      split; [exact (zsh_lit_21d40 _ _ _ _ _ HAR3) | exact (ac_lit_hull _ _ _ _ _ HAR3)].
    + exact RecAns.resp_parse.
    + cbn [map RtPFCmd.arg_of app]. cbn [pf_args_asan pf_arg_asan]. refine (conj (conj Hcode _) I).
      unfold argZ. rewrite E13, R13. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite <- (Zmod_div_mod (2 ^ 32) (2 ^ 64) code); [reflexivity | lia | lia | exists (2 ^ 32); reflexivity].
    + exact (RecAns.resp_text code).
    + unfold RecAns.RESP_PS. cbn. trivial.
    + (* fr_lit_ok (recipe E.0.4): the format's address 0x21d40 in [CMD_IMG_LO, CMD_GOTW - 8], nonempty, %d only *)
      vm_compute. reflexivity.
  - clear - Hes. lia.
  - clear - HTL. lia.
  - clear - HF4096. lia.
  - rewrite HSL. pose proof alloc_ceiling_lt as Hlt. clear - HFceil HTL Hlt. lia.
  - rewrite HSL. unfold snp_out. cbn [pairwise].
    split; [apply Forall_cons; [|apply Forall_nil]; unfold zdisjoint; cbn [fst snd]; clear - HDSP; lia
    | split; [apply Forall_nil | exact I]].
  - rewrite HSL. intros a Ha. destruct (HFpres3 a ltac:(clear - Ha HTL; lia)) as [Hp Hno].
    split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. rewrite Qsp3, Hes. rewrite FS in Hslo.
    clear - Ha HTL HFceil Hceil Hslo Hsp1. lia.
  - (* the shared contract's band premise reads 8 bytes past the written part (a Theorem Labs lane's `+ 8`): the 17 bytes and 8
       more lie in the 128-byte fake frame (F + 32 + 25 <= F + 128), PASS4-REFIT.md E.0's amem_range_sub_app form *)
    rewrite HSL. exact (amem_range_sub_app F 128 (F + 32) (Z.of_nat (length T) + 1 + 8) HFapp HFceil ltac:(clear - Hes; lia) ltac:(clear - HTL; lia)
    ltac:(clear - Hes; lia)).
  - rewrite HSL. intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
    pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
    assert (Hx8 : x / 8 = F / 8 + (x / 8 - F / 8)) by lia. rewrite Hx8, Z.add_assoc. apply ZS3.
    assert (F mod 8 = 0) by (rewrite HFq, Z.mul_comm; replace 64 with (8 * 8) by reflexivity; rewrite Z.mul_assoc; apply Z_mod_mult).
    split; [apply Z.le_add_le_sub_l; apply Z.div_le_lower_bound; lia | apply Z.lt_sub_lt_add_l; apply Z.div_lt_upper_bound; lia].
  - rewrite HSL. apply (shadow_hull_vis_of_frame SEGS B LAWS ly S2 W (ms_mem ms3) _ 1 fpos (F + 32) _ HAR3 Hfin);
    [fold F; lia | fold F; change (fs_frame_bytes 1) with 128; lia | lia].
  - rewrite HSL. unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. clear - HDOFF. lia.
  - exact HFRM. }
cbv beta. intros W4 c4 _ (-> & fx1 & regs4 & mem4 & md4 & -> & Hfx4 & Hfrm4 & HAR4 & HP4 & Hsame4 & Ha04 & Hbuf4 & Hkeep4 & Hpres4).
rewrite HSL in Hkeep4.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT2).
assert (HJ4 : ajournal SEGS B ANSWER_CODE_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly S2 W mem4 md4 0).
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low ANSWER_CODE_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly S2 W
(ms_mem ms3) _ 0 mem4 md4 (fun a => (F + 32 <= a < F + 64) \/ (sp1 - 3 * ESTACK <= a < sp1)) S2 [(1, fpos)] HJ2).
- intros a Ha Hn. apply Hkeep4; [exact Ha | intros H; apply Hn; left; clear - H HTL; lia
  | rewrite Qsp3; intros H; apply Hn; right; unfold CMD_SNP_K in H; rewrite Hes in H |- *; clear - H; lia].
- exact Hpres4.
- exact Hsame4.
- intros a [Ha | Ha]; left.
+ right; right; right; left. exists 1, fpos. split; [left; reflexivity|].
left. unfold in_zr; cbn [fst snd]. fold F. change (fs_frame_bytes 1) with 128. lia.
+ left. rewrite FS, Hes in *. lia.
- exact HAR4.
- reflexivity.
- reflexivity.
- lia.
- exact Hfrs2.
- exact HQT2. }
assert (RA3 : w64 (raZ (ms_regs ms3)) = Z_to_bv 64 (BASE + 26072)) by (unfold raZ; rewrite R1; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
unfold cfg_at. rewrite RA3.
assert (K34 : forall a, KA a -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) (ms_mem ms3) a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & _). apply Hkeep4; [lia | lia | rewrite Qsp3; unfold CMD_SNP_K; lia]. }
jafter_call_keep_hi HS 1042%nat regs4 (mrestrict (w_H W) mem4) HP4 [0;1;2;3;4;5]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil;
(eapply (region_kept_aview E2 (w_H W) (ms_mem ms3) mem4); [first [exact V1041 | exact V1028 | exact V2 | exact V34] | | exact Hpres4]);
(intros a Ha; apply Hkeep4; [unfold SB in *; lia | unfold SB in *; lia | rewrite Qsp3; unfold CMD_SNP_K, SB in *; lia]). }
rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
(* the code after the snprintf call runs at the FP state fx1 the call returned: the symbolic state is read at fx1,
   the goal's post becomes apost_base at fx1 (ac_postF with the call's two FP clauses), and fx leaves the context,
   so every implicit FP state below is fx1 *)
pose proof (PaFx.st_ok_pi_restrict_xfx fx fx1 _ _ _ _ _ _ _ _ _ HS) as HS1. clear HS. rename HS1 into HS.
lazymatch goal with |- SRr _ _ _ (@apost_baseF _ _ _ _ _ ?STK0 ?FP0 ?rg0 ?ly0 ?S0 ?W0 ?m0 ?md0 ?k0 ?Q0) =>
  apply (SRr_mono _ _ _ (@apost_base fx1 rc SK SEGS B STK0 FP0 rg0 ly0 S0 W0 m0 md0 k0 Q0));
  [| intros W' c' _ HQ'; exact (ac_postF fx fx1 STK0 FP0 rg0 ly0 S0 W0 m0 md0 k0 Q0 W' c' HQ' Hfx4 Hfrm4)]
end.
clear RUNP RUNC Hfx4 Hfrm4 HFRM.
repeat match goal with H : context [fx] |- _ => clear H end.
clear fx.
pose (RUNP := @SRr_run_pi_AJ fx1 rc SK cmd_listing PL_cmd PI B LAWS).
pose (RUNC := @SRr_run_pi_AJ_call fx1 rc SK cmd_listing PL_cmd PI B LAWS).
remember (havoc E2 1042 (map (getr regs4) CLOB)) as E3 eqn:HE3 in HS.
assert (HAE3 : env_agree 32 (Ereg regs (ac_extra sp1)) E3) by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]).
assert (OLD3 : forall n, (n < 1042)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
clear HE3.
assert (W2 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact V2).
assert (W34 : bv_unsigned (ew E3 34) = sp1) by (rewrite OLD3 by lia; exact V34).
assert (W1028 : bv_unsigned (ew E3 1028) = F) by (rewrite OLD3 by lia; exact V1028).
assert (W1040 : bv_unsigned (ew E3 1040) = FL) by (rewrite OLD3 by lia; exact V1040).
assert (W1041 : bv_unsigned (ew E3 1041) = SB + F / 8) by (rewrite OLD3 by lia; exact V1041).
assert (EFA : frame_addr ly 1 fpos = F) by reflexivity.
clear R1 R2 R3 R4 R10 R11 R12 R13 RA3.
(* run 3: a0 := buf, the call of hand_back *)
paj_run_shc RUNP RUNC HS HJ4.
{ awr6 fpos sp1 regs FS W1041 W1028 W2 W34 EFA. }
rename ms into ms5, mat into mat5, HF into HF5, HFr into HFr5, HG into HG5.
(* the call of hand_back(buf) *)
assert (SIGHB : SIG CS_hand_back = BASE + AF_hand_back).
{ rewrite (cmd_sig_prog_PB CS_hand_back ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))). reflexivity. }
pmkst HS. rewrite SIGHB.
preg HS (10%bv : bv 5) R10. preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3.
preg HS (4%bv : bv 5) R4. preg HS (8%bv : bv 5) R8.
cbn [sv_denot] in R10, R1. rewrite W1028 in R10. rewrite (img_env_codeptr E3 HEI3 26080) in R1.
rewrite denot_off0, OLD3, OLD2, E34 in R2 by lia.
rewrite denot_off0, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite denot_off0, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in R4 by lia.
rewrite denot_off0, OLD3, OLD2, Esp in R8 by lia.
pose proof (proj1 HJ4) as HAR5.
assert (Qsp5 : spZ (ms_regs ms5) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
assert (HROD5 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms5)))
by exact (arodata_ok_journalP SEGS RLO RHI (RELRO_IMG SEGS B LAWS HB IMG) (RO := ROB SEGS B LAWS HB IMG) B _ _ FP ly S W mem md _ ly S2 W (ms_mem ms5) _ 0 HJ4 HFPRO HROD).
assert (HPS : as_prog_static B = YF0m.TFIB_PROG_STATIC) by exact (YF0m.ts_prog B HB).
assert (K45 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms5) a = aview SEGS (w_H W) mem4 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _). apply (aview_frame_pt E3 _ (w_H W) mem4 (ms_mem ms5) a HFr5); [lia|].
nwin_tac ltac:(fun H => rewrite ?W2, ?W34, ?W1028, ?W1041 in H; lia). }
assert (K05 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms5) a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite (K45 a Ha), (K34 a Ha); exact (K03 a Ha)).
pose proof (RecAns.resp_len code Hcode) as RL. pose proof (resp_length code Hcode) as RL2.
assert (HBUF : abytes_at SEGS W mem4 (F + 32) (resp code ++ [Z_to_bv 8 0])).
{ rewrite <- (RecAns.pf_resp code Hcode). fold T. intros i Hi. unfold PF.pf_bytes in Hi |- *.
  rewrite length_app, length_map in Hi. cbn [length] in Hi.
  assert (Hx : aview SEGS (w_H W) mem4 (F + 32 + Z.of_nat i) = Some (nth i (T ++ [0]) 0)).
  { rewrite (Hbuf4 (Z.of_nat i) ltac:(rewrite HSL; lia)), HSB, Nat2Z.id. reflexivity. }
  rewrite Hx. f_equal.
  change [Z_to_bv 8 0] with (map (Z_to_bv 8) [0]). rewrite <- map_app, map_nth.
  pose proof (ac_aview_rng _ _ _ _ _ Hx) as Rx.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity. }
assert (HSTR5 : astr_atR (rdW W (ms_mem ms5)) (F + 32) (resp code)).
{ split; [|exact (resp_no0 code)]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite (aview_frame_pt E3 _ (w_H W) mem4 (ms_mem ms5) (F + 32 + Z.of_nat i) HFr5); [exact (HBUF i ltac:(rewrite length_app; cbn [length]; lia)) | lia |].
nwin_tac ltac:(fun H => rewrite ?W2, ?W34, ?W1028, ?W1041 in H; unfold SB in *; lia). }
assert (ZS5 : forall j, 4 <= j < 8 -> rdW W (ms_mem ms5) (SB + F / 8 + j) = Some 0).
{ intros j Hj. pose proof (st_ok_region_nth E3 _ _ 0 _ HS eq_refl) as HR0.
cbn [ms_mem restrict mkst] in HR0.
assert (Hj4 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
destruct Hj4 as [-> | [-> | [-> | ->]]];
(apply (aview_of_val_mem1 SEGS); [|lia]);
(lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
refine (field_of_region E3 _ 1041 (SB + F / 8) _ 0 16 0 16 od 1%N (SLit 0) 0 HR0 W1041 _ _ _ _) end;
[cbn [In]; tauto | reflexivity | lia | lia]). }
assert (HF8m : F mod 8 = 0) by (rewrite HFq, Z.mul_comm; replace 64 with (8 * 8) by reflexivity; rewrite Z.mul_assoc; apply Z_mod_mult).
assert (HRA5 : range_addressable (rdW W (ms_mem ms5)) SHADOW_OFF (F + 32) (Z.of_nat (length (resp code)) + 1)).
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
assert (Hx8 : x / 8 = F / 8 + (x / 8 - F / 8)) by lia. rewrite Hx8, Z.add_assoc. apply ZS5.
split; [apply Z.le_add_le_sub_l; apply Z.div_le_lower_bound; lia | apply Z.lt_sub_lt_add_l; apply Z.div_lt_upper_bound; lia]. }
assert (HREP5 : rec_repA B ly S2 (rdW W (ms_mem ms5)) R O).
{ apply (rec_repA_kept ly S (rdW W mem) ly S2 (rdW W (ms_mem ms5)) R O HREP).
- intros pn Hpn. rewrite Eab. exact (rec_repA_in _ _ _ _ _ HREP pn Hpn).
- intros a Ha. apply K05. left. exact Ha.
- intros a Ha. apply K05. right. left. exact Ha.
- intros p n i Hpn Hi. apply K05. right. right. exists p, n.
split; [exact (rec_repA_in _ _ _ _ _ HREP (p, n) Hpn)|]. unfold req_size. destruct (Z.eqb_spec n 0); lia. }
assert (HOLD5 : aval_mem (rdW W (ms_mem ms5)) (A_G_REC + OFF_ANSWER) 8 old).
{ apply (aval_mem_kept (rdW W mem)); [exact HOLD|]. intros k Hk. apply K05. left. unfold OFF_ANSWER. lia. }
assert (HMO5 : mo_ok MT S2 (XM_HAND_BACK MT (resp code))).
{ rewrite ES2. apply (mo_ok_set_fs MT MTLF). apply (mo_ok_le MT MTL _ _ (XM_ANSWER_CODE MT code)); [exact MOK|].
unfold XM_ANSWER_CODE. pose proof (mo_free_nonneg MT MTL). lia. }
assert (HNFP : forall a, spZ regs <= a < 2 ^ 64 -> ~ inFP FP a).
{ intros a Ha (r & Hr & Hrq). destruct Hr as [<- | Hr]; [cbn [fst snd] in Hrq; unfold A_G_REC, OFF_ANSWER in Hrq; lia|].
unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). apply in_filter_old in Hpn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (rec_repA_in _ _ _ _ _ HREP (p, n) Hpn)) as (_ & _ & Hpc & _).
cbn [fst snd] in Hrq. lia. }
assert (HCH5 : exists ch5, achain ly (rdW W (ms_mem ms5)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms5)) ch5).
{ unfold s0Z. rewrite R8, unsigned_lit_small by lia.
pose proof (st_ok_region_nth E3 _ _ 4 _ HS eq_refl) as HR4. cbn [ms_mem restrict mkst] in HR4.
destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch).
eapply (achain_push ly (rdW W mem) (rdW W (ms_mem ms5)) (spZ regs) (s0Z regs) (raZ regs) ch); [exact Hch | lia | | | | exact Hra4 | lia | exact (Z_mod_16_8 _ Hal16) | exact Hlt | lia].
+ intros a Ha. exact (aview_above_of_journal B _ _ FP ly S W mem md _ _ _ _ _ _ _ HJ4 a Ha (HNFP a Ha)).
+ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
replace (spZ regs - 8) with (spZ regs + -8) by lia.
refine (field_of_region E3 _ 2 (spZ regs) _ (-64) 0 (-64) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR4 W2 _ _ _ _);
[cbn [In]; tauto | rewrite denot_off0, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
| unfold raZ; apply bv_unsigned_in_range | lia].
+ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
replace (spZ regs - 16) with (spZ regs + -16) by lia.
refine (field_of_region E3 _ 2 (spZ regs) _ (-64) 0 (-64) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR4 W2 _ _ _ _);
[cbn [In]; tauto | rewrite denot_off0, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
| unfold s0Z; apply bv_unsigned_in_range | lia].
- exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH5 as (ch5 & HCH5).
assert (HFPKA : forall a, inFP FP a -> KA a).
{ intros a (r & Hr & Hrq). destruct Hr as [<- | Hr].
- left. cbn [fst snd] in Hrq. unfold OFF_ANSWER in Hrq. lia.
- right. right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). apply in_filter_old in Hpn.
exists p, n. split; [exact (rec_repA_in _ _ _ _ _ HREP (p, n) Hpn) | cbn [fst snd] in Hrq; exact Hrq]. }
assert (HBS : HAND_BACK_STK = 16448) by (vm_compute; reflexivity).
assert (HAFO5 : afobj SEGS B ly S2 W (ms_mem ms5) (F + 32) (Z.of_nat (length (resp code)) + 1)).
{ split; [exists 1, fpos; split; [exact Hfin|]; split; [lia|]; fold F; split; [exact HF8m|]; split; [lia | change (fs_frame_bytes 1) with 128; lia]|].
split; [rewrite Zplus_mod, HF8m; reflexivity | exact HRA5]. }
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms5) (ms_mem ms5) (Z_to_bv 64 (BASE + AF_hand_back)) ANSWER_CODE_STK (spZ regs) FP ly S W mem md
[(1, fpos)] ly S2 _ 0 HAND_BACK_STK FP EV_HAND_BACK (sp1 - spZ regs) (getr (ms_regs ms5) 1) ch5 _ HJ4 Qsp5 Hsp1b);
[ lia | rewrite HBS; lia | rewrite HBS, FS; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp | reflexivity
| rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]
| rewrite R1, unsigned_lit_small by lia; lia
| exact HCH5
| intros HPRE5; exact (THAND_BACK fx1 ly S2 W (ms_regs ms5) (ms_mem ms5) _ ch5 (F + 32) old (resp code) R O HPRE5 HROD5 R10 ltac:(lia) HSTR5
ltac:(unfold LMAX; lia) HAFO5 HREP5 HOLD5 Hold64 ltac:(unfold EV_ANSWER_CODE in Hev; lia) ltac:(unfold LIVE_ANSWER_CODE in Hlive; lia) HMO5)
| intros a Ha; destruct (HFPB ly S2 a Ha) as [Hpg | (b & n & Hbn & Hba)];
[ right; right; right; right; left; split; [exact Ha|]; rewrite HPS; split; [exact Hpg | exact (cmd_prog_img SEGS B LAWS HB IMG a Hpg)]
| right; left; split; [exact Ha|]; exists b, n; split; [apply in_app_or in Hbn as [Hbn | Hbn]; [rewrite Eab; exact Hbn | exact Hbn] | exact Hba] ]
| intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _; exfalso; destruct (KLOC a (HFPKA a Ha)) as (Hb & _); rewrite FS in Hw; lia ]. }
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HJ6c & HP6 & HK6).
cbv zeta in HK6. destruct HK6 as (p1 & p2 & O' & Ha06 & Hp2 & Hp12 & Hnp & Hbl6 & HREP6 & HO' & HSTR6 & HBB6 & HMLE6).
rewrite R1.
pose proof (proj1 HJ6) as HAR6.
pose proof HJ6c as (_ & Hly6 & _ & _ & _ & Hfrs6 & _). cbn [app] in Hfrs6.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly6 HAR5 Hly6) as (Eab6 & Efa6 & _).
assert (EFA6 : frame_addr ly6 1 fpos = F) by (rewrite Efa6; reflexivity).
assert (Hfin6 : In (1, fpos) (frames S6)) by (rewrite Hfrs6; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR6 Hfin6) as (_ & _ & HFpres6 & HFSpres6). rewrite EFA6 in HFpres6, HFSpres6.
change (fs_frame_bytes 1) with 128 in HFpres6, HFSpres6. change (128 / 8) with 16 in HFSpres6.
jafter_call_keep_hi HS 1058%nat regs6 (mrestrict (w_H W6) mem6) HP6 [0;1;2;3;4;5]%nat HS6.
match type of HS6 with ?tq -> _ => assert (HRK : tq); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_fshadow_sub (segs := SEGS) B E3 _ _ FP ly S2 W (ms_mem ms5) _ ly6 S6 W6 mem6 md6 _ 1041 (SB + F / 8) _ _ _ _ _ 1 fpos HJ6c W1041 Hfin);
[ unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; lia
| unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia
| intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (_ & _ & HnS & _); lia
| intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
apply (proj1 (HFSpres6 (a - (SB + F / 8)) ltac:(lia))) ].
- eapply (region_kept_frame_sub (segs := SEGS) B E3 _ _ FP ly S2 W (ms_mem ms5) _ ly6 S6 W6 mem6 md6 _ 1028 F _ _ _ _ _ 1 fpos HJ6c W1028 Hfin);
[ fold F; lia | fold F; change (fs_frame_bytes 1) with 128; lia
| intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (_ & HnF & _); lia
| intros a Ha; lia ].
- eapply (region_kept_frame_sub (segs := SEGS) B E3 _ _ FP ly S2 W (ms_mem ms5) _ ly6 S6 W6 mem6 md6 _ 1028 F _ _ _ _ _ 1 fpos HJ6c W1028 Hfin);
[ fold F; lia | fold F; change (fs_frame_bytes 1) with 128; lia
| intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)) as (_ & HnF & _); lia
| intros a Ha; exact (proj1 (HFpres6 a ltac:(lia))) ].
- eapply (region_kept_stack_sub SEGS B E3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJ6c HJ6 W2);
[lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)); lia].
- eapply (region_kept_stack_sub SEGS B E3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJ6c HJ6 W2);
[lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)); lia].
- eapply (region_kept_stack_sub SEGS B E3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _ HJ6c HJ6 W34);
[lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HFPKA a HFa)); lia]. }
rewrite <- restrict_mkst_fx in HS6. clear HS. rename HS6 into HS.
remember (havoc E3 1058 (map (getr regs6) CLOB)) as E4 eqn:HE4 in HS.
assert (HAE4 : env_agree 32 (Ereg regs (ac_extra sp1)) E4) by (rewrite HE4; apply env_agree_havoc_ge; [lia | exact HAE3]).
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc_hi; [exact HEI3 | unfold A_LIM; lia]).
assert (OLD4 : forall n, (n < 1058)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply ew_havoc_old; exact Hn).
assert (E1062 : ew E4 1062 = Z_to_bv 64 p2).
{ rewrite HE4. change 1062%nat with (1058 + 4)%nat. rewrite (ew_havoc_new E3 1058 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
unfold CLOB. cbn [map nth]. exact Ha06. }
clear HE4.
assert (X2 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact W2).
assert (X34 : bv_unsigned (ew E4 34) = sp1) by (rewrite OLD4 by lia; exact W34).
assert (X1028 : bv_unsigned (ew E4 1028) = F) by (rewrite OLD4 by lia; exact W1028).
assert (X1040 : bv_unsigned (ew E4 1040) = FL) by (rewrite OLD4 by lia; exact W1040).
assert (X1041 : bv_unsigned (ew E4 1041) = SB + F / 8) by (rewrite OLD4 by lia; exact W1041).
clear R1 R2 R3 R4 R8 R10.
(* run 4: the call of the free wrapper on hand_back's returned copy *)
paj_run_shc RUNP RUNC HS HJ6.
{ awr6 fpos sp1 regs FS X1041 X1028 X2 X34 EFA6. }
rename ms into ms7, mat into mat7, HF into HF7, HFr into HFr7, HG into HG7.
(* the call of the free wrapper: free(hand_back's returned copy) *)
pmkst HS. rewrite (pal_free B TL).
preg HS (10%bv : bv 5) R10. preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3.
preg HS (4%bv : bv 5) R4. preg HS (8%bv : bv 5) R8.
rewrite denot_off0, E1062 in R10. cbn [sv_denot] in R1. rewrite (img_env_codeptr E4 HEI4 26084) in R1.
rewrite denot_off0, OLD4, OLD3, OLD2, E34 in R2 by lia.
rewrite denot_off0, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in R3 by lia.
rewrite denot_off0, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in R4 by lia.
rewrite denot_off0, OLD4, OLD3, OLD2, Esp in R8 by lia.
pose proof (proj1 HJ6) as HAR7.
assert (Qsp7 : spZ (ms_regs ms7) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
pose proof HJ6 as (_ & Hly7 & _ & _ & _ & _ & Hnev7 & _).
pose proof Hly7 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop7 & _).
assert (HCP7 : exists ch7, chain_pre ly6 (rdW W6 (ms_mem ms7)) (ms_regs ms7) ch7).
{ pose proof (st_ok_region_nth E4 _ _ 4 _ HS eq_refl) as HR4. cbn [ms_mem restrict mkst] in HR4.
assert (Hs07 : s0Z (ms_regs ms7) = spZ regs) by (unfold s0Z; rewrite R8, unsigned_lit_small by lia; reflexivity).
assert (Hra7 : 4096 <= raZ (ms_regs ms7)) by (unfold raZ; rewrite R1, unsigned_lit_small by lia; lia).
destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch).
apply (achain_chain_pre ly6 _ (spZ regs + (sp1 - spZ regs)) (spZ regs) _ (ms_regs ms7)); [| rewrite Qsp7; lia | exact Hs07 | exact Hra7].
eapply (achain_push ly6 (rdW W mem) (rdW W6 (ms_mem ms7)) (spZ regs) (s0Z regs) (raZ regs) ch);
[apply (achain_ly_top ly ly6); [exact Etop7 | exact Hch] | rewrite Etop7; lia | | | | exact Hra4 | lia | exact (Z_mod_16_8 _ Hal16) | rewrite Etop7; exact Hlt | lia].
+ intros a Ha. exact (aview_above_of_journal B _ _ FP ly S W mem md _ _ _ _ _ _ _ HJ6 a Ha (HNFP a Ha)).
+ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
replace (spZ regs - 8) with (spZ regs + -8) by lia.
refine (field_of_region E4 _ 2 (spZ regs) _ (-64) 0 (-64) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR4 X2 _ _ _ _);
[cbn [In]; tauto | rewrite denot_off0, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
| unfold raZ; apply bv_unsigned_in_range | lia].
+ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
replace (spZ regs - 16) with (spZ regs + -16) by lia.
refine (field_of_region E4 _ 2 (spZ regs) _ (-64) 0 (-64) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR4 X2 _ _ _ _);
[cbn [In]; tauto | rewrite denot_off0, OLD4, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
| unfold s0Z; apply bv_unsigned_in_range | lia].
- exists []. apply (achain_chain_pre ly6 _ (spZ regs + (sp1 - spZ regs)) (spZ regs) [] (ms_regs ms7));
[left; split; [right; left; rewrite Etop7; lia | reflexivity] | rewrite Qsp7; lia | exact Hs07 | exact Hra7]. }
destruct HCP7 as (ch7 & HCP7).
assert (Hinp2 : In (p2, Z.of_nat (length (resp code)) + 1) (ablocks B ly6 S6)) by (apply Hbl6; right; right; reflexivity).
assert (HMO7 : mo_ok MT S6 (mo_free MT)).
{ apply (mo_ok_step MT MTL S2 S6 (XM_HAND_BACK MT (resp code)) (mo_free MT)); [|exact HMLE6].
rewrite ES2. apply (mo_ok_set_fs MT MTLF). exact MOK. }
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE4 fx1) W6 (ms_regs ms7) (ms_mem ms7) ANSWER_CODE_STK (spZ regs) FP ly S W mem md
[(1, fpos)] ly6 S6 _ _ p2 (Z.of_nat (length (resp code)) + 1) (sp1 - spZ regs) (Z_to_bv 64 (BASE + 26084)) ch7 HJ6 Hinp2 R10 Qsp7 Hsp1b);
[ lia | rewrite Has, FS; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
| unfold EV_ANSWER_CODE in Hev; lia | exact HCP7
| intros Hin i Hi; destruct (Z.eq_dec p2 old) as [Eo | Ne];
[ destruct (inFP_ablocks_fp (filter (fun pn => fst pn =? old) O) p2 (Z.of_nat (length (resp code)) + 1) i
(in_filter_old_intro old O _ (old_in_O ly S W mem md R O old _ HAR HREP HOLD Hold64 Hin Eo) Eo) Hi) as (r & Hr & Hrr);
exists r; split; [right; exact Hr | exact Hrr]
| exfalso; exact (proj2 (Hnp _ ltac:(rewrite Eab; exact Hin) Ne) eq_refl) ]
| exact HMO7 ]. }
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HP8 & (l1 & l2 & El1 & El2) & Hfrs8 & HK8 & HMLE8 & HJ8c).
pose proof (proj1 HJ8) as HAR8.
pose proof HJ8c as (_ & Hly8 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly8 HAR7 Hly8) as (_ & Efa8 & _).
assert (EFA8 : frame_addr ly8 1 fpos = F) by (rewrite Efa8; exact EFA6).
assert (Hfin8 : In (1, fpos) (frames S8)) by (rewrite Hfrs8; exact Hfin6).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR8 Hfin8) as (_ & _ & HFpres8 & HFSpres8). rewrite EFA8 in HFpres8, HFSpres8.
change (fs_frame_bytes 1) with 128 in HFpres8, HFSpres8. change (128 / 8) with 16 in HFSpres8.
pose proof HK8 as (HK81 & HK82 & HK83 & _ & _ & _).
pose proof HJ8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ8pres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR7 Hinp2) as (_ & Hp24096 & Hp2ceil & Hp2app & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly6 S6 W6 (ms_mem ms7) _ p2 _ 1 fpos HAR7 Hinp2 Hfin6) as Hd2.
unfold zdisjoint in Hd2. cbn [fst snd] in Hd2. rewrite EFA6 in Hd2. change (fs_frame_bytes 1) with 128 in Hd2.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hp2app.
jafter_call_keep_hi HS 1074%nat regs8 (mrestrict (w_H W8) mem8) HP8 [0;1;2;3;4;5]%nat HS8.
match type of HS8 with ?tq -> _ => assert (HRK : tq); [|specialize (HS8 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_ownframe_aj SEGS B E4 ly6 S6 W6 (ms_mem ms7) W8 mem8 _ _ _ 1041 0 16 0 16 _ (SB + F / 8) 1 fpos HK8 X1041 Hfin6);
[ right; unfold shadow_addr; rewrite EFA6, <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia
| intros a Ha Hp; unfold SB in *; lia
| intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
apply (proj1 (HFSpres8 (a - (SB + F / 8)) ltac:(lia))) ].
- eapply (region_kept_frame_aj SEGS B E4 ly6 S6 W6 (ms_mem ms7) W8 mem8 _ _ _ 1028 120 128 120 120 _ F 1 fpos HK8 X1028 Hfin6);
[ rewrite EFA6; lia | rewrite EFA6; change (fs_frame_bytes 1) with 128; lia | lia | intros a Ha Hp; lia ].
- eapply (region_kept_ownframe_aj SEGS B E4 ly6 S6 W6 (ms_mem ms7) W8 mem8 _ _ _ 1028 0 32 0 24 _ F 1 fpos HK8 X1028 Hfin6);
[ left; rewrite EFA6; change (fs_frame_bytes 1) with 128; lia | intros a Ha Hp; lia | intros a Ha; exact (proj1 (HFpres8 a ltac:(lia))) ].
- eapply (region_kept_hi2 E4 (w_H W6) (w_H W8) (ms_mem ms7) mem8 2 (spZ regs)); [exact X2 | intros a Ha; apply HK81; lia | intros a Ha; apply HJ8pres; rewrite FS; lia].
- eapply (region_kept_hi2 E4 (w_H W6) (w_H W8) (ms_mem ms7) mem8 2 (spZ regs)); [exact X2 | intros a Ha; apply HK81; lia | intros a Ha; apply HJ8pres; rewrite FS; lia].
- eapply (region_kept_hi2 E4 (w_H W6) (w_H W8) (ms_mem ms7) mem8 34 sp1); [exact X34 | intros a Ha; apply HK81; lia | intros a Ha; apply HJ8pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS8. clear HS. rename HS8 into HS.
remember (havoc E4 1074 (map (getr regs8) CLOB)) as E5 eqn:HE5 in HS.
assert (HAE5 : env_agree 32 (Ereg regs (ac_extra sp1)) E5) by (rewrite HE5; apply env_agree_havoc_ge; [lia | exact HAE4]).
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc_hi; [exact HEI4 | unfold A_LIM; lia]).
assert (OLD5 : forall n, (n < 1074)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply ew_havoc_old; exact Hn).
clear HE5.
assert (Y2 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact X2).
assert (Y34 : bv_unsigned (ew E5 34) = sp1) by (rewrite OLD5 by lia; exact X34).
assert (Y1028 : bv_unsigned (ew E5 1028) = F) by (rewrite OLD5 by lia; exact X1028).
assert (Y1040 : bv_unsigned (ew E5 1040) = FL) by (rewrite OLD5 by lia; exact X1040).
assert (Y1041 : bv_unsigned (ew E5 1041) = SB + F / 8) by (rewrite OLD5 by lia; exact X1041).
assert (EFL8 : flag_addr ly8 1 fpos = FL).
{ pose proof EFA8 as Hx. unfold F, frame_addr in Hx. unfold FL, flag_addr. lia. }
destruct (FFL _ _ _ _ _ 1 fpos HAR8 Hfin8) as (HFLp8 & HFLo8 & _ & _). rewrite EFL8 in HFLp8, HFLo8.
assert (HFLnS : ~ (SB + F / 8 <= FL < SB + F / 8 + 16)).
{ intros Hx. apply (proj2 (HFSpres8 (FL - (SB + F / 8)) ltac:(lia))).
replace (shadow_addr F + (FL - (SB + F / 8))) with FL by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia). exact HFLo8. }
assert (HFLnF : ~ (F <= FL < F + 128)) by (intros Hx; exact (proj2 (HFpres8 FL Hx) HFLo8)).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 1040%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Y1040; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp8)
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Y1040, Y1041, Y1028, Y2, Y34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
(* the epilogue: buf's shadow := f8, the frame's magic retired, the frame's shadow := f5, its flag byte := 0 (the
   release), the saved registers back, a0 := code, return *)
pose (RUNF := @aj_flag_store_pi fx1 rc SK cmd_listing PL_cmd PI B LAWS ML AFREE_LAW FFL).
paj_run_flag_sh RUNF HS HJ8.
- lia.
- intros a (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
destruct Hin as [<- | Hin]; [right; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Y1040 in Hr; rewrite EFL8; lia|]. left.
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Y1041, ?Y1028, ?Y2, ?Y34 in Hr;
first [ exfalso; lia | left; rewrite FS; lia
| right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; rewrite EFA8; change (fs_frame_bytes 1) with 128; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA8, <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia ] ] |]).
destruct Hin.
- intros msr HSr. rewrite EFL8.
pose proof (st_ok_pi_region_nth E5 _ _ 0 _ HSr eq_refl) as HR0.
pose proof (field_of_region E5 _ 1040 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR0 Y1040 ltac:(cbn [In]; tauto) eq_refl ltac:(lia) ltac:(lia)) as HV.
specialize (HV 0%nat ltac:(lia)). rewrite !Z.add_0_r in HV. rewrite HV. reflexivity.
-
rename ms into ms9, mat into mat9, HF into HF9, HFr into HFr9, HG into HG9.
clear R1 R2 R3 R4 R8 R10.
preg HS (1%bv : bv 5) R1. preg HS (10%bv : bv 5) R10.
rewrite denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) in R1 by lia.
rewrite denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 10%nat 10%bv eq_refl), H10 in R10 by lia.
(* the recorder's bytes and the surviving blocks from hand_back's return to here *)
pose proof (ablocks_nodup _ _ _ _ _ HAR7) as ND. rewrite El1 in ND.
assert (EAB9 : ablocks B ly8 (stack_free_state 1 fpos S8) = l1 ++ l2).
{ unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly8 S8). exact El2. }
assert (HO'B : forall pn, In pn O' -> In pn (l1 ++ l2)).
{ intros pn Hpn. pose proof (rec_repA_in _ _ _ _ _ HREP6 pn Hpn) as H6. rewrite El1 in H6.
apply in_app_or in H6 as [H | [H | H]]; [apply in_or_app; left; exact H | | apply in_or_app; right; exact H].
exfalso. rewrite <- H in Hpn. apply HO' in Hpn as [[Ho Hoo] | Hp].
- exact (proj2 (Hnp _ ltac:(rewrite Eab; exact (rec_repA_in _ _ _ _ _ HREP _ Ho)) Hoo) eq_refl).
- injection Hp as Eqp. apply Hp12. symmetry. exact Eqp. }
set (KB := fun a : Z => (A_G_REC <= a < A_G_REC + 960) \/ (A_REC_SPILL <= a < A_REC_SPILL + 56) \/
(exists p n, In (p, n) (l1 ++ l2) /\ p <= a < p + req_size n)).
assert (KBLOC : forall a, KB a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16) /\ a <> FL).
{ intros a Ha. destruct Ha as [Ha | [Ha | (p & n & Hpn & Hpa)]].
- apply KLOC. left. exact Ha.
- apply KLOC. right. left. exact Ha.
- rewrite <- El2 in Hpn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR8 Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpres8 & _).
pose proof (sep_block_frame SEGS B LAWS ly8 S8 W8 mem8 md8 p n 1 fpos HAR8 Hpn Hfin8) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA8 in Hd. change (fs_frame_bytes 1) with 128 in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
split; [lia|]. split; [lia|]. split; [unfold SB; lia|]. intros ->. exact (proj2 (Hpres8 FL ltac:(lia)) HFLo8). }
assert (K69 : forall a, KB a -> aview SEGS (w_H W8) (ms_mem ms9) a = aview SEGS (w_H W6) mem6 a).
{ intros a Ha. destruct (KBLOC a Ha) as (Hb & HnF & HnS & HnFL).
rewrite (aview_frame_pt E5 _ (w_H W8) mem8 (ms_mem ms9) a HFr9); [| lia | nwin_tac ltac:(fun H => rewrite ?Y2, ?Y34, ?Y1028, ?Y1040, ?Y1041 in H; lia)].
rewrite <- (aview_frame_pt E4 _ (w_H W6) mem6 (ms_mem ms7) a HFr7); [| lia | nwin_tac ltac:(fun H => rewrite ?X2, ?X34, ?X1028, ?X1041 in H; lia)].
destruct Ha as [Ha | [Ha | (p & n & Hpn & Hpa)]].
- apply HK83; [apply (cmd_prog_img SEGS B LAWS HB IMG); left; unfold in_zr, REC_SIZE; cbn [fst snd]; exact Ha
| rewrite (YF0m.ts_owned B HB); apply (not_in_ranges _ 0x5e32c0 0x5e3680); [vm_compute; reflexivity | unfold A_G_REC in Ha; lia]
| rewrite (YF0m.ts_errno B HB); unfold YF0m.TFIB_ERRNO, A_G_REC in *; lia].
- apply HK83; [apply (cmd_prog_img SEGS B LAWS HB IMG); right; left; unfold in_zr, SC_SIZE; cbn [fst snd]; exact Ha
| rewrite (YF0m.ts_owned B HB); apply (not_in_ranges _ 0x5e3760 0x5e3798); [vm_compute; reflexivity | unfold A_REC_SPILL in Ha; lia]
| rewrite (YF0m.ts_errno B HB); unfold YF0m.TFIB_ERRNO, A_REC_SPILL in *; lia].
- assert (Hpn6 : In (p, n) (ablocks B ly6 S6)) by (rewrite El1; apply in_app_or in Hpn as [H | H]; apply in_or_app; [left; exact H | right; right; exact H]).
assert (Hne : (p, n) <> (p2, Z.of_nat (length (resp code)) + 1)) by (intros Eqp; rewrite Eqp in Hpn; exact (List.NoDup_remove_2 _ _ _ ND Hpn)).
pose proof (sep_blocks SEGS B LAWS ly6 S6 W6 (ms_mem ms7) _ p n p2 _ HAR7 Hpn6 Hinp2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
replace a with (p + (a - p)) by lia. apply (HK82 p n (a - p) Hpn6); [lia | cbv beta; lia]. }
eapply (paj_ret_at (PL := PL_cmd) (PI := PI) W8 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
eexists ly8, (stack_free_state 1 fpos S8), (ms_regs ms9), (ms_mem ms9), _.
pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
split; [rewrite R1, Hra'; reflexivity|].
split; [eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ8 | unfold EV_ANSWER_CODE; lia]|].
split; [eapply (aregs_preserved_of_st_ok SEGS (w_H W8) E5 _ ms9 regs (ac_extra sp1) HS HAE5); vm_compute; reflexivity|].
exists p1, O'. cbv zeta.
split; [rewrite R10; reflexivity|].
split; [intros pn Hpn Hpo; exact (proj1 (Hnp pn ltac:(rewrite Eab; exact Hpn) Hpo))|].
split.
{ intros pn. rewrite EAB9. split.
- intros Hpn.
assert (Hpn6 : In pn (ablocks B ly6 S6)) by (rewrite El1; apply in_app_or in Hpn as [H | H]; apply in_or_app; [left; exact H | right; right; exact H]).
assert (Hne : pn <> (p2, Z.of_nat (length (resp code)) + 1)) by (intros Eqp; rewrite Eqp in Hpn; exact (List.NoDup_remove_2 _ _ _ ND Hpn)).
apply Hbl6 in Hpn6 as [H | [H | H]]; [left; rewrite <- Eab; exact H | right; exact H | exfalso; exact (Hne H)].
- intros Hpn.
assert (Hpn6 : In pn (ablocks B ly6 S6)) by (apply Hbl6; destruct Hpn as [[H1 H2] | H]; [left; split; [rewrite Eab; exact H1 | exact H2] | right; left; exact H]).
rewrite El1 in Hpn6. apply in_app_or in Hpn6 as [H | [H | H]]; [apply in_or_app; left; exact H | | apply in_or_app; right; exact H].
exfalso. rewrite <- H in Hpn. destruct Hpn as [[H1 H1o] | H2]; [exact (proj2 (Hnp _ ltac:(rewrite Eab; exact H1) H1o) eq_refl) | injection H2 as Eqp; apply Hp12; symmetry; exact Eqp]. }
split.
{ change (fst (rec_answer_code R code)) with (fst (hand_back R (resp code))).
apply (rec_repA_kept ly6 S6 (rdW W6 mem6) ly8 (stack_free_state 1 fpos S8) (rdW W8 (ms_mem ms9)) _ O' HREP6).
- intros pn Hpn. rewrite EAB9. exact (HO'B pn Hpn).
- intros a Ha. apply K69. left. exact Ha.
- intros a Ha. apply K69. right. left. exact Ha.
- intros p n i Hpn Hi. apply K69. right. right. exists p, n. split; [exact (HO'B _ Hpn)|].
unfold req_size. destruct (Z.eqb_spec n 0); lia. }
split; [exact HO'|].
split.
{ assert (B9 : blocks_bytes (stack_free_state 1 fpos S8) = bsum (ablocks B ly8 (stack_free_state 1 fpos S8))) by apply blocks_bytes_bsum.
assert (B6 : blocks_bytes S6 = bsum (ablocks B ly6 S6)) by apply blocks_bytes_bsum.
assert (B2 : blocks_bytes S2 = blocks_bytes S) by (rewrite ES2; reflexivity).
rewrite B9, EAB9, bsum_app. rewrite B6, El1, bsum_app, bsum_cons, B2 in HBB6. cbn [snd] in HBB6.
unfold LIVE_ANSWER_CODE. lia. }
unfold XM_ANSWER_CODE, stack_free_state. apply (mo_le_set_fs_r MT MTLF).
apply (mo_le_trans MT MTL S S6 S8); [| exact HMLE8].
apply (mo_le_set_fs_l MT MTLF S S6 fS2). rewrite <- ES2. exact HMLE6.
Qed.
End e.
End f.
End d.

(* the statement at the Section's FP state, with the statement's Section hypotheses and the walk's *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTACK1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : @cmd_val_objs rc PI.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis TLF : @PALibF rc cmd_listing PI B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
Hypothesis cmd_palib : forall B0 : asyms, YF0m.CmdBSyms B0 -> @PALib rc cmd_listing PI B0.
Hypothesis cmd_sig_prog_PB : @cmd_sig_prog rc PI.
Hypothesis cmd_img_facts_tfib : forall B0 : asyms, YF0m.CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis cmd_frame_flag_law : forall B0 : asyms, frame_flag_lawP SEGS B0.
Theorem tanswer_code_holds : tanswer_code_spec B MT.
Proof.
exact (@tanswer_code_holds_any rc SK PI B MT THAND_BACK AFREE4 ASTACK1 AFREE_LAW ASNPRINTF VOBJS HB TLF MTL MTLF cmd_palib
  cmd_sig_prog_PB cmd_img_facts_tfib cmd_frame_flag_law fx).
Qed.
End e2.
End f2.
End d2.

Check tanswer_code_holds.
Print Assumptions tanswer_code_holds.
