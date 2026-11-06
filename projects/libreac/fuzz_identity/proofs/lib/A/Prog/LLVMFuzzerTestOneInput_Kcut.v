(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530,
   1556-1561, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_D4.v; 198 of its 270 lines of code are new or changed and 866 lines of the source are left out. *)
(* The cut points of segment K's walk (fuzz_identity.asan 0x81e60 .. 0x82090), and the model facts the walk
   decides every compare with.

   seg_K of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v splits at two slots of the listing:
     0x81f00 (BASE + 0x17f4)  the head of the token loop (tk = nm lower-cased, its first '-' dropped);
     0x81fa0 (BASE + 0x1894)  after the loop, at the scope store of `count` and reac_box_catalogue.
   `k_loop_at g pos mf nm tk dp j t d` is the state at the loop head after j bytes of the expected name,
   `k_mid g pos mf nm tk dp` the state at 0x81fa0. The two cut statements below are what the helper lanes prove:
     `k_token_loop_stmt`  the loop, from k_loop_at to k_mid (file LLVMFuzzerTestOneInput_Ktok.v);
     `k_cat_tail_stmt`    the catalogue tail, from k_mid to inv_K_end (file LLVMFuzzerTestOneInput_Kcat.v).
   LLVMFuzzerTestOneInput_K.v proves the rest (the r <> 0 branch, the three strlen / check_str pairs and the two
   strcmp of name and display, 0x81e60 .. 0x81f00) and composes the three into seg_K.

   Nothing here is proved about the machine: the statements are state predicates in the boundary layer's own
   shape (`acut`), and the model lemmas are facts of lib/Prog/SlotModel.v's functions of the input bytes alone. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require check_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the model: the bytes K compares, and the token the loop checks ---------------------------------------
   Everything here is a fact of lib/Prog/SlotModel.v's functions of the input bytes alone; no address, no
   machine state. The walk uses them to decide each compare and to refute each abort. *)
Import RcIdentModel.
Definition nzb (b : byte) : Prop := bz b <> 0.
Definition nzl (l : list byte) : Prop := Forall nzb l.

Lemma k_nzl_app : forall l1 l2, nzl l1 -> nzl l2 -> nzl (l1 ++ l2).
Proof. intros l1 l2 H1 H2. unfold nzl. apply Forall_app. split; assumption. Qed.

Lemma k_forallb_nzl : forall l, forallb (fun b => negb (bz b =? 0)) l = true -> nzl l.
Proof.
intros l H. apply Forall_forall. intros b Hb.
rewrite forallb_forall in H. specialize (H b Hb). apply negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

(* The digits of a decimal field are '0' .. '9'. *)
Lemma k_dec1_nz : forall x, 0 <= x <= 40 -> nzl (IdentSpec.DEC x 1).
Proof.
intros x Hx. apply k_forallb_nzl.
exact (IdentSpec.z_all_spec (fun x => forallb (fun b => negb (bz b =? 0)) (IdentSpec.DEC x 1))
  (Z.to_nat 41) 0 ltac:(vm_compute; reflexivity) x ltac:(lia)).
Qed.

Lemma k_dec2_nz : forall x, 0 <= x <= 40 -> nzl (IdentSpec.DEC x 2).
Proof.
intros x Hx. apply k_forallb_nzl.
exact (IdentSpec.z_all_spec (fun x => forallb (fun b => negb (bz b =? 0)) (IdentSpec.DEC x 2))
  (Z.to_nat 41) 0 ltac:(vm_compute; reflexivity) x ltac:(lia)).
Qed.

(* A name taken from the identity struct stops at its first zero byte. *)
Lemma k_firstn_fz_nz : forall l, nzl (firstn (first_zero l) l).
Proof.
induction l as [|b l IH]; cbn [first_zero firstn]; [constructor|].
destruct (Z.eqb_spec (bz b) 0) as [E|E]; cbn [firstn]; [constructor|].
constructor; [exact E | exact IH].
Qed.

Lemma k_name_str_nz : forall idb, nzl (SlotModel.name_str idb).
Proof. intro idb. unfold SlotModel.name_str. apply k_firstn_fz_nz. Qed.

Lemma k_stem_img_nz : forall f, nzl (SlotModel.stem_img f).
Proof.
intro f. unfold SlotModel.stem_img.
destruct (f =? 1); [apply k_forallb_nzl; vm_compute; reflexivity|].
destruct (f =? 2); [apply k_forallb_nzl; vm_compute; reflexivity|].
destruct (f =? 3); apply k_forallb_nzl; vm_compute; reflexivity.
Qed.

Lemma k_stem_nz : forall inp, nzl (SlotModel.n_stem inp).
Proof.
intro inp. unfold SlotModel.n_stem. destruct (SlotModel.n_use_said inp);
[apply k_name_str_nz | apply k_stem_img_nz].
Qed.

Lemma k_w4_nz : forall inp, SlotModel.n_wok inp = true -> nzl (SlotModel.n_W4 inp).
Proof.
intros inp H. destruct (SlotModel.wok_chans inp H) as [Hi Ho].
unfold SlotModel.n_W4. apply k_nzl_app; apply k_dec2_nz; lia.
Qed.

Lemma k_exp_nm_nz : forall inp, SlotModel.n_wok inp = true -> nzl (SlotModel.n_EXP_NM inp).
Proof.
intros inp H. unfold SlotModel.n_EXP_NM. destruct (SlotModel.n_ends_w4 inp); [apply k_stem_nz|].
apply k_nzl_app; [apply k_stem_nz|]. apply k_nzl_app; [|apply k_w4_nz; exact H].
constructor; [unfold nzb, SlotModel.dash, bz, zb; vm_compute; discriminate | constructor].
Qed.

Lemma k_exp_dp_nz : forall inp, SlotModel.n_wok inp = true -> nzl (SlotModel.n_EXP_DP inp).
Proof.
intros inp H. destruct (SlotModel.wok_chans inp H) as [Hi Ho].
assert (A1 : nzl (SlotModel.n_EXP_NM inp)) by (apply k_exp_nm_nz; exact H).
assert (A2 : nzl (SlotModel.str_bytes " ("%string)) by (apply k_forallb_nzl; vm_compute; reflexivity).
assert (A3 : nzl (IdentSpec.DEC (SlotModel.t_in inp) 1)) by (apply k_dec1_nz; lia).
assert (A4 : nzl (SlotModel.str_bytes " in / "%string)) by (apply k_forallb_nzl; vm_compute; reflexivity).
assert (A5 : nzl (IdentSpec.DEC (SlotModel.t_out inp) 1)) by (apply k_dec1_nz; lia).
assert (A6 : nzl (SlotModel.str_bytes " out)"%string)) by (apply k_forallb_nzl; vm_compute; reflexivity).
unfold SlotModel.n_EXP_DP. repeat (apply k_nzl_app; [assumption|]). assumption.
Qed.

(* The token: the name lower-cased, with its first '-' dropped. *)
Lemma k_lower_nz : forall b, nzb b -> nzb (SlotModel.lower b).
Proof.
intros b H. unfold SlotModel.lower. destruct ((65 <=? bz b) && (bz b <=? 90)) eqn:E; [|exact H].
apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
unfold nzb, bz, zb in *. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_small by lia. lia.
Qed.

Lemma k_tok_nz : forall l d, nzl l -> nzl (SlotModel.tok_go d l).
Proof.
induction l as [|b l IH]; intros d H; cbn [SlotModel.tok_go]; [constructor|].
apply Forall_cons_iff in H as [Hb Hl].
destruct (negb d && (bz b =? 45)); [apply IH; exact Hl|].
constructor; [apply k_lower_nz; exact Hb | apply IH; exact Hl].
Qed.

Lemma k_n_tk_nz : forall inp, SlotModel.n_wok inp = true -> nzl (SlotModel.n_TK inp).
Proof. intros inp H. unfold SlotModel.n_TK, SlotModel.TOK. apply k_tok_nz. apply k_exp_nm_nz. exact H. Qed.

(* How the token grows, byte by byte: what the loop checks at each index. *)
Lemma k_tok_app : forall a b d,
SlotModel.tok_go d (a ++ b) =
SlotModel.tok_go d a ++ SlotModel.tok_go (d || SlotModel.has_dash a) b.
Proof.
induction a as [|c a IH]; intros b d.
- cbn [app SlotModel.tok_go SlotModel.has_dash existsb]. rewrite orb_false_r. reflexivity.
- cbn [app SlotModel.tok_go SlotModel.has_dash existsb].
  destruct (Z.eqb_spec (bz c) 45) as [Ec|Ec]; cbn [orb].
  + destruct d; cbn [negb andb app orb]; rewrite (IH b true); cbn [orb]; reflexivity.
  + rewrite andb_false_r. cbn [app]. rewrite (IH b d). reflexivity.
Qed.

Lemma k_has_dash_len : forall l, SlotModel.has_dash l = true -> (1 <= length l)%nat.
Proof. intros [|b l] H; cbn in *; [discriminate | lia]. Qed.

Lemma k_has_dash_cons : forall b l,
SlotModel.has_dash (b :: l) = ((bz b =? 45) || SlotModel.has_dash l)%bool.
Proof. reflexivity. Qed.

Lemma k_tok_len : forall l d,
length (SlotModel.tok_go d l) = (length l - (if d then 0 else if SlotModel.has_dash l then 1 else 0))%nat.
Proof.
induction l as [|b l IH]; intros d.
- cbn [SlotModel.tok_go length]. destruct d; reflexivity.
- cbn [SlotModel.tok_go length]. rewrite k_has_dash_cons.
  destruct (Z.eqb_spec (bz b) 45) as [Eb|Eb]; cbn [orb].
  + destruct d; cbn [negb andb length]; rewrite (IH true); cbn [length]; lia.
  + rewrite andb_false_r. cbn [length]. rewrite (IH d). destruct d; [lia|].
    destruct (SlotModel.has_dash l) eqn:Hd; [pose proof (k_has_dash_len l Hd)|]; lia.
Qed.

Lemma k_n_tk_len : forall inp, Z.of_nat (length (SlotModel.n_TK inp)) = SlotModel.n_lt inp.
Proof.
intro inp. unfold SlotModel.n_TK, SlotModel.TOK, SlotModel.n_lt, SlotModel.n_ln.
rewrite k_tok_len.
destruct (SlotModel.has_dash (SlotModel.n_EXP_NM inp)) eqn:Hd; [pose proof (k_has_dash_len _ Hd)|]; lia.
Qed.

(* r = 0 is the harness's "the name fits and the widths are good" case. *)
Lemma k_r0 : forall inp, SlotModel.n_r inp = 0 ->
SlotModel.n_wok inp = true /\ SlotModel.n_fits inp = true.
Proof.
intros inp H. unfold SlotModel.n_r in H.
destruct (SlotModel.n_wok inp) eqn:Ew; [|cbn in H; discriminate].
destruct (SlotModel.n_fits inp) eqn:Ef; [split; reflexivity | cbn in H; discriminate].
Qed.

Lemma k_fits : forall inp, SlotModel.n_fits inp = true ->
SlotModel.n_ln inp < SlotModel.t_cap_name inp /\
SlotModel.n_lt inp < SlotModel.t_cap_tok inp /\
SlotModel.n_ld inp < SlotModel.t_cap_disp inp.
Proof.
intros inp H. unfold SlotModel.n_fits in H.
apply andb_true_iff in H as [H1 H3]. apply andb_true_iff in H1 as [H1 H2].
apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. auto.
Qed.

(* ---- the two cut points of the walk ----------------------------------------------------------------------- *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* the Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order *)
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ACUT := (@acut fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation HBLOCKS := (@hblocks rc PI B).
#[local] Notation INV_J := (@inv_J_end fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_K := (@inv_K_end fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

(* The three output buffers of the run, as inv_I_end / inv_J_end / inv_K_end name them. *)
Definition k_blocks (g : ectx) (nm tk dp : Z) : list (Z * Z) :=
[(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
 (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
 (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)].

(* 0x81fa0 (BASE + 0x1894): the token loop is done. x18 = &count (SF + V_cnt, 0x81ee8), x21 = tk, x22 = dp,
   x24 = in (0x81efc), x25 = out (0x81ed4); the machine frame still holds the row index, the name buffer, the
   shadow base and the frame pointer. The scope byte of `count` is still poisoned: the tail unpoisons it
   (0x81fa0 sb zero,90(s3)). *)
Definition k_mid (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1894)
(fun ly2 S2 W2 regs2 mem2 md2 =>
HBLOCKS g ly2 S2 (k_blocks g nm tk dp) /\
SlotModel.n_r (e_pl g) = 0 /\
getr regs2 18 = w64 (SFa g pos + V_cnt) /\
getr regs2 21 = w64 tk /\ getr regs2 22 = w64 dp /\
getr regs2 24 = w64 (SlotModel.t_in (e_pl g)) /\
getr regs2 25 = w64 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SlotModel.t_row (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 nm /\
bytes_at8 W2 mem2 dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0])).

(* 0x81f00 (BASE + 0x17f4): the head of the token loop, after j bytes of the expected name have been read,
   t bytes of the token checked and d = "a '-' has been dropped". x10 = x15 = nm + j (0x81ef0, 0x81ef4),
   x12 = t (0x81ee0), x13 = d (0x81edc), x14 = 45 (0x81eec), x6 = the shadow base (0x81ef8). *)
Definition k_loop_at (g : ectx) (pos mf nm tk dp : Z) (j t : nat) (d : bool) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x17f4)
(fun ly2 S2 W2 regs2 mem2 md2 =>
HBLOCKS g ly2 S2 (k_blocks g nm tk dp) /\
SlotModel.n_r (e_pl g) = 0 /\
(j <= length (SlotModel.n_EXP_NM (e_pl g)))%nat /\
t = length (SlotModel.TOK (firstn j (SlotModel.n_EXP_NM (e_pl g)))) /\
d = SlotModel.has_dash (firstn j (SlotModel.n_EXP_NM (e_pl g))) /\
getr regs2 10 = w64 (nm + Z.of_nat j) /\ getr regs2 15 = w64 (nm + Z.of_nat j) /\
getr regs2 12 = w64 (Z.of_nat t) /\ getr regs2 13 = w64 (if d then 1 else 0) /\
getr regs2 14 = w64 45 /\ getr regs2 6 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (SFa g pos + V_cnt) /\
getr regs2 21 = w64 tk /\ getr regs2 22 = w64 dp /\
getr regs2 24 = w64 (SlotModel.t_in (e_pl g)) /\
getr regs2 25 = w64 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SlotModel.t_row (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 nm /\
bytes_at8 W2 mem2 nm (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 tk (SlotModel.n_TK (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0])).

(* 0x81f00 .. 0x81fa0: one byte of the name per iteration. The loop reads nm[j] and, unless it is the first
   '-', tk[t], and aborts when they differ after the lower-casing (0x81f4c); at the NUL it checks that the
   token ends there too (0x81f9c). Both checks hold of the model: tk's bytes are n_TK = TOK (n_EXP_NM).
   A helper lane proves this (file LLVMFuzzerTestOneInput_Ktok.v); it may use every model lemma above
   (k_tok_app is the step law, k_tok_len / k_n_tk_len the length, k_exp_nm_nz / k_n_tk_nz the non-zero bytes)
   and IdentBlkTail.v's blk_tail_present for the wrappers' tail word. *)
Definition k_token_loop_stmt : Prop :=
forall g pos mf nm tk dp j t d W2 c2,
k_loop_at g pos mf nm tk dp j t d W2 c2 ->
SRr SEGS W2 c2 (k_mid g pos mf nm tk dp).

(* 0x81fa0 .. 0x82090: the scope byte and the zeroing of `count`, reac_box_catalogue (count = 11),
   the row at VAL (A_OBJ 27) + 296 * (t_row mod 11), reac_box_catalogue_defect twice, the row's widths at
   +16 / +20, the strcmp of the row's display against dp, the compare of the two masks (0x82084) and the
   re-poisoning of `count` (0x8208c). A helper lane proves this (file LLVMFuzzerTestOneInput_Kcat.v) from the
   contract's HCAT, HCATD, ASTRCMP (lib/Reusable/AStrcmpDef.v) and HIMG's catalogue clause. *)
Definition k_cat_tail_stmt : Prop :=
forall g pos mf nm tk dp W2 c2,
k_mid g pos mf nm tk dp W2 c2 ->
SRr SEGS W2 c2 (INV_K g pos mf nm tk dp).

(* ---- the r = 0 path: the state at the return of each check_str and strcmp ---------------------------------
   kpre ... pc: at slot pc, the journal and the frame of inv_J_end, its blocks and meter, the part of the start
   state's memory mem2 every callee journal keeps (three clauses below), and the callee-saved
   registers K keeps: x18 = nm (0x81e6c), x20 = cap_tok, x21 = tk, x22 = dp, x24 = exp_dp, x26 = exp_nm,
   x27 = r = 0. *)
Definition kpre (g : ectx) (pos mf nm tk dp : Z) (W2 : world SEGS) (mem2 : word -> option byte) (pc : Z)
  : world SEGS -> config -> Prop :=
fun W c => W = W2 /\ exists ly S regs mem md,
c = cfg_at SEGS pc regs mem md /\
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
  ly S W2 mem md (4 * Z.of_nat (m_nrec g) + 7) /\
frames S = [(4, pos)] /\
mo_le MT (e_S g) S ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) /\
mo_ok MT S ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) /\
hblocks B g ly S (k_blocks g nm tk dp) /\
(* the memory a callee's journal keeps (YCbq.v:358-371): the bytes at or above the allocator's ceiling outside
   the callees' window below sp = mf (the machine frame and the saved words), every live heap block's user
   bytes (nm, tk, dp and the input), and the entry's frame and its shadow but the scope byte of `w4` *)
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (mf - check_str.CHECK_STR_STK <= a < mf) ->
  aview SEGS (w_H W2) mem a = aview SEGS (w_H W2) mem2 a) /\
(forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n ->
  aview SEGS (w_H W2) mem (b + i) = aview SEGS (w_H W2) mem2 (b + i)) /\
(forall a, (in_zr a (frame_rng ly (4, pos)) \/ in_zr a (shadow_addr (frame_addr ly 4 pos), fs_frame_bytes 4 / 8)) ->
  ~ (shadow_addr (SFa g pos) + 86 <= a < shadow_addr (SFa g pos) + 87) ->
  aview SEGS (w_H W2) mem a = aview SEGS (w_H W2) mem2 a) /\
getr regs 2 = w64 mf /\ getr regs 9 = w64 mf /\ getr regs 8 = w64 (e_sp0 g) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 19 = w64 (shadow_addr (SFa g pos)) /\ getr regs 18 = w64 nm /\
getr regs 20 = w64 (SlotModel.t_cap_tok (e_pl g)) /\ getr regs 21 = w64 tk /\ getr regs 22 = w64 dp /\
getr regs 24 = w64 (SFa g pos + V_dp) /\ getr regs 26 = w64 (SFa g pos + V_nm) /\ getr regs 27 = w64 0.

(* The r = 0 path 0x81e60 .. 0x81f00 splits at the returns of the three check_str calls:
     k_pairA  0x81e60 (inv_J_end, r = 0) -> 0x81e88 (BASE + 0x177c): the branch, strlen (nm), check_str (nm, cap_name);
     k_pairB  0x81e88 -> 0x81ea0 (BASE + 0x1794): strlen (tk), check_str (tk, cap_tok = x20);
     k_pairC  0x81ea0 -> 0x81eb8 (BASE + 0x17ac): strlen (dp), check_str (dp, cap_disp = mf+144);
     k_cmp    0x81eb8 -> 0x81f00 (k_loop_at, j = t = 0, d = false): strcmp (nm, exp_nm) = 0,
              strcmp (dp, exp_dp) = 0, and the loop's set-up 0x81ed4 .. 0x81efc.
   Each takes inv_J_end of the start state (mem2) for the bytes, shadow and slot values it reads; kpre carries
   what changed. The wrappers' premises for a heap string are LLVMFuzzerTestOneInput_K.v's k_heap_str bundle
   (first_byte, amem_range, range_addressable, shadow_hull_vis, the tail word, the block's bounds); the model
   facts are k_r0 / k_fits (capacities), k_exp_nm_nz / k_exp_dp_nz / k_n_tk_nz (no zero byte), k_n_tk_len. *)
Definition k_pairA_stmt : Prop :=
forall g pos mf nm tk dp W2 regs2 mem2 md2,
INV_J g pos mf nm tk dp W2 (cfg_at SEGS (BASE + 0x1754) regs2 mem2 md2) -> SlotModel.n_r (e_pl g) = 0 ->
SRr SEGS W2 (cfg_at SEGS (BASE + 0x1754) regs2 mem2 md2) (kpre g pos mf nm tk dp W2 mem2 (BASE + 0x177c)).
Definition k_pairB_stmt : Prop :=
forall g pos mf nm tk dp W2 regs2 mem2 md2 W c,
INV_J g pos mf nm tk dp W2 (cfg_at SEGS (BASE + 0x1754) regs2 mem2 md2) -> SlotModel.n_r (e_pl g) = 0 ->
kpre g pos mf nm tk dp W2 mem2 (BASE + 0x177c) W c ->
SRr SEGS W c (kpre g pos mf nm tk dp W2 mem2 (BASE + 0x1794)).
Definition k_pairC_stmt : Prop :=
forall g pos mf nm tk dp W2 regs2 mem2 md2 W c,
INV_J g pos mf nm tk dp W2 (cfg_at SEGS (BASE + 0x1754) regs2 mem2 md2) -> SlotModel.n_r (e_pl g) = 0 ->
kpre g pos mf nm tk dp W2 mem2 (BASE + 0x1794) W c ->
SRr SEGS W c (kpre g pos mf nm tk dp W2 mem2 (BASE + 0x17ac)).
Definition k_cmp_stmt : Prop :=
forall g pos mf nm tk dp W2 regs2 mem2 md2 W c,
INV_J g pos mf nm tk dp W2 (cfg_at SEGS (BASE + 0x1754) regs2 mem2 md2) -> SlotModel.n_r (e_pl g) = 0 ->
kpre g pos mf nm tk dp W2 mem2 (BASE + 0x17ac) W c ->
SRr SEGS W c (k_loop_at g pos mf nm tk dp 0 0 false).
End c.
End b.
End a.
