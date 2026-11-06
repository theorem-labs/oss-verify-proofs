(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YB1j.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_headamp. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0c YK0e YK0f YK09 YA0c YA0e.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import APC. Import APG. Import APSG.
Definition roundup (x m : Z) : Z := ((x + m - 1) / m) * m.
Definition rounddown (x m : Z) : Z := (x / m) * m.
Definition range_align_fact (k : list kentry) (e : expr) : list kentry :=
let a := Z.min (ealign k e) 12 in
if Z.ltb 0 a then
match xlo k e, xhi k e with
| Some lo, Some hi =>
let m := 2 ^ a in
let lo' := roundup lo m in let hi' := rounddown hi m in
if Z.leb lo' hi' then [KRange e lo' hi'] else []
| _, _ => []
end
else [].
Fixpoint range_align_facts (k : list kentry) (regs : list expr) (args : list expr) : list kentry :=
match args with
| ELit r :: rest =>
(if (Z.leb 0 r && Z.ltb r 32)%bool then range_align_fact k (nth (Z.to_nat r) regs (ELit 0)) else [])
++ range_align_facts k regs rest
| _ => []
end.
Definition xn_range_align (nx0 : nat) (args : list expr) (cs : acs) : option acs :=
let k := kn cs in
match range_align_facts k (s_regs (a_ss cs)) args with
| [] => None
| fs => Some (set_kn cs (fs ++ k))
end.
#[local] Instance rangealign_fx : YK11.FPState := YK11.fx0.
Lemma roundup_ge : forall x m, 0 < m -> x <= roundup x m.
Proof. intros x m Hm. unfold roundup. pose proof (Z_div_mod_eq_full (x + m - 1) m). pose proof (Z.mod_pos_bound (x + m - 1) m Hm). lia. Qed.
Lemma rounddown_le : forall x m, 0 < m -> rounddown x m <= x.
Proof. intros x m Hm. unfold rounddown. pose proof (Z_div_mod_eq_full x m). pose proof (Z.mod_pos_bound x m Hm). lia. Qed.
Lemma multiple_le_rounddown : forall v x m, 0 < m -> (m | v) -> v <= x -> v <= rounddown x m.
Proof.
intros v x m Hm [q Hq] Hle. unfold rounddown. subst v.
assert (Hq' : q <= x / m). { apply Z.div_le_lower_bound; [exact Hm|]. rewrite Z.mul_comm. exact Hle. }
apply Z.mul_le_mono_nonneg_r; [lia | exact Hq'].
Qed.
Lemma multiple_ge_roundup : forall v x m, 0 < m -> (m | v) -> x <= v -> roundup x m <= v.
Proof.
intros v x m Hm [q Hq] Hle. unfold roundup. subst v.
assert (Hq' : (x + m - 1) / m <= q).
{ apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [exact Hm|]. nia. }
apply Z.mul_le_mono_nonneg_r; [lia | exact Hq'].
Qed.
Section b.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variables LIMIT TOP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Lemma range_align_fact_ok : forall E M k e,
know_ok SEGS E M k -> Forall (kentry_ok SEGS E M) (range_align_fact k e).
Proof.
intros E M k e HK. unfold range_align_fact.
destruct (Z.ltb 0 (Z.min (ealign k e) 12)) eqn:Ha; [|constructor]. apply Z.ltb_lt in Ha.
destruct (xlo k e) as [lo|] eqn:Hlo; [|constructor]. destruct (xhi k e) as [hi|] eqn:Hhi; [|constructor].
destruct (Z.leb _ _) eqn:Hle; [|constructor].
constructor; [|constructor]. cbn [kentry_ok].
pose proof (xlo_sound SEGS E M k e lo HK Hlo) as L. pose proof (xhi_sound SEGS E M k e hi HK Hhi) as H.
pose proof (ealign_sound SEGS E M k e HK) as [Arng Adiv].
set (a := Z.min (ealign k e) 12) in *.
assert (Hm : 0 < 2 ^ a) by (apply Z.pow_pos_nonneg; lia).
assert (Hdiv : (2 ^ a | bv_unsigned (edenot E e))).
{ destruct Adiv as [q Hq]. exists (q * 2 ^ (ealign k e - a)). rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
replace (ealign k e - a + a) with (ealign k e) by lia. exact Hq. }
split; [apply multiple_ge_roundup | apply multiple_le_rounddown]; assumption.
Qed.
Lemma range_align_facts_ok : forall E M k regs args,
know_ok SEGS E M k -> Forall (kentry_ok SEGS E M) (range_align_facts k regs args).
Proof.
intros E M k regs args HK. induction args as [|x rest IH]; [constructor|].
cbn [range_align_facts]. destruct x; try constructor.
apply Forall_app. split; [|exact IH].
destruct (Z.leb 0 z && Z.ltb z 32)%bool; [apply range_align_fact_ok; exact HK | constructor].
Qed.
Lemma know_ok_app : forall E M k1 k2, Forall (kentry_ok SEGS E M) k1 -> know_ok SEGS E M k2 -> know_ok SEGS E M (k1 ++ k2).
Proof.
intros E M k1 k2 H1 H2. induction H1 as [|K k1 HK H1 IH]; [exact H2|]. cbn. constructor; [exact HK | exact IH].
Qed.
Theorem xn_range_align_sound : forall args,
node1_stmt SEGS A nx0 LIMIT TOP SINV argH FS0 always (xn_range_align nx0 args).
Proof.
intros args cs cs' E R FULL model T HC _ Hn Hk.
unfold xn_range_align in Hn.
destruct (range_align_facts (kn cs) (s_regs (a_ss cs)) args) as [|f fs] eqn:Hf; [discriminate Hn|].
injection Hn as <-.
assert (HC' : cs_ok SEGS A LIMIT TOP SINV argH FS0 E (set_kn cs ((f :: fs) ++ kn cs)) R FULL model).
{ apply cs_ok_set_kn; [exact HC|]. apply know_ok_app; [| exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)].
rewrite <- Hf. apply range_align_facts_ok. exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC). }
specialize (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' eq_refl).
exact Hk.
Qed.
End b.
