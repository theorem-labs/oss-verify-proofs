(* The pure part of the walk of is_instance_verb on the ASan+UBSan build of plugin-hostd/fuzz_command
   (fuzz_command.asan-ubsan, image B): the listing offsets and image objects the walk names, the 18 format literals
   g_instance_verbs points to, what cmd_ro_ok gives about them, and the pure steps that turn the two wrappers' values
   into Verbs.verb_is_m (the plain proof's lib/Prog/is_instance_verb.v:103-242 and lib/Prog/VerbsFacts.v, restated
   per pass). The B twin of lib/A/Prog/is_instance_verb_s1.v: every image address is A's moved to B by symbol
   (g_instance_verbs 0xa61a0 -> 0xa5d00, ".str" 0x224c0 -> 0x22500, ".str.56" 0x22d80 -> 0x22dc0, each format
   literal +0x40, checked against B's table words in lib/B/Prog/CmdRo.v RO_g_instance_verbs). The walk itself is
   lib/B/Prog/is_instance_verb.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strcspn_c VerbsFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaShadow PaRun PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdAddr CmdPa CmdPaLib CmdObj CmdRo CmdBase CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the listing offsets this walk names (B: gen/dis/is_instance_verb.s, 0x8e340 + d) ---- *)
Definition IIV_ENTRY : Z := AF_is_instance_verb.          (* 0x8e340 *)
Definition IIV_LOOP : Z := AF_is_instance_verb + 0x6c.      (* 0x8e3ac, the loop header *)
Definition IIV_STEP : Z := AF_is_instance_verb + 0x9c.      (* 0x8e3dc, the step block *)

(* ---- the image objects the walk reads (B: the listing's atoms A_OBJ 126, 92, 120, lib/B/Prog/CmdAddr.v) ---- *)
Definition A_TAB : Z := 0xa5d00.        (* g_instance_verbs, 18 pointers *)
Definition A_SEPS : Z := 0x22500.       (* ".str" = " \t" *)
Definition A_SP : Z := 0x22dc0.         (* ".str.56" = " " *)

Definition iiv_addrs : list Z :=
[0x22520; 0x22a60; 0x22aa0; 0x22ac0; 0x22b00; 0x22b20; 0x22560; 0x22b60; 0x22b80;
 0x22ba0; 0x22be0; 0x22c20; 0x22c60; 0x22ca0; 0x22d00; 0x22d20; 0x22d60; 0x22da0].
Definition iiv_lits : list (list byte) :=
[RO_lit_22520; RO_lit_22a60; RO_lit_22aa0; RO_lit_22ac0; RO_lit_22b00; RO_lit_22b20; RO_lit_22560; RO_lit_22b60;
 RO_lit_22b80; RO_lit_22ba0; RO_lit_22be0; RO_lit_22c20; RO_lit_22c60; RO_lit_22ca0; RO_lit_22d00; RO_lit_22d20;
 RO_lit_22d60; RO_lit_22da0].
Definition iiv_addr (n : nat) : Z := nth n iiv_addrs 0.
Definition iiv_fmt (n : nat) : list byte := nth n Lit.instance_verb_formats [].

(* the ranges the two wrappers' shadow checks read: the two separator strings and the 18 literals *)
Definition iiv_ro_ranges : list (Z * Z) :=
(A_SEPS, 3) :: (A_SP, 2) ::
map (fun p => (fst p, Z.of_nat (length (snd p)))) (combine iiv_addrs iiv_lits).

Lemma iiv_lit_fmt : forall n, (n < 18)%nat -> nth n iiv_lits [] = iiv_fmt n ++ [Z_to_bv 8 0].
Proof.
intros n Hn.
do 18 (destruct n as [|n]; [vm_compute; reflexivity|]). cbn in Hn. lia.
Qed.

Lemma iiv_nz_of_forallb : forall l : list byte,
forallb (fun b : byte => negb (bv_unsigned b =? 0)) l = true -> Forall (fun b : byte => bv_unsigned b <> 0) l.
Proof.
intros l H. apply Forall_forall. intros b Hb. rewrite forallb_forall in H.
specialize (H b Hb). cbv beta in H. apply Bool.negb_true_iff, Z.eqb_neq in H. exact H.
Qed.

Lemma iiv_fmt_nz0 : forall n, (n < 18)%nat -> Forall (fun b : byte => bv_unsigned b <> 0) (iiv_fmt n).
Proof.
intros n Hn.
do 18 (destruct n as [|n]; [apply iiv_nz_of_forallb; vm_compute; reflexivity|]). cbn in Hn. lia.
Qed.

Lemma iiv_fmt_nz : forall n, (n < 18)%nat -> ~ In (Z_to_bv 8 0) (iiv_fmt n).
Proof.
intros n Hn Hin.
exact (proj1 (Forall_forall _ _) (iiv_fmt_nz0 n Hn) _ Hin eq_refl).
Qed.

Lemma iiv_fmt_in : forall n, (n < 18)%nat -> In (iiv_fmt n) Lit.instance_verb_formats.
Proof.
intros n Hn. unfold iiv_fmt. apply nth_In. vm_compute (length Lit.instance_verb_formats). exact Hn.
Qed.

Lemma iiv_len : length Lit.instance_verb_formats = 18%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma iiv_addr_range : forall n, (n < 18)%nat -> 0x10000 <= iiv_addr n /\ iiv_addr n + 128 <= 0x23000.
Proof. intros n Hn. do 18 (destruct n as [|n]; [vm_compute; split; discriminate|]). cbn in Hn. lia. Qed.

Lemma iiv_lit_len : forall n, (n < 18)%nat ->
Z.of_nat (length (iiv_fmt n)) + 1 = Z.of_nat (length (nth n iiv_lits [])).
Proof. intros n Hn. rewrite (iiv_lit_fmt n Hn), length_app. cbn [length]. lia. Qed.

Lemma iiv_range_in : forall n, (n < 18)%nat ->
In (iiv_addr n, Z.of_nat (length (iiv_fmt n)) + 1) iiv_ro_ranges.
Proof.
intros n Hn. unfold iiv_ro_ranges. cbn [map app].
rewrite (iiv_lit_len n Hn). do 2 right.
unfold iiv_addr. do 18 (destruct n as [|n]; [vm_compute; tauto|]). cbn in Hn. lia.
Qed.

Lemma iiv_seps_in : In (A_SEPS, 3) iiv_ro_ranges.
Proof. unfold iiv_ro_ranges. left. reflexivity. Qed.
Lemma iiv_sp_in : In (A_SP, 2) iiv_ro_ranges.
Proof. unfold iiv_ro_ranges. right. left. reflexivity. Qed.

(* ---- the pure step of the loop body: the two wrapper values decide verb_is_m ---- *)
Definition iiv_seps : list byte := map (Z_to_bv 8) [32; 9].
Definition iiv_spl : list byte := map (Z_to_bv 8) [32].

Lemma iiv_cspn_t : forall tb, Z.of_nat (cspn_len iiv_seps tb) = Z.of_nat (length (tfirst tb)).
Proof. intros tb. unfold iiv_seps. rewrite cspn_tfirst. reflexivity. Qed.

Lemma iiv_cspn_f : forall f, Z.of_nat (cspn_len iiv_spl f) = Z.of_nat (length (vfirst f)).
Proof. intros f. unfold iiv_spl. cbn [map]. rewrite cspn_vfirst. reflexivity. Qed.

Lemma iiv_step_ne : forall tb n, (n < 18)%nat ->
length (tfirst tb) <> length (vfirst (iiv_fmt n)) -> verb_is_m tb (iiv_fmt n) = false.
Proof. intros tb n _ H. exact (verb_is_m_len_ne tb (iiv_fmt n) H). Qed.

Lemma iiv_step_eq : forall tb n, (n < 18)%nat ->
Forall (fun b => bv_unsigned b <> 0) tb ->
length (tfirst tb) = length (vfirst (iiv_fmt n)) ->
exists v, StrFun.strncmp_model (tb ++ [Z_to_bv 8 0]) (nth n iiv_lits []) (Z.of_nat (length (tfirst tb))) = Some v
       /\ -256 < v < 256 /\ (v =? 0) = verb_is_m tb (iiv_fmt n).
Proof.
intros tb n Hn Nt Hlen.
rewrite (iiv_lit_fmt n Hn).
pose proof (iiv_fmt_nz0 n Hn) as Nf.
replace (iiv_fmt n ++ [Z_to_bv 8 0]) with (iiv_fmt n ++ Z_to_bv 8 0 :: []) by reflexivity.
rewrite Hlen.
destruct (strncmp_verb tb (iiv_fmt n) [] Nt Nf Hlen) as (v & Hv & Rv & Qv).
exists v. split; [exact Hv | split; [exact Rv | exact Qv]].
Qed.

(* the result the loop reports: the first format that matches, or none *)
Lemma iiv_found : forall tb n, (n < 18)%nat -> verb_is_m tb (iiv_fmt n) = true ->
existsb (verb_is_m tb) Lit.instance_verb_formats = true.
Proof.
intros tb n Hn Hm. apply existsb_exists. exists (iiv_fmt n). split; [exact (iiv_fmt_in n Hn) | exact Hm].
Qed.

Lemma iiv_none : forall tb,
existsb (verb_is_m tb) (firstn 18 Lit.instance_verb_formats) = false ->
existsb (verb_is_m tb) Lit.instance_verb_formats = false.
Proof. intros tb H. rewrite <- (firstn_all Lit.instance_verb_formats), iiv_len. exact H. Qed.

Lemma firstn_S_nth : forall {A} (l : list A) (d : A) n, (n < length l)%nat ->
firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
intros A l d. induction l as [|x l IH]; intros n Hn; [cbn in Hn; lia|].
destruct n as [|n]; cbn [firstn nth length app] in *; [reflexivity|].
rewrite (IH n ltac:(lia)). reflexivity.
Qed.

Lemma iiv_firstn_S : forall tb n, (n < 18)%nat ->
existsb (verb_is_m tb) (firstn n Lit.instance_verb_formats) = false ->
verb_is_m tb (iiv_fmt n) = false ->
existsb (verb_is_m tb) (firstn (S n) Lit.instance_verb_formats) = false.
Proof.
intros tb n Hn HF Hm.
rewrite (firstn_S_nth Lit.instance_verb_formats [] n ltac:(rewrite iiv_len; exact Hn)).
rewrite existsb_app, HF. cbn [existsb orb]. unfold iiv_fmt in Hm. rewrite Hm. reflexivity.
Qed.

(* ---- what cmd_ro_ok gives this walk: the table's 18 words, the two separator strings, the 18 literals and the
   readable word tail after each terminator (the premise musl's word loops need, a Theorem Labs lane's atail_vis) ---- *)
Lemma iiv_ro_facts : forall rd, cmd_ro_ok rd ->
abytes_atR rd A_TAB RO_g_instance_verbs
/\ abytes_atR rd A_SEPS RO_lit_22500
/\ abytes_atR rd A_SP RO_lit_22dc0
/\ (forall n, (n < 18)%nat -> abytes_atR rd (iiv_addr n) (nth n iiv_lits []))
/\ cmd_ro_tails rd.
Proof.
intros rd H. destruct H as [Hb Ht]. unfold cmd_ro_bytes in Hb.
repeat match goal with G : _ /\ _ |- _ => destruct G end.
unfold A_TAB, A_SEPS, A_SP.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [|exact Ht].
intros n Hn. unfold iiv_addr.
do 18 (destruct n as [|n]; [cbn [nth iiv_addrs iiv_lits]; assumption|]). cbn in Hn. lia.
Qed.

Lemma iiv_tab_word : forall rd, abytes_atR rd A_TAB RO_g_instance_verbs ->
forall n, (n < 18)%nat -> aval_mem rd (A_TAB + 8 * Z.of_nat n) 8 (iiv_addr n).
Proof.
intros rd H n Hn k Hk.
replace (A_TAB + 8 * Z.of_nat n + Z.of_nat k) with (A_TAB + Z.of_nat (8 * n + k)) by lia.
rewrite (H (8 * n + k)%nat ltac:(assert (HL : (144 <= length RO_g_instance_verbs)%nat) by (vm_compute; lia); lia)).
f_equal. unfold iiv_addr.
do 18 (destruct n as [|n]; [do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); cbn in Hk; lia|]).
cbn in Hn. lia.
Qed.

Lemma iiv_tail_in : forall n, (n < 18)%nat -> In (iiv_addr n + Z.of_nat (length (iiv_fmt n))) cmd_ro_ends.
Proof.
intros n Hn. unfold iiv_addr, iiv_fmt.
do 18 (destruct n as [|n]; [vm_compute; repeat (first [left; reflexivity | right])|]).
cbn in Hn. lia.
Qed.

Lemma iiv_seps_tail_in : In (A_SEPS + 2) cmd_ro_ends.
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.
Lemma iiv_sp_tail_in : In (A_SP + 1) cmd_ro_ends.
Proof. vm_compute. repeat (first [left; reflexivity | right]). Qed.

Lemma iiv_ends_low : forall e, In e cmd_ro_ends -> 0 <= e < 0x606000.
Proof.
intros e He.
assert (HA : forallb (fun x => (0 <=? x) && (x <? 0x606000)) cmd_ro_ends = true) by (vm_compute; reflexivity).
rewrite forallb_forall in HA. specialize (HA e He). cbv beta in HA.
apply andb_prop in HA as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* The call adapter this walk uses is lib/B/Prog/PaArt.v aj_art_at, with its kept_out transports for the facts the
   walk carries across a call. *)
