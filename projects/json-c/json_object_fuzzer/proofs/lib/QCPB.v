(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz Qrxj QRjH Qpox QsV0 QO3A QBxa Q7m0 QSpR QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 Qpox QsV0 QRjH QO3A QBxa.Mq1 QBxa.Mq3.
Import Q7m0 QSpR.Mq4 QuJV.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition blobs_ev (bl : list (list byte)) : nat -> list byte := fun n => nth n bl [].

Section Drive.
Variable segs : list Segment.

#[using="Type"] Theorem rz_run : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
E M rom R model T,
sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
carry (s_log ss') kn [] = (kn', scs2, hs2) ->
regs_ok E sr R -> know_ok segs E M kn ->
scs_denot segs M E scs -> scs_denot segs M E scs2 ->
m_halted model = None ->
m_vm_lazy model = [] ->
(forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
M' = mem_denot E M (s_log ss') ->
realizes segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
as (R' & HR' & Hlf & Hms).
eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
apply (Hcont R' _ HR'); [|reflexivity].
eapply carry_after; eassumption.
Qed.

Definition kread (kn : list kentry) (b : expr) (k : Z) (n : nat) : option expr :=
match know_lookup segs kn b k n false [] [] with
| LHit v [] _ => Some v
| _ => None
end.

#[using="Type"] Lemma kread_sound : forall E M kn b k n v,
know_ok segs E M kn -> kread kn b k n = Some v -> (1 <= n)%nat -> (n <= 8)%nat ->
flat E (SA b k) (Z.of_nat n) ->
exists bs, rdn segs M (adenot E (SA b k)) n = Some bs /\ length bs = n
/\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E v.
Proof.
intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl. unfold kread in Hr.
pose proof (know_lookup_sound segs E M kn b k n false [] [] Hkn Hn1 Hn8) as Hs.
destruct (know_lookup segs kn b k n false [] []) as [v' scs h|scs h|]; try discriminate.
destruct scs; [|discriminate]. injection Hr as ->.
destruct (Hs ltac:(constructor) Hfl) as (bs & A & B & C). exists bs. unfold extz in C. auto.
Qed.

#[using="Type"] Lemma word_to_le_bytes_of_lez : forall n bs,
length bs = n -> (n <= 8)%nat -> word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
intros n bs Hl Hn. unfold word_to_le_bytes.
pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb.
assert (Hlt : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia.
rewrite <- Hl. apply Z_to_le_bytes_lez.
Qed.

#[using="Type"] Lemma kread_rdn : forall E M kn b k n v,
know_ok segs E M kn -> kread kn b k n = Some v -> (1 <= n)%nat -> (n <= 8)%nat ->
flat E (SA b k) (Z.of_nat n) ->
rdn segs M (adenot E (SA b k)) n = Some (word_to_le_bytes n (edenot E v)).
Proof.
intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl.
destruct (kread_sound E M kn b k n v Hkn Hr Hn1 Hn8 Hfl) as (bs & A & B & C).
rewrite A, <- C, word_to_le_bytes_of_lez by assumption. reflexivity.
Qed.

Fixpoint kblob_find (kn : list kentry) (b : expr) (k : Z) : option (expr * nat) :=
match kn with
| [] => None
| KBlob (SA kb kk) len bk :: rest =>
if (expr_eqb b kb && Z.eqb k kk)%bool then Some (len, bk) else kblob_find rest b k
| _ :: rest => kblob_find rest b k
end.

#[using="Type"] Lemma kblob_find_sound : forall E M kn b k len bk,
know_ok segs E M kn -> kblob_find kn b k = Some (len, bk) ->
kentry_ok segs E M (KBlob (SA b k) len bk).
Proof.
intros E M kn b k len bk Hkn. induction kn as [|K rest IH]; cbn [kblob_find]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| |[kb kk] len' bk'| | | | |]; try (apply IH; assumption).
destruct (expr_eqb b kb && Z.eqb k kk)%bool eqn:Heq; [|apply IH; assumption].
apply andb_prop in Heq as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst.
injection H as <- <-. exact HK.
Qed.

#[using="Type"] Lemma kblob_rdn : forall E M kn b k len bk,
know_ok segs E M kn -> kblob_find kn b k = Some (len, bk) ->
rdn segs M (adenot E (SA b k)) (length (eb E bk)) = Some (eb E bk).
Proof.
intros E M kn b k len bk Hkn Hf.
pose proof (kblob_find_sound E M kn b k len bk Hkn Hf) as HK. cbn [kentry_ok] in HK.
destruct HK as (Hfl & Hlen & Hb).
apply rdn_pointwise.
- reflexivity.
- rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
- intros j Hj. rewrite (flat_u E _ _ Hfl). rewrite Hb by lia. rewrite Nat2Z.id. reflexivity.
Qed.

#[using="Type"] Lemma env_ext_regs : forall vals x ebs sr R,
sr_vars_lt (length vals) sr = true ->
regs_ok (Env (vals_ev vals) ebs) sr R -> regs_ok (Env (vals_ev (vals ++ [x])) ebs) sr R.
Proof. intros. eapply regs_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

#[using="Type"] Lemma env_ext_know : forall vals x ebs M kn,
kn_vars_lt (length vals) kn = true ->
know_ok segs (Env (vals_ev vals) ebs) M kn -> know_ok segs (Env (vals_ev (vals ++ [x])) ebs) M kn.
Proof. intros. eapply know_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

#[using="Type"] Lemma vals_ev_last : forall vals x, vals_ev (vals ++ [x]) (length vals) = x.
Proof. intros. unfold vals_ev. rewrite nth_middle || (rewrite app_nth2, Nat.sub_diag by lia; reflexivity). reflexivity. Qed.

#[using="Type"] Lemma v_addi_pc4 : forall pc, (0 <= pc)%Z -> (pc + 4 < 2 ^ 64)%Z ->
v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4).
Proof. intros pc H0 H1. unfold v_addi. rewrite u_small by lia. reflexivity. Qed.

#[using="Type"] Lemma regs_set_a0 : forall E sr R v e,
regs_ok E sr R -> edenot E e = v -> regs_ok E (sr_upd sr (ridx 10) e) (regupd R 10 v).
Proof. intros. apply regs_ok_set; [assumption | discriminate | assumption]. Qed.

Definition junk_vals (R' : bvmap 5 word) : list word :=
map (fun i => getr R' (Z_to_bv 5 (Z.of_nat i))) (seq 0 32).

Definition sr_after_call_j (sr : list expr) (kept : list nat) (jbase : nat) : list expr :=
map (fun i => if existsb (Nat.eqb i) kept then nth i sr (ELit 0) else EVar (jbase + i))
(seq 0 32).

#[using="Type"] Lemma nth_map_seq_gen : forall {A} (f : nat -> A) len s n d, (n < len)%nat ->
nth n (map f (seq s len)) d = f (s + n)%nat.
Proof.
intros A f len. induction len as [|len IH]; intros s n d H; [lia|].
cbn [seq map]. destruct n as [|n].
- cbn [nth]. rewrite Nat.add_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma nth_map_seq : forall {A} (f : nat -> A) n len d, (n < len)%nat ->
nth n (map f (seq 0 len)) d = f n.
Proof. intros. rewrite nth_map_seq_gen by assumption. reflexivity. Qed.

#[using="Type"] Lemma sr_vars_lt_nth : forall b sr n, sr_vars_lt b sr = true -> expr_vars_lt b (nth n sr (ELit 0)) = true.
Proof.
intros b sr. induction sr as [|e t IH]; intros n H; [destruct n; reflexivity|].
cbn [sr_vars_lt] in H. apply andb_prop in H as [He Ht]. destruct n; [exact He | apply IH; exact Ht].
Qed.

#[using="Type"] Lemma regs_after_call : forall vals ebs sr R R' kept,
sr_vars_lt (length vals) sr = true ->
regs_ok (Env (vals_ev vals) ebs) sr R ->
(forall i, In i kept -> (i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = getr R (Z_to_bv 5 (Z.of_nat i))) ->
~ In 0%nat kept ->
regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sr_after_call_j sr kept (length vals)) R'.
Proof.
intros vals ebs sr R R' kept Hlt HR Hkept H0 r.
pose proof (ridx_range r) as Hr.
unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
- unfold sr_after_call_j. rewrite nth_map_seq by exact Hr.
destruct (existsb (Nat.eqb (ridx r)) kept) eqn:Hex.
+ apply existsb_exists in Hex as (i & Hin & Heqi). apply Nat.eqb_eq in Heqi. subst i.
destruct (Hkept _ Hin) as [_ Hg]. rewrite ridx_roundtrip in Hg. rewrite Hg.
pose proof (HR r) as Hv. unfold sr_get in Hv. rewrite Hr0 in Hv. rewrite Hv.
eapply edenot_agree; [apply vals_app_agree|]. apply sr_vars_lt_nth. exact Hlt.
+ cbn [edenot ev]. unfold vals_ev. rewrite app_nth2 by lia.
replace (length vals + ridx r - length vals)%nat with (ridx r) by lia.
unfold junk_vals. rewrite nth_map_seq by exact Hr. rewrite ridx_roundtrip. reflexivity.
Qed.

End Drive.
End FPGEN1.

End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition sregion : Type := (saddr * Z)%type.

Definition rdenot (E : env) (r : sregion) : word * Z :=
(Z_to_bv 64 (estart E (fst r)), snd r).

Fixpoint entry_covered (rs : list sregion) (a : saddr) (w : nat) : bool :=
match rs with
| [] => false
| (SA rb rk, n) :: rest =>
(expr_eqb (a_base a) rb && Z.leb rk (a_off a) && Z.leb (a_off a + Z.of_nat w) (rk + n))%bool
|| entry_covered rest a w
end.

Fixpoint log_covered (rs : list sregion) (log : list sentry) : bool :=
match log with
| [] => true
| SE a w _ :: rest => entry_covered rs a w && log_covered rs rest
end.

Definition regions_flat (E : env) (rs : list sregion) : Prop :=
forall r, In r rs -> flat E (fst r) (snd r).

#[using="Type"] Lemma entry_covered_in : forall E rs a w (x : word),
entry_covered rs a w = true -> regions_flat E rs -> flat E a (Z.of_nat w) ->
(estart E a <= bv_unsigned x < estart E a + Z.of_nat w)%Z ->
~ outside x (map (rdenot E) rs).
Proof.
intros E rs a w x. induction rs as [|[[rb rk] n] rest IH]; cbn [entry_covered map outside]; intros Hc Hrf Hfa Hx.
- discriminate.
- apply orb_prop in Hc as [Hc|Hc].
+ apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
intros [Hno _]. apply Hno. unfold in_rng, rdenot. cbn [fst snd].
pose proof (Hrf _ (or_introl eq_refl)) as Hfr. cbn [fst snd] in Hfr.
unfold flat, estart in *. cbn [a_base a_off] in *. rewrite <- H1 in *.
rewrite u64_lit by lia. lia.
+ intros [_ Hout]. apply (IH Hc); [| exact Hfa | exact Hx | exact Hout].
intros r Hr. apply Hrf. right. exact Hr.
Qed.

#[using="Type"] Lemma frame_layer : forall E rs m a w (v : word),
entry_covered rs a w = true -> regions_flat E rs -> flat E a (Z.of_nat w) ->
frame_mod m (wbytes m (adenot E a) (word_to_le_bytes w v)) (map (rdenot E) rs).
Proof.
intros E rs m a w v Hc Hrf Hfa.
pose proof (flat_u E a _ Hfa) as Hu.
eapply frame_mod_weaken.
2:{ apply frame_mod_wbytes. rewrite length_N_to_le_bytes, Hu. destruct Hfa as (?&?&?&?). lia. }
intros x Hout. cbn [outside]. split; [|exact I].
intros Hin. unfold in_rng in Hin. rewrite length_N_to_le_bytes, Hu in Hin.
exact (entry_covered_in E rs a w x Hc Hrf Hfa Hin Hout).
Qed.

#[using="Type"] Theorem log_covered_frame : forall E base rs log,
log_covered rs log = true -> regions_flat E rs -> log_flat E log ->
frame_mod base (mem_denot E base log) (map (rdenot E) rs).
Proof.
intros E base rs log. induction log as [|[a w v] rest IH]; cbn [log_covered mem_denot log_flat]; intros Hc Hrf Hlf.
- apply frame_mod_refl.
- apply andb_prop in Hc as [H1 H2]. destruct Hlf as (Hw & Hfa & Hlf').
eapply frame_mod_trans_same; [apply IH; assumption|].
apply frame_layer; assumption.
Qed.

#[using="Type"] Lemma regs_ok_same : forall E sr sr' R R' (r : reg),
regs_ok E sr R -> regs_ok E sr' R' -> sr_get sr' r = sr_get sr r -> getr R' r = getr R r.
Proof. intros E sr sr' R R' r HR HR' Hs. rewrite (HR r), (HR' r), Hs. reflexivity. Qed.

Fixpoint same_regs (sr sr' : list expr) (rs : list reg) : bool :=
match rs with
| [] => true
| r :: rest => expr_eqb (sr_get sr' r) (sr_get sr r) && same_regs sr sr' rest
end.

#[using="Type"] Lemma same_regs_sound : forall E sr sr' R R' rs,
same_regs sr sr' rs = true -> regs_ok E sr R -> regs_ok E sr' R' ->
forall r, In r rs -> getr R' r = getr R r.
Proof.
intros E sr sr' R R' rs. induction rs as [|r0 rest IH]; cbn [same_regs]; intros Hs HR HR' r Hin.
- destruct Hin.
- apply andb_prop in Hs as [H1 H2]. destruct Hin as [<-|Hin].
+ apply (regs_ok_same E sr sr' R R' r0 HR HR'). apply expr_eqb_eq. exact H1.
+ apply IH; assumption.
Qed.

#[using="Type"] Lemma keeps_cs_of_same : forall E sr sr' R R',
same_regs sr sr' callee_saved = true -> regs_ok E sr R -> regs_ok E sr' R' -> keeps_cs R R'.
Proof. intros E sr sr' R R' Hs HR HR' r Hin. eapply same_regs_sound; eassumption. Qed.

#[using="Type"] Theorem run_sound_log : forall segs fuel stops scr pc sr log kn nx ss' scs scr' E base rom regs,
sym_exec segs fuel true stops scr (SS pc sr log kn nx) [] = (ss', scs, scr') ->
regs_ok E sr regs -> log_flat E log -> know_ok segs E base kn ->
scs_denot segs base E scs ->
exists R, regs_ok E (s_regs ss') R
/\ log_flat E (s_log ss')
/\ msteps segs (mkst regs (Z_to_bv 64 pc) (mem_denot E base log) rom)
(mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
intros segs fuel stops scr pc sr log kn nx ss' scs scr' E base rom regs Hex HR Hlf HK Hsc.
eapply sym_exec_ex; [exact Hex | exact Hsc |].
exists regs. cbn [s_pc s_log s_regs s_know].
split; [reflexivity|]. split; [exact HR|]. split; [exact Hlf | exact HK].
Qed.
End FPGEN1.

