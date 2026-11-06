(* copied from proofs/cgif/cgif_file_fuzzer/lib/YP0c.v (origin/ossv/recipes c8557374ad2e), unrelocated; module paths moved to fuzz_preset lib.Reusable *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d.
Variable psym : Type.
Definition pw_word (e : pinstr psym) : option Z := match e with PW w => Some w | _ => None end.
Definition tw_ins (k : Z) (e : pinstr psym) (t : ctable) : ctable := match pw_word e with Some w => tset (ckey k) w t | None => t end.
Fixpoint tw_from (k : Z) (l : list (pinstr psym)) (t : ctable) : ctable :=
match l with
| [] => t
| e :: l' => tw_from (k + 4) l' (tw_ins k e t)
end.
Definition tw_of (k0 : Z) (l : ptable psym) : ctable := tw_from k0 l TEmpty.
Inductive ptres := PTRun (st : shst) | PTEcall (st : shst) | PTCall (s : psym) (st : shst) | PTStop (why : stop_reason).
Inductive ptrun_status := PTS_running | PTS_ecall | PTS_call (s : psym) | PTS_stopped (why : stop_reason).
Section g.
Variable tpi : ptree psym.
Variable tw : ctable.
Variables (K : nat) (Bx : sv) (Bspan : Z * Z) (SH : list shent).
Definition not_andi_at (L : Z) : bool :=
match dec tw L with
| Some i => match as_andi i with Some _ => false | None => true end
| None => match plookup tpi L with Some (PCall _ _) | Some (PTail _) => true | _ => false end
end.
Definition sh_mem_pi (ss : sstate) (i : instr) : option sstate :=
let G := ss_facts ss in
let R := sr_get (ss_regs ss) in
match i with
| Load sz sg rd rs1 imm =>
let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
match addr_of a with
| Some _ => None
| None =>
match shadow_norm G a with
| Some (b, off) =>
match sload_pi G (ss_mem ss) b off sz sg with
| Some v => Some (setreg ss rd v (ss_pc ss + 4))
| None => None
end
| None => None
end
end
| Store sz rs1 rs2 imm =>
match ss_resv ss with
| Some _ => None
| None =>
let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
match addr_of a with
| Some _ => None
| None =>
match shadow_norm G a with
| Some (b, off) =>
match sstore (ss_mem ss) b off sz (R rs2) with
| Some m' => Some (mkSST (ss_pc ss + 4) (ss_regs ss) (ss_fregs ss) m' None G)
| None => None
end
| None => None
end
end
end
| _ => None
end.
(* the pi runner's step for a prefix word of the generalised slow block (YCbn.sbg_cert): the plain pi step,
   else the shadow-normal memory step, as in sym_step_pi_tok *)
Definition sbg_pi (s : sstate) (i : instr) : option sstate :=
match sym_step_pi tpi s with PRun s' => Some s' | _ => sh_mem_pi s i end.
Definition tok_branch_pi (st : shst) (cnd : branch_cond) (rs1 rs2 : reg) (imm : Z) : option shst :=
let ss := sh_ss st in
let R := sr_get (ss_regs ss) in
if negb (bv_eqb rs2 0) then None else
match ss_resv ss with Some _ => None | None =>
match R rs1 with
| SOff T z0 =>
if negb (z0 =? 0) then None else
match find_tok (sh_toks st) rs1 T with
| None => None
| Some tk =>
let x := tk_x tk in
let pc := ss_pc ss in
let '(Lnz, Lz) := match cnd with
| BC_NE => (zcanon (pc + imm), pc + 4)
| BC_EQ => (pc + 4, zcanon (pc + imm))
| _ => (0, 0) end in
match cnd with
| BC_NE | BC_EQ =>
tb_arms K Bx Bspan SH (sb_cert tw ss x Lnz Lz rs1) (not_andi_at Lnz) (fun _ => sbg_cert tw sbg_pi ss x Lnz Lz rs1) st x rs1 Lz
| _ => None
end
end
| _ => None
end
end.
Definition sym_step_pi_tok (st : shst) : ptres :=
let ss := sh_ss st in
match sym_step_pi tpi ss with
| PRun ss' => PTRun (advance st ss')
| PEcall ss' => PTEcall (advance st ss')
| PCallx s ss' => PTCall s (advance st ss')
| PStop why =>
match dec tw (ss_pc ss) with
| None => PTStop why
| Some i =>
match sh_mem_pi ss i with
| Some ss' => PTRun (advance st ss')
| None =>
match i with
| Load SZ1 sg rd rs1 imm =>
let a := s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm)) in
match tok_load K Bx Bspan SH st sg rd a with Some st' => PTRun st' | None => PTStop why end
| Branch cnd rs1 rs2 imm =>
match plookup tpi (ss_pc ss + bv_signed imm) with
| None => PTStop why
| Some _ =>
match tok_branch_pi st cnd rs1 rs2 (bv_signed imm) with Some st' => PTRun st' | None => PTStop why end
end
| _ => PTStop why
end
end
end
end.
Fixpoint sym_run_pi_tok (fuel : nat) (st : shst) : shst * ptrun_status :=
match fuel with
| O => (st, PTS_running)
| S f => match sym_step_pi_tok st with
| PTRun st' => sym_run_pi_tok f st'
| PTEcall st' => (st', PTS_ecall)
| PTCall s st' => (st', PTS_call s)
| PTStop why => (st, PTS_stopped why)
end
end.
Fixpoint sym_run_to_pi_tok (fuel : nat) (stop_k : Z) (st : shst) : shst * ptrun_status :=
match fuel with
| O => (st, PTS_running)
| S f => if ss_pc (sh_ss st) =? stop_k then (st, PTS_running) else
match sym_step_pi_tok st with
| PTRun st' => sym_run_to_pi_tok f stop_k st'
| PTEcall st' => (st', PTS_ecall)
| PTCall s st' => (st', PTS_call s)
| PTStop why => (st, PTS_stopped why)
end
end.
Definition sym_runN_pi_tok (n : N) (ss : sstate) := sym_run_pi_tok (N.to_nat n) (start K Bx Bspan SH ss).
Definition sym_run_toN_pi_tok (n : N) (stop_k : Z) (ss : sstate) := sym_run_to_pi_tok (N.to_nat n) stop_k (start K Bx Bspan SH ss).
End g.
End d.
Arguments pw_word {psym} _.
Arguments tw_ins {psym} _ _ _.
Arguments tw_from {psym} _ _ _.
Arguments tw_of {psym} _ _.
Arguments PTRun {psym} _.
Arguments PTEcall {psym} _.
Arguments PTCall {psym} _ _.
Arguments PTStop {psym} _.
Arguments PTS_running {psym}.
Arguments PTS_ecall {psym}.
Arguments PTS_call {psym} _.
Arguments PTS_stopped {psym} _.
Arguments not_andi_at {psym} _ _ _.
Arguments sbg_pi {psym} _ _ _.
Arguments tok_branch_pi {psym} _ _ _ _ _ _ _ _ _ _ _.
Arguments sym_step_pi_tok {psym} _ _ _ _ _ _ _.
Arguments sym_run_pi_tok {psym} _ _ _ _ _ _ _ _.
Arguments sym_run_to_pi_tok {psym} _ _ _ _ _ _ _ _ _.
Arguments sym_runN_pi_tok {psym} _ _ _ _ _ _ _ _.
Arguments sym_run_toN_pi_tok {psym} _ _ _ _ _ _ _ _ _.
Section h.
Variable psym : Type.
Lemma tget_tw_ins : forall k (e : pinstr psym) t pc, 0 <= k -> 0 <= pc ->
tget (ckey pc) (tw_ins k e t) = if pc =? k then match pw_word e with Some w => Some w | None => tget (ckey pc) t end else tget (ckey pc) t.
Proof.
intros k e t pc Hk Hpc. unfold tw_ins. destruct (Z.eqb_spec pc k) as [->|Hne].
- destruct (pw_word e); [apply tget_tset_same | reflexivity].
- destruct (pw_word e); [|reflexivity]. rewrite tget_tset_other; [reflexivity|]. intros Heq. apply ckey_inj in Heq; lia.
Qed.
Lemma tw_from_spec : forall (l : list (pinstr psym)) k0 t pc,
0 <= k0 -> k0 mod 4 = 0 -> 0 <= pc ->
tget (ckey pc) (tw_from k0 l t) =
if ((k0 <=? pc) && ((pc - k0) mod 4 =? 0) && (Z.to_nat ((pc - k0) / 4) <? length l)%nat)%bool
then match nth_error l (Z.to_nat ((pc - k0) / 4)) with Some e => match pw_word e with Some w => Some w | None => tget (ckey pc) t end | None => tget (ckey pc) t end
else tget (ckey pc) t.
Proof.
induction l as [|e l IH]; intros k0 t pc Hk0 Hm Hpc.
- cbn [tw_from length]. replace (Z.to_nat ((pc - k0) / 4) <? 0)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
rewrite andb_false_r. reflexivity.
- cbn [tw_from length].
assert (Hm4 : (k0 + 4) mod 4 = 0) by (rewrite <- Zplus_mod_idemp_l, Hm; reflexivity).
rewrite (IH (k0 + 4) _ pc ltac:(lia) Hm4 Hpc). rewrite tget_tw_ins by lia.
destruct (Z.eqb_spec pc k0) as [->|Hne].
+ replace (k0 + 4 <=? k0) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
rewrite Z.leb_refl, Z.sub_diag. cbn. reflexivity.
+ destruct (Z.leb_spec k0 pc) as [Hle2|Hgt2].
* destruct (Z.leb_spec (k0 + 4) pc) as [Hle|Hgt]; cbn [andb].
-- replace ((pc - (k0 + 4)) mod 4 =? 0) with ((pc - k0) mod 4 =? 0).
2: { replace (pc - k0) with ((pc - (k0 + 4)) + 1 * 4) by lia. rewrite Z.mod_add by lia. reflexivity. }
destruct (Z.eqb_spec ((pc - k0) mod 4) 0) as [Hq|Hq]; cbn [andb]; [|reflexivity].
assert (Hs : Z.to_nat ((pc - k0) / 4) = S (Z.to_nat ((pc - (k0 + 4)) / 4))).
{ replace (pc - k0) with ((pc - (k0 + 4)) + 1 * 4) by lia. rewrite Z.div_add by lia.
assert (0 <= (pc - (k0 + 4)) / 4) by (apply Z.div_pos; lia). lia. }
rewrite Hs. reflexivity.
-- replace ((pc - k0) mod 4 =? 0) with false; [reflexivity|]. symmetry. apply Z.eqb_neq. rewrite Z.mod_small by lia. lia.
* replace (k0 + 4 <=? pc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.
Lemma tw_of_lookup : forall (l : ptable psym) k0 k,
0 <= k0 -> k0 mod 4 = 0 ->
clookup (tw_of k0 l) (k0 + k) =
if ((0 <=? k) && (k mod 4 =? 0))%bool then match nth_error l (Z.to_nat (k / 4)) with Some e => pw_word e | None => None end else None.
Proof.
intros l k0 k Hk0 Hm. unfold clookup, tw_of.
destruct (Z.leb_spec 0 (k0 + k)) as [Hge|Hlt].
- rewrite tw_from_spec by lia. replace (k0 + k - k0) with k by lia.
destruct (Z.leb_spec 0 k) as [Hk|Hk]; [|replace (k0 <=? k0 + k) with false by (symmetry; apply Z.leb_gt; lia); cbn; destruct (ckey (k0 + k)); reflexivity].
replace (k0 <=? k0 + k) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
destruct (k mod 4 =? 0); [|cbn; destruct (ckey (k0 + k)); reflexivity].
destruct (Nat.ltb_spec (Z.to_nat (k / 4)) (length l)) as [Hl|Hl].
+ destruct (nth_error l (Z.to_nat (k / 4))) as [e|] eqn:Hn; [|exfalso; apply nth_error_None in Hn; lia].
destruct (pw_word e); [reflexivity|]. destruct (ckey (k0 + k)); reflexivity.
+ rewrite (proj2 (nth_error_None l (Z.to_nat (k / 4)))) by lia. destruct (ckey (k0 + k)); reflexivity.
- replace (0 <=? k) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.
Lemma tw_shift : forall (l : ptable psym) B k, 0 <= B -> B mod 4 = 0 ->
clookup (tw_of B l) (B + k) = clookup (tw_of 0 l) k.
Proof.
intros l B k HB HBm. replace (clookup (tw_of 0 l) k) with (clookup (tw_of 0 l) (0 + k)) by (rewrite Z.add_0_l; reflexivity).
rewrite !tw_of_lookup by lia. reflexivity.
Qed.
Lemma dec_shift : forall (l : ptable psym) B k, 0 <= B -> B mod 4 = 0 ->
dec (tw_of B l) (B + k) = dec (tw_of 0 l) k.
Proof. intros l B k HB HBm. unfold dec. rewrite tw_shift by assumption. reflexivity. Qed.
Lemma tw_of_plookup : forall (l : ptable psym) k w,
clookup (tw_of 0 l) k = Some w -> plookup (ptree_of_list l) k = Some (PW w) /\ 0 <= k < 4 * Z.of_nat (length l).
Proof.
intros l k w H. rewrite <- (Z.add_0_l k) in H. rewrite tw_of_lookup in H by lia.
destruct ((0 <=? k) && (k mod 4 =? 0))%bool eqn:Hg; [|discriminate H]. apply andb_prop in Hg as [H0 H4]. apply Z.leb_le in H0. apply Z.eqb_eq in H4.
destruct (nth_error l (Z.to_nat (k / 4))) as [e|] eqn:Hn; [|discriminate H].
assert (Hlt : (Z.to_nat (k / 4) < length l)%nat) by (apply (proj1 (nth_error_Some l _)); rewrite Hn; discriminate).
split.
- unfold plookup. replace ((0 <=? k) && (k mod 4 =? 0))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.eqb_eq; exact H4]).
unfold ptree_of_list, pkey. rewrite (ptree_from_spec psym) by lia.
replace (Z.pos (Z.to_pos (k / 4 + 1)) - 1) with (k / 4) by (pose proof (Z.div_pos k 4 ltac:(lia) ltac:(lia)); lia).
replace (k / 4 <? 0) with false by (symmetry; apply Z.ltb_ge; apply Z.div_pos; lia). rewrite Z.sub_0_r, Hn.
destruct e; cbn [pw_word] in H; try discriminate H. injection H as ->. reflexivity.
- pose proof (Z.div_mod k 4 ltac:(lia)) as Hd. rewrite H4 in Hd. split; [lia|]. apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by (apply Z.div_pos; lia). lia.
Qed.
End h.
Section m.
Variable psym : Type.
Variable segs : list Segment.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Context {fx : FPState}.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Variable A_LIM : nat.
Hypothesis HLIM0 : (A_TEXT < A_LIM)%nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
Hypothesis HLEN : 4 * Z.of_nat (length listing) <= 2 ^ 40.
Variables (K : nat) (Bx : sv) (Bspan : Z * Z) (SH : list shent).
Hypothesis HK : (A_LIM <= K)%nat.
#[local] Notation tpi := (ptree_of_list listing).
#[local] Notation B := (val A_TEXT).
#[local] Notation tw := (tw_of 0 listing).
#[local] Notation tB := (tw_of B listing).
#[local] Notation img_env := (img_env val A_LIM).
#[local] Notation abs_ss := (abs_ss val).
#[local] Notation st_ok_pi := (st_ok_pi segs val).
#[local] Notation INV := (INV segs K Bx Bspan SH).
#[local] Notation sym_step_pi_tok := (sym_step_pi_tok tpi tw K Bx Bspan SH).
#[local] Notation tok_branch_piN := (tok_branch_pi tpi tw K Bx Bspan SH).
#[local] Notation not_andi_atN := (not_andi_at tpi tw).
#[local] Notation sbg_piN := (sbg_pi tpi).
Definition abs_sh (st : shst) : shst := mkSH (abs_ss (sh_ss st)) (sh_j st) (sh_toks st) (sh_chk st) (sh_obls st).
Lemma tB_ok : table_ok segs tB.
Proof.
intros pc w Hl. pose proof HB as (HB0 & _ & HB4).
replace pc with (B + (pc - B)) in Hl |- * by lia. rewrite (tw_shift psym listing B (pc - B) HB0 HB4) in Hl.
destruct (tw_of_plookup psym listing _ _ Hl) as [Hp Hr].
pose proof (cert_slot psym fetch val sigma listing Hcert _ _ Hp) as (Hck & _ & _). unfold pi_slot_check in Hck.
destruct (fetch (B + (pc - B))) as [wz|] eqn:Hfw; [|discriminate Hck]. apply Z.eqb_eq in Hck. subst wz. exact (Hfetch _ _ Hfw).
Qed.
Lemma img_env_ewset : forall E T v, img_env E -> (K <= T)%nat -> img_env (ewset E T v).
Proof. intros E T v HE HT a Ha. rewrite ew_ewset_other by lia. exact (HE a Ha). Qed.
Lemma advance_abs : forall st ss', advance (abs_sh st) (abs_ss ss') = abs_sh (advance st ss').
Proof. intros [ss j toks chk obls] ss'. reflexivity. Qed.
Lemma tok_load_abs : forall st sg rd a st',
tok_load K Bx Bspan SH st sg rd a = Some st' ->
tok_load K Bx Bspan SH (abs_sh st) sg rd a = Some (abs_sh st').
Proof.
intros [ss j toks chk obls] sg rd a st' H. unfold tok_load in H |- *. cbn [sh_ss sh_j sh_toks sh_chk sh_obls abs_sh] in *.
cbn [ss_facts ss_resv ss_regs ss_mem ss_pc YP0d.abs_ss setpc] in *.
destruct (bv_eqb rd 0); [discriminate H|].
destruct (match_x Bx a) as [x|]; [|discriminate H].
destruct chk; [|discriminate H]. cbn [negb] in *.
destruct ss as [pc sr fr sm rv G]; cbn [ss_facts ss_resv ss_regs ss_mem ss_pc setpc] in *.
destruct rv; [discriminate H|].
destruct (covered SH x 8).
- injection H as <-.
unfold abs_sh, YP0d.abs_ss, setreg, setpc, prune, tok_live; cbn [sh_ss sh_j sh_toks sh_chk sh_obls ss_regs ss_pc ss_fregs ss_mem ss_resv ss_facts].
f_equal. f_equal. f_equal. lia.
- unfold YP0d.abs_ss, setpc, ss_atoms_lt in *. cbn [ss_regs ss_mem ss_facts ss_pc ss_fregs ss_resv] in *.
match type of H with (if ?c then _ else _) = _ => destruct c; [discriminate H|] end.
destruct (need K Bx Bspan SH G x 1 obls) as [obls'|]; [|discriminate H]. injection H as <-.
unfold abs_sh, YP0d.abs_ss, setreg, setpc, prune, tok_live; cbn [sh_ss sh_j sh_toks sh_chk sh_obls ss_regs ss_pc ss_fregs ss_mem ss_resv ss_facts].
f_equal. f_equal. f_equal. lia.
Qed.
Lemma sh_mem_pi_abs : forall ss i ss',
YCbn.dec tB (B + ss_pc ss) = Some i ->
sh_mem_pi ss i = Some ss' ->
sym_step_sh segs tB (abs_ss ss) = SRun (abs_ss ss').
Proof.
intros ss i ss' Hd H. unfold YCbn.dec in Hd.
destruct (clookup tB (B + ss_pc ss)) as [wz|] eqn:Hlk; [|discriminate Hd].
destruct (is_ecall (Z_to_bv 32 wz)) eqn:Hec; [discriminate Hd|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i' isz]|] eqn:Hdec; [|discriminate Hd].
destruct (isz =? 4) eqn:Hsz; [|discriminate Hd]. injection Hd as ->.
unfold sym_step_sh, sym_step. cbn [ss_pc ss_facts ss_regs ss_mem ss_resv ss_fregs YP0d.abs_ss setpc].
rewrite Hlk. cbv zeta. rewrite Hec, Hdec, Hsz. cbn [negb].
unfold sh_mem_pi in H.
destruct i; try discriminate H.
-
destruct (addr_of _) as [[b0 o0]|] eqn:Hao; [discriminate H|].
destruct (shadow_norm _ _) as [[b off]|] eqn:Hsn; [|discriminate H].
destruct (sload_pi _ _ _ _ _ _) as [v|] eqn:Hsl; [|discriminate H]. injection H as <-.
rewrite (YP0d.sload_pi_sload segs _ _ _ _ _ _ _ Hsl).
unfold setreg, setpc, YP0d.abs_ss; cbn. unfold setpc; cbn. f_equal. f_equal. lia.
-
destruct ss as [pc sr fr sm rv G]; cbn [ss_resv ss_pc ss_facts ss_regs ss_mem ss_fregs] in *.
destruct rv; [discriminate H|].
destruct (addr_of _) as [[b0 o0]|] eqn:Hao; [discriminate H|].
destruct (shadow_norm _ _) as [[b off]|] eqn:Hsn; [|discriminate H].
destruct (sstore _ _ _ _ _) as [m'|] eqn:Hst; [|discriminate H]. injection H as <-.
unfold setpc, YP0d.abs_ss; cbn. unfold setpc; cbn. f_equal. f_equal. lia.
Qed.
Lemma zcanon_shift_eqb : forall u v, (zcanon (B + u) =? zcanon (B + v)) = (zcanon u =? zcanon v).
Proof.
intros u v. unfold zcanon.
destruct (Z.eqb_spec (u mod M64) (v mod M64)) as [Heq|Hne]; destruct (Z.eqb_spec ((B + u) mod M64) ((B + v) mod M64)) as [Heq2|Hne2]; try reflexivity; exfalso.
- apply Hne2. rewrite <- Zplus_mod_idemp_r, Heq, Zplus_mod_idemp_r. reflexivity.
- apply Hne. apply (f_equal (fun x => (x + (M64 - B mod M64)) mod M64)) in Heq2.
rewrite !Zplus_mod_idemp_l in Heq2.
replace (B + u + (M64 - B mod M64)) with (u + (B - B mod M64) + 1 * M64) in Heq2 by lia.
replace (B + v + (M64 - B mod M64)) with (v + (B - B mod M64) + 1 * M64) in Heq2 by lia.
rewrite !Z.mod_add in Heq2 by (unfold M64; lia).
pose proof (Z.div_mod B M64 ltac:(unfold M64; lia)) as Hd.
replace (B - B mod M64) with (B / M64 * M64) in Heq2 by lia. rewrite !Z.mod_add in Heq2 by (unfold M64; lia). exact Heq2.
Qed.
Lemma dec_tw_range : forall x i, dec tw x = Some i -> 0 <= x < 2 ^ 40.
Proof.
intros x i H. unfold dec in H. destruct (clookup tw x) as [w|] eqn:Hl; [|discriminate H].
destruct (tw_of_plookup psym listing x w Hl) as [_ Hr]. lia.
Qed.
Lemma zcanon_small : forall x, 0 <= x < 2 ^ 40 -> zcanon x = x.
Proof. intros x Hx. unfold zcanon, M64. apply Z.mod_small. lia. Qed.
Lemma zcanon_back : forall x, 0 <= zcanon x < 2 ^ 40 -> - 2 ^ 63 <= x < 2 ^ 63 -> zcanon x = x.
Proof.
intros x Hz Hx. unfold zcanon, M64 in *.
destruct (Z.leb_spec 0 x) as [H0|H0]; [apply Z.mod_small; lia|].
exfalso. replace x with ((x + 2 ^ 64) + (-1) * 2 ^ 64) in Hz by lia. rewrite Z.mod_add, Z.mod_small in Hz by lia. lia.
Qed.
Lemma slow_block_shift_eq : forall L Lz t,
slow_block tB (B + L) (B + Lz) t = slow_block tw L Lz t.
Proof.
intros L Lz t. pose proof HB as (HB0 & HB1 & HB4). unfold slow_block, decp.
rewrite <- !(Z.add_assoc B). rewrite !(dec_shift psym listing B _ HB0 HB4).
destruct (dec tw L) as [i|]; [|reflexivity]. destruct (as_andi i) as [[[u xr] i7]|]; [|reflexivity].
destruct (negb (i7 =? 7) || bv_eqb u 0 || bv_eqb u t)%bool; [reflexivity|].
destruct (dec tw (L + 4)) as [i0|]; [destruct (as_addi i0) as [[[u1 u2] k]|]; [destruct (bv_eqb u1 u && bv_eqb u2 u)%bool|] |].
all: cbv beta iota zeta.
all: rewrite <- ?(Z.add_assoc B); rewrite ?(dec_shift psym listing B _ HB0 HB4).
all: match goal with |- context [if negb ?c then _ else _] => destruct (negb c); [reflexivity|] end.
all: match goal with |- context [match dec tw ?L2 with _ => _ end] => destruct (dec tw L2) as [ib|]; [destruct (as_branch ib) as [[[[c r1] r2] off]|]; [destruct c|] |] end; try reflexivity.
all: try match goal with |- context [if (bv_eqb ?r1 ?u && bv_eqb ?r2 ?t)%bool then _ else _] => destruct (bv_eqb r1 u && bv_eqb r2 t)%bool; [|reflexivity] end.
all: rewrite <- ?(Z.add_assoc B), ?zcanon_shift_eqb, ?(dec_shift psym listing B _ HB0 HB4); try reflexivity.
all: match goal with |- context [match dec tw ?L3 with _ => _ end] => destruct (dec tw L3) as [ij|]; [destruct (as_j ij) as [offj|]|] end; try reflexivity.
all: rewrite <- ?(Z.add_assoc B), ?zcanon_shift_eqb; reflexivity.
Qed.
(* The four arms of tok_branch commute with abs_sh (they never read the pc). *)
Lemma tb_slow_abs : forall st x u k Lz,
tb_slow K Bx Bspan SH (abs_sh st) x u k (B + Lz) = option_map abs_sh (tb_slow K Bx Bspan SH st x u k Lz).
Proof.
intros [[pc sr fr sm rv G] j toks chk obls] x u k Lz.
unfold tb_slow, abs_sh, YP0d.abs_ss, setpc.
cbn [sh_ss sh_j sh_toks sh_chk sh_obls ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
change (ss_atoms_lt (K + j) (mkSST (B + pc) sr fr sm rv G)) with (ss_atoms_lt (K + j) (mkSST pc sr fr sm rv G)).
destruct (negb (ss_atoms_lt (K + j) (mkSST pc sr fr sm rv G))); [reflexivity|].
destruct (need K Bx Bspan SH G x (k + 1) obls) as [o|]; [|reflexivity].
cbn [option_map]. unfold abs_sh, YP0d.abs_ss, setreg, setpc, prune, tok_live; cbn. reflexivity.
Qed.
Lemma tb_forma_abs : forall ok st x rs1 Lz,
tb_forma K Bx Bspan SH ok (abs_sh st) x rs1 (B + Lz) = option_map abs_sh (tb_forma K Bx Bspan SH ok st x rs1 Lz).
Proof.
intros ok [[pc sr fr sm rv G] j toks chk obls] x rs1 Lz.
unfold tb_forma, abs_sh, YP0d.abs_ss, setpc.
cbn [sh_ss sh_j sh_toks sh_chk sh_obls ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
destruct (negb ok); [reflexivity|].
destruct (need K Bx Bspan SH G (gran G x) 8 obls) as [o|]; [|reflexivity].
cbn [option_map]. unfold abs_sh, YP0d.abs_ss, setreg, setpc, prune, tok_live; cbn. reflexivity.
Qed.
Lemma tb_cs_abs : forall c st x Lz,
tb_cs K Bx Bspan SH c (abs_sh st) x (B + Lz) = option_map abs_sh (tb_cs K Bx Bspan SH c st x Lz).
Proof. intros [[u k]|] st x Lz; unfold tb_cs; [exact (tb_slow_abs st x u k Lz) | reflexivity]. Qed.
Lemma tb_fa_abs : forall ok st x rs1 Lz,
tb_fa K Bx Bspan SH ok (abs_sh st) x rs1 (B + Lz) = option_map abs_sh (tb_fa K Bx Bspan SH ok st x rs1 Lz).
Proof.
intros ok st x rs1 Lz. unfold tb_fa.
change (ss_facts (sh_ss (abs_sh st))) with (ss_facts (sh_ss st)).
destruct (covered SH (gran (ss_facts (sh_ss st)) x) 8); [exact (tb_forma_abs ok st x rs1 Lz) | reflexivity].
Qed.
Lemma sb_cert_abs : forall ss x L Lz t, sb_cert tB (abs_ss ss) x (B + L) (B + Lz) t = sb_cert tw ss x L Lz t.
Proof. intros ss x L Lz t. unfold sb_cert. rewrite slow_block_shift_eq. reflexivity. Qed.
Lemma not_andi_abs : forall L i, dec tw L = Some i -> not_andi tB (B + L) = not_andi_atN L.
Proof.
intros L i Hd. pose proof HB as (HB0 & _ & HB4). unfold not_andi, not_andi_at.
rewrite (dec_shift psym listing B L HB0 HB4), Hd. reflexivity.
Qed.
(* The generalised slow block at relative pcs (table tw) and at absolute pcs (table tB). *)
Lemma decp_shift : forall {A} (f : instr -> option A) L, decp tB f (B + L) = decp tw f L.
Proof. intros A f L. pose proof HB as (HB0 & _ & HB4). unfold decp. rewrite (dec_shift psym listing B L HB0 HB4). reflexivity. Qed.
Lemma sbg_tail_shift : forall L Lz t, sbg_tail tB (B + L) (B + Lz) t = sbg_tail tw L Lz t.
Proof.
intros L Lz t. unfold sbg_tail. rewrite decp_shift.
destruct (decp tw as_branch L) as [[[[c u] r2] off]|]; [|reflexivity].
destruct c; try reflexivity.
- rewrite <- (Z.add_assoc B L off), zcanon_shift_eqb. reflexivity.
- destruct (bv_eqb r2 t); [|reflexivity].
rewrite <- (Z.add_assoc B L 4), decp_shift.
destruct (decp tw as_j (L + 4)) as [offj|]; [|reflexivity].
rewrite <- (Z.add_assoc B (L + 4) offj), zcanon_shift_eqb. reflexivity.
Qed.
Lemma sbg_scan_shift : forall n L Lz t u m L2, sbg_scan tw n L Lz t = Some (u, m, L2) ->
sbg_scan tB n (B + L) (B + Lz) t = Some (u, m, B + L2).
Proof.
induction n as [|n IH]; intros L Lz t u m L2 H; cbn [sbg_scan] in H |- *; [discriminate H|].
rewrite decp_shift, <- (Z.add_assoc B L 4), sbg_tail_shift.
destruct (decp tw sbg_rd L) as [rd|]; [|discriminate H].
destruct (sbg_tail tw (L + 4) Lz t) as [u1|].
- destruct (bv_eqb rd u1); [|discriminate H]. injection H as <- <- <-. reflexivity.
- destruct (sbg_scan tw n (L + 4) Lz t) as [[[u1 m1] L3]|] eqn:Hs; [|discriminate H].
rewrite (IH _ _ _ _ _ _ Hs). destruct (bv_eqb rd u1); [|discriminate H]. injection H as <- <- <-. reflexivity.
Qed.
Lemma sbg_gen_shift : forall L Lz t u m L2, sbg_gen tw L Lz t = Some (u, m, L2) ->
sbg_gen tB (B + L) (B + Lz) t = Some (u, m, B + L2).
Proof.
intros L Lz t u m L2 H. unfold sbg_gen in H |- *.
destruct (sbg_scan tw 4 L Lz t) as [[[u1 m1] L3]|] eqn:Hs; [|discriminate H].
rewrite (sbg_scan_shift _ _ _ _ _ _ _ Hs).
destruct (bv_eqb u1 0 || bv_eqb u1 t); [discriminate H|]. injection H as <- <- <-. reflexivity.
Qed.
Lemma sbg_run_abs : forall (step1 step2 : sstate -> option sstate),
(forall s s', step1 s = Some s' -> step2 (abs_ss s) = Some (abs_ss s')) ->
forall m s s1, sbg_run step1 m s = Some s1 -> sbg_run step2 m (abs_ss s) = Some (abs_ss s1).
Proof.
intros step1 step2 Hst. induction m as [|m IH]; intros s s1 H; cbn [sbg_run] in H |- *.
- injection H as <-. reflexivity.
- destruct (step1 s) as [s'|] eqn:Hs; [|discriminate H]. rewrite (Hst _ _ Hs). exact (IH _ _ H).
Qed.
Lemma sym_step_tbl : forall t1 t2 s, clookup t1 (ss_pc s) = clookup t2 (ss_pc s) -> sym_step segs t1 s = sym_step segs t2 s.
Proof. intros t1 t2 s H. unfold sym_step. cbv zeta. rewrite H. reflexivity. Qed.
(* A prefix step of the pi runner is the absolute runner's sym_step_sh step (pw_plain_step for a plain word,
   sh_mem_pi_abs for a shadow-normal load), so the prefix Load's read is discharged by sym_step_sh_soundP. *)
Lemma sbg_step_abs : forall u s s', sbg_step tw sbg_piN u s = Some s' ->
sbg_step tB (sbg_sh segs tB) u (abs_ss s) = Some (abs_ss s').
Proof.
intros u s s' H. pose proof HB as (HB0 & HB1 & HB4).
unfold sbg_step in H |- *. change (ss_pc (abs_ss s)) with (B + ss_pc s).
rewrite (dec_shift psym listing B _ HB0 HB4).
destruct (dec tw (ss_pc s)) as [i|] eqn:Hd; [|discriminate H].
destruct (sbg_rd i) as [rd|] eqn:Hrd; [|discriminate H].
destruct (bv_eqb rd u); [|discriminate H].
pose proof (dec_tw_range _ _ Hd) as Hk.
assert (Hd' : dec tB (B + ss_pc s) = Some i) by (rewrite (dec_shift psym listing B _ HB0 HB4); exact Hd).
unfold sbg_pi in H. unfold sbg_sh.
destruct (sym_step_pi tpi s) as [s1|s1|sy s1|why] eqn:Hs.
2, 3, 4: rewrite (sh_mem_pi_abs s i s' Hd' H); reflexivity.
injection H as <-.
unfold dec in Hd. destruct (clookup tw (ss_pc s)) as [wz|] eqn:Hl; [|discriminate Hd].
destruct (is_ecall (Z_to_bv 32 wz)) eqn:Hec; [discriminate Hd|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i0 isz]|] eqn:Hdc; [|discriminate Hd].
destruct (isz =? 4) eqn:Hsz; [|discriminate Hd]. injection Hd as <-. apply Z.eqb_eq in Hsz. subst isz.
destruct (tw_of_plookup psym listing _ _ Hl) as [Hpl _].
assert (Hplain : plain_instr i0 = true) by (destruct i0; try discriminate Hrd; reflexivity).
destruct (pw_plain_step psym segs fetch val sigma listing Hcert (conj HB0 HB1) s s1 wz i0 Hpl Hdc Hec Hplain Hs)
as (ss1 & Hst & R1 & R2 & R3 & R4 & R5 & R6).
assert (Hst' : sym_step segs tB (abs_ss s) = SRun ss1).
{ rewrite <- Hst. apply sym_step_tbl. change (ss_pc (abs_ss s)) with (B + ss_pc s).
rewrite tbl1_lookup by lia. rewrite (tw_shift psym listing B _ HB0 HB4). exact Hl. }
unfold sym_step_sh. rewrite Hst'. cbv beta iota. f_equal.
destruct ss1 as [p1 r1 f1 m1 v1 g1], s1 as [p2 r2 f2 m2 v2 g2]; cbn [ss_regs ss_mem ss_resv ss_facts ss_fregs ss_pc] in *.
unfold YP0d.abs_ss, setpc; cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts]. subst. reflexivity.
Qed.
Lemma sbg_cert_abs : forall ss x Lnz Lz t u k,
sbg_cert tw sbg_piN ss x Lnz Lz t = Some (u, k) ->
sbg_cert tB (sbg_sh segs tB) (abs_ss ss) x (B + Lnz) (B + Lz) t = Some (u, k).
Proof.
intros ss x Lnz Lz t u k H. unfold sbg_cert in H |- *.
destruct (sbg_gen tw Lnz Lz t) as [[[u1 m] L2]|] eqn:Hg; [|discriminate H].
rewrite (sbg_gen_shift _ _ _ _ _ _ Hg).
destruct (sbg_run (sbg_step tw sbg_piN u1) m (setpc ss Lnz)) as [ss1|] eqn:Hr; [|discriminate H].
replace (setpc (abs_ss ss) (B + Lnz)) with (abs_ss (setpc ss Lnz)) by reflexivity.
rewrite (sbg_run_abs _ _ (sbg_step_abs u1) m _ _ Hr).
change (ss_pc (abs_ss ss1)) with (B + ss_pc ss1). change (ss_facts (abs_ss ss)) with (ss_facts ss).
change (ss_regs (abs_ss ss1)) with (ss_regs ss1).
replace (B + ss_pc ss1 =? B + L2) with (ss_pc ss1 =? L2)
by (destruct (Z.eqb_spec (ss_pc ss1) L2), (Z.eqb_spec (B + ss_pc ss1) (B + L2)); first [reflexivity | exfalso; lia]).
exact H.
Qed.
Lemma tbl1_other : forall p w q, 0 <= p -> 0 <= q -> q <> p -> clookup (tbl1 p w) q = None.
Proof.
intros p w q Hp Hq Hne. unfold clookup, tbl1. replace (0 <=? q) with true by (symmetry; apply Z.leb_le; lia).
rewrite tget_tset_other; [destruct (ckey q); reflexivity|]. intros Heq. apply ckey_inj in Heq; lia.
Qed.
Lemma tok_branch_pi_abs : forall st cnd rs1 rs2 imm st',
0 <= ss_pc (sh_ss st) < 2 ^ 40 -> 0 <= ss_pc (sh_ss st) + imm < 2 ^ 40 ->
tok_branch_piN st cnd rs1 rs2 imm = Some st' ->
exists tbl, table_ok segs tbl /\ tok_branch segs tbl K Bx Bspan SH (abs_sh st) cnd rs1 rs2 imm = Some (abs_sh st').
Proof.
intros [ss j toks chk obls] cnd rs1 rs2 imm st' Hpc Htg H. pose proof HB as (HB0 & HB1 & HB4).
unfold tok_branch_pi in H. cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in *.
destruct ss as [pc sr fr sm rv G]. cbn [ss_facts ss_resv ss_regs ss_mem ss_pc ss_fregs] in *.
destruct (negb (bv_eqb rs2 0)) eqn:Hrs2; [discriminate H|].
destruct rv as [rvv|]; [discriminate H|].
destruct (sr_get sr rs1) as [|T z0| | | | | | | | |] eqn:Hrs1; try discriminate H.
destruct (negb (z0 =? 0)) eqn:Hz0; [discriminate H|].
destruct (find_tok toks rs1 T) as [tk|] eqn:Hft; [|discriminate H].
(* arms 1 and 3 run on tB; FORM A (arms 2 and 4) runs on the one-word table at B + Lnz, where arms 1 and 3 fail *)
assert (MAIN : forall Lnz Lz, 0 <= Lnz ->
tb_arms K Bx Bspan SH (sb_cert tw (mkSST pc sr fr sm None G) (tk_x tk) Lnz Lz rs1) (not_andi_atN Lnz)
(fun _ => sbg_cert tw sbg_piN (mkSST pc sr fr sm None G) (tk_x tk) Lnz Lz rs1)
(mkSH (mkSST pc sr fr sm None G) j toks chk obls) (tk_x tk) rs1 Lz = Some st' ->
exists tbl, table_ok segs tbl /\
tb_arms K Bx Bspan SH (sb_cert tbl (abs_ss (mkSST pc sr fr sm None G)) (tk_x tk) (B + Lnz) (B + Lz) rs1)
(not_andi tbl (B + Lnz)) (fun _ => sbg_cert tbl (sbg_sh segs tbl) (abs_ss (mkSST pc sr fr sm None G)) (tk_x tk) (B + Lnz) (B + Lz) rs1)
(abs_sh (mkSH (mkSST pc sr fr sm None G) j toks chk obls)) (tk_x tk) rs1 (B + Lz) = Some (abs_sh st')).
{ intros Lnz Lz HLnz HM.
destruct (tb_arms_cases K Bx Bspan SH _ _ _ _ _ _ _ _ HM)
as [(u & k & Hc1 & Hsl) | [(u & k & Hc3 & Hsl & Ha1 & Ha2) | Hfa]].
- exists tB. split; [exact tB_ok|]. rewrite sb_cert_abs, Hc1.
apply (tb_arms_arm1 K Bx Bspan SH) with (u := u) (k := k); [reflexivity|]. rewrite tb_slow_abs, Hsl. reflexivity.
- exists tB. split; [exact tB_ok|]. cbv beta in Hc3.
assert (Hdi : exists i, dec tw Lnz = Some i).
{ unfold sbg_cert in Hc3. destruct (sbg_gen tw Lnz Lz rs1) as [p|] eqn:Hg; [|discriminate Hc3].
exact (sbg_gen_dec tw Lnz Lz rs1 p Hg). }
destruct Hdi as (i & Hdi).
rewrite sb_cert_abs, (not_andi_abs Lnz i Hdi), (sbg_cert_abs _ _ _ _ _ _ _ Hc3).
apply (tb_arms_arm3 K Bx Bspan SH) with (u := u) (k := k).
+ rewrite tb_cs_abs, Ha1. reflexivity.
+ rewrite tb_fa_abs, Ha2. reflexivity.
+ reflexivity.
+ rewrite tb_slow_abs, Hsl. reflexivity.
- assert (Hok : not_andi_atN Lnz = true).
{ unfold tb_forma in Hfa. destruct (not_andi_atN Lnz); [reflexivity | discriminate Hfa]. }
assert (W : exists wz i', fetch_word segs (Z_to_bv 64 (B + Lnz)) = Some (Z_to_bv 32 wz)
/\ dec (tbl1 (B + Lnz) wz) (B + Lnz) = Some i' /\ as_andi i' = None).
{ unfold not_andi_at in Hok. destruct (dec tw Lnz) as [i|] eqn:Hdi.
+ destruct (as_andi i) eqn:Hai; [discriminate Hok|].
pose proof Hdi as Hdi'. unfold dec in Hdi'. destruct (clookup tw Lnz) as [wz|] eqn:Hl; [|discriminate Hdi'].
exists wz, i. split; [|split; [|exact Hai]].
* apply tB_ok. rewrite (tw_shift psym listing B _ HB0 HB4). exact Hl.
* rewrite <- Hdi. unfold dec. rewrite tbl1_lookup by lia. rewrite Hl. reflexivity.
+ destruct (plookup tpi Lnz) as [e|] eqn:Hpl; [|discriminate Hok].
pose proof (cert_slot psym fetch val sigma listing Hcert _ _ Hpl) as (Hck & _ & _). unfold pi_slot_check in Hck.
destruct (fetch (B + Lnz)) as [wz|] eqn:Hfw; [|discriminate Hck].
assert (JAL : exists rd off, decode_any (Z_to_bv 32 wz) = Some (Jal rd off, 4)).
{ destruct e as [w | s' rd | s' | rd jj | rd rs jj a off | rd rs jj a off sz sg]; try discriminate Hok;
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; try discriminate Hck;
apply andb_prop in Hck as [Hsz Hck]; apply Z.eqb_eq in Hsz; subst isz; destruct i; try discriminate Hck; eexists _, _; reflexivity. }
destruct JAL as (rd & off & Hdec).
exists wz, (Jal rd off). split; [exact (Hfetch _ _ Hfw)|]. split; [|reflexivity].
unfold dec. rewrite tbl1_lookup by lia. rewrite (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)), Hdec. reflexivity. }
destruct W as (wz & i' & Hfw & Hdt & Hai).
exists (tbl1 (B + Lnz) wz). split; [exact (tbl1_ok segs (B + Lnz) wz ltac:(lia) Hfw)|].
assert (SB0 : sb_cert (tbl1 (B + Lnz) wz) (abs_ss (mkSST pc sr fr sm None G)) (tk_x tk) (B + Lnz) (B + Lz) rs1 = None).
{ unfold sb_cert, slow_block, decp. rewrite Hdt. cbv beta iota. rewrite Hai. reflexivity. }
assert (NA : not_andi (tbl1 (B + Lnz) wz) (B + Lnz) = true).
{ unfold not_andi. rewrite Hdt. cbv beta iota. rewrite Hai. reflexivity. }
assert (G0 : sbg_cert (tbl1 (B + Lnz) wz) (sbg_sh segs (tbl1 (B + Lnz) wz)) (abs_ss (mkSST pc sr fr sm None G)) (tk_x tk)
(B + Lnz) (B + Lz) rs1 = None).
{ unfold sbg_cert. rewrite sbg_gen_isolated; [reflexivity|]. unfold dec. rewrite tbl1_other by lia. reflexivity. }
rewrite SB0, NA, G0, tb_arms_forma, tb_forma_abs. rewrite Hok in Hfa. rewrite Hfa. reflexivity. }
destruct cnd; try discriminate H; cbv beta iota zeta in H; unfold tok_branch; cbn [sh_ss sh_j sh_toks sh_chk sh_obls abs_sh];
unfold YP0d.abs_ss, setpc; cbn [ss_facts ss_resv ss_regs ss_mem ss_pc ss_fregs]; rewrite Hrs2, Hrs1, Hz0, Hft; cbv beta iota zeta.
-
rewrite (zcanon_small (pc + imm)) in H by lia. rewrite <- !(Z.add_assoc B).
replace (zcanon (B + (pc + imm))) with (B + (pc + imm)) by (unfold zcanon, M64; rewrite Z.mod_small; lia).
exact (MAIN (pc + 4) (pc + imm) ltac:(lia) H).
-
rewrite (zcanon_small (pc + imm)) in H by lia. rewrite <- !(Z.add_assoc B).
replace (zcanon (B + (pc + imm))) with (B + (pc + imm)) by (unfold zcanon, M64; rewrite Z.mod_small; lia).
exact (MAIN (pc + imm) (pc + 4) ltac:(lia) H).
Qed.
Lemma tok_branch_pi_doml : forall st cnd rs1 rs2 imm st',
0 <= ss_pc (sh_ss st) < 2 ^ 40 -> 0 <= ss_pc (sh_ss st) + imm < 2 ^ 40 ->
tok_branch_piN st cnd rs1 rs2 imm = Some st' -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
intros st cnd rs1 rs2 imm st' Hpc Htg H.
destruct (tok_branch_pi_abs st cnd rs1 rs2 imm st' Hpc Htg H) as (tbl & _ & Ht).
pose proof (tok_branch_doml segs tbl K Bx Bspan SH (abs_sh st) cnd rs1 rs2 imm (abs_sh st') Ht) as D. destruct st, st'; exact D.
Qed.
Lemma plookup_range : forall k e, plookup tpi k = Some e -> 0 <= k < 2 ^ 40.
Proof.
intros k e H. apply plookup_list_of_tree in H. unfold plookup_list in H.
destruct ((k <? 0) || negb (k mod 4 =? 0))%bool eqn:Hg; [discriminate H|].
apply Bool.orb_false_elim in Hg as [Hneg Hmod]. apply Z.ltb_ge in Hneg. apply Bool.negb_false_iff in Hmod. apply Z.eqb_eq in Hmod.
assert (Hlt : (Z.to_nat (k / 4) < length listing)%nat) by (apply (proj1 (nth_error_Some listing _)); rewrite H; discriminate).
apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by (apply Z.div_pos; lia).
pose proof (Z.div_mod k 4 ltac:(lia)) as Hd. rewrite Hmod in Hd. lia.
Qed.
Theorem sym_step_pi_tok_sound : forall final E st st' ms,
img_env E -> INV final E (abs_sh st) ms ->
sym_step_pi_tok st = PTRun st' -> doml (sh_obls st') final ->
exists ms' E',
msteps segs ms ms' /\ INV final E' (abs_sh st') ms' /\ img_env E'
/\ ((sh_j st' = sh_j st /\ E' = E)
\/ (exists v, sh_j st' = S (sh_j st) /\ E' = ewset E (K + sh_j st) v /\ ss_atoms_lt (K + sh_j st) (sh_ss st) = true))
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of E (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
intros final E st st' ms HE HI H Hdom. pose proof HB as (HB0 & HB1 & HB4).
pose proof (proj1 HI) as HS. cbn [sh_ss abs_sh] in HS.
assert (Hpend : ms_svc_pending ms = None) by exact (proj1 (proj2 (proj2 HS))).
assert (Hpc : ms_pc_val ms = Z_to_bv 64 (B + ss_pc (sh_ss st))) by exact (proj1 (proj2 HS)).
unfold sym_step_pi_tok in H.
destruct (sym_step_pi tpi (sh_ss st)) as [ss1 | ss1 | s ss1 | why] eqn:Hs; try discriminate H.
-
injection H as <-.
destruct (YP0d.sym_step_pi_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM E (sh_ss st) ss1 ms HE HS Hs)
as (ms' & Hstep & HS1 & Hfr).
exists ms', E. split; [exact (msteps_one segs ms ms' Hpend Hstep)|].
split; [| split; [exact HE | split; [left; split; [destruct st; reflexivity | reflexivity] | split; [| split; [exact Hfr | destruct st; reflexivity]]]]].
+ rewrite <- advance_abs. apply (advance_sound segs K Bx Bspan SH final E (abs_sh st) (abs_ss ss1) ms ms' HI HS1).
* cbn [sh_ss abs_sh]. exact (sym_step_pi_skeleton psym listing (sh_ss st) ss1 Hs).
* exact Hfr.
+ cbn [sh_ss advance]. exact (sym_step_pi_skeleton psym listing (sh_ss st) ss1 Hs).
-
destruct (dec tw (ss_pc (sh_ss st))) as [i|] eqn:Hd; [|discriminate H].
pose proof Hd as Hd'. rewrite <- (dec_shift psym listing B (ss_pc (sh_ss st)) HB0 HB4) in Hd'.
destruct (YCbn.dec_sound segs tB tB_ok _ _ Hd') as (w & Hf & Hec & Hdec). rewrite <- Hpc in Hf.
pose proof (dec_tw_range _ _ Hd) as Hk.
destruct (sh_mem_pi (sh_ss st) i) as [ss2|] eqn:Hm.
{
injection H as <-.
pose proof (sh_mem_pi_abs (sh_ss st) i ss2 Hd' Hm) as Hsh.
destruct (sym_step_sh_soundP segs tB tB_ok P1_pin P5_pin E (abs_ss (sh_ss st)) (abs_ss ss2) ms
(proj1 (st_ok_P segs E _ ms) HS) Hsh) as (ms' & Hstep & HS1 & Hfr).
apply (proj2 (st_ok_P segs E _ ms')) in HS1.
pose proof (sym_step_sh_skeleton segs tB _ _ Hsh) as Hsk.
unfold YP0d.abs_ss, setpc in Hsk, Hfr. cbn [ss_mem] in Hsk, Hfr.
exists ms', E. split; [exact (msteps_one segs ms ms' Hpend Hstep)|].
split; [| split; [exact HE | split; [left; split; [destruct st; reflexivity | reflexivity] | split; [| split; [exact Hfr | destruct st; reflexivity]]]]].
+ rewrite <- advance_abs. apply (advance_sound segs K Bx Bspan SH final E (abs_sh st) (abs_ss ss2) ms ms' HI HS1).
* cbn [sh_ss abs_sh]. exact Hsk.
* exact Hfr.
+ cbn [sh_ss advance]. exact Hsk. }
destruct i; try discriminate H.
+
destruct (plookup tpi (ss_pc (sh_ss st) + bv_signed imm)) as [e|] eqn:Hpl; [|discriminate H].
pose proof (plookup_range _ _ Hpl) as Htg.
destruct (tok_branch_piN st c rs1 rs2 (bv_signed imm)) as [st1|] eqn:Ht; [|discriminate H]. injection H as <-.
pose proof (tok_branch_pi_doml st c rs1 rs2 (bv_signed imm) st1 Hk Htg Ht) as [_ Hchk].
destruct (tok_branch_pi_abs st c rs1 rs2 (bv_signed imm) st1 Hk Htg Ht) as (tbl & Htbl & Htb).
destruct (tok_branch_sound segs tbl K Bx Bspan SH Htbl final E (abs_sh st) c rs1 rs2 imm (abs_sh st1) ms w HI Hf Hec Hdec Htb Hdom)
as (ms' & E' & Hms & HI' & HE' & Hm1 & Hm2 & Hm3).
exists ms', E'. split; [exact Hms|]. split; [exact HI'|].
cbn [sh_ss sh_j abs_sh] in HE', Hm1, Hm3. unfold YP0d.abs_ss in Hm1. cbn [ss_mem setpc] in Hm1.
split; [destruct HE' as [[_ ->]|(v & _ & -> & _)]; [exact HE | apply img_env_ewset; [exact HE | lia]]|].
split; [exact HE'|]. split; [rewrite Hm1; reflexivity|]. split; [rewrite Hm2; apply frame_of_refl | exact Hchk].
+
destruct sz; try discriminate H.
destruct (tok_load K Bx Bspan SH st signed rd (s_alu2 (ss_facts (sh_ss st)) ALU_ADD (sr_get (ss_regs (sh_ss st)) rs1) (SLit (bv_signed imm)))) as [st1|] eqn:Ht; [|discriminate H].
injection H as <-.
pose proof (tok_load_doml K Bx Bspan SH st signed rd _ st1 Ht) as [_ Hchk].
destruct (tok_load_sound segs K Bx Bspan SH final E (abs_sh st) signed rd rs1 imm (abs_sh st1) ms w HI Hf Hec Hdec
(tok_load_abs st signed rd _ st1 Ht) Hdom) as (ms' & E' & Hstep & HI' & HE' & Hm1 & Hm2 & Hm3).
exists ms', E'. split; [exact (msteps_one segs ms ms' Hpend Hstep)|]. split; [exact HI'|].
cbn [sh_ss sh_j abs_sh] in HE', Hm1, Hm3. unfold YP0d.abs_ss in Hm1. cbn [ss_mem setpc] in Hm1.
split; [destruct HE' as [[_ ->]|(v & _ & -> & _)]; [exact HE | apply img_env_ewset; [exact HE | lia]]|].
split; [exact HE'|]. split; [rewrite Hm1; reflexivity|]. split; [rewrite Hm2; apply frame_of_refl | exact Hchk].
Qed.
Lemma sym_step_pi_no_ecall : forall ss ss1, sym_step_pi tpi ss = PEcall ss1 -> False.
Proof.
intros ss ss1 H. unfold sym_step_pi in H.
destruct (plookup tpi (ss_pc ss)) as [e|]; [|discriminate H]. destruct e; try discriminate H.
all: cbv zeta in H.
all: repeat match type of H with
| context [match ?x with _ => _ end] => destruct x; try discriminate H
| context [if ?b then _ else _] => destruct b; try discriminate H
end.
Qed.
Lemma sym_step_pi_tok_doml : forall st st',
(sym_step_pi_tok st = PTRun st' \/ (exists s, sym_step_pi_tok st = PTCall s st')) ->
doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
intros st st' Hor. unfold sym_step_pi_tok in Hor.
destruct (sym_step_pi tpi (sh_ss st)) as [ss1 | ss1 | s ss1 | why] eqn:Hs.
- destruct Hor as [H|[s H]]; [|discriminate H]. injection H as <-. destruct st; cbn. split; [apply doml_refl | reflexivity].
- exfalso. exact (sym_step_pi_no_ecall _ _ Hs).
- destruct Hor as [H|[s' H]]; [discriminate H|]. injection H as _ <-. destruct st; cbn. split; [apply doml_refl | reflexivity].
- destruct (dec tw (ss_pc (sh_ss st))) as [i|] eqn:Hd; [|destruct Hor as [H|[s H]]; discriminate H].
destruct (sh_mem_pi (sh_ss st) i) as [ss2|] eqn:Hm.
{ destruct Hor as [H|[s H]]; [|discriminate H]. injection H as <-. destruct st; cbn. split; [apply doml_refl | reflexivity]. }
destruct i; try (destruct Hor as [H|[s H]]; discriminate H).
+ destruct (plookup tpi (ss_pc (sh_ss st) + bv_signed imm)) as [e|] eqn:Hpl; [|destruct Hor as [H|[s H]]; discriminate H].
destruct (tok_branch_piN st c rs1 rs2 (bv_signed imm)) as [st1|] eqn:Ht; [|destruct Hor as [H|[s H]]; discriminate H].
destruct Hor as [H|[s H]]; [|discriminate H]. injection H as <-.
exact (tok_branch_pi_doml st c rs1 rs2 _ st1 (dec_tw_range _ _ Hd) (plookup_range _ _ Hpl) Ht).
+ destruct sz; try (destruct Hor as [H|[s H]]; discriminate H).
destruct (tok_load K Bx Bspan SH st signed rd _) as [st1|] eqn:Ht; [|destruct Hor as [H|[s H]]; discriminate H].
destruct Hor as [H|[s H]]; [|discriminate H]. injection H as <-. exact (tok_load_doml K Bx Bspan SH st signed rd _ st1 Ht).
Qed.
Lemma sym_run_pi_tok_doml : forall fuel st st' r,
sym_run_pi_tok tpi tw K Bx Bspan SH fuel st = (st', r) -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros st st' r H; cbn [sym_run_pi_tok] in H.
- injection H as <- <-. split; [apply doml_refl | reflexivity].
- destruct (sym_step_pi_tok st) as [st1 | st1 | s st1 | why] eqn:Hs.
+ destruct (sym_step_pi_tok_doml st st1 (or_introl Hs)) as [D1 C1]. destruct (IH st1 st' r H) as [D2 C2].
split; [eapply doml_trans; [exact D1 | exact D2] | congruence].
+ exfalso. unfold sym_step_pi_tok in Hs. destruct (sym_step_pi tpi (sh_ss st)) as [ss1 | ss1 | s ss1 | why] eqn:Hs'; try discriminate Hs.
* exact (sym_step_pi_no_ecall _ _ Hs').
* destruct (dec tw (ss_pc (sh_ss st))) as [i|]; [|discriminate Hs]. destruct (sh_mem_pi (sh_ss st) i); [discriminate Hs|]. destruct i; try discriminate Hs.
-- destruct (plookup tpi (ss_pc (sh_ss st) + bv_signed imm)); [|discriminate Hs]. destruct (tok_branch_piN st c rs1 rs2 (bv_signed imm)); discriminate Hs.
-- destruct sz; try discriminate Hs. destruct (tok_load K Bx Bspan SH st signed rd _); discriminate Hs.
+ injection H as <- <-. exact (sym_step_pi_tok_doml st st1 (or_intror (ex_intro _ s Hs))).
+ injection H as <- <-. split; [apply doml_refl | reflexivity].
Qed.
Lemma sym_run_to_pi_tok_doml : forall fuel stop st st' r,
sym_run_to_pi_tok tpi tw K Bx Bspan SH fuel stop st = (st', r) -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros stop st st' r H; cbn [sym_run_to_pi_tok] in H.
- injection H as <- <-. split; [apply doml_refl | reflexivity].
- destruct (ss_pc (sh_ss st) =? stop); [injection H as <- <-; split; [apply doml_refl | reflexivity]|].
destruct (sym_step_pi_tok st) as [st1 | st1 | s st1 | why] eqn:Hs.
+ destruct (sym_step_pi_tok_doml st st1 (or_introl Hs)) as [D1 C1]. destruct (IH stop st1 st' r H) as [D2 C2].
split; [eapply doml_trans; [exact D1 | exact D2] | congruence].
+ exfalso. unfold sym_step_pi_tok in Hs. destruct (sym_step_pi tpi (sh_ss st)) as [ss1 | ss1 | s ss1 | why] eqn:Hs'; try discriminate Hs.
* exact (sym_step_pi_no_ecall _ _ Hs').
* destruct (dec tw (ss_pc (sh_ss st))) as [i|]; [|discriminate Hs]. destruct (sh_mem_pi (sh_ss st) i); [discriminate Hs|]. destruct i; try discriminate Hs.
-- destruct (plookup tpi (ss_pc (sh_ss st) + bv_signed imm)); [|discriminate Hs]. destruct (tok_branch_piN st c rs1 rs2 (bv_signed imm)); discriminate Hs.
-- destruct sz; try discriminate Hs. destruct (tok_load K Bx Bspan SH st signed rd _); discriminate Hs.
+ injection H as <- <-. exact (sym_step_pi_tok_doml st st1 (or_intror (ex_intro _ s Hs))).
+ injection H as <- <-. split; [apply doml_refl | reflexivity].
Qed.
Definition ptok_post (E : env) (st' : shst) (r : ptrun_status psym) (ms' : machine_state) : Prop :=
match r with
| PTS_call s => st_ok segs E (setpc (sh_ss st') (sigma s)) ms'
| PTS_ecall => False
| _ => st_ok_pi E (sh_ss st') ms'
end.
Lemma sym_step_pi_tok_call : forall final E st s st1 ms,
img_env E -> INV final E (abs_sh st) ms -> sym_step_pi_tok st = PTCall s st1 ->
exists ms', msteps segs ms ms' /\ st_ok segs E (setpc (sh_ss st1) (sigma s)) ms'
/\ (sh_chk st1 = true -> sh_ok segs Bx SH E (ms_mem ms'))
/\ ms_mem ms' = ms_mem ms /\ ss_mem (sh_ss st1) = ss_mem (sh_ss st) /\ sh_j st1 = sh_j st /\ sh_chk st1 = sh_chk st.
Proof.
intros final E st s st1 ms HE HI H. pose proof (proj1 HI) as HS. cbn [sh_ss abs_sh] in HS.
assert (Hpend : ms_svc_pending ms = None) by exact (proj1 (proj2 (proj2 HS))).
unfold sym_step_pi_tok in H.
destruct (sym_step_pi tpi (sh_ss st)) as [ss1 | ss1 | s' ss1 | why] eqn:Hs; try discriminate H.
2: { destruct (dec tw (ss_pc (sh_ss st))) as [i|]; [|discriminate H]. destruct (sh_mem_pi (sh_ss st) i); [discriminate H|]. destruct i; try discriminate H.
- destruct (plookup tpi (ss_pc (sh_ss st) + bv_signed imm)); [|discriminate H]. destruct (tok_branch_piN st c rs1 rs2 (bv_signed imm)); discriminate H.
- destruct sz; try discriminate H. destruct (tok_load K Bx Bspan SH st signed rd _); discriminate H. }
injection H as Hs1 Hst1. subst s' st1.
destruct (YP0d.sym_step_pi_call psym segs fetch val sigma listing Hfetch Hcert A_LIM HLIM0 E (sh_ss st) ss1 s ms HE HS Hs)
as (ms' & Hstep & HS1 & Hm & Hss & _).
exists ms'. split; [exact (msteps_one segs ms ms' Hpend Hstep)|]. split; [destruct st; exact HS1|].
split; [| destruct st; cbn; auto].
intros Hc. rewrite Hm. destruct st as [ss j toks chk obls]; cbn in Hc |- *. subst chk.
destruct HI as (_ & _ & HC & _). destruct (HC eq_refl) as (_ & _ & Hsh & _). exact Hsh.
Qed.
Theorem sym_run_pi_tok_sound_gen : forall final fuel E0 ws st ms st' r,
img_env (extK E0 K ws) ->
INV final (extK E0 K ws) (abs_sh st) ms -> length ws = sh_j st ->
sym_run_pi_tok tpi tw K Bx Bspan SH fuel st = (st', r) ->
doml (sh_obls st') final ->
exists ws2 ms',
length (ws ++ ws2) = sh_j st' /\ msteps segs ms ms' /\ img_env (extK E0 K (ws ++ ws2))
/\ match r with
| PTS_call s => st_ok segs (extK E0 K (ws ++ ws2)) (setpc (sh_ss st') (sigma s)) ms'
/\ (sh_chk st' = true -> sh_ok segs Bx SH (extK E0 K (ws ++ ws2)) (ms_mem ms'))
| PTS_ecall => False
| _ => INV final (extK E0 K (ws ++ ws2)) (abs_sh st') ms'
end
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of (extK E0 K ws) (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros E0 ws st ms st' r HE HI Hlen H Hdom; cbn [sym_run_pi_tok] in H.
- injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HE|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
- destruct (sym_step_pi_tok st) as [st1 | st1 | s st1 | why] eqn:Hs.
+ assert (Hdom1 : doml (sh_obls st1) final).
{ eapply doml_trans; [exact (proj1 (sym_run_pi_tok_doml fuel st1 st' r H)) | exact Hdom]. }
destruct (sym_step_pi_tok_sound final _ st st1 ms HE HI Hs Hdom1) as (ms1 & E1 & Hms1 & HI1 & HE1 & Hj & Hsk1 & Hfr1 & Hchk1).
assert (Hws1 : exists ws1, E1 = extK E0 K (ws ++ ws1) /\ length (ws ++ ws1) = sh_j st1).
{ destruct Hj as [[Hj ->] | (v & Hj & -> & _)].
- exists []. rewrite app_nil_r. split; [reflexivity | lia].
- exists [v]. rewrite extK_snoc, Hlen. split; [reflexivity|]. rewrite length_app. cbn. lia. }
destruct Hws1 as (ws1 & HE1eq & Hlen1). rewrite HE1eq in HI1, HE1.
destruct (IH E0 (ws ++ ws1) st1 ms1 st' r HE1 HI1 Hlen1 H Hdom) as (ws2 & ms' & Hlen' & Hms & HE' & HR & Hsk & Hfr & Hchk).
exists (ws1 ++ ws2), ms'. rewrite app_assoc.
split; [exact Hlen'|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|]. split; [exact HE'|]. split; [exact HR|].
split; [congruence|]. split; [|congruence].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 |].
destruct Hj as [[Hj HEj] | (v & Hj & HEj & Hal)].
* destruct ws1 as [|v1 ws1']; [rewrite app_nil_r in Hfr; exact Hfr|].
exfalso. rewrite length_app in Hlen1. cbn in Hlen1. lia.
* assert (Hws1 : ws1 = [v]).
{ destruct ws1 as [|v1 [|v2 l]]; rewrite length_app in Hlen1; cbn in Hlen1; try lia.
rewrite HEj in HE1eq. rewrite <- Hlen in HE1eq. apply (f_equal (fun E => ew E (K + length ws)%nat)) in HE1eq. cbn beta in HE1eq.
rewrite extK_snoc, !ew_ewset_same in HE1eq. rewrite HE1eq. reflexivity. }
subst ws1. rewrite extK_snoc, Hlen in Hfr.
eapply (frame_of_agree_skel (K + sh_j st) _ _ (ss_mem (sh_ss st))); [apply env_agree_ewset | | exact Hsk1 | exact Hfr].
unfold ss_atoms_lt in Hal. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [_ Hm]. exact Hm.
+ exfalso. unfold sym_step_pi_tok in Hs. destruct (sym_step_pi tpi (sh_ss st)) as [ss1 | ss1 | s ss1 | why] eqn:Hs'; try discriminate Hs.
* exact (sym_step_pi_no_ecall _ _ Hs').
* destruct (dec tw (ss_pc (sh_ss st))) as [i|]; [|discriminate Hs]. destruct (sh_mem_pi (sh_ss st) i); [discriminate Hs|]. destruct i; try discriminate Hs.
-- destruct (plookup tpi (ss_pc (sh_ss st) + bv_signed imm)); [|discriminate Hs]. destruct (tok_branch_piN st c rs1 rs2 (bv_signed imm)); discriminate Hs.
-- destruct sz; try discriminate Hs. destruct (tok_load K Bx Bspan SH st signed rd _); discriminate Hs.
+ injection H as <- <-.
destruct (sym_step_pi_tok_call final _ st s st1 ms HE HI Hs) as (ms1 & Hms1 & HS1 & Hsh & Hm & Hss & Hj & Hchk).
exists [], ms1. rewrite app_nil_r.
split; [rewrite Hj; exact Hlen|]. split; [exact Hms1|]. split; [exact HE|]. split; [split; [exact HS1 | exact Hsh]|].
rewrite Hss, Hm. split; [reflexivity|]. split; [apply frame_of_refl | exact Hchk].
+ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HE|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
Qed.
Theorem sym_run_to_pi_tok_sound_gen : forall final fuel stop E0 ws st ms st' r,
img_env (extK E0 K ws) ->
INV final (extK E0 K ws) (abs_sh st) ms -> length ws = sh_j st ->
sym_run_to_pi_tok tpi tw K Bx Bspan SH fuel stop st = (st', r) ->
doml (sh_obls st') final ->
exists ws2 ms',
length (ws ++ ws2) = sh_j st' /\ msteps segs ms ms' /\ img_env (extK E0 K (ws ++ ws2))
/\ match r with
| PTS_call s => st_ok segs (extK E0 K (ws ++ ws2)) (setpc (sh_ss st') (sigma s)) ms'
/\ (sh_chk st' = true -> sh_ok segs Bx SH (extK E0 K (ws ++ ws2)) (ms_mem ms'))
| PTS_ecall => False
| _ => INV final (extK E0 K (ws ++ ws2)) (abs_sh st') ms'
end
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of (extK E0 K ws) (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros stop E0 ws st ms st' r HE HI Hlen H Hdom; cbn [sym_run_to_pi_tok] in H.
- injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HE|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
- destruct (ss_pc (sh_ss st) =? stop).
{ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HE|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity]. }
destruct (sym_step_pi_tok st) as [st1 | st1 | s st1 | why] eqn:Hs.
+ assert (Hdom1 : doml (sh_obls st1) final).
{ eapply doml_trans; [exact (proj1 (sym_run_to_pi_tok_doml fuel stop st1 st' r H)) | exact Hdom]. }
destruct (sym_step_pi_tok_sound final _ st st1 ms HE HI Hs Hdom1) as (ms1 & E1 & Hms1 & HI1 & HE1 & Hj & Hsk1 & Hfr1 & Hchk1).
assert (Hws1 : exists ws1, E1 = extK E0 K (ws ++ ws1) /\ length (ws ++ ws1) = sh_j st1).
{ destruct Hj as [[Hj ->] | (v & Hj & -> & _)].
- exists []. rewrite app_nil_r. split; [reflexivity | lia].
- exists [v]. rewrite extK_snoc, Hlen. split; [reflexivity|]. rewrite length_app. cbn. lia. }
destruct Hws1 as (ws1 & HE1eq & Hlen1). rewrite HE1eq in HI1, HE1.
destruct (IH stop E0 (ws ++ ws1) st1 ms1 st' r HE1 HI1 Hlen1 H Hdom) as (ws2 & ms' & Hlen' & Hms & HE' & HR & Hsk & Hfr & Hchk).
exists (ws1 ++ ws2), ms'. rewrite app_assoc.
split; [exact Hlen'|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|]. split; [exact HE'|]. split; [exact HR|].
split; [congruence|]. split; [|congruence].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 |].
destruct Hj as [[Hj HEj] | (v & Hj & HEj & Hal)].
* destruct ws1 as [|v1 ws1']; [rewrite app_nil_r in Hfr; exact Hfr|].
exfalso. rewrite length_app in Hlen1. cbn in Hlen1. lia.
* assert (Hws1 : ws1 = [v]).
{ destruct ws1 as [|v1 [|v2 l]]; rewrite length_app in Hlen1; cbn in Hlen1; try lia.
rewrite HEj in HE1eq. rewrite <- Hlen in HE1eq. apply (f_equal (fun E => ew E (K + length ws)%nat)) in HE1eq. cbn beta in HE1eq.
rewrite extK_snoc, !ew_ewset_same in HE1eq. rewrite HE1eq. reflexivity. }
subst ws1. rewrite extK_snoc, Hlen in Hfr.
eapply (frame_of_agree_skel (K + sh_j st) _ _ (ss_mem (sh_ss st))); [apply env_agree_ewset | | exact Hsk1 | exact Hfr].
unfold ss_atoms_lt in Hal. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [_ Hm]. exact Hm.
+ exfalso. unfold sym_step_pi_tok in Hs. destruct (sym_step_pi tpi (sh_ss st)) as [ss1 | ss1 | s ss1 | why] eqn:Hs'; try discriminate Hs.
* exact (sym_step_pi_no_ecall _ _ Hs').
* destruct (dec tw (ss_pc (sh_ss st))) as [i|]; [|discriminate Hs]. destruct (sh_mem_pi (sh_ss st) i); [discriminate Hs|]. destruct i; try discriminate Hs.
-- destruct (plookup tpi (ss_pc (sh_ss st) + bv_signed imm)); [|discriminate Hs]. destruct (tok_branch_piN st c rs1 rs2 (bv_signed imm)); discriminate Hs.
-- destruct sz; try discriminate Hs. destruct (tok_load K Bx Bspan SH st signed rd _); discriminate Hs.
+ injection H as <- <-.
destruct (sym_step_pi_tok_call final _ st s st1 ms HE HI Hs) as (ms1 & Hms1 & HS1 & Hsh & Hm & Hss & Hj & Hchk).
exists [], ms1. rewrite app_nil_r.
split; [rewrite Hj; exact Hlen|]. split; [exact Hms1|]. split; [exact HE|]. split; [split; [exact HS1 | exact Hsh]|].
rewrite Hss, Hm. split; [reflexivity|]. split; [apply frame_of_refl | exact Hchk].
+ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HE|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
Qed.
Lemma start_abs : forall ss, start K Bx Bspan SH (abs_ss ss) = abs_sh (start K Bx Bspan SH ss).
Proof. intros ss. reflexivity. Qed.
Theorem sym_run_pi_tok_sound : forall n E ss ms st' r,
img_env E -> st_ok_pi E ss ms -> sh_ok segs Bx SH E (ms_mem ms) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi tw K Bx Bspan SH n ss = (st', r) ->
Forall (ob_holds segs Bx E (ms_mem ms)) (sh_obls st') ->
exists ws ms',
length ws = sh_j st' /\ msteps segs ms ms' /\ img_env (extK E K ws)
/\ ptok_post (extK E K ws) st' r ms'
/\ sh_ok segs Bx SH (extK E K ws) (ms_mem ms')
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem ss)
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n E ss ms st' r HE HS Hsh Hchk H Hfin. unfold sym_runN_pi_tok in H.
pose proof (start_INV segs K Bx Bspan SH (sh_obls st') E (abs_ss ss) ms HS Hsh Hchk Hfin) as HI0. rewrite start_abs in HI0.
destruct (sym_run_pi_tok_sound_gen (sh_obls st') (N.to_nat n) E [] (start K Bx Bspan SH ss) ms st' r HE HI0 eq_refl H (doml_refl _))
as (ws & ms' & Hlen & Hms & HE' & HR & Hsk & Hfr & Hc).
cbn [app extK length start sh_ss sh_chk] in *. rewrite Hchk in Hc.
exists ws, ms'. split; [exact Hlen|]. split; [exact Hms|]. split; [exact HE'|].
destruct r.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
- destruct HR.
- destruct HR as [HS' Hsh']. split; [exact HS'|]. split; [exact (Hsh' Hc)|]. auto.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
Qed.
Theorem sym_run_to_pi_tok_sound : forall n stop E ss ms st' r,
img_env E -> st_ok_pi E ss ms -> sh_ok segs Bx SH E (ms_mem ms) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi tw K Bx Bspan SH n stop ss = (st', r) ->
Forall (ob_holds segs Bx E (ms_mem ms)) (sh_obls st') ->
exists ws ms',
length ws = sh_j st' /\ msteps segs ms ms' /\ img_env (extK E K ws)
/\ ptok_post (extK E K ws) st' r ms'
/\ sh_ok segs Bx SH (extK E K ws) (ms_mem ms')
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem ss)
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n stop E ss ms st' r HE HS Hsh Hchk H Hfin. unfold sym_run_toN_pi_tok in H.
pose proof (start_INV segs K Bx Bspan SH (sh_obls st') E (abs_ss ss) ms HS Hsh Hchk Hfin) as HI0. rewrite start_abs in HI0.
destruct (sym_run_to_pi_tok_sound_gen (sh_obls st') (N.to_nat n) stop E [] (start K Bx Bspan SH ss) ms st' r HE HI0 eq_refl H (doml_refl _))
as (ws & ms' & Hlen & Hms & HE' & HR & Hsk & Hfr & Hc).
cbn [app extK length start sh_ss sh_chk] in *. rewrite Hchk in Hc.
exists ws, ms'. split; [exact Hlen|]. split; [exact Hms|]. split; [exact HE'|].
destruct r.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
- destruct HR.
- destruct HR as [HS' Hsh']. split; [exact HS'|]. split; [exact (Hsh' Hc)|]. auto.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
Qed.
End m.
