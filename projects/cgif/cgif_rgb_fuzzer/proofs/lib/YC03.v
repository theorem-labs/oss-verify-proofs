(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK0p YK15.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ00 YQ0h YQ09 YQ04 YQ0f YC02 YQ07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition is_prefix_instr (i : instr) : bool :=
match i with
| Jal rd _ => bv_eqb rd 0
| Load _ _ _ _ _ => true
| OpImm _ _ _ _ => true
| _ => false
end.
Definition regs_same_except (u : reg) (sr2 sr : list sv) : bool :=
forallb (fun i => Nat.eqb i (ridx u) || sv_eqb (nth i sr2 (SLit 0)) (nth i sr (SLit 0))) (seq 1 31).
Lemma regs_same_except_sound : forall u sr2 sr r,
regs_same_except u sr2 sr = true -> r <> u -> sr_get sr2 r = sr_get sr r.
Proof.
intros u sr2 sr r H Hr. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|].
unfold regs_same_except in H. rewrite forallb_forall in H.
assert (Hin : In (ridx r) (seq 1 31)).
{ apply in_seq. unfold ridx. pose proof (u5_range r) as Hu.
assert (bv_unsigned r <> 0).
{ intros Hz. assert (r = 0%bv) by (apply bv_eq; rewrite Hz; reflexivity). subst r. rewrite bv_eqb_refl in Hr0. discriminate. }
lia. }
specialize (H _ Hin). apply orb_prop in H as [H|H].
- apply Nat.eqb_eq in H. apply ridx_inj in H. contradiction.
- apply sv_eqb_eq in H. exact H.
Qed.
Definition xmod8 (G : facts) (x : sv) : option Z :=
match x with
| SOff m c =>
match atom_lookup (f_atoms G) m with
| Some f => if (3 <=? af_al2 f) && (af_al2 f <=? 64) && (0 <=? af_lo f) && (0 <=? c) && (af_hi f + c <? M64)
then Some (c mod 8) else None
| None => None
end
| _ => None
end.
Lemma xmod8_sound : forall E G x m, facts_ok E G -> xmod8 G x = Some m -> U E x mod 8 = m.
Proof.
intros E G x m HG H. unfold xmod8 in H. destruct x as [|a c| | | | | | | | |]; try discriminate.
destruct (atom_lookup (f_atoms G) a) as [f|] eqn:Hl; [|discriminate].
destruct ((3 <=? af_al2 f) && (af_al2 f <=? 64) && (0 <=? af_lo f) && (0 <=? c) && (af_hi f + c <? M64)) eqn:Hb; [|discriminate].
injection H as <-. repeat (apply andb_prop in Hb as [Hb ?]).
apply Z.leb_le in Hb. repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hl) as (Hlohi & Hal & Hal2).
set (v := bv_unsigned (ew E a)) in *.
assert (Hv8 : v mod 8 = 0).
{ destruct (proj1 (Z.mod_divide v (2 ^ af_al2 f) ltac:(apply Z.pow_nonzero; lia)) Hal) as [k Hk].
rewrite Hk. replace (2 ^ af_al2 f) with (2 ^ (af_al2 f - 3) * 8) by (change 8 with (2 ^ 3); rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
rewrite U_SOff. fold v. rewrite zcanon_id by (unfold M64 in *; lia).
rewrite Z.add_mod, Hv8, Z.add_0_l, Z.mod_mod by lia. reflexivity.
Qed.
Definition slow_k (G : facts) (x e : sv) : option Z :=
match e with
| SLit c => match xmod8 G x with Some m => Some (c - m) | None => None end
| SAlu ALU_AND x' (SLit s7) => if (s7 =? 7) && sv_eqb x' x then Some 0 else None
| SAlu ALU_ADD (SAlu ALU_AND x' (SLit s7)) (SLit k) => if (s7 =? 7) && sv_eqb x' x then Some k else None
| _ => None
end.
Lemma slow_k_sound : forall E G x e k, facts_ok E G -> slow_k G x e = Some k -> 0 <= k <= 7 ->
sv_denot E e = Z_to_bv 64 (U E x mod 8 + k).
Proof.
intros E G x e k HG H Hk. pose proof (U_range E x) as HUx. pose proof (Z.mod_pos_bound (U E x) 8 ltac:(lia)) as Hm.
destruct e as [c| |op a b| | | | | | | |]; cbn [slow_k] in H; try discriminate.
- destruct (xmod8 G x) as [m|] eqn:Hx; [|discriminate]. injection H as <-.
rewrite (xmod8_sound E G x m HG Hx). cbn [sv_denot]. f_equal. lia.
- destruct op; try discriminate.
+
destruct a as [| |op2 a2 b2| | | | | | | |]; try discriminate. destruct op2; try discriminate.
destruct b2 as [s7| | | | | | | | | |]; try discriminate. destruct b as [k'| | | | | | | | | |]; try discriminate.
destruct ((s7 =? 7) && sv_eqb a2 x) eqn:Hc; [|discriminate]. injection H as ->.
apply andb_prop in Hc as [H7 Hx]. apply Z.eqb_eq in H7. apply sv_eqb_eq in Hx. subst s7 a2.
cbn [sv_denot]. rewrite (denot_lit_U E x), alu_and7 by exact HUx.
apply alu_add_small; unfold M64 in *; lia.
+
destruct b as [s7| | | | | | | | | |]; try discriminate.
destruct ((s7 =? 7) && sv_eqb a x) eqn:Hc; [|discriminate]. injection H as <-.
apply andb_prop in Hc as [H7 Hx]. apply Z.eqb_eq in H7. apply sv_eqb_eq in Hx. subst s7 a.
cbn [sv_denot]. rewrite (denot_lit_U E x), alu_and7 by exact HUx. rewrite Z.add_0_r. reflexivity.
Qed.
Section X2.
Variable segs : list Segment.
Variable tbl : ctable.
Variables (K : nat) (Bx : sv) (Bspan : Z * Z) (SH : list shent).
Fixpoint run_prefix (fuel : nat) (ss : sstate) : option sstate :=
match fuel with
| O => None
| S f =>
match dec tbl (ss_pc ss) with
| Some i =>
if is_prefix_instr i then
match sym_step segs tbl ss with SRun ss' => run_prefix f ss' | _ => None end
else Some ss
| None => None
end
end.
Definition cmp_at (L2 Lz : Z) (t : reg) : option reg :=
match decp tbl as_branch L2 with
| Some (BC_LT, r1, r2, off) =>
if bv_eqb r2 t && (zcanon (L2 + off) =? zcanon Lz) then Some r1 else None
| Some (BC_GE, r1, r2, off) =>
if bv_eqb r2 t then
match decp tbl as_j (L2 + 4) with
| Some offj => if zcanon (L2 + 4 + offj) =? zcanon Lz then Some r1 else None
| None => None
end
else None
| _ => None
end.
Definition tok_branchX (st : shst) (cnd : branch_cond) (rs1 rs2 : reg) (imm : Z) : option shst :=
let ss := sh_ss st in
let G := ss_facts ss in
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
match (match cnd with
| BC_NE => Some (zcanon (pc + imm), pc + 4)
| BC_EQ => Some (pc + 4, zcanon (pc + imm))
| _ => None end) with
| None => None
| Some (Lnz, Lz) =>
match slow_block tbl Lnz Lz rs1 with
| Some _ => None
| None =>
match run_prefix 5 (setpc ss Lnz) with
| None => None
| Some ss2 =>
match cmp_at (ss_pc ss2) Lz rs1 with
| None => None
| Some u =>
if bv_eqb u 0 || bv_eqb u rs1 then None else
if negb (regs_same_except u (ss_regs ss2) (ss_regs ss)) then None else
match slow_k G x (sr_get (ss_regs ss2) u) with
| None => None
| Some k =>
if negb ((0 <=? k) && (k <=? 7)) then None else
match need K Bx Bspan SH G x (k + 1) (sh_obls st) with
| None => None
| Some obls' =>
if sv_eqb (sr_get (ss_regs ss2) u) (R u) then
let ss' := setpc ss Lz in
Some (mkSH ss' (sh_j st) (prune ss' (sh_toks st)) (sh_chk st) obls')
else
let U0 := (K + sh_j st)%nat in
if negb (ss_atoms_lt U0 ss) then None else
let ss' := setreg ss u (SOff U0 0) Lz in
Some (mkSH ss' (S (sh_j st)) (prune ss' (sh_toks st)) (sh_chk st) obls')
end
end
end
end
end
end
end
| _ => None
end
end.
Definition tok_branchX_at (st : shst) : option shst :=
match dec tbl (ss_pc (sh_ss st)) with
| Some (Branch cnd rs1 rs2 imm) => tok_branchX st cnd rs1 rs2 (bv_signed imm)
| _ => None
end.
Definition sym_step_tokX (st : shst) : tres :=
match tok_branchX_at st with
| Some st' => TRun st'
| None => sym_step_tok segs tbl K Bx Bspan SH st
end.
End X2.
Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Context {fx : FPState}.
Variables (K : nat) (Bx : sv) (Bspan : Z * Z) (SH : list shent).
Hypothesis Htbl : table_ok segs tbl.
Lemma sym_step_prefix_keep : forall ss ss' i,
dec tbl (ss_pc ss) = Some i -> is_prefix_instr i = true -> sym_step segs tbl ss = SRun ss' ->
ss_mem ss' = ss_mem ss /\ ss_facts ss' = ss_facts ss /\ ss_resv ss' = ss_resv ss.
Proof.
intros ss ss' i Hd Hp H. unfold dec in Hd. unfold sym_step in H.
destruct (clookup tbl (ss_pc ss)) as [wz|]; [|discriminate]. cbv zeta in Hd, H.
destruct (is_ecall (Z_to_bv 32 wz)); [discriminate|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i0 isz]|]; [|discriminate].
destruct (isz =? 4); cbn [negb] in H; [|discriminate]. injection Hd as ->.
destruct i; try discriminate Hp.
- injection H as <-. cbn. auto.
- destruct (addr_of _) as [[b off]|]; [|discriminate].
destruct (sload _ _ _ _ _ _ _) as [v|]; [|discriminate]. injection H as <-. cbn. auto.
- injection H as <-. cbn. auto.
Qed.
Lemma run_prefix_keep : forall fuel ss ss2,
run_prefix segs tbl fuel ss = Some ss2 ->
ss_mem ss2 = ss_mem ss /\ ss_facts ss2 = ss_facts ss /\ ss_resv ss2 = ss_resv ss.
Proof.
induction fuel as [|fuel IH]; intros ss ss2 H; cbn [run_prefix] in H; [discriminate|].
destruct (dec tbl (ss_pc ss)) as [i|] eqn:Hd; [|discriminate].
destruct (is_prefix_instr i) eqn:Hp.
- destruct (sym_step segs tbl ss) as [ss1| |] eqn:Hs; try discriminate.
destruct (sym_step_prefix_keep ss ss1 i Hd Hp Hs) as (H1 & H2 & H3).
destruct (IH ss1 ss2 H) as (H1' & H2' & H3'). repeat split; congruence.
- injection H as <-. auto.
Qed.
Lemma run_prefix_sound : forall fuel E ss ss2 ms,
st_ok segs E ss ms -> run_prefix segs tbl fuel ss = Some ss2 ->
exists ms2, msteps segs ms ms2 /\ st_ok segs E ss2 ms2 /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms2).
Proof.
induction fuel as [|fuel IH]; intros E ss ss2 ms HS H; cbn [run_prefix] in H; [discriminate|].
destruct (dec tbl (ss_pc ss)) as [i|] eqn:Hd; [|discriminate].
destruct (is_prefix_instr i) eqn:Hp.
- destruct (sym_step segs tbl ss) as [ss1| |] eqn:Hs; try discriminate.
destruct (sym_step_sound segs tbl Htbl E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hfr1).
destruct (sym_step_prefix_keep ss ss1 i Hd Hp Hs) as (Hm1 & _ & _).
destruct (IH E ss1 ss2 ms1 HS1 H) as (ms2 & Hms & HS2 & Hfr2).
exists ms2. split; [|split; [exact HS2|]].
+ eapply mst_step; [destruct HS as (_ & _ & Hp0 & _); exact Hp0 | exact Hstep | exact Hms].
+ eapply frame_of_trans; [|exact Hfr1 | exact Hfr2]. rewrite Hm1. reflexivity.
- injection H as <-. exists ms. split; [apply mst_refl|]. split; [exact HS | apply frame_of_refl].
Qed.
Lemma cmp_at_facts : forall L2 Lz t u, cmp_at tbl L2 Lz t = Some u ->
(exists off, decp tbl as_branch L2 = Some (BC_LT, u, t, off) /\ zcanon (L2 + off) = zcanon Lz)
\/ (exists off offj, decp tbl as_branch L2 = Some (BC_GE, u, t, off) /\ decp tbl as_j (L2 + 4) = Some offj
/\ zcanon (L2 + 4 + offj) = zcanon Lz).
Proof.
intros L2 Lz t u H. unfold cmp_at in H.
destruct (decp tbl as_branch L2) as [[[[c r1] r2] off]|] eqn:HD2; [|discriminate].
destruct c; try discriminate.
- destruct (bv_eqb r2 t && (zcanon (L2 + off) =? zcanon Lz)) eqn:Hc; [|discriminate]. injection H as ->.
apply andb_prop in Hc as [Hb Hz]. apply bv_eqb_eq in Hb. subst r2. apply Z.eqb_eq in Hz. left. exists off. auto.
- destruct (bv_eqb r2 t) eqn:Hb; [|discriminate]. apply bv_eqb_eq in Hb. subst r2.
destruct (decp tbl as_j (L2 + 4)) as [offj|] eqn:HD3; [|discriminate].
destruct (zcanon (L2 + 4 + offj) =? zcanon Lz) eqn:Hz; [|discriminate]. injection H as ->. apply Z.eqb_eq in Hz.
right. exists off, offj. auto.
Qed.
Lemma cmp_exec : forall L2 Lz (t u : reg) regs mem,
cmp_at tbl L2 Lz t = Some u -> bv_lts (getr regs u) (getr regs t) = true ->
msteps segs (mkst regs (Z_to_bv 64 L2) mem (seg_rom segs)) (mkst regs (Z_to_bv 64 Lz) mem (seg_rom segs)).
Proof.
intros L2 Lz t u regs mem H Hlts.
destruct (cmp_at_facts L2 Lz t u H) as [(off & HD2 & Hz) | (off & offj & HD2 & HD3 & Hz)].
- destruct (decp_sound tbl as_branch _ _ HD2) as (i2 & HD2' & Hi2).
destruct (as_branch_sound i2 _ _ _ _ Hi2) as (offb & -> & Hoff).
destruct (dec_sound segs tbl Htbl _ _ HD2') as (w2 & F2 & E2 & D2).
apply msteps_one; [reflexivity|].
rewrite (step_branch_tk_gen segs regs _ mem _ w2 BC_LT u t offb F2 E2 D2); [|cbn [branch_taken]; exact Hlts].
rewrite btgt_lit, Hoff, (zv_zcanon_eq _ _ Hz). reflexivity.
- destruct (decp_sound tbl as_branch _ _ HD2) as (i2 & HD2' & Hi2).
destruct (as_branch_sound i2 _ _ _ _ Hi2) as (offb & -> & Hoff).
destruct (dec_sound segs tbl Htbl _ _ HD2') as (w2 & F2 & E2 & D2).
destruct (decp_sound tbl as_j _ _ HD3) as (i3 & HD3' & Hi3).
destruct (as_j_sound i3 _ Hi3) as (offc & -> & Hoffc).
destruct (dec_sound segs tbl Htbl _ _ HD3') as (w3 & F3 & E3 & D3).
eapply mst_step; [reflexivity| |].
{ rewrite (step_branch_ft_gen segs regs _ mem _ w2 BC_GE u t offb F2 E2 D2); [reflexivity|].
cbn [branch_taken]. rewrite Hlts. reflexivity. }
rewrite v_addi_lit. apply msteps_one; [reflexivity|].
rewrite (step_jal_x0 segs regs _ mem _ w3 offc F3 E3 D3). rewrite btgt_lit, Hoffc, (zv_zcanon_eq _ _ Hz). reflexivity.
Qed.
Lemma st_ok_setpc : forall E ss regs pc mem pc',
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) -> ss_resv ss = None ->
st_ok segs E (setpc ss pc') (mkst regs (Z_to_bv 64 pc') mem (seg_rom segs)).
Proof.
intros E ss regs pc mem pc' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hrv.
unfold st_ok, setpc; cbn. rewrite Hrv. cbn. repeat (split; [reflexivity|]). split; [exact H7|]. split; assumption.
Qed.
Lemma st_ok_rebuild : forall E ss regs pc mem regs' mem' pc',
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) -> ss_resv ss = None ->
regs_ok E (ss_regs ss) regs' -> mem_ok segs E mem' (ss_mem ss) ->
st_ok segs E (setpc ss pc') (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom segs)).
Proof.
intros E ss regs pc mem regs' mem' pc' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hrv HR HM.
unfold st_ok, setpc; cbn. rewrite Hrv. cbn. repeat (split; [reflexivity|]). split; [exact HR|]. split; assumption.
Qed.
Lemma tok_branchX_sound : forall final E st cnd rs1 rs2 (imm : bv 13) st' ms w,
INV segs K Bx Bspan SH final E st ms ->
fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
decode_any w = Some (Branch cnd rs1 rs2 imm, 4) ->
tok_branchX segs tbl K Bx Bspan SH st cnd rs1 rs2 (bv_signed imm) = Some st' ->
doml (sh_obls st') final ->
exists ms' E',
msteps segs ms ms' /\ INV segs K Bx Bspan SH final E' st' ms'
/\ ((sh_j st' = sh_j st /\ E' = E)
\/ (exists v, sh_j st' = S (sh_j st) /\ E' = ewset E (K + sh_j st) v /\ ss_atoms_lt (K + sh_j st) (sh_ss st) = true))
/\ ss_mem (sh_ss st') = ss_mem (sh_ss st)
/\ frame_of E (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
intros final E st cnd rs1 rs2 imm st' ms w HI Hf He Hd H Hdom.
destruct st as [ss j toks chk obls]. cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in *.
unfold INV in HI. destruct HI as (HS & HT & HC & HN). cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in *.
unfold tok_branchX in H. cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in H.
destruct (bv_eqb rs2 0) eqn:Hrs2; [|discriminate]. cbn [negb] in H. apply bv_eqb_eq in Hrs2. subst rs2.
destruct (ss_resv ss) as [rv|] eqn:Hrv; [discriminate|].
destruct (sr_get (ss_regs ss) rs1) as [|T z0| | | | | | | | |] eqn:HR1; try discriminate.
destruct (z0 =? 0) eqn:Hz0; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hz0. subst z0.
destruct (find_tok toks rs1 T) as [tk|] eqn:Htk; [|discriminate].
destruct (find_tok_sound _ _ _ _ Htk) as (Htkin & Htkr & HtkT).
destruct chk; [|rewrite (HN eq_refl) in Htkin; destruct Htkin].
destruct (HC eq_refl) as (Hst & Hat & Hsh & Htoks & Hob).
assert (Htok : tok_ok segs K Bx Bspan E (ms_mem ms) tk) by (rewrite Forall_forall in Htoks; exact (Htoks tk Htkin)).
destruct Htok as (Hxk & Hcsp & b & Hb & Hv).
set (x := tk_x tk) in *.
destruct (match cnd with
| BC_NE => Some (zcanon (ss_pc ss + bv_signed imm), ss_pc ss + 4)
| BC_EQ => Some (ss_pc ss + 4, zcanon (ss_pc ss + bv_signed imm))
| _ => None end) as [[Lnz Lz]|] eqn:HLL; [|discriminate].
assert (Hcnd : (cnd = BC_NE /\ Lnz = zcanon (ss_pc ss + bv_signed imm) /\ Lz = ss_pc ss + 4)
\/ (cnd = BC_EQ /\ Lnz = ss_pc ss + 4 /\ Lz = zcanon (ss_pc ss + bv_signed imm))).
{ destruct cnd; try discriminate; injection HLL as <- <-; auto. }
clear HLL.
destruct (slow_block tbl Lnz Lz rs1) as [?|] eqn:Hsb; [discriminate|].
destruct (run_prefix segs tbl 5 (setpc ss Lnz)) as [ss2|] eqn:Hpre; [|discriminate].
destruct (cmp_at tbl (ss_pc ss2) Lz rs1) as [u|] eqn:Hcmp; [|discriminate].
destruct (bv_eqb u 0 || bv_eqb u rs1) eqn:Hu; [discriminate|]. apply orb_false_elim in Hu as [Hu0 Hut].
destruct (regs_same_except u (ss_regs ss2) (ss_regs ss)) eqn:Hsame; [|discriminate]. cbn [negb] in H.
destruct (slow_k (ss_facts ss) x (sr_get (ss_regs ss2) u)) as [k|] eqn:Hk; [|discriminate].
destruct ((0 <=? k) && (k <=? 7)) eqn:Hk07; [|discriminate]. cbn [negb] in H.
apply andb_prop in Hk07 as [Hk0 Hk7]. apply Z.leb_le in Hk0. apply Z.leb_le in Hk7.
destruct (need K Bx Bspan SH (ss_facts ss) x (k + 1) obls) as [obls'|] eqn:Hneed; [|discriminate].
assert (Hdom' : doml obls' final).
{ destruct (sv_eqb (sr_get (ss_regs ss2) u) (sr_get (ss_regs ss) u)); [injection H as <-; exact Hdom|].
destruct (ss_atoms_lt (K + j) ss); [|discriminate]. injection H as <-. exact Hdom. }
pose proof HS as HS0. destruct HS as (_ & Hpc & _ & _ & _ & _ & Hregs & Hmem & HG).
pose proof (st_ok_mkst segs E ss ms HS0 Hrv) as Hshape.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
assert (Ht : getr regs rs1 = cellval (tk_sg tk) b).
{ rewrite (Hregs rs1), HR1. cbn [sv_denot]. rewrite <- HtkT, Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
rewrite Hshape in Hf. cbn [ms_pc_val mkst] in Hf.
assert (Hrds : rd_of segs mem (shadow_of_addr (U E Bx) (U E x)) = Some (bv_unsigned b)).
{ unfold rd_of, shadow_of_addr. unfold cell_x in Hb. rewrite Hb. reflexivity. }
pose proof (U_range E x) as HUx.
pose proof (Z.mod_pos_bound (U E x) 8 ltac:(lia)) as Hxm.
assert (Hune : u <> 0%bv) by (intros ->; rewrite bv_eqb_refl in Hu0; discriminate).
assert (Hut' : rs1 <> u) by (intros ->; rewrite bv_eqb_refl in Hut; discriminate).
destruct (need_sound segs K Bx Bspan SH final E _ mem (ss_facts ss) x (k + 1) obls obls' Hst Hsh Hob HG Hneed Hdom' ltac:(lia)) as [HRA _].
pose proof (check_passes_lb (rd_of segs mem) (U E Bx) (U E x) (k + 1) (U E x) (k + 1) (bv_unsigned b)
HRA ltac:(lia) ltac:(lia) ltac:(lia) Hrds) as Hpass.
rewrite Hshape in HS0.
assert (PATHS : exists regs' mem',
msteps segs (mkst regs (Z_to_bv 64 (ss_pc ss)) mem (seg_rom segs)) (mkst regs' (Z_to_bv 64 Lz) mem' (seg_rom segs))
/\ (forall r, r <> u -> getr regs' r = getr regs r)
/\ (sr_get (ss_regs ss2) u = sr_get (ss_regs ss) u -> getr regs' u = getr regs u)
/\ frame_of E (ss_mem ss) mem mem'
/\ mem_ok segs E mem' (ss_mem ss)).
{ destruct (Z.eq_dec (bv_unsigned b) 0) as [Hs0|Hs0].
-
exists regs, mem. split; [|split; [intros; reflexivity | split; [intros; reflexivity | split; [apply frame_of_refl | exact Hmem]]]].
assert (Ht0 : getr regs rs1 = Z_to_bv 64 0) by (rewrite Ht; apply (proj2 (cellval_zero_iff _ _)); exact Hs0).
apply msteps_one; [reflexivity|].
destruct Hcnd as [(-> & _ & ->) | (-> & _ & ->)].
+ rewrite (step_branch_ft_gen segs regs _ mem _ w BC_NE rs1 0 imm Hf He Hd); [rewrite v_addi_lit; reflexivity|].
cbn [branch_taken]. rewrite Ht0, getr_zero, bv_eqb_refl. reflexivity.
+ rewrite (step_branch_tk_gen segs regs _ mem _ w BC_EQ rs1 0 imm Hf He Hd); [rewrite btgt_lit, Z_to_bv64_canon; reflexivity|].
cbn [branch_taken]. rewrite Ht0, getr_zero, bv_eqb_refl. reflexivity.
-
destruct Hpass as [Hz | [Hlt Hsr]]; [lia|].
assert (Hts : getr regs rs1 = Z_to_bv 64 (bv_unsigned b)) by (rewrite Ht; apply cellval_small; lia).
assert (Hne0 : bv_eqb (getr regs rs1) (getr regs 0) = false).
{ rewrite Hts, getr_zero. apply Bool.not_true_is_false. intros Hq. apply bv_eqb_eq in Hq.
apply (f_equal bv_unsigned) in Hq. rewrite !unsigned_lit_small in Hq by lia. lia. }
assert (M0 : RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (ss_pc ss)) mem (seg_rom segs))
= MachineOk (mkst regs (Z_to_bv 64 Lnz) mem (seg_rom segs))).
{ destruct Hcnd as [(-> & -> & _) | (-> & -> & _)].
+ rewrite (step_branch_tk_gen segs regs _ mem _ w BC_NE rs1 0 imm Hf He Hd); [rewrite btgt_lit, Z_to_bv64_canon; reflexivity|].
cbn [branch_taken]. rewrite Hne0. reflexivity.
+ rewrite (step_branch_ft_gen segs regs _ mem _ w BC_EQ rs1 0 imm Hf He Hd); [rewrite v_addi_lit; reflexivity|].
cbn [branch_taken]. exact Hne0. }
pose proof (st_ok_setpc E ss regs _ mem Lnz HS0 Hrv) as HSnz.
destruct (run_prefix_sound 5 E (setpc ss Lnz) ss2 _ HSnz Hpre) as (ms2 & Mpre & HS2 & Hfr2).
destruct (run_prefix_keep 5 (setpc ss Lnz) ss2 Hpre) as (Hm2 & Hf2 & Hr2). cbn [setpc ss_mem ss_facts ss_resv] in Hm2, Hf2, Hr2.
pose proof (st_ok_mkst segs E ss2 ms2 HS2 ltac:(rewrite Hr2; exact Hrv)) as Hshape2.
destruct HS2 as (_ & _ & _ & _ & _ & _ & Hregs2 & Hmem2 & _).
set (regs2 := ms_regs ms2) in *. set (mem2 := ms_mem ms2) in *.
assert (Hsame_r : forall r, r <> u -> getr regs2 r = getr regs r).
{ intros r Hr. rewrite (Hregs2 r), (Hregs r), (regs_same_except_sound u _ _ r Hsame Hr). reflexivity. }
assert (Hu2 : getr regs2 u = Z_to_bv 64 (U E x mod 8 + k)).
{ rewrite (Hregs2 u). apply (slow_k_sound E (ss_facts ss) x _ k HG Hk). lia. }
assert (Ht2 : getr regs2 rs1 = Z_to_bv 64 (bv_unsigned b)) by (rewrite (Hsame_r rs1 Hut'); exact Hts).
assert (Hlts : bv_lts (getr regs2 u) (getr regs2 rs1) = true).
{ rewrite Hu2, Ht2, bv_lts_small by lia. apply Z.ltb_lt. lia. }
exists regs2, mem2. split; [|split; [exact Hsame_r | split; [|split]]].
+ eapply mst_step; [reflexivity | exact M0 |].
eapply msteps_trans; [rewrite Hshape2 in Mpre; exact Mpre|].
exact (cmp_exec (ss_pc ss2) Lz rs1 u regs2 mem2 Hcmp Hlts).
+ intros Heq. rewrite (Hregs2 u), (Hregs u), Heq. reflexivity.
+ cbn [setpc ss_mem] in Hfr2. cbn [ms_mem mkst] in Hfr2. exact Hfr2.
+ rewrite <- Hm2. exact Hmem2. }
destruct PATHS as (regs' & mem' & Mp & Hfr & Hfu & Hfrm & Hmem').
destruct (sv_eqb (sr_get (ss_regs ss2) u) (sr_get (ss_regs ss) u)) eqn:Hclob.
-
injection H as <-. apply sv_eqb_eq in Hclob.
exists (mkst regs' (Z_to_bv 64 Lz) mem' (seg_rom segs)), E.
split; [rewrite Hshape at 1; exact Mp|].
split; [|split; [left; split; reflexivity | split; [reflexivity | split; [exact Hfrm | reflexivity]]]].
unfold INV; cbn [sh_ss sh_j sh_toks sh_chk sh_obls].
split; [|split; [apply Forall_filter'; exact HT | split; [|intros; discriminate]]].
+ apply (st_ok_rebuild E ss regs _ mem regs' mem' Lz HS0 Hrv); [|exact Hmem'].
intros r. destruct (bv_eqb r u) eqn:Hru.
* apply bv_eqb_eq in Hru. subst r. rewrite (Hfu Hclob). apply Hregs.
* rewrite Hfr; [apply Hregs|]. intros ->. rewrite bv_eqb_refl in Hru. discriminate.
+ intros _. cbn [setpc ss_mem].
split; [exact Hst|]. split; [exact Hat|]. split; [|split].
* exact (sh_ok_frame segs K Bx Bspan SH E _ _ _ Hst Hfrm Hsh).
* apply Forall_filter'. rewrite Forall_forall in Htoks |- *. intros tk0 Hin0.
exact (tok_ok_frame segs K Bx Bspan SH E _ _ _ tk0 Hst Hfrm (Htoks tk0 Hin0)).
* exact (OBL_frame segs K Bx Bspan SH final E _ _ _ Hst Hfrm Hob).
-
destruct (ss_atoms_lt (K + j) ss) eqn:Hal; [|discriminate]. cbn [negb] in H. injection H as <-.
set (U0 := (K + j)%nat) in *. set (v := getr regs' u). set (E' := ewset E U0 v).
assert (HA : env_agree U0 E E') by apply env_agree_ewset.
assert (HUK : (K <= U0)%nat) by lia.
assert (Hat' : sh_atoms_ltb Bx SH U0 = true) by (apply (sh_atoms_lt_mono Bx SH K); [lia | exact Hat]).
assert (Hmlt : mem_atoms_lt U0 (ss_mem ss) = true).
{ unfold ss_atoms_lt in Hal. apply andb_prop in Hal as [Hal2 _]. apply andb_prop in Hal2 as [Hal2 _]. apply andb_prop in Hal2 as [_ Hm2]. exact Hm2. }
exists (mkst regs' (Z_to_bv 64 Lz) mem' (seg_rom segs)), E'.
split; [rewrite Hshape at 1; exact Mp|].
split; [|split; [right; exists v; split; [reflexivity | split; [reflexivity | first [exact Hal | reflexivity]]] | split; [reflexivity | split; [exact Hfrm | reflexivity]]]].
unfold INV; cbn [sh_ss sh_j sh_toks sh_chk sh_obls].
split; [|split; [|split; [|intros; discriminate]]].
+ pose proof (st_ok_set_regs_mem segs U0 E E' ss regs regs' _ Lz mem mem' (ss_mem ss) [(u, SOff U0 0)] HS0 HA Hal eq_refl) as HX.
assert (HX' : st_ok segs E' (mkSS Lz (sr_sets (ss_regs ss) [(u, SOff U0 0)]) (ss_mem ss) None (ss_facts ss))
(mkst regs' (Z_to_bv 64 Lz) mem' (seg_rom segs))).
{ apply HX.
- intros r Hr. cbn in Hr. apply orb_false_elim in Hr as [Hr _]. apply Hfr. intros ->. rewrite bv_eqb_refl in Hr. discriminate.
- constructor; [|constructor]. cbn [fst snd]. split; [exact Hu0|].
cbn [sv_denot]. subst E'. rewrite ew_ewset_same, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- exact (mem_ok_agree segs U0 E E' _ _ HA Hmlt Hmem'). }
destruct HX' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok, setreg; cbn. rewrite Hrv. cbn in *. repeat (split; [assumption|]). exact H9.
+ apply Forall_filter'. rewrite Forall_forall in HT |- *. intros tk0 Hin0. specialize (HT tk0 Hin0). lia.
+ intros _. cbn [setreg ss_mem].
split; [|split; [exact Hat|split; [|split]]].
* exact (static_sem_agree K Bx Bspan SH U0 E E' _ HA Hat' Hmlt Hst).
* apply (sh_ok_agree segs Bx SH U0 E E' _ HA Hat'). exact (sh_ok_frame segs K Bx Bspan SH E _ _ _ Hst Hfrm Hsh).
* apply Forall_filter'. rewrite Forall_forall in Htoks, HT |- *. intros tk0 Hin0.
apply (tok_ok_agree segs K Bx Bspan SH U0 E E'); [exact HA | exact HUK | exact Hat' | exact (HT tk0 Hin0) |].
exact (tok_ok_frame segs K Bx Bspan SH E _ _ _ tk0 Hst Hfrm (Htoks tk0 Hin0)).
* apply (OBL_agree segs K Bx Bspan SH final U0 E E' _ HA HUK Hat'). exact (OBL_frame segs K Bx Bspan SH final E _ _ _ Hst Hfrm Hob).
Qed.
Lemma tok_branchX_doml : forall st cnd rs1 rs2 imm st',
tok_branchX segs tbl K Bx Bspan SH st cnd rs1 rs2 imm = Some st' ->
doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
intros st cnd rs1 rs2 imm st' H. unfold tok_branchX in H.
destruct (negb (bv_eqb rs2 0)); [discriminate|].
destruct (ss_resv (sh_ss st)); [discriminate|].
destruct (sr_get (ss_regs (sh_ss st)) rs1) as [|T z0| | | | | | | | |]; try discriminate.
destruct (negb (z0 =? 0)); [discriminate|].
destruct (find_tok (sh_toks st) rs1 T) as [tk|]; [|discriminate].
destruct (match cnd with BC_NE => _ | BC_EQ => _ | _ => None end) as [[Lnz Lz]|]; [|discriminate].
destruct (slow_block tbl Lnz Lz rs1); [discriminate|].
destruct (run_prefix segs tbl 5 (setpc (sh_ss st) Lnz)) as [ss2|]; [|discriminate].
destruct (cmp_at tbl (ss_pc ss2) Lz rs1) as [u|]; [|discriminate].
destruct (bv_eqb u 0 || bv_eqb u rs1); [discriminate|].
destruct (negb (regs_same_except u (ss_regs ss2) (ss_regs (sh_ss st)))); [discriminate|].
destruct (slow_k _ _ _) as [k|]; [|discriminate].
destruct (negb ((0 <=? k) && (k <=? 7))); [discriminate|].
destruct (need K Bx Bspan SH _ _ (k + 1) (sh_obls st)) as [obls'|] eqn:Hneed; [|discriminate].
pose proof (need_doml K Bx Bspan SH _ _ _ _ _ Hneed) as Hd.
destruct (sv_eqb _ _).
- injection H as <-. cbn. split; [exact Hd | reflexivity].
- destruct (negb (ss_atoms_lt _ _)); [discriminate|]. injection H as <-. cbn. split; [exact Hd | reflexivity].
Qed.
Lemma sym_step_tokX_doml : forall st st',
sym_step_tokX segs tbl K Bx Bspan SH st = TRun st' \/ sym_step_tokX segs tbl K Bx Bspan SH st = TEcall st' ->
doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
intros st st' H. unfold sym_step_tokX in H.
destruct (tok_branchX_at segs tbl K Bx Bspan SH st) as [st1|] eqn:HX.
- destruct H as [H|H]; [|discriminate]. injection H as <-.
unfold tok_branchX_at in HX. destruct (dec tbl (ss_pc (sh_ss st))) as [i|]; [|discriminate].
destruct i; try discriminate. exact (tok_branchX_doml _ _ _ _ _ _ HX).
- exact (sym_step_tok_doml segs tbl K Bx Bspan SH st st' H).
Qed.
Theorem sym_step_tokX_sound : forall final E st st' ms,
INV segs K Bx Bspan SH final E st ms -> sym_step_tokX segs tbl K Bx Bspan SH st = TRun st' -> doml (sh_obls st') final ->
exists ms' E',
msteps segs ms ms' /\ INV segs K Bx Bspan SH final E' st' ms'
/\ ((sh_j st' = sh_j st /\ E' = E)
\/ (exists v, sh_j st' = S (sh_j st) /\ E' = ewset E (K + sh_j st) v /\ ss_atoms_lt (K + sh_j st) (sh_ss st) = true))
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of E (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
intros final E st st' ms HI H Hdom. unfold sym_step_tokX in H.
destruct (tok_branchX_at segs tbl K Bx Bspan SH st) as [st1|] eqn:HX.
- injection H as <-. unfold tok_branchX_at in HX.
destruct (dec tbl (ss_pc (sh_ss st))) as [i|] eqn:HD; [|discriminate].
destruct i; try discriminate.
destruct (dec_sound segs tbl Htbl _ _ HD) as (w & Hf & He & Hdi).
assert (Hf' : fetch_word segs (ms_pc_val ms) = Some w).
{ pose proof HI as HI'. unfold INV in HI'. destruct HI' as ((_ & Hpc & _) & _). rewrite Hpc. exact Hf. }
destruct (tok_branchX_sound final E st c rs1 rs2 imm st1 ms w HI Hf' He Hdi HX Hdom) as (ms' & E' & Hms & HI' & Hj & Hm1 & Hfr & Hchk).
exists ms', E'. split; [exact Hms|]. split; [exact HI'|]. split; [exact Hj|].
rewrite Hm1. split; [reflexivity|]. split; [exact Hfr | exact Hchk].
- exact (sym_step_tok_sound segs tbl K Bx Bspan SH Htbl final E st st' ms HI H Hdom).
Qed.

End d.
Definition is_fp_instr (i : instr) : bool :=
match i with
| FLoad _ _ _ _ | FStore _ _ _ _ | Fma _ _ _ _ _ _ _ | Fari _ _ _ _ _ _ | Fsqrt _ _ _ _
| Fsgnj _ _ _ _ _ | Fminmax _ _ _ _ _ | Fcmp _ _ _ _ _ | Fcvt _ _ _ _ _ | Fmv _ _ _ _ | Fclass _ _ _ => true
| _ => false
end.
Definition set_fregs (ss : sstate) (sfr : list sv) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) sfr (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition with_fregs (sfr : list sv) (st : shst) : shst :=
mkSH (set_fregs (sh_ss st) sfr) (sh_j st) (sh_toks st) (sh_chk st) (sh_obls st).
Section g.
Variable segs : list Segment.
Variable tbl : ctable.
Variables (K : nat) (Bx : sv) (Bspan : Z * Z) (SH : list shent).
Definition is_fp_at (ss : sstate) : bool :=
match dec tbl (ss_pc ss) with Some i => is_fp_instr i | None => false end.
Definition sym_step_tokF (st : shst) : tres :=
let ss := sh_ss st in
if is_fp_at ss then
match sym_stepF segs tbl ss with
| SRun ss' => TRun (advance st ss')
| SEcall _ => TStop SR_unsupported
| SStop why => TStop why
end
else
match sym_step_tokX segs tbl K Bx Bspan SH st with
| TRun st' =>
if Nat.eqb (sh_j st') (sh_j st) || regs_atoms_lt (K + sh_j st) (ss_fregs ss)
then TRun (with_fregs (ss_fregs ss) st') else TStop SR_unsupported
| TEcall _ => TStop SR_unsupported
| TStop why => TStop why
end.
Fixpoint sym_run_tokF (fuel : nat) (st : shst) : shst * trun_status :=
match fuel with
| O => (st, TS_running)
| S f => match sym_step_tokF st with
| TRun st' => sym_run_tokF f st'
| TEcall st' => (st', TS_ecall)
| TStop why => (st, TS_stopped why)
end
end.
Fixpoint sym_run_to_tokF (fuel : nat) (stop_pc : Z) (st : shst) : shst * trun_status :=
match fuel with
| O => (st, TS_running)
| S f => if ss_pc (sh_ss st) =? stop_pc then (st, TS_running) else
match sym_step_tokF st with
| TRun st' => sym_run_to_tokF f stop_pc st'
| TEcall st' => (st', TS_ecall)
| TStop why => (st, TS_stopped why)
end
end.
Definition sym_runN_tokF (n : N) (ss : sstate) := sym_run_tokF (N.to_nat n) (start K Bx Bspan SH ss).
Definition sym_run_toN_tokF (n : N) (stop : Z) (ss : sstate) := sym_run_to_tokF (N.to_nat n) stop (start K Bx Bspan SH ss).
End g.
Section h.
Variable segs : list Segment.
Variable tbl : ctable.
Variables (K : nat) (Bx : sv) (Bspan : Z * Z) (SH : list shent).
Hypothesis Htbl : table_ok segs tbl.
Local Abbreviation INVL fx := (@INV segs fx K Bx Bspan SH).
Definition INVF (final : list shob) (E : env) (st : shst) (ms : machine_state) : Prop :=
INVL (fp_of ms) final E st ms
/\ fregs_ok E (ss_fregs (sh_ss st)) (ms_fregs ms)
/\ frm_zero (ms_fcsr ms).
Lemma INVF_st_okF : forall final E st ms, INVF final E st ms -> st_okF segs E (sh_ss st) ms.
Proof.
intros final E st ms (HI & Hf & Hz). unfold INV in HI. destruct HI as (HS & _).
exact (st_ok_to_F segs (fp_of ms) E (sh_ss st) ms HS Hf Hz).
Qed.
Lemma INV_with_fregs : forall fx final E st ms sfr,
INVL fx final E st ms -> INVL fx final E (with_fregs sfr st) ms.
Proof. intros fx final E st ms sfr H. exact H. Qed.
Lemma fp_of_legacy_step : forall E ss ms ms',
@st_ok segs (fp_of ms) E ss ms' -> fp_of ms' = fp_of ms.
Proof.
intros E ss ms ms' (H1 & _ & _ & _ & H5 & _). cbn [fp_regs fp_csr fp_of] in H1, H5.
unfold fp_of. rewrite H1, H5. reflexivity.
Qed.
Lemma advance_soundF : forall final E st ss' ms ms',
INVF final E st ms ->
st_okF segs E ss' ms' ->
skeleton (ss_mem ss') = skeleton (ss_mem (sh_ss st)) ->
frame_of E (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms') ->
INVF final E (advance st ss') ms'.
Proof.
intros final E st ss' ms ms' (HI & _ & _) HS' Hsk HF.
unfold INV in HI. destruct HI as (_ & HT & HC & HN).
split; [| split; [exact (st_okF_fregs_ok segs E ss' ms' HS') | exact (st_okF_frm segs E ss' ms' HS')]].
unfold INV, advance; cbn [sh_ss sh_j sh_toks sh_chk sh_obls].
split; [exact (st_okF_to_legacy segs E ss' ms' HS')|]. split; [apply Forall_filter'; exact HT|]. split.
- intros Hchk. destruct (HC Hchk) as (Hst & Hat & Hsh & Htk & Hob).
split; [exact (static_sem_skeleton K Bx Bspan SH E _ _ Hsk Hst)|]. split; [exact Hat|]. split; [|split].
+ exact (sh_ok_frame segs K Bx Bspan SH E _ _ _ Hst HF Hsh).
+ apply Forall_filter'. rewrite Forall_forall in Htk |- *. intros tk Hin.
exact (tok_ok_frame segs K Bx Bspan SH E _ _ _ tk Hst HF (Htk tk Hin)).
+ exact (OBL_frame segs K Bx Bspan SH final E _ _ _ Hst HF Hob).
- intros Hchk. rewrite (HN Hchk). reflexivity.
Qed.
Lemma sym_step_tokF_doml : forall st st',
sym_step_tokF segs tbl K Bx Bspan SH st = TRun st' ->
doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
intros st st' H. unfold sym_step_tokF in H.
destruct (is_fp_at tbl (sh_ss st)).
- destruct (sym_stepF segs tbl (sh_ss st)) as [ss1|ss1|why]; try discriminate.
injection H as <-. cbn. split; [apply doml_refl | reflexivity].
- destruct (sym_step_tokX segs tbl K Bx Bspan SH st) as [st1|st1|why] eqn:Hs; try discriminate.
destruct (Nat.eqb (sh_j st1) (sh_j st) || regs_atoms_lt (K + sh_j st) (ss_fregs (sh_ss st))); [|discriminate].
injection H as <-. cbn [with_fregs sh_obls sh_chk].
exact (sym_step_tokX_doml segs tbl K Bx Bspan SH st st1 (or_introl Hs)).
Qed.
Theorem sym_step_tokF_sound : forall final E st st' ms,
INVF final E st ms -> sym_step_tokF segs tbl K Bx Bspan SH st = TRun st' -> doml (sh_obls st') final ->
exists ms' E',
msteps segs ms ms' /\ INVF final E' st' ms'
/\ ((sh_j st' = sh_j st /\ E' = E)
\/ (exists v, sh_j st' = S (sh_j st) /\ E' = ewset E (K + sh_j st) v /\ ss_atoms_lt (K + sh_j st) (sh_ss st) = true))
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of E (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
intros final E st st' ms HI H Hdom. unfold sym_step_tokF in H.
destruct (is_fp_at tbl (sh_ss st)).
-
destruct (sym_stepF segs tbl (sh_ss st)) as [ss1|ss1|why] eqn:Hs; try discriminate. injection H as <-.
pose proof (INVF_st_okF _ _ _ _ HI) as HSF.
destruct (sym_stepF_sound segs tbl Htbl E (sh_ss st) ss1 ms HSF Hs) as (ms1 & Hstep & HS1 & Hfr).
pose proof (sym_stepF_skeleton segs tbl (sh_ss st) ss1 Hs) as Hsk.
exists ms1, E. split.
{ apply msteps_one; [destruct HSF as (_ & _ & Hp & _); exact Hp | exact Hstep]. }
split; [exact (advance_soundF final E st ss1 ms ms1 HI HS1 Hsk Hfr)|].
split; [left; split; reflexivity|]. split; [exact Hsk|]. split; [exact Hfr | reflexivity].
-
destruct (sym_step_tokX segs tbl K Bx Bspan SH st) as [st1|st1|why] eqn:Hs; try discriminate.
destruct (Nat.eqb (sh_j st1) (sh_j st) || regs_atoms_lt (K + sh_j st) (ss_fregs (sh_ss st))) eqn:Hck; [|discriminate].
injection H as <-. cbn [with_fregs sh_obls] in Hdom.
destruct HI as (HI & Hf & Hz).
destruct (@sym_step_tokX_sound segs tbl (fp_of ms) K Bx Bspan SH Htbl final E st st1 ms HI Hs Hdom)
as (ms1 & E1 & Hms & HI1 & Hj & Hsk & Hfr & Hchk).
assert (Hfp : fp_of ms1 = fp_of ms).
{ pose proof HI1 as HI1'. unfold INV in HI1'. destruct HI1' as (HS1 & _). exact (fp_of_legacy_step E1 _ ms ms1 HS1). }
assert (Hfr1 : ms_fregs ms1 = ms_fregs ms) by (apply (f_equal (@fp_regs)) in Hfp; exact Hfp).
assert (Hcs1 : ms_fcsr ms1 = ms_fcsr ms) by (apply (f_equal (@fp_csr)) in Hfp; exact Hfp).
exists ms1, E1. split; [exact Hms|]. split.
{ split; [rewrite Hfp; apply INV_with_fregs; exact HI1|].
cbn [with_fregs set_fregs sh_ss ss_fregs]. rewrite Hfr1, Hcs1. split; [|exact Hz].
destruct Hj as [[_ ->] | (v & Hj & -> & _)]; [exact Hf|].
apply (fregs_ok_agree (K + sh_j st) E _ _ _ (env_agree_ewset _ _ _)); [|exact Hf].
rewrite Hj in Hck. rewrite (proj2 (Nat.eqb_neq _ _)) in Hck by lia. exact Hck. }
split; [exact Hj|]. split; [exact Hsk|]. split; [exact Hfr | exact Hchk].
Qed.
Lemma sym_step_tokF_noecall : forall st st', sym_step_tokF segs tbl K Bx Bspan SH st <> TEcall st'.
Proof.
intros st st' H. unfold sym_step_tokF in H.
destruct (is_fp_at tbl (sh_ss st)).
- destruct (sym_stepF segs tbl (sh_ss st)); discriminate.
- destruct (sym_step_tokX segs tbl K Bx Bspan SH st); try discriminate.
destruct (Nat.eqb _ _ || _); discriminate.
Qed.
Lemma sym_run_tokF_doml : forall fuel st st' r,
sym_run_tokF segs tbl K Bx Bspan SH fuel st = (st', r) -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros st st' r H; cbn [sym_run_tokF] in H.
- injection H as <- <-. split; [apply doml_refl | reflexivity].
- destruct (sym_step_tokF segs tbl K Bx Bspan SH st) as [st1|st1|why] eqn:Hs.
+ destruct (sym_step_tokF_doml st st1 Hs) as [Hd Hc]. destruct (IH st1 st' r H) as [Hd' Hc'].
split; [eapply doml_trans; eassumption | congruence].
+ exfalso. exact (sym_step_tokF_noecall st st1 Hs).
+ injection H as <- <-. split; [apply doml_refl | reflexivity].
Qed.
Lemma sym_run_to_tokF_doml : forall fuel stop st st' r,
sym_run_to_tokF segs tbl K Bx Bspan SH fuel stop st = (st', r) -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros stop st st' r H; cbn [sym_run_to_tokF] in H.
- injection H as <- <-. split; [apply doml_refl | reflexivity].
- destruct (ss_pc (sh_ss st) =? stop).
{ injection H as <- <-. split; [apply doml_refl | reflexivity]. }
destruct (sym_step_tokF segs tbl K Bx Bspan SH st) as [st1|st1|why] eqn:Hs.
+ destruct (sym_step_tokF_doml st st1 Hs) as [Hd Hc]. destruct (IH stop st1 st' r H) as [Hd' Hc'].
split; [eapply doml_trans; eassumption | congruence].
+ exfalso. exact (sym_step_tokF_noecall st st1 Hs).
+ injection H as <- <-. split; [apply doml_refl | reflexivity].
Qed.
Theorem sym_run_tokF_sound_gen : forall final fuel E0 ws st ms st' r,
INVF final (extK E0 K ws) st ms -> length ws = sh_j st ->
sym_run_tokF segs tbl K Bx Bspan SH fuel st = (st', r) ->
doml (sh_obls st') final ->
exists ws2 ms',
length (ws ++ ws2) = sh_j st' /\ msteps segs ms ms'
/\ INVF final (extK E0 K (ws ++ ws2)) st' ms' /\ r <> TS_ecall
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of (extK E0 K ws) (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros E0 ws st ms st' r HI Hlen H Hdom; cbn [sym_run_tokF] in H.
- injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [discriminate|].
split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
- destruct (sym_step_tokF segs tbl K Bx Bspan SH st) as [st1|st1|why] eqn:Hs.
+ assert (Hdom1 : doml (sh_obls st1) final).
{ eapply doml_trans; [exact (proj1 (sym_run_tokF_doml fuel st1 st' r H)) | exact Hdom]. }
destruct (sym_step_tokF_sound final _ st st1 ms HI Hs Hdom1) as (ms1 & E1 & Hms1 & HI1 & Hj & Hsk1 & Hfr1 & Hchk1).
assert (Hws1 : exists ws1, E1 = extK E0 K (ws ++ ws1) /\ length (ws ++ ws1) = sh_j st1).
{ destruct Hj as [[Hj ->] | (v & Hj & -> & _)].
- exists []. rewrite app_nil_r. split; [reflexivity | lia].
- exists [v]. rewrite extK_snoc, Hlen. split; [reflexivity|]. rewrite length_app. cbn. lia. }
destruct Hws1 as (ws1 & -> & Hlen1).
destruct (IH E0 (ws ++ ws1) st1 ms1 st' r HI1 Hlen1 H Hdom) as (ws2 & ms' & Hlen' & Hms & HR & Hne & Hsk & Hfr & Hchk).
exists (ws1 ++ ws2), ms'. rewrite app_assoc.
split; [exact Hlen'|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|]. split; [exact HR|]. split; [exact Hne|].
split; [congruence|]. split; [|congruence].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 |].
destruct Hj as [[Hj HE] | (v & Hj & HE & Hal)].
* destruct ws1 as [|v1 ws1']; [rewrite app_nil_r in Hfr; exact Hfr|].
exfalso. rewrite length_app in Hlen1. cbn in Hlen1. lia.
* assert (Hws1 : ws1 = [v]).
{ destruct ws1 as [|v1 [|v2 l]]; rewrite length_app in Hlen1; cbn in Hlen1; try lia.
rewrite <- Hlen in HE. apply (f_equal (fun E => ew E (K + length ws)%nat)) in HE. cbn beta in HE.
rewrite extK_snoc, !ew_ewset_same in HE. rewrite HE. reflexivity. }
subst ws1. rewrite extK_snoc, Hlen in Hfr.
eapply (frame_of_agree_skel (K + sh_j st) _ _ (ss_mem (sh_ss st))); [apply env_agree_ewset | | exact Hsk1 | exact Hfr].
unfold ss_atoms_lt in Hal. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [_ Hm]. exact Hm.
+ exfalso. exact (sym_step_tokF_noecall st st1 Hs).
+ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [discriminate|].
split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
Qed.
Theorem sym_run_to_tokF_sound_gen : forall final fuel stop E0 ws st ms st' r,
INVF final (extK E0 K ws) st ms -> length ws = sh_j st ->
sym_run_to_tokF segs tbl K Bx Bspan SH fuel stop st = (st', r) ->
doml (sh_obls st') final ->
exists ws2 ms',
length (ws ++ ws2) = sh_j st' /\ msteps segs ms ms'
/\ INVF final (extK E0 K (ws ++ ws2)) st' ms' /\ r <> TS_ecall
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of (extK E0 K ws) (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros stop E0 ws st ms st' r HI Hlen H Hdom; cbn [sym_run_to_tokF] in H.
- injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [discriminate|].
split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
- destruct (ss_pc (sh_ss st) =? stop).
{ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [discriminate|].
split; [reflexivity|]. split; [apply frame_of_refl | reflexivity]. }
destruct (sym_step_tokF segs tbl K Bx Bspan SH st) as [st1|st1|why] eqn:Hs.
+ assert (Hdom1 : doml (sh_obls st1) final).
{ eapply doml_trans; [exact (proj1 (sym_run_to_tokF_doml fuel stop st1 st' r H)) | exact Hdom]. }
destruct (sym_step_tokF_sound final _ st st1 ms HI Hs Hdom1) as (ms1 & E1 & Hms1 & HI1 & Hj & Hsk1 & Hfr1 & Hchk1).
assert (Hws1 : exists ws1, E1 = extK E0 K (ws ++ ws1) /\ length (ws ++ ws1) = sh_j st1).
{ destruct Hj as [[Hj ->] | (v & Hj & -> & _)].
- exists []. rewrite app_nil_r. split; [reflexivity | lia].
- exists [v]. rewrite extK_snoc, Hlen. split; [reflexivity|]. rewrite length_app. cbn. lia. }
destruct Hws1 as (ws1 & -> & Hlen1).
destruct (IH stop E0 (ws ++ ws1) st1 ms1 st' r HI1 Hlen1 H Hdom) as (ws2 & ms' & Hlen' & Hms & HR & Hne & Hsk & Hfr & Hchk).
exists (ws1 ++ ws2), ms'. rewrite app_assoc.
split; [exact Hlen'|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|]. split; [exact HR|]. split; [exact Hne|].
split; [congruence|]. split; [|congruence].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 |].
destruct Hj as [[Hj HE] | (v & Hj & HE & Hal)].
* destruct ws1 as [|v1 ws1']; [rewrite app_nil_r in Hfr; exact Hfr|].
exfalso. rewrite length_app in Hlen1. cbn in Hlen1. lia.
* assert (Hws1 : ws1 = [v]).
{ destruct ws1 as [|v1 [|v2 l]]; rewrite length_app in Hlen1; cbn in Hlen1; try lia.
rewrite <- Hlen in HE. apply (f_equal (fun E => ew E (K + length ws)%nat)) in HE. cbn beta in HE.
rewrite extK_snoc, !ew_ewset_same in HE. rewrite HE. reflexivity. }
subst ws1. rewrite extK_snoc, Hlen in Hfr.
eapply (frame_of_agree_skel (K + sh_j st) _ _ (ss_mem (sh_ss st))); [apply env_agree_ewset | | exact Hsk1 | exact Hfr].
unfold ss_atoms_lt in Hal. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [_ Hm]. exact Hm.
+ exfalso. exact (sym_step_tokF_noecall st st1 Hs).
+ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [discriminate|].
split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
Qed.
Lemma start_INVF : forall final E ss ms,
st_okF segs E ss ms -> sh_ok segs Bx SH E (ms_mem ms) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
Forall (ob_holds segs Bx E (ms_mem ms)) final ->
INVF final E (start K Bx Bspan SH ss) ms.
Proof.
intros final E ss ms HS Hsh Hchk Hfin. split; [|split].
- exact (@start_INV segs (fp_of ms) K Bx Bspan SH final E ss ms (st_okF_to_legacy segs E ss ms HS) Hsh Hchk Hfin).
- exact (st_okF_fregs_ok segs E ss ms HS).
- exact (st_okF_frm segs E ss ms HS).
Qed.
Theorem sym_run_tokF_sound : forall n E ss ms st' r,
st_okF segs E ss ms -> sh_ok segs Bx SH E (ms_mem ms) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tokF segs tbl K Bx Bspan SH n ss = (st', r) ->
Forall (ob_holds segs Bx E (ms_mem ms)) (sh_obls st') ->
exists ws ms',
length ws = sh_j st' /\ msteps segs ms ms'
/\ st_okF segs (extK E K ws) (sh_ss st') ms' /\ r <> TS_ecall
/\ sh_ok segs Bx SH (extK E K ws) (ms_mem ms')
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem ss)
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n E ss ms st' r HS Hsh Hchk H Hfin. unfold sym_runN_tokF in H.
destruct (sym_run_tokF_sound_gen (sh_obls st') (N.to_nat n) E [] (start K Bx Bspan SH ss) ms st' r
(start_INVF _ E ss ms HS Hsh Hchk Hfin) eq_refl H (doml_refl _)) as (ws & ms' & Hlen & Hms & HR & Hne & Hsk & Hfr & Hc).
cbn [app extK length start sh_ss sh_chk] in *. rewrite Hchk in Hc.
exists ws, ms'. split; [exact Hlen|]. split; [exact Hms|].
split; [exact (INVF_st_okF _ _ _ _ HR)|]. split; [exact Hne|].
destruct HR as (HI & _). unfold INV in HI. destruct HI as (_ & _ & HC & _).
split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
Qed.
Theorem sym_run_to_tokF_sound : forall n stop E ss ms st' r,
st_okF segs E ss ms -> sh_ok segs Bx SH E (ms_mem ms) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tokF segs tbl K Bx Bspan SH n stop ss = (st', r) ->
Forall (ob_holds segs Bx E (ms_mem ms)) (sh_obls st') ->
exists ws ms',
length ws = sh_j st' /\ msteps segs ms ms'
/\ st_okF segs (extK E K ws) (sh_ss st') ms' /\ r <> TS_ecall
/\ sh_ok segs Bx SH (extK E K ws) (ms_mem ms')
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem ss)
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n stop E ss ms st' r HS Hsh Hchk H Hfin. unfold sym_run_toN_tokF in H.
destruct (sym_run_to_tokF_sound_gen (sh_obls st') (N.to_nat n) stop E [] (start K Bx Bspan SH ss) ms st' r
(start_INVF _ E ss ms HS Hsh Hchk Hfin) eq_refl H (doml_refl _)) as (ws & ms' & Hlen & Hms & HR & Hne & Hsk & Hfr & Hc).
cbn [app extK length start sh_ss sh_chk] in *. rewrite Hchk in Hc.
exists ws, ms'. split; [exact Hlen|]. split; [exact Hms|].
split; [exact (INVF_st_okF _ _ _ _ HR)|]. split; [exact Hne|].
destruct HR as (HI & _). unfold INV in HI. destruct HI as (_ & _ & HC & _).
split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
Qed.
End h.
Ltac sym_why_tokF segs tbl K Bx Bspan SH st :=
let r := eval vm_compute in (sym_step_tokF segs tbl K Bx Bspan SH st) in
lazymatch r with
| TStop ?why => why
| _ => fail "sym_why_tokF: state is not stuck"
end.
