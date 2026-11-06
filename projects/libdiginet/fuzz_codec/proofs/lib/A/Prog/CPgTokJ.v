(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: tok_branch_j, its soundness proof and the run pieces below are the text of
   lib/Reusable/YCbn.v (tok_branch :238-290, tok_branch_doml :1358-1371, tok_branch_sound :1181-1343, sym_run_tok /
   sym_run_to_tok / sym_runN_tok / sym_run_toN_tok :307-328, their doml and soundness lemmas :1388-1410,
   :1485-1595, :1613-1662) and of lib/Reusable/YCbq.v (SRr_run_tok_AJ / SRr_run_to_tok_AJ :2513-2546, aj_run_tok /
   aj_run_to_tok :3119-3166) and lib/A/Prog/CPgWalk.v (cw_run / cw_run_ob / cw_run_to), renamed with the suffix j
   (prefix cwj_ for the walk tactics) and run over the extended step sym_step_tokj. *)
(* The token engine of lib/Reusable/YCbn.v, extended for the instrumented check whose slow path lies behind a jump:
     lb t,(x >> 3)+SB ; beqz t,FAST ; j SLOW        SLOW: andi u,x,7 ; bge u,t,ERR ; j FAST
   (the input-byte reads of the entry function, e.g. 0x80d2c-0x80d34 with SLOW = 0x82b74). YCbn's tok_branch looks
   for the slow block at the fall-through address only; when it finds a jump there it asks the whole 8-byte granule
   of x to be usable, which is false for a byte of a block's last partial granule. slow_block_j also follows that
   jump, so the check asks only the k + 1 bytes from x (one byte for these reads).
   WHY A COPY. tok_branch is called by name inside YCbn's sym_step_tok, so the step cannot be extended from outside:
   sym_step_tokj tries tok_branch_j first on a stuck branch and otherwise is YCbn's sym_step_tok; its soundness
   reuses YCbn's sym_step_tok_sound / _doml / _ecall for every other case. The run loops, their soundness, the AJ
   lemmas and the run tactics are copied (renamed) because each names its step. Every lemma tok_branch_j_sound
   needs (need_sound, check_passes_lb, slow_block_exec, st_ok_set_regs, the agree lemmas) is YCbn's, used as is.
   USE: cwj_run / cwj_run_ob / cwj_run_to take the arguments of CPgWalk's cw_run / cw_run_ob / cw_run_to; a stop at
   an undecided branch is split with CPgWalk's cw_branch as before (its stop reason does not depend on tokens). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CodecGlobs CPgWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the extended step ================================ *)
Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Context {fx : FPState}.
Variables (K : nat) (Bx : sv) (Bspan : Z * Z) (SH : list shent).
(* the slow block at L, or at the target of the jump at L *)
Definition slow_block_j (L Lz : Z) (t : Prelude.reg) : option (Prelude.reg * Prelude.reg * Z) :=
match slow_block tbl L Lz t with
| Some r => Some r
| None => match decp tbl as_j L with Some off => slow_block tbl (zcanon (L + off)) Lz t | None => None end
end.
(* YCbn's tok_branch with slow_block_j for slow_block; no answer where it has no slow block *)
Definition tok_branch_j (st : shst) (cnd : branch_cond) (rs1 rs2 : Prelude.reg) (imm : Z) : option shst :=
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
let '(Lnz, Lz) := match cnd with
| BC_NE => (zcanon (pc + imm), pc + 4)
| BC_EQ => (pc + 4, zcanon (pc + imm))
| _ => (0, 0) end in
match cnd with
| BC_NE | BC_EQ =>
match slow_block_j Lnz Lz rs1 with
| Some (u, xr, k) =>
if negb (sv_eqb (R xr) x) then None else
let U0 := (K + sh_j st)%nat in
if negb (ss_atoms_lt U0 ss) then None else
match need K Bx Bspan SH G x (k + 1) (sh_obls st) with
| None => None
| Some obls' =>
let ss' := setreg ss u (SOff U0 0) Lz in
Some (mkSH ss' (S (sh_j st)) (prune ss' (sh_toks st)) (sh_chk st) obls')
end
| None => None
end
| _ => None
end
end
| _ => None
end
end.
(* tok_branch_j first on a stuck branch, else YCbn's step *)
Definition sym_step_tokj (st : shst) : tres :=
let ss := sh_ss st in
match sym_step_sh segs tbl ss with
| SStop _ =>
match dec tbl (ss_pc ss) with
| Some (Branch cnd rs1 rs2 imm) =>
match tok_branch_j st cnd rs1 rs2 (bv_signed imm) with
| Some st' => TRun st'
| None => sym_step_tok segs tbl K Bx Bspan SH st
end
| _ => sym_step_tok segs tbl K Bx Bspan SH st
end
| _ => sym_step_tok segs tbl K Bx Bspan SH st
end.
Fixpoint sym_run_tokj (fuel : nat) (st : shst) : shst * trun_status :=
match fuel with
| O => (st, TS_running)
| S f => match sym_step_tokj st with
| TRun st' => sym_run_tokj f st'
| TEcall st' => (st', TS_ecall)
| TStop why => (st, TS_stopped why)
end
end.
Fixpoint sym_run_to_tokj (fuel : nat) (stop_pc : Z) (st : shst) : shst * trun_status :=
match fuel with
| O => (st, TS_running)
| S f => if ss_pc (sh_ss st) =? stop_pc then (st, TS_running) else
match sym_step_tokj st with
| TRun st' => sym_run_to_tokj f stop_pc st'
| TEcall st' => (st', TS_ecall)
| TStop why => (st, TS_stopped why)
end
end.
Definition sym_runN_tokj (n : N) (ss : sstate) := sym_run_tokj (N.to_nat n) (start K Bx Bspan SH ss).
Definition sym_run_toN_tokj (n : N) (stop : Z) (ss : sstate) := sym_run_to_tokj (N.to_nat n) stop (start K Bx Bspan SH ss).
End d.

(* ================================ soundness of the extended step ================================ *)
Section g.
Variable segs : list Segment.
Variable tbl : ctable.
Context {fx : FPState}.
Variables (K : nat) (Bx : sv) (Bspan : Z * Z) (SH : list shent).
Hypothesis Htbl : table_ok segs tbl.
Local Notation INV := (YCbn.INV segs K Bx Bspan SH).
Local Notation need := (YCbn.need K Bx Bspan SH).
Local Notation rd_of := (YCbn.rd_of segs).
Local Notation sh_atoms_lt := (sh_atoms_ltb Bx SH).
Local Notation sym_step_tok := (YCbn.sym_step_tok segs tbl K Bx Bspan SH).

Lemma slow_block_j_facts : forall L Lz t u xr k,
slow_block_j tbl L Lz t = Some (u, xr, k) -> bv_eqb u 0 = false /\ bv_eqb u t = false /\ 0 <= k <= 7.
Proof.
intros L Lz t u xr k H. unfold slow_block_j in H.
destruct (slow_block tbl L Lz t) as [[[u0 xr0] k0]|] eqn:Hs.
- injection H as -> -> ->.
  destruct (slow_block_facts tbl L Lz t u xr k Hs) as (L2 & _ & Hu0 & Hut & _ & Hk & _). auto.
- destruct (decp tbl as_j L) as [off|]; [|discriminate].
  destruct (slow_block_facts tbl _ Lz t u xr k H) as (L2 & _ & Hu0 & Hut & _ & Hk & _). auto.
Qed.

Lemma slow_block_j_exec : forall L Lz (t u xr : Prelude.reg) k regs mem x s,
slow_block_j tbl L Lz t = Some (u, xr, k) ->
getr regs xr = Z_to_bv 64 x -> 0 <= x < M64 ->
getr regs t = Z_to_bv 64 s -> 0 < s < 8 -> x mod 8 + k < s ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 L) mem (seg_rom segs)) (mkst regs' (Z_to_bv 64 Lz) mem (seg_rom segs))
/\ (forall r : Prelude.reg, r <> u -> getr regs' r = getr regs r).
Proof.
intros L Lz t u xr k regs mem x s H Hxr Hx Ht Hs Hlt. unfold slow_block_j in H.
destruct (slow_block tbl L Lz t) as [[[u0 xr0] k0]|] eqn:Hsb.
- injection H as <- <- <-. exact (slow_block_exec segs tbl Htbl L Lz t u0 xr0 k0 regs mem x s Hsb Hxr Hx Ht Hs Hlt).
- destruct (decp tbl as_j L) as [off|] eqn:HDj; [|discriminate].
  destruct (slow_block_exec segs tbl Htbl _ Lz t u xr k regs mem x s H Hxr Hx Ht Hs Hlt) as (regs' & Ms & Hfr).
  exists regs'. split; [|exact Hfr].
  destruct (decp_sound tbl as_j _ _ HDj) as (i3 & HD3' & Hi3).
  destruct (as_j_sound i3 _ Hi3) as (offc & -> & Hoffc).
  destruct (dec_sound segs tbl Htbl _ _ HD3') as (w3 & F3 & E3 & D3).
  eapply mst_step; [reflexivity| |exact Ms].
  rewrite (step_jal_x0 segs regs _ mem _ w3 offc F3 E3 D3). rewrite btgt_lit, Hoffc, Z_to_bv64_canon. reflexivity.
Qed.

Lemma tok_branch_j_doml : forall st cnd rs1 rs2 imm st',
tok_branch_j tbl K Bx Bspan SH st cnd rs1 rs2 imm = Some st' -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
intros st cnd rs1 rs2 imm st'. unfold tok_branch_j. destruct st as [ss j toks chk obls]; cbn.
repeat match goal with
|- context [match ?y with _ => _ end] =>
lazymatch y with
| YCbn.need _ _ _ _ ?G ?x ?n ?l => destruct y eqn:?
| _ => destruct y
end; try discriminate
end;
intros Hb; try discriminate; injection Hb as <-; cbn [sh_obls sh_chk];
(split; [first [apply doml_refl | eapply need_doml; eassumption] | reflexivity]).
Qed.

Lemma tok_branch_j_sound : forall final E st cnd rs1 rs2 (imm : bv 13) st' ms w,
INV final E st ms ->
fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
decode_any w = Some (Branch cnd rs1 rs2 imm, 4) ->
tok_branch_j tbl K Bx Bspan SH st cnd rs1 rs2 (bv_signed imm) = Some st' ->
doml (sh_obls st') final ->
exists ms' E',
msteps segs ms ms' /\ INV final E' st' ms'
/\ ((sh_j st' = sh_j st /\ E' = E)
\/ (exists v, sh_j st' = S (sh_j st) /\ E' = ewset E (K + sh_j st) v /\ ss_atoms_lt (K + sh_j st) (sh_ss st) = true))
/\ ss_mem (sh_ss st') = ss_mem (sh_ss st) /\ ms_mem ms' = ms_mem ms /\ ss_facts (sh_ss st') = ss_facts (sh_ss st).
Proof.
intros final E st cnd rs1 rs2 imm st' ms w HI Hf He Hd H Hdom.
destruct st as [ss j toks chk obls]. cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in *.
destruct HI as (HS & HT & HC & HN). cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in *.
unfold tok_branch_j in H. cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in H.
destruct (bv_eqb rs2 0) eqn:Hrs2; [|discriminate]. cbn [negb] in H. apply bv_eqb_eq in Hrs2. subst rs2.
destruct (ss_resv ss) as [rv|] eqn:Hrv; [discriminate|].
destruct (sr_get (ss_regs ss) rs1) as [|T z0| | | | | | | | |] eqn:HR1; try discriminate.
destruct (z0 =? 0) eqn:Hz0; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hz0. subst z0.
destruct (find_tok toks rs1 T) as [tk|] eqn:Htk; [|discriminate].
destruct (find_tok_sound _ _ _ _ Htk) as (Htkin & Htkr & HtkT).
destruct chk; [|rewrite (HN eq_refl) in Htkin; destruct Htkin].
destruct (HC eq_refl) as (Hst & Hat & Hsh & Htoks & Hob).
pose proof Hst as (Hwin & Hents & HK & Hspan).
assert (Htok : tok_ok segs K Bx Bspan E (ms_mem ms) tk) by (rewrite Forall_forall in Htoks; exact (Htoks tk Htkin)).
destruct Htok as (Hxk & Hcsp & b & Hb & Hv).
set (x := tk_x tk) in *.
remember (match cnd with
| BC_NE => (zcanon (ss_pc ss + bv_signed imm), ss_pc ss + 4)
| BC_EQ => (ss_pc ss + 4, zcanon (ss_pc ss + bv_signed imm))
| _ => (0, 0) end) as LL eqn:HLL.
destruct LL as [Lnz Lz].
assert (Hcnd : (cnd = BC_NE /\ Lnz = zcanon (ss_pc ss + bv_signed imm) /\ Lz = ss_pc ss + 4)
\/ (cnd = BC_EQ /\ Lnz = ss_pc ss + 4 /\ Lz = zcanon (ss_pc ss + bv_signed imm))).
{ destruct cnd; try discriminate; injection HLL as -> ->; auto. }
assert (H' : match slow_block_j tbl Lnz Lz rs1 with
| Some (u, xr, k) =>
if negb (sv_eqb (sr_get (ss_regs ss) xr) x) then None else
if negb (ss_atoms_lt (K + j) ss) then None else
match need (ss_facts ss) x (k + 1) obls with
| None => None
| Some obls' => Some (mkSH (setreg ss u (SOff (K + j) 0) Lz) (S j) (prune (setreg ss u (SOff (K + j) 0) Lz) toks) true obls')
end
| None => None
end = Some st').
{ destruct cnd; try discriminate; exact H. }
clear H. rename H' into H.
pose proof HS as HS0. destruct HS as (_ & Hpc & _ & _ & _ & _ & Hregs & Hmem & HG).
pose proof (YP03.st_ok_mkst segs E ss ms HS0 Hrv) as Hshape.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
assert (Ht : getr regs rs1 = cellval (tk_sg tk) b).
{ rewrite (Hregs rs1), HR1. cbn [sv_denot]. rewrite <- HtkT, Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
rewrite Hshape in Hf. cbn [ms_pc_val mkst] in Hf.
assert (Hrds : rd_of mem (shadow_of_addr (U E Bx) (U E x)) = Some (bv_unsigned b)).
{ unfold YCbn.rd_of, shadow_of_addr. unfold cell_x in Hb. rewrite Hb. reflexivity. }
pose proof (U_range E x) as HUx.
assert (ZERO : bv_unsigned b = 0 ->
msteps segs (mkst regs (Z_to_bv 64 (ss_pc ss)) mem (seg_rom segs)) (mkst regs (Z_to_bv 64 Lz) mem (seg_rom segs))).
{ intros Hb0.
assert (Ht0 : getr regs rs1 = Z_to_bv 64 0) by (rewrite Ht; apply (proj2 (cellval_zero_iff _ _)); exact Hb0).
apply msteps_one; [reflexivity|].
destruct Hcnd as [(-> & _ & ->) | (-> & _ & ->)].
+ rewrite (step_branch_ft_gen segs regs _ mem _ w BC_NE rs1 0 imm Hf He Hd); [rewrite v_addi_lit; reflexivity|].
cbn [branch_taken]. rewrite Ht0, getr_zero, bv_eqb_refl. reflexivity.
+ rewrite (step_branch_tk_gen segs regs _ mem _ w BC_EQ rs1 0 imm Hf He Hd); [rewrite btgt_lit, Z_to_bv64_canon; reflexivity|].
cbn [branch_taken]. rewrite Ht0, getr_zero, bv_eqb_refl. reflexivity. }
destruct (slow_block_j tbl Lnz Lz rs1) as [[[u xr] k]|] eqn:Hsb; [|discriminate].
destruct (sv_eqb (sr_get (ss_regs ss) xr) x) eqn:Hxr; [|discriminate]. cbn [negb] in H. apply sv_eqb_eq in Hxr.
destruct (ss_atoms_lt (K + j) ss) eqn:Hal; [|discriminate]. cbn [negb] in H.
destruct (need (ss_facts ss) x (k + 1) obls) as [obls'|] eqn:Hneed; [|discriminate]. injection H as <-.
cbn [sh_obls] in Hdom.
pose proof (slow_block_j_facts _ _ _ _ _ _ Hsb) as (Hu0 & Hut & Hk).
assert (Hune : u <> 0%bv) by (intros ->; rewrite bv_eqb_refl in Hu0; discriminate).
destruct (need_sound segs K Bx Bspan SH final E _ mem (ss_facts ss) x (k + 1) obls obls' Hst Hsh Hob HG Hneed Hdom ltac:(lia)) as [HRA _].
pose proof (check_passes_lb (rd_of mem) (U E Bx) (U E x) (k + 1) (U E x) (k + 1) (bv_unsigned b)
HRA ltac:(lia) ltac:(lia) ltac:(lia) Hrds) as Hpass.
assert (Hx : getr regs xr = Z_to_bv 64 (U E x)) by (rewrite (Hregs xr), Hxr, denot_lit_U; reflexivity).
assert (PATHS : exists regs', msteps segs (mkst regs (Z_to_bv 64 (ss_pc ss)) mem (seg_rom segs))
(mkst regs' (Z_to_bv 64 Lz) mem (seg_rom segs))
/\ (forall r, r <> u -> getr regs' r = getr regs r)).
{ destruct (Z.eq_dec (bv_unsigned b) 0) as [Hs0|Hs0].
- exists regs. split; [exact (ZERO Hs0) | intros; reflexivity].
- destruct Hpass as [Hz | [Hlt Hsr]]; [lia|].
assert (Hts : getr regs rs1 = Z_to_bv 64 (bv_unsigned b)) by (rewrite Ht; apply cellval_small; lia).
assert (Hne0 : bv_eqb (getr regs rs1) (getr regs 0) = false).
{ rewrite Hts, getr_zero. apply Bool.not_true_is_false. intros Hq. apply bv_eqb_eq in Hq.
apply (f_equal bv_unsigned) in Hq. rewrite !unsigned_lit_small in Hq by lia. lia. }
destruct (slow_block_j_exec Lnz Lz rs1 u xr k regs mem _ (bv_unsigned b) Hsb Hx ltac:(lia) Hts ltac:(lia) ltac:(lia))
as (regs' & Mslow & Hfr).
exists regs'. split; [|exact Hfr].
eapply mst_step; [reflexivity| |exact Mslow].
destruct Hcnd as [(-> & -> & _) | (-> & -> & _)].
+ rewrite (step_branch_tk_gen segs regs _ mem _ w BC_NE rs1 0 imm Hf He Hd); [rewrite btgt_lit, Z_to_bv64_canon; reflexivity|].
cbn [branch_taken]. rewrite Hne0. reflexivity.
+ rewrite (step_branch_ft_gen segs regs _ mem _ w BC_EQ rs1 0 imm Hf He Hd); [rewrite v_addi_lit; reflexivity|].
cbn [branch_taken]. exact Hne0. }
destruct PATHS as (regs' & Mp & Hfr).
set (U0 := (K + j)%nat) in *. set (v := getr regs' u). set (E' := ewset E U0 v).
assert (HA : env_agree U0 E E') by apply env_agree_ewset.
assert (HUK : (K <= U0)%nat) by lia.
exists (mkst regs' (Z_to_bv 64 Lz) mem (seg_rom segs)), E'.
split; [rewrite Hshape at 1; exact Mp|].
split; [|split; [right; exists v; split; [reflexivity | split; [reflexivity | first [exact Hal | reflexivity]]] | split; [reflexivity | split; reflexivity]]].
unfold INV; cbn [sh_ss sh_j sh_toks sh_chk sh_obls].
assert (Hat' : sh_atoms_lt U0 = true) by (apply (sh_atoms_lt_mono Bx SH K); [lia | exact Hat]).
split; [|split; [|split; [|intros; discriminate]]].
+ rewrite Hshape in HS0.
change (setreg ss u (SOff U0 0) Lz) with (set_regs_pc ss [(u, SOff U0 0)] Lz).
apply (st_ok_set_regs segs U0 E E' ss regs regs' _ Lz mem [(u, SOff U0 0)] HS0 HA Hal Hrv).
* reflexivity.
* intros r Hr. cbn in Hr. apply orb_false_elim in Hr as [Hr _]. apply Hfr. intros ->. rewrite bv_eqb_refl in Hr. discriminate.
* constructor; [|constructor]. cbn [fst snd]. split; [exact Hu0|].
cbn [sv_denot]. subst E'. rewrite ew_ewset_same, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ apply Forall_filter'. rewrite Forall_forall in HT |- *. intros tk0 Hin0. specialize (HT tk0 Hin0). lia.
+ intros _.
split; [|split; [exact Hat|split; [|split]]].
* eapply (static_sem_agree K Bx Bspan SH U0 E E'); [exact HA | exact Hat' | | exact Hst].
unfold ss_atoms_lt in Hal. apply andb_prop in Hal as [Hal2 _]. apply andb_prop in Hal2 as [Hal2 _]. apply andb_prop in Hal2 as [_ Hm2]. exact Hm2.
* exact (sh_ok_agree segs Bx SH U0 E E' _ HA Hat' Hsh).
* apply Forall_filter'. rewrite Forall_forall in Htoks, HT |- *. intros tk0 Hin0.
apply (tok_ok_agree segs K Bx Bspan SH U0 E E'); [exact HA | exact HUK | exact Hat' | exact (HT tk0 Hin0) | exact (Htoks tk0 Hin0)].
* exact (OBL_agree segs K Bx Bspan SH final U0 E E' _ HA HUK Hat' Hob).
Qed.

(* the step: tok_branch_j fired, or the step is YCbn's *)
Lemma sym_step_tokj_cases : forall st,
sym_step_tokj segs tbl K Bx Bspan SH st = sym_step_tok st \/
exists why cnd rs1 rs2 imm st', sym_step_sh segs tbl (sh_ss st) = SStop why /\
dec tbl (ss_pc (sh_ss st)) = Some (Branch cnd rs1 rs2 imm) /\
tok_branch_j tbl K Bx Bspan SH st cnd rs1 rs2 (bv_signed imm) = Some st' /\ sym_step_tokj segs tbl K Bx Bspan SH st = TRun st'.
Proof.
intros st. unfold sym_step_tokj.
destruct (sym_step_sh segs tbl (sh_ss st)) as [ss1|ss1|why] eqn:Hs; [left; reflexivity | left; reflexivity|].
destruct (dec tbl (ss_pc (sh_ss st))) as [i|] eqn:HD; [|left; reflexivity].
destruct i; try (left; reflexivity).
destruct (tok_branch_j tbl K Bx Bspan SH st c rs1 rs2 (bv_signed imm)) as [st'|] eqn:Hb; [|left; reflexivity].
right. exists why, c, rs1, rs2, imm, st'. repeat split; first [reflexivity | exact Hb | exact Hs | exact HD].
Qed.

Lemma sym_step_tokj_doml : forall st st',
(sym_step_tokj segs tbl K Bx Bspan SH st = TRun st' \/ sym_step_tokj segs tbl K Bx Bspan SH st = TEcall st') ->
doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
intros st st' H. destruct (sym_step_tokj_cases st) as [E|(why & cnd & rs1 & rs2 & imm & st1 & _ & _ & Hb & E)].
- rewrite E in H. exact (sym_step_tok_doml segs tbl K Bx Bspan SH st st' H).
- rewrite E in H. destruct H as [H|H]; [injection H as <- | discriminate]. exact (tok_branch_j_doml _ _ _ _ _ _ Hb).
Qed.

Lemma sym_run_tokj_doml : forall fuel st st' r,
sym_run_tokj segs tbl K Bx Bspan SH fuel st = (st', r) -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros st st' r H; cbn [sym_run_tokj] in H.
- injection H as <- <-. split; [apply doml_refl | reflexivity].
- destruct (sym_step_tokj segs tbl K Bx Bspan SH st) as [st1|st1|why] eqn:Hs.
+ destruct (sym_step_tokj_doml st st1 (or_introl Hs)) as [D1 C1]. destruct (IH _ _ _ H) as [D2 C2].
split; [exact (doml_trans _ _ _ D1 D2) | congruence].
+ injection H as <- <-. exact (sym_step_tokj_doml st st1 (or_intror Hs)).
+ injection H as <- <-. split; [apply doml_refl | reflexivity].
Qed.
Lemma sym_run_to_tokj_doml : forall fuel stop st st' r,
sym_run_to_tokj segs tbl K Bx Bspan SH fuel stop st = (st', r) -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros stop st st' r H; cbn [sym_run_to_tokj] in H.
- injection H as <- <-. split; [apply doml_refl | reflexivity].
- destruct (ss_pc (sh_ss st) =? stop); [injection H as <- <-; split; [apply doml_refl | reflexivity]|].
destruct (sym_step_tokj segs tbl K Bx Bspan SH st) as [st1|st1|why] eqn:Hs.
+ destruct (sym_step_tokj_doml st st1 (or_introl Hs)) as [D1 C1]. destruct (IH _ _ _ _ H) as [D2 C2].
split; [exact (doml_trans _ _ _ D1 D2) | congruence].
+ injection H as <- <-. exact (sym_step_tokj_doml st st1 (or_intror Hs)).
+ injection H as <- <-. split; [apply doml_refl | reflexivity].
Qed.

Theorem sym_step_tokj_sound : forall final E st st' ms,
INV final E st ms -> sym_step_tokj segs tbl K Bx Bspan SH st = TRun st' -> doml (sh_obls st') final ->
exists ms' E',
msteps segs ms ms' /\ INV final E' st' ms'
/\ ((sh_j st' = sh_j st /\ E' = E)
\/ (exists v, sh_j st' = S (sh_j st) /\ E' = ewset E (K + sh_j st) v /\ ss_atoms_lt (K + sh_j st) (sh_ss st) = true))
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of E (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
intros final E st st' ms HI H Hdom.
pose proof (proj2 (sym_step_tokj_doml st st' (or_introl H))) as Hchk.
destruct (sym_step_tokj_cases st) as [Eq|(why & cnd & rs1 & rs2 & imm & st1 & Hs & HD & Hb & Eq)].
- rewrite Eq in H. exact (sym_step_tok_sound segs tbl K Bx Bspan SH Htbl final E st st' ms HI H Hdom).
- rewrite Eq in H. injection H as <-.
pose proof HI as (HS & _).
destruct (dec_sound segs tbl Htbl _ _ HD) as (w & Hf & He & Hdi).
assert (Hf' : fetch_word segs (ms_pc_val ms) = Some w).
{ destruct HS as (_ & Hpc & _). rewrite Hpc. exact Hf. }
destruct (tok_branch_j_sound final E st cnd rs1 rs2 imm st1 ms w HI Hf' He Hdi Hb Hdom) as (ms' & E' & Hms & HI' & Hj & Hm1 & Hm2 & _).
exists ms', E'. split; [exact Hms|]. split; [exact HI'|]. split; [exact Hj|].
rewrite Hm1, Hm2. split; [reflexivity|]. split; [apply frame_of_refl | exact Hchk].
Qed.

Theorem sym_step_tokj_ecall : forall final E st st' ms,
INV final E st ms -> sym_step_tokj segs tbl K Bx Bspan SH st = TEcall st' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_ok_ecall segs E (sh_ss st') ms'
/\ ms_mem ms' = ms_mem ms /\ sh_ss st' = sh_ss st /\ sh_j st' = sh_j st /\ sh_chk st' = sh_chk st
/\ sh_obls st' = sh_obls st.
Proof.
intros final E st st' ms HI H.
destruct (sym_step_tokj_cases st) as [Eq|(why & cnd & rs1 & rs2 & imm & st1 & _ & _ & _ & Eq)].
- rewrite Eq in H. exact (sym_step_tok_ecall segs tbl K Bx Bspan SH Htbl final E st st' ms HI H).
- rewrite Eq in H. discriminate.
Qed.

Theorem sym_run_tokj_sound_gen : forall final fuel E0 ws st ms st' r,
INV final (extK E0 K ws) st ms -> length ws = sh_j st ->
sym_run_tokj segs tbl K Bx Bspan SH fuel st = (st', r) ->
doml (sh_obls st') final ->
exists ws2 ms',
length (ws ++ ws2) = sh_j st' /\ msteps segs ms ms'
/\ match r with
| TS_ecall => st_ok_ecall segs (extK E0 K (ws ++ ws2)) (sh_ss st') ms'
/\ (sh_chk st' = true -> sh_ok segs Bx SH (extK E0 K (ws ++ ws2)) (ms_mem ms'))
| _ => INV final (extK E0 K (ws ++ ws2)) st' ms'
end
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of (extK E0 K ws) (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros E0 ws st ms st' r HI Hlen H Hdom; cbn [sym_run_tokj] in H.
- injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
- destruct (sym_step_tokj segs tbl K Bx Bspan SH st) as [st1|st1|why] eqn:Hs.
+ assert (Hdom1 : doml (sh_obls st1) final).
{ eapply doml_trans; [exact (proj1 (sym_run_tokj_doml fuel st1 st' r H)) | exact Hdom]. }
destruct (sym_step_tokj_sound final _ st st1 ms HI Hs Hdom1) as (ms1 & E1 & Hms1 & HI1 & Hj & Hsk1 & Hfr1 & Hchk1).
assert (Hws1 : exists ws1, E1 = extK E0 K (ws ++ ws1) /\ length (ws ++ ws1) = sh_j st1).
{ destruct Hj as [[Hj ->] | (v & Hj & -> & _)].
- exists []. rewrite app_nil_r. split; [reflexivity | lia].
- exists [v]. rewrite extK_snoc, Hlen. split; [reflexivity|]. rewrite length_app. cbn. lia. }
destruct Hws1 as (ws1 & -> & Hlen1).
destruct (IH E0 (ws ++ ws1) st1 ms1 st' r HI1 Hlen1 H Hdom) as (ws2 & ms' & Hlen' & Hms & HR & Hsk & Hfr & Hchk).
exists (ws1 ++ ws2), ms'. rewrite app_assoc.
split; [exact Hlen'|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|]. split; [exact HR|].
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
+ injection H as <- <-.
destruct (sym_step_tokj_ecall final _ st st1 ms HI Hs) as (ms1 & Hstep & HS1 & Hm & Hss & Hj & Hchk & _).
exists [], ms1. rewrite app_nil_r.
split; [rewrite Hj; exact Hlen|]. split.
{ apply msteps_one; [destruct HI as ((_ & _ & Hp & _) & _); exact Hp | exact Hstep]. }
split.
{ split; [exact HS1|]. intros Hc. rewrite Hm. rewrite Hchk in Hc.
destruct HI as (_ & _ & HC & _). destruct (HC Hc) as (_ & _ & Hsh & _). exact Hsh. }
rewrite Hss, Hm. split; [reflexivity|]. split; [apply frame_of_refl | exact Hchk].
+ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
Qed.

Theorem sym_run_to_tokj_sound_gen : forall final fuel stop E0 ws st ms st' r,
INV final (extK E0 K ws) st ms -> length ws = sh_j st ->
sym_run_to_tokj segs tbl K Bx Bspan SH fuel stop st = (st', r) ->
doml (sh_obls st') final ->
exists ws2 ms',
length (ws ++ ws2) = sh_j st' /\ msteps segs ms ms'
/\ match r with
| TS_ecall => st_ok_ecall segs (extK E0 K (ws ++ ws2)) (sh_ss st') ms'
/\ (sh_chk st' = true -> sh_ok segs Bx SH (extK E0 K (ws ++ ws2)) (ms_mem ms'))
| _ => INV final (extK E0 K (ws ++ ws2)) st' ms'
end
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of (extK E0 K ws) (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros stop E0 ws st ms st' r HI Hlen H Hdom; cbn [sym_run_to_tokj] in H.
- injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
- destruct (ss_pc (sh_ss st) =? stop).
{ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity]. }
destruct (sym_step_tokj segs tbl K Bx Bspan SH st) as [st1|st1|why] eqn:Hs.
+ assert (Hdom1 : doml (sh_obls st1) final).
{ eapply doml_trans; [exact (proj1 (sym_run_to_tokj_doml fuel stop st1 st' r H)) | exact Hdom]. }
destruct (sym_step_tokj_sound final _ st st1 ms HI Hs Hdom1) as (ms1 & E1 & Hms1 & HI1 & Hj & Hsk1 & Hfr1 & Hchk1).
assert (Hws1 : exists ws1, E1 = extK E0 K (ws ++ ws1) /\ length (ws ++ ws1) = sh_j st1).
{ destruct Hj as [[Hj ->] | (v & Hj & -> & _)].
- exists []. rewrite app_nil_r. split; [reflexivity | lia].
- exists [v]. rewrite extK_snoc, Hlen. split; [reflexivity|]. rewrite length_app. cbn. lia. }
destruct Hws1 as (ws1 & -> & Hlen1).
destruct (IH stop E0 (ws ++ ws1) st1 ms1 st' r HI1 Hlen1 H Hdom) as (ws2 & ms' & Hlen' & Hms & HR & Hsk & Hfr & Hchk).
exists (ws1 ++ ws2), ms'. rewrite app_assoc.
split; [exact Hlen'|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|]. split; [exact HR|].
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
+ injection H as <- <-.
destruct (sym_step_tokj_ecall final _ st st1 ms HI Hs) as (ms1 & Hstep & HS1 & Hm & Hss & Hj & Hchk & _).
exists [], ms1. rewrite app_nil_r.
split; [rewrite Hj; exact Hlen|]. split.
{ apply msteps_one; [destruct HI as ((_ & _ & Hp & _) & _); exact Hp | exact Hstep]. }
split.
{ split; [exact HS1|]. intros Hc. rewrite Hm. rewrite Hchk in Hc.
destruct HI as (_ & _ & HC & _). destruct (HC Hc) as (_ & _ & Hsh & _). exact Hsh. }
rewrite Hss, Hm. split; [reflexivity|]. split; [apply frame_of_refl | exact Hchk].
+ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
Qed.

Theorem sym_run_tokj_sound : forall n E ss ms st' r,
st_ok segs E ss ms -> sh_ok segs Bx SH E (ms_mem ms) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tokj segs tbl K Bx Bspan SH n ss = (st', r) ->
Forall (ob_holds segs Bx E (ms_mem ms)) (sh_obls st') ->
exists ws ms',
length ws = sh_j st' /\ msteps segs ms ms'
/\ match r with
| TS_ecall => st_ok_ecall segs (extK E K ws) (sh_ss st') ms'
| _ => st_ok segs (extK E K ws) (sh_ss st') ms'
end
/\ sh_ok segs Bx SH (extK E K ws) (ms_mem ms')
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem ss)
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n E ss ms st' r HS Hsh Hchk H Hfin. unfold sym_runN_tokj in H.
destruct (sym_run_tokj_sound_gen (sh_obls st') (N.to_nat n) E [] (start K Bx Bspan SH ss) ms st' r
(start_INV segs K Bx Bspan SH _ E ss ms HS Hsh Hchk Hfin) eq_refl H (doml_refl _)) as (ws & ms' & Hlen & Hms & HR & Hsk & Hfr & Hc).
cbn [app extK length start sh_ss sh_chk] in *. rewrite Hchk in Hc.
exists ws, ms'. split; [exact Hlen|]. split; [exact Hms|].
destruct r.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
- destruct HR as [HS' Hsh']. split; [exact HS'|]. split; [exact (Hsh' Hc)|]. auto.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
Qed.
Theorem sym_run_to_tokj_sound : forall n stop E ss ms st' r,
st_ok segs E ss ms -> sh_ok segs Bx SH E (ms_mem ms) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tokj segs tbl K Bx Bspan SH n stop ss = (st', r) ->
Forall (ob_holds segs Bx E (ms_mem ms)) (sh_obls st') ->
exists ws ms',
length ws = sh_j st' /\ msteps segs ms ms'
/\ match r with
| TS_ecall => st_ok_ecall segs (extK E K ws) (sh_ss st') ms'
| _ => st_ok segs (extK E K ws) (sh_ss st') ms'
end
/\ sh_ok segs Bx SH (extK E K ws) (ms_mem ms')
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem ss)
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n stop E ss ms st' r HS Hsh Hchk H Hfin. unfold sym_run_toN_tokj in H.
destruct (sym_run_to_tokj_sound_gen (sh_obls st') (N.to_nat n) stop E [] (start K Bx Bspan SH ss) ms st' r
(start_INV segs K Bx Bspan SH _ E ss ms HS Hsh Hchk Hfin) eq_refl H (doml_refl _)) as (ws & ms' & Hlen & Hms & HR & Hsk & Hfr & Hc).
cbn [app extK length start sh_ss sh_chk] in *. rewrite Hchk in Hc.
exists ws, ms'. split; [exact Hlen|]. split; [exact Hms|].
destruct r.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
- destruct HR as [HS' Hsh']. split; [exact HS'|]. split; [exact (Hsh' Hc)|]. auto.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
Qed.
End g.

(* ================================ the runs on the journal ================================ *)
Section e0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Lemma SRr_run_tokj_AJ : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tokj segs tbl K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJ segs B W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_tokj_sound segs tbl K Bx Bspan SH tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply (SRr_chain_tok_AJ segs B LAWS segs_low Hwx);
[exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_to_tokj_AJ : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tokj segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJ segs B W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HS Hsh Hchk Hrun Hr HJ Hobl Hwr Hk.
destruct (sym_run_to_tokj_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply (SRr_chain_tok_AJ segs B LAWS segs_low Hwx);
[exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
Qed.
End e0.

(* ================================ the run tactics ================================ *)
Ltac aj_run_tokj tblok HS HJ SHOK Bspan :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_runN_tokj segs tbl K Bx Bspan SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tokj segs tbl K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HL := aj_laws in let HSL := aj_segs_low in let HWX := aj_wx in
eapply (SRr_run_tokj_AJ segs _ HL HSL tbl tblok HWX W FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
aj_after_run_tok HS HJ SHOK ]
end
end end
| _ => fail "aj_run_tokj: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
Ltac aj_run_to_tokj tblok HS HJ SHOK Bspan stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_tokj segs tbl K Bx Bspan SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tokj segs tbl K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HL := aj_laws in let HSL := aj_segs_low in let HWX := aj_wx in
eapply (SRr_run_to_tokj_AJ segs _ HL HSL tbl tblok HWX W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
aj_after_run_tok HS HJ SHOK ]
end
end end
| _ => fail "aj_run_to_tokj: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
(* CPgWalk's cw_run / cw_run_ob / cw_run_to on the extended engine, same arguments *)
Ltac cwj_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tokj tfibtbl_lib_ok HS HJ SHOK CW_Bspan; [ .. | awr | idtac ] end.
Ltac cwj_run_ob awr obl :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tokj tfibtbl_lib_ok HS HJ SHOK CW_Bspan; [ obl .. | awr | idtac ] end.
Ltac cwj_run_to awr stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tokj tfibtbl_lib_ok HS HJ SHOK CW_Bspan stop; [ .. | awr | idtac ] end.
