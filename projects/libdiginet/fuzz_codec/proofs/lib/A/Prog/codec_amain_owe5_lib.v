(* The led loop of OWE5 (RING) in the image-A walk of LLVMFuzzerTestOneInput, 0x824cc-0x82510 (fuzz_codec.c:179-182,
   owe_ring of lib/Prog/codec_owe.v): 14 passes with led = 2 .. 15 in a5, -led in a6, t2 = -16, t3 = 9, a0 = b; a pass
   tests bit led - 1 of b (0x824d8 beqz) and sets bit 8 - led of a3 (led <= 8) or bit 15 - led of a2. It reads and
   writes no memory and calls nothing.
   The test depends on b, so the executor would double its paths at each pass. o5_loop is the loop as one lemma over
   machine states, by induction on the passes left: each pass runs from a register-only executor state
   (CPgWalk.cw_entry0), the branches are decided by the pass's numbers, and the registers it leaves are the next
   pass's premises. A walk re-seats its own state after the loop with lib/Reusable/YI04.v st_ok_after_stretch over
   the clobber list O5_CLOB. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the loop's arithmetic ================================ *)
(* one pass of owe_ring, as owe_ring's own step *)
Definition o5_step (b : Z) : Z * Z -> Z -> Z * Z :=
fun '(p1, p2) led =>
  if Z.testbit b (led - 1) then
    if led <=? 8 then (Z.lor p1 (2 ^ (8 - led)), p2) else (p1, Z.lor p2 (2 ^ (15 - led)))
  else (p1, p2).
(* the accumulators after j passes *)
Definition o5_acc (b : Z) (j : nat) : Z * Z := fold_left (o5_step b) (map Z.of_nat (seq 2 j)) (0, 0).

Lemma o5_acc_14 : forall b, o5_acc b 14 = codec_owe.owe_ring b.
Proof. intros b. reflexivity. Qed.

Lemma o5_acc_S : forall b j, o5_acc b (S j) = o5_step b (o5_acc b j) (2 + Z.of_nat j).
Proof.
intros b j. unfold o5_acc. rewrite seq_S, map_app, fold_left_app. cbn [map fold_left].
f_equal. lia.
Qed.

Lemma o5_lor_lt : forall p k, 0 <= p < 128 -> 0 <= k <= 6 -> 0 <= Z.lor p (2 ^ k) < 128.
Proof.
intros p k Hp Hk.
assert (Hk2 : 0 < 2 ^ k <= 64) by (split; [apply Z.pow_pos_nonneg; lia | change 64 with (2 ^ 6); apply Z.pow_le_mono_r; lia]).
split; [apply Z.lor_nonneg; lia|].
assert (E : Z.lor p (2 ^ k) = Z.land (Z.lor p (2 ^ k)) (Z.ones 7)).
{ rewrite Z.land_lor_distr_l, !Z.land_ones by lia. change (2 ^ 7) with 128. rewrite !Z.mod_small by lia. reflexivity. }
rewrite E, Z.land_ones by lia. change (2 ^ 7) with 128. pose proof (Z.mod_pos_bound (Z.lor p (2 ^ k)) 128 ltac:(lia)). lia.
Qed.

Lemma o5_acc_range : forall b j, (j <= 14)%nat ->
0 <= fst (o5_acc b j) < 128 /\ 0 <= snd (o5_acc b j) < 128.
Proof.
intros b j. induction j as [|j IH]; intros Hj; [cbn; lia|].
rewrite o5_acc_S. destruct (o5_acc b j) as [p1 p2]. cbn [fst snd] in IH |- *.
destruct (IH ltac:(lia)) as [H1 H2]. unfold o5_step.
destruct (Z.testbit b (2 + Z.of_nat j - 1)); [|cbn; lia].
destruct (Z.leb_spec (2 + Z.of_nat j) 8); cbn [fst snd].
- split; [apply o5_lor_lt; lia | exact H2].
- split; [exact H1 | apply o5_lor_lt; lia].
Qed.

(* the executor's values, from a `SAluw` whose 32-bit result is r *)
Lemma o5_Uw : forall E op a b r, - 2 ^ 31 <= r < 2 ^ 31 ->
zalu_raw 31 32 op (U E a mod 2 ^ 32) (U E b mod 2 ^ 32) mod 2 ^ 32 = r mod 2 ^ 32 ->
U E (SAluw op a b) = r mod 2 ^ 64.
Proof.
intros E op a b r Hr H. rewrite U_of_S, S_SAluw.
set (x := zalu_raw 31 32 op (U E a mod 2 ^ 32) (U E b mod 2 ^ 32)) in *.
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
assert (Hx : (x + 2 ^ 31) mod 2 ^ 32 = r + 2 ^ 31).
{ rewrite Zplus_mod, H, <- Zplus_mod. apply Z.mod_small. lia. }
rewrite Hx. f_equal. lia.
Qed.

Lemma o5_U_soff : forall E n v o, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + o < 2 ^ 64 ->
U E (SOff n o) = v + o.
Proof.
intros E n v o Hn Hv Hvo. rewrite U_SOff, Hn, unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

Lemma o5_land1 : forall x k, 0 <= x -> 0 <= k ->
Z.land (Z.shiftr x k) 1 = if Z.testbit x k then 1 else 0.
Proof.
intros x k Hx Hk. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. rewrite Z.pow_1_r.
rewrite Zmod_odd. replace (Z.testbit x k) with (Z.testbit (Z.shiftr x k) 0)
  by (rewrite Z.shiftr_spec by lia; f_equal; lia).
rewrite Z.bit0_odd. reflexivity.
Qed.

(* 0x824cc-0x824d4: a7 = (b >>w (a5 - 1)) & 1 *)
Lemma o5_U_bit : forall E b led, ew E 10 = Z_to_bv 64 b -> ew E 15 = Z_to_bv 64 led ->
0 <= b < 2 ^ 16 -> 2 <= led <= 15 ->
U E (SAlu ALU_AND (SAluw ALU_SRL (SOff 10 0) (SOff 15 (-1))) (SLit 1)) = if Z.testbit b (led - 1) then 1 else 0.
Proof.
intros E b led E10 E15 Hb Hled.
assert (Hs : 0 <= Z.shiftr b (led - 1) < 2 ^ 16).
{ rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (led - 1) ltac:(lia) ltac:(lia)).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; nia]. }
assert (Ux : U E (SAluw ALU_SRL (SOff 10 0) (SOff 15 (-1))) = Z.shiftr b (led - 1)).
{ rewrite (o5_Uw E ALU_SRL _ _ (Z.shiftr b (led - 1))) by (try lia;
    rewrite (o5_U_soff E 10 b 0 E10) by lia; rewrite (o5_U_soff E 15 led (-1) E15) by lia;
    cbn [zalu_raw]; rewrite Z.add_0_r, (Z.mod_small b) by lia; rewrite (Z.mod_small (led + -1)) by lia;
    replace (Z.land (led + -1) 31) with (led - 1)
      by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 5) with 32; lia);
    reflexivity).
  apply Z.mod_small. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ux, U_lit by lia. rewrite o5_land1 by lia.
unfold zcanon, M64. destruct (Z.testbit b (led - 1)); reflexivity.
Qed.

(* 0x8250c addiw a5,a5,1 *)
Lemma o5_U_inc : forall E led, ew E 15 = Z_to_bv 64 led -> 2 <= led <= 15 ->
U E (SAluw ALU_ADD (SOff 15 0) (SLit 1)) = led + 1.
Proof.
intros E led E15 Hled.
rewrite (o5_Uw E ALU_ADD _ _ (led + 1)) by (try lia;
  rewrite (o5_U_soff E 15 led 0 E15) by lia; rewrite U_lit by lia; cbn [zalu_raw];
  rewrite Z.add_0_r; rewrite (Z.mod_small led) by lia; rewrite (Z.mod_small 1) by lia; reflexivity).
apply Z.mod_small. lia.
Qed.

(* 0x82508 addiw a6,a6,-1 *)
Lemma o5_U_dec : forall E led, ew E 16 = Z_to_bv 64 (2 ^ 64 - led) -> 2 <= led <= 15 ->
U E (SAluw ALU_ADD (SOff 16 0) (SLit (-1))) = 2 ^ 64 - (led + 1).
Proof.
intros E led E16 Hled.
rewrite (o5_Uw E ALU_ADD _ _ (- (led + 1))).
- change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia.
- lia.
- rewrite (o5_U_soff E 16 (2 ^ 64 - led) 0 E16) by lia. rewrite U_SLit. cbn [zalu_raw].
  unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

(* 0x824ec / 0x824f4: t0 = 1 <<w (o + a6), o = 8 or 15 *)
Lemma o5_U_t0 : forall E led o, ew E 16 = Z_to_bv 64 (2 ^ 64 - led) -> 2 <= led <= 15 -> 0 <= o - led <= 6 ->
U E (SAluw ALU_SLL (SLit 1) (SOff 16 o)) = 2 ^ (o - led).
Proof.
intros E led o E16 Hled Ho.
assert (Hp : 1 <= 2 ^ (o - led) <= 64)
  by (split; [apply (Z.pow_le_mono_r 2 0); lia | change 64 with (2 ^ 6); apply Z.pow_le_mono_r; lia]).
assert (Uo : U E (SOff 16 o) = o - led).
{ rewrite U_SOff, E16, unsigned_lit_small by lia. unfold zcanon, M64.
  replace (2 ^ 64 - led + o) with ((o - led) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite (o5_Uw E ALU_SLL _ _ (2 ^ (o - led))) by (try lia;
  rewrite Uo, U_lit by lia; cbn [zalu_raw]; rewrite (Z.mod_small 1) by lia; rewrite (Z.mod_small (o - led)) by lia;
  replace (Z.land (o - led) 31) with (o - led)
    by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 5) with 32; lia);
  rewrite Z.shiftl_1_l; reflexivity).
apply Z.mod_small. lia.
Qed.

Lemma o5_U_or : forall E n p led o, ew E n = Z_to_bv 64 p -> 0 <= p < 128 ->
ew E 16 = Z_to_bv 64 (2 ^ 64 - led) -> 2 <= led <= 15 -> 0 <= o - led <= 6 ->
U E (SAlu ALU_OR (SOff n 0) (SAluw ALU_SLL (SLit 1) (SOff 16 o))) = Z.lor p (2 ^ (o - led)).
Proof.
intros E n p led o En Hp E16 Hled Ho.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (o5_U_t0 E led o E16 Hled Ho), (U_atom E n p En) by lia.
pose proof (o5_lor_lt p (o - led) Hp Ho). unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* a register read off a state is the literal of its U *)
Lemma o5_reg : forall E e (x : word) v, x = sv_denot E e -> U E e = v -> x = Z_to_bv 64 v.
Proof. intros E e x v -> <-. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* ================================ registers a run keeps ================================ *)
Definition O5_CLOB : list (bv 5) := [5; 6; 12; 13; 15; 16; 17]%bv.
Definition o5_keep_b (sr : list sv) : bool :=
forallb (fun r => reg_in r O5_CLOB || sv_eqb (sr_get sr r) (sr_get sr_atoms r)) all_regs.

Section k. Context {fx : YK11.FPState}.
Lemma o5_keep : forall regs xs ss H ms, st_ok tfibsegs (Ereg regs xs) ss (restrict H ms) ->
o5_keep_b (ss_regs ss) = true -> forall r, reg_in r O5_CLOB = false -> getr (ms_regs ms) r = getr regs r.
Proof.
intros regs xs ss H ms HS Hk r Hr.
rewrite (st_ok_restrict_reg tfibsegs H _ ss ms r HS).
unfold o5_keep_b in Hk. rewrite forallb_forall in Hk. specialize (Hk r (all_regs_in r)).
rewrite Hr in Hk. cbn [orb] in Hk. rewrite (sv_eqb_eq _ _ Hk). symmetry. apply regs_ok_Ereg.
Qed.
End k.

(* ================================ the loop ================================ *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the memory a register-only run leaves: its restricted bytes are the old ones *)
Ltac o5_mem M :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict ?Hh (ms_mem ?ms2)) |- _ =>
  lazymatch type of M with forall x, mrestrict _ ?m1 x = mrestrict _ ?m0 x =>
    let M2 := fresh "M" in
    assert (M2 : forall x, mrestrict Hh (ms_mem ms2) x = mrestrict Hh m0 x)
      by (let x := fresh "x" in intros x; transitivity (mrestrict Hh m1 x); [apply HFr | apply M];
          let r := fresh "r" in let Hr := fresh "Hr" in intros (r & Hr & _); vm_compute in Hr; destruct Hr);
    clear M HFr; try (lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end);
    try (lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end);
    rename M2 into M end end.
Ltac o5_run M := cw_run ltac:(idtac; apply awr_ok_nil); o5_mem M.
Ltac o5_run_to M p := cw_run_to ltac:(idtac; apply awr_ok_nil) p; o5_mem M.
Ltac o5_rreg HS r Q :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  assert (Q : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms r HS) end.
(* the state's pc, computed, in a goal `SRr .. (mkCfg ms ..) ..` *)
Ltac o5_mkst :=
  lazymatch goal with HS : st_ok _ _ ?ssv (restrict _ ?msv) |- _ =>
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
    let p := eval vm_compute in (ss_pc ssv) in change (ss_pc ssv) with p end.

Lemma o5_loop : forall n j (W : world tfibsegs) regs mem md STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc k
(Q : world tfibsegs -> config -> Prop) b,
(j + n = 14)%nat -> (1 <= n)%nat -> 0 <= b < 2 ^ 16 ->
ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 10%bv = Z_to_bv 64 b ->
getr regs 13%bv = Z_to_bv 64 (fst (o5_acc b j)) -> getr regs 12%bv = Z_to_bv 64 (snd (o5_acc b j)) ->
getr regs 15%bv = Z_to_bv 64 (2 + Z.of_nat j) -> getr regs 16%bv = Z_to_bv 64 (2 ^ 64 - (2 + Z.of_nat j)) ->
getr regs 7%bv = Z_to_bv 64 (2 ^ 64 - 16) -> getr regs 28%bv = Z_to_bv 64 9 ->
(forall regs' mem' md',
  ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem' md' k ->
  (forall r, reg_in r O5_CLOB = false -> getr regs' r = getr regs r) ->
  getr regs' 13%bv = Z_to_bv 64 (fst (codec_owe.owe_ring b)) ->
  getr regs' 12%bv = Z_to_bv 64 (snd (codec_owe.owe_ring b)) ->
  (forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 0x82514) mem' (seg_rom tfibsegs)) md') Q) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x824cc) mem (seg_rom tfibsegs)) md) Q.
Proof.
induction n as [|n IH]; intros j W regs mem md STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc k Q b Hjn Hn1 Hb HJ
  R10 R13 R12 R15 R16 R7 R28 KC; [lia|].
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
assert (Hj14 : (j <= 13)%nat) by lia.
remember (2 + Z.of_nat j) as led eqn:Hledj. try rewrite <- Hledj in R15. try rewrite <- Hledj in R16.
assert (Hled : 2 <= led <= 15) by lia.
destruct (o5_acc_range b j ltac:(lia)) as (P1 & P2).
pose proof (o5_acc_S b j) as AS. try rewrite <- Hledj in AS.
pose proof (cw_entry0 0x824cc [] W regs mem) as HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [] (Ereg regs (cw_extra [])) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (KEEP0 : forall ss H ms, st_ok tfibsegs (Ereg regs (cw_extra [])) ss (restrict H ms) ->
  o5_keep_b (ss_regs ss) = true -> forall r, reg_in r O5_CLOB = false -> getr (ms_regs ms) r = getr regs r)
  by (intros ss H ms HS1; exact (o5_keep regs _ ss H ms HS1)).
remember (Ereg regs (cw_extra [])) as E eqn:HEE.
assert (E10 : ew E 10 = Z_to_bv 64 b) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E12 : ew E 12 = Z_to_bv 64 (snd (o5_acc b j))) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact R12).
assert (E13 : ew E 13 = Z_to_bv 64 (fst (o5_acc b j))) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact R13).
assert (E15 : ew E 15 = Z_to_bv 64 led) by (subst E; rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact R15).
assert (E16 : ew E 16 = Z_to_bv 64 (2 ^ 64 - led)) by (subst E; rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact R16).
assert (E7 : ew E 7 = Z_to_bv 64 (2 ^ 64 - 16)) by (subst E; rewrite (ew_Ereg_nat regs _ 7 7%bv eq_refl); exact R7).
assert (E28 : ew E 28 = Z_to_bv 64 9) by (subst E; rewrite (ew_Ereg_nat regs _ 28 28%bv eq_refl); exact R28).
clear HEE.
assert (U7 : U E (SOff 7 0) = 2 ^ 64 - 16) by (apply (U_atom E 7 _ E7); lia).
assert (U15 : U E (SOff 15 0) = led) by (apply (U_atom E 15 _ E15); lia).
assert (U28 : U E (SOff 28 0) = 9) by (apply (U_atom E 28 _ E28); lia).
assert (M : forall x, mrestrict (w_H W) mem x = mrestrict (w_H W) mem x) by reflexivity.
(* 0x824cc-0x824d8: the bit test *)
o5_run M.
cw_branch Hb1.
all: rewrite branch_eq_U, (o5_U_bit E b led E10 E15 Hb Hled), U_lit in Hb1 by lia.
all: destruct (Z.testbit b (led - 1)) eqn:Tb; cbn in Hb1; try discriminate.
- (* the bit is clear: 0x82508-0x82510 *)
  assert (AS' : o5_acc b (S j) = o5_acc b j) by (rewrite AS; destruct (o5_acc b j); unfold o5_step; cbn [fst snd]; rewrite Tb; reflexivity).
  o5_run M.
  cw_branch Hb2.
  all: rewrite branch_ne_U, (o5_U_dec E led E16 Hled), U7 in Hb2.
  + (* loop back *)
    apply negb_true_iff, Z.eqb_neq in Hb2.
    destruct n as [|n]; [exfalso; lia|].
    o5_run_to M 0x824cc.
    o5_rreg HS (10%bv : bv 5) Q10. o5_rreg HS (12%bv : bv 5) Q12. o5_rreg HS (13%bv : bv 5) Q13.
    o5_rreg HS (15%bv : bv 5) Q15. o5_rreg HS (16%bv : bv 5) Q16. o5_rreg HS (7%bv : bv 5) Q7. o5_rreg HS (28%bv : bv 5) Q28.
    o5_mkst.
    eapply (IH (S j)); [lia | lia | exact Hb | exact HJ | | | | | | | | ].
    * apply (o5_reg E _ _ _ Q10). apply (U_atom E 10 _ E10). lia.
    * rewrite AS'. apply (o5_reg E _ _ _ Q13). apply (U_atom E 13 _ E13). lia.
    * rewrite AS'. apply (o5_reg E _ _ _ Q12). apply (U_atom E 12 _ E12). lia.
    * apply (o5_reg E _ _ _ Q15). rewrite (o5_U_inc E led E15 Hled). lia.
    * apply (o5_reg E _ _ _ Q16). rewrite (o5_U_dec E led E16 Hled). lia.
    * apply (o5_reg E _ _ _ Q7). exact U7.
    * apply (o5_reg E _ _ _ Q28). exact U28.
    * intros regs' mem' md' HJ' Hk' V13 V12 M'. apply KC; [exact HJ' | | exact V13 | exact V12 |].
      -- intros r Hr. rewrite (Hk' r Hr). exact (KEEP0 _ _ _ HS ltac:(vm_compute; reflexivity) r Hr).
      -- intros x. rewrite M'. apply M.
  + (* the last pass: to 0x82514 *)
    apply negb_false_iff, Z.eqb_eq in Hb2.
    assert (Hj13 : j = 13%nat) by (lia).
    o5_run_to M 0x82514.
    o5_rreg HS (12%bv : bv 5) Q12. o5_rreg HS (13%bv : bv 5) Q13.
    o5_mkst.
    apply KC; [exact HJ | | | | exact M].
    * intros r Hr. exact (KEEP0 _ _ _ HS ltac:(vm_compute; reflexivity) r Hr).
    * rewrite <- o5_acc_14. replace 14%nat with (S j) by lia. rewrite AS'.
      apply (o5_reg E _ _ _ Q13). apply (U_atom E 13 _ E13). lia.
    * rewrite <- o5_acc_14. replace 14%nat with (S j) by lia. rewrite AS'.
      apply (o5_reg E _ _ _ Q12). apply (U_atom E 12 _ E12). lia.
- (* the bit is set: 0x824dc-0x824e4, the led <= 8 test *)
  o5_run M.
  cw_branch Hb2.
  all: rewrite branch_ltu_U, U15, U28 in Hb2.
  all: o5_run M.
  all: cw_branch Hb3.
  all: rewrite branch_ltu_U, U_lit, U15 in Hb3 by lia.
  all: try (apply Z.ltb_lt in Hb2); try (apply Z.ltb_ge in Hb2); try (apply Z.ltb_lt in Hb3); try (apply Z.ltb_ge in Hb3).
  all: try (exfalso; lia).
  all: o5_run M.
  all: cw_branch Hb4.
  all: rewrite branch_ne_U, (o5_U_dec E led E16 Hled), U7 in Hb4.
  + (* led <= 8, a3 updated, loop back *)
    apply negb_true_iff, Z.eqb_neq in Hb4.
    destruct n as [|n]; [exfalso; lia|].
    assert (AS' : o5_acc b (S j) = (Z.lor (fst (o5_acc b j)) (2 ^ (8 - led)), snd (o5_acc b j))).
    { rewrite AS. destruct (o5_acc b j). unfold o5_step. cbn [fst snd]. rewrite Tb.
      replace (led <=? 8) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    o5_run_to M 0x824cc.
    o5_rreg HS (10%bv : bv 5) Q10. o5_rreg HS (12%bv : bv 5) Q12. o5_rreg HS (13%bv : bv 5) Q13.
    o5_rreg HS (15%bv : bv 5) Q15. o5_rreg HS (16%bv : bv 5) Q16. o5_rreg HS (7%bv : bv 5) Q7. o5_rreg HS (28%bv : bv 5) Q28.
    o5_mkst.
    eapply (IH (S j)); [lia | lia | exact Hb | exact HJ | | | | | | | | ].
    * apply (o5_reg E _ _ _ Q10). apply (U_atom E 10 _ E10). lia.
    * rewrite AS'. apply (o5_reg E _ _ _ Q13). apply (o5_U_or E 13 _ led 8 E13 P1 E16 Hled). lia.
    * rewrite AS'. apply (o5_reg E _ _ _ Q12). apply (U_atom E 12 _ E12). lia.
    * apply (o5_reg E _ _ _ Q15). rewrite (o5_U_inc E led E15 Hled). lia.
    * apply (o5_reg E _ _ _ Q16). rewrite (o5_U_dec E led E16 Hled). lia.
    * apply (o5_reg E _ _ _ Q7). exact U7.
    * apply (o5_reg E _ _ _ Q28). exact U28.
    * intros regs' mem' md' HJ' Hk' V13 V12 M'. apply KC; [exact HJ' | | exact V13 | exact V12 |].
      -- intros r Hr. rewrite (Hk' r Hr). exact (KEEP0 _ _ _ HS ltac:(vm_compute; reflexivity) r Hr).
      -- intros x. rewrite M'. apply M.
  + (* led <= 8 cannot be the last pass *)
    apply negb_false_iff, Z.eqb_eq in Hb4. exfalso. lia.
  + (* led >= 9, a2 updated, loop back *)
    apply negb_true_iff, Z.eqb_neq in Hb4.
    destruct n as [|n]; [exfalso; lia|].
    assert (AS' : o5_acc b (S j) = (fst (o5_acc b j), Z.lor (snd (o5_acc b j)) (2 ^ (15 - led)))).
    { rewrite AS. destruct (o5_acc b j). unfold o5_step. cbn [fst snd]. rewrite Tb.
      replace (led <=? 8) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    o5_run_to M 0x824cc.
    o5_rreg HS (10%bv : bv 5) Q10. o5_rreg HS (12%bv : bv 5) Q12. o5_rreg HS (13%bv : bv 5) Q13.
    o5_rreg HS (15%bv : bv 5) Q15. o5_rreg HS (16%bv : bv 5) Q16. o5_rreg HS (7%bv : bv 5) Q7. o5_rreg HS (28%bv : bv 5) Q28.
    o5_mkst.
    eapply (IH (S j)); [lia | lia | exact Hb | exact HJ | | | | | | | | ].
    * apply (o5_reg E _ _ _ Q10). apply (U_atom E 10 _ E10). lia.
    * rewrite AS'. apply (o5_reg E _ _ _ Q13). apply (U_atom E 13 _ E13). lia.
    * rewrite AS'. apply (o5_reg E _ _ _ Q12). apply (o5_U_or E 12 _ led 15 E12 P2 E16 Hled). lia.
    * apply (o5_reg E _ _ _ Q15). rewrite (o5_U_inc E led E15 Hled). lia.
    * apply (o5_reg E _ _ _ Q16). rewrite (o5_U_dec E led E16 Hled). lia.
    * apply (o5_reg E _ _ _ Q7). exact U7.
    * apply (o5_reg E _ _ _ Q28). exact U28.
    * intros regs' mem' md' HJ' Hk' V13 V12 M'. apply KC; [exact HJ' | | exact V13 | exact V12 |].
      -- intros r Hr. rewrite (Hk' r Hr). exact (KEEP0 _ _ _ HS ltac:(vm_compute; reflexivity) r Hr).
      -- intros x. rewrite M'. apply M.
  + (* led >= 9, the last pass *)
    apply negb_false_iff, Z.eqb_eq in Hb4.
    assert (Hj13 : j = 13%nat) by (lia).
    assert (AS' : o5_acc b (S j) = (fst (o5_acc b j), Z.lor (snd (o5_acc b j)) (2 ^ (15 - led)))).
    { rewrite AS. destruct (o5_acc b j). unfold o5_step. cbn [fst snd]. rewrite Tb.
      replace (led <=? 8) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    o5_run_to M 0x82514.
    o5_rreg HS (12%bv : bv 5) Q12. o5_rreg HS (13%bv : bv 5) Q13.
    o5_mkst.
    apply KC; [exact HJ | | | | exact M].
    * intros r Hr. exact (KEEP0 _ _ _ HS ltac:(vm_compute; reflexivity) r Hr).
    * rewrite <- o5_acc_14. replace 14%nat with (S j) by lia. rewrite AS'.
      apply (o5_reg E _ _ _ Q13). apply (U_atom E 13 _ E13). lia.
    * rewrite <- o5_acc_14. replace 14%nat with (S j) by lia. rewrite AS'.
      apply (o5_reg E _ _ _ Q12). apply (o5_U_or E 12 _ led 15 E12 P2 E16 Hled). lia.
Qed.
End b.
