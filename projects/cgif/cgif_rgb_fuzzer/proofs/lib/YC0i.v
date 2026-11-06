(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20 YI1k YI1h YI16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC1b YC2q YC2u YC4r YC13 YC2o YC16 YC12 YC20 YC3q YC0u YC0w YC0v YC0q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma val_mem_byte1B : forall H mem a v, aview trasegs H mem a = Some v -> val_mem trasegs (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv. destruct (aview_byte trasegs H mem a v Hv) as (b & Hb & -> & Hr).
intros j Hj. destruct j; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YP0g.le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite (Z.mod_small (bv_unsigned b) 256) by (clear - Hr; lia). rewrite (Z.mod_small (bv_unsigned b) 256) by (clear - Hr; lia).
rewrite (Z.mod_small (bv_unsigned b) 256) by (clear - Hr; lia). reflexivity.
Qed.
Lemma block_byte_val : forall H mem a, apresent H mem a ->
exists v, aview trasegs H mem a = Some v /\ val_mem trasegs (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
intros H mem a Hp. destruct (aview trasegs H mem a) as [v|] eqn:Hv; [| exfalso; exact (aview_some_of_apresent trasegs H mem a Hp Hv)].
exists v. split; [reflexivity|]. split; [exact (val_mem_byte1B H mem a v Hv)|].
destruct (aview_byte trasegs H mem a v Hv) as (b & _ & _ & Hr). exact Hr.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma st_ok_rebase : forall k (Ex : env) ss ms (sr : list sv) (vals : list word),
st_ok trasegs Ex ss ms -> ss_resv ss = None ->
mem_atoms_lt k (ss_mem ss) && facts_atoms_lt k (ss_facts ss) = true ->
(forall r : bv 5, (sv_atoms_lt k (sr_get sr r) = true /\ sr_get sr r = sr_get (ss_regs ss) r)
\/ (exists (i : nat) (w : word), sr_get sr r = SOff (k + i) 0 /\ nth_error vals i = Some w /\ getr (ms_regs ms) r = w)) ->
st_ok trasegs (havoc Ex k vals) (mkSST (ss_pc ss) sr (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros k Ex ss ms sr vals (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hrv Hlt Hregs.
apply andb_prop in Hlt as [Hm Hf].
pose proof (env_agree_havoc_ge k k Ex Ex vals ltac:(lia) (env_agree_refl k Ex)) as HA.
unfold st_ok; cbn. rewrite Hrv in H4 |- *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
split; [| split; [eapply mem_ok_agree; [exact HA | exact Hm | exact H8] | eapply facts_ok_agree; [exact HA | exact Hf | exact H9]]].
intros r. destruct (Hregs r) as [[Hat Heq] | (i & w & Heq & Hnth & Hr)].
- rewrite Heq in Hat. rewrite Heq. rewrite (sv_denot_agree k Ex _ _ HA Hat). apply H7.
- rewrite Heq, Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (YO3v.ew_havoc_new Ex k vals i (Z_to_bv 64 0)) by (apply (proj1 (nth_error_Some vals i)); rewrite Hnth; discriminate).
symmetry. exact (nth_error_nth vals i _ Hnth).
Qed.
End c.
Fixpoint find_reg_atom (sr : list sv) (n : nat) (rs : list (bv 5)) : option (bv 5) :=
match rs with
| [] => None
| r :: rs' => if sv_eqb (sr_get sr r) (SOff n 0) then Some r else find_reg_atom sr n rs'
end.
Fixpoint rebase_regs_from (sr : list sv) (k i fuel : nat) : list (option (bv 5)) :=
match fuel with
| O => []
| S f => match find_reg_atom sr (k + i) all_regs with
| Some r => Some r :: rebase_regs_from sr k (S i) f
| None => []
end
end.
Ltac rejoin_reg HS k vals :=
lazymatch goal with |- (sv_atoms_lt _ (sr_get ?sr ?r) = true /\ _) \/ _ =>
let e := eval vm_compute in (sr_get sr r) in
change (sr_get sr r) with e;
first
[ left; split; [vm_compute; reflexivity | vm_compute; reflexivity]
| lazymatch e with SOff ?n 0 =>
let i := eval vm_compute in (n - k)%nat in
right; exists i; eexists; split; [reflexivity|]; split; [reflexivity|];
cbn [ms_regs restrict mkst];
first [ reflexivity
| lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?Hh ?msq) =>
lazymatch goal with |- getr _ _ = getr _ ?rep =>
rewrite (st_ok_restrict_reg trasegs Hh Ex ssx msq r HS), (st_ok_restrict_reg trasegs Hh Ex ssx msq rep HS);
let e1 := eval vm_compute in (sr_get (ss_regs ssx) r) in
let e2 := eval vm_compute in (sr_get (ss_regs ssx) rep) in
change (sr_get (ss_regs ssx) r) with e1; change (sr_get (ss_regs ssx) rep) with e2; reflexivity end end ] end
| idtac "REJOIN-REG-FAIL" r e; fail ] end.
Ltac af_rejoin HS target k :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem trasegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trasegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let sr := eval cbn [ss_regs] in (ss_regs tg) in
let dl := eval vm_compute in (rebase_regs_from sr k 0 32) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs msx) in
let vals := eval cbn [map] in (map (fun o : option (bv 5) => match o with Some r => getr rg r | None => Z_to_bv 64 0 end) dl) in
pose proof (st_ok_rebase k Ex ssx msx sr vals HS eq_refl ltac:(vm_compute; reflexivity)
ltac:(refine (reg_cases_lit _ _); let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbv [all_regs In] in Hr;
repeat (destruct Hr as [<- | Hr]; [rejoin_reg HS k vals |]); destruct Hr)) as HS3;
clear HS; rename HS3 into HS end;
cbn [ss_pc ss_fregs ss_mem ss_resv ss_facts] in HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
Ltac awr_b_rec Usp E32u Hing HTS hd Bhd Hfb Hfq :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YQ0b.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := 0);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |]
| |- awr_ok _ (YQ0b.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32u | exact Hing | cbn [YQ0b.r_wlo]; lia
| cbn [YQ0b.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; unfold FPa, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| ]
| |- awr_ok _ (YQ0b.mkRegion (Some hd) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
lazymatch type of Bhd with _ = ?p =>
eapply awr_ok_cons_block with (n := hd) (m := FRAME_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact Bhd | exact Hfb | cbn [YQ0b.r_wlo]; lia
| cbn [YQ0b.r_whi]; change (req_size FRAME_SIZE) with 40; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; unfold FPa, ablocks_fp;
exists (p, p + req_size FRAME_SIZE); split;
[ apply (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ (p, FRAME_SIZE)); exact Hfq
| cbn [fst snd]; change (req_size FRAME_SIZE) with 40; lia ]
| ] end
end
| fail 1 "awr_b: no rule for the head region" ];
awr_b_rec Usp E32u Hing HTS hd Bhd Hfb Hfq
end.
Ltac awr_b Usp E32u Hing HTS hd Bhd Hfb Hfq :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_b_rec Usp E32u Hing HTS hd Bhd Hfb Hfq.
Section h. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition af_hdr (hd : nat) : YQ0b.region :=
YQ0b.mkRegion (Some hd) 0 40 24 24
[YQ0b.mkChunk 8 (CVal 8 (SOff 70 0)); YQ0b.mkChunk 16 (CVal 4 (SOff 71 0)); YQ0b.mkChunk 24 (CVal 2 (SOff 72 0))].
Definition af_SHB (hd : nat) : list shent := af_SH ++ [mkSHE hd 0 FRAME_SIZE].
Definition ss_BX (ih ho : Z) (hd : nat) : sstate :=
add_atom (add_atom (add_atom
(mkSS AF_B (ss_regs (ss_B ih ho hd)) (af_hdr hd :: ss_mem (ss_B ih ho hd)) None (ss_facts (ss_B ih ho hd)))
hd hfactA) 71 (mkAF 0 4294967295 0)) 72 (mkAF 0 65535 0).
Definition ss_L0 (ih ho : Z) (hd : nat) : sstate :=
(mkSS AF_LOOP
[SLit 0; SOff 200 0; SOff 2 (-224); SOff 3 0; SOff 4 0; SOff 201 0; SOff 202 0; SOff 203 0; SOff 32 88; shq 32 88; SOff 205 0; SOff 206 0; SOff 207 0; SOff 208 0; SOff 209 0; SOff 46 0; SOff 210 0; SOff 211 0; SOff 32 0; SOff 213 0; SOff 204 0; shq 32 ho; SOff 38 0; SOff 32 ho; SLit ih; SOff 214 0; SOff 214 0; SOff 213 0; SOff 212 0; SOff 215 0; SOff 216 0; SOff 217 0]
[{|
r_base := Some 2%nat;
r_lo := -224;
r_hi := -104;
r_wlo := -224;
r_whi := -104;
r_chunks :=
[{| c_off := -216; YQ0b.c_val := CVal 8 (SAlu ALU_ADD (SOff 72 0) (SExt false 16 (SOff 51 0))) |};
{| c_off := -200; YQ0b.c_val := CVal 8 (SOff hd 24) |};
{| c_off := -208; YQ0b.c_val := CVal 8 (shq hd 24) |};
{| c_off := -112; YQ0b.c_val := CVal 8 (SOff hd 0) |};
{| c_off := -120; YQ0b.c_val := CVal 8 (SOff 46 0) |};
{| c_off := -128; YQ0b.c_val := CVal 8 (SOff 46 24) |};
{| c_off := -152; YQ0b.c_val := CVal 8 (SLit ho) |};
{| c_off := -184; YQ0b.c_val := CVal 8 (SOff 32 92) |};
{| c_off := -192; YQ0b.c_val := CVal 8 (shq 32 92) |};
{| c_off := -160; YQ0b.c_val := CVal 8 (SOff 67 0) |};
{| c_off := -136; YQ0b.c_val := CVal 8 (SOff 46 16) |};
{| c_off := -144; YQ0b.c_val := CVal 8 (shq 46 16) |};
{| c_off := -168; YQ0b.c_val := CVal 8 (SOff 32 40) |};
{| c_off := -176; YQ0b.c_val := CVal 8 (shq 32 40) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YQ0b.c_val := CVal 8 (SOff 27 0) |};
{| c_off := -96; YQ0b.c_val := CVal 8 (SOff 26 0) |};
{| c_off := -88; YQ0b.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YQ0b.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YQ0b.c_val := CVal 8 (SOff 23 0) |};
{| c_off := -64; YQ0b.c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; YQ0b.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YQ0b.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YQ0b.c_val := CVal 8 (SOff 19 0) |};
{| c_off := -32; YQ0b.c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; YQ0b.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YQ0b.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YQ0b.c_val := CVal 8 (SOff 1 0) |}]
|};
{|
r_base := None;
r_lo := 663904;
r_hi := 663912;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 663904; YQ0b.c_val := CVal 8 (SLit 696760) |}]
|};
{|
r_base := None;
r_lo := 696760;
r_hi := 696768;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 696760; YQ0b.c_val := CVal 8 (SOff 38 0) |}]
|};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 88;
r_whi := 92;
r_chunks :=
[{| c_off := 0; YQ0b.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 8; YQ0b.c_val := CVal 8 (SOff 34 0) |};
{| c_off := 16; YQ0b.c_val := CVal 8 (SOff 35 0) |};
{| c_off := 24; YQ0b.c_val := CVal 8 (SOff 39 0) |};
{| c_off := 40; YQ0b.c_val := CVal 4 (SOff 40 0) |};
{| c_off := 44; YQ0b.c_val := CVal 4 (SOff 41 0) |};
{| c_off := 48; YQ0b.c_val := CVal 2 (SOff 42 0) |};
{| c_off := 50; YQ0b.c_val := CVal 2 (SOff 43 0) |};
{| c_off := 52; YQ0b.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 54; YQ0b.c_val := CVal 2 (SOff 45 0) |};
{| c_off := 56; YQ0b.c_val := CVal 8 (SLit 529828) |};
{| c_off := 64; YQ0b.c_val := CVal 8 (SLit 0) |};
{| c_off := 72; YQ0b.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 80; YQ0b.c_val := CVal 8 (SLit 0) |};
{| c_off := 88; YQ0b.c_val := CVal 4 (SOff 37 0) |};
{| c_off := 92; YQ0b.c_val := CVal 4 (SLit ih) |}]
|};
{|
r_base := Some 46%nat;
r_lo := 0;
r_hi := 32;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YQ0b.c_val := CVal 8 (SOff 47 0) |};
{| c_off := 8; YQ0b.c_val := CVal 8 (SOff 48 0) |};
{| c_off := 16; YQ0b.c_val := CVal 4 (SOff 49 0) |};
{| c_off := 20; YQ0b.c_val := CVal 4 (SOff 50 0) |};
{| c_off := 24; YQ0b.c_val := CVal 2 (SOff 51 0) |};
{| c_off := 26; YQ0b.c_val := CVal 2 (SOff 52 0) |};
{| c_off := 28; YQ0b.c_val := CVal 1 (SOff 53 0) |}]
|}]
None
{|
f_atoms :=
[(72%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(71%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(hd,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 4
|});
(2%nat,
{|
af_lo := 70368744177664;
af_hi := 140737488355328;
af_al2 := 4
|});
(32%nat,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 4
|});
(38%nat,
{| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(46%nat,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 3
|})];
f_conds := [];
f_alias := []
|}).
Definition ss_SM (ih ho : Z) (hd : nat) : sstate :=
(mkSS AF_SAME
[SLit 0; SOff 200 0; SOff 2 (-224); SOff 3 0; SOff 4 0; SOff 201 0; SOff 202 0; SOff 203 0; SOff 32 88; shq 32 88; SOff 204 0; SOff 205 0; SOff 206 0; SOff 207 0; SOff 208 0; SOff 209 0; SOff 210 0; SOff 211 0; SOff 32 0; SOff 212 0; SOff 213 0; shq 32 ho; SOff 38 0; SOff 32 ho; SLit ih; SOff 214 0; SOff 215 0; SOff 216 0; SOff 217 0; SOff 218 0; SOff 219 0; SOff 220 0]
[{|
r_base := Some hd;
r_lo := 0;
r_hi := 40;
r_wlo := 24;
r_whi := 24;
r_chunks :=
[{| c_off := 8; YQ0b.c_val := CVal 8 (SOff 70 0) |};
{| c_off := 16; YQ0b.c_val := CVal 4 (SOff 71 0) |};
{| c_off := 24; YQ0b.c_val := CVal 2 (SOff 72 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -224;
r_hi := -104;
r_wlo := -224;
r_whi := -104;
r_chunks :=
[{| c_off := -216; YQ0b.c_val := CVal 8 (SAlu ALU_ADD (SOff 72 0) (SExt false 16 (SOff 51 0))) |};
{| c_off := -200; YQ0b.c_val := CVal 8 (SOff hd 24) |};
{| c_off := -208; YQ0b.c_val := CVal 8 (shq hd 24) |};
{| c_off := -112; YQ0b.c_val := CVal 8 (SOff hd 0) |};
{| c_off := -120; YQ0b.c_val := CVal 8 (SOff 46 0) |};
{| c_off := -128; YQ0b.c_val := CVal 8 (SOff 46 24) |};
{| c_off := -152; YQ0b.c_val := CVal 8 (SLit ho) |};
{| c_off := -184; YQ0b.c_val := CVal 8 (SOff 32 92) |};
{| c_off := -192; YQ0b.c_val := CVal 8 (shq 32 92) |};
{| c_off := -160; YQ0b.c_val := CVal 8 (SOff 67 0) |};
{| c_off := -136; YQ0b.c_val := CVal 8 (SOff 46 16) |};
{| c_off := -144; YQ0b.c_val := CVal 8 (shq 46 16) |};
{| c_off := -168; YQ0b.c_val := CVal 8 (SOff 32 40) |};
{| c_off := -176; YQ0b.c_val := CVal 8 (shq 32 40) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YQ0b.c_val := CVal 8 (SOff 27 0) |};
{| c_off := -96; YQ0b.c_val := CVal 8 (SOff 26 0) |};
{| c_off := -88; YQ0b.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YQ0b.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YQ0b.c_val := CVal 8 (SOff 23 0) |};
{| c_off := -64; YQ0b.c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; YQ0b.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YQ0b.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YQ0b.c_val := CVal 8 (SOff 19 0) |};
{| c_off := -32; YQ0b.c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; YQ0b.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YQ0b.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YQ0b.c_val := CVal 8 (SOff 1 0) |}]
|};
{|
r_base := None;
r_lo := 663904;
r_hi := 663912;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 663904; YQ0b.c_val := CVal 8 (SLit 696760) |}]
|};
{|
r_base := None;
r_lo := 696760;
r_hi := 696768;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 696760; YQ0b.c_val := CVal 8 (SOff 38 0) |}]
|};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 88;
r_whi := 92;
r_chunks :=
[{| c_off := 0; YQ0b.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 8; YQ0b.c_val := CVal 8 (SOff 34 0) |};
{| c_off := 16; YQ0b.c_val := CVal 8 (SOff 35 0) |};
{| c_off := 24; YQ0b.c_val := CVal 8 (SOff 39 0) |};
{| c_off := 40; YQ0b.c_val := CVal 4 (SOff 40 0) |};
{| c_off := 44; YQ0b.c_val := CVal 4 (SOff 41 0) |};
{| c_off := 48; YQ0b.c_val := CVal 2 (SOff 42 0) |};
{| c_off := 50; YQ0b.c_val := CVal 2 (SOff 43 0) |};
{| c_off := 52; YQ0b.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 54; YQ0b.c_val := CVal 2 (SOff 45 0) |};
{| c_off := 56; YQ0b.c_val := CVal 8 (SLit 529828) |};
{| c_off := 64; YQ0b.c_val := CVal 8 (SLit 0) |};
{| c_off := 72; YQ0b.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 80; YQ0b.c_val := CVal 8 (SLit 0) |};
{| c_off := 88; YQ0b.c_val := CVal 4 (SOff 37 0) |};
{| c_off := 92; YQ0b.c_val := CVal 4 (SLit ih) |}]
|};
{|
r_base := Some 46%nat;
r_lo := 0;
r_hi := 32;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YQ0b.c_val := CVal 8 (SOff 47 0) |};
{| c_off := 8; YQ0b.c_val := CVal 8 (SOff 48 0) |};
{| c_off := 16; YQ0b.c_val := CVal 4 (SOff 49 0) |};
{| c_off := 20; YQ0b.c_val := CVal 4 (SOff 50 0) |};
{| c_off := 24; YQ0b.c_val := CVal 2 (SOff 51 0) |};
{| c_off := 26; YQ0b.c_val := CVal 2 (SOff 52 0) |};
{| c_off := 28; YQ0b.c_val := CVal 1 (SOff 53 0) |}]
|}]
None
{|
f_atoms :=
[(72%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(71%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(hd,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 4
|});
(2%nat,
{|
af_lo := 70368744177664;
af_hi := 140737488355328;
af_al2 := 4
|});
(32%nat,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 4
|});
(38%nat,
{| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(46%nat,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 3
|})];
f_conds := [];
f_alias := []
|}).
Definition af_EB (regs : bvmap 5 word) (g : Z) (s : cgif_st) (cfp lpal img fattr fgen delay nlp tidx : Z) (f : frame_st) (E : env) : Prop :=
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E /\
ew E 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0) /\
ew E 70 = Z_to_bv 64 (fr_img f) /\ ew E 71 = Z_to_bv 64 (fr_attr f) /\ ew E 72 = Z_to_bv 64 (fr_delay f).
Lemma af_EB_agree : forall regs g s cfp lpal img fattr fgen delay nlp tidx f E E',
af_EB regs g s cfp lpal img fattr fgen delay nlp tidx f E -> (forall n, (n < 73)%nat -> ew E' n = ew E n) ->
af_EB regs g s cfp lpal img fattr fgen delay nlp tidx f E'.
Proof.
intros regs g s cfp lpal img fattr fgen delay nlp tidx f E E' (HE & E67 & E70 & E71 & E72) HA.
split; [apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | intros n Hn; apply HA; lia]|].
rewrite !HA by lia. repeat split; assumption.
Qed.
Definition af_preB (B : asyms) ly S W (regs : bvmap 5 word) mem md (g cfp : Z) (s : cgif_st) (N fattr : Z) (ms1 : machine_state) md1 : Prop :=
ajournal trasegs B TADDFRAME_STK (spZ regs) (FPa g s N) ly S W mem md [] ly S W (ms_mem ms1) md1 0 /\
af_side (mrestrict (w_H W) (ms_mem ms1)) g s /\
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte trasegs (mrestrict (w_H W) (ms_mem ms1)) (g + i) = mbyte trasegs (mrestrict (w_H W) mem) (g + i)) /\
(cg_cur s = 0 \/ cg_cur s = R_PENDING) /\
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) /\
(cg_ihead s = 1 \/ cg_ihead s = 2).

Definition AF_SM_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (f : frame_st),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_EB regs g s cfp lpal img fattr fgen delay nlp tidx f E ->
af_preB B ly S W regs mem md g cfp s N fattr ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok trasegs E (ss_SM (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok trasegs Bxa (af_SHB (33 + Z.to_nat (cg_ihead s))) E (mrestrict (w_H W) (ms_mem ms1)) ->
SRr trasegs W (mkCfg ms1 md1) (af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_L_stmt (B : asyms) : Prop :=
forall (n : nat) ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (f : frame_st) (kk : Z),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_EB regs g s cfp lpal img fattr fgen delay nlp tidx f E ->
af_preB B ly S W regs mem md g cfp s N fattr ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok trasegs E (ss_L0 (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok trasegs Bxa (af_SHB (33 + Z.to_nat (cg_ihead s))) E (mrestrict (w_H W) (ms_mem ms1)) ->
ew E 213 = Z_to_bv 64 (img + kk) -> ew E 214 = Z_to_bv 64 (fr_img f + kk) -> ew E 204 = Z_to_bv 64 (Z.of_nat n) ->
0 <= kk -> kk + Z.of_nat n = N -> (1 <= n)%nat ->
SRr trasegs W (mkCfg ms1 md1) (af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_Li_stmt (B : asyms) (ihv : Z) : Prop :=
forall (n : nat) ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (f : frame_st) (kk : Z),
cg_ihead s = ihv ->
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_EB regs g s cfp lpal img fattr fgen delay nlp tidx f E ->
af_preB B ly S W regs mem md g cfp s N fattr ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok trasegs E (ss_L0 (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok trasegs Bxa (af_SHB (33 + Z.to_nat (cg_ihead s))) E (mrestrict (w_H W) (ms_mem ms1)) ->
ew E 213 = Z_to_bv 64 (img + kk) -> ew E 214 = Z_to_bv 64 (fr_img f + kk) -> ew E 204 = Z_to_bv 64 (Z.of_nat n) ->
0 <= kk -> kk + Z.of_nat n = N -> (1 <= n)%nat ->
SRr trasegs W (mkCfg ms1 md1) (af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_Bi_stmt (B : asyms) (ihv : Z) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (f : frame_st),
cg_ihead s = ihv ->
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E ->
af_pre B ly S W regs mem md g cfp s N fattr E ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok trasegs E (ss_B (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok trasegs Bxa af_SH E (mrestrict (w_H W) (ms_mem ms1)) ->
SRr trasegs W (mkCfg ms1 md1) (af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Section l.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Lemma af_B_blocks : forall ly S W mem md g cfp s N img fattr lpa nlp rest f,
AR trasegs B ly S W mem md ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ af_cblocks img N fattr lpa nlp rest) ->
afobj B ly S W mem cfp 32 -> In (Some f) (cg_frames s) ->
In (img, N) (ablocks B ly S) /\ In (fr_img f, N) (ablocks B ly S) /\ In (fr_ptr f, FRAME_SIZE) (ablocks B ly S) /\
In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s N) /\
(g + 96 <= img \/ img + req_size N <= g) /\ (g + 96 <= fr_img f \/ fr_img f + req_size N <= g) /\
(cfp + 32 <= img \/ img + req_size N <= cfp) /\ (cfp + 32 <= fr_img f \/ fr_img f + req_size N <= cfp) /\
(img + req_size N <= fr_img f \/ fr_img f + req_size N <= img) /\
(g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g) /\ (cfp + 32 <= fr_ptr f \/ fr_ptr f + 40 <= cfp).
Proof.
intros ly S W mem md g cfp s N img fattr lpa nlp rest f HAR HPerm HFO HfIn.
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
assert (HfimgF : In (fr_img f, N) (frames_blocks N (cg_frames s))).
{ unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact HfIn | right; left; reflexivity]. }
assert (HfptrF : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (cg_frames s))).
{ unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact HfIn | left; reflexivity]. }
assert (Hfq : In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s N)).
{ unfold cgif_blocks. right. right. apply in_or_app. right. exact HfptrF. }
assert (Hfiq : In (fr_img f, N) (cgif_blocks g s N)).
{ unfold cgif_blocks. right. right. apply in_or_app. right. exact HfimgF. }
assert (Himg : In (img, N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. left. reflexivity. }
assert (Hfimg : In (fr_img f, N) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. left. exact Hfiq. }
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. left. exact Hfq. }
assert (NEi : (fr_img f, N) <> (g, CGIF_SIZE)).
{ intros Hq. pose proof (sep_hd_in B LAWS ly S W mem md (g, CGIF_SIZE) (img, N) _ HAR HPerm ltac:(right; apply in_or_app; right; left; reflexivity)) as D.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfimg) as (_ & _ & _ & _ & _ & _ & HN0 & _).
injection Hq as E1 E2. unfold CGIF_SIZE in E2.
assert (HP2 : Permutation (ablocks B ly S) ((img, N) :: cgif_blocks g s N ++ (rest))).
{ eapply Permutation_trans; [exact HPerm|]. apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_hd_in B LAWS ly S W mem md (img, N) (fr_img f, N) _ HAR HP2 ltac:(apply in_or_app; left; exact Hfiq)) as D2.
pose proof (sep_hd_in B LAWS ly S W mem md (g, CGIF_SIZE) (fr_img f, N) _ HAR HPerm) as D3.
unfold zdisjoint, block_rng in D3. cbn [fst snd] in D3. change (req_size CGIF_SIZE) with 96 in D3.
specialize (D3 ltac:(right; apply in_or_app; left; apply in_or_app; right; exact HfimgF)).
rewrite E1 in D3. pose proof (req_size_pos N ltac:(lia)) as [X _]. lia. }
pose proof (sep_hd_in B LAWS ly S W mem md (g, CGIF_SIZE) (img, N) _ HAR HPerm ltac:(right; apply in_or_app; right; left; reflexivity)) as Dig.
pose proof (sep_hd_in B LAWS ly S W mem md (g, CGIF_SIZE) (fr_img f, N) _ HAR HPerm ltac:(right; apply in_or_app; left; apply in_or_app; right; exact HfimgF)) as Dfg.
pose proof (sep_hd_in B LAWS ly S W mem md (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm ltac:(right; apply in_or_app; left; apply in_or_app; right; exact HfptrF)) as Dgh.
assert (HP2 : Permutation (ablocks B ly S) ((img, N) :: cgif_blocks g s N ++ (rest))).
{ eapply Permutation_trans; [exact HPerm|]. apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_hd_in B LAWS ly S W mem md (img, N) (fr_img f, N) _ HAR HP2 ltac:(apply in_or_app; left; exact Hfiq)) as Dif.
pose proof (sep_block_frame trasegs B LAWS ly S W _ _ img N cid pos HAR Himg Hfin) as Dic.
pose proof (sep_block_frame trasegs B LAWS ly S W _ _ (fr_img f) N cid pos HAR Hfimg Hfin) as Dfc.
pose proof (sep_block_frame trasegs B LAWS ly S W _ _ (fr_ptr f) FRAME_SIZE cid pos HAR Hfb Hfin) as Dch.
unfold zdisjoint, block_rng in Dig, Dfg, Dgh, Dif, Dic, Dfc, Dch. cbn [fst snd] in Dig, Dfg, Dgh, Dif, Dic, Dfc, Dch.
change (req_size CGIF_SIZE) with 96 in Dig, Dfg, Dgh. change (req_size FRAME_SIZE) with 40 in Dgh, Dch.
repeat match goal with |- _ /\ _ => split end; try assumption; clear - Dig Dfg Dgh Dif Dic Dfc Dch Hflo Hfhi; lia.
Qed.
Lemma af_B_ext : forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E0 : env) (ms1 : machine_state) md1 (f : frame_st),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E0 ->
af_pre B ly S W regs mem md g cfp s N fattr E0 ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok trasegs E0 (ss_B (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok trasegs Bxa af_SH E0 (mrestrict (w_H W) (ms_mem ms1)) ->
let E := havoc E0 70 [Z_to_bv 64 (fr_img f); Z_to_bv 64 (fr_attr f); Z_to_bv 64 (fr_delay f)] in
af_EB regs g s cfp lpal img fattr fgen delay nlp tidx f E /\ af_preB B ly S W regs mem md g cfp s N fattr ms1 md1 /\
st_ok trasegs E (ss_BX (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) /\
sh_ok trasegs Bxa (af_SHB (33 + Z.to_nat (cg_ihead s))) E (mrestrict (w_H W) (ms_mem ms1)).
Proof.
intros ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E0 ms1 md1 f CX HE0 HPX Hn HS SHOK.
pose proof HPX as (HJ & HSD & HGK & Hcur & HnoTab & E67_0 & Hih).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (HFS : FRAME_SIZE = 40) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trasegs _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (Hcfp : 4096 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
assert (HfIn : In (Some f) (cg_frames s)) by (rewrite <- Hn; apply nth_In; rewrite (proj1 HWF); destruct Hih as [-> | ->]; cbn; lia).
pose proof (proj2 HSD f HfIn) as HOBf.
pose proof (af_B_blocks ly S W mem md g cfp s N img fattr lpa nlp rest f HAR HPerm HFO HfIn) as (_ & _ & Hfb & Hfq & _ & _ & _ & _ & _ & Dgh & Dch).
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR1 Hfb) as (Hh16 & Hh4096 & Hhceil & Hhh_ia & HhP & _). pose proof (proj1 Hhh_ia) as Hhh.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR1 Hfb) as Hhh_img.
change (req_size FRAME_SIZE) with 40 in Hhceil, Hhh, HhP, Hhh_img.
pose proof (obj_at_nth trasegs _ _ _ _ 1 (8, 8%N) (fr_img f) HOBf eq_refl eq_refl) as [Vhimg Rhimg].
pose proof (obj_at_nth trasegs _ _ _ _ 2 (16, 4%N) (fr_attr f) HOBf eq_refl eq_refl) as [Vhattr Rhattr].
pose proof (obj_at_nth trasegs _ _ _ _ 4 (24, 2%N) (fr_delay f) HOBf eq_refl eq_refl) as [Vhdel Rhdel].
cbn [snd N.to_nat] in Vhimg, Rhimg, Vhattr, Rhattr, Vhdel, Rhdel.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rhimg. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rhattr. change (2 ^ (8 * Z.of_N 2)) with 65536 in Rhdel.
pose proof (st_ok_havoc trasegs 70 E0 _ _ [Z_to_bv 64 (fr_img f); Z_to_bv 64 (fr_attr f); Z_to_bv 64 (fr_delay f)] HS ltac:(destruct Hih as [Q|Q]; rewrite Q; vm_compute; reflexivity)) as HS1.
clear HS. rename HS1 into HS. cbv zeta.
set (E := havoc E0 70 [Z_to_bv 64 (fr_img f); Z_to_bv 64 (fr_attr f); Z_to_bv 64 (fr_delay f)]) in *.
assert (OLD : forall n, (n < 70)%nat -> ew E n = ew E0 n) by (intros n Hn0; subst E; apply YO3v.ew_havoc_old; exact Hn0).
assert (E70 : ew E 70 = Z_to_bv 64 (fr_img f)) by (subst E; change 70%nat with (70 + 0)%nat; rewrite (YO3v.ew_havoc_new E0 70 _ 0 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (E71 : ew E 71 = Z_to_bv 64 (fr_attr f)) by (subst E; change 71%nat with (70 + 1)%nat; rewrite (YO3v.ew_havoc_new E0 70 _ 1 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (E72 : ew E 72 = Z_to_bv 64 (fr_delay f)) by (subst E; change 72%nat with (70 + 2)%nat; rewrite (YO3v.ew_havoc_new E0 70 _ 2 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (HE : af_E regs g s cfp lpal img fattr fgen delay nlp tidx E) by (subst E; apply af_E_havoc; [exact HE0 | clear; lia]).
assert (E67 : ew E 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite OLD by (clear; lia); exact E67_0).
assert (HAE0 : env_agree 70 E0 E) by (subst E; apply env_agree_havoc_ge; [clear; lia | apply env_agree_refl]).
pose proof (sh_ok_agree trasegs Bxa af_SH 70 E0 E _ HAE0 eq_refl SHOK) as SHOK1. clear SHOK.
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & _).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
split; [split; [exact HE | split; [exact E67 | split; [exact E70 | split; [exact E71 | exact E72]]]]|].
split; [split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | exact Hih]]]]]|].
assert (Bhd : bv_unsigned (ew E (33 + Z.to_nat (cg_ihead s))) = fr_ptr f).
{ destruct Hih as [Q|Q]; rewrite Q in Hn |- *; [change (33 + Z.to_nat 1)%nat with 34%nat; rewrite E34 | change (33 + Z.to_nat 2)%nat with 35%nat; rewrite E35];
[change (Z.to_nat 1) with 1%nat in Hn | change (Z.to_nat 2) with 2%nat in Hn]; rewrite Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia. }
split.
- unfold ss_BX.
apply st_ok_add_fact; [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E72, unsigned_lit_small by (clear - Rhdel; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rhdel; lia].
apply st_ok_add_fact; [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E71, unsigned_lit_small by (clear - Rhattr; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rhattr; lia].
apply st_ok_add_fact; [| unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bhd; change (2 ^ 4) with 16; clear - Hh4096 Hhh Hhceil Hh16 C1 C3 C4; lia].
lazymatch type of HS with st_ok _ _ ?ssx _ =>
change (mkSS AF_B _ _ None _) with (mkSS (ss_pc ssx) (ss_regs ssx) (af_hdr (33 + Z.to_nat (cg_ihead s)) :: ss_mem ssx) (ss_resv ssx) (ss_facts ssx)) end.
apply (ast_ok_add_region trasegs E _ _ (af_hdr (33 + Z.to_nat (cg_ihead s))) HS eq_refl).
+ unfold region_ok, af_hdr; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst].
rewrite Bhd. split; [clear - Hh4096 Hhceil C1; lia|]. split; [clear - Hh4096 Hhceil C1; lia|].
split; [intros o Ho; exfalso; clear - Ho; lia|].
constructor; [eapply (chunk_ok_val trasegs E _ (fr_ptr f)); [cbn [sv_denot]; rewrite E70, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhimg]|].
constructor; [eapply (chunk_ok_val trasegs E _ (fr_ptr f)); [cbn [sv_denot]; rewrite E71, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhattr]|].
constructor; [eapply (chunk_ok_val trasegs E _ (fr_ptr f)); [cbn [sv_denot]; rewrite E72, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhdel]|].
constructor.
+ destruct Hih as [Q|Q]; rewrite Q in Bhd |- *;
[change (33 + Z.to_nat 1)%nat with 34%nat in Bhd |- * | change (33 + Z.to_nat 2)%nat with 35%nat in Bhd |- *];
(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, af_hdr; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Bhd, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgh Dch Hh4096 Hhh Hhh_img Hhceil Hcfp HZg Hceil Hslo HTS C1 C3 C4; unfold off_img in Hhh_img; repeat split; lia).
- unfold sh_ok, af_SHB. apply Forall_app. split; [exact SHOK1|]. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS ly S W (ms_mem ms1) md1 E Bxa (33 + Z.to_nat (cg_ihead s)) (fr_ptr f) FRAME_SIZE 0 FRAME_SIZE HAR1 Hfb).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bhd.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia.
Qed.
Lemma af_side_blk : forall ly S W (m m2 : word -> option byte) md g s N cb,
AR trasegs B ly S W m md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) ->
af_side (mrestrict (w_H W) m) g s ->
(forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> ~ inFP [] (p + i) ->
aview trasegs (w_H W) m2 (p + i) = aview trasegs (w_H W) m (p + i)) ->
af_side (mrestrict (w_H W) m2) g s.
Proof.
intros ly S W m m2 md g s N cb HAR HP [Hr Hf] G2.
assert (NF : forall a, ~ inFP [] a) by (intros a (rr & Hrr & _); exact Hrr).
split.
- assert (Hinr : In (cg_raw s, RAW_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP|]; right; left; reflexivity).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros i Hi. apply (mbyte_of_aview trasegs).
apply (G2 (cg_raw s) RAW_SIZE i Hinr Hinr); [change (req_size RAW_SIZE) with 48; exact Hi | apply NF].
- intros f Hin. assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_or_app. left. exact (af_frame_in_blocks g s N f Hin). }
apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame). intros i Hi. apply (mbyte_of_aview trasegs).
apply (G2 (fr_ptr f) FRAME_SIZE i Hfb Hfb); [change (req_size FRAME_SIZE) with 40; exact Hi | apply NF].
Qed.
End l.
End h.
Ltac af_B_names LAWS CX HEB HPB Hn :=
lazymatch type of CX with af_cx ?B ?ly ?S ?W ?regs ?mem ?md ?ch ?g ?cfp ?s ?N ?lpal ?lpa ?img ?fattr ?fgen ?delay ?nlp ?tidx ?rest =>
lazymatch type of HEB with af_EB _ _ _ _ _ _ _ _ _ _ _ ?f ?E =>
pose proof HPB as (HJ & HSD & HGK & Hcur & HnoTab & Hih);
pose proof Hwx_tfa as Hwx; pose proof tra_segs_low as Hsegs; pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL);
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (HTS : TADDFRAME_STK = 17664) by reflexivity; assert (HFS : FRAME_SIZE = 40) by reflexivity; assert (HES : ESTACK = 4096) by reflexivity;
set (sp0 := spZ regs) in *;
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity);
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _); pose proof (proj1 Hgh_ia) as Hgh;
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hing) as Hgh_img;
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img;
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA);
destruct (frames_bounds trasegs _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
assert (Hcfp : 4096 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia);
pose proof (in_app_sub _ _ cfp 32 Hfhigh ltac:(clear - Hflo; lia) ltac:(clear; lia) ltac:(clear - Hfhi; lia)) as Hcfp_ia;
pose proof (proj1 HWF) as Hlen;
assert (HfIn : In (Some f) (cg_frames s)) by (rewrite <- Hn; apply nth_In; rewrite Hlen; destruct Hih as [-> | ->]; cbn; lia);
pose proof (af_B_blocks B LAWS ly S W mem md g cfp s N img fattr lpa nlp rest f HAR HPerm HFO HfIn) as (Himg & Hfimg & Hfb & Hfq & Dig & Dfg & Dic & Dfc & Dif & Dgh & Dch);
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfb) as (Hh16 & Hh4096 & Hhceil & Hhh_ia & _); pose proof (proj1 Hhh_ia) as Hhh;
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hfb) as Hhh_img;
change (req_size FRAME_SIZE) with 40 in Hhceil, Hhh, Hhh_img;
destruct (al_blocks _ _ LAWS _ _ _ _ _ img N HAR Himg) as (_ & Hi4096 & Hiceil & Hih0_ia & _); pose proof (proj1 Hih0_ia) as Hih0;
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Himg) as Hih0_img;
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N HAR Hfimg) as (_ & Hfi4096 & Hficeil & Hfih0_ia & _); pose proof (proj1 Hfih0_ia) as Hfih0;
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hfimg) as Hfih0_img;
pose proof HWF as (_ & HW1 & HH1 & HNWH & HNmax & _);
assert (HN1 : 1 <= N <= 100000000) by (clear - HW1 HH1 HNWH HNmax; nia);
pose proof (req_size_pos N ltac:(clear - HN1; lia)) as [_ HrN];
pose proof (obj_at_nth trasegs _ _ _ _ 7 (48, 2%N) (cg_W s) (proj1 HT) eq_refl eq_refl) as [_ RW];
pose proof (obj_at_nth trasegs _ _ _ _ 8 (50, 2%N) (cg_H s) (proj1 HT) eq_refl eq_refl) as [_ RH];
cbn [snd] in RW, RH; change (2 ^ (8 * Z.of_N 2)) with 65536 in RW, RH;
pose proof (obj_at_nth trasegs _ _ _ _ 15 (88, 4%N) (cg_cur s) (proj1 HT) eq_refl eq_refl) as [_ Rcur]; cbn [snd] in Rcur;
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rcur;
pose proof HEB as (HE & E67 & E70 & E71 & E72);
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53);
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity);
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia);
pose proof (af_sideZ B LAWS ly S W mem md g s N _ ly sp0 HAR HPerm Hstk) as [HZr HZf];
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia);
assert (HAE54 : env_agree 54 E E) by (split; [intros; reflexivity | reflexivity])
end end.
