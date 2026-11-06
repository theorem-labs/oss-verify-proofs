(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane), free hand B of a Theorem Labs lane: the STATE-SURGERY kit that the
   parse_items segment runs use at every resume. Generic over the engine: no parse_items fact, no callee spec, no
   machine run. A kit (rule 24: no function proved here).
   WHAT IS HERE. The five state builders that a Theorem Labs lane's measured states are made of - pik_setr (set registers),
   pik_addf (prepend facts), pik_addr (prepend regions), pik_setm (replace the region list) and pik_treg (a read-only
   literal byte window at a cursor atom, chunks pik_txt) - and the facts that carry YP0l.st_ok tfibsegs across them:
     pik_st_ok_setm / _extra / _setr / _addf / _addr  st_ok after each builder (over YP06.st_ok_submem / st_ok_facts,
                                                      YP03.st_ok_agree, YI08.st_ok_set_reg);
     pik_treg_ok / pik_treg_wf                        the literal window is region_ok over the text bytes, and wf;
     pik_chunks_agree                                 the frame chunks of a call, carried from the run's env to the
                                                      resume env;
     pik_cond_ltu / pik_cond_ne                       BC_LTU / BC_NE of two SOff atoms, from Z facts;
     pik_alias_ok_lin                                 the two address aliases a + 8 n (slli 3) and a + 56 n (mul 56).
   CHOICES AND ADDED PREMISES (against wpi3/hand-B-kit.txt):
   - chunks_atom is pik_chunks_atom, defined here (not YCeo.sv_atoms_on): atom n is in pik_chunk_atoms of some chunk of
     cs, i.e. it is an SOff atom of a CVal value (CZero / CImg / CData chunks name no atom). On a concrete chunk list
     the membership computes, so `cbn in Hn` (or `vm_compute in Hn`) turns it into a disjunction of equations.
   - pik_chunks_agree takes one more premise, ed E = ed E': a CData chunk reads ed E d (YP09.cbyte) and an SData term
     inside a CVal value reads ed E d (YP0m.data_word), so equal atoms alone do not carry chunk_ok. Two Ereg envs have
     the same ed (fun _ => []), so the premise is eq_refl at a Theorem Labs lane's call steps.
   - pik_alias_ok_lin is ONE lemma for both forms: the conjunction of the slli-3 alias (t = A + 8 N) and the mul-56
     alias (t = A + 56 N), each under its own range and t equation.
   COPIED, never imported (the implicit-instance guard of FSH_Gen.v:29): A/AF0r.v:312 env_agree_Ereg_app, as
   pik_env_agree_Ereg_app, unchanged but for its name. pik_atoms_ok_app / pik_conds_ok_app / pik_alias_ok_app are
   Reusable/YN07.v:402-407 (not in this file's import block), unchanged but for their names. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP06 YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI04 YI08.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section pik. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the state builders ---- *)
Definition pik_setr (ss : sstate) (l : list (bv 5 * sv)) : sstate :=
  mkSS (ss_pc ss) (fold_left (fun r q => sr_set r (fst q) (snd q)) l (ss_regs ss)) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition pik_addf (ss : sstate) (atl : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss)
    (mkFacts (atl ++ f_atoms (ss_facts ss)) (cs ++ f_conds (ss_facts ss)) (al ++ f_alias (ss_facts ss))).
Definition pik_addr (ss : sstate) (rs : list YP09.region) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (rs ++ ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition pik_setm (ss : sstate) (rs : list YP09.region) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss).
Definition pik_txt (bs : list Z) (o : Z) : list YP09.chunk :=
  map (fun ib => YP09.mkChunk (o + Z.of_nat (fst ib)) (CVal 1 (SLit (snd ib)))) (combine (seq 0 (length bs)) bs).
(* a read-only literal byte window at the cursor atom a: bytes bs at offsets o .. o + |bs| - 1 *)
Definition pik_treg (a : nat) (o : Z) (bs : list Z) : YP09.region :=
  YP09.mkRegion (Some a) 0 (o + Z.of_nat (length bs)) 0 0 (pik_txt bs o).

(* ---- the atoms a chunk list names (pik_chunks_agree's chunks_atom) ---- *)
Fixpoint pik_sv_atoms (v : sv) : list nat :=
  match v with
  | SLit _ => []
  | SOff n _ => [n]
  | SAlu _ a b => pik_sv_atoms a ++ pik_sv_atoms b
  | SAluw _ a b => pik_sv_atoms a ++ pik_sv_atoms b
  | SMd _ a b => pik_sv_atoms a ++ pik_sv_atoms b
  | SMdw _ a b => pik_sv_atoms a ++ pik_sv_atoms b
  | SExt _ _ a => pik_sv_atoms a
  | SData _ _ _ => []
  | SF1 _ a => pik_sv_atoms a
  | SF2 _ a b => pik_sv_atoms a ++ pik_sv_atoms b
  | SF3 _ a b c => pik_sv_atoms a ++ pik_sv_atoms b ++ pik_sv_atoms c
  end.
Definition pik_chunk_atoms (c : YP09.chunk) : list nat :=
  match YP09.c_val c with CVal _ v => pik_sv_atoms v | _ => [] end.
Definition pik_chunks_atom (cs : list YP09.chunk) (n : nat) : Prop := In n (flat_map pik_chunk_atoms cs).

(* ---- helpers ---- *)
(* Reusable/YN07.v:402-407, renamed *)
Lemma pik_atoms_ok_app E l1 l2 : atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. induction l1 as [|[n f] t IH]; cbn; intros H1 H2; [exact H2|]. destruct H1; split; auto. Qed.
Lemma pik_conds_ok_app E l1 l2 : conds_ok E l1 -> conds_ok E l2 -> conds_ok E (l1 ++ l2).
Proof. induction l1 as [|c t IH]; cbn; intros H1 H2; [exact H2|]. destruct H1; split; auto. Qed.
Lemma pik_alias_ok_app E l1 l2 : alias_ok E l1 -> alias_ok E l2 -> alias_ok E (l1 ++ l2).
Proof. induction l1 as [|[a b] t IH]; cbn; intros H1 H2; [exact H2|]. destruct H1; split; auto. Qed.
(* A/AF0r.v:312 env_agree_Ereg_app, renamed *)
Lemma pik_env_agree_Ereg_app : forall regs l1 l2 k, (k <= 32 + length l1)%nat ->
  env_agree k (Ereg regs l1) (Ereg regs (l1 ++ l2)).
Proof.
intros regs l1 l2 k Hk. split; [|reflexivity]. intros n Hn.
destruct (Nat.lt_ge_cases n 32) as [L|L].
- unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia].
- replace n with (32 + (n - 32))%nat by lia. rewrite !ew_Ereg_extra. rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma pik_sv_denot_agree : forall E E' v, ed E = ed E' ->
  (forall n, In n (pik_sv_atoms v) -> ew E n = ew E' n) -> sv_denot E v = sv_denot E' v.
Proof.
intros E E' v Hed. induction v; cbn [pik_sv_atoms sv_denot]; intros H.
all: try (unfold data_word; rewrite Hed; reflexivity).
all: try (rewrite (H n (or_introl eq_refl)); reflexivity).
all: repeat match goal with
  | IH : _ -> sv_denot ?e ?x = sv_denot ?e' ?x |- _ =>
      rewrite IH by (intros k Hk; apply H; rewrite ?in_app_iff; tauto); clear IH
  end.
all: reflexivity.
Qed.
Lemma pik_chunk_ok_agree : forall E E' m base c, ed E = ed E' ->
  (forall n, In n (pik_chunk_atoms c) -> ew E n = ew E' n) ->
  YP09.chunk_ok tfibsegs E m base c -> YP09.chunk_ok tfibsegs E' m base c.
Proof.
intros E E' m base [off cv] Hed H Hc i Hi. destruct (Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [|exact Hb2].
destruct cv as [w v|len|len|d s len]; cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1 |- *.
- rewrite <- (pik_sv_denot_agree E E' v Hed H). exact Hb1.
- exact Hb1.
- exact Hb1.
- rewrite <- Hed. exact Hb1.
Qed.
Lemma pik_in_combine_seq : forall (bs : list Z) k i x, In (i, x) (combine (seq k (length bs)) bs) ->
  (k <= i)%nat /\ (i < k + length bs)%nat /\ nth (i - k)%nat bs 0 = x.
Proof.
induction bs as [|b bs IH]; intros k i x H; cbn [length seq combine] in H.
- destruct H.
- destruct H as [H|H].
  + injection H as <- <-. split; [lia|]. split; [cbn [length]; lia|]. rewrite Nat.sub_diag. reflexivity.
  + destruct (IH (S k) i x H) as (H1 & H2 & H3). split; [lia|]. split; [cbn [length]; lia|].
    replace (i - k)%nat with (S (i - S k)) by lia. exact H3.
Qed.
Lemma pik_bow_lit : forall x, 0 <= x < 256 -> YP09.byte_of_word (Z_to_bv 64 x) 0 = Z_to_bv 8 x.
Proof.
intros x Hx. unfold YP09.byte_of_word. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
rewrite YP03.unsigned_lit_small by lia. reflexivity.
Qed.
Lemma pik_U_eq : forall E x y, YP0e.U E x = YP0e.U E y -> sv_denot E x = sv_denot E y.
Proof. intros E x y H. apply bv_eq. exact H. Qed.

(* ---- st_ok across the builders ---- *)
Lemma pik_st_ok_setm : forall E ss ms rs, st_ok tfibsegs E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok tfibsegs E (pik_setm ss rs) ms.
Proof. intros E ss ms rs HS Hsub Hwf. exact (YP06.st_ok_submem tfibsegs E ss ms rs HS Hsub Hwf). Qed.
Lemma pik_st_ok_extra : forall regs xs ys ss ms, st_ok tfibsegs (Ereg regs xs) ss ms ->
  ss_atoms_lt (32 + length xs) ss = true -> st_ok tfibsegs (Ereg regs (xs ++ ys)) ss ms.
Proof.
intros regs xs ys ss ms HS Hat.
exact (YP03.st_ok_agree tfibsegs (32 + length xs) _ _ ss ms HS
  (pik_env_agree_Ereg_app regs xs ys (32 + length xs) (le_n _)) Hat).
Qed.
Lemma pik_st_ok_setr : forall E ss ms l, st_ok tfibsegs E ss ms ->
  Forall (fun q => fst q <> 0%bv /\ YK11.getr (ms_regs ms) (fst q) = sv_denot E (snd q)) l ->
  st_ok tfibsegs E (pik_setr ss l) ms.
Proof.
intros E ss ms l HS Hl. revert ss HS. induction Hl as [|q l [Hq1 Hq2] Hl IH]; intros ss HS.
- destruct ss; exact HS.
- exact (IH _ (YI08.st_ok_set_reg tfibsegs E ss ms (fst q) (snd q) HS Hq1 Hq2)).
Qed.
Lemma pik_st_ok_addf : forall E ss ms atl cs al, st_ok tfibsegs E ss ms -> atoms_ok E atl -> conds_ok E cs ->
  alias_ok E al -> st_ok tfibsegs E (pik_addf ss atl cs al) ms.
Proof.
intros E ss ms atl cs al HS Ha Hc Hal.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & Ha0 & Hc0 & Hal0).
unfold pik_addf. apply YP06.st_ok_facts; [exact HS|].
split; [|split]; cbn [f_atoms f_conds f_alias].
- exact (pik_atoms_ok_app E atl _ Ha Ha0).
- exact (pik_conds_ok_app E cs _ Hc Hc0).
- exact (pik_alias_ok_app E al _ Hal Hal0).
Qed.
Lemma pik_st_ok_addr : forall E ss ms rs, st_ok tfibsegs E ss ms -> regions_wf (rs ++ ss_mem ss) = true ->
  Forall (region_ok tfibsegs E (ms_mem ms)) rs -> pairwise_disjoint E (rs ++ ss_mem ss) ->
  st_ok tfibsegs E (pik_addr ss rs) ms.
Proof.
intros E ss ms rs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hwf Hok Hpd.
destruct H8 as (_ & Hok0 & _).
unfold st_ok, pik_addr. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [|exact H9].
split; [exact Hwf|]. split; [|exact Hpd].
apply (proj2 (Forall_forall _ _)). intros r Hr. apply in_app_iff in Hr as [Hr|Hr].
- exact (proj1 (Forall_forall _ _) Hok r Hr).
- exact (proj1 (Forall_forall _ _) Hok0 r Hr).
Qed.

(* ---- the literal byte window ---- *)
Lemma pik_treg_ok : forall E m a b o bs, bv_unsigned (ew E a) = b -> 0 <= o -> 0 <= b ->
  b + o + Z.of_nat (length bs) <= 2 ^ 64 -> Forall (fun c => 0 <= c < 256) bs ->
  (forall i, (i < length bs)%nat -> mbyte tfibsegs m (b + o + Z.of_nat i) = Some (Z_to_bv 8 (nth i bs 0))) ->
  region_ok tfibsegs E m (pik_treg a o bs).
Proof.
intros E m a b o bs Hb Ho Hb0 Hhi Hbs Hm.
unfold region_ok, pik_treg.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
rewrite Hb.
split; [lia|]. split; [lia|]. split; [intros o' Ho'; exfalso; lia|].
apply (proj2 (Forall_forall _ _)). intros c Hc. unfold pik_txt in Hc.
apply in_map_iff in Hc as ([i x] & <- & Hin).
destruct (pik_in_combine_seq bs 0 i x Hin) as (_ & Hi & Hx). rewrite Nat.sub_0_r in Hx.
assert (Hxr : 0 <= x < 256).
{ rewrite <- Hx. apply (proj1 (Forall_forall _ _) Hbs). apply nth_In. lia. }
cbn [fst snd]. intros j Hj.
assert (j = 0) as ->.
{ cbn [YP09.c_len YP09.cv_len YP09.c_val] in Hj. try change (Z.of_N 1) with 1 in Hj. lia. }
exists (Z_to_bv 8 x). split.
- cbn [YP09.cbyte YP09.c_val sv_denot]. rewrite pik_bow_lit by exact Hxr. reflexivity.
- cbn [YP09.c_off]. replace (b + (o + Z.of_nat i) + 0) with (b + o + Z.of_nat i) by lia.
  rewrite Hm by lia. rewrite Hx. reflexivity.
Qed.
Lemma pik_treg_wf : forall a o bs, 0 <= o -> YP09.region_wf (pik_treg a o bs) = true.
Proof.
intros a o bs Ho. unfold YP09.region_wf, pik_treg.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
apply andb_true_intro. split; [apply andb_true_intro; split|].
- apply Z.leb_le. lia.
- reflexivity.
- apply (proj2 (forallb_forall _ _)). intros c Hc. unfold pik_txt in Hc.
  apply in_map_iff in Hc as ([i x] & <- & Hin).
  destruct (pik_in_combine_seq bs 0 i x Hin) as (_ & Hi & _).
  unfold YP09.chunk_inside. cbn [fst snd YP09.r_lo YP09.r_hi YP09.c_off YP09.c_len YP09.c_val YP09.cv_len].
  try change (Z.of_N 1) with 1.
  apply andb_true_intro. split; [apply andb_true_intro; split|]; apply Z.leb_le; lia.
Qed.

(* ---- the frame chunks of a call, carried to the resume env ---- *)
Lemma pik_chunks_agree : forall E E' m base cs, Forall (YP09.chunk_ok tfibsegs E m base) cs ->
  (forall n, pik_chunks_atom cs n -> ew E n = ew E' n) -> ed E = ed E' ->
  Forall (YP09.chunk_ok tfibsegs E' m base) cs.
Proof.
intros E E' m base cs Hcs. induction Hcs as [|c cs' Hc Hcs IH]; intros H Hed; constructor.
- apply (pik_chunk_ok_agree E E' m base c Hed); [|exact Hc].
  intros n Hn. apply H. unfold pik_chunks_atom. cbn [flat_map]. apply in_or_app. left. exact Hn.
- apply IH; [|exact Hed]. intros n Hn. apply H. unfold pik_chunks_atom in *. cbn [flat_map].
  apply in_or_app. right. exact Hn.
Qed.

(* ---- branch conditions and aliases from Z facts ---- *)
Lemma pik_cond_ltu : forall E a b c d x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x + c < 2 ^ 64 -> 0 <= y + d < 2 ^ 64 -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x + c < y + d ->
  acond_ok E (mkAC BC_LTU (SOff a c) (SOff b d)).
Proof.
intros E a b c d x y Ha Hb Hxc Hyd Hx Hy Hlt. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite YI04.branch_ltu_U, (YI04.U_atom_off E a x c Ha Hx Hxc), (YI04.U_atom_off E b y d Hb Hy Hyd).
apply Z.ltb_lt. exact Hlt.
Qed.
Lemma pik_cond_ne : forall E a b c d x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x + c < 2 ^ 64 -> 0 <= y + d < 2 ^ 64 -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x + c <> y + d ->
  acond_ok E (mkAC BC_NE (SOff a c) (SOff b d)).
Proof.
intros E a b c d x y Ha Hb Hxc Hyd Hx Hy Hne. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite YI04.branch_ne_U, (YI04.U_atom_off E a x c Ha Hx Hxc), (YI04.U_atom_off E b y d Hb Hy Hyd).
apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hne.
Qed.
Lemma pik_alias_ok_lin : forall E a n t A N,
  ew E a = Z_to_bv 64 A -> ew E n = Z_to_bv 64 N -> 0 <= A < 2 ^ 64 -> 0 <= N < 2 ^ 64 ->
  (0 <= A + 8 * N < 2 ^ 64 -> ew E t = Z_to_bv 64 (A + 8 * N) ->
     alias_ok E [(SAlu ALU_ADD (SOff a 0) (SAlu ALU_SLL (SOff n 0) (SLit 3)), SOff t 0)]) /\
  (0 <= A + 56 * N < 2 ^ 64 -> ew E t = Z_to_bv 64 (A + 56 * N) ->
     alias_ok E [(SAlu ALU_ADD (SOff a 0) (SMd M_MUL (SOff n 0) (SLit 56)), SOff t 0)]).
Proof.
intros E a n t A N Ha Hn HA HN.
split; intros HR Ht; cbn [alias_ok]; (split; [|exact I]); apply pik_U_eq.
- rewrite !YP0e.U_SAlu. cbn [zalu_raw].
  rewrite YP0e.U_SLit, (YI04.U_atom_off E a A 0 Ha HA ltac:(lia)), (YI04.U_atom_off E n N 0 Hn HN ltac:(lia)),
    (YI04.U_atom_off E t (A + 8 * N) 0 Ht HR ltac:(lia)).
  rewrite !Z.add_0_r. replace (Z.land (zcanon 3) 63) with 3 by reflexivity.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (YP0e.zcanon_id (N * 8)) by (unfold M64; lia). rewrite YP0e.zcanon_id by (unfold M64; lia). lia.
- rewrite YP0e.U_SAlu, YP0e.U_SMd. cbn [zalu_raw zmd_raw].
  rewrite YP0e.U_SLit, (YI04.U_atom_off E a A 0 Ha HA ltac:(lia)), (YI04.U_atom_off E n N 0 Hn HN ltac:(lia)),
    (YI04.U_atom_off E t (A + 56 * N) 0 Ht HR ltac:(lia)).
  rewrite !Z.add_0_r. replace (zcanon 56) with 56 by reflexivity.
  rewrite (YP0e.zcanon_id (N * 56)) by (unfold M64; lia). rewrite YP0e.zcanon_id by (unfold M64; lia). lia.
Qed.

End pik.
