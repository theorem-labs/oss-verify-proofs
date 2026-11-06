(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S07 (route add, B 0x8d2e8) of the walk of verbs_receive on the
   ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v, vr_s07_stmt): the kit of the inline
   is_placement(tok[3]) at B 0x8d348-0x8d390 (.str.24-.str.26, A's addresses + 0x40): the literals "own" 0x228a0, "default" 0x228c0 and "pool:" 0x228e0 (lit07,
   lit07_at), strcmp(tok[3], literal) and strncmp(tok[3], literal, 5) through a Theorem Labs lane's contracts and art07 (cmp07,
   ncmp07), the model's prefix test (add_prefix07), a0 read off `beqz a0` (reg0_07, regn0_07) and a literal's
   address in a register (objval07). verbs_receive_s07.v's legP walks the test. The B twin of
   lib/A/Prog/verbs_receive_s07i.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
verbs_receive_s07a verbs_receive_s07b verbs_receive_s07c verbs_receive_s07e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

(* strncmp(w, "pool:", 5) is 0 exactly when w starts with "pool:" (the plain proof's verbs_receive_br_add0.v
   add_prefix_walk / add_prefix, lib/Prog, functional) *)
Lemma add_prefix_walk07 : forall p w k,
  length p = S k -> Forall (fun b : byte => bv_unsigned b <> 0) p ->
  exists v, StrFun.strncmp_walk (w ++ [Z_to_bv 8 0]) (p ++ [Z_to_bv 8 0]) k = Some v /\
    -256 < v < 256 /\ (v =? 0) = PV.has_prefix p w.
Proof.
  induction p as [|b p IH]; intros w k LP NP; [discriminate|].
  inversion NP as [|? ? NB NPS]; subst.
  pose proof (bv_unsigned_in_range 8 b) as RB. change (bv_modulus 8) with 256 in RB.
  destruct w as [|a w].
  - cbn [app StrFun.strncmp_walk]. exists (- bv_unsigned b).
    split; [f_equal; lia|]. split; [lia|].
    unfold PV.has_prefix. cbn [length Nat.leb andb]. apply Z.eqb_neq. lia.
  - pose proof (bv_unsigned_in_range 8 a) as RA. change (bv_modulus 8) with 256 in RA.
    cbn [app StrFun.strncmp_walk]. rewrite (proj2 (Z.eqb_neq _ _) NB).
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [EQ|NE].
    + assert (NA : (bv_unsigned a =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite NA. cbn [orb negb]. destruct k as [|k].
      * destruct p; cbn [length] in LP; [|discriminate].
        cbn [Nat.eqb]. exists 0. split; [f_equal; lia|]. split; [lia|].
        unfold PV.has_prefix. cbn [length Nat.leb firstn PV.list_eqb]. rewrite EQ, !Z.eqb_refl. reflexivity.
      * cbn [Nat.eqb]. destruct (IH w k ltac:(cbn [length] in LP; lia) NPS) as (v & HV & RV & QV).
        exists v. split; [exact HV|]. split; [exact RV|]. rewrite QV.
        unfold PV.has_prefix. cbn [length Nat.leb firstn PV.list_eqb]. rewrite EQ, !Z.eqb_refl. reflexivity.
    + cbn [negb orb]. rewrite !orb_true_r. exists (bv_unsigned a - bv_unsigned b).
      split; [reflexivity|]. split; [lia|].
      assert (EZ : (bv_unsigned a - bv_unsigned b =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite EZ. unfold PV.has_prefix. cbn [length Nat.leb firstn PV.list_eqb].
      rewrite (proj2 (Z.eqb_neq _ _) NE), andb_false_l, andb_false_r. reflexivity.
Qed.
Lemma add_prefix07 : forall w,
  exists v, StrFun.strncmp_model (w ++ [Z_to_bv 8 0]) (PV.Lit.place_pool_prefix ++ [Z_to_bv 8 0]) 5 = Some v /\
    -256 < v < 256 /\ (v =? 0) = PV.has_prefix PV.Lit.place_pool_prefix w.
Proof.
  intros w. apply (add_prefix_walk07 PV.Lit.place_pool_prefix w 4); vm_compute; repeat constructor; discriminate.
Qed.

Lemma no0_07 : forall s, forallb (fun b : byte => negb (bv_unsigned b =? 0)) s = true -> ~ In (Z_to_bv 8 0) s.
Proof. intros s H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate H. Qed.

(* the register a0 after a comparison, read off the test `beqz a0` *)
Lemma reg0_07 : forall E (w : word), ew E 10 = w -> U E (SOff 10 0) = 0 -> w = w64 0.
Proof.
intros E w Hw HU. rewrite U_SOff, Hw, Z.add_0_r in HU.
pose proof (bv_unsigned_in_range 64 w) as Hr. unfold bv_modulus in Hr. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr.
rewrite zcanon_id in HU by (unfold M64; lia).
apply bv_eq. rewrite HU. unfold w64. rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma regn0_07 : forall E (w : word), ew E 10 = w -> U E (SOff 10 0) <> 0 -> w <> w64 0.
Proof. intros E w Hw HU E0. apply HU. rewrite U_SOff, Hw, E0, Z.add_0_r. reflexivity. Qed.

Lemma list_eqb_false07 : forall a b, a <> b -> PV.list_eqb a b = false.
Proof. intros a b H. destruct (PV.list_eqb a b) eqn:E; [apply PV.list_eqb_eq in E; contradiction | reflexivity]. Qed.

(* the value of a register that an auipc/addi pair set to a literal's object atom *)
Ltac objval07 Q E HEI VOBJS :=
  let n := lazymatch type of Q with getr _ _ = ew _ ?n => n end in
  let j := eval vm_compute in (n - 241)%nat in
  let yv := eval vm_compute in (nth j cmd_objs 0) in
  let Xl := fresh "Xl" in
  assert (Xl : ew E n = Z_to_bv 64 yv)
    by (rewrite (img_env_atomP E n HEI ltac:(unfold A_TEXT, A_LIM; lia)); change n with (A_OBJ j);
        rewrite (VOBJS j ltac:(vm_compute; lia)); reflexivity);
  rewrite Xl in Q; clear Xl.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the literals the placement test reads *)
Definition lit07 (y : Z) (sy : list byte) : Prop :=
(forall rd, cmd_ro_ok rd -> abytes_atR rd y (sy ++ [Z_to_bv 8 0])) /\
In (y, Z.of_nat (length sy) + 1) vr_shr /\
existsb (Z.eqb (y + Z.of_nat (length sy))) cmd_ro_ends = true /\
~ In (Z_to_bv 8 0) sy /\ 0x10000 <= y /\ y + Z.of_nat (length sy) + 1 <= 0x606000.
Lemma ro_lits07 : forall rd, cmd_ro_ok rd ->
abytes_atR rd 0x228a0 RO_lit_228a0 /\ abytes_atR rd 0x228c0 RO_lit_228c0 /\ abytes_atR rd 0x228e0 RO_lit_228e0.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. decompose [and] H. repeat split; assumption. Qed.
Ltac lit07_tac :=
split; [intros rd H; pose proof (ro_lits07 rd H) as X; decompose [and] X; assumption|];
split; [unfold vr_shr, vr_lits; cbn [map app fst snd]; repeat (first [left; reflexivity | right])|];
split; [vm_compute; reflexivity|];
split; [apply no0_07; vm_compute; reflexivity|];
split; apply Z.leb_le; vm_compute; reflexivity.
Lemma lit07_own : lit07 0x228a0 PV.Lit.place_own. Proof. lit07_tac. Qed.
Lemma lit07_default : lit07 0x228c0 PV.Lit.place_default. Proof. lit07_tac. Qed.
Lemma lit07_pool : lit07 0x228e0 PV.Lit.place_pool_prefix. Proof. lit07_tac. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis STRCMP : RtString.astrcmp_realizes SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis STRNCMP : RtString.astrncmp_realizes SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Hypothesis TL : PALib B.
Hypothesis SHOK : vr_shadow_ok B.
Hypothesis BLKT : vr_blktail B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let ART07 := art07 B MT TL ROA RRO RECC PROGU.

(* a literal at a call (the S06 kit's v6_lit_at) *)
Lemma lit07_at : forall (W : world SEGS) mem ly S md y sy, lit07 y sy -> vr_env B W mem -> AR SEGS B ly S W mem md ->
astr_atR (rdW W mem) y sy /\
(forall stk (regs : bvmap 5 word) n', alloc_ceiling <= spZ regs - stk -> 0 <= n' <= Z.of_nat (length sy) + 1 ->
 aread_ok SEGS stk W regs mem y n') /\
atail_vis SEGS W mem (y + Z.of_nat (length sy)) /\ 0x10000 <= y.
Proof.
intros W mem ly S md y sy (Hb & Hsh & Hend & Hn0 & Hy & Hye) HENV HAR.
pose proof HENV as (_ & _ & HROK & _).
pose proof (Hb _ HROK) as Hab.
destruct (SHOK ly S W mem md y _ HAR Hsh) as [Hra Hhv].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hvis : forall a, y <= a < y + (Z.of_nat (length sy) + 1) -> rdW W mem a <> None).
{ intros a Ha. assert (Hab' := Hab (Z.to_nat (a - y)) ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite Z2Nat.id in Hab' by lia. replace (y + (a - y)) with a in Hab' by lia. rewrite Hab'. discriminate. }
split; [split; [exact Hab | exact Hn0]|].
split.
{ intros stk regs n' Hsp Hn'. unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; split; [apply Hvis; lia | unfold ascratch_stk; lia]|].
  split; [left; lia|]. split; [apply (range_addressable_sub _ _ y (Z.of_nat (length sy) + 1) y n' Hra); lia|].
  intros Hn0'. unfold shadow_hull_vis in *. intros s Hs. apply Hhv.
  assert (A1 : shadow_addr (y + n' - 1) <= shadow_addr (y + (Z.of_nat (length sy) + 1) - 1))
    by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (A2 : shadow_addr (y + n' - 1) / 8 <= shadow_addr (y + (Z.of_nat (length sy) + 1) - 1) / 8) by (apply Z.div_le_mono; lia).
  lia. }
split; [|exact Hy].
destruct HROK as [_ HT]. apply existsb_exists in Hend as (e' & He' & Hq). apply Z.eqb_eq in Hq. subst e'.
intros a Ha. exact (HT _ He' a Ha).
Qed.

(* strcmp(tok[3], literal) and strncmp(tok[3], literal, 5) through a Theorem Labs lane's contracts *)
Lemma cmp07 : forall e pos F q c tp lyc Sc W regsT memT mdT k nm rl retk p x y sy (Q : world SEGS -> config -> Prop),
vr_ent B MT e ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE
  lyc Sc W regsT memT mdT ->
vr_line B e q W memT -> vr_copy B e F c tp W memT -> cs07 rl ->
getr regsT (Z_to_bv 5 1) = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
getr regsT (Z_to_bv 5 10) = w64 p -> getr regsT (Z_to_bv 5 11) = w64 y ->
nth_error tp 3 = Some p -> nth_error (PV.toks (e_D e)) 3 = Some x -> lit07 y sy ->
(forall regs2 mem2 md2,
  vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE
    lyc Sc W regs2 mem2 md2 ->
  vr_line B e q W mem2 -> vr_copy B e F c tp W mem2 -> (getr regs2 (Z_to_bv 5 10) = w64 0 <-> x = sy) ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA CS___interceptor_trampoline_strcmp)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros e pos F q c tp lyc Sc W regsT memT mdT k nm rl retk p x y sy Q Hent Hcore Hline Hcopy Hcs R1 Hr1 Hr2 R10 R11
  Hjp Hjw Hlit K.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
pose proof Hcore as (HJ & _ & _ & _ & _ & _ & _ & _ & Henv & Hrec & _ & Hperm & _).
pose proof (proj1 HJ) as HAR.
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (_ & _ & _ & _ & _ & Hspz & _ & _ & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vr_stk_ge as [Hstk4 Hstk5].
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. right. left. reflexivity. }
assert (Hsp2 : alloc_ceiling <= spZ regsT - 2 * ESTACK) by (rewrite Hspz; unfold ESTACK in *; lia).
destruct (tok_rt B BLKT e F c tp lyc Sc W memT mdT regsT (2 * ESTACK) 3 p x HAR Hcopy Hcb Hjp Hjw Hsp2) as (STRp & RDp & TLp).
destruct (tok_blk07 B e F c tp lyc Sc W memT mdT (e_R e) (e_O e) [vr_lb e q; vr_cb e c] 3 p x HAR Hcopy Hrec
  ltac:(right; left; reflexivity) Hperm Hjp Hjw) as (_ & _ & _ & _ & Hp4 & _ & _).
destruct (lit07_at W memT lyc Sc mdT y sy Hlit Henv HAR) as (HLs & HLr & HLt & Hy).
pose proof Henv as (HRO & _).
eapply (ART07 e pos F q c tp _ _ _ _ _ _ _ _ _ lyc Sc W regsT memT mdT (2 * ESTACK) (fun _ => False) _ retk
  (SIGMA CS___interceptor_trampoline_strcmp) Q Hcore Hline Hcopy ltac:(left; reflexivity) ltac:(right; left; reflexivity)
  HDn Hcs R1 Hr1 Hr2).
- unfold ESTACK. lia.
- intros a [].
- intros HPRE. apply (STRCMP lyc Sc W regsT memT mdT p y x sy HPRE R10 R11).
  + lia.
  + lia.
  + exact STRp.
  + apply astr_atR_view. exact HLs.
  + exact RDp.
  + apply HLr; [lia | unfold astr_len; lia].
  + exact TLp.
  + exact HLt.
  + exact (vr_rtrom_ok B W memT HRO).
- intros regs2 mem2 md2 Hc2 Hl2 Hcp2 HQ HP. exact (K regs2 mem2 md2 Hc2 Hl2 Hcp2 HQ).
Qed.

Lemma ncmp07 : forall e pos F q c tp lyc Sc W regsT memT mdT k nm rl retk p x y sy (Q : world SEGS -> config -> Prop),
vr_ent B MT e ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE
  lyc Sc W regsT memT mdT ->
vr_line B e q W memT -> vr_copy B e F c tp W memT -> cs07 rl ->
getr regsT (Z_to_bv 5 1) = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
getr regsT (Z_to_bv 5 10) = w64 p -> getr regsT (Z_to_bv 5 11) = w64 y -> getr regsT (Z_to_bv 5 12) = w64 5 ->
nth_error tp 3 = Some p -> nth_error (PV.toks (e_D e)) 3 = Some x -> lit07 y sy -> (5 <= length sy + 1)%nat ->
(forall regs2 mem2 md2,
  vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rl (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE
    lyc Sc W regs2 mem2 md2 ->
  vr_line B e q W mem2 -> vr_copy B e F c tp W mem2 ->
  (getr regs2 (Z_to_bv 5 10) = w64 0 <-> StrFun.strncmp_model (x ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) 5 = Some 0) ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA CS___interceptor_trampoline_strncmp)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros e pos F q c tp lyc Sc W regsT memT mdT k nm rl retk p x y sy Q Hent Hcore Hline Hcopy Hcs R1 Hr1 Hr2 R10 R11 R12
  Hjp Hjw Hlit Hsy K.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
pose proof Hcore as (HJ & _ & _ & _ & _ & _ & _ & _ & Henv & Hrec & _ & Hperm & _).
pose proof (proj1 HJ) as HAR.
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (_ & _ & _ & _ & _ & Hspz & _ & _ & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vr_stk_ge as [Hstk4 Hstk5].
assert (Hcb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. right. left. reflexivity. }
assert (Hsp2 : alloc_ceiling <= spZ regsT - 2 * ESTACK) by (rewrite Hspz; unfold ESTACK in *; lia).
destruct (tok_rt B BLKT e F c tp lyc Sc W memT mdT regsT (2 * ESTACK) 3 p x HAR Hcopy Hcb Hjp Hjw Hsp2) as (STRp & RDp & TLp).
destruct (tok_blk07 B e F c tp lyc Sc W memT mdT (e_R e) (e_O e) [vr_lb e q; vr_cb e c] 3 p x HAR Hcopy Hrec
  ltac:(right; left; reflexivity) Hperm Hjp Hjw) as (Hblk & _ & _ & _ & Hp4 & _ & _).
destruct (lit07_at W memT lyc Sc mdT y sy Hlit Henv HAR) as (HLs & HLr & HLt & Hy).
pose proof Henv as (HRO & _).
assert (RDp' : aread_ok SEGS (2 * ESTACK) W regsT memT p (Z.min 5 (astr_len x + 1))).
{ destruct RDp as (A1 & A2 & A3 & A4 & A5 & A6 & A7). unfold astr_len in *.
  assert (Hm : 0 <= Z.min 5 (Z.of_nat (length x) + 1) <= Z.of_nat (length x) + 1) by lia.
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply A4; lia|].
  split; [unfold amem_range in *; lia|].
  split; [apply (range_addressable_sub _ _ p (Z.of_nat (length x) + 1) p (Z.min 5 (Z.of_nat (length x) + 1)) A6); lia|].
  intros Hn0'. pose proof (A7 ltac:(lia)) as Hhv. unfold shadow_hull_vis in *. intros s Hs. apply Hhv.
  assert (B1 : shadow_addr (p + Z.min 5 (Z.of_nat (length x) + 1) - 1) <= shadow_addr (p + (Z.of_nat (length x) + 1) - 1))
    by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (B2 : shadow_addr (p + Z.min 5 (Z.of_nat (length x) + 1) - 1) / 8 <=
    shadow_addr (p + (Z.of_nat (length x) + 1) - 1) / 8) by (apply Z.div_le_mono; lia).
  lia. }
eapply (ART07 e pos F q c tp _ _ _ _ _ _ _ _ _ lyc Sc W regsT memT mdT (2 * ESTACK) (fun _ => False) _ retk
  (SIGMA CS___interceptor_trampoline_strncmp) Q Hcore Hline Hcopy ltac:(left; reflexivity) ltac:(right; left; reflexivity)
  HDn Hcs R1 Hr1 Hr2).
- unfold ESTACK. lia.
- intros a [].
- intros HPRE. apply (STRNCMP lyc Sc W regsT memT mdT p y 5 x sy HPRE R10 R11 R12).
  + lia.
  + lia.
  + lia.
  + exact STRp.
  + apply astr_atR_view. exact HLs.
  + exact RDp'.
  + apply (amem8_of_blockA SEGS B (YG0q.AR_laws_ok SEGS B) lyc Sc W memT mdT); [exact HAR | exact Hblk | unfold astr_len; lia].
  + apply HLr; [lia | unfold astr_len; lia].
  + destruct Hlit as (_ & _ & _ & _ & _ & Hye). apply amem8_of_low; unfold astr_len, kLowMemEnd; lia.
  + exact TLp.
  + exact HLt.
  + exact (vr_rtrom_ok B W memT HRO).
- intros regs2 mem2 md2 Hc2 Hl2 Hcp2 HQ HP. exact (K regs2 mem2 md2 Hc2 Hl2 Hcp2 HQ).
Qed.

End e.
End f.
End d.
