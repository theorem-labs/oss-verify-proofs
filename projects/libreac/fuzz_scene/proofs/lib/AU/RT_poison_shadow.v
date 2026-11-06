(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan instance of lib/Reusable/AsStackLeaf.v's poison_shadow_realizes, at
   __asan::PoisonShadow = 0x55be4 of the pinned image fuzz_scene.asan-ubsan (libreac/fuzz_scene). The walk is the
   cgif-family symbolic-run table walk (released cgif_rgb_fuzzer lib/YF9a.v / YF9c.v run the same body inline inside
   the class-7 stack-malloc walk), over the AU start-up tables. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB1v YB1w YE34 YF0l YF0m YF0x YE2y YE3d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackLeaf RT_PoisonFrameLaw.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).

(* ---------- the body and the cells it reads (MEASURED, fuzz_scene.asan-ubsan) ---------- *)
Definition PS_ENTRY : Z := 0x55be4.
Definition ps_ranges : list (Z * nat) := [(PS_ENTRY, 319%nat)].
Definition tbl_ps : ctable := Eval vm_compute in build_ranges ps_ranges TEmpty.
Lemma tbl_ps_eq : tbl_ps = build_ranges ps_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tbl_ps). Qed.
Lemma tbl_ps_ok : table_ok tfibsegs tbl_ps.
Proof. rewrite tbl_ps_eq. apply build_ranges_ok; [unfold ps_ranges; repeat constructor; cbn; discriminate | exact (table_ok_empty tfibsegs)]. Qed.

(* can_poison_memory, the shadow-offset cell, kMidMemBeg / kMidMemEnd / kHighMemEnd, REAL(memset) and
   clear_shadow_mmap_threshold, with the GOT words that reach them. Every row is in AU/YF0m.v's Tfib_const.
   By section of the asan-ubsan image (a Theorem Labs lane's import check, 2026-10-29 03:10Z, from the unstripped twin):
   FILE-BACKED -- the value is the image's own bytes:
     .got  0x9ba30 -> 0x135628 (common_flags)  0x9ba40 -> 0xa3af8   0x9ba48 -> 0xa47e8
     .got  0x9ba50 -> 0xa47f0                  0x9ba58 -> 0xa47e0   0x9ba60 -> 0x9d8b0
     .data 0x9d8b0 (__interception::real_memset) -> 0x95174 (musl memset)
   NOBITS (.bss) -- NOT a file fact: the value is the START-UP STATE, measured by a Theorem Labs lane in all 50 of
   scene's collected hand-off states, and it enters through the start-up certificate that supplies Tfib_const:
     0xa335c = 1 (can_poison_memory)   0xa3af8 = 0x7fff8000 (__asan_shadow_memory_dynamic_address)
     0xa47e8 = 0 (kMidMemBeg)          0xa47f0 = 0 (kMidMemEnd)   0xa47e0 = 0x7fffffffffff (kHighMemEnd)
     0x1356a0 = 2^64-1 (common_flags+0x78, clear_shadow_mmap_threshold) *)
Definition ps_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
[(0xa335c, 1, [(0, 1%N, 1)]);
(0x9ba40, 8, [(0, 8%N, 0xa3af8)]); (0xa3af8, 8, [(0, 8%N, 0x7fff8000)]);
(0x9ba48, 8, [(0, 8%N, 0xa47e8)]); (0xa47e8, 8, [(0, 8%N, 0)]);
(0x9ba50, 8, [(0, 8%N, 0xa47f0)]); (0xa47f0, 8, [(0, 8%N, 0)]);
(0x9ba58, 8, [(0, 8%N, 0xa47e0)]); (0xa47e0, 8, [(0, 8%N, 0x7fffffffffff)]);
(0x9ba60, 8, [(0, 8%N, 0x9d8b0)]); (0x9d8b0, 8, [(0, 8%N, 0x95174)]);
(0x9ba30, 8, [(0, 8%N, 0x135628)]); (0x1356a0, 8, [(0, 8%N, 18446744073709551615)])].
Lemma ps_rodata_chk : forall ly, rodata_chk ly ps_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Definition RUN (s : sstate) := sym_runN tfibsegs tbl_ps FUEL s.

(* ---------- the entry state: one stack window, the rodata cells, four atom facts ---------- *)
Definition stk : YP09.region := YP09.mkRegion (Some 2%nat) (- PS_STK) 0 (- PS_STK) 0 [].
Definition P_HI_LO : Z := kHighMemBeg.
Definition P_HI_HI : Z := 0x7fffff800000 - 8.
Definition P_LO_LO : Z := 4096.
Definition P_LO_HI : Z := kLowShadowBeg - 8.
Definition N_MAX : Z := 2 ^ 20.
Definition facts_of (plo phi : Z) : list (nat * afact) :=
[(2%nat, mkAF (kHighMemBeg + PS_STK) kHighMemEnd 4); (10%nat, mkAF plo phi 3);
(11%nat, mkAF 8 N_MAX 3); (12%nat, mkAF 0 255 0)].
Definition ss_ent (plo phi : Z) : sstate :=
mkSS PS_ENTRY sr_atoms (stk :: map ro_region ps_rodata) None (mkFacts (facts_of plo phi) [] []).
Definition ss_z (hi : bool) : sstate := if hi then ss_ent P_HI_LO P_HI_HI else ss_ent P_LO_LO P_LO_HI.

(* ---------- the walk: run, stop at a branch, add the measured condition, run on ---------- *)
Fixpoint runc (cs : list acond) (s : sstate) : sstate * run_status :=
match cs with
| [] => RUN s
| c :: cs' => match RUN s with
| (s1, RS_stopped (SR_branch _ _ _)) => runc cs' (add_cond s1 c)
| r => r
end
end.
Definition base_is2 (b : option nat) : bool := match b with Some n => Nat.eqb n 2 | None => false end.
Definition win_stk (r : YP09.region) : bool :=
if base_is2 (YP09.r_base r)
then (- PS_STK <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0)
else YP09.r_whi r <=? YP09.r_wlo r.
Definition wins_stk (s : sstate) : bool := forallb win_stk (ss_mem s).
Fixpoint runc_win (cs : list acond) (s : sstate) : bool :=
wins_stk s &&
match cs with
| [] => true
| c :: cs' => match RUN s with
| (s1, RS_stopped (SR_branch _ _ _)) => runc_win cs' (add_cond s1 c)
| _ => true
end
end.

(* The three measured branch conditions of the body. *)
Definition C_v0 : acond := mkAC BC_EQ (SOff 12 0) (SLit 0).
Definition C_vn : acond := mkAC BC_NE (SOff 12 0) (SLit 0).
Definition C_lo : acond := mkAC BC_GEU (SLit 2147450879) (SAlu ALU_ADD (SOff 10 (-8)) (SOff 11 0)).
Definition CNT : sv :=
SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 (-8)) (SOff 11 0)) (SLit 3)) (SLit 1))
(SAlu ALU_SRL (SOff 10 0) (SLit 3)).
Definition THR : Z := 18446744073709551615.
Definition C_thr : acond := mkAC BC_LTU CNT (SLit THR).
Definition conds (hi v0 : bool) : list acond :=
(if v0 then [C_v0] else [C_vn]) ++ (if hi then [] else [C_lo]) ++ (if v0 then [C_thr] else []).

Definition e_HN : sstate := Eval vm_compute in fst (runc (conds true false) (ss_z true)).
Definition e_HZ : sstate := Eval vm_compute in fst (runc (conds true true) (ss_z true)).
Definition e_LN : sstate := Eval vm_compute in fst (runc (conds false false) (ss_z false)).
Definition e_LZ : sstate := Eval vm_compute in fst (runc (conds false true) (ss_z false)).
Definition e_ps (hi v0 : bool) : sstate :=
if hi then (if v0 then e_HZ else e_HN) else (if v0 then e_LZ else e_LN).
Lemma r_ps : forall hi v0, runc (conds hi v0) (ss_z hi) = (e_ps hi v0, RS_stopped SR_fetch).
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.
Lemma w_ps : forall hi v0, runc_win (conds hi v0) (ss_z hi) = true.
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.

(* The shape at the tail jump into musl memset: a0 = shadow_addr p, a1 = v, a2 = n/8, callee-saved kept. *)
Definition A0E : sv := SAlu ALU_ADD (SLit 2147450880) (SAlu ALU_SRL (SOff 10 0) (SLit 3)).
Definition A2E : sv := SAlu ALU_ADD CNT (SLit 0).
Definition keep_regs : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition shape_ps (s : sstate) : bool :=
(ss_pc s =? tfib_A_musl_memset) && (match ss_resv s with None => true | _ => false end) &&
sv_eqb (sr_get (ss_regs s) 10%bv) A0E && sv_eqb (sr_get (ss_regs s) 11%bv) (SOff 12 0) &&
sv_eqb (sr_get (ss_regs s) 12%bv) A2E &&
forallb (fun r => sv_eqb (RG s r) (SOff (Z.to_nat r) 0)) keep_regs.
Lemma shape_ok : forall hi v0, shape_ps (e_ps hi v0) = true.
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.

(* region 0 of the end state is still the caller's stack window: the body's spills are inside it. *)
Definition stk0_ok (s : sstate) : bool :=
match ss_mem s with
| r :: _ => base_is2 (YP09.r_base r) && (YP09.r_wlo r <=? - PS_STK) && (0 <=? YP09.r_whi r)
| [] => false
end.
Lemma stk0_ps : forall hi v0, stk0_ok (e_ps hi v0) = true.
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.

(* ---------- the walk lemmas ---------- *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma ps_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_ps FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_ps tbl_ps_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.

Lemma st_ok_add_cond' : forall E ss ms c, st_ok tfibsegs E ss ms -> acond_ok E c -> st_ok tfibsegs E (add_cond ss c) ms.
Proof. intros E ss ms [cc ca cb] HS HC. exact (st_ok_add_cond tfibsegs E ss ms cc ca cb HS HC). Qed.

Lemma win_stk_sound : forall E s a, wins_stk s = true -> in_wrange E (ss_mem s) a ->
bv_unsigned (ew E 2) - PS_STK <= a < bv_unsigned (ew E 2).
Proof.
intros E s a Hw (r & Hin & Ha). unfold wins_stk in Hw. rewrite forallb_forall in Hw.
specialize (Hw r Hin). unfold win_stk, base_is2 in Hw.
destruct (YP09.r_base r) as [k|]; cbn [base_val] in Ha.
- destruct (Nat.eqb k 2) eqn:Hk2.
+ apply Nat.eqb_eq in Hk2. subst k.
apply andb_prop in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
+ apply Z.leb_le in Hw. lia.
- apply Z.leb_le in Hw. lia.
Qed.

Lemma stk0_apresent : forall (Hb : word -> bool) E ss ms a,
stk0_ok ss = true -> st_ok tfibsegs E ss (restrict Hb ms) ->
bv_unsigned (ew E 2) - PS_STK <= a < bv_unsigned (ew E 2) ->
TFIB_IMG_END <= a < 2 ^ 64 -> apresent Hb (ms_mem ms) a.
Proof.
intros Hb E ss ms a Hok HS Ha Hr. unfold stk0_ok in Hok.
destruct (ss_mem ss) as [|r0 rest] eqn:Em; [discriminate|].
apply (YF0x.st_ok_window_apresent Hb E ss ms 0%nat r0 a HS); [rewrite Em; reflexivity | | exact Hr].
apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [Hbb H2].
unfold base_is2 in Hbb. destruct (YP09.r_base r0) as [k|]; [|discriminate].
apply Nat.eqb_eq in Hbb. subst k. cbn [base_val].
apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.

Lemma walk : forall (W : world tfibsegs) E cs ss ss' ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> conds_ok E cs ->
runc cs ss = (ss', RS_stopped SR_fetch) -> runc_win cs ss = true ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\
(forall z : word, ~ (bv_unsigned (ew E 2) - PS_STK <= bv_unsigned z < bv_unsigned (ew E 2)) -> ms_mem ms1 z = ms_mem ms z)).
Proof.
intros W E cs. induction cs as [|c cs IH]; intros ss ss' ms md HS HC Hrun Hwin.
- cbn [runc] in Hrun. cbn [runc_win] in Hwin. rewrite andb_true_r in Hwin.
eapply SRr_bind; [apply (ps_phase W E ss ss' _ ms md HS Hrun)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _).
apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|].
intros z Hz. apply HF1. intros Hin. apply Hz. exact (win_stk_sound E ss _ Hwin Hin).
- cbn [runc] in Hrun. cbn [runc_win] in Hwin.
destruct (RUN ss) as [s1 st1] eqn:E1.
apply andb_prop in Hwin as [Hw0 Hwin].
destruct HC as [HCc HCs].
destruct st1 as [| | why]; try discriminate Hrun.
destruct why; try discriminate Hrun.
{ assert (Es : s1 = ss') by congruence. subst s1.
eapply SRr_bind; [apply (ps_phase W E ss ss' _ ms md HS E1)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _).
apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|].
intros z Hz. apply HF1. intros Hin. apply Hz. exact (win_stk_sound E ss _ Hw0 Hin). }
eapply SRr_bind; [apply (ps_phase W E ss s1 _ ms md HS E1)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _).
eapply SRr_bind; [apply (IH (add_cond s1 c) ss' ms1 _ (st_ok_add_cond' E s1 _ c HS1 HCc) HCs Hrun Hwin)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2).
apply SRr_ret. split; [reflexivity|]. exists ms2, mat2.
split; [f_equal; apply wvb_collapse|].
split; [exact HS2|].
intros z Hz. rewrite (HF2 z Hz). apply HF1. intros Hin. apply Hz. exact (win_stk_sound E ss _ Hw0 Hin).
Qed.
End b.

(* ---------- the denotation of the three conditions and of the tail shape ---------- *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma U_CNT : forall E p n, ew E 10 = w64 p -> ew E 11 = w64 n ->
0 < p -> p mod 8 = 0 -> 0 < n -> n mod 8 = 0 -> p + n <= 2 ^ 63 -> U E CNT = n / 8.
Proof.
intros E p n H10 H11 Hp0 Hp8 Hn0 Hn8 Hhi.
assert (Rp : 0 <= p < 2 ^ 64) by lia. assert (Rn : 0 <= n < 2 ^ 64) by lia.
assert (Hp' : ew E 10 = Z_to_bv 64 p) by exact H10. assert (Hn' : ew E 11 = Z_to_bv 64 n) by exact H11.
assert (Bp : 0 <= p / 8 <= 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Bn : 1 <= n / 8 <= 2 ^ 60) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (HA : U E (SAlu ALU_ADD (SOff 10 (-8)) (SOff 11 0)) = p - 8 + n).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E 10 p (-8) Hp' Rp ltac:(lia)), (U_atom E 11 n Hn' Rn).
apply zcanon_small. lia. }
assert (D1 : (p - 8 + n) / 8 = p / 8 + n / 8 - 1).
{ pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn.
rewrite Hp8, Z.add_0_r in Dp. rewrite Hn8, Z.add_0_r in Dn.
replace (p - 8 + n) with ((p / 8 + n / 8 - 1) * 8) by lia. apply Z_div_mult. lia. }
assert (HS1 : U E (SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 (-8)) (SOff 11 0)) (SLit 3)) = p / 8 + n / 8 - 1)
by (rewrite U_srl3, HA; exact D1).
assert (HS2 : U E (SAlu ALU_SRL (SOff 10 0) (SLit 3)) = p / 8)
by (rewrite U_srl3, (U_atom E 10 p Hp' Rp); reflexivity).
assert (HAdd : U E (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 (-8)) (SOff 11 0)) (SLit 3)) (SLit 1))
= p / 8 + n / 8).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite HS1, U_SLit. change (zcanon 1) with 1.
rewrite (zcanon_small (p / 8 + n / 8 - 1 + 1)) by lia. lia. }
unfold CNT. rewrite U_SAlu. cbn [zalu_raw]. rewrite HAdd, HS2.
replace (p / 8 + n / 8 - p / 8) with (n / 8) by lia. apply zcanon_small. lia.
Qed.

Lemma A0E_denot : forall E p, ew E 10 = w64 p -> 0 <= p < 2 ^ 64 ->
sv_denot E A0E = w64 (shadow_addr p).
Proof.
intros E p H10 Rp. assert (Hp' : ew E 10 = Z_to_bv 64 p) by exact H10.
unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E A0E)). f_equal.
change (bv_unsigned (sv_denot E A0E)) with (U E A0E).
unfold A0E. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_srl3, (U_atom E 10 p Hp' Rp).
unfold shadow_addr, SHADOW_OFF. change (zcanon 2147450880) with 2147450880.
pose proof (Z.div_pos p 8 ltac:(lia)). pose proof (Z.div_le_upper_bound p 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
apply zcanon_small. lia.
Qed.

Lemma A2E_denot : forall E p n, ew E 10 = w64 p -> ew E 11 = w64 n ->
0 < p -> p mod 8 = 0 -> 0 < n -> n mod 8 = 0 -> p + n <= 2 ^ 63 -> sv_denot E A2E = w64 (n / 8).
Proof.
intros E p n H10 H11 Hp0 Hp8 Hn0 Hn8 Hhi.
unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E A2E)). f_equal.
change (bv_unsigned (sv_denot E A2E)) with (U E A2E).
unfold A2E. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_CNT E p n H10 H11 Hp0 Hp8 Hn0 Hn8 Hhi). change (zcanon 0) with 0. rewrite Z.add_0_r.
assert (Bn : 0 <= n / 8 <= 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
apply zcanon_small. lia.
Qed.

Lemma cond_v0 : forall E v, ew E 12 = w64 v -> 0 <= v < 256 -> v = 0 -> acond_ok E C_v0.
Proof.
intros E v H12 Rv ->. unfold acond_ok, C_v0. cbn [ac_c ac_a ac_b].
rewrite branch_eq_U, U_SLit, (U_atom E 12 0 H12 ltac:(lia)). reflexivity.
Qed.
Lemma cond_vn : forall E v, ew E 12 = w64 v -> 0 <= v < 256 -> v <> 0 -> acond_ok E C_vn.
Proof.
intros E v H12 Rv Hv. unfold acond_ok, C_vn. cbn [ac_c ac_a ac_b].
rewrite branch_ne_U, U_SLit, (U_atom E 12 v H12 ltac:(lia)). change (zcanon 0) with 0.
apply negb_true_iff. apply Z.eqb_neq. exact Hv.
Qed.
Lemma cond_lo : forall E p n, ew E 10 = w64 p -> ew E 11 = w64 n ->
8 <= p -> 0 <= n -> p + n <= 2147450887 -> acond_ok E C_lo.
Proof.
intros E p n H10 H11 Hp Hn Hpn. unfold acond_ok, C_lo. cbn [ac_c ac_a ac_b].
assert (Hp' : ew E 10 = Z_to_bv 64 p) by exact H10. assert (Hn' : ew E 11 = Z_to_bv 64 n) by exact H11.
rewrite branch_geu_U, U_SLit, U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 10 p (-8) Hp' ltac:(lia) ltac:(lia)), (U_atom E 11 n Hn' ltac:(lia)).
rewrite (zcanon_small (p + -8 + n)) by lia. change (zcanon 2147450879) with 2147450879.
apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma cond_thr : forall E p n, ew E 10 = w64 p -> ew E 11 = w64 n ->
0 < p -> p mod 8 = 0 -> 0 < n -> n mod 8 = 0 -> p + n <= 2 ^ 63 -> acond_ok E C_thr.
Proof.
intros E p n H10 H11 Hp0 Hp8 Hn0 Hn8 Hhi. unfold acond_ok, C_thr. cbn [ac_c ac_a ac_b].
rewrite branch_ltu_U, U_SLit, (U_CNT E p n H10 H11 Hp0 Hp8 Hn0 Hn8 Hhi).
change (zcanon THR) with THR. unfold THR.
assert (Bn : 0 <= n / 8 <= 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
apply Z.ltb_lt. lia.
Qed.
End c.

(* ---------- the instance ---------- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.

Theorem scene_poison_shadow_au : AsStackLeaf.poison_shadow_realizes tfibsegs B PS_ENTRY.
Proof.
intros ly S W regs mem md cid pos p n v HAR Hra Hal16 Hslo Htop HpresE Hgp Htp
Hcid Hpos G10 G11 G12 Hv Hn0 Hn8 Hp8 Hfa1 Hfa2 Hsh.
set (H := w_H W) in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (YG0t.F_app ly HLY) as (FH0 & FHZ & _). ceil.
pose proof (frame_off_bounds cid pos Hcid Hpos) as (FO1 & FO2 & FO3 & FO4 & FO5 & FO6).
set (F := ly_F ly) in *. set (sp0 := spZ regs) in *.
assert (HFA : F + kFakeFramesOff + cid * 2 ^ 20 <= frame_addr ly cid pos /\
frame_addr ly cid pos + fs_frame_bytes cid <= F + kFakeStackSize)
by (unfold frame_addr; fold F; unfold kFakeStackSize in *; lia).
assert (HNB : n <= N_MAX).
{ unfold N_MAX. assert (fs_frame_bytes cid <= 2 ^ 20) by (unfold kFakeFramesOff in *; lia). lia. }
assert (Hp4k : 4096 <= p) by (unfold kFakeFramesOff, kFakeStackSize in *; lia).
assert (Hp0 : 0 < p) by lia.
assert (HPN : p + n <= F + kFakeStackSize) by lia.
assert (HCEIL : F + kFakeStackSize <= kLowShadowBeg \/ (kHighMemBeg <= F /\ F + kFakeStackSize <= ASAN_CEIL))
by exact FHZ.
assert (Rp64 : 0 <= p < 2 ^ 64) by (unfold kLowShadowBeg, ASAN_CEIL, kHighMemBeg in *; lia).
assert (Rn64 : 0 <= n < 2 ^ 64) by (unfold N_MAX in *; lia).
assert (Hpn63 : p + n <= 2 ^ 63) by (unfold kLowShadowBeg, ASAN_CEIL, kHighMemBeg in *; lia).
assert (Hsp44 : kHighMemBeg + PS_STK <= sp0 <= kHighMemEnd) by (unfold PS_STK in *; lia).
assert (SPR : 0 <= sp0 < 2 ^ 64) by (unfold kHighMemBeg, kHighMemEnd, PS_STK in Hsp44; lia).
(* the shadow range of the write, and its place inside the frame's shadow *)
set (SHADR := shadow_addr p) in *. set (CNTZ := n / 8) in *.
assert (BCNT : 1 <= CNTZ <= 2 ^ 17)
by (unfold CNTZ, N_MAX in *; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (SHB : kLowMemEnd <= SHADR /\ SHADR + CNTZ <= kHighMemBeg).
{ unfold SHADR, CNTZ. split.
- unfold shadow_addr, SHADOW_OFF, kLowMemEnd. pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)). lia.
- pose proof (shadow_range_below p n ltac:(lia) ltac:(lia)
ltac:(unfold kHighMemEnd, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in *; lia)) as SR. exact SR. }
assert (SHR : 0 <= SHADR /\ SHADR + CNTZ < 2 ^ 64)
by (unfold kLowMemEnd, kHighMemBeg in SHB; lia).
assert (DISJ : SHADR + CNTZ <= sp0 - PS_STK) by (unfold PS_STK in *; lia).
assert (FSH : shadow_addr (frame_addr ly cid pos) <= SHADR /\
SHADR + CNTZ <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8).
{ set (fa := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *.
assert (Hfa8 : fa mod 8 = 0).
{ unfold fa, frame_addr. fold F. pose proof (lo_F_al ly HLY) as FAL. unfold page_aligned in FAL.
apply Z.mod_divide; [lia|]. apply Z.mod_divide in FAL; [|lia]. apply Z.mod_divide in FO3; [|lia].
destruct FAL as [k1 Hk1]. destruct FO3 as [k2 Hk2]. exists (k1 * 512 + k2 * 8). lia. }
assert (Hfb8 : fb mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in FO5; [|lia];
destruct FO5 as [k Hk]; exists (k * 8); lia).
assert (Hfa0 : 0 <= fa) by (unfold kFakeFramesOff in *; lia).
assert (Hfb0 : 0 <= fb) by lia.
unfold SHADR, CNTZ, shadow_addr. split.
- pose proof (Z.div_le_mono fa p 8 ltac:(lia) ltac:(lia)). lia.
- assert (Hsum : p / 8 + n / 8 <= fa / 8 + fb / 8).
{ pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn.
pose proof (Z.div_mod fa 8 ltac:(lia)) as Dfa. pose proof (Z.div_mod fb 8 ltac:(lia)) as Dfb.
rewrite Hp8, Z.add_0_r in Dp. rewrite Hn8, Z.add_0_r in Dn.
rewrite Hfa8, Z.add_0_r in Dfa. rewrite Hfb8, Z.add_0_r in Dfb. lia. }
lia. }
(* the goal's post, named *)
match goal with |- SRr _ _ _ ?QQ => set (Qpost := QQ) end.
set (EE := YE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r)
by (intros; apply YE2y.Env_reg; assumption).
assert (E2 : ew EE 2 = w64 sp0)
by (rewrite (EEreg 2%nat 2%bv eq_refl); unfold sp0, spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (E10 : ew EE 10 = w64 p) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (E11 : ew EE 11 = w64 n) by (rewrite (EEreg 11%nat 11%bv eq_refl); exact G11).
assert (E12 : ew EE 12 = w64 v) by (rewrite (EEreg 12%nat 12%bv eq_refl); exact G12).
assert (U2 : bv_unsigned (ew EE 2) = sp0) by (rewrite E2; apply unsigned_lit_small; exact SPR).
assert (U2' : bv_unsigned (ew (Ereg regs []) 2) = sp0) by exact U2.
assert (E10' : ew (Ereg regs []) 10 = w64 p) by exact E10.
assert (E11' : ew (Ereg regs []) 11 = w64 n) by exact E11.
assert (E12' : ew (Ereg regs []) 12 = w64 v) by exact E12.
(* the tail: from the entry of musl memset to the post *)
assert (FIN : forall regs1 mem1 mat1,
getr regs1 10 = w64 SHADR -> getr regs1 11 = w64 v -> getr regs1 12 = w64 CNTZ ->
(forall r, In r keep_regs -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall z : word, ~ (sp0 - PS_STK <= bv_unsigned z < sp0) -> mem1 z = mem z) ->
(forall a, sp0 - PS_STK <= a < sp0 -> apresent H mem1 a) ->
SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 tfib_A_musl_memset) mem1 (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md) mat1 md)) Qpost).
{
intros regs1 mem1 mat1 A10 A11 A12 KEEP1 MEQ1 PRE1.
pose proof YF0x.Hwx_tfa as Hwx.
assert (A1 : getr regs1 1 = getr regs 1) by (apply (KEEP1 1); unfold keep_regs; cbn [In]; tauto).
assert (PRs : forall a, SHADR <= a < SHADR + CNTZ -> apresent H mem a) by exact Hsh.
assert (DW : forall a, SHADR <= a < SHADR + CNTZ -> writable_at tfibsegs (mrestrict H mem1) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (PRs a Ha) as [Hh [b Hb]]. split; [|exact Hh].
apply YE2y.apresent_writable. split; [exact Hh|]. exists b. rewrite MEQ1; [exact Hb|].
rewrite unsigned_lit_small by lia. lia. }
set (nn := Z.to_nat CNTZ). assert (Hnn : Z.of_nat nn = CNTZ) by (subst nn; lia).
assert (SOK : store_ok tfibsegs (mrestrict H mem1) (w64 SHADR) nn = true).
{ apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by lia; [lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(lia))) as Wz. unfold writable_at in Wz.
rewrite Z_to_bv_bv_unsigned in Wz. exact Wz. }
destruct (tfib_memset (w64 SHADR) (w64 v) (w64 CNTZ) nn (mrestrict H mem1) (seg_rom tfibsegs) regs1 A10 A11 A12
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) SOK
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia))
as (regs2 & Hms & B10 & Hkeep).
rewrite A1, Hra in Hms.
set (cb := Z_to_bv 8 (bv_unsigned (w64 v) mod 256)) in Hms.
set (m1r := mrestrict H mem1) in *. set (m2r := wbytes m1r (w64 SHADR) (repeat cb nn)) in Hms.
set (mem2 := munrestrict H mem1 m2r).
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _.
pose proof (same_but_materialized_trans _ _ _ (with_vm_backing_same md mat1) Hsbm) as HSBM.
change (unrestrict H mem1 (mkst regs2 (getr regs 1) m2r (seg_rom tfibsegs)))
with (mkst regs2 (getr regs 1) mem2 (seg_rom tfibsegs)).
assert (LEN : Z.of_nat (length (repeat cb nn)) = CNTZ) by (rewrite repeat_length; exact Hnn).
assert (M2out : forall z : word, ~ (SHADR <= bv_unsigned z < SHADR + CNTZ) -> mem2 z = mem1 z).
{ intros z Hz. subst mem2 m2r. unfold munrestrict. destruct (H z) eqn:Hh; [reflexivity|].
assert (Ew : wbytes m1r (w64 SHADR) (repeat cb nn) z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) SHADR) as [L|L].
- apply wbytes_below; unfold w64; rewrite ?LEN, unsigned_lit_small by lia; lia.
- apply wbytes_above. unfold w64. rewrite LEN, unsigned_lit_small by lia. lia. }
rewrite Ew. subst m1r. unfold mrestrict. rewrite Hh. reflexivity. }
assert (M2in : forall i, 0 <= i < CNTZ -> mem2 (Z_to_bv 64 (SHADR + i)) = Some cb).
{ intros i Hi. subst mem2. unfold munrestrict. rewrite (proj2 (DW (SHADR + i) ltac:(lia))).
subst m2r. rewrite (YE2y.wbytes_inside (repeat cb nn) m1r (w64 SHADR) (Z_to_bv 64 (SHADR + i)));
unfold w64; rewrite ?LEN, ?unsigned_lit_small by lia; [|lia|lia].
replace (Z.to_nat (SHADR + i - SHADR)) with (Z.to_nat i) by lia. apply nth_error_repeat. lia. }
assert (CB : bv_unsigned cb = v).
{ subst cb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold w64.
rewrite unsigned_lit_small by lia. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
assert (MOUT : forall z : word, ~ (SHADR <= bv_unsigned z < SHADR + CNTZ) ->
~ (sp0 - PS_STK <= bv_unsigned z < sp0) -> mem2 z = mem z).
{ intros z H1 H2. rewrite (M2out z H1). apply MEQ1. exact H2. }
assert (AVout : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADR <= a < SHADR + CNTZ) -> ~ (sp0 - PS_STK <= a < sp0) ->
aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Hr H1 H2. apply YF0x.aview_same. apply MOUT; rewrite unsigned_lit_small by lia; assumption. }
assert (AVin : forall i, 0 <= i < CNTZ -> aview tfibsegs H mem2 (SHADR + i) = Some v).
{ intros i Hi. unfold aview, mbyte, mrestrict. rewrite (proj2 (DW (SHADR + i) ltac:(lia))), (M2in i Hi).
cbn [option_map]. rewrite CB. reflexivity. }
assert (PRE2 : forall a, sp0 - PS_STK <= a < sp0 -> apresent H mem2 a).
{ intros a Ha. apply (YF0x.apresent_same H mem1); [apply M2out; rewrite unsigned_lit_small by lia; lia|].
apply PRE1. exact Ha. }
assert (PW : forall a, (SHADR <= a < SHADR + CNTZ \/ sp0 - PS_STK <= a < sp0) -> apresent H mem2 a).
{ intros a [Ha|Ha]; [|exact (PRE2 a Ha)].
split.
- exact (proj2 (DW a Ha)).
- exists cb. replace a with (SHADR + (a - SHADR)) by lia. apply M2in. lia. }
pose proof (same_but_materialized_frame md model' HSBM) as MF.
apply SRr_ret. unfold Qpost. cbv beta. split; [reflexivity|].
exists regs2, mem2, model'.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ (* AR is kept *)
apply (RT_PoisonFrameLaw.AR_poison_frame tfibsegs B ly S W mem md mem2 model' cid pos HAR Hcid Hpos).
- intros a Hr Hown Hnf. apply AVout; [exact Hr| |].
+ intros Ha. apply Hnf. unfold RT_PoisonFrameLaw.frame_shadow, in_zr. cbn [fst snd]. lia.
+ intros Ha. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold PS_STK in *; lia) Hown).
- intros a Hvw. rewrite (YE2y.aview_mod _ mem2 a). rewrite (YE2y.aview_mod _ mem a) in Hvw.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' SHADR) as [L1|L1].
+ destruct (Z_lt_le_dec a' (sp0 - PS_STK)) as [L3|L3];
[rewrite AVout by lia; exact Hvw|].
destruct (Z_lt_le_dec a' sp0) as [L4|L4];
[apply YE2y.aview_some_of_apresent; apply PW; right; lia | rewrite AVout by lia; exact Hvw].
+ destruct (Z_lt_le_dec a' (SHADR + CNTZ)) as [L2|L2];
[apply YE2y.aview_some_of_apresent; apply PW; left; lia|].
destruct (Z_lt_le_dec a' (sp0 - PS_STK)) as [L3|L3];
[rewrite AVout by lia; exact Hvw|].
destruct (Z_lt_le_dec a' sp0) as [L4|L4];
[apply YE2y.aview_some_of_apresent; apply PW; right; lia | rewrite AVout by lia; exact Hvw].
- apply MF. - apply MF. - apply MF.
- intros a Hb Hh. change (w_H W (w64 a)) with (H (Z_to_bv 64 a)) in Hh.
apply MOUT; unfold w64; rewrite unsigned_lit_small by (exact (YE2y.in_band_rw_u64 a Hb)); intros Ha.
+ rewrite (proj2 (DW a Ha)) in Hh. discriminate.
+ destruct (HpresE a Ha) as [Hh0 _]. rewrite Hh0 in Hh. discriminate. }
split.
{ (* callee-saved *)
intros r Hr.
assert (NE : forall x : bv 5, 11 <= bv_unsigned x <= 16 -> Z_to_bv 5 r <> x).
{ intros x Hx Eq. rewrite <- Eq in Hx. rewrite Z_to_bv_unsigned in Hx. unfold bv_wrap in Hx.
change (bv_modulus 5) with 32 in Hx. unfold acallee_saved in Hr. rewrite Z.mod_small in Hx by lia. lia. }
rewrite Hkeep; [apply KEEP1; unfold acallee_saved in Hr; unfold keep_regs; cbn [In]; lia | | | | | |];
apply NE; (split; apply Z.leb_le; reflexivity). }
split; [exact HSBM|].
split.
{ intros i Hi. fold CNTZ in Hi. fold SHADR. apply AVin. exact Hi. }
split.
{ intros a Hr Ha1 Ha2. apply AVout; [exact Hr | exact Ha1 | exact Ha2]. }
{ intros a Ha. apply PRE2. exact Ha. }
}
(* the walk: zone and value split *)
assert (ENT : forall plo phi, plo <= p <= phi ->
st_ok tfibsegs EE (ss_ent plo phi)
(restrict H (mkst regs (Z_to_bv 64 PS_ENTRY) mem (seg_rom tfibsegs)))).
{ intros plo phi Hr. rewrite restrict_mkst_fx. unfold ss_ent, EE, YE2y.Env.
apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons.
+ unfold stk. apply (region_ok_stack tfibsegs (YE2y.Env regs []) _ 2%nat sp0 (- PS_STK));
[ exact U2'
| unfold PS_STK in *; lia | unfold kHighMemEnd in *; lia |].
intros a Ha. apply YE2y.apresent_writable. apply HpresE. unfold PS_STK in *. lia.
+ exact (YE2y.rodata_ok B TB ps_rodata ly S H mem _ (ps_rodata_chk ly) (proj1 HAR)).
- apply pairwise_disjoint_of_extents.
unfold stk, ps_rodata, ro_region, extent_of_region.
cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
rewrite U2'.
unfold zdisj. cbn [fst snd]. unfold PS_STK, kHighMemBeg in *. repeat split; lia.
- split.
+ cbn [f_atoms atoms_ok facts_of]. unfold afact_ok. cbn [af_lo af_hi af_al2].
cbn [map]. rewrite U2', E10', E11', E12', !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
repeat split; first [exact Hal16 | exact Hp8 | exact Hn8 | apply Z.mod_1_r | lia].
+ split; exact I. }
assert (TAIL : forall (hi v0 : bool), (if hi then P_HI_LO <= p <= P_HI_HI else P_LO_LO <= p <= P_LO_HI) ->
conds_ok EE (conds hi v0) -> (if v0 then v = 0 else v <> 0) -> SRr tfibsegs W (cfg_at tfibsegs PS_ENTRY regs mem md) Qpost).
{ intros hi v0 Hzone HC Hvz.
assert (HS0 : st_ok tfibsegs EE (ss_z hi) (restrict H (mkst regs (Z_to_bv 64 PS_ENTRY) mem (seg_rom tfibsegs))))
by (unfold ss_z; destruct hi; apply ENT; exact Hzone).
unfold cfg_at. change (w64 PS_ENTRY) with (Z_to_bv 64 PS_ENTRY).
eapply SRr_bind; [apply (walk W EE (conds hi v0) (ss_z hi) (e_ps hi v0) _ md HS0 HC (r_ps hi v0) (w_ps hi v0))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
pose proof (shape_ok hi v0) as SH. unfold shape_ps in SH.
apply andb_prop in SH as [SH KR]. apply andb_prop in SH as [SH S12].
apply andb_prop in SH as [SH S11]. apply andb_prop in SH as [SH S10].
apply andb_prop in SH as [Spc Srv]. apply Z.eqb_eq in Spc.
assert (Hrv : ss_resv (e_ps hi v0) = None) by (destruct (ss_resv (e_ps hi v0)); [discriminate | reflexivity]).
apply sv_eqb_eq in S10. apply sv_eqb_eq in S11. apply sv_eqb_eq in S12. rewrite forallb_forall in KR.
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 Hrv) as Hshape1. rewrite Spc in Hshape1.
rewrite Hshape1.
set (regs1 := ms_regs ms1) in *. set (mem1 := ms_mem ms1) in *.
assert (RD : forall (r : bv 5) (x : sv), sr_get (ss_regs (e_ps hi v0)) r = x -> getr regs1 r = sv_denot EE x).
{ intros r x Hx. unfold regs1. rewrite (st_ok_restrict_reg tfibsegs H EE _ ms1 r HS1), Hx. reflexivity. }
assert (KEEP1 : forall r, In r keep_regs -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. specialize (KR r Hr). cbn beta in KR. apply sv_eqb_eq in KR. unfold RG in KR.
rewrite (RD (Z_to_bv 5 r) _ KR). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply EEreg. unfold keep_regs in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
apply (FIN regs1 mem1 mat1).
- rewrite (RD 10%bv _ S10). apply (A0E_denot EE p E10). lia.
- rewrite (RD 11%bv _ S11). cbn [sv_denot].
rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (RD 12%bv _ S12). unfold CNTZ. apply (A2E_denot EE p n E10 E11); try lia; assumption.
- exact KEEP1.
- intros z Hz. apply HF1. rewrite U2. exact Hz.
- intros a Ha. apply (stk0_apresent H EE (e_ps hi v0) ms1 a (stk0_ps hi v0) HS1).
+ rewrite U2. exact Ha.
+ unfold TFIB_IMG_END. unfold kHighMemBeg, kHighMemEnd, PS_STK in Hsp44, Ha. lia. }
(* which zone, and which value *)
destruct (Z.eq_dec v 0) as [Hv0|Hvn]; destruct HCEIL as [HLO|[HH1 HH2]].
- apply (TAIL false true).
+ unfold P_LO_LO, P_LO_HI, kLowShadowBeg in *. unfold kFakeFramesOff, kFakeStackSize in *. lia.
+ unfold conds. cbn [app].
split; [exact (cond_v0 EE v E12 Hv Hv0)|].
split; [exact (cond_lo EE p n E10 E11 ltac:(lia) ltac:(lia) ltac:(unfold kLowShadowBeg in *; lia))|].
split; [exact (cond_thr EE p n E10 E11 Hp0 Hp8 Hn0 Hn8 Hpn63) | exact I].
+ exact Hv0.
- apply (TAIL true true).
+ unfold P_HI_LO, P_HI_HI. unfold kFakeFramesOff, kFakeStackSize, ASAN_CEIL in *. lia.
+ unfold conds. cbn [app].
split; [exact (cond_v0 EE v E12 Hv Hv0)|].
split; [exact (cond_thr EE p n E10 E11 Hp0 Hp8 Hn0 Hn8 Hpn63) | exact I].
+ exact Hv0.
- apply (TAIL false false).
+ unfold P_LO_LO, P_LO_HI, kLowShadowBeg in *. unfold kFakeFramesOff, kFakeStackSize in *. lia.
+ unfold conds. cbn [app].
split; [exact (cond_vn EE v E12 Hv Hvn)|].
split; [exact (cond_lo EE p n E10 E11 ltac:(lia) ltac:(lia) ltac:(unfold kLowShadowBeg in *; lia)) | exact I].
+ exact Hvn.
- apply (TAIL true false).
+ unfold P_HI_LO, P_HI_HI. unfold kFakeFramesOff, kFakeStackSize, ASAN_CEIL in *. lia.
+ unfold conds. cbn [app]. split; [exact (cond_vn EE v E12 Hv Hvn) | exact I].
+ exact Hvn.
Qed.
End e.
Theorem scene_poison_shadow : forall (B : asyms), AR_laws tfibsegs B -> TfibSyms B ->
AsStackLeaf.poison_shadow_realizes tfibsegs B PS_ENTRY.
Proof. intros B LAWS TB. exact (scene_poison_shadow_au B LAWS TB). Qed.
End d.
