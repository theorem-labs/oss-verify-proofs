(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the last segment of pins_set's ASan walk, after cgif_file_fuzzer's cgif_close
   walk, proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v .. ACh6.v at c8557374ad2e (a segment as one
   symbolic run from a re-seeded state, and the step through a call and back), over fuzz_command's recorder. *)

(* `ps_seg_x4`: from the return of the fourth xstrdup (0x8c9a4) to the end of pins_set. The run stores the last
   copy into the slot (nargs := 4, args[3] := p; the two instrumented checks on the slot's words pass, because
   the shadow byte of a program static marks it usable, so the error path is not reached) and stops at the test
   of g_rec.refuse. When the recorder refuses, the body restores the saved registers and jumps into answer_code
   with the recorder's code in a0. Otherwise it calls mix_call on (g_rec.state, the slot), stores the digest to
   g_rec.state and jumps into answer_code with 0 in a0. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaCall PaCallRun PaNoChain PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c mix_call_c answer_code_c pins_set_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas pins_set_s2 pins_set_s1 pins_set_s3 pins_set_s4 pins_set_s5 pins_set_s6 pins_set_s7 pins_set_s8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* two readers that hold the same n-byte value agree on those n bytes *)
Lemma ps_same_val : forall (rd rd' : reader) a n v, aval_mem rd a n v -> aval_mem rd' a n v ->
forall y, a <= y < a + Z.of_nat n -> rd' y = rd y.
Proof.
intros rd rd' a n v H H' y Hy.
assert (Hk : (Z.to_nat (y - a) < n)%nat) by lia.
replace y with (a + Z.of_nat (Z.to_nat (y - a))) by lia.
rewrite (H (Z.to_nat (y - a)) Hk), (H' (Z.to_nat (y - a)) Hk). reflexivity.
Qed.

(* two 32-bit signed values with the same 64-bit word are equal *)
Lemma ps_bv_eq_small : forall a b, - 2 ^ 31 <= a < 2 ^ 31 -> - 2 ^ 31 <= b < 2 ^ 31 ->
Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof.
intros a b Ha Hb H.
assert (E : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> z mod 2 ^ 64 = z \/ z mod 2 ^ 64 = z + 2 ^ 64).
{ intros z Hz. destruct (Z_lt_le_dec z 0) as [Hn | Hp].
  - right. rewrite <- (Z_mod_plus_full z 1 (2 ^ 64)). apply Z.mod_small. lia.
  - left. apply Z.mod_small. lia. }
apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H.
unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H.
destruct (E a Ha) as [Ea | Ea]; destruct (E b Hb) as [Eb | Eb]; rewrite Ea, Eb in H; lia.
Qed.

(* the sign extension of a 32-bit field: the signed value the field holds *)
Lemma ps_sext32 : forall E m v, ew E m = Z_to_bv 64 (v mod 2 ^ 32) -> - 2 ^ 31 <= v < 2 ^ 31 ->
sv_denot E (SExt true 32 (SOff m 0)) = Z_to_bv 64 v.
Proof.
intros E m v Hm Hv.
assert (Hmod : 0 <= v mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (HS : bv_swrap 32 (v mod 2 ^ 32) = v).
{ unfold bv_swrap, bv_wrap.
  assert (HM : bv_modulus 32 = 2 ^ 32) by reflexivity.
  assert (HH : bv_half_modulus 32 = 2 ^ 31) by reflexivity.
  rewrite HM, HH.
  destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
  - assert (Hv32 : v mod 2 ^ 32 = v + 2 ^ 32)
      by (rewrite <- (Z_mod_plus_full v 1 (2 ^ 32)); apply Z.mod_small; lia).
    rewrite Hv32. replace (v + 2 ^ 32 + 2 ^ 31) with (v + 2 ^ 31 + 1 * 2 ^ 32) by lia.
    rewrite Z_mod_plus_full, (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. lia.
  - rewrite (Z.mod_small v (2 ^ 32)), (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. lia. }
rewrite (denot_lit_U E (SExt true 32 (SOff m 0))), U_SExt, U_SOff, Hm,
  (unsigned_lit_small (v mod 2 ^ 32) ltac:(lia)), Z.add_0_r.
change (Z.of_N 32) with 32. unfold zcanon. unfold M64.
rewrite (Z.mod_small (v mod 2 ^ 32) (2 ^ 64)) by lia. rewrite Zmod_mod, HS.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity.
Qed.

Lemma ps_denot_off : forall E k v d, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff k d) = Z_to_bv 64 (v + d).
Proof. intros E k v d Hk Hv. cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma ps_denot_reg : forall E k (b : bv 5) (rg : bvmap 5 word), ew E k = getr rg b ->
sv_denot E (SOff k 0) = getr rg b.
Proof. intros E k b rg Hk. cbn [sv_denot]. rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Ltac ps_in := cbn [In]; repeat first [ solve [left; reflexivity] | right ].
(* after a run the model is `with_vm_backing (m_vm_lazy md) mat md` in the goal and the journal; name it, so a
   chain of runs does not double the term (a 66 GB compile was measured) *)
Ltac ps_fold_md :=
repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?mt ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) mt m) in *; clearbody mdv end.
(* a register of the state a run left, with the symbolic value given (never vm_compute: the state of a state at a
   call holds `pa_sigma`, whose arguments are the whole listing) *)
Ltac psgv HS r e Hr :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  change (sr_get (ss_regs ss) r) with e in Hr
| st_ok ?sg ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg sg H E ss ms r HS) as Hr;
  change (sr_get (ss_regs ss) r) with e in Hr
end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* PaDenot's field_of_region with the address and the width as equations *)
Lemma ps_field : forall E m n b cs lo hi wlo whi od (w : N) e v a kk,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> a = b + od -> kk = N.to_nat w ->
val_mem SEGS m a kk v.
Proof.
intros E m n b cs lo hi wlo whi od w e v a kk HR Hn Hc He Hv Hw -> ->.
exact (field_of_region E m n b cs lo hi wlo whi od w e v HR Hn Hc He Hv Hw).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis TMIX_CALL : tmix_call_spec B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a callee with an empty footprint keeps the caller's frame (above its own window) and the program's statics *)
Lemma ps_call_kept : forall STK1 sp1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
((sp1 <= a < 2 ^ 64 /\ alloc_ceiling <= a) \/ Exists (in_zr a) recb_PG) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 a HJ Ha.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _ & K3 & _).
assert (Hnf : ~ inFP [] a) by (intros (r & Hr & _); destruct Hr).
destruct Ha as [(Ha1 & Ha2) | HP].
- apply K1; [lia | lia | exact Hnf].
- assert (HP' : Exists (in_zr a) (as_prog_static B)) by (rewrite (recb_ts_prog_m B HB); exact HP).
  destruct (prog_static_sep B a (ts_ok B HB) HP') as (H1 & H2 & _).
  apply K3; [exact (cmd_prog_img a HP) | exact H1 | exact H2 |].
  apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | exact Hnf].
Qed.

(* a callee with an empty footprint keeps the bytes of a block live before and after it *)
Lemma ps_call_kept_blk : forall STK1 sp1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 k1 q n i,
ajournal SEGS B STK1 sp1 [] lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
In (q, n) (ablocks B lyc Sc) -> In (q, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
rdW W2 mem2 (q + i) = rdW Wc memc (q + i).
Proof.
intros STK1 sp1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 q n i HJ H1 H2 Hi.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
apply (K2 q n i H1 H2 Hi). intros (r & Hr & _); destruct Hr.
Qed.

Section entry.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (pu pf pl pv : Z) (uri files layout verdict : option (list byte)) (R : rstate)
  (O : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B PINS_SET_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis HREPA : rec_repA B ly S (rdW W mem) R O.
Hypothesis HEV : st_nev S + EV_PINS_SET R <= EV_MAX.
Hypothesis PS_STORE : ps_store_stmt B MT ly S W regs mem md uri files layout verdict R O.
Hypothesis PS_CLOSE : ps_close_stmt B MT ly S W regs mem md uri files layout verdict R O.
Hypothesis PS_TAIL : ps_tail_stmt B MT ly S W regs mem md uri files layout verdict R O.

#[local] Notation sp0 := (ps_sp0 regs).
#[local] Notation FPps := (ps_FP O).
#[local] Notation A := (ps_A uri files layout verdict).
#[local] Notation CORE := (ps_core B MT ly S W regs mem md uri files layout verdict R O).
#[local] Notation KEEP := (ps_keep B regs pf pl pv R).
#[local] Notation POST := (ps_post B MT ly S W regs mem md uri files layout verdict R O).

Lemma ps_sig_mix : pa_sigma CS_mix_call = BASE + AF_mix_call.
Proof. rewrite (SIGP CS_mix_call ltac:(unfold cmd_prog_syms; ps_in)). f_equal; try (vm_compute; reflexivity). Qed.
Lemma ps_sig_answer : pa_sigma CS_answer_code = BASE + AF_answer_code.
Proof. rewrite (SIGP CS_answer_code ltac:(unfold cmd_prog_syms; ps_in)). f_equal; try (vm_compute; reflexivity). Qed.

Lemma ps_seg_x4 : ps_x4_stmt B MT ly S W regs mem md pf pl pv uri files layout verdict R O.
Proof.
unfold ps_x4_stmt, ps_xret_stmt.
intros P p lyc Sc Wc regsc memc mdc k HlenP HC HK Ha0.
change (ps_ret 4) with PS_RET4.
assert (HLEN : 0 < Z.of_nat (length (nth (4 - 1) A [])) + 1) by lia.
set (LEN := Z.of_nat (length (nth (4 - 1) A [])) + 1) in *.
pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (ps_sp0_facts B ly S W regs mem md ch HPRE) as (Hsp46 & Hsp16 & Hspc).
destruct (ps_core_slot B MT ly S W regs mem md uri files layout verdict R O P [(p, LEN)]
  lyc Sc Wc memc mdc k HC) as (Hn16 & Hcok & Hcases).
destruct (ps_core_scalars B MT ly S W regs mem md uri files layout verdict R O P [(p, LEN)]
  lyc Sc Wc memc mdc k HC) as (Vrf & Vcd & Vst & Hst64 & Hrf31 & Hcd31).
destruct (ps_slot_bounds (ps_c R) Hcok) as [Hcb Hc8].
assert (Hc64 : 0 <= ps_c R < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
pose proof HC as HC0. destruct HC0 as [HJ Hk Hlen Hmo Hbb Hfr Hlive Hrec].
destruct HK as (K2 & K3 & K4 & K8 & K18 & K22 & K23 & K24 & K21 & K20 & K19 & K9 & KHI).
pose proof (proj1 HJ) as HARc.
assert (Hlen4 : length (P ++ [(p, LEN)]) = 4%nat) by (rewrite length_app, HlenP; reflexivity).
rewrite Hlen4 in Hk, Hbb, Hmo.
assert (Hspc2 : spZ regsc = sp0 - 80).
{ unfold spZ. rewrite K2. unfold w64. apply unsigned_lit_small. unfold ps_sp0 in *. lia. }
assert (Hsp16c : spZ regsc mod 16 = 0).
{ rewrite Hspc2. replace (sp0 - 80) with (sp0 + (-5) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
(* the slot's argument count and the frame, as the seed asks for them *)
destruct Hrec as (Rb & Qb & rdb & blb & HA & HlenR & Hrr & Hsp0q & Hprot & HQb & Hcov & HNC & HFN & HNA & HND & HARGS & HNEWB).
rewrite HlenP in HNA.
(* the copy the fourth xstrdup made is a live block, so its address is a machine word *)
assert (HinP : In (p, LEN) (ablocks B lyc Sc)).
{ assert (Hi : nth_error (P ++ [(p, LEN)]) (length P) = Some (p, LEN))
    by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
  destruct (HNEWB (length P) (p, LEN) Hi) as (_ & _ & _ & N4 & _). exact N4. }
assert (Hp64 : 0 <= p < 2 ^ 64).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ p LEN HARc HinP) as (_ & H4096 & Hce & _).
  assert (Hrq : req_size LEN = LEN) by (unfold req_size; destruct (Z.eqb_spec LEN 0); lia). lia. }
assert (HFRM0 : forall i r, nth_error ps_saved i = Some r ->
  aval_mem (rdW Wc memc) (spZ regsc + 72 - 8 * Z.of_nat i) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros i r Hir. replace (spZ regsc + 72 - 8 * Z.of_nat i) with (sp0 - 8 - 8 * Z.of_nat i) by (rewrite Hspc2; lia).
  exact (Hfr i r Hir). }
destruct (ps_aft_seed B HB VOBJS cmd_prog_writable lyc Sc Wc memc mdc regs regsc 4%nat PS_RET4 (ps_c R)
  (r_refuse R mod 2 ^ 32) (r_code R mod 2 ^ 32) (r_state R) HARc Hcok ltac:(lia)
  ltac:(rewrite Hspc2; lia) Hsp16c K8 K18 K22 K23 K24 K21 HNA HFRM0 Vrf Vcd Vst
  ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) Hst64) as [HS SHOK].
set (E := ps_Ec regsc regs (ps_c R) (r_refuse R mod 2 ^ 32) (r_code R mod 2 ^ 32) (r_state R)) in *.
destruct (ps_Ec_facts VOBJS regsc regs (ps_c R) (r_refuse R mod 2 ^ 32) (r_code R mod 2 ^ 32) (r_state R))
  as (HEI & ESB & EC & E35 & E36 & E37 & EG & ESP & EE & ESV).
fold E in HEI, ESB, EC, E35, E36, E37, EG, ESP, EE, ESV.
assert (UC : bv_unsigned (ew E 34%nat) = ps_c R)
  by (change 34%nat with PS_C; rewrite EC; apply unsigned_lit_small; exact Hc64).
assert (UG : bv_unsigned (ew E 285%nat) = A_G_REC)
  by (change 285%nat with PS_GREC; rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U2 : ew E 2%nat = Z_to_bv 64 (sp0 - 80))
  by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl), K2; reflexivity).
assert (Hd10 : sv_denot E (SOff 10 0) = Z_to_bv 64 p)
  by (rewrite (ps_denot_reg E 10%nat (10%bv : bv 5) regsc (EE 10%nat (10%bv : bv 5) eq_refl)); exact Ha0).
(* the store of the fourth copy and the close of the recorded call, at any memory the segment reaches *)
assert (STEP : forall (m2 : word -> option byte) (md2 : Model),
  ajournal SEGS B PINS_SET_STK sp0 FPps ly S W mem md [] lyc Sc Wc m2 md2 k ->
  (forall y, 0 <= y < 2 ^ 64 -> ~ (ps_c R + 4 <= y < ps_c R + 8) -> ~ (ps_c R + 32 <= y < ps_c R + 40) ->
     rdW Wc m2 y = rdW Wc memc y) ->
  aval_mem (rdW Wc m2) (ps_c R + 4) 4 4 ->
  aval_mem (rdW Wc m2) (ps_c R + 8 + 8 * Z.of_nat (4 - 1)) 8 p ->
  exists O2, rec_repA B lyc Sc (rdW Wc m2) (rec_record R REC_PINS_SET A) O2 /\
  (forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O2) /\
  (forall pn, In pn O2 -> In pn O \/ ~ In pn (ablocks B ly S)) /\
  acall_at (ablocks B lyc Sc) (rdW Wc m2) (ps_c R) (REC_PINS_SET, A) (P ++ [(p, LEN)])).
{ intros m2 md2 HJ2 KEEPy V4 Vp.
  assert (KEEPM : forall y, 0 <= y < 2 ^ 64 -> ~ (ps_c R + 4 <= y < ps_c R + 8) ->
    ~ (ps_c R + 8 + 8 * Z.of_nat (4 - 1) <= y < ps_c R + 16 + 8 * Z.of_nat (4 - 1)) ->
    rdW Wc m2 y = rdW Wc memc y).
  { intros y Hy N1 N2. change (Z.of_nat (4 - 1)) with 3 in N2. apply KEEPy; [exact Hy | exact N1 | lia]. }
  exact (PS_CLOSE (P ++ [(p, LEN)]) lyc Sc Wc m2 md2 k Hlen4
    (PS_STORE 4%nat P (p, LEN) lyc Sc Wc memc m2 mdc md2 k ltac:(lia) HlenP HC HJ2 KEEPM V4 Vp)). }
(* the model's answer, on each arm of the refusal test *)
assert (HMODT : r_refuse R <> 0 ->
  pins_set_m R uri files layout verdict = rec_answer_code (rec_record R REC_PINS_SET A) (r_code R)).
{ intros Hne. unfold pins_set_m, rec_stub_code, ps_A. cbv zeta.
  destruct (ps_rec_record_scalars R REC_PINS_SET
    [sarg uri; sarg files; sarg layout; darg verdict (bstr "-"%string)]) as (M1 & M2 & _ & _).
  rewrite M1, M2, (proj2 (Z.eqb_neq (r_refuse R) 0) Hne). reflexivity. }
assert (HMODM : r_refuse R = 0 ->
  pins_set_m R uri files layout verdict =
  rec_answer_code (rec_mix (rec_record R REC_PINS_SET A) (REC_PINS_SET, A)) 0).
{ intros Hz. unfold pins_set_m, rec_stub_code, ps_A. cbv zeta.
  destruct (ps_rec_record_scalars R REC_PINS_SET
    [sarg uri; sarg files; sarg layout; darg verdict (bstr "-"%string)]) as (M1 & _ & _ & _).
  rewrite M1, (proj2 (Z.eqb_eq (r_refuse R) 0) Hz). reflexivity. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev0 & _).
change (Z.of_nat 4) with 4 in Hk.
unfold EV_PINS_SET, EV_ANSWER_CODE, EV_HAND_BACK, EV_XSTRDUP in HEV.
assert (HEVT : k + EV_ANSWER_CODE <= EV_PINS_SET R)
  by (unfold EV_PINS_SET, EV_ANSWER_CODE, EV_HAND_BACK, EV_XSTRDUP; lia).
assert (HNEV : st_nev Sc + EV_MIX_CALL <= EV_MAX) by (unfold EV_MIX_CALL; lia).
(* 0x8c9a4 .. 0x8c9d8: the two checks on the slot, nargs := 4, args[3] := p, the load of g_rec.refuse *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  eapply awr_ok_cons_gen with (n := 34%nat); [reflexivity | exact UC | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    exact (ps_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ (ps_c R) a Hcok ltac:(unfold CALL_SIZE; lia)). }
  eapply awr_ok_cons_gen with (n := 34%nat); [reflexivity | exact UC | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    exact (ps_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ (ps_c R) a Hcok ltac:(unfold CALL_SIZE; lia)). }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_nil. }
ps_fold_md. rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
(* the branch on g_rec.refuse *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* g_rec.refuse = 0: the call is mixed into the recorder's digest *)
  assert (Href0 : r_refuse R = 0).
  { cbn [branch_taken] in Hc. apply bv_eqb_eq in Hc.
    rewrite (ps_sext32 E 35%nat (r_refuse R) E35 Hrf31) in Hc. cbn [sv_denot] in Hc.
    exact (ps_bv_eq_small (r_refuse R) 0 Hrf31 ltac:(lia) Hc). }
  (* 0x8c9dc .. 0x8c9ec: g_rec.state and the slot into a0 / a1, the call of mix_call *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply awr_ok_cons_gen with (n := 34%nat); [reflexivity | exact UC | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
      exact (ps_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ (ps_c R) a Hcok ltac:(unfold CALL_SIZE; lia)). }
    eapply awr_ok_cons_gen with (n := 34%nat); [reflexivity | exact UC | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
      exact (ps_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ (ps_c R) a Hcok ltac:(unfold CALL_SIZE; lia)). }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_nil. }
  ps_fold_md. rename HF into HF2. rename HFr into HFr2. rename HG into HG2.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    pose proof (st_ok_region_nth E _ _ 0%nat
      (YP09.mkRegion (Some 34%nat) 4 8 4 8 [YP09.mkChunk 4 (CVal 4 (SLit 4))]) HS ltac:(reflexivity)) as HR0;
    pose proof (st_ok_region_nth E _ _ 1%nat
      (YP09.mkRegion (Some 34%nat) 32 40 32 40 [YP09.mkChunk 32 (CVal 8 (SOff 10 0))]) HS ltac:(reflexivity)) as HR1;
    cbn [ms_mem restrict mkst] in HR0, HR1;
    assert (KEEP12 : forall y, 0 <= y < 2 ^ 64 -> ~ (ps_c R + 4 <= y < ps_c R + 8) ->
      ~ (ps_c R + 32 <= y < ps_c R + 40) -> rdW Wc (ms_mem msx) y = rdW Wc memc y)
  end.
  { intros y Hy N1 N2.
    transitivity (rdW Wc (ms_mem ms) y).
    - apply (ps_rd_frame E _ (w_H Wc) (ms_mem ms) _ y HF2 Hy).
      intros (r & Hin & Hr).
      lazymatch type of Hin with In r ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end.
      destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        [rewrite UC in Hr; lia | rewrite UC in Hr; lia | lia | lia | lia].
    - apply (ps_rd_frame E _ (w_H Wc) memc (ms_mem ms) y HF1 Hy).
      intros (r & Hin & Hr).
      lazymatch type of Hin with In r ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end.
      destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        [rewrite UC in Hr; lia | rewrite UC in Hr; lia | lia | lia | lia]. }
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    assert (V4b : aval_mem (rdW Wc (ms_mem msx)) (ps_c R + 4) 4 4);
    [ apply (aval_mem_view SEGS);
      exact (ps_field E _ 34%nat (ps_c R) _ 4 8 4 8 4 4%N (SLit 4) 4 (ps_c R + 4) 4%nat HR0 UC ltac:(ps_in) eq_refl
        ltac:(change (8 * Z.of_N 4) with 32; lia) ltac:(change (Z.of_N 4) with 4; lia) eq_refl eq_refl) |];
    assert (Vpb : aval_mem (rdW Wc (ms_mem msx)) (ps_c R + 8 + 8 * Z.of_nat (4 - 1)) 8 p);
    [ apply (aval_mem_view SEGS);
      exact (ps_field E _ 34%nat (ps_c R) _ 32 40 32 40 32 8%N (SOff 10 0) p
        (ps_c R + 8 + 8 * Z.of_nat (4 - 1)) 8%nat HR1 UC ltac:(ps_in) Hd10
        ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(change (Z.of_N 8) with 8; lia) ltac:(lia) eq_refl) |]
  end.
  destruct (STEP _ _ HJ KEEP12 V4b Vpb) as (O2 & HREP1 & HCOV1 & HO21 & HCALL1).
  assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms0)))
    by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
        (ps_FP_ro B cmd_ro_prog_apart ly S W regs mem md ch R O HPRE HREPA) HROD).
  assert (HRO2 : cmd_ro_ok (rdW Wc (ms_mem ms0)))
    by exact (cmd_ro_ok_of_aro lyc Sc Wc (ms_mem ms0) _ (proj1 HJ) HROD2).
  assert (HSLOTD : (exists i, 0 <= i < REC_CALLS_MAX /\ ps_c R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/
    ps_c R = A_REC_SPILL).
  { destruct Hcases as [(X1 & X2 & X3) | (X1 & X2)]; [left | right; exact X1].
    exists (ps_n R). split; [unfold REC_CALLS_MAX; lia|].
    unfold ps_c, ps_slot_of. rewrite (proj2 (Z.eqb_neq (ps_n R) 16) ltac:(lia)). reflexivity. }
  psgv HS (1%bv : bv 5) (SOff 240 25868) M1.
  psgv HS (2%bv : bv 5) (SOff 2 0) M2.
  psgv HS (3%bv : bv 5) (SOff 3 0) M3.
  psgv HS (4%bv : bv 5) (SOff 4 0) M4.
  psgv HS (10%bv : bv 5) (SOff 37 0) M10.
  psgv HS (11%bv : bv 5) (SOff 34 0) M11.
  psgv HS (25%bv : bv 5) (SOff 25 0) M25.
  psgv HS (26%bv : bv 5) (SOff 26 0) M26.
  psgv HS (27%bv : bv 5) (SOff 27 0) M27.
  cbn [sv_denot] in M1. rewrite (img_env_codeptr E HEI 25868) in M1.
  rewrite (ps_denot_off E 2%nat (sp0 - 80) 0 U2 ltac:(lia)), Z.add_0_r in M2.
  rewrite (ps_denot_reg E 3%nat (3%bv : bv 5) regsc (EE 3%nat (3%bv : bv 5) eq_refl)), K3 in M3.
  rewrite (ps_denot_reg E 4%nat (4%bv : bv 5) regsc (EE 4%nat (4%bv : bv 5) eq_refl)), K4 in M4.
  rewrite (ps_denot_off E 37%nat (r_state R) 0 E37 Hst64), Z.add_0_r in M10.
  rewrite (ps_denot_off E 34%nat (ps_c R) 0 ltac:(change 34%nat with PS_C; exact EC) Hc64), Z.add_0_r in M11.
  rewrite (ps_denot_reg E 25%nat (25%bv : bv 5) regsc (EE 25%nat (25%bv : bv 5) eq_refl)) in M25.
  rewrite (ps_denot_reg E 26%nat (26%bv : bv 5) regsc (EE 26%nat (26%bv : bv 5) eq_refl)) in M26.
  rewrite (ps_denot_reg E 27%nat (27%bv : bv 5) regsc (EE 27%nat (27%bv : bv 5) eq_refl)) in M27.
  pmkst HS. rewrite ps_sig_mix.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?mdq |} _ =>
  assert (Msp : spZ rg = sp0 + -80) by (unfold spZ at 1; rewrite M2; rewrite unsigned_lit_small; lia);
  eapply SRr_bind;
  [ eapply (cl_callS_na B LAWS Wc rg mm _ PINS_SET_STK sp0 FPps ly S W mem md [] lyc Sc mdq k
      MIX_CALL_STK [] EV_MIX_CALL (-80) (getr rg 1)
      (fun ly4 S4 W4 regs4 mem4 md4 =>
         getr regs4 10 = w64 (mixcall (r_state R) REC_PINS_SET A) /\
         Permutation (ablocks B ly4 S4) (ablocks B lyc Sc) /\ ly4 = lyc /\ S4 = Sc) HJ Msp);
    [ reflexivity | lia | unfold MIX_CALL_STK, ESTACK; lia
    | unfold PINS_SET_STK, REC_CALLS_FREE_STK, XSTRDUP_STK, MIX_CALL_STK, ASTACK, ESTACK; lia
    | exact M3 | exact M4 | reflexivity
    | rewrite M1; apply ret_ok_codeptr_v; [lia | reflexivity]
    | rewrite M1, unsigned_lit_small by lia; lia
    | intros HPRE1;
      exact (TMIX_CALL lyc Sc Wc rg mm mdq (r_state R) (ps_c R) (REC_PINS_SET, A) (P ++ [(p, LEN)])
        HPRE1 HROD2 M10 Hst64 M11 HSLOTD HCALL1 HRO2 HNEV)
    | intros a (r & Hr & _); destruct Hr ]
  | ] end.
  cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & Hm10 & HPerm3 & Hly3 & HSS3).
  subst ly3 S3. rewrite M1.
  (* back at 0x8c9f0 *)
  pose proof (proj1 HJ3) as HAR3.
  assert (Hregs3 : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr (ms_regs ms0) (Z_to_bv 5 r))
    by exact HP3.
  assert (H3sp : getr regs3 2 = getr (ms_regs ms0) 2)
    by (rewrite <- (ps_pres (ms_regs ms0) regs3 2 (2%bv : bv 5) HP3 ltac:(unfold acallee_saved; lia)
          ltac:(apply bv_eq; reflexivity)); reflexivity).
  assert (Hsp3 : spZ regs3 = sp0 - 80)
    by (unfold spZ; rewrite H3sp, M2; apply unsigned_lit_small; lia).
  assert (H3g : getr regs3 22 = w64 A_G_REC).
  { rewrite (ps_pres (ms_regs ms0) regs3 22 (22%bv : bv 5) HP3 ltac:(unfold acallee_saved; lia)
      ltac:(apply bv_eq; reflexivity)).
    psgv HS (22%bv : bv 5) (SOff 285 0) M22.
    rewrite M22, (ps_denot_off E 285%nat A_G_REC 0 ltac:(change 285%nat with PS_GREC; exact EG)
      ltac:(unfold A_G_REC; lia)), Z.add_0_r. reflexivity. }
  (* the bytes above the callee's window, kept by the call *)
  assert (KEEPhi : forall a, sp0 - 80 <= a < sp0 -> rdW W3 mem3 a = rdW Wc (ms_mem ms0) a).
  { intros a Ha.
    apply (ps_call_kept MIX_CALL_STK (sp0 + -80) lyc Sc Wc (ms_mem ms0) _ lyc Sc W3 mem3 md3 _ a HJc3).
    left. split; [split|].
    - lia.
    - change (2 ^ 64) with 18446744073709551616.
      change (2 ^ 47) with 140737488355328 in Hsp46. lia.
    - lia. }
  (* the frame of saved registers, kept by the call *)
  assert (HFRM3 : forall i r, nth_error ps_saved i = Some r ->
    aval_mem (rdW W3 mem3) (spZ regs3 + 72 - 8 * Z.of_nat i) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  { intros i r Hir.
    assert (Hi : (i < 10)%nat)
      by (change 10%nat with (length ps_saved); apply nth_error_Some; rewrite Hir; discriminate).
    replace (spZ regs3 + 72 - 8 * Z.of_nat i) with (sp0 - 8 - 8 * Z.of_nat i) by (rewrite Hsp3; lia).
    apply (ps_aval_mem_in (rdW Wc memc)); [exact (Hfr i r Hir)|].
    intros y Hy. change (Z.of_nat 8) with 8 in Hy.
    rewrite (KEEPhi y ltac:(lia)).
    apply KEEP12; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE in *; lia. }
  (* the symbolic state at the return of mix_call *)
  destruct (ps_mix_seed B HB VOBJS cmd_prog_writable lyc Sc W3 mem3 md3 regs regs3 PS_RET_MIX (ps_c R)
    HAR3 Hcok ltac:(lia) ltac:(rewrite Hsp3; replace (sp0 - 80) with (sp0 + (-5) * 16) by lia;
      rewrite Z_mod_plus_full; exact Hsp16) H3g HFRM3) as [HS2 SHOK2].
  set (E2 := ps_Ec regs3 regs (ps_c R) 0 0 0) in *.
  destruct (ps_Ec_facts VOBJS regs3 regs (ps_c R) 0 0 0)
    as (HEI2 & ESB2 & EC2 & E352 & E362 & E372 & EG2 & ESP2 & EE2 & ESV2).
  fold E2 in HEI2, ESB2, EC2, E352, E362, E372, EG2, ESP2, EE2, ESV2.
  assert (UG2 : bv_unsigned (ew E2 285%nat) = A_G_REC)
    by (change 285%nat with PS_GREC; rewrite EG2; apply unsigned_lit_small; unfold A_G_REC; lia).
  assert (U22 : ew E2 2%nat = Z_to_bv 64 (sp0 - 80))
    by (rewrite (EE2 2%nat (2%bv : bv 5) eq_refl); unfold spZ in Hsp3; rewrite <- Hsp3;
        rewrite Z_to_bv_bv_unsigned; reflexivity).
  (* 0x8c9f0 .. 0x8ca28: g_rec.state := the digest, the epilogue, the tail jump *)
  paj_run_tok RUN HS2 HJ3 SHOK2 Bspan.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen with (n := 285%nat); [reflexivity | exact UG2 | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (ps_awr_prog B HB cmd_prog_img _ _ _ _ _ _ _ _ a).
    left. unfold REC_SIZE. lia. }
  ps_fold_md.
  (* the digest in g_rec.state *)
  assert (Hmix64 : 0 <= mixcall (r_state R) REC_PINS_SET A < 2 ^ 64) by (apply mixcall_range; exact Hst64).
  assert (Hd10b : sv_denot E2 (SOff 10 0) = Z_to_bv 64 (mixcall (r_state R) REC_PINS_SET A)).
  { rewrite (ps_denot_reg E2 10%nat (10%bv : bv 5) regs3 (EE2 10%nat (10%bv : bv 5) eq_refl)). exact Hm10. }
  lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?msx) =>
    pose proof (st_ok_region_nth E2 _ _ 1%nat
      (YP09.mkRegion (Some 285%nat) 944 952 944 952 [YP09.mkChunk 944 (CVal 8 (SOff 10 0))]) HS2
      ltac:(reflexivity)) as HRst;
    cbn [ms_mem restrict mkst] in HRst;
    assert (Vstate : aval_mem (rdW W3 (ms_mem msx)) (A_G_REC + OFF_STATE) 8
      (mixcall (r_state R) REC_PINS_SET A));
    [ apply (aval_mem_view SEGS);
      exact (ps_field E2 _ 285%nat A_G_REC _ 944 952 944 952 944 8%N (SOff 10 0)
        (mixcall (r_state R) REC_PINS_SET A) (A_G_REC + OFF_STATE) 8%nat HRst UG2 ltac:(ps_in) Hd10b
        ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(change (Z.of_N 8) with 8; lia)
        ltac:(unfold OFF_STATE; lia) eq_refl) |];
    assert (KEEPst : forall y, 0 <= y < 2 ^ 64 -> ~ (A_G_REC + OFF_STATE <= y < A_G_REC + OFF_STATE + 8) ->
      rdW W3 (ms_mem msx) y = rdW W3 mem3 y)
  end.
  { intros y Hy N1. apply (ps_rd_frame E2 _ (w_H W3) mem3 _ y HF Hy).
    intros (r & Hin & Hr).
    lazymatch type of Hin with In r ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      [lia | rewrite UG2 in Hr; unfold OFF_STATE in *; lia]. }
  (* the recorder after the digest *)
  destruct HREP1 as (Q1 & HA1 & HO1).
  assert (HREPM : rec_repA B lyc Sc (rdW W3 (ms_mem ms1)) (rec_mix (rec_record R REC_PINS_SET A) (REC_PINS_SET, A)) O2).
  { exists Q1. split; [|exact HO1].
    unfold rec_mix. cbn [fst snd].
    destruct (ps_rec_record_scalars R REC_PINS_SET A) as (_ & _ & E3s & _). rewrite E3s.
    apply (arep_set_state (ablocks B lyc Sc) (rdW Wc (ms_mem ms0)) _ _ Q1 _ HA1); [| exact Vstate | exact Hmix64].
    intros x Hx Hnx.
    assert (Hx64 : 0 <= x < 2 ^ 64).
    { destruct Hx as [Hx | [Hx | ([q n] & Hq & Hx)]];
        [unfold A_G_REC, REC_SIZE in *; lia | unfold A_REC_SPILL, SC_SIZE in *; lia |].
      cbn [fst snd] in Hx.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HARc (lay_blocks_in _ _ _ _ _ _ HA1 (q, n) Hq))
        as (_ & H4096 & Hce & _ & _ & _ & Hn0).
      pose proof (req_size_pos n ltac:(lia)) as [Q1a Q2a]. lia. }
    rewrite (KEEPst x Hx64 Hnx).
    destruct Hx as [Hx | [Hx | ([q n] & Hq & Hx)]].
    - exact (ps_call_kept MIX_CALL_STK (sp0 + -80) lyc Sc Wc (ms_mem ms0) _ lyc Sc W3 mem3 md3 _ x HJc3
        (or_intror (recb_grec_in x Hx))).
    - exact (ps_call_kept MIX_CALL_STK (sp0 + -80) lyc Sc Wc (ms_mem ms0) _ lyc Sc W3 mem3 md3 _ x HJc3
        (or_intror (recb_spill_in x Hx))).
    - cbn [fst snd] in Hx.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HARc (lay_blocks_in _ _ _ _ _ _ HA1 (q, n) Hq))
        as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos n ltac:(lia)) as [Q1a Q2a].
      replace x with (q + (x - q)) by lia.
      exact (ps_call_kept_blk MIX_CALL_STK (sp0 + -80) lyc Sc Wc (ms_mem ms0) _ lyc Sc W3 mem3 md3 _
        q n (x - q) HJc3 (lay_blocks_in _ _ _ _ _ _ HA1 (q, n) Hq)
        (lay_blocks_in _ _ _ _ _ _ HA1 (q, n) Hq) ltac:(lia)). }
  (* the tail jump into answer_code, with 0 in a0 *)
  psgv HS2 (10%bv : bv 5) (SLit 0) N10.
  pmkst HS2. rewrite ps_sig_answer.
  replace (k + EV_MIX_CALL) with k in HJ3 by (unfold EV_MIX_CALL; lia).
  refine (PS_TAIL lyc Sc W3 (ms_mem ms1) _ k (ms_regs ms1)
    (rec_mix (rec_record R REC_PINS_SET A) (REC_PINS_SET, A)) O2 0
    HJ3 _ _ _ _ ltac:(lia) HREPM HCOV1 Hlive HO21 (HMODM Href0) HEVT Hbb Hmo).
  + (* sp *)
    psgv HS2 (2%bv : bv 5) (SOff 2 80) X2.
    unfold spZ. rewrite X2, (ps_denot_off E2 2%nat (sp0 - 80) 80 U22 ltac:(lia)).
    rewrite (unsigned_lit_small (sp0 - 80 + 80) ltac:(lia)). lia.
  + (* ra *)
    psgv HS2 (1%bv : bv 5) (SOff 38 0) X1.
    rewrite X1, (ps_denot_reg E2 38%nat (Z_to_bv 5 1) regs (ESV2 0%nat 1 eq_refl)).
    f_equal; try (apply bv_eq; reflexivity).
  + (* the callee-saved registers, restored from the frame *)
    intros r Hr. unfold acallee_saved in Hr.
    assert (Hr15 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
      r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    repeat (destruct Hr15 as [Hr15 | Hr15]); subst r.
    * psgv HS2 (Z_to_bv 5 2) (SOff 2 80) X.
      rewrite X, (ps_denot_off E2 2%nat (sp0 - 80) 80 U22 ltac:(lia)).
      replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
      unfold ps_sp0, spZ. replace (bv_unsigned (getr regs 2) - 80 + 80) with (bv_unsigned (getr regs 2)) by lia.
      apply Z_to_bv_bv_unsigned.
    * psgv HS2 (Z_to_bv 5 3) (SOff 3 0) X.
      rewrite X, (ps_denot_reg E2 3%nat (Z_to_bv 5 3) regs3 (EE2 3%nat (Z_to_bv 5 3) ltac:(reflexivity))).
      rewrite (HP3 3 ltac:(unfold acallee_saved; lia)).
      replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite M3. symmetry. exact Hgp.
    * psgv HS2 (Z_to_bv 5 4) (SOff 4 0) X.
      rewrite X, (ps_denot_reg E2 4%nat (Z_to_bv 5 4) regs3 (EE2 4%nat (Z_to_bv 5 4) ltac:(reflexivity))).
      rewrite (HP3 4 ltac:(unfold acallee_saved; lia)).
      replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite M4. symmetry. exact Htp.
    * psgv HS2 (Z_to_bv 5 8) (SOff 39 0) X.
      rewrite X, (ps_denot_reg E2 39%nat (Z_to_bv 5 8) regs (ESV2 1%nat 8 eq_refl)). reflexivity.
    * psgv HS2 (Z_to_bv 5 9) (SOff 40 0) X.
      rewrite X, (ps_denot_reg E2 40%nat (Z_to_bv 5 9) regs (ESV2 2%nat 9 eq_refl)). reflexivity.
    * psgv HS2 (Z_to_bv 5 18) (SOff 41 0) X.
      rewrite X, (ps_denot_reg E2 41%nat (Z_to_bv 5 18) regs (ESV2 3%nat 18 eq_refl)). reflexivity.
    * psgv HS2 (Z_to_bv 5 19) (SOff 42 0) X.
      rewrite X, (ps_denot_reg E2 42%nat (Z_to_bv 5 19) regs (ESV2 4%nat 19 eq_refl)). reflexivity.
    * psgv HS2 (Z_to_bv 5 20) (SOff 43 0) X.
      rewrite X, (ps_denot_reg E2 43%nat (Z_to_bv 5 20) regs (ESV2 5%nat 20 eq_refl)). reflexivity.
    * psgv HS2 (Z_to_bv 5 21) (SOff 44 0) X.
      rewrite X, (ps_denot_reg E2 44%nat (Z_to_bv 5 21) regs (ESV2 6%nat 21 eq_refl)). reflexivity.
    * psgv HS2 (Z_to_bv 5 22) (SOff 45 0) X.
      rewrite X, (ps_denot_reg E2 45%nat (Z_to_bv 5 22) regs (ESV2 7%nat 22 eq_refl)). reflexivity.
    * psgv HS2 (Z_to_bv 5 23) (SOff 46 0) X.
      rewrite X, (ps_denot_reg E2 46%nat (Z_to_bv 5 23) regs (ESV2 8%nat 23 eq_refl)). reflexivity.
    * psgv HS2 (Z_to_bv 5 24) (SOff 47 0) X.
      rewrite X, (ps_denot_reg E2 47%nat (Z_to_bv 5 24) regs (ESV2 9%nat 24 eq_refl)). reflexivity.
    * psgv HS2 (Z_to_bv 5 25) (SOff 25 0) X.
      rewrite X, (ps_denot_reg E2 25%nat (Z_to_bv 5 25) regs3 (EE2 25%nat (Z_to_bv 5 25) ltac:(reflexivity))).
      rewrite (HP3 25 ltac:(unfold acallee_saved; lia)).
      replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite M25. exact (KHI 25 ltac:(lia)).
    * psgv HS2 (Z_to_bv 5 26) (SOff 26 0) X.
      rewrite X, (ps_denot_reg E2 26%nat (Z_to_bv 5 26) regs3 (EE2 26%nat (Z_to_bv 5 26) ltac:(reflexivity))).
      rewrite (HP3 26 ltac:(unfold acallee_saved; lia)).
      replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite M26. exact (KHI 26 ltac:(lia)).
    * psgv HS2 (Z_to_bv 5 27) (SOff 27 0) X.
      rewrite X, (ps_denot_reg E2 27%nat (Z_to_bv 5 27) regs3 (EE2 27%nat (Z_to_bv 5 27) ltac:(reflexivity))).
      rewrite (HP3 27 ltac:(unfold acallee_saved; lia)).
      replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite M27. exact (KHI 27 ltac:(lia)).
  + (* a0 = 0 *)
    rewrite N10. cbn [sv_denot]. reflexivity.
- (* g_rec.refuse <> 0: the recorder's code goes to answer_code *)
  assert (Hrefne : r_refuse R <> 0).
  { intros Hz. revert Hc. cbn [branch_taken].
    rewrite (ps_sext32 E 35%nat (r_refuse R) E35 Hrf31). cbn [sv_denot]. rewrite Hz.
    rewrite (proj2 (bv_eqb_eq (Z_to_bv 64 0) (Z_to_bv 64 0)) eq_refl). discriminate. }
  (* 0x8c9fc .. 0x8ca28: g_rec.code into a0, the epilogue, the tail jump *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply awr_ok_cons_gen with (n := 34%nat); [reflexivity | exact UC | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
      exact (ps_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ (ps_c R) a Hcok ltac:(unfold CALL_SIZE; lia)). }
    eapply awr_ok_cons_gen with (n := 34%nat); [reflexivity | exact UC | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
      exact (ps_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ (ps_c R) a Hcok ltac:(unfold CALL_SIZE; lia)). }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_nil. }
  ps_fold_md.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    pose proof (st_ok_region_nth E _ _ 0%nat
      (YP09.mkRegion (Some 34%nat) 4 8 4 8 [YP09.mkChunk 4 (CVal 4 (SLit 4))]) HS ltac:(reflexivity)) as HR0;
    pose proof (st_ok_region_nth E _ _ 1%nat
      (YP09.mkRegion (Some 34%nat) 32 40 32 40 [YP09.mkChunk 32 (CVal 8 (SOff 10 0))]) HS ltac:(reflexivity)) as HR1;
    cbn [ms_mem restrict mkst] in HR0, HR1;
    assert (KEEP12 : forall y, 0 <= y < 2 ^ 64 -> ~ (ps_c R + 4 <= y < ps_c R + 8) ->
      ~ (ps_c R + 32 <= y < ps_c R + 40) -> rdW Wc (ms_mem msx) y = rdW Wc memc y)
  end.
  { intros y Hy N1 N2.
    transitivity (rdW Wc (ms_mem ms) y).
    - apply (ps_rd_frame E _ (w_H Wc) (ms_mem ms) _ y HF Hy).
      intros (r & Hin & Hr).
      lazymatch type of Hin with In r ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end.
      destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        [rewrite UC in Hr; lia | rewrite UC in Hr; lia | lia | lia | lia].
    - apply (ps_rd_frame E _ (w_H Wc) memc (ms_mem ms) y HF1 Hy).
      intros (r & Hin & Hr).
      lazymatch type of Hin with In r ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end.
      destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        [rewrite UC in Hr; lia | rewrite UC in Hr; lia | lia | lia | lia]. }
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    assert (V4b : aval_mem (rdW Wc (ms_mem msx)) (ps_c R + 4) 4 4);
    [ apply (aval_mem_view SEGS);
      exact (ps_field E _ 34%nat (ps_c R) _ 4 8 4 8 4 4%N (SLit 4) 4 (ps_c R + 4) 4%nat HR0 UC ltac:(ps_in) eq_refl
        ltac:(change (8 * Z.of_N 4) with 32; lia) ltac:(change (Z.of_N 4) with 4; lia) eq_refl eq_refl) |];
    assert (Vpb : aval_mem (rdW Wc (ms_mem msx)) (ps_c R + 8 + 8 * Z.of_nat (4 - 1)) 8 p);
    [ apply (aval_mem_view SEGS);
      exact (ps_field E _ 34%nat (ps_c R) _ 32 40 32 40 32 8%N (SOff 10 0) p
        (ps_c R + 8 + 8 * Z.of_nat (4 - 1)) 8%nat HR1 UC ltac:(ps_in) Hd10
        ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(change (Z.of_N 8) with 8; lia) ltac:(lia) eq_refl) |]
  end.
  destruct (STEP _ _ HJ KEEP12 V4b Vpb) as (O2 & HREP1 & HCOV1 & HO21 & HCALL1).
  pmkst HS. rewrite ps_sig_answer.
  refine (PS_TAIL lyc Sc Wc (ms_mem ms0) _ k (ms_regs ms0)
    (rec_record R REC_PINS_SET A) O2 (r_code R)
    HJ _ _ _ _ Hcd31 HREP1 HCOV1 Hlive HO21 (HMODT Hrefne) HEVT Hbb Hmo).
  + psgv HS (2%bv : bv 5) (SOff 2 80) X2.
    unfold spZ. rewrite X2, (ps_denot_off E 2%nat (sp0 - 80) 80 U2 ltac:(lia)).
    rewrite (unsigned_lit_small (sp0 - 80 + 80) ltac:(lia)). lia.
  + psgv HS (1%bv : bv 5) (SOff 38 0) X1.
    rewrite X1, (ps_denot_reg E 38%nat (Z_to_bv 5 1) regs (ESV 0%nat 1 eq_refl)).
    f_equal; try (apply bv_eq; reflexivity).
  + intros r Hr. unfold acallee_saved in Hr.
    assert (Hr15 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
      r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    repeat (destruct Hr15 as [Hr15 | Hr15]); subst r.
    * psgv HS (Z_to_bv 5 2) (SOff 2 80) X.
      rewrite X, (ps_denot_off E 2%nat (sp0 - 80) 80 U2 ltac:(lia)).
      replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
      unfold ps_sp0, spZ. replace (bv_unsigned (getr regs 2) - 80 + 80) with (bv_unsigned (getr regs 2)) by lia.
      apply Z_to_bv_bv_unsigned.
    * psgv HS (Z_to_bv 5 3) (SOff 3 0) X.
      rewrite X, (ps_denot_reg E 3%nat (Z_to_bv 5 3) regsc (EE 3%nat (Z_to_bv 5 3) ltac:(reflexivity))).
      replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite K3. symmetry. exact Hgp.
    * psgv HS (Z_to_bv 5 4) (SOff 4 0) X.
      rewrite X, (ps_denot_reg E 4%nat (Z_to_bv 5 4) regsc (EE 4%nat (Z_to_bv 5 4) ltac:(reflexivity))).
      replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite K4. symmetry. exact Htp.
    * psgv HS (Z_to_bv 5 8) (SOff 39 0) X.
      rewrite X, (ps_denot_reg E 39%nat (Z_to_bv 5 8) regs (ESV 1%nat 8 eq_refl)). reflexivity.
    * psgv HS (Z_to_bv 5 9) (SOff 40 0) X.
      rewrite X, (ps_denot_reg E 40%nat (Z_to_bv 5 9) regs (ESV 2%nat 9 eq_refl)). reflexivity.
    * psgv HS (Z_to_bv 5 18) (SOff 41 0) X.
      rewrite X, (ps_denot_reg E 41%nat (Z_to_bv 5 18) regs (ESV 3%nat 18 eq_refl)). reflexivity.
    * psgv HS (Z_to_bv 5 19) (SOff 42 0) X.
      rewrite X, (ps_denot_reg E 42%nat (Z_to_bv 5 19) regs (ESV 4%nat 19 eq_refl)). reflexivity.
    * psgv HS (Z_to_bv 5 20) (SOff 43 0) X.
      rewrite X, (ps_denot_reg E 43%nat (Z_to_bv 5 20) regs (ESV 5%nat 20 eq_refl)). reflexivity.
    * psgv HS (Z_to_bv 5 21) (SOff 44 0) X.
      rewrite X, (ps_denot_reg E 44%nat (Z_to_bv 5 21) regs (ESV 6%nat 21 eq_refl)). reflexivity.
    * psgv HS (Z_to_bv 5 22) (SOff 45 0) X.
      rewrite X, (ps_denot_reg E 45%nat (Z_to_bv 5 22) regs (ESV 7%nat 22 eq_refl)). reflexivity.
    * psgv HS (Z_to_bv 5 23) (SOff 46 0) X.
      rewrite X, (ps_denot_reg E 46%nat (Z_to_bv 5 23) regs (ESV 8%nat 23 eq_refl)). reflexivity.
    * psgv HS (Z_to_bv 5 24) (SOff 47 0) X.
      rewrite X, (ps_denot_reg E 47%nat (Z_to_bv 5 24) regs (ESV 9%nat 24 eq_refl)). reflexivity.
    * psgv HS (Z_to_bv 5 25) (SOff 25 0) X.
      rewrite X, (ps_denot_reg E 25%nat (Z_to_bv 5 25) regsc (EE 25%nat (Z_to_bv 5 25) ltac:(reflexivity))).
      exact (KHI 25 ltac:(lia)).
    * psgv HS (Z_to_bv 5 26) (SOff 26 0) X.
      rewrite X, (ps_denot_reg E 26%nat (Z_to_bv 5 26) regsc (EE 26%nat (Z_to_bv 5 26) ltac:(reflexivity))).
      exact (KHI 26 ltac:(lia)).
    * psgv HS (Z_to_bv 5 27) (SOff 27 0) X.
      rewrite X, (ps_denot_reg E 27%nat (Z_to_bv 5 27) regsc (EE 27%nat (Z_to_bv 5 27) ltac:(reflexivity))).
      exact (KHI 27 ltac:(lia)).
  + psgv HS (10%bv : bv 5) (SExt true 32 (SOff 36 0)) X10.
    rewrite X10, (ps_sext32 E 36%nat (r_code R) E36 Hcd31). reflexivity.
Qed.

End entry.
End e.
End f.
End d.
