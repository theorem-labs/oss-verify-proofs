(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the middle segments of pins_set's ASan walk (from the return of the j-th
   xstrdup to the call of the next one), after cgif_file_fuzzer's cgif_close walk, proofs/cgif/cgif_file_fuzzer/lib/A/ACh*.v
   at c8557374ad2e (a straight symbolic run, a branch on an argument, and the step through a call
   with cl_callS) over fuzz_command's recorder. *)

(* `ps_seg_x`: for j = 1 .. 3, the walk from the return of the j-th xstrdup (pc ps_ret j, the copy p in a0) to the
   call of the (j + 1)-th. The run checks the shadow byte of the slot's nargs word c + 4 (marked usable), loads nargs
   (the literal j - 1), stores j, checks the shadow byte of the argument word c + 8 + 8 (j - 1) and stores p there; the
   compare 4 < nargs is decided on the literal. The next argument is then tested against 0 (one branch; the other arm
   contradicts the statement's argument fact), the default literal replaces a NULL argument, and the run reaches the
   call of xstrdup. ps_store (pins_set_s7.v) turns the stored words into the invariant `ps_core (P ++ [pn]) []`, and
   ps_call_x (pins_set_s4.v) steps through the call into the premise `ps_xret_stmt (j + 1)`. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
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

(* the bytes a run of the segment may write: the slot's nargs word (c + 4 .. c + 8) and its argument word
   (c + 8 + 8 jz .. c + 16 + 8 jz); every other region of the run is read-only *)
Definition psx_wr_ok (jz : Z) (r : YP09.region) : bool :=
(YP09.r_whi r <=? YP09.r_wlo r) ||
(match YP09.r_base r with Some n => Nat.eqb n PS_C | None => false end &&
 (((YP09.r_wlo r =? 4) && (YP09.r_whi r =? 8)) ||
  ((YP09.r_wlo r =? 8 + 8 * jz) && (YP09.r_whi r =? 16 + 8 * jz)))).

Lemma psx_wr_cases : forall E rs jz a, forallb (psx_wr_ok jz) rs = true -> in_wrange E rs a ->
base_val E (Some PS_C) + 4 <= a < base_val E (Some PS_C) + 8 \/
base_val E (Some PS_C) + 8 + 8 * jz <= a < base_val E (Some PS_C) + 16 + 8 * jz.
Proof.
intros E rs jz a Hf (r & Hin & Ha).
pose proof (proj1 (forallb_forall _ rs) Hf r Hin) as Hr. unfold psx_wr_ok in Hr.
apply orb_true_iff in Hr as [Hr | Hr]; [apply Z.leb_le in Hr; lia|].
apply andb_true_iff in Hr as [Hb Hr].
destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate Hb].
apply Nat.eqb_eq in Hb. subst n.
apply orb_true_iff in Hr as [Hr | Hr]; apply andb_true_iff in Hr as [H1 H2]; apply Z.eqb_eq in H1, H2;
  rewrite H1, H2 in Ha; [left | right]; lia.
Qed.

Lemma psx_base_c : forall E c, ew E PS_C = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 -> base_val E (Some PS_C) = c.
Proof. intros E c H Hc. cbn [base_val]. rewrite H. apply unsigned_lit_small. exact Hc. Qed.

Lemma psx_den_atom : forall E k v d, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff k d) = Z_to_bv 64 (v + d).
Proof. intros E k v d Hk Hv. cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hv. reflexivity. Qed.

(* `bnez x` on an atom x *)
Lemma psx_bnez : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (v =? 0).
Proof. intros E n v Hn Hv. rewrite branch_ne_U, (U_atom E n v Hn Hv), U_SLit. reflexivity. Qed.

Ltac psx_in := cbn [In]; repeat first [ solve [left; reflexivity] | right ].
Ltac psx_creg := first [ intros ?; exfalso; lia | intros _; vm_compute; reflexivity ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the bytes outside the two words a segment writes keep their value *)
Definition psx_kept (Wc : world SEGS) (memc memc' : word -> option byte) (c jz : Z) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ (c + 4 <= x < c + 8) -> ~ (c + 8 + 8 * jz <= x < c + 16 + 8 * jz) ->
rdW Wc memc' x = rdW Wc memc x.

Lemma psx_kept_run : forall Wc memc m0 m1 E rs c jz, psx_kept Wc memc m0 c jz -> frame_of E rs m0 m1 ->
forallb (psx_wr_ok jz) rs = true -> ew E PS_C = Z_to_bv 64 c -> 0 <= c < 2 ^ 64 -> psx_kept Wc memc m1 c jz.
Proof.
intros Wc memc m0 m1 E rs c jz HK Hf Hrs Hc Hc64 x Hx H1 H2.
rewrite (ps_rd_frame E rs (w_H Wc) m0 m1 x Hf Hx); [exact (HK x Hx H1 H2)|].
intros Hw. destruct (psx_wr_cases E rs jz x Hrs Hw) as [Hw' | Hw']; rewrite (psx_base_c E c Hc Hc64) in Hw'; lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis TXSTRDUP : txstrdup_spec B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a, AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* every byte the run may write is a byte of the slot, a program static in the footprint *)
Lemma psx_awr : forall O E rs c jz STK sp0 bl0 blc fr0 lyc own, forallb (psx_wr_ok jz) rs = true ->
ew E PS_C = Z_to_bv 64 c -> ps_slot_ok c -> 0 <= jz <= 3 ->
awr_ok SEGS B E rs STK sp0 (ps_FP O) bl0 blc fr0 lyc own.
Proof.
intros O E rs c jz STK sp0 bl0 blc fr0 lyc own Hrs Hc Hcok Hj a Hw.
destruct (ps_slot_bounds c Hcok) as [Hcb _].
assert (Hc64 : 0 <= c < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
apply (ps_awr_slot B HB cmd_prog_img STK sp0 O bl0 blc fr0 lyc own c a Hcok).
destruct (psx_wr_cases E rs jz a Hrs Hw) as [Hw' | Hw']; rewrite (psx_base_c E c Hc Hc64) in Hw'; unfold CALL_SIZE; lia.
Qed.

Lemma psx_den_reg : forall (regsc rg : bvmap 5 word) c rf cd st k (r : bv 5), Z.of_nat k = bv_unsigned r ->
sv_denot (ps_Ec regsc rg c rf cd st) (SOff k 0) = getr regsc r.
Proof.
intros regsc rg c rf cd st k r Hk.
destruct (ps_Ec_facts VOBJS regsc rg c rf cd st) as (_ & _ & _ & _ & _ & _ & _ & _ & EE & _).
cbn [sv_denot]. rewrite (EE k r Hk), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma psx_atom_env : forall (regsc rg : bvmap 5 word) c rf cd st a, (A_TEXT <= a < A_LIM)%nat ->
ew (ps_Ec regsc rg c rf cd st) a = Z_to_bv 64 (VAL a).
Proof.
intros regsc rg c rf cd st a Ha.
exact (img_env_atomP _ a (proj1 (ps_Ec_facts VOBJS regsc rg c rf cd st)) Ha).
Qed.

(* an argument of the statement is NULL (p = 0) or a string (p <> 0) *)
Lemma psx_arg_nz : forall ly0 S0 rd ro O0 p v, astr_argA B ly0 S0 rd ro O0 p v ->
(v = None /\ p = 0) \/ (exists x, v = Some x /\ p <> 0).
Proof.
intros ly0 S0 rd ro O0 p v H. destruct v as [x|].
- right. exists x. split; [reflexivity | exact (proj1 H)].
- left. split; [reflexivity | exact H].
Qed.

Section entry.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (pu pf pl pv : Z) (uri files layout verdict : option (list byte)) (R : rstate)
  (O : list (Z * Z)).
Hypothesis HPRE : afn_pre SEGS B PINS_SET_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis HSU : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu uri.
Hypothesis HSF : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pf files.
Hypothesis HSL : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pl layout.
Hypothesis HSV : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pv verdict.
Hypothesis HREPA : rec_repA B ly S (rdW W mem) R O.
Hypothesis HEV : st_nev S + EV_PINS_SET R <= EV_MAX.
Hypothesis HLIVE : blocks_bytes S + LIVE_PINS_SET R uri files layout verdict <= LIVE_MAX.
Hypothesis HMOK : mo_ok MT S (XM_PINS_SET MT R uri files layout verdict).

#[local] Notation sp0 := (ps_sp0 regs).
#[local] Notation FPps := (ps_FP O).
#[local] Notation A := (ps_A uri files layout verdict).
#[local] Notation PTRS := (ps_ptrs pu pf pl pv uri files layout verdict).
#[local] Notation CORE := (ps_core B MT ly S W regs mem md uri files layout verdict R O).
#[local] Notation KEEP := (ps_keep B regs pf pl pv R).
#[local] Notation POST := (ps_post B MT ly S W regs mem md uri files layout verdict R O).
(* the environment of a segment's symbolic state: the registers at the return of xstrdup, the slot, and g_rec's
   refuse / code / state as the invariant holds them (ps_core_scalars) *)
#[local] Notation ESX regsc := (ps_Ec regsc regs (ps_c R) (r_refuse R mod 2 ^ 32) (r_code R mod 2 ^ 32) (r_state R)).

(* an argument of the statement is NULL, a byte of a live block, or a byte of the read-only image: a 64-bit value *)
Lemma psx_arg_bound : forall p v, astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p v -> 0 <= p < 2 ^ 64.
Proof.
intros p v H. destruct v as [x|]; [|cbn in H; lia].
destruct H as (_ & _ & _ & [((q & m & Hqm & Hq1 & Hq2) & _) | (Hro & _)]).
- pose proof HPRE as (HAR & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hqm) as (_ & H4096 & Hce & _).
  pose proof asan_consts as (C1 & _).
  assert (Hrq : req_size m >= m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  lia.
- destruct (Hro 0 ltac:(lia)) as (Hr & _). rewrite Z.add_0_r in Hr.
  destruct (cmd_ro_prog_apart p Hr) as [Himg _]. pose proof (pa_img_range _ Himg). lia.
Qed.

(* the copy xstrdup returned is a live block: below the allocator's ceiling *)
Lemma psx_p_bounds : forall P p n lyc Sc Wc memc mdc k, CORE P [(p, n)] lyc Sc Wc memc mdc k -> 0 <= p < 2 ^ 64.
Proof.
intros P p n lyc Sc Wc memc mdc k HC.
destruct HC as [HJ _ _ _ _ _ _ (Rb & Qb & rdb & blb & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNEWB)].
assert (Hi : nth_error (P ++ [(p, n)]) (length P) = Some (p, n))
  by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
destruct (HNEWB _ _ Hi) as (_ & Hn & _ & Hin & _). cbn [snd] in Hn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ) Hin) as (_ & H4096 & Hce & _).
pose proof asan_consts as (C1 & _).
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
rewrite Hrq in Hce. lia.
Qed.

(* the two default literals' atoms in a segment's environment *)
Lemma psx_null_env : forall regsc, ew (ESX regsc) PS_NULL = Z_to_bv 64 0x22480.
Proof.
intros regsc. rewrite (psx_atom_env regsc regs _ _ _ _ PS_NULL ltac:(unfold PS_NULL, A_OBJ, A_TEXT, A_LIM; lia)).
rewrite (ps_null_val VOBJS). reflexivity.
Qed.
Lemma psx_dash_env : forall regsc, ew (ESX regsc) PS_DASH = Z_to_bv 64 0x21d40.
Proof.
intros regsc. rewrite (psx_atom_env regsc regs _ _ _ _ PS_DASH ltac:(unfold PS_DASH, A_OBJ, A_TEXT, A_LIM; lia)).
rewrite (ps_dash_val VOBJS). reflexivity.
Qed.

(* the symbolic state at the return of the j-th xstrdup, from the invariant *)
Lemma psx_seed : forall j P pn lyc Sc Wc regsc memc mdc k,
(1 <= j <= 3)%nat -> length P = (j - 1)%nat -> CORE P [pn] lyc Sc Wc memc mdc k -> KEEP j regsc ->
st_ok_pi SEGS VAL (ESX regsc) (mkSS (ps_ret j) (ps_sregs j) (ps_aft_rs j) None ps_mfacts)
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + ps_ret j)) memc (seg_rom SEGS))) /\
sh_ok SEGS ps_Bx ps_SH (ESX regsc) (mrestrict (w_H Wc) memc).
Proof.
intros j P pn lyc Sc Wc regsc memc mdc k Hj HlenP HC HK.
pose proof (ps_core_slot B MT ly S W regs mem md uri files layout verdict R O P [pn] lyc Sc Wc memc mdc k HC)
  as (_ & Hcok & _).
pose proof (ps_core_scalars B MT ly S W regs mem md uri files layout verdict R O P [pn] lyc Sc Wc memc mdc k HC)
  as (HRF & HCD & HST & Hst & _ & _).
pose proof (ps_sp0_facts B ly S W regs mem md ch HPRE) as (Hsp & Hsp16 & Hspc).
destruct HK as (K2 & K3 & K4 & K8 & K18 & K22 & K23 & K24 & K21 & K20 & K19 & K9 & KHI).
pose proof HC as [HJ _ _ _ _ Hfr _ Hrec].
destruct Hrec as (Rb & Qb & rdb & blb & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNA & _).
assert (Hsp' : spZ regsc = ps_sp0 regs - 80)
  by (unfold spZ; rewrite K2; unfold w64; apply unsigned_lit_small; lia).
exact (ps_aft_seed B HB VOBJS cmd_prog_writable lyc Sc Wc memc mdc regs regsc j (ps_ret j) (ps_c R)
  (r_refuse R mod 2 ^ 32) (r_code R mod 2 ^ 32) (r_state R) (proj1 HJ) Hcok ltac:(lia)
  ltac:(rewrite Hsp'; lia)
  ltac:(rewrite Hsp'; replace (ps_sp0 regs - 80) with (ps_sp0 regs + (-5) * 16) by lia;
        rewrite Z_mod_plus_full; exact Hsp16)
  K8 K18 K22 K23 K24 K21
  ltac:(rewrite <- HlenP; exact HNA)
  ltac:(intros i r Hir; rewrite Hsp';
        replace (ps_sp0 regs - 80 + 72 - 8 * Z.of_nat i) with (ps_sp0 regs - 8 - 8 * Z.of_nat i) by lia;
        exact (Hfr i r Hir))
  HRF HCD HST ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) Hst).
Qed.

(* the registers a callee keeps, at the call of the (j + 1)-th xstrdup *)
Lemma psx_keep_next : forall j regsc regs2,
(1 <= j <= 3)%nat -> KEEP j regsc -> ps_slot_ok (ps_c R) ->
getr regs2 2 = sv_denot (ESX regsc) (SOff 2 0) ->
getr regs2 3 = sv_denot (ESX regsc) (SOff 3 0) ->
getr regs2 4 = sv_denot (ESX regsc) (SOff 4 0) ->
getr regs2 8 = sv_denot (ESX regsc) (SOff PS_C 0) ->
getr regs2 18 = sv_denot (ESX regsc) (SOff PS_C 4) ->
getr regs2 21 = sv_denot (ESX regsc) (SOff PS_C 8) ->
getr regs2 22 = sv_denot (ESX regsc) (SOff PS_GREC 0) ->
getr regs2 23 = sv_denot (ESX regsc) (SOff PS_SB 0) ->
getr regs2 24 = sv_denot (ESX regsc) ps_shx ->
((Datatypes.S j <= 2)%nat -> getr regs2 19 = sv_denot (ESX regsc) (SOff 19 0)) ->
((Datatypes.S j <= 3)%nat -> getr regs2 9 = sv_denot (ESX regsc) (SOff 9 0)) ->
getr regs2 25 = sv_denot (ESX regsc) (SOff 25 0) ->
getr regs2 26 = sv_denot (ESX regsc) (SOff 26 0) ->
getr regs2 27 = sv_denot (ESX regsc) (SOff 27 0) ->
KEEP (Datatypes.S j) regs2.
Proof.
intros j regsc regs2 Hj HK Hcok R2 R3 R4 R8 R18 R21 R22 R23 R24 R19 R9 R25 R26 R27.
destruct HK as (K2 & K3 & K4 & _ & _ & _ & _ & _ & _ & _ & K19 & K9 & KHI).
destruct (ps_Ec_facts VOBJS regsc regs (ps_c R) (r_refuse R mod 2 ^ 32) (r_code R mod 2 ^ 32) (r_state R))
  as (_ & ESB & EC & _ & _ & _ & EG & _ & _ & _).
destruct (ps_slot_bounds (ps_c R) Hcok) as [Hcb _].
assert (Hc64 : 0 <= ps_c R < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
unfold ps_keep.
split; [rewrite R2, (psx_den_reg regsc regs _ _ _ _ 2%nat (2%bv : bv 5) eq_refl); exact K2|].
split; [rewrite R3, (psx_den_reg regsc regs _ _ _ _ 3%nat (3%bv : bv 5) eq_refl); exact K3|].
split; [rewrite R4, (psx_den_reg regsc regs _ _ _ _ 4%nat (4%bv : bv 5) eq_refl); exact K4|].
split; [rewrite R8, (psx_den_atom _ PS_C (ps_c R) 0 EC Hc64), Z.add_0_r; reflexivity|].
split; [rewrite R18, (psx_den_atom _ PS_C (ps_c R) 4 EC Hc64); reflexivity|].
split; [rewrite R22, (psx_den_atom _ PS_GREC A_G_REC 0 EG ltac:(unfold A_G_REC; lia)), Z.add_0_r; reflexivity|].
split; [rewrite R23, (psx_den_atom _ PS_SB SB 0 ESB ltac:(unfold SB; lia)), Z.add_0_r; reflexivity|].
split.
{ rewrite R24. unfold ps_shx.
  rewrite (denot_shx _ PS_C PS_SB 4 (ps_c R) SB EC ESB) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS, SB in *; lia).
  reflexivity. }
split; [intros _; rewrite R21, (psx_den_atom _ PS_C (ps_c R) 8 EC Hc64); reflexivity|].
split; [intros Hx; lia|].
split; [intros Hx; rewrite (R19 Hx), (psx_den_reg regsc regs _ _ _ _ 19%nat (19%bv : bv 5) eq_refl); exact (K19 ltac:(lia))|].
split; [intros Hx; rewrite (R9 Hx), (psx_den_reg regsc regs _ _ _ _ 9%nat (9%bv : bv 5) eq_refl); exact (K9 ltac:(lia))|].
intros r Hr. rewrite <- (KHI r Hr).
assert (Hr3 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr3 as [-> | [-> | ->]].
- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite R25. exact (psx_den_reg regsc regs _ _ _ _ 25%nat (25%bv : bv 5) eq_refl).
- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite R26. exact (psx_den_reg regsc regs _ _ _ _ 26%nat (26%bv : bv 5) eq_refl).
- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite R27. exact (psx_den_reg regsc regs _ _ _ _ 27%nat (27%bv : bv 5) eq_refl).
Qed.

(* the end of a segment: the state at the call of the (j + 1)-th xstrdup gives the invariant `ps_core (P ++ [pn]) []`
   (ps_store), the kept registers, the return address and the argument, and ps_call_x steps through the call *)
Lemma psx_fin : forall j P p lyc Sc Wc regsc memc mdc k ss ms2 mdc2 a0e,
(1 <= j <= 3)%nat -> length P = (j - 1)%nat ->
CORE P [(p, Z.of_nat (length (nth (j - 1) A [])) + 1)] lyc Sc Wc memc mdc k ->
KEEP j regsc -> getr regsc 10 = w64 p ->
ps_xret_stmt B MT ly S W regs mem md pf pl pv uri files layout verdict R O (Datatypes.S j) ->
ajournal SEGS B PINS_SET_STK sp0 FPps ly S W mem md [] lyc Sc Wc (ms_mem ms2) mdc2 k ->
psx_kept Wc memc (ms_mem ms2) (ps_c R) (Z.of_nat (j - 1)) ->
st_ok SEGS (ESX regsc) (YP0l.setpc ss (pa_sigma CS_xstrdup)) (restrict (w_H Wc) ms2) ->
ss_resv ss = None ->
sr_get (ss_regs ss) 1 = SOff A_TEXT (ps_ret (Datatypes.S j)) ->
sr_get (ss_regs ss) 2 = SOff 2 0 -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 8 = SOff PS_C 0 -> sr_get (ss_regs ss) 18 = SOff PS_C 4 ->
sr_get (ss_regs ss) 21 = SOff PS_C 8 -> sr_get (ss_regs ss) 22 = SOff PS_GREC 0 ->
sr_get (ss_regs ss) 23 = SOff PS_SB 0 -> sr_get (ss_regs ss) 24 = ps_shx ->
((Datatypes.S j <= 2)%nat -> sr_get (ss_regs ss) 19 = SOff 19 0) ->
((Datatypes.S j <= 3)%nat -> sr_get (ss_regs ss) 9 = SOff 9 0) ->
sr_get (ss_regs ss) 25 = SOff 25 0 -> sr_get (ss_regs ss) 26 = SOff 26 0 -> sr_get (ss_regs ss) 27 = SOff 27 0 ->
sr_get (ss_regs ss) 10 = a0e -> sv_denot (ESX regsc) a0e = w64 (nth (Datatypes.S j - 1) PTRS 0) ->
nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some PS_C) 4 8 4 8 [YP09.mkChunk 4 (CVal 4 (SLit (Z.of_nat j)))]) ->
nth_error (ss_mem ss) 1 = Some (YP09.mkRegion (Some PS_C) (8 + 8 * Z.of_nat (j - 1)) (16 + 8 * Z.of_nat (j - 1))
  (8 + 8 * Z.of_nat (j - 1)) (16 + 8 * Z.of_nat (j - 1))
  [YP09.mkChunk (8 + 8 * Z.of_nat (j - 1)) (CVal 8 (SOff 10 0))]) ->
SRr SEGS Wc (mkCfg ms2 mdc2) POST.
Proof.
intros j P p lyc Sc Wc regsc memc mdc k ss ms2 mdc2 a0e Hj HlenP HC HK H10 HNEXT HJ2 KP HS Hrv
  S1 S2 S3 S4 S8 S18 S21 S22 S23 S24 S19 S9 S25 S26 S27 S10 Ha0 HM0 HM1.
pose proof (ps_core_slot B MT ly S W regs mem md uri files layout verdict R O P _ lyc Sc Wc memc mdc k HC)
  as (_ & Hcok & _).
destruct (ps_slot_bounds (ps_c R) Hcok) as [Hcb _].
assert (Hc64 : 0 <= ps_c R < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
pose proof (psx_p_bounds P p _ lyc Sc Wc memc mdc k HC) as Hp64.
destruct (ps_Ec_facts VOBJS regsc regs (ps_c R) (r_refuse R mod 2 ^ 32) (r_code R mod 2 ^ 32) (r_state R))
  as (HEI & _ & EC & _ & _ & _ & _ & _ & _ & _).
assert (Ecu : bv_unsigned (ew (ESX regsc) PS_C) = ps_c R) by (rewrite EC; apply unsigned_lit_small; exact Hc64).
assert (RG : forall r, getr (ms_regs ms2) r = sv_denot (ESX regsc) (sr_get (ss_regs ss) r))
  by (intros r; exact (st_ok_restrict_reg SEGS (w_H Wc) _ _ ms2 r HS)).
(* the stored count and the stored copy, from the regions of the final state *)
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS HM0) as HR0.
pose proof (st_ok_region_nth _ _ _ 1%nat _ HS HM1) as HR1.
cbn [ms_mem restrict] in HR0, HR1.
pose proof (field_of_region_any (ESX regsc) (mrestrict (w_H Wc) (ms_mem ms2)) PS_C (ps_c R) _ 4 8 4 8 4 4%N
  (SLit (Z.of_nat j)) HR0 Ecu (or_introl eq_refl) ltac:(cbn; lia)) as HV0.
pose proof (field_of_region_any (ESX regsc) (mrestrict (w_H Wc) (ms_mem ms2)) PS_C (ps_c R) _
  (8 + 8 * Z.of_nat (j - 1)) (16 + 8 * Z.of_nat (j - 1)) (8 + 8 * Z.of_nat (j - 1)) (16 + 8 * Z.of_nat (j - 1))
  (8 + 8 * Z.of_nat (j - 1)) 8%N (SOff 10 0) HR1 Ecu (or_introl eq_refl) ltac:(cbn; lia)) as HV1.
assert (HNA : aval_mem (rdW Wc (ms_mem ms2)) (ps_c R + 4) 4 (Z.of_nat j)).
{ apply (aval_mem_view SEGS (w_H Wc) (ms_mem ms2) (ps_c R + 4) 4%nat (Z.of_nat j)).
  cbn [sv_denot] in HV0. rewrite ps_pow4, unsigned_lit_small, Z.mod_small in HV0 by lia. exact HV0. }
assert (HARG : aval_mem (rdW Wc (ms_mem ms2)) (ps_c R + 8 + 8 * Z.of_nat (j - 1)) 8 p).
{ replace (ps_c R + 8 + 8 * Z.of_nat (j - 1)) with (ps_c R + (8 + 8 * Z.of_nat (j - 1))) by lia.
  apply (aval_mem_view SEGS (w_H Wc) (ms_mem ms2) _ 8%nat p).
  rewrite (psx_den_reg regsc regs _ _ _ _ 10%nat (10%bv : bv 5) eq_refl), H10 in HV1. unfold w64 in HV1.
  rewrite ps_pow8, unsigned_lit_small, Z.mod_small in HV1 by exact Hp64. exact HV1. }
pose proof (ps_store B MT ly S W regs mem md ch uri files layout verdict R O HPRE j P _ lyc Sc Wc memc (ms_mem ms2)
  mdc mdc2 k ltac:(lia) HlenP HC HJ2 KP HNA HARG) as HC2.
(* the registers at the call *)
assert (HK2 : KEEP (Datatypes.S j) (ms_regs ms2)).
{ apply (psx_keep_next j regsc (ms_regs ms2) Hj HK Hcok).
  - rewrite RG, S2. reflexivity.
  - rewrite RG, S3. reflexivity.
  - rewrite RG, S4. reflexivity.
  - rewrite RG, S8. reflexivity.
  - rewrite RG, S18. reflexivity.
  - rewrite RG, S21. reflexivity.
  - rewrite RG, S22. reflexivity.
  - rewrite RG, S23. reflexivity.
  - rewrite RG, S24. reflexivity.
  - intros Hx. rewrite RG, (S19 Hx). reflexivity.
  - intros Hx. rewrite RG, (S9 Hx). reflexivity.
  - rewrite RG, S25. reflexivity.
  - rewrite RG, S26. reflexivity.
  - rewrite RG, S27. reflexivity. }
assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + ps_ret (Datatypes.S j)))
  by (rewrite RG, S1; exact (codeptr_val (ESX regsc) _ HEI)).
assert (Ha0' : getr (ms_regs ms2) 10 = w64 (nth (Datatypes.S j - 1) PTRS 0)) by (rewrite RG, S10; exact Ha0).
assert (Hlen2 : length (P ++ [(p, Z.of_nat (length (nth (j - 1) A [])) + 1)]) = (Datatypes.S j - 1)%nat)
  by (rewrite length_app; cbn [length]; lia).
rewrite (st_ok_restrict_mkst SEGS (w_H Wc) (ESX regsc) (YP0l.setpc ss (pa_sigma CS_xstrdup)) ms2 HS Hrv).
cbn [ss_pc YP0l.setpc].
rewrite (SIGP CS_xstrdup ltac:(unfold cmd_prog_syms; psx_in)).
replace (cmd_af CS_xstrdup) with AF_xstrdup by (vm_compute; reflexivity).
exact (ps_call_x B MT TXSTRDUP MTL HB cmd_prog_img RRO RELRO_IMG cmd_ro_ok_of_aro cmd_ro_prog_apart cmd_heap_tail_vis
  CMD_RO_IN ly S W regs mem md ch pu pf pl pv uri files layout verdict R O HPRE HROD HSU HSF HSL HSV HREPA HEV
  HLIVE HMOK (Datatypes.S j) _ lyc Sc Wc (ms_regs ms2) (ms_mem ms2) mdc2 k ltac:(lia) Hlen2 HC2 HK2 Hra Ha0'
  (fun ly2 S2 W2 regs2 mem2 md2 p2 HC3 HK3 H103 =>
     HNEXT _ p2 ly2 S2 W2 regs2 mem2 md2 (k + 1) Hlen2 HC3 HK3 H103)).
Qed.

(* --- the runs ------------------------------------------------------------------------------------------- *)

Ltac psx_awr_tac c jz EC Hcok :=
  lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx (ps_FP ?Ox) ?b0 ?bc ?fr ?lyx ?own =>
    exact (psx_awr Ox Ex rs c jz stk spx b0 bc fr lyx own ltac:(vm_compute; reflexivity) EC Hcok ltac:(lia)) end.

Ltac psx_keep c jz EC Hc64 :=
  lazymatch goal with HF : frame_of ?Ex ?rs ?m0 ?m1, KP : psx_kept ?Wx ?mx ?m0 _ _ |- _ =>
    let KP2 := fresh "KP" in
    pose proof (psx_kept_run Wx mx m0 m1 Ex rs c jz KP HF ltac:(vm_compute; reflexivity) EC Hc64) as KP2;
    clear KP; rename KP2 into KP end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* one symbolic run, its write obligation, the model fixed (the memory trap: chained runs double it), the kept bytes *)
Ltac psx_run c jz EC Hcok Hc64 :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ => paj_run_tok RUN HS HJ SHOK Bspan end;
  [ psx_awr_tac c jz EC Hcok | ];
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy _) _ _) in *; clearbody mdv;
  psx_keep c jz EC Hc64.

Ltac psx_fin_tac j P p lyc Sc Wc regsc memc mdc k HlenP HC HK H10 HNEXT a0e HA0 :=
  lazymatch goal with HS : st_ok _ _ (YP0l.setpc ?ssx _) (restrict _ ?msx),
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, KP : psx_kept _ _ _ _ _ |- SRr _ _ (mkCfg _ ?mdx) _ =>
  exact (psx_fin j P p lyc Sc Wc regsc memc mdc k ssx msx mdx a0e ltac:(lia) HlenP HC HK H10 HNEXT HJ KP HS eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(psx_creg) ltac:(psx_creg)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) HA0
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.

(* the segment from the return of the first xstrdup to the call of the second (files) *)
Lemma ps_seg_x1 : ps_segx_stmt B MT ly S W regs mem md pf pl pv uri files layout verdict R O 1.
Proof.
unfold ps_segx_stmt. intros HNEXT. unfold ps_xret_stmt.
intros P p lyc Sc Wc regsc memc mdc k HlenP HC HK H10.
pose proof (ps_core_slot B MT ly S W regs mem md uri files layout verdict R O P _ lyc Sc Wc memc mdc k HC)
  as (_ & Hcok & _).
destruct (ps_slot_bounds (ps_c R) Hcok) as [Hcb _].
assert (Hc64 : 0 <= ps_c R < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K20 & _ & _ & _).
destruct (ps_Ec_facts VOBJS regsc regs (ps_c R) (r_refuse R mod 2 ^ 32) (r_code R mod 2 ^ 32) (r_state R))
  as (HEI & _ & EC & _ & _ & _ & _ & _ & EE & _).
assert (EN : ew (ESX regsc) 20 = Z_to_bv 64 pf)
  by (rewrite (EE 20%nat (20%bv : bv 5) eq_refl); exact (K20 ltac:(lia))).
assert (KP : psx_kept Wc memc memc (ps_c R) (Z.of_nat (1 - 1))) by (intros x _ _ _; reflexivity).
pose proof HC as [HJ _ _ _ _ _ _ _].
destruct (psx_seed 1 P _ lyc Sc Wc regsc memc mdc k ltac:(lia) HlenP HC HK) as [HS SHOK].
psx_run (ps_c R) (Z.of_nat (1 - 1)) EC Hcok Hc64.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* files <> NULL *)
  rewrite (psx_bnez _ 20 pf EN (psx_arg_bound pf files HSF)) in Hc.
  destruct (psx_arg_nz _ _ _ _ _ _ _ HSF) as [(EL & Hp0) | (x & EL & Hp0)];
    [rewrite Hp0 in Hc; cbn in Hc; discriminate Hc|].
  psx_run (ps_c R) (Z.of_nat (1 - 1)) EC Hcok Hc64.
  assert (HA0 : sv_denot (ESX regsc) (SOff 20 0) = w64 (nth (Datatypes.S 1 - 1) PTRS 0)).
  { rewrite (psx_den_reg regsc regs _ _ _ _ 20%nat (20%bv : bv 5) eq_refl).
    unfold ps_ptrs. cbn [nth Nat.sub]. rewrite EL. cbn [ps_sptr]. exact (K20 ltac:(lia)). }
  psx_fin_tac 1%nat P p lyc Sc Wc regsc memc mdc k HlenP HC HK H10 HNEXT (SOff 20 0) HA0.
- (* files = NULL: the default literal "(null)" *)
  rewrite (psx_bnez _ 20 pf EN (psx_arg_bound pf files HSF)) in Hc.
  destruct (psx_arg_nz _ _ _ _ _ _ _ HSF) as [(EL & Hp0) | (x & EL & Hp0)];
    [|apply negb_false_iff, Z.eqb_eq in Hc; contradiction].
  psx_run (ps_c R) (Z.of_nat (1 - 1)) EC Hcok Hc64.
  assert (HA0 : sv_denot (ESX regsc) (SOff PS_NULL 0) = w64 (nth (Datatypes.S 1 - 1) PTRS 0)).
  { rewrite (psx_den_atom (ESX regsc) PS_NULL 0x22480 0 (psx_null_env regsc) ltac:(lia)).
    unfold ps_ptrs. cbn [nth Nat.sub]. rewrite EL. cbn [ps_sptr]. rewrite Z.add_0_r. reflexivity. }
  psx_fin_tac 1%nat P p lyc Sc Wc regsc memc mdc k HlenP HC HK H10 HNEXT (SOff PS_NULL 0) HA0.
Qed.

(* the segment from the return of the second xstrdup to the call of the third (layout) *)
Lemma ps_seg_x2 : ps_segx_stmt B MT ly S W regs mem md pf pl pv uri files layout verdict R O 2.
Proof.
unfold ps_segx_stmt. intros HNEXT. unfold ps_xret_stmt.
intros P p lyc Sc Wc regsc memc mdc k HlenP HC HK H10.
pose proof (ps_core_slot B MT ly S W regs mem md uri files layout verdict R O P _ lyc Sc Wc memc mdc k HC)
  as (_ & Hcok & _).
destruct (ps_slot_bounds (ps_c R) Hcok) as [Hcb _].
assert (Hc64 : 0 <= ps_c R < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K19 & _ & _).
destruct (ps_Ec_facts VOBJS regsc regs (ps_c R) (r_refuse R mod 2 ^ 32) (r_code R mod 2 ^ 32) (r_state R))
  as (HEI & _ & EC & _ & _ & _ & _ & _ & EE & _).
assert (EN : ew (ESX regsc) 19 = Z_to_bv 64 pl)
  by (rewrite (EE 19%nat (19%bv : bv 5) eq_refl); exact (K19 ltac:(lia))).
assert (KP : psx_kept Wc memc memc (ps_c R) (Z.of_nat (2 - 1))) by (intros x _ _ _; reflexivity).
pose proof HC as [HJ _ _ _ _ _ _ _].
destruct (psx_seed 2 P _ lyc Sc Wc regsc memc mdc k ltac:(lia) HlenP HC HK) as [HS SHOK].
psx_run (ps_c R) (Z.of_nat (2 - 1)) EC Hcok Hc64.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* layout <> NULL *)
  rewrite (psx_bnez _ 19 pl EN (psx_arg_bound pl layout HSL)) in Hc.
  destruct (psx_arg_nz _ _ _ _ _ _ _ HSL) as [(EL & Hp0) | (x & EL & Hp0)];
    [rewrite Hp0 in Hc; cbn in Hc; discriminate Hc|].
  psx_run (ps_c R) (Z.of_nat (2 - 1)) EC Hcok Hc64.
  assert (HA0 : sv_denot (ESX regsc) (SOff 19 0) = w64 (nth (Datatypes.S 2 - 1) PTRS 0)).
  { rewrite (psx_den_reg regsc regs _ _ _ _ 19%nat (19%bv : bv 5) eq_refl).
    unfold ps_ptrs. cbn [nth Nat.sub]. rewrite EL. cbn [ps_sptr]. exact (K19 ltac:(lia)). }
  psx_fin_tac 2%nat P p lyc Sc Wc regsc memc mdc k HlenP HC HK H10 HNEXT (SOff 19 0) HA0.
- (* layout = NULL: the default literal "(null)" *)
  rewrite (psx_bnez _ 19 pl EN (psx_arg_bound pl layout HSL)) in Hc.
  destruct (psx_arg_nz _ _ _ _ _ _ _ HSL) as [(EL & Hp0) | (x & EL & Hp0)];
    [|apply negb_false_iff, Z.eqb_eq in Hc; contradiction].
  psx_run (ps_c R) (Z.of_nat (2 - 1)) EC Hcok Hc64.
  assert (HA0 : sv_denot (ESX regsc) (SOff PS_NULL 0) = w64 (nth (Datatypes.S 2 - 1) PTRS 0)).
  { rewrite (psx_den_atom (ESX regsc) PS_NULL 0x22480 0 (psx_null_env regsc) ltac:(lia)).
    unfold ps_ptrs. cbn [nth Nat.sub]. rewrite EL. cbn [ps_sptr]. rewrite Z.add_0_r. reflexivity. }
  psx_fin_tac 2%nat P p lyc Sc Wc regsc memc mdc k HlenP HC HK H10 HNEXT (SOff PS_NULL 0) HA0.
Qed.

(* the segment from the return of the third xstrdup to the call of the fourth (verdict) *)
Lemma ps_seg_x3 : ps_segx_stmt B MT ly S W regs mem md pf pl pv uri files layout verdict R O 3.
Proof.
unfold ps_segx_stmt. intros HNEXT. unfold ps_xret_stmt.
intros P p lyc Sc Wc regsc memc mdc k HlenP HC HK H10.
pose proof (ps_core_slot B MT ly S W regs mem md uri files layout verdict R O P _ lyc Sc Wc memc mdc k HC)
  as (_ & Hcok & _).
destruct (ps_slot_bounds (ps_c R) Hcok) as [Hcb _].
assert (Hc64 : 0 <= ps_c R < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
destruct (ps_Ec_facts VOBJS regsc regs (ps_c R) (r_refuse R mod 2 ^ 32) (r_code R mod 2 ^ 32) (r_state R))
  as (HEI & _ & EC & _ & _ & _ & _ & _ & EE & _).
assert (EN : ew (ESX regsc) 9 = Z_to_bv 64 pv)
  by (rewrite (EE 9%nat (9%bv : bv 5) eq_refl); exact (K9 ltac:(lia))).
assert (KP : psx_kept Wc memc memc (ps_c R) (Z.of_nat (3 - 1))) by (intros x _ _ _; reflexivity).
pose proof HC as [HJ _ _ _ _ _ _ _].
destruct (psx_seed 3 P _ lyc Sc Wc regsc memc mdc k ltac:(lia) HlenP HC HK) as [HS SHOK].
psx_run (ps_c R) (Z.of_nat (3 - 1)) EC Hcok Hc64.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* verdict <> NULL *)
  rewrite (psx_bnez _ 9 pv EN (psx_arg_bound pv verdict HSV)) in Hc.
  destruct (psx_arg_nz _ _ _ _ _ _ _ HSV) as [(EL & Hp0) | (x & EL & Hp0)];
    [rewrite Hp0 in Hc; cbn in Hc; discriminate Hc|].
  psx_run (ps_c R) (Z.of_nat (3 - 1)) EC Hcok Hc64.
  assert (HA0 : sv_denot (ESX regsc) (SOff 9 0) = w64 (nth (Datatypes.S 3 - 1) PTRS 0)).
  { rewrite (psx_den_reg regsc regs _ _ _ _ 9%nat (9%bv : bv 5) eq_refl).
    unfold ps_ptrs. cbn [nth Nat.sub]. rewrite EL. cbn [ps_sptr]. exact (K9 ltac:(lia)). }
  psx_fin_tac 3%nat P p lyc Sc Wc regsc memc mdc k HlenP HC HK H10 HNEXT (SOff 9 0) HA0.
- (* verdict = NULL: the default literal "-" *)
  rewrite (psx_bnez _ 9 pv EN (psx_arg_bound pv verdict HSV)) in Hc.
  destruct (psx_arg_nz _ _ _ _ _ _ _ HSV) as [(EL & Hp0) | (x & EL & Hp0)];
    [|apply negb_false_iff, Z.eqb_eq in Hc; contradiction].
  psx_run (ps_c R) (Z.of_nat (3 - 1)) EC Hcok Hc64.
  assert (HA0 : sv_denot (ESX regsc) (SOff PS_DASH 0) = w64 (nth (Datatypes.S 3 - 1) PTRS 0)).
  { rewrite (psx_den_atom (ESX regsc) PS_DASH 0x21d40 0 (psx_dash_env regsc) ltac:(lia)).
    unfold ps_ptrs. cbn [nth Nat.sub]. rewrite EL. cbn [ps_sptr]. rewrite Z.add_0_r. reflexivity. }
  psx_fin_tac 3%nat P p lyc Sc Wc regsc memc mdc k HlenP HC HK H10 HNEXT (SOff PS_DASH 0) HA0.
Qed.

Lemma ps_seg_x : forall j, (1 <= j <= 3)%nat ->
ps_segx_stmt B MT ly S W regs mem md pf pl pv uri files layout verdict R O j.
Proof.
intros j Hj. destruct j as [|[|[|[|j]]]]; [lia | exact ps_seg_x1 | exact ps_seg_x2 | exact ps_seg_x3 | lia].
Qed.

End entry.
End e.
End f.
End d.
