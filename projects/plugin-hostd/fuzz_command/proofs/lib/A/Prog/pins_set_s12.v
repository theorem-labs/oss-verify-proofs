(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the join segment of pins_set's ASan walk, after cgif_file_fuzzer's cgif_close
   walk (proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v, a segment's seed and straight run, and lib/A/ACh2.v, the step
   into a call, at c8557374ad2e) over fuzz_command's recorder. *)

(* `ps_join`: from record()'s join to the first call of xstrdup. At PS_RET_RCF (the spill arm, after rec_calls_free)
   the code is one jump to PS_JOIN. From PS_JOIN the run loads the shadow byte of the slot c (marked usable, so the
   instrumented check does not take the error path), stores c->fn := 20, checks the shadow byte of c + 4 the same
   way, stores c->nargs := 0 and tests s5, the uri pointer: when it is 0 the argument is the default literal
   "(null)" at 0x22480. The call of xstrdup composes with ps_call_x (pins_set_s4.v), and the walk goes on at its
   return by the premise `ps_xret_stmt 1`. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas pins_set_s2 pins_set_s1 pins_set_s3
pins_set_s4 pins_set_s5 pins_set_s6 pins_set_s7 pins_set_s8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a register the run left at an atom of the environment *)
Lemma pj_reg : forall E k (rg : bvmap 5 word) (r : bv 5) (w : word),
getr rg r = sv_denot E (SOff k 0) -> ew E k = w -> getr rg r = w.
Proof. intros E k rg r w H Hk. rewrite H. cbn [sv_denot]. rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma pj_off : forall E k v d (rg : bvmap 5 word) (r : bv 5),
getr rg r = sv_denot E (SOff k d) -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> getr rg r = w64 (v + d).
Proof. intros E k v d rg r H Hk Hv. rewrite H. cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hv. reflexivity. Qed.

(* read a register of the state the run leaves (at a call: the registers of the state under setpc) *)
Ltac pj_reg_of HS r Hr :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
| st_ok ?sg ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg sg H E ss ms r HS) as Hr;
  lazymatch ss with context [mkSST _ ?rgs _ _ _ _] =>
    let e := eval vm_compute in (sr_get rgs r) in change (sr_get (ss_regs ss) r) with e in Hr
  end
end.

(* the registers ps_keep 1 names, and the return address and the argument, at the call *)
Ltac pj_regs HS K1 K2 K3 K4 K8 K9 K10 K18 K19 K20 K22 K23 K24 K25 K26 K27 :=
pj_reg_of HS (1%bv : bv 5) K1; pj_reg_of HS (2%bv : bv 5) K2; pj_reg_of HS (3%bv : bv 5) K3;
pj_reg_of HS (4%bv : bv 5) K4; pj_reg_of HS (8%bv : bv 5) K8; pj_reg_of HS (9%bv : bv 5) K9;
pj_reg_of HS (10%bv : bv 5) K10; pj_reg_of HS (18%bv : bv 5) K18; pj_reg_of HS (19%bv : bv 5) K19;
pj_reg_of HS (20%bv : bv 5) K20; pj_reg_of HS (22%bv : bv 5) K22; pj_reg_of HS (23%bv : bv 5) K23;
pj_reg_of HS (24%bv : bv 5) K24; pj_reg_of HS (Z_to_bv 5 25) K25; pj_reg_of HS (Z_to_bv 5 26) K26;
pj_reg_of HS (Z_to_bv 5 27) K27.

Ltac pj_in := cbn [In]; repeat first [ solve [left; reflexivity] | right ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
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
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the default literal's atom *)
Lemma pj_null : forall E, img_env VAL A_LIM E -> ew E PS_NULL = Z_to_bv 64 0x22480.
Proof.
intros E HEI. rewrite (img_env_atomP E PS_NULL HEI ltac:(unfold PS_NULL, A_OBJ, A_TEXT, A_LIM; lia)), (ps_null_val VOBJS).
reflexivity.
Qed.

(* the run writes only the slot's fn and nargs words: the program-static disjunct of awr_byte *)
Lemma pj_awr : forall E c cs STK sp0 O bl0 blc fr0 lyx own,
bv_unsigned (ew E PS_C) = c -> ps_slot_ok c ->
awr_ok SEGS B E [YP09.mkRegion (Some PS_C) 0 8 0 8 cs] STK sp0 (ps_FP O) bl0 blc fr0 lyx own.
Proof.
intros E c cs STK sp0 O bl0 blc fr0 lyx own Ec Hc a (r & Hin & Ha).
destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Ec in Ha.
apply (ps_awr_slot B HB cmd_prog_img STK sp0 O bl0 blc fr0 lyx own c a Hc). unfold CALL_SIZE. lia.
Qed.

(* a byte outside the slot's two words is kept by a run whose start state writes only them *)
Lemma pj_keep1 : forall E c cs (m m' : word -> option byte) (H : word -> bool) x,
frame_of E [YP09.mkRegion (Some PS_C) 0 8 0 8 cs] m m' ->
bv_unsigned (ew E PS_C) = c -> 0 <= x < 2 ^ 64 -> ~ (c <= x < c + 8) ->
aview SEGS H m' x = aview SEGS H m x.
Proof.
intros E c cs m m' H x Hfr Ec Hx Hn. apply (ps_rd_frame E _ H m m' x Hfr Hx).
intros (r & [<- | []] & Hr). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Ec in Hr. lia.
Qed.

(* the slot's fn and nargs words of the state at the call *)
Lemma pj_slot_words : forall E (H : word -> bool) m c cs,
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some PS_C) 0 8 0 8 cs) ->
bv_unsigned (ew E PS_C) = c ->
In (YP09.mkChunk 0 (CVal 4 (SLit 20))) cs -> In (YP09.mkChunk 4 (CVal 4 (SLit 0))) cs ->
aval_mem (aview SEGS H m) c 4 REC_PINS_SET /\ aval_mem (aview SEGS H m) (c + 4) 4 0.
Proof.
intros E H m c cs HR Ec H0 H4.
pose proof (field_of_region_any E (mrestrict H m) PS_C c cs 0 8 0 8 0 4%N (SLit 20) HR Ec H0 ltac:(cbn; lia)) as HV0.
pose proof (field_of_region_any E (mrestrict H m) PS_C c cs 0 8 0 8 4 4%N (SLit 0) HR Ec H4 ltac:(cbn; lia)) as HV4.
cbn [sv_denot] in HV0, HV4.
rewrite ps_pow4, unsigned_lit_small, (Z.mod_small 20 (2 ^ 32)), Z.add_0_r in HV0 by lia.
rewrite ps_pow4, unsigned_lit_small, (Z.mod_small 0 (2 ^ 32)) in HV4 by lia.
split; [exact (aval_mem_view SEGS H m c 4%nat 20 HV0) | exact (aval_mem_view SEGS H m (c + 4) 4%nat 0 HV4)].
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
Hypothesis HPU : 0 <= pu < 2 ^ 64.

Lemma pj_c_range : 0 <= ps_c R /\ ps_c R + 8 < 2 ^ 63.
Proof.
pose proof (ps_n_le16 B ly S W mem R O HREPA) as Hn.
pose proof (ps_slot_bounds (ps_c R) (ps_slot_of_ok (ps_n R) Hn)) as [Hcb _].
unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb. lia.
Qed.

Lemma pj_ecu : forall E, ew E PS_C = Z_to_bv 64 (ps_c R) -> bv_unsigned (ew E PS_C) = ps_c R.
Proof. intros E EC. pose proof pj_c_range as [H1 H2]. rewrite EC. apply unsigned_lit_small. lia. Qed.

Lemma pj_sp : forall (regsc : bvmap 5 word), getr regsc 2 = w64 (ps_sp0 regs - 80) ->
2 ^ 46 - 80 <= spZ regsc <= 2 ^ 47 /\ spZ regsc mod 16 = 0.
Proof.
intros regsc R2. pose proof (ps_sp0_facts B ly S W regs mem md ch HPRE) as (Hsp & Hsp16 & _).
assert (Esp : spZ regsc = ps_sp0 regs - 80) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
rewrite Esp. split; [lia|].
replace (ps_sp0 regs - 80) with (ps_sp0 regs + (-5) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
Qed.

(* the registers the rest of the body reads, at the call: ps_keep 1 *)
Lemma pj_keep_regs : forall E (rg regsc : bvmap 5 word),
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regsc r) ->
ew E PS_SB = Z_to_bv 64 SB -> ew E PS_C = Z_to_bv 64 (ps_c R) -> ew E PS_GREC = Z_to_bv 64 A_G_REC ->
getr regsc 2 = w64 (ps_sp0 regs - 80) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 20 = w64 pf -> getr regsc 19 = w64 pl -> getr regsc 9 = w64 pv ->
(forall r, 25 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
getr rg 2 = sv_denot E (SOff 2 0) -> getr rg 3 = sv_denot E (SOff 3 0) -> getr rg 4 = sv_denot E (SOff 4 0) ->
getr rg 8 = sv_denot E (SOff PS_C 0) -> getr rg 18 = sv_denot E (SOff PS_C 4) ->
getr rg 22 = sv_denot E (SOff PS_GREC 0) -> getr rg 23 = sv_denot E (SOff PS_SB 0) ->
getr rg 24 = sv_denot E ps_shx ->
getr rg 20 = sv_denot E (SOff 20 0) -> getr rg 19 = sv_denot E (SOff 19 0) -> getr rg 9 = sv_denot E (SOff 9 0) ->
getr rg (Z_to_bv 5 25) = sv_denot E (SOff 25 0) -> getr rg (Z_to_bv 5 26) = sv_denot E (SOff 26 0) ->
getr rg (Z_to_bv 5 27) = sv_denot E (SOff 27 0) ->
KEEP 1 rg.
Proof.
intros E rg regsc EE ESB EC EG R2 R3 R4 R20 R19 R9 RHI K2 K3 K4 K8 K18 K22 K23 K24 K20 K19 K9 K25 K26 K27.
pose proof pj_c_range as [Hc0 Hc63].
assert (Hc64 : 0 <= ps_c R < 2 ^ 64) by lia.
unfold ps_keep.
split; [exact (eq_trans (pj_reg E 2%nat _ _ _ K2 (EE 2%nat (2%bv : bv 5) eq_refl)) R2)|].
split; [exact (eq_trans (pj_reg E 3%nat _ _ _ K3 (EE 3%nat (3%bv : bv 5) eq_refl)) R3)|].
split; [exact (eq_trans (pj_reg E 4%nat _ _ _ K4 (EE 4%nat (4%bv : bv 5) eq_refl)) R4)|].
split; [exact (pj_reg E PS_C _ _ _ K8 EC)|].
split; [exact (pj_off E PS_C (ps_c R) 4 _ _ K18 EC Hc64)|].
split; [exact (pj_reg E PS_GREC _ _ _ K22 EG)|].
split; [exact (pj_reg E PS_SB _ _ _ K23 ESB)|].
split.
{ rewrite K24. unfold ps_shx.
  apply (denot_shx E PS_C PS_SB 4 (ps_c R) SB EC ESB); [lia | lia | lia | cbv [SB]; lia]. }
split; [intros Hlt; exfalso; lia|].
split; [intros _; exact (eq_trans (pj_reg E 20%nat _ _ _ K20 (EE 20%nat (20%bv : bv 5) eq_refl)) R20)|].
split; [intros _; exact (eq_trans (pj_reg E 19%nat _ _ _ K19 (EE 19%nat (19%bv : bv 5) eq_refl)) R19)|].
split; [intros _; exact (eq_trans (pj_reg E 9%nat _ _ _ K9 (EE 9%nat (9%bv : bv 5) eq_refl)) R9)|].
intros r Hr. rewrite <- (RHI r Hr).
assert (Hr3 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr3 as [-> | [-> | ->]].
- exact (pj_reg E 25%nat _ _ _ K25 (EE 25%nat (Z_to_bv 5 25) eq_refl)).
- exact (pj_reg E 26%nat _ _ _ K26 (EE 26%nat (Z_to_bv 5 26) eq_refl)).
- exact (pj_reg E 27%nat _ _ _ K27 (EE 27%nat (Z_to_bv 5 27) eq_refl)).
Qed.

(* the first call of xstrdup: the walk's invariant at the call (ps_core [] []) from ps_jinv and the two words the
   join stored, then ps_call_x, whose return the premise `ps_xret_stmt 1` takes *)
Lemma ps_join_call : forall lyc Sc (Wc : world SEGS) regsc memc memc' (rg : bvmap 5 word) mdc mdc' k,
ps_xret_stmt B MT ly S W regs mem md pf pl pv uri files layout verdict R O 1 ->
ps_jinv B MT ly S W regs mem md pu pf pl pv R O lyc Sc Wc regsc memc mdc k ->
ajournal SEGS B PINS_SET_STK (ps_sp0 regs) (ps_FP O) ly S W mem md [] lyc Sc Wc memc' mdc' k ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (ps_c R <= x < ps_c R + 8) -> rdW Wc memc' x = rdW Wc memc x) ->
aval_mem (rdW Wc memc') (ps_c R) 4 REC_PINS_SET -> aval_mem (rdW Wc memc') (ps_c R + 4) 4 0 ->
KEEP 1 rg -> getr rg 1 = Z_to_bv 64 (BASE + ps_ret 1) -> getr rg 10 = w64 (nth 0 PTRS 0) ->
SRr SEGS Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + AF_xstrdup)) memc' (seg_rom SEGS)) mdc') POST.
Proof.
intros lyc Sc Wc regsc memc memc' rg mdc mdc' k HX1 HJI HJ' KEEPM HFN HNA HK Hra Ha0.
destruct HJI as (HJ & Hk & Hmo & Hbb & Hfr & Hlive & Hrec0 & _).
destruct Hrec0 as (Rb & Qb & rdb & blb & HA & HlenR & Hrr & Hsp0 & Hprot & HQb & Hcov & HNC).
pose proof (proj1 HJ) as HARc.
pose proof (ps_n_le16 B ly S W mem R O HREPA) as Hn.
pose proof (ps_sp0_facts B ly S W regs mem md ch HPRE) as (Hsp & Hsp16 & Hspc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ps_slot_bounds (ps_c R) (ps_slot_of_ok (ps_n R) Hn)) as [Hcb Hc8].
assert (HOWN : forall pn, In pn (lay_blocks Qb) ->
  iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE)
  by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HA)))))))).
assert (HC : CORE [] [] lyc Sc Wc memc' mdc' k).
{ constructor.
  - exact HJ'.
  - cbn [app length Z.of_nat]. lia.
  - cbn [app length]. lia.
  - cbn [app length]. replace (ps_xm MT uri files layout verdict 0) with 0 by reflexivity.
    rewrite Z.add_0_r. exact Hmo.
  - cbn [app length]. replace (ps_live uri files layout verdict 0) with 0 by reflexivity.
    rewrite Z.add_0_r. exact Hbb.
  - intros i r Hir. apply (ps_aval_mem_in (rdW Wc memc)); [exact (Hfr i r Hir)|].
    assert (Hi : (i < 10)%nat)
      by (change 10%nat with (length ps_saved); apply nth_error_Some; rewrite Hir; discriminate).
    intros x Hx. apply KEEPM; [lia|]. unfold A_REC_SPILL in *. lia.
  - exact Hlive.
  - exists Rb, Qb, rdb, blb.
    split; [exact HA|]. split; [exact HlenR|]. split; [exact Hrr|]. split; [exact Hsp0|].
    split.
    { intros x Hx. rewrite <- (Hprot x Hx).
      pose proof (ps_prot_out_slot R Qb x HOWN Hn Hx) as Hout.
      apply KEEPM; [|unfold CALL_SIZE in Hout; lia].
      destruct Hx as [(Hg & _) | [(Hs & _) | ([q m] & Hq & Hx)]];
        [unfold A_G_REC, REC_SIZE in *; lia | unfold A_REC_SPILL, SC_SIZE in *; lia|].
      destruct (HQb _ Hq) as (HqS & _ & _).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc HqS) as (_ & H4096 & Hce & _).
      assert (req_size m >= m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). cbn [fst snd] in Hx. lia. }
    split; [exact HQb|].
    split; [intros pn Hpn; destruct (Hcov pn Hpn) as [H | H]; [left; exact H | right; left; exact H]|].
    split.
    { intros Hlt. apply (ps_aval_mem_in (rdW Wc memc)); [exact (HNC Hlt)|].
      intros x Hx. apply KEEPM; unfold A_G_REC, OFF_NCALLS, OFF_CALLS in *; lia. }
    split; [exact HFN|]. split; [exact HNA|].
    split; [constructor|].
    split; [intros i pn Hi; destruct i; discriminate Hi|].
    intros i pn Hi; destruct i; discriminate Hi. }
exact (ps_call_x B MT TXSTRDUP MTL HB cmd_prog_img RRO RELRO_IMG cmd_ro_ok_of_aro cmd_ro_prog_apart cmd_heap_tail_vis
  CMD_RO_IN ly S W regs mem md ch pu pf pl pv uri files layout verdict R O HPRE HROD HSU HSF HSL HSV HREPA HEV
  HLIVE HMOK 1%nat [] lyc Sc Wc rg memc' mdc' k ltac:(lia) eq_refl HC HK Hra Ha0
  (fun ly2 S2 W2 regs2 mem2 md2 p HC2 HK2 Hp10 => HX1 [] p ly2 S2 W2 regs2 mem2 md2 (k + 1) eq_refl HC2 HK2 Hp10)).
Qed.

(* the walk from PS_JOIN: the run to `bnez s5`, its two arms, the run to the call, and ps_join_call *)
Lemma pj_from_join : forall E (msj : machine_state) lyc Sc (Wc : world SEGS) regsc memc mdc mdc' k,
ps_xret_stmt B MT ly S W regs mem md pf pl pv uri files layout verdict R O 1 ->
ps_jinv B MT ly S W regs mem md pu pf pl pv R O lyc Sc Wc regsc memc mdc k ->
img_env VAL A_LIM E ->
ew E PS_SB = Z_to_bv 64 SB -> ew E PS_C = Z_to_bv 64 (ps_c R) -> ew E PS_GREC = Z_to_bv 64 A_G_REC ->
ew E PS_NULL = Z_to_bv 64 0x22480 ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regsc r) ->
st_ok_pi SEGS VAL E (mkSS PS_JOIN ps_jregs [ps_fnargs_r] None ps_mfacts) (restrict (w_H Wc) msj) ->
sh_ok SEGS ps_Bx ps_SH E (mrestrict (w_H Wc) (ms_mem msj)) ->
ajournal SEGS B PINS_SET_STK (ps_sp0 regs) (ps_FP O) ly S W mem md [] lyc Sc Wc (ms_mem msj) mdc' k ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (ps_c R <= x < ps_c R + 8) -> rdW Wc (ms_mem msj) x = rdW Wc memc x) ->
SRr SEGS Wc (mkCfg msj mdc') POST.
Proof.
intros E msj lyc Sc Wc regsc memc mdc mdc' k HX1 HJI HEI ESB EC EG EN EE HS SHOK HJ KEEP0.
pose proof HJI as (_ & _ & _ & _ & _ & _ & _ & R2 & R3 & R4 & R8 & R22 & R23 & R21 & R20 & R19 & R9 & RHI).
pose proof (ps_n_le16 B ly S W mem R O HREPA) as Hn.
assert (Hcok : ps_slot_ok (ps_c R)) by exact (ps_slot_of_ok (ps_n R) Hn).
pose proof (pj_ecu E EC) as ECu.
assert (E21 : ew E 21%nat = Z_to_bv 64 pu) by exact (eq_trans (EE 21%nat (21%bv : bv 5) eq_refl) R21).
assert (HSIG : pa_sigma CS_xstrdup = BASE + AF_xstrdup)
  by (rewrite (SIGP CS_xstrdup ltac:(unfold cmd_prog_syms; pj_in)); f_equal; reflexivity).
(* to `bnez s5`: the shadow bytes of c and c + 4 are marked usable, fn := 20, nargs := 0 *)
paj_run_tok RUN HS HJ SHOK Bspan.
all: try (lazymatch goal with |- SRr _ _ _ _ => fail | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ =>
  exact (pj_awr E (ps_c R) _ _ _ _ _ _ _ _ _ ECu Hcok) end).
set (mdv1 := with_vm_backing (m_vm_lazy _) _ _) in *; clearbody mdv1.
rename ms into ms1.
assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> ~ (ps_c R <= x < ps_c R + 8) -> rdW Wc (ms_mem ms1) x = rdW Wc memc x).
{ intros x Hx Hnx. rewrite <- (KEEP0 x Hx Hnx).
  exact (pj_keep1 E (ps_c R) _ (ms_mem msj) (ms_mem ms1) (w_H Wc) x HF ECu Hx Hnx). }
clear HF HFr HG KEEP0.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s5 <> 0: the uri pointer is the argument *)
  rewrite branch_ne_U, (ps_U_atom E 21%nat pu E21 HPU), U_SLit in Hc.
  change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hptr : nth 0 PTRS 0 = pu) by (destruct uri as [x|]; [reflexivity | exfalso; exact (Hc HSU)]).
  paj_run_tok RUN HS HJ SHOK Bspan.
  all: try (lazymatch goal with |- SRr _ _ _ _ => fail | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact (pj_awr E (ps_c R) _ _ _ _ _ _ _ _ _ ECu Hcok) end).
  set (mdv2 := with_vm_backing (m_vm_lazy _) _ _) in *; clearbody mdv2.
  rename ms into ms2.
  pj_regs HS K1 K2 K3 K4 K8 K9 K10 K18 K19 K20 K22 K23 K24 K25 K26 K27.
  assert (K10' : getr (ms_regs ms2) 10 = w64 (nth 0 PTRS 0))
    by (rewrite Hptr; exact (pj_reg E 21%nat _ _ _ K10 E21)).
  pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  destruct (pj_slot_words E (w_H Wc) (ms_mem ms2) (ps_c R) _ HR0 ECu ltac:(pj_in) ltac:(pj_in)) as [HFN HNA].
  pose proof (pj_keep_regs E (ms_regs ms2) regsc EE ESB EC EG R2 R3 R4 R20 R19 R9 RHI
    K2 K3 K4 K8 K18 K22 K23 K24 K20 K19 K9 K25 K26 K27) as HK.
  assert (K1' : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + ps_ret 1))
    by (rewrite K1; exact (codeptr_val E (ps_ret 1) HEI)).
  assert (KEEPM : forall x, 0 <= x < 2 ^ 64 -> ~ (ps_c R <= x < ps_c R + 8) -> rdW Wc (ms_mem ms2) x = rdW Wc memc x).
  { intros x Hx Hnx. rewrite <- (KEEP1 x Hx Hnx).
    exact (pj_keep1 E (ps_c R) _ (ms_mem ms1) (ms_mem ms2) (w_H Wc) x HF ECu Hx Hnx). }
  pmkst HS. rewrite HSIG.
  exact (ps_join_call lyc Sc Wc regsc memc (ms_mem ms2) (ms_regs ms2) mdc mdv2 k HX1 HJI HJ KEEPM HFN HNA HK K1' K10').
- (* s5 = 0: the default literal "(null)" is the argument *)
  rewrite branch_ne_U, (ps_U_atom E 21%nat pu E21 HPU), U_SLit in Hc.
  change (zcanon 0) with 0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hptr : nth 0 PTRS 0 = 0x22480)
    by (destruct uri as [x|]; [exfalso; destruct HSU as [Hne _]; exact (Hne Hc) | reflexivity]).
  paj_run_tok RUN HS HJ SHOK Bspan.
  all: try (lazymatch goal with |- SRr _ _ _ _ => fail | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact (pj_awr E (ps_c R) _ _ _ _ _ _ _ _ _ ECu Hcok) end).
  set (mdv2 := with_vm_backing (m_vm_lazy _) _ _) in *; clearbody mdv2.
  rename ms into ms2.
  pj_regs HS K1 K2 K3 K4 K8 K9 K10 K18 K19 K20 K22 K23 K24 K25 K26 K27.
  assert (K10' : getr (ms_regs ms2) 10 = w64 (nth 0 PTRS 0))
    by (rewrite Hptr; exact (pj_reg E PS_NULL _ _ _ K10 EN)).
  pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  destruct (pj_slot_words E (w_H Wc) (ms_mem ms2) (ps_c R) _ HR0 ECu ltac:(pj_in) ltac:(pj_in)) as [HFN HNA].
  pose proof (pj_keep_regs E (ms_regs ms2) regsc EE ESB EC EG R2 R3 R4 R20 R19 R9 RHI
    K2 K3 K4 K8 K18 K22 K23 K24 K20 K19 K9 K25 K26 K27) as HK.
  assert (K1' : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + ps_ret 1))
    by (rewrite K1; exact (codeptr_val E (ps_ret 1) HEI)).
  assert (KEEPM : forall x, 0 <= x < 2 ^ 64 -> ~ (ps_c R <= x < ps_c R + 8) -> rdW Wc (ms_mem ms2) x = rdW Wc memc x).
  { intros x Hx Hnx. rewrite <- (KEEP1 x Hx Hnx).
    exact (pj_keep1 E (ps_c R) _ (ms_mem ms1) (ms_mem ms2) (w_H Wc) x HF ECu Hx Hnx). }
  pmkst HS. rewrite HSIG.
  exact (ps_join_call lyc Sc Wc regsc memc (ms_mem ms2) (ms_regs ms2) mdc mdv2 k HX1 HJI HJ KEEPM HFN HNA HK K1' K10').
Qed.

(* the table arm: the walk starts at PS_JOIN *)
Lemma ps_join_j : forall lyc Sc (Wc : world SEGS) regsc memc mdc k,
ps_xret_stmt B MT ly S W regs mem md pf pl pv uri files layout verdict R O 1 ->
ps_jinv B MT ly S W regs mem md pu pf pl pv R O lyc Sc Wc regsc memc mdc k ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + PS_JOIN)) memc (seg_rom SEGS)) mdc) POST.
Proof.
intros lyc Sc Wc regsc memc mdc k HX1 HJI.
pose proof HJI as (HJ & _ & _ & _ & _ & _ & _ & R2 & _ & _ & R8 & R22 & R23 & _).
pose proof (ps_n_le16 B ly S W mem R O HREPA) as Hn.
pose proof (pj_sp regsc R2) as [Hsp Hsp16].
destruct (ps_join_seed B HB VOBJS cmd_prog_writable lyc Sc Wc memc mdc regs regsc PS_JOIN (ps_c R) (proj1 HJ)
  (ps_slot_of_ok (ps_n R) Hn) Hsp Hsp16 R8 R22 R23) as [HS SHOK].
destruct (ps_Ec_facts VOBJS regsc regs (ps_c R) 0 0 0) as (HEI & ESB & EC & _ & _ & _ & EG & _ & EE & _).
exact (pj_from_join _ _ lyc Sc Wc regsc memc mdc mdc k HX1 HJI HEI ESB EC EG (pj_null _ HEI) EE HS SHOK HJ
  (fun x _ _ => eq_refl)).
Qed.

(* the spill arm: the walk starts at PS_RET_RCF, one jump before PS_JOIN *)
Lemma ps_join_r : forall lyc Sc (Wc : world SEGS) regsc memc mdc k,
ps_xret_stmt B MT ly S W regs mem md pf pl pv uri files layout verdict R O 1 ->
ps_jinv B MT ly S W regs mem md pu pf pl pv R O lyc Sc Wc regsc memc mdc k ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + PS_RET_RCF)) memc (seg_rom SEGS)) mdc) POST.
Proof.
intros lyc Sc Wc regsc memc mdc k HX1 HJI.
pose proof HJI as (HJ & _ & _ & _ & _ & _ & _ & R2 & _ & _ & R8 & R22 & R23 & _).
pose proof (ps_n_le16 B ly S W mem R O HREPA) as Hn.
assert (Hcok : ps_slot_ok (ps_c R)) by exact (ps_slot_of_ok (ps_n R) Hn).
pose proof (pj_sp regsc R2) as [Hsp Hsp16].
destruct (ps_join_seed B HB VOBJS cmd_prog_writable lyc Sc Wc memc mdc regs regsc PS_RET_RCF (ps_c R) (proj1 HJ)
  Hcok Hsp Hsp16 R8 R22 R23) as [HS SHOK].
destruct (ps_Ec_facts VOBJS regsc regs (ps_c R) 0 0 0) as (HEI & ESB & EC & _ & _ & _ & EG & _ & EE & _).
pose proof (pj_ecu _ EC) as ECu.
set (E := ps_Ec regsc regs (ps_c R) 0 0 0) in *. clearbody E.
paj_run_to_tok RUNTO HS HJ SHOK Bspan PS_JOIN.
all: try (lazymatch goal with |- SRr _ _ _ _ => fail | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ =>
  exact (pj_awr E (ps_c R) _ _ _ _ _ _ _ _ _ ECu Hcok) end).
set (mdv0 := with_vm_backing (m_vm_lazy _) _ _) in *; clearbody mdv0.
exact (pj_from_join E ms lyc Sc Wc regsc memc mdc mdv0 k HX1 HJI HEI ESB EC EG (pj_null E HEI) EE HS SHOK HJ
  (fun x Hx Hnx => pj_keep1 E (ps_c R) _ memc (ms_mem ms) (w_H Wc) x HF ECu Hx Hnx)).
Qed.

Lemma ps_join : ps_join_stmt B MT ly S W regs mem md pu pf pl pv uri files layout verdict R O.
Proof.
unfold ps_join_stmt, ps_jcont. intros HX1 pc lyc Sc Wc regsc memc mdc k Hpc HJI.
destruct Hpc as [-> | ->].
- exact (ps_join_j lyc Sc Wc regsc memc mdc k HX1 HJI).
- exact (ps_join_r lyc Sc Wc regsc memc mdc k HX1 HJI).
Qed.

End entry.
End e.
End f.
End d.
